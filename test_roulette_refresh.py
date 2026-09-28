"""Offline regression tests; no browser, casino connection or Tk window required."""
import json
import os
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

# CI/Linux may not ship the optional desktop Tk bindings.
try:
    import tkinter  # noqa: F401
except ImportError:
    tk = types.ModuleType("tkinter")
    tk.ttk = types.ModuleType("tkinter.ttk")
    sys.modules["tkinter"] = tk
    sys.modules["tkinter.ttk"] = tk.ttk

import roulette_v1 as roulette


class TableRefreshTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        patcher = patch.object(roulette, "persistent_data_dir", return_value=self.temp.name)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.state = roulette.RouletteState()
        # Distinctive deterministic 500-result window, newest first.
        self.old = [(i * 13 + i * i // 31) % 37 for i in range(500)]
        self.new = [3, 6, 34] + self.old[:497]

    def archive(self, tid):
        return roulette.load_table_long_archive(self.temp.name, "pragmatic_" + tid)

    def test_ten_minute_single_tab_cycle_and_background_banks(self):
        self.assertEqual(roulette.TAB_WALK_REFRESH_SECONDS, 600.0)
        s = self.state
        self.assertEqual(s.store_background_table_history(self.old, "A"), 500)
        self.assertEqual(s.store_background_table_history(self.old, "B"), 500)
        self.assertEqual(s.store_background_table_history(self.old, "A"), 0)
        self.assertEqual(s.store_background_table_history(self.new, "A"), 3)
        self.assertEqual(s.store_background_table_history(self.new, "A"), 0)
        self.assertEqual(self.archive("A"), [3, 6, 34] + self.old)
        self.assertEqual(self.archive("B"), self.old)
        self.assertEqual(s.table_registry["A"]["long_count"], 503)
        # An older out-of-order reply must neither rewind the 500 anchor nor
        # cause the following scan to append the same results a second time.
        self.assertEqual(s.store_background_table_history(self.old, "A"), 0)
        self.assertEqual(s._saved_table500("pragmatic_A"), self.new)
        self.assertEqual(s.store_background_table_history(self.new, "A"), 0)
        self.assertEqual(self.archive("A"), [3, 6, 34] + self.old)

        # New process uses the on-disk 500 anchor to append only fresh spins.
        restarted = roulette.RouletteState()
        newer = [8, 18] + self.new[:498]
        self.assertEqual(restarted.store_background_table_history(newer, "A"), 2)
        self.assertEqual(self.archive("A"), [8, 18, 3, 6, 34] + self.old)

    def test_finished_pass_schedules_restart_but_manual_stop_cancels_it(self):
        bridge = object.__new__(roulette.ChromeBridge)
        bridge.state = self.state
        bridge._close_table_scan_target = lambda: None
        bridge.ws = None
        bridge.table_scan_tab_walk = True
        bridge.table_scan_auto_cycle = True
        bridge.table_scan_cycle_seconds = roulette.TAB_WALK_REFRESH_SECONDS
        bridge.table_scan_enabled = True
        with patch.object(roulette.time, "time", return_value=2000.0):
            bridge.stop_table_scan("lobi sonuna ulaşıldı")
        self.assertEqual(bridge.table_scan_next_cycle, 2600.0)
        self.assertIn("10 dk sonra", self.state.table_scan_status)
        bridge.stop_table_scan("kullanıcı durdurdu")
        self.assertFalse(bridge.table_scan_auto_cycle)
        self.assertEqual(bridge.table_scan_next_cycle, 0.0)

    def test_disjoint_or_reversed_window_does_not_mix_tables(self):
        s = self.state
        s.store_background_table_history(self.old, "A")
        unrelated = [(i * 17 + 4) % 37 for i in range(500)]
        s.store_background_table_history(unrelated, "A")
        self.assertEqual(self.archive("A"), self.old)
        self.assertEqual(s._saved_table500("pragmatic_A"), self.old)
        self.assertEqual(s.store_background_table_history(self.new, "A"), 3)

    def test_partial_window_can_expand_without_counting_old_spins_as_new(self):
        s = self.state
        self.assertEqual(s.store_background_table_history(self.old[:20], "A"), 20)
        self.assertEqual(s.store_background_table_history(self.old, "A"), 0)
        self.assertEqual(self.archive("A"), self.old)
        self.assertEqual(s._saved_table500("pragmatic_A"), self.old)
        self.assertEqual(s.store_background_table_history(self.new, "A"), 3)
        self.assertEqual(len(self.archive("A")), 503)

        s.set_pragmatic_identity("B", title="B")
        s.update_table_history_500(self.old[:20], table_name="B")
        s.update_table_history_500(self.old, table_name="B")
        self.assertEqual(s.table_long_history, self.old)

    def test_repeated_active_scan_does_not_recompute_prediction(self):
        s = self.state
        s.set_pragmatic_identity("A", title="A")
        s.update_table_history_500(self.old, table_name="A")
        self.assertEqual(len(s.table_long_history), 500)
        with patch.object(s, "_make_prediction", wraps=s._make_prediction) as predict:
            s.update_table_history_500(self.old, table_name="A")
            self.assertEqual(predict.call_count, 0)
        s.update_table_history_500(self.new, table_name="A")
        self.assertEqual(len(s.table_long_history), 503)
        s.update_table_history_500(self.old, table_name="A")
        self.assertEqual(s.table_history_500, self.new)
        self.assertEqual(len(s.table_long_history), 503)

    def test_scored_history_and_neighbor_tabs_restore_without_rescoring(self):
        s = self.state
        s.set_pragmatic_identity("A", title="A")
        s.table_name = "A"
        row = {
            "actual": 34, "predicted": 16, "side4_numbers": [33, 32, 17, 19],
            "neighbor_bet": {"actual": 34, "net": 16, "any_neighbor_hit": False,
                             "unique_coverage": 20},
            "neighbor1_bet": {"actual": 34, "net": 16, "any_neighbor_hit": True,
                              "unique_coverage": 12},
        }
        s.validation_history = [row]
        s.display_compare_batch = [row]
        s.neighbor_display_batch = [row["neighbor_bet"]]
        s.neighbor1_display_batch = [row["neighbor1_bet"]]
        s._save_learning()
        restored = roulette.RouletteState()
        restored.set_pragmatic_identity("A", title="A")
        restored._try_load_learning("A", self.old[:20])
        self.assertEqual(restored.display_compare_batch, [row])
        self.assertEqual(restored.neighbor_display_batch, [row["neighbor_bet"]])
        self.assertEqual(restored.neighbor1_display_batch, [row["neighbor1_bet"]])
        self.assertTrue(restored.last_neighbor1_package["won"])
        self.assertFalse(restored.last_neighbor2_package["won"])
        self.assertEqual(restored.validation["trials"], 0)
        restored.clear_neighbor_comparisons()
        again = roulette.RouletteState()
        again.set_pragmatic_identity("A", title="A")
        again._try_load_learning("A", self.old[:20])
        self.assertEqual(again.neighbor_display_batch, [])


if __name__ == "__main__":
    unittest.main()
