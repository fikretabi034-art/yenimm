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


class LiveFreezeRegressionTests(unittest.TestCase):
    """V2.9.42: the live view used to freeze after the very first hand."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        patcher = patch.object(roulette, "persistent_data_dir", return_value=self.temp.name)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.state = roulette.RouletteState()
        self.state.set_pragmatic_identity("T1", title="Table1")
        # Deterministic spin stream, newest-first windows are built from it.
        self.stream = [(i * 11 + i * i // 7) % 37 for i in range(60)]

    def feed_dom_widget(self, window, source="DOM canlı kilitli"):
        chosen = roulette.choose_live_dom_candidate(
            [{"nums": list(window), "cls": "recent-results"}],
            list(self.state.history),
        )
        if not chosen:
            return False
        self.state.update_results(
            chosen["nums"],
            table_name="Table1",
            source=source,
        )
        return True

    def test_short_live_widget_no_longer_freezes_after_first_hand(self):
        # Several Pragmatic skins render only 5..8 recent numbers. The old
        # fixed 8-number overlap made such a widget unmatchable forever:
        # the bootstrap read worked and every later spin proved nothing.
        widget_size = 6
        first = self.stream[:widget_size]
        self.assertTrue(self.feed_dom_widget(first))
        self.assertEqual(self.state.history, list(first))

        for index, spin in enumerate(self.stream[widget_size:widget_size + 15], 1):
            window = ([spin] + first)[:widget_size]
            self.assertTrue(
                self.feed_dom_widget(window),
                f"{index}. elde DOM penceresi eşleştirilemedi (ekran dondu)",
            )
            self.assertEqual(int(self.state.history[0]), int(spin))
            first = window
            self.assertEqual((index - 1) % 12 + 1, len(self.state.display_compare_batch))

        self.assertEqual(self.state.score_error_status, "OK")

    def test_eight_number_widget_against_long_live_history(self):
        long_window = self.stream[:20]
        self.state.update_results(long_window, table_name="Table1", source="API")
        self.assertEqual(len(self.state.history), 20)

        for spin in self.stream[20:26]:
            self.assertTrue(self.feed_dom_widget([spin] + long_window[:7]))
            self.assertEqual(int(self.state.history[0]), int(spin))
            long_window = [spin] + long_window[:19]

    def test_unrelated_widget_is_still_locked_out_while_feed_is_alive(self):
        self.state.update_results(self.stream[:20], table_name="Table1", source="API")
        before = list(self.state.history)
        unrelated = [(i * 17 + 5) % 37 for i in range(20)]
        for _ in range(6):
            self.state.update_results(unrelated, table_name="Table1", source="DOM")
        # The live feed just applied data, so an unaligned window must never
        # rewrite the visible history.
        self.assertEqual(self.state.history, before)
        self.assertEqual(self.state.live_resync_count, 0)
        self.assertEqual(self.state.display_compare_batch, [])

    def test_stale_anchor_recovers_once_and_keeps_scored_rounds(self):
        clock = {"t": 1000.0}
        with patch.object(roulette.time, "time", lambda: clock["t"]):
            self._run_stale_anchor_recovery(clock)

    def _run_stale_anchor_recovery(self, clock):
        self.state.update_results(self.stream[:20], table_name="Table1", source="API")
        # One real scored round.
        self.assertTrue(self.feed_dom_widget([self.stream[20]] + self.stream[:19]))
        self.assertEqual(len(self.state.display_compare_batch), 1)
        self.assertEqual(len(self.state.neighbor_display_batch), 1)
        self.assertEqual(len(self.state.neighbor1_display_batch), 1)
        scored_actual = self.state.display_compare_batch[0]["actual"]

        # The widget is replaced / the table restarts: every offered window is
        # unrelated to the live head. This used to freeze the screen forever.
        fresh = self.stream[21:41]
        clock["t"] += roulette.LIVE_RESYNC_IDLE_SECONDS + 5.0
        for _ in range(roulette.LIVE_RESYNC_CONFIRMATIONS - 1):
            self.state.update_results(fresh, table_name="Table1", source="DOM")
            self.assertEqual(self.state.live_resync_count, 0)

        clock["t"] += 1.0
        self.state.update_results(fresh, table_name="Table1", source="DOM")
        self.assertEqual(self.state.live_resync_count, 1)
        self.assertEqual(self.state.history, list(fresh[:20]))
        self.assertIn("YENIDEN SENKRON", self.state.status)

        # Already scored K1/K2/GECMIS data must survive the re-anchor.
        self.assertEqual(len(self.state.display_compare_batch), 1)
        self.assertEqual(self.state.display_compare_batch[0]["actual"], scored_actual)
        self.assertEqual(len(self.state.neighbor_display_batch), 1)
        self.assertEqual(len(self.state.neighbor1_display_batch), 1)
        self.assertEqual(self.state.neighbor_stats_total["trials"], 1)
        self.assertEqual(self.state.neighbor1_stats_total["trials"], 1)

        # ...and live tracking continues from the re-anchored window.
        clock["t"] += 5.0
        for spin in self.stream[41:46]:
            self.assertTrue(self.feed_dom_widget([spin] + self.state.history[:19]))
            self.assertEqual(int(self.state.history[0]), int(spin))
        self.assertEqual(len(self.state.display_compare_batch), 6)

    def test_every_hand_advances_all_views_for_both_widget_orientations(self):
        # Live-continuity acceptance criterion: after entering a table every
        # subsequent hand must reach the state. This replays DOM-style windows
        # with exactly one new front number each -- a short 5-number widget and
        # the same widget rendered oldest-first (newest last) -- and checks that
        # SON20, GEÇMİŞ, the scored trials and BOTH komşu batches move forward
        # once per hand.
        for orientation in ("newest-first", "newest-last"):
            with self.subTest(orientation=orientation):
                state = roulette.RouletteState()
                state.set_pragmatic_identity("T2", title="Table2")
                state.live_resync_window = None
                state.live_resync_seen = None
                state.live_resync_count = 0
                state.last_live_apply = 0.0
                state.last_resync_at = 0.0
                size = 5
                head = self.stream[:size]
                # The game screen always exposes the current winning number;
                # that is the only evidence available before any history exists.
                state.last_live_result_number = int(head[0])

                def feed(window):
                    nums = list(reversed(window)) if orientation == "newest-last" else list(window)
                    chosen = roulette.choose_live_dom_candidate(
                        [{"nums": nums, "cls": "recent-results"}],
                        list(state.history),
                    )
                    if not chosen:
                        return False
                    state.update_results(
                        chosen["nums"], table_name="Table2", source="DOM canlı"
                    )
                    return True

                self.assertTrue(feed(head))
                self.assertEqual(state.history, list(head))
                # Persisted learning from an earlier table may already hold
                # scored rounds, so measure the advance per hand.
                base_trials = int(
                    (state.validation or {}).get("trials", 0) or 0
                )
                base_n1 = int((state.neighbor_stats_total or {}).get("trials", 0) or 0)
                base_n2 = int((state.neighbor1_stats_total or {}).get("trials", 0) or 0)

                for hand, spin in enumerate(self.stream[size:size + 12], 1):
                    window = ([spin] + head)[:size]
                    state.last_live_result_number = int(spin)
                    self.assertTrue(
                        feed(window),
                        f"{orientation}: {hand}. elde DOM penceresi eşleştirilemedi",
                    )
                    self.assertEqual(int(state.history[0]), int(spin))
                    self.assertEqual(hand, len(state.display_compare_batch))
                    self.assertEqual(hand, len(state.neighbor_display_batch))
                    self.assertEqual(hand, len(state.neighbor1_display_batch))
                    validation = state.validation
                    if isinstance(validation, dict):
                        self.assertEqual(
                            hand,
                            int(validation.get("trials", 0)) - base_trials,
                        )
                    self.assertEqual(
                        hand, state.neighbor_stats_total["trials"] - base_n1
                    )
                    self.assertEqual(
                        hand, state.neighbor1_stats_total["trials"] - base_n2
                    )
                    head = window

                self.assertEqual(state.score_error_status, "OK")
                self.assertEqual(len(state.display_compare_batch), 12)

    def test_oldest_first_api_window_keeps_scoring_every_hand(self):
        # V2.9.44: `detect_new_front` only compares forward. An endpoint that
        # answers oldest-first (newest last) was therefore rejected on EVERY
        # hand: the prediction was produced but never ran, GEÇMİŞ/K1/K2 stayed
        # at zero and the screen froze while the game kept spinning.
        state = self.state
        state.update_results(self.stream[:20], table_name="Table1", source="API")
        self.assertEqual(int(state.history[0]), int(self.stream[0]))
        base_trials = int((state.validation or {}).get("trials", 0) or 0)

        head = self.stream[:20]
        for hand, spin in enumerate(self.stream[20:32], 1):
            # Endpoint renders the window oldest-first.
            oldest_first = list(reversed([spin] + head[:19]))
            state.update_results(
                oldest_first, table_name="Table1", source="Pragmatic API"
            )
            self.assertEqual(
                int(state.history[0]), int(spin),
                f"{hand}. elde canlı görünüm ilerlemedi (yön hâlâ yanlış)",
            )
            self.assertEqual(
                hand,
                int((state.validation or {}).get("trials", 0)) - base_trials,
                f"{hand}. elde tur puanlanmadı",
            )
            self.assertEqual(hand, len(state.display_compare_batch))
            self.assertEqual(hand, len(state.neighbor_display_batch))
            self.assertEqual(hand, len(state.neighbor1_display_batch))
            head = [spin] + head[:19]

        self.assertEqual(state.score_error_status, "OK")

    def test_unrelated_window_still_cannot_prove_new_spins_in_either_orientation(self):
        state = self.state
        state.update_results(self.stream[:20], table_name="Table1", source="API")
        before = list(state.history)
        for orientation in ("forward", "reversed"):
            with self.subTest(orientation=orientation):
                unrelated = [(i * 17 + 5) % 37 for i in range(20)]
                if orientation == "reversed":
                    unrelated = list(reversed(unrelated))
                for _ in range(6):
                    state.update_results(
                        unrelated, table_name="Table1", source="Pragmatic API"
                    )
                self.assertEqual(state.history, before)
                self.assertEqual(state.live_resync_count, 0)
                self.assertEqual(len(state.display_compare_batch), 0)

    def test_detect_new_front_still_requires_a_real_overlap(self):
        # V2.9.44: `needed` used to be clamped by `remaining`, so a short tail
        # lowered the bar to ONE number and a coincidental match at the end of
        # an unrelated window "proved" many new spins.
        history = [7, 14, 21, 28, 35, 3, 9, 18, 26, 1, 32, 5, 12, 30, 11, 24]
        # One coincidentally equal number is not proof of a new spin.
        self.assertEqual(roulette.detect_new_front(history, [7, 2, 4, 6, 8]), [])
        # A genuine continuation of the same window is accepted.
        self.assertEqual(
            roulette.detect_new_front(history, [13] + history[:5]),
            [13],
        )
        # A short tail must not lower the overlap floor to one number: here the
        # only match is the single last element of the reversed window, which
        # used to "prove" nine new spins.
        tail_match = list(reversed([7, 14, 21, 28, 35, 3, 9, 18, 26, 1]))
        self.assertEqual(roulette.detect_new_front(history, tail_match), [])


if __name__ == "__main__":
    unittest.main()


class DirectFeedBootstrapTests(unittest.TestCase):
    """V2.9.43: PRAGMATIC DIRECT 500/500 used to be discarded forever.

    `update_table_history_500` rejected a window that did not prefix-align with
    the stored long archive, and that early return ran BEFORE the live-view
    bootstrap. Result on a live session: "MASA SON500: örtüşme doğrulanamadı"
    together with "SON: --" and "CANLI HAFİZA: 0 spin" -- an empty screen even
    though the game's own 500-result panel was already in hand.
    """

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        patcher = patch.object(
            roulette, "persistent_data_dir", return_value=self.temp.name
        )
        patcher.start()
        self.addCleanup(patcher.stop)
        self.state = roulette.RouletteState()
        self.state.set_pragmatic_identity("T9", title="Table9")
        # Deterministic spin stream; index 0 is the newest spin.
        self.stream = [(i * 11 + i * i // 7) % 37 for i in range(120)]
        self.state.live_resync_window = None
        self.state.live_resync_seen = None
        self.state.live_resync_count = 0
        self.state.last_live_apply = 0.0
        self.state.last_resync_at = 0.0

    def trials(self):
        value = self.state.validation
        return int(value.get("trials", 0)) if isinstance(value, dict) else 0

    def test_disjoint_archive_no_longer_blocks_first_live_view(self):
        s = self.state
        # An unrelated (other day / other channel) archive already on disk.
        s.table_long_history = [(40 - i) % 37 for i in range(400)]
        s.table_long_source = "MASA SON500"
        s.table_long_table = "pragmatic_T9"
        s.table_history_500 = list(s.table_long_history[:500])
        s.table_history_table = "pragmatic_T9"

        s.update_table_history_500(self.stream, table_name="T9")

        self.assertTrue(s.history, "canlı görünüm hâlâ boş")
        self.assertEqual(int(s.history[0]), int(self.stream[0]))
        self.assertEqual(len(s.history), 20)
        self.assertEqual(s.table_long_history[:120], self.stream)
        self.assertIn("İLK CANLI GÖRÜNÜM", s.table_history_source)
        self.assertIn("ARŞİV YENİDEN KURULDU", s.table_long_source)

    def test_live_lock_still_rejects_disjoint_window_once_history_exists(self):
        s = self.state
        s.update_table_history_500(self.stream[:60], table_name="T9")
        s.update_results(self.stream[:10], table_name="T9", source="CANLI")
        before = list(s.history)
        archive = list(s.table_long_history)

        for offset in (30, 31, 32, 33, 34):
            s.update_table_history_500(
                self.stream[offset:offset + 50], table_name="T9"
            )

        self.assertEqual(s.history, before, "kurulmuş canlı görünüm bozuldu")
        self.assertEqual(s.table_long_history, archive)
        self.assertIn("örtüşme doğrulanamadı", s.table_history_source)

    def test_bootstrap_orientation_follows_live_badge(self):
        s = self.state
        # Some endpoints answer oldest-first. The game's own winning-number
        # badge is the only proof of orientation, and it must win over the
        # window order.
        s.last_live_result_number = int(self.stream[0])
        s.update_table_history_500(
            list(reversed(self.stream)), table_name="T9"
        )
        self.assertEqual(int(s.history[0]), int(self.stream[0]))
        self.assertEqual(s.table_long_history[:120], self.stream)

    def test_completed_newest_first_window_is_not_flipped(self):
        s = self.state
        s.update_table_history_500(self.stream[:20], table_name="T9")
        s.update_results(self.stream[:10], table_name="T9", source="CANLI")
        s.last_live_result_number = int(self.stream[0])
        trials_before = self.trials()

        s.update_table_history_500(self.stream[:60], table_name="T9")

        self.assertEqual(int(s.history[0]), int(self.stream[0]))
        self.assertEqual(s.history[:3], [int(x) for x in self.stream[:3]])
        self.assertEqual(s.table_long_history[:60], self.stream[:60])
        # Completing a partial SON500 fills OLDER data: no new round is scored.
        self.assertEqual(self.trials(), trials_before)

    def test_oldest_first_source_keeps_updating_after_bootstrap(self):
        s = self.state
        s.last_live_result_number = int(self.stream[0])
        s.update_table_history_500(list(reversed(self.stream[:60])), table_name="T9")
        self.assertEqual(int(s.history[0]), int(self.stream[0]))

        # The feed keeps answering oldest-first. Each hand: the live screen
        # shows one new winner (the only source of "now"), then SON500 arrives
        # with a window whose newest entry is that same winner.
        applied = 0
        for step in range(1, 6):
            winner = int(self.stream[step])
            self.assertTrue(
                s.update_live_result(winner, source="CANLI SONUÇ EKRANI"),
                f"{step}. elde canlı sonuç ekrana alınamadı",
            )
            s.last_live_result_number = winner
            window = list(reversed(self.stream[step:step + 60]))
            s.update_table_history_500(window, table_name="T9")
            applied += 1
            self.assertEqual(
                int(s.history[0]), winner,
                f"{applied}. elde canlı görünüm ilerlemedi (yön hâlâ yanlış)",
            )
            self.assertGreaterEqual(
                self.trials(), applied,
                f"{applied}. elde tur puanlanmadı",
            )

    def test_orient_window_newest_first_uses_the_badge(self):
        window = [30, 5, 21, 33, 16]
        self.assertEqual(
            roulette.orient_window_newest_first(window, 30), window
        )
        self.assertEqual(
            roulette.orient_window_newest_first(window, 16),
            list(reversed(window)),
        )
        # No badge: keep the order the endpoint used (never guess).
        self.assertEqual(
            roulette.orient_window_newest_first(window, None), window
        )
        # A badge that is not at either end proves nothing either.
        self.assertEqual(
            roulette.orient_window_newest_first(window, 21), window
        )
