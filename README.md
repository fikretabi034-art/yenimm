# Roulette Pro AI — masa verisi ve canlı karşılaştırmalar

Windows'ta `BASLAT_ROULETTE_V2_9_12_MULTI_TABLE_COLLECTOR.bat` ile başlatın. Tkinter arayüzünde **VERİ → TEK SEKME LOBİ TOPLA • 10 DK** düğmesine basarak tek sekmeli otomatik toplamayı başlatın. Bir lobi turu tamamlandıktan **10 dakika sonra** bir sonraki tur başlar; **TARAMAYI DURDUR** otomatik tekrarı da kapatır. Program yeniden açıldığında toplamayı tekrar başlatmanız gerekir.

Her masa kendi `tableId` kimliğiyle, kullanıcının `PragmaticRouletteTracker` veri klasöründe ayrı bir SON500 penceresi ve uzun arşiv tutar. Sonraki toplamalarda örtüşen bölüm doğrulanır; yalnızca yeni sonuçlar uzun arşivin başına eklenir. Aynı pencere tekrar geldiğinde spinler yeniden eklenmez. Eski veya örtüşmesi doğrulanamayan pencere arşivi değiştirmez; 20/500 gibi kısmi pencerenin daha sonra 500/500'e tamamlanması ise eski sonuçları yeni spin saymadan arşivi tamamlar.

**GEÇMİŞ, 1 KOMŞU, 2 KOMŞU** karşılaştırmaları yalnızca *önceden gösterilmiş tahminin ardından doğrulanmış gerçek sonuçlarla* puanlanır. Toplanan eski 500 spin geçmişe dönük tahmin başarısı olarak sayılmaz. Bu üç görünümün son 12'lik listeleri uygulama yeniden açıldığında da geri gelir. Rastgele rulette geçmiş frekanslar gelecekteki sonuçları garanti etmez.

Çevrimdışı regresyon testleri: `python -m unittest -v test_roulette_refresh.py`. Tarayıcı/oyun sitesinin canlı davranışı bu testlerde simüle edilmez.
