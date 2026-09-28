ROULETTE PRO AI V2.9.41 • SON500 KİLİT OKU

SORUN
- Bazı operator sayfalarında Pragmatic rulet lobisinin DOM'u masa açıldıktan sonra arkada kalıyor.
- Masa ekranda açık ve SON500 paneli görünürken program alttaki/arkadaki lobi kartlarını görüp 'Rulet lobisi' modunda kalabiliyordu.
- Bu yüzden önceden hızlıca 500/500 alıp çıkan masa bazen ilk masada bekliyordu.

DÜZELTME
1. Aktif masa görünümü lobi taramasından önce kilitlenir.
   - Sağ üst oyun içi Lobi düğmesi veya görünür SON500 kontrolü varsa,
   - bahis/masa arayüzü görünüyorsa,
   - program önce bunu gerçek masa olarak kabul eder.

2. SON500 görünüyorsa lobi kartları yok sayılır.
   - Genel lobi/kart tarayıcısı çalışmaz.
   - Masa bekleme kilidi yeniden oluşturulur.
   - HISTORY500_SCAN hemen tetiklenir.
   - Panelden 500 spin okunup bankaya kaydedilir.

3. Bekleme kilidi yanlışlıkla temizlenmiş olsa bile veri okunur.
   - Collector hâlâ masa ekranındaysa HISTORY500 okumaları devam eder.
   - Panel görünüyorsa 500/500 kayıt yapılabilir.

4. Bloklu/SON500 olmayan masa kuralı korunur.
   - PowerUp Rulet ve Sıcak & Soğuk-only masalar atlanır.

BEKLENEN DURUM YAZILARI
- SEKMELİ TOPLA: masa açık • SON500 paneli görüldü • ... • 500 spin okunuyor
- SEKMELİ TOPLA: sağ-alt SON500 paneli kaydedildi • ... • 500/500 • minimum bekleme sonrası lobiye dönülecek
- SEKMELİ TOPLA: bloklu masa • ... • anında es geçiliyor

500 SPİN KONTROLÜ
- PRAGMATIC DIRECT: 500/500
- PRAGMATIC statisticHistory network: 500/500
- UZUN MASA ARŞİVİ: 500+
- MASA BANKALARINI GÖR düğmesi
