# Roulette Pro AI — masa verisi ve canlı karşılaştırmalar

Windows'ta `BASLAT_ROULETTE_V2_9_12_MULTI_TABLE_COLLECTOR.bat` ile başlatın. Tkinter arayüzünde **VERİ → TEK SEKME LOBİ TOPLA • 10 DK** düğmesine basarak tek sekmeli otomatik toplamayı başlatın. Bir lobi turu tamamlandıktan **10 dakika sonra** bir sonraki tur başlar; **TARAMAYI DURDUR** otomatik tekrarı da kapatır. Program yeniden açıldığında toplamayı tekrar başlatmanız gerekir.

Her masa kendi `tableId` kimliğiyle, kullanıcının `PragmaticRouletteTracker` veri klasöründe ayrı bir SON500 penceresi ve uzun arşiv tutar. Sonraki toplamalarda örtüşen bölüm doğrulanır; yalnızca yeni sonuçlar uzun arşivin başına eklenir. Aynı pencere tekrar geldiğinde spinler yeniden eklenmez. Eski veya örtüşmesi doğrulanamayan pencere arşivi değiştirmez; 20/500 gibi kısmi pencerenin daha sonra 500/500'e tamamlanması ise eski sonuçları yeni spin saymadan arşivi tamamlar.

**GEÇMİŞ, 1 KOMŞU, 2 KOMŞU** karşılaştırmaları yalnızca *önceden gösterilmiş tahminin ardından doğrulanmış gerçek sonuçlarla* puanlanır. Toplanan eski 500 spin geçmişe dönük tahmin başarısı olarak sayılmaz. Bu üç görünümün son 12'lik listeleri uygulama yeniden açıldığında da geri gelir. Rastgele rulette geçmiş frekanslar gelecekteki sonuçları garanti etmez.

Çevrimdışı regresyon testleri: `python -m unittest -v test_roulette_refresh.py`. Tarayıcı/oyun sitesinin canlı davranışı bu testlerde simüle edilmez.


## V2.9.42 — CANLI DONMA DÜZELTMESİ (GEÇMİŞ / K1 / K2)

Masa açıldığında SON SAYI ve SON 20 doğru görünüp bir el sonra ekranın aynı kalmasının
nedeni, bazı Pragmatic görünümlerinde **sadece 5–8 sayı gösteren** "son sonuçlar" şeridine
8 sayılık kesin eşleşme isteyen aday seçiciydi: ilk okuma çalışıyor, sonraki her el için
hiçbir aday seçilemiyor ve canlı akış tamamen duruyordu.

Yapılanlar:

* `choose_live_dom_candidate` artık kısa şeritlerle de çalışır (en az 4 sayılık gerçek
  kesinti kanıtı). Canlı geçmişin koruması yine `update_results` içindeki LIVE LOCK'ta.
* `detect_new_front` boş dilim karşılaştırmasını (ilişkisiz bir listeyi "yeni" sayma)
  kabul etmiyor; yalnızca gerçekten aynı pencerenin devamını yeniler.
* Bir kez bozulan canlı çapa için güvenli kurtarma eklendi: aynı tam pencere üst üste
  geliyorsa ve canlı akış 20 saniyedir sessizse SON 20 bir kez yeniden çapalanır.
  Kazanılan/kaybedilen turlar, K1/K2 istatistikleri ve listeleri bozulmaz.
* GEÇMİŞ sekmesindeki her satırda artık **KAZANDI / KAYBETTİ** bilgisi açıkça yazıyor ve
  her tur için **K1** ve **K2** sonucu ayrı ayrı görünüyor. 1 KOMŞU / 2 KOMŞU sekmelerinin
  satırları ve özetinde de "K1 KAZANDI / K1 KAYBETTİ" ifadesi var, ayrıca "SON TUR" satırı
  son elin K1 ve K2 sonucunu gösteriyor.

Çevrimdışı regresyon testleri: `python -m unittest -v test_roulette_refresh.py`


## V2.9.43 — CANLI GÖRÜNÜM DÜZELTMESİ (PRAGMATIC DIRECT 500/500)

Canlı masada **`PRAGMATIC DIRECT: 500/500`** verisi gelmesine rağmen ekranın tamamen boş
kalabildiği durum düzeltildi. Belirtiler: `MASA SON500: örtüşme doğrulanamadı`,
`MASA ARŞİVİ: bekleniyor`, `SON: --`, `CANLI HAFİZA: 0 spin`, `CANLI SYNC: -`.

Nedeni: `update_table_history_500`, diskteki uzun arşivle örtüşmeyen bir pencereyi reddeden
erken `return` bloğundaydı ve bu blok canlı görünümü kuran bootstrap kodundan **önce**
çalışıyordu. Arşiv başka bir güne/kanala ait olduğunda (veya en başta hiç arşiv yoksa)
oyunun kendi 500'ü her taramada bir daha reddediliyor, ekran hiç açılmıyordu.

Yapılanlar:

* **İlk canlı görünüm yetkisi:** canlı geçmiş boşken ve gelen pencere en az
  `LIVE_BOOTSTRAP_MIN_NUMBERS` (20) sayı içeriyorsa, doğrulanmış oyun penceresi
  geçerli kabul edilir; uzun arşiv bu pencereden yeniden kurulur ve canlı görünüm
  açılır. Durum etiketlerinde `• İLK CANLI GÖRÜNÜM` ve `• ARŞİV YENİDEN KURULDU` yazar.
  Canlı geçmiş kurulduktan sonra LIVE LOCK tam olarak çalışmaya devam eder: örtüşmesi
  doğrulanamayan pencere kurulmuş SON 20'yi değiştiremez.
* **Yön tespiti:** bazı uç noktalar listeyi en eskiden en yeniye verir. Artık
  `orient_window_newest_first` oyunun ekranındaki kazanan sayıdan (canlı sonuç
  rozeti) yönü belirler; ayrıca masanın kendi SON500 arşivi bağımsız bir kanıt olarak
  kullanılır. Böylece ters sıralı ilk pencere de doğru kurulur ve sonraki eller
  donmadan ilerlemeye devam eder.
* **Ayna penceresi kontrolü:** pencere reddedilmeden önce ters çevrilmiş hâli de
  arşive karşı denenir; en eskiden en yeniye veren ağ yanıtı böylece tanınır.

Çevrimdışı regresyon testleri: `python -m unittest -v test_roulette_refresh.py`


## V2.9.44 — CANLI TAHMİN DÜZELTMESİ (en eskiden yeniye veren uç nokta)

Masa açık, veri geliyor ama **tahmin yürütülmüyor**: GEÇMİŞ / K1 / K2 hiç artmıyor,
tur sayacı 0'da kalıyor ve ekran aynı kalıyordu.

Nedeni: `detect_new_front()` yalnızca **ileri yönlü** karşılaştırma yapıyordu. Bazı
Pragmatic/operatör uç noktaları `last20Results` listesini **en eskiden en yeniye**
(en yeni sonda) veriyor; bu yüzden her el LIVE LOCK'a takılıyor, canlı geçmiş hiç
güncellenmiyor ve tahmin hiç puanlanmıyordu.

Yapılanlar:

* `update_results()` artık LIVE LOCK'a düşmeden önce **ayna pencereyi** (ters
  çevrilmiş listeyi) de dener. İlişkisiz bir liste iki yönde de eşleşemez, bu yüzden
  LIVE LOCK tam korumasını korur (testle sabitlendi).
* `detect_new_front()` güvenlik açığı kapatıldı: eşleşme eşiği `remaining` ile
  kırpıldığı için kısa bir kuyrukta bar **tek sayıya** düşüyor ve tesadüfen eşleşen
  bir sayı "birçok yeni spin" olarak kanıtlanıyordu. Artık eşik sabit; kısa kuyruk
  hiç kanıt kabul edilmiyor.
* GEÇMİŞ sekmesindeki tur sayacı ve K1/K2 kazanma sayaçları bu düzeltmeyle birlikte
  gerçekten ilerliyor.

Çevrimdışı regresyon testleri: `python -m unittest -v test_roulette_refresh.py`
