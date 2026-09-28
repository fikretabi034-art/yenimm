@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title Roulette Pro AI Baslat

if not exist "%~dp0roulette_v1.py" goto NEED_EXTRACT
if not exist "%~dp0resolve_last_roulette.py" goto NEED_EXTRACT

set "PYTHON_EXE="
set "PYTHON_ARGS="

rem Python bulma bolumu
for /f "delims=" %%P in ('where py 2^>nul') do (
    if not defined PYTHON_EXE (
        "%%P" -3.11 -c "import sys" >nul 2>nul
        if not errorlevel 1 (
            set "PYTHON_EXE=%%P"
            set "PYTHON_ARGS=-3.11"
        )
    )
)

if not defined PYTHON_EXE (
    for /f "delims=" %%P in ('where python 2^>nul') do (
        if not defined PYTHON_EXE (
            "%%P" -c "import sys; raise SystemExit(0 if sys.version_info >= (3,11) else 1)" >nul 2>nul
            if not errorlevel 1 (
                set "PYTHON_EXE=%%P"
                set "PYTHON_ARGS="
            )
        )
    )
)

if not defined PYTHON_EXE (
    for /f "delims=" %%P in ('where python3.11 2^>nul') do (
        if not defined PYTHON_EXE (
            "%%P" -c "import sys" >nul 2>nul
            if not errorlevel 1 (
                set "PYTHON_EXE=%%P"
                set "PYTHON_ARGS="
            )
        )
    )
)

if not defined PYTHON_EXE (
    if exist "%LOCALAPPDATA%\Programs\Python\Python311\python.exe" (
        "%LOCALAPPDATA%\Programs\Python\Python311\python.exe" -c "import sys" >nul 2>nul
        if not errorlevel 1 (
            set "PYTHON_EXE=%LOCALAPPDATA%\Programs\Python\Python311\python.exe"
            set "PYTHON_ARGS="
        )
    )
)

if not defined PYTHON_EXE (
    if exist "%ProgramFiles%\Python311\python.exe" (
        "%ProgramFiles%\Python311\python.exe" -c "import sys" >nul 2>nul
        if not errorlevel 1 (
            set "PYTHON_EXE=%ProgramFiles%\Python311\python.exe"
            set "PYTHON_ARGS="
        )
    )
)

if not defined PYTHON_EXE (
    if exist "%ProgramFiles(x86)%\Python311\python.exe" (
        "%ProgramFiles(x86)%\Python311\python.exe" -c "import sys" >nul 2>nul
        if not errorlevel 1 (
            set "PYTHON_EXE=%ProgramFiles(x86)%\Python311\python.exe"
            set "PYTHON_ARGS="
        )
    )
)

if not defined PYTHON_EXE (
    echo.
    echo Python 3.11 bulunamadi.
    echo.
    echo CMD acip sunu kontrol et:
    echo python --version
    echo.
    echo Python kuruluysa ama burada bulunmuyorsa Python'u tekrar kurarken:
    echo Add python.exe to PATH secenegini isaretle.
    echo.
    pause
    exit /b 1
)

echo Python bulundu:
echo "%PYTHON_EXE%" %PYTHON_ARGS%
echo.

set "CHROME="
if exist "%ProgramFiles%\Google\Chrome\Application\chrome.exe" set "CHROME=%ProgramFiles%\Google\Chrome\Application\chrome.exe"
if not defined CHROME if exist "%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe" set "CHROME=%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe"
if not defined CHROME if exist "%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe" set "CHROME=%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe"

if not defined CHROME (
    echo Google Chrome bulunamadi.
    pause
    exit /b 1
)

:START_ALL
set "LASTURL="

for /f "usebackq delims=" %%U in (`"%PYTHON_EXE%" %PYTHON_ARGS% "%~dp0resolve_last_roulette.py"`) do if not "%%U"=="" set "LASTURL=%%U"

if defined LASTURL (
    echo [AUTO] Canli casino girisi aciliyor...
    start "" "%CHROME%" ^
        --remote-debugging-address=127.0.0.1 ^
        --remote-debugging-port=9222 ^
        --remote-allow-origins=* ^
        --user-data-dir="%LOCALAPPDATA%\PragmaticBlackjackChrome" ^
        --start-maximized ^
        "%LASTURL%"
) else (
    echo [AUTO] Kayitli rulet adresi bulunamadi. Chrome aciliyor.
    start "" "%CHROME%" ^
        --remote-debugging-address=127.0.0.1 ^
        --remote-debugging-port=9222 ^
        --remote-allow-origins=* ^
        --user-data-dir="%LOCALAPPDATA%\PragmaticBlackjackChrome" ^
        --start-maximized
)

timeout /t 2 /nobreak >nul

"%PYTHON_EXE%" %PYTHON_ARGS% "%~dp0roulette_v1.py"
set "RC=%ERRORLEVEL%"

if "%RC%"=="77" (
    echo.
    echo [AUTO RECOVER] Yenileme uyarisi algilandi.
    echo [AUTO RECOVER] Chrome kapatiliyor ve program tekrar baslatiliyor...
    powershell -NoProfile -ExecutionPolicy Bypass -Command "$p=Get-CimInstance Win32_Process -Filter \"Name='chrome.exe'\"; foreach($x in $p){ if($x.CommandLine -like '*PragmaticBlackjackChrome*'){ Stop-Process -Id $x.ProcessId -Force -ErrorAction SilentlyContinue } }" >nul 2>&1
    timeout /t 4 /nobreak >nul
    goto START_ALL
)

if not "%RC%"=="0" (
    echo.
    echo Program hata ile kapandi. Kod: %RC%
    echo.
    pause
)

endlocal
exit /b %RC%

:NEED_EXTRACT
echo.
echo ================================================================
echo PROGRAM ZIP / RAR ICINDEN CALISTIRILAMAZ
echo ================================================================
echo.
echo Once ZIP dosyasini tamamen klasore cikart.
echo Sonra bu BAT dosyasini cikan klasorun icinden calistir.
echo.
pause
endlocal
exit /b 2
