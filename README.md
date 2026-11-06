# 歸結法定理證明器

一階邏輯自動證明器:否定結論後以歸結法(resolution)搜尋矛盾,支援等號(paramodulation)。不依賴任何套件,需要 Node.js 15 以上。

## 目錄結構

    theorem-prover/
    ├── src/prover.js          核心:解析器、子句化、合一、歸結、等式替換(Node 與瀏覽器共用)
    ├── bin/cli.js             命令列介面
    ├── web/template.html      網頁介面原始檔
    ├── web/index.html         建置後的單檔網頁版(直接用瀏覽器開啟)
    ├── scripts/build-web.js   把 prover.js 內嵌進網頁
    ├── examples/*.txt         範例問題檔
    └── test/test.js           範例測試

## 使用

    npm run demo                                   # 執行內建範例
    node bin/cli.js examples/socrates.txt          # 從檔案讀取
    node bin/cli.js -e "forall x. (P(x) -> Q(x))" "P(a)" "|- Q(a)"
    npm test                                       # 跑測試
    npm run build                                  # 修改 src 或 web/template.html 後重新產生 web/index.html

問題檔格式:每行一個前提,`|-` 開頭的行是結論(省略則檢查前提是否矛盾),`#` 開頭是註解。

## 語法

`~` 否定、`&` 且、`|` 或、`->` 蘊含、`<->` 若且唯若、`forall x.`、`exists x.`、`a = b`、`a != b`。
也接受 ∀ ∃ ¬ ∧ ∨ → ↔。被量詞綁定的名稱是變數,其餘名稱是常數或函數。

## 作為函式庫

    const P = require('./src/prover.js');
    const r = P.prove(['forall x. (Man(x) -> Mortal(x))', 'Man(socrates)'], 'Mortal(socrates)');
    console.log(P.format(r));   // r.status 為 proved / saturated / timeout

## 限制

等式推論沒有項排序與化簡,較難的代數題可能逾時;預設上限為 10 秒、20000 個子句。
