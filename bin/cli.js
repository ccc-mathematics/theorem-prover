#!/usr/bin/env node
// 用法:
//   node cli.js --demo                      執行內建範例
//   node cli.js problem.txt                 從檔案讀取
//   node cli.js -e "前提1" "前提2" "|- 結論"   直接在命令列輸入
//   cat problem.txt | node cli.js           從標準輸入讀取
// 檔案格式:每行一個前提;以 |- 開頭的行是結論(可省略,省略則檢查前提是否矛盾);# 開頭為註解
const fs = require('fs');
const P = require('../src/prover.js');
const a = process.argv.slice(2);

function run(lines, name) {
  const premises = []; let goal = '';
  for (const raw of lines) {
    const l = raw.trim();
    if (!l || l.startsWith('#')) continue;
    if (l.startsWith('|-') || l.startsWith('⊢')) goal = l.replace(/^(\|-|⊢)/, '').trim();
    else premises.push(l);
  }
  if (name) console.log(`\n== ${name}`);
  try { console.log(P.format(P.prove(premises, goal || null))); }
  catch (e) { console.log('錯誤:' + e.message); }
}

if (a[0] === '--demo' || (!a.length && process.stdin.isTTY)) {
  for (const e of P.examples) run([...e.premises, '|- ' + e.goal], e.name);
} else if (a[0] === '-e') run(a.slice(1));
else run(fs.readFileSync(a.length ? a[0] : 0, 'utf8').split('\n'));
