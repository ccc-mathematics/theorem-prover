// 把 src/prover.js 內嵌進 web/template.html,產生單檔的 web/index.html
const fs = require('fs'), path = require('path');
const root = path.join(__dirname, '..');
const html = fs.readFileSync(path.join(root, 'web/template.html'), 'utf8')
  .split('/*PROVER*/').join(fs.readFileSync(path.join(root, 'src/prover.js'), 'utf8'));
fs.writeFileSync(path.join(root, 'web/index.html'), html);
console.log('已產生 web/index.html');
