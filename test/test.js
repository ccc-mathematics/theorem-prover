const P = require('../src/prover.js');
let fail = 0;
for (const e of P.examples) {
  const want = e.name.includes('非定理') ? 'saturated' : 'proved';
  const got = P.prove(e.premises, e.goal || null).status;
  console.log(`${got === want ? 'PASS' : 'FAIL'}  ${e.name}  (${got})`);
  if (got !== want) fail++;
}
process.exit(fail ? 1 : 0);
