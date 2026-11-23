// A stack virtual machine for make.fun's tiny stack ISA v1.
// For every instance <id> in the input dir it runs program.bin on input.bin and writes
// stdout.bin (the exact bytes written) and exit.txt (halt/exit code, or a trap's code).
// Machine: 32-bit wrapping integers, 256-value stack, 64-deep call stack, 256 words of
// memory, at most 1,000,000 steps and 65,536 output bytes per program.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const enc = new TextEncoder();

// Opcode byte -> [immediate bytes, values popped, values pushed]; unlisted bytes trap 5.
const T: [number, number, number][] = [];
for (const [b, i, p, q] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2], [5, 0, 2, 2],
  [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1],
  [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1],
  [26, 0, 2, 1], [27, 0, 1, 1], [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1],
  [33, 0, 2, 1], [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1],
  [83, 0, 1, 0],
]) T[b] = [i, p, q];

// Runs one program to its end; returns [output bytes, exit code].
function run(P: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = P.length;
  const S = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code: number): [Uint8Array, number] => [out.slice(0, olen), code];
  for (;;) {
    // One step, in the ISA's order: step limit, pc range, known opcode, immediate fits.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const b = P[pc], op = T[b];
    if (op === undefined) return done(5);
    if (pc + op[0] >= n) return done(9);
    steps++;
    const nx = pc + 1 + op[0];
    if (sp < op[1]) return done(2); // stack underflow, checked before the instruction acts
    if (sp - op[1] + op[2] > 256) return done(3); // stack overflow
    pc = nx;
    if (b === 0) return done(0); // HALT
    if (b === 1) { S[sp++] = (P[nx - 1] << 24) >> 24; continue; } // PUSH8, sign-extended
    if (b === 2) { S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); continue; } // PUSH32
    if (b === 3) { sp--; continue; } // POP
    if (b === 4) { S[sp] = S[sp - 1]; sp++; continue; } // DUP
    if (b === 5) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; continue; } // SWAP
    if (b === 6) { S[sp] = S[sp - 2]; sp++; continue; } // OVER
    if (b === 7) { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; continue; } // ROT
    if (b === 23) { S[sp - 1] = -S[sp - 1] | 0; continue; } // NEG, wraps
    if (b === 27) { S[sp - 1] = ~S[sp - 1]; continue; } // NOT
    if ((b >= 16 && b <= 22) || (b >= 24 && b <= 26) || (b >= 28 && b <= 30) || (b >= 32 && b <= 34)) {
      // Two-operand arithmetic, bitwise, shift and comparison opcodes: ( a b -- r ).
      const y = S[sp - 1], x = S[sp - 2];
      let r = 0;
      if (b === 16) r = (x + y) | 0; // ADD
      else if (b === 17) r = (x - y) | 0; // SUB
      else if (b === 18) r = Math.imul(x, y); // MUL, low 32 bits of the exact product
      else if (b === 19) { if (y === 0) return done(4); r = x === -2147483648 && y === -1 ? x : (x / y) | 0; } // DIV
      else if (b === 20) { if (y === 0) return done(4); r = y === -1 ? 0 : x % y | 0; } // MOD, sign of x
      else if (b === 21) { if (y === 0) return done(4); r = Math.floor((x >>> 0) / (y >>> 0)) | 0; } // DIVU
      else if (b === 22) { if (y === 0) return done(4); r = (x >>> 0) % (y >>> 0) | 0; } // MODU
      else if (b === 24) r = x & y; // AND
      else if (b === 25) r = x | y; // OR
      else if (b === 26) r = x ^ y; // XOR
      else if (b === 28) r = x << (y & 31); // SHL, only the low 5 bits of the count
      else if (b === 29) r = x >> (y & 31); // SHR, arithmetic
      else if (b === 30) r = (x >>> (y & 31)) | 0; // SHRU, logical
      else if (b === 32) r = x === y ? 1 : 0; // EQ
      else if (b === 33) r = x < y ? 1 : 0; // LT, signed
      else r = (x >>> 0) < (y >>> 0) ? 1 : 0; // LTU, unsigned
      sp -= 2;
      S[sp++] = r;
      continue;
    }
    if (b === 48 || b === 49 || b === 50) {
      // JMP / JZ / JNZ: target is next + signed 16-bit offset, unchecked until the next step.
      const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
      let take = true;
      if (b !== 48) { const v = S[--sp]; take = b === 49 ? v === 0 : v !== 0; }
      if (take) pc = nx + rel;
      continue;
    }
    if (b === 51) { // CALL: the immediate is an unsigned absolute address
      if (csp === 64) return done(7);
      C[csp++] = nx;
      pc = P[nx - 2] | (P[nx - 1] << 8);
      continue;
    }
    if (b === 52) { if (csp === 0) return done(8); pc = C[--csp]; continue; } // RET
    if (b === 64) { const a = S[sp - 1]; if (a < 0 || a > 255) return done(6); S[sp - 1] = M[a]; continue; } // LOAD
    if (b === 65) { // STORE: ( v addr -- )
      const a = S[sp - 1], v = S[sp - 2];
      if (a < 0 || a > 255) return done(6);
      sp -= 2;
      M[a] = v;
      continue;
    }
    if (b === 80) { // PRINT: decimal ASCII; a print past the output limit writes nothing
      const bytes = enc.encode(String(S[sp - 1]));
      if (olen + bytes.length > 65536) return done(11);
      sp--;
      out.set(bytes, olen);
      olen += bytes.length;
      continue;
    }
    if (b === 81) { if (olen + 1 > 65536) return done(11); out[olen++] = S[--sp] & 255; continue; } // PUTC
    if (b === 82) { S[sp++] = ip < inp.length ? inp[ip++] : -1; continue; } // IN, -1 past the end
    if (b === 83) return done(S[--sp] & 255); // EXIT, low byte only
  }
}

for (const id of readdirSync(I).sort()) {
  const program = readFileSync(join(I, id, 'program.bin'));
  let input: Uint8Array = new Uint8Array(0);
  try { input = readFileSync(join(I, id, 'input.bin')); } catch { /* no input file: empty input */ }
  const [stdout, code] = run(program, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), String(code) + '\n');
}
