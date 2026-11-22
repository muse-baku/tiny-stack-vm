// Tiny stack VM for make.fun's tiny stack ISA (kit's ISA.md): one run answers
// every instance, writing stdout.bin and exit.txt (halt, EXIT or trap) per id.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// Opcode facts by byte: immediate length (-1: no such opcode), pops, pushes.
const IMM = new Int8Array(256).fill(-1), POP = new Uint8Array(256), PSH = new Uint8Array(256);
const def = (o, i, p, q) => { IMM[o] = i; POP[o] = p; PSH[o] = q; };
def(0, 0, 0, 0); def(1, 1, 0, 1); def(2, 4, 0, 1); def(3, 0, 1, 0); def(4, 0, 1, 2);
def(5, 0, 2, 2); def(6, 0, 2, 3); def(7, 0, 3, 3); def(23, 0, 1, 1); def(27, 0, 1, 1);
for (const o of [16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34]) def(o, 0, 2, 1);
def(48, 2, 0, 0); def(49, 2, 1, 0); def(50, 2, 1, 0); def(51, 2, 0, 0); def(52, 0, 0, 0);
def(64, 0, 1, 1); def(65, 0, 2, 0); def(80, 0, 1, 0); def(81, 0, 1, 0); def(82, 0, 0, 1); def(83, 0, 1, 0);
const enc = new TextEncoder();
function run(P, inp) {
  const n = P.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = P[pc], imm = IMM[op];
    if (imm < 0) return done(5);
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < POP[op]) return done(2);
    if (sp - POP[op] + PSH[op] > 256) return done(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (P[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24: case 25:
      case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) return done(4); r = b === -1 ? 0 : a % b; }
        else if (op === 21) { if (!b) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        D[sp - 2] = r; sp--;
        break;
      }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: case 49: case 50: {
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        if (op === 48 || (op === 49 ? D[--sp] === 0 : D[--sp] !== 0)) pc = nx + rel;
        break;
      }
      case 51:
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 52:
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        M[a] = D[sp - 2]; sp -= 2;
        break;
      }
      case 80: {
        const bs = enc.encode(String(D[sp - 1]));
        if (olen + bs.length > 65536) return done(11);
        out.set(bs, olen); olen += bs.length; sp--;
        break;
      }
      case 81:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
