import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.auH_err

/-!
# `Work.Resample.buQWhints`: reading notes for the `buQW` stage lemmas

**This file contains no mathematics to use; it is a set of notes** (plus two trivial lemmas about
`auH`).  It is meant to be imported by the stage lemmas `buQWsel`, `buQWrounds`, `buQWscale`.

## 0. The overall shape of `Work.Resample.buQW`

`buQW` (the target) asks for ONE program `q` with, for all parameters,
`cvecVal u :: buTabList p α s t hs hcop ++ rest ↦ cvecVal w :: buTabList ... ++ rest`
where `w = buPhiL p α s t hs hcop u`, i.e. the composition

`w = buPermL (buDscL buWd (buJsumL buWt (buSelL u)))`

(`buQWdefs.lean`).  The three stages below are the pieces; they take their table entries as explicit
top-of-stack arguments (not as the table), and a generic value list `rest` below, so that the
*assembly* (`buQW.lean`) is only responsible for copying the table entries into place.

* `buQWsel`      : `cvecVal u :: buKeysT s t :: .int s :: rest ↦ cvecVal (buSelL s t u) :: rest`
* `buQWrounds`   : `buSignsT :: cvecVal v :: cvecVal v :: buColsT :: .int s :: .int p :: rest ↦
                    cvecVal (buJsumL buWt p s m n v) :: rest`
* `buQWscale`    : `cvecVal u :: buWdL :: buKeysS :: .int s :: .int p :: rest ↦
                    cvecVal (buPermL (buDscL buWd p s u)) :: rest`

## 1. Program sketch (library words only; no `self` except inside the products)

All stages are compositions of `KernelLib`/`LayoutLib`/`IntLib` words, whose programs are obtained
from the hypotheses `KL IL LL FL` (`KL.pick/roll/drop/dup/swap/zipWith/mapList/foldList/loop/consV/
unconsV/ifZero/ifNil/pushVal`, `LL.length/reverse/append/take/drop/sortByKey`, `IL.add/sub/neg/mulS/
tdiv/tmod/fmod/shrT/lt/eq/pow2`, …).  Everything is `WordR`-composition, no raw `Ev` needed, because
`buInV`/range hypotheses keep all value sizes bounded by explicit functions of `p`.

**`buQWsel`**: `pick` the key list up, `KL.zipWith` with the element word `KL.consV` (making records
`cons (int (egLam i)) (cfxVal uᵢ)`), `LL.sortByKey`, then `.int s` must be on top of the sorted list:
`pick` it, `LL.take`, `drop` it, and `KL.mapList` with a word turning
`cons (int ℓ) (cons (int x) (int y))` into `cfxVal (x tdiv 2, y tdiv 2)`
(`KL.unconsV`, `KL.drop`, `pushVal (int 2)`, `IL.tdiv` twice, `KL.swap`, `KL.consV`).
The *mathematical* content is `buQWsort` + `buQWkey` (both available): the sorted list has the `s`
smallest keys `0…s-1` in order, the record with key `ℓ` is the one with `i = egNu s t ℓ`.

**`buQWrounds`**: an outer `KL.foldList` over the sign list (`buSignsT` is exactly the `Val` list of
`List.range (egN-1) |>.map (fun j => (-1)^(j+1))`), with accumulator
`acc = [cvecVal v_k, cvecVal acc_k] ++ buColsT :: .int s :: .int p :: rest`, and a body which
(i) takes the sign `σ` at the top, (ii) computes `v' = buRoundL buWt p s (egM p α) v_k` and
(iii) replaces the accumulator by `[cvecVal v', cvecVal (buAddV acc_k (buSMulV σ v'))]`.
Step (ii) is an inner `KL.foldList` over the columns `buColsT` (whose elements are
`cons (int h) (ofList col)`), with accumulator `[cvecVal v_k, cvecVal Z]`, `Z = replicate s (0,0)`,
and a body doing, for one column `h`:
* `unconsV`, `IL.fmod` to get `h % s` (the divisor `int s` is available; `Int.fmod` for `0 < s`
  gives the Euclidean remainder in `[0,s)`), `KL.dup` the vector, `LL.drop`, `LL.take`, `LL.append`
  to build `buRot ((h % s).toNat) v`;
* `KL.zipWith` the rotated vector with the column (element word: `cons (int c) (cfxVal z)` is split by
  `unconsV` and the two coordinates are multiplied by `c` with `Cmd.self` — the operands have
  `natAbs ≤ 2^(p+2)`, so `mulSize < N` and the cost is `Cm (mulSize) ≤ Cm (Kc*p)`);
* `KL.zipWith` the accumulator with that with `IL.add` coordinatewise (`KL.consV` to rebuild).
Finally `KL.mapList` with a word dividing both coordinates by `2^p` (`IL.shrT` with `int p`), and the
last copy of `v` is `KL.drop`ped.  The number of rounds is `egN - 1`, i.e. automatically the length
of the sign list.

**`buQWscale`**: `KL.zipWith` (`buWdL` with the vector) with an element word doing
`tdiv (Wd*x) 2^p`, `tdiv (Wd*y) 2^p` (`Cmd.self` twice, then `IL.shrT` with `int p`, `KL.consV`);
then the same label-sort-take-strip as in `buQWsel` with `buKeysS`, using that `i ↦ (t*i) % s` is a
permutation (`egKeyS_inj`/`egKeyS_surj`/`egGam_spec` of `sliceB1defs.lean`); the records are
`cons (int ((t i) % s)) (cfxVal dᵢ)` and after `LL.sortByKey` position `j` holds the record with key
`j`, i.e. the entry `egGam j` (use `buQWsort` with `s := s`, then strip the keys with `KL.mapList` +
`KL.unconsV` + `KL.drop`).

## 2. The size invariants (what the stage hypotheses are for)

`buIn B z : z.1^2 + z.2^2 ≤ B^2` is the disc of radius `B`; `buInV B v` for vectors.
`buIn (2^p) z ↔ HvdH.inDisc p z`.  The chain is
`buQWsel` : `2^p ↦ 2^(p-1)+2` (halving), `buQWrounds` : `2^(p-1)+2 ↦ 2^(p+1)`, `buQWscale` :
`2^(p+1) ↦ 2^p`.  Helper lemmas in `buQWdefs.lean`: `buInV_coord` (`|zᵢ| ≤ B`), `buIn_mono`,
`buIn_add` (the ℓ² triangle inequality, proved through `Complex`), `inDisc_iff_buIn`.

## 3. The weights `buWt`/`buWd` (why the hypotheses are what they are)

* `buWt p α s t ℓ h = tdiv (auH p (-(buZ)) (auNstep p)) (2^(auPrec p - p))` when the guard
  `buZ ≤ (p+10)·2^(auPrec p)` holds, and `0` otherwise.  The Horner recursion satisfies
  `auH p Z j ≈ 2^(auPrec p) * exp (Z / 2^(auPrec p))` (see `auH_err`; `#eval` confirms:
  `auH 1 (2^103) 206 / 2^103 = 2.718…`, `auH 1 (-2^103) 206 / 2^103 = 0.367…`,
  `auH 1 (-4·2^103) 206 / 2^103 = 0.0183…`).  Hence
  `buWt ≈ 2^p · exp (-π α² buN/s²) = 2^p · egW` — this is `buWtAcc`, the accuracy of the weights;
  `buQWrowsum` derives from it the row-sum bound `Σ_{h ∈ egHset (egM p α)} |buWt| ≤ 2^p/2 + 8·egM`
  used as `hrow` in `buQWrounds` (the round contracts: `|v'| ≤ (1/2 + tiny)|v| + √2`).
* `buWd p α s t ℓ = tdiv (auH p (buZb p α s t ℓ) (auNstep p)) (2^(auPrec p - p + 2α² - 2))`
  (note `buZb ≥ 0`), so `buWd ≈ 2^p · exp (+π α² β_ℓ²) / 2^(2α²-2)`, matching the paper's
  `D' = diag(e^{+πα²β²})/2^{2α²-2}` (`HvdH.diagD'`) — a *growing* exponential in `β_ℓ²`.  With
  `|β_ℓ| ≤ 1/2` the maximum is `2^p·e^{πα²/4}/2^{2α²-2} = 2^{2-0.867α²}·2^p`, which for `α = 2` is
  `e^π/64 ≈ 0.3616`, and for `α ≥ 3` is `< 2^{-5}`.  (Beware: the definition of `buWd` in
  `sliceBu.lean` had the *opposite* sign until 2026-09-26 19:33; `Work.Resample.buWdAcc` states the
  accuracy of the *current* definition and is consistent with it.)  The clean provable consequence
  used by the stage lemmas is `8·|buWd p α s t ℓ| ≤ 3·2^p` (for `α ≥ 2`, all `p`).

## 4. Costs

Shapes are absolute constants times the displayed factors; `Kc` is chosen by the prover and is
absorbed by the final `K` of `buQW`.  Products by `self` are only used on operands of `natAbs ≤ 2^(p+2)`
(hence `mulSize ≤ p+3 < N` from `Kc*p < N`), so each costs `≤ Cm (Kc*p)` by monotonicity of `Cm`.
-/

-- (no lemmas here: this module is documentation only)
