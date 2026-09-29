import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.axisDefs
import Submission.Work.SynFFT.cvecsInj
import Submission.Work.SynFFT.axisStepDefs
import Submission.Work.SynFFT.axisParamsDown
import Submission.Work.SynFFT.axisParamsUp
import Submission.Work.SynFFT.axisSwap23
import Submission.Work.SynFFT.axisApproxSLScat
import Submission.Work.SynFFT.axisScatInDisc
import Submission.Work.SynFFT.scatterCvecs
import Submission.Work.SynFFT.cvecsFlattenBlocks
import Submission.Work.SynFFT.fftSliceWord
import Submission.Work.SynFFT.sliceGood
import Submission.Work.SynFFT.axisFinalScat
import Submission.Work.SynFFT.axisTranspose

/-!
# `Work.SynFFT.HasAxis` — one axis pass of the synthetic FFT (route and status)

## The statement to prove

`HasAxis` (kit2.lean) asks for a word applying the slice word `HasFFT1` to every `i`-slice of the
`A × t × B` decomposition of the flat array and reassembling the result in the same flat layout,
at cost

```
K * N * (r+1) * (p+1) * (k+1) + K * N * (r+1) * (p+1) * ((N).size + 2) + K,   N = A*t*B.
```

## Why `HvdH.LayoutLib.applyAlong` cannot be used (this is the whole difficulty)

The area's design (`Submission/Work/SynFFT/STATUS.md`) says `HasAxis` is "one `applyAlong` of the
slice word".  That is *not provable*: `applyAlong`'s cost (Interfaces.lean, proved by
`Work.Layout.applyAlongWord`) contains the factor `(A'*B'*(m+n+1)).size + 1` **twice**, and the
specification forces `m = n = t` on all `A*B` slices, so `A'*B'*(m+n+1) ≥ 2N` and every
instantiation pays `≥ N·(log N)²`.  The target above allows only `N·(r+1)(p+1)·(k+1+log N)`, so the
intended derivation needs `log N ≲ (r+1)(p+1)`; nothing in `HasAxis` bounds `A` (only `0 < A`,
`t = 2^k`, `t ∣ 2r`, `2r < 2^p`), while `K` is chosen *before* the universal quantifiers over
`A,t,B`.  Concretely, for `r = 2, p = 3, t = 2, k = 1, B = 1, A = 2^m` (all hypotheses hold) the
ratio (applyAlong cost)/(target) is `≈ 0.2·m`, unbounded.  **`HasAxis` is nevertheless TRUE**: the
axis pass exists; only the `applyAlong` *route* is too expensive.

## The route used here: gather with a *row-recursive* transpose

Replace the sort-based `applyAlong` by the transpose `Work.SynFFT.HasAxisTranspose`
(axisDefs.lean), which costs one pass over the encoded data per row-split level, i.e.
`O(N (L+1) log t + N log N)`.  The pipeline is (`;;;` = `Cmd.seq`):

```
T (shape A,t,B)      -- gather: flat ↦ slice-major (`List.flatten (slices A t B es)`)
axisParamsDown       -- move the parameter block `A t B` below `k sgn r p`
pick 6               -- copy `int t` to the top
chunksOf t           -- the A*B slices as values
mapList HasFFT1      -- apply the slice word to every slice (parameters in `rest`)
flatten              -- back to the slice-major flat list
axisParamsUp         -- restore `A B t` below the array (for the scatter's parameter order)
T (shape A,B,t)      -- scatter (`List.flatten (slices A B t ·)` is the transpose of the
                     -- transpose, i.e. the permutation `i ↦ (i/(t*B)*B + i%B)*t + i/B%t`)
axisSwap23           -- restore the parameter order `A t B k sgn r p`
```

Each shuffling stage is a constant number of `KLib.roll`/`KLib.pick`/`KLib.drop`/`KLib.swap`,
hence `O(N (L+1))`; the slice word contributes `K1*N*(r+1)(p+1)(k+1)`; everything fits the target
with room to spare (`L = r*(2p+6)+1 ≤ 8(r+1)(p+1)`, `t.size ≤ N.size`, `N.size+2 ≥ 3`).

## Status

**The assembly is done** (`Work.SynFFT.hasAxis_of_transpose`, below): the pipeline is built out of
`KLib`, `LayoutLib`, `HasFFT1`, `AxisTSlicesProp` and the transpose `HasAxisTranspose`, one
`WordR` per stage, composed with `MrgKit.WordR_seqC` / the local `WordR_seqE` and weakened with
`MrgKit.WordR_weaken`; the cost is folded into the target with the budget `axisBd` and its
elementary bounds (`bd_ge_*`).  All the arithmetic is in this file (`costGather`, `costGather2`,
`costPrms`, `costPick`, `costChunks`, `costMap`, `costFlatten`, `costSwap2`).

The three pieces of the assembly that are *not* in this file are proved in
`Submission/Work/SynFFT/`:

| piece | file | statement |
|---|---|---|
| `fftSliceWord` | `fftSliceWord.lean` | the whole `HasFFT1` word, packaged with `SlPre`/`SlPost` |
| `sliceGood` | `sliceGood.lean` | the slice of the chunk list is the slice of the array (from `Forall₂ SlPost`) |
| `axisFinalScat` | `axisFinalScat.lean` | the scatter of the per-slice results is in-disc and approximates `axisT` |

so that

```
hasAxis := hasAxis_of_transpose hk hl axisTranspose h1 (fftSliceWord h1) (...) axisFinalScat
```

**Remaining input:** `Work.SynFFT.axisTranspose : HasAxisTranspose` (`axisTranspose.lean`,
`axisDefs.lean`) -- the layout-transpose word.  *No* route through `HvdH.LayoutLib.applyAlong`
exists, since `applyAlong`'s cost carries `(log N)^2` while `HasAxis` allows only `r·p·log N`
(see the discussion at the top of this file); the transpose is budgeted `O(N(L+1) log t + N log N)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

/-! ## Elementary list facts (used by every step of the assembly) -/

/-- `cvecVal` is injective (immediate from `cvecsInj`). -/
theorem cvecVal_injective : Function.Injective cvecVal := by
  intro u v h
  have h1 : cvecs [u] = cvecs [v] := by simp [cvecs, h]
  simpa using cvecsInj h1

/-- `cvecs` commutes with `++`. -/
theorem cvecs_append (xs ys : List (List (ℤ × ℤ))) :
    cvecs (xs ++ ys) = cvecs xs ++ cvecs ys := by
  simp [cvecs]

/-- `cvecs` is `List.map cvecVal`. -/
theorem cvecs_eq_map (ws : List (List (ℤ × ℤ))) : cvecs ws = ws.map cvecVal := rfl

/-- Reading a `cvecs` list at an in-range index. -/
theorem getElem_cvecs (ws : List (List (ℤ × ℤ))) {i : ℕ} (hi : i < ws.length) :
    (cvecs ws)[i]'(by simpa [cvecs] using hi) = cvecVal (ws[i]'hi) := by
  simp [cvecs]

/-- `List.getD` of a `cvecs` list at an in-range index. -/
theorem getD_cvecs (ws : List (List (ℤ × ℤ))) {i : ℕ} (hi : i < ws.length) (b : Val) :
    List.getD (cvecs ws) i b = cvecVal (List.getD ws i []) := by
  have h1 : i < (cvecs ws).length := by simpa [cvecs] using hi
  rw [List.getD_eq_getElem (cvecs ws) b h1, List.getD_eq_getElem ws [] hi]
  exact getElem_cvecs ws hi

/-- `ofList` (the `cons`-chain encoding of a list) is injective. -/
theorem ofList_injective : Function.Injective ofList := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp [ofList] at h
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := by
        simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ih h'.2]


/-! ## Cost arithmetic for the assembly -/

theorem Npos (A t B : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) : 0 < A * t * B := by
  positivity

theorem t_le_N (A t B : ℕ) (hA : 0 < A) (hB : 0 < B) : t ≤ A * t * B := by
  have hAB : 0 < A * B := by positivity
  calc t = 1 * t := (one_mul _).symm
    _ ≤ (A * B) * t := Nat.mul_le_mul_right t hAB
    _ = A * t * B := by ring

theorem A_le_N (A t B : ℕ) (ht : 0 < t) (hB : 0 < B) : A ≤ A * t * B := by
  have hAB : 0 < t * B := by positivity
  calc A = A * 1 := (Nat.mul_one _).symm
    _ ≤ A * (t * B) := Nat.mul_le_mul_left A hAB
    _ = A * t * B := by ring

theorem B_le_N (A t B : ℕ) (hA : 0 < A) (ht : 0 < t) : B ≤ A * t * B := by
  have hAB : 0 < A * t := by positivity
  calc B = 1 * B := (one_mul _).symm
    _ ≤ (A * t) * B := Nat.mul_le_mul_right B hAB
    _ = A * t * B := by ring

theorem AB_le_N (A t B : ℕ) (ht : 0 < t) : A * B ≤ A * t * B := by
  calc A * B = A * B * 1 := (Nat.mul_one _).symm
    _ ≤ A * B * t := Nat.mul_le_mul_left _ (by omega)
    _ = A * t * B := by ring

theorem k_le_N (A t B k : ℕ) (hA : 0 < A) (hB : 0 < B) (htk : t = 2 ^ k) : k ≤ A * t * B := by
  have h1 : k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
  rw [← htk] at h1
  exact le_trans h1 (t_le_N A t B hA hB)

theorem isz_sgn_le (sgn : ℤ) (h : sgn = 1 ∨ sgn = -1) : isz sgn = 3 := by
  rcases h with h | h <;> simp [isz, h]

/-- `8 (r+1) (p+1)` also dominates `r (2p+6) + 4`. -/
theorem slL_le_rp4 (r p : ℕ) : r * (2 * p + 6) + 4 ≤ 8 * (r + 1) * (p + 1) := by
  nlinarith [Nat.zero_le r, Nat.zero_le p]

/-- Bound on the encoded size of a flat array of `N` in-disc vectors. -/
theorem vsz_rarr_le_bd (A t B r p k v : ℕ) (hN : 0 < A * t * B)
    (hv : v ≤ A * t * B * (r * (2 * p + 6) + 2) + 1) : v ≤ 9 * axisBd A t B r p k := by
  have h1 : A * t * B * (r * (2 * p + 6) + 2) ≤ A * t * B * (8 * (r + 1) * (p + 1)) :=
    Nat.mul_le_mul_left _ (slL_le_rp r p)
  have h2 : A * t * B * (8 * (r + 1) * (p + 1)) = 8 * (A * t * B * (r + 1) * (p + 1)) := by ring
  have h3 : 8 * (A * t * B * (r + 1) * (p + 1)) ≤ 8 * axisBd A t B r p k :=
    Nat.mul_le_mul_left 8 (bd_ge_Nrp A t B r p k)
  have h4 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  omega

/-- `isz` of a natural bounded by `A*t*B`. -/
theorem isz_nat_le_bd (A t B r p k n : ℕ) (hN : 0 < A * t * B) (hn : n ≤ A * t * B) :
    isz (n : ℤ) ≤ axisBd A t B r p k := by
  have h1 : isz (n : ℤ) = n.size + 2 := by simp [isz]
  have h2 : n.size ≤ (A * t * B).size := Nat.size_le_size hn
  have h3 : (A * t * B).size + 2 ≤ axisBd A t B r p k := bd_ge_log' A t B r p k hN
  omega

theorem isz_r_le_bd (A t B r p k : ℕ) (hN : 0 < A * t * B) :
    isz (r : ℤ) ≤ 3 * axisBd A t B r p k := by
  have h1 : isz (r : ℤ) = r.size + 2 := by simp [isz]
  have h2 : r.size ≤ r := (Nat.size_le).mpr Nat.lt_two_pow_self
  have h3 : r + 1 ≤ axisBd A t B r p k := bd_ge_r A t B r p k hN
  have h4 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  omega

theorem isz_p_le_bd (A t B r p k : ℕ) (hN : 0 < A * t * B) :
    isz (p : ℤ) ≤ 3 * axisBd A t B r p k := by
  have h1 : isz (p : ℤ) = p.size + 2 := by simp [isz]
  have h2 : p.size ≤ p := (Nat.size_le).mpr Nat.lt_two_pow_self
  have h3 : p + 1 ≤ axisBd A t B r p k := bd_ge_p A t B r p k hN
  have h4 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  omega

/-- The cost of the gather/scatter transpose. -/
theorem costGather (A t B r p k KT : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) :
    KT * (A * t * B) * (r * (2 * p + 6) + 2) * ((t).size + 1) +
      KT * (A * t * B) * ((A * t * B).size + 1) + KT ≤ 10 * (KT * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h1 : (t).size + 1 ≤ (A * t * B).size + 2 := by
    have := Nat.size_le_size (t_le_N A t B hA hB); omega
  have h2 : r * (2 * p + 6) + 2 ≤ 8 * (r + 1) * (p + 1) := slL_le_rp r p
  have h3 : KT * (A * t * B) * (r * (2 * p + 6) + 2) * ((t).size + 1)
      ≤ 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2))) := by
    calc KT * (A * t * B) * (r * (2 * p + 6) + 2) * ((t).size + 1)
        ≤ KT * (A * t * B) * (8 * (r + 1) * (p + 1)) * ((A * t * B).size + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (KT * (A * t * B)) h2) h1
      _ = 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2))) := by ring
  have h4 : 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2)))
      ≤ 8 * (KT * axisBd A t B r p k) :=
    Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left KT (bd_ge_log A t B r p k))
  have h5 : KT * (A * t * B) * ((A * t * B).size + 1) ≤ KT * axisBd A t B r p k := by
    have hle : (A * t * B).size + 1 ≤ (A * t * B).size + 2 := by omega
    calc KT * (A * t * B) * ((A * t * B).size + 1)
        ≤ KT * (A * t * B) * ((A * t * B).size + 2) := Nat.mul_le_mul_left _ hle
      _ = KT * (A * t * B * ((A * t * B).size + 2)) := by ring
      _ ≤ KT * axisBd A t B r p k := Nat.mul_le_mul_left KT (bd_ge_szN A t B r p k hN)
  have h6 : KT ≤ KT * axisBd A t B r p k := by
    calc KT = KT * 1 := (Nat.mul_one _).symm
      _ ≤ KT * axisBd A t B r p k := Nat.mul_le_mul_left KT (bd_ge_one A t B r p k)
  omega

/-- The cost of the parameter shuffles (`axisParamsDown` / `axisParamsUp`). -/
theorem costPrms (A t B r p k : ℕ) (sgn : ℤ) (Kpd v : ℕ) (hA : 0 < A) (hB : 0 < B)
    (ht : 0 < t) (htk : t = 2 ^ k) (hsgn : sgn = 1 ∨ sgn = -1)
    (hv : v ≤ A * t * B * (r * (2 * p + 6) + 2) + 1) :
    Kpd * (v + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + isz (k : ℤ) + isz sgn +
      isz (r : ℤ) + isz (p : ℤ) + 1) ≤ 24 * (Kpd * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h1 : v ≤ 9 * axisBd A t B r p k := vsz_rarr_le_bd A t B r p k v hN hv
  have h2 : isz (A : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k A hN (A_le_N A t B ht hB)
  have h3 : isz (t : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k t hN (t_le_N A t B hA hB)
  have h4 : isz (B : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k B hN (B_le_N A t B hA ht)
  have h5 : isz (k : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k k hN (k_le_N A t B k hA hB htk)
  have h6 : isz sgn = 3 := isz_sgn_le sgn hsgn
  have h7 : isz (r : ℤ) ≤ 3 * axisBd A t B r p k := isz_r_le_bd A t B r p k hN
  have h8 : isz (p : ℤ) ≤ 3 * axisBd A t B r p k := isz_p_le_bd A t B r p k hN
  have h9 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hsum : v + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + isz (k : ℤ) + isz sgn +
      isz (r : ℤ) + isz (p : ℤ) + 1 ≤ 24 * axisBd A t B r p k := by omega
  calc Kpd * (v + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + isz (k : ℤ) + isz sgn +
      isz (r : ℤ) + isz (p : ℤ) + 1) ≤ Kpd * (24 * axisBd A t B r p k) :=
        Nat.mul_le_mul_left Kpd hsum
    _ = 24 * (Kpd * axisBd A t B r p k) := by ring

/-- The cost of the `pick 6` step. -/
theorem costPick (A t B r p k : ℕ) (sgn : ℤ) (Kp v : ℕ) (hA : 0 < A) (hB : 0 < B)
    (ht : 0 < t) (htk : t = 2 ^ k) (hsgn : sgn = 1 ∨ sgn = -1)
    (hv : v ≤ A * t * B * (r * (2 * p + 6) + 2) + 1) :
    Kp * 7 * (v + isz (k : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + isz (A : ℤ) +
      isz (t : ℤ) + 1) ≤ 170 * (Kp * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h1 : v ≤ 9 * axisBd A t B r p k := vsz_rarr_le_bd A t B r p k v hN hv
  have h2 : isz (k : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k k hN (k_le_N A t B k hA hB htk)
  have h3 : isz sgn = 3 := isz_sgn_le sgn hsgn
  have h4 : isz (r : ℤ) ≤ 3 * axisBd A t B r p k := isz_r_le_bd A t B r p k hN
  have h5 : isz (p : ℤ) ≤ 3 * axisBd A t B r p k := isz_p_le_bd A t B r p k hN
  have h6 : isz (A : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k A hN (A_le_N A t B ht hB)
  have h7 : isz (t : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k t hN (t_le_N A t B hA hB)
  have h8 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hsum : 7 * (v + isz (k : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + isz (A : ℤ) +
      isz (t : ℤ) + 1) ≤ 170 * axisBd A t B r p k := by omega
  calc Kp * 7 * (v + isz (k : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + isz (A : ℤ) +
      isz (t : ℤ) + 1) = Kp * (7 * (v + isz (k : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) +
        isz (A : ℤ) + isz (t : ℤ) + 1)) := by ring
    _ ≤ Kp * (170 * axisBd A t B r p k) := Nat.mul_le_mul_left Kp hsum
    _ = 170 * (Kp * axisBd A t B r p k) := by ring

/-- The cost of `chunksOf t`. -/
theorem costChunks (A t B r p k Kc v : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t)
    (hv : v ≤ A * t * B * (r * (2 * p + 6) + 2) + 1) :
    Kc * (v + (A * t * B / t + 1) * isz (t : ℤ) + 1) ≤ 16 * (Kc * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have hdiv : A * t * B / t = A * B := by
    rw [show A * t * B = (A * B) * t by ring, Nat.mul_div_left _ ht]
  rw [hdiv]
  have h1 : v ≤ 9 * axisBd A t B r p k := vsz_rarr_le_bd A t B r p k v hN hv
  have h2 : (A * B + 1) * isz (t : ℤ) ≤ 6 * axisBd A t B r p k := by
    have hisz : isz (t : ℤ) = t.size + 2 := by simp [isz]
    rw [hisz]
    have hsz : t.size + 2 ≤ 3 * t := by
      have hle : t.size ≤ t := (Nat.size_le).mpr Nat.lt_two_pow_self
      omega
    have h2a : (A * B + 1) * (t.size + 2) ≤ (A * B + 1) * (3 * t) := Nat.mul_le_mul_left _ hsz
    have h2b : (A * B + 1) * (3 * t) = 3 * ((A * B + 1) * t) := by ring
    have h2c : (A * B + 1) * t = A * t * B + t := by ring
    have h2d : A * t * B + t ≤ 2 * (A * t * B) := by
      have := t_le_N A t B hA hB; omega
    have h2e : 2 * (A * t * B) ≤ 2 * axisBd A t B r p k :=
      Nat.mul_le_mul_left 2 (bd_ge_N A t B r p k)
    omega
  have h3 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hsum : v + (A * B + 1) * isz (t : ℤ) + 1 ≤ 16 * axisBd A t B r p k := by omega
  calc Kc * (v + (A * B + 1) * isz (t : ℤ) + 1) ≤ Kc * (16 * axisBd A t B r p k) :=
        Nat.mul_le_mul_left Kc hsum
    _ = 16 * (Kc * axisBd A t B r p k) := by ring

/-- The cost of the `mapList` stage. -/
theorem costMap (A t B r p k K1 Kml : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) :
    (A * B) * ((K1 * t * (r + 1) * (p + 1) * (k + 1) + K1) + Kml * (slL p r t + 1)) + Kml
      ≤ (2 * K1 + 9 * Kml) * axisBd A t B r p k := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have hterm1 : (A * B) * (K1 * t * (r + 1) * (p + 1) * (k + 1))
      ≤ K1 * axisBd A t B r p k := by
    rw [show (A * B) * (K1 * t * (r + 1) * (p + 1) * (k + 1))
        = K1 * (A * t * B * (r + 1) * (p + 1) * (k + 1)) by ring_nf]
    exact Nat.mul_le_mul_left K1 (bd_ge_main A t B r p k)
  have hterm2 : (A * B) * K1 ≤ K1 * axisBd A t B r p k := by
    calc (A * B) * K1 ≤ (A * t * B) * K1 :=
          Nat.mul_le_mul_right K1 (AB_le_N A t B ht)
      _ = K1 * (A * t * B) := by ring
      _ ≤ K1 * axisBd A t B r p k := Nat.mul_le_mul_left K1 (bd_ge_N A t B r p k)
  have hterm3 : (A * B) * (Kml * (slL p r t + 1)) ≤ 8 * (Kml * axisBd A t B r p k) := by
    have hsl : slL p r t + 1 = t * (r * (2 * p + 6) + 2) + 2 := rfl
    rw [hsl]
    have hle : t * (r * (2 * p + 6) + 2) + 2 ≤ t * (r * (2 * p + 6) + 4) := by
      have : (2:ℕ) ≤ 2 * t := by omega
      nlinarith
    calc (A * B) * (Kml * (t * (r * (2 * p + 6) + 2) + 2))
        ≤ (A * B) * (Kml * (t * (r * (2 * p + 6) + 4))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left Kml hle)
      _ = Kml * (A * t * B * (r * (2 * p + 6) + 4)) := by ring
      _ ≤ Kml * (A * t * B * (8 * (r + 1) * (p + 1))) :=
          Nat.mul_le_mul_left Kml (Nat.mul_le_mul_left _ (slL_le_rp4 r p))
      _ = 8 * (Kml * (A * t * B * (r + 1) * (p + 1))) := by ring
      _ ≤ 8 * (Kml * axisBd A t B r p k) :=
          Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left Kml (bd_ge_Nrp A t B r p k))
  have hK : Kml ≤ Kml * axisBd A t B r p k := by
    calc Kml = Kml * 1 := (Nat.mul_one _).symm
      _ ≤ Kml * axisBd A t B r p k := Nat.mul_le_mul_left Kml (bd_ge_one A t B r p k)
  have hsplit : (A * B) * ((K1 * t * (r + 1) * (p + 1) * (k + 1) + K1) +
        Kml * (slL p r t + 1))
      = (A * B) * (K1 * t * (r + 1) * (p + 1) * (k + 1)) + (A * B) * K1 +
        (A * B) * (Kml * (slL p r t + 1)) := by ring
  calc (A * B) * ((K1 * t * (r + 1) * (p + 1) * (k + 1) + K1) + Kml * (slL p r t + 1)) + Kml
      = ((A * B) * (K1 * t * (r + 1) * (p + 1) * (k + 1)) + (A * B) * K1 +
        (A * B) * (Kml * (slL p r t + 1))) + Kml := by rw [hsplit]
    _ ≤ 2 * (K1 * axisBd A t B r p k) + 9 * (Kml * axisBd A t B r p k) := by
        omega
    _ = (2 * K1 + 9 * Kml) * axisBd A t B r p k := by ring

/-- The cost of the `flatten` stage. -/
theorem costFlatten (A t B r p k Kf : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t)
    (xss : List (List Val)) (hx : xss.length = A * B)
    (hxs : ∀ xs ∈ xss, vsz (ofList xs) ≤ slL p r t) :
    Kf * (vsz (ofList (xss.map ofList)) + 1) ≤ 12 * (Kf * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  rw [MrgKit.vsz_ofList]
  have h2 : (xss.map ofList).length = A * B := by simp [hx]
  have h3 : ((xss.map ofList).map vsz).sum ≤ A * B * slL p r t := by
    rw [show ((xss.map ofList).map vsz) = (xss.map (fun xs => vsz (ofList xs))) from by
      rw [List.map_map]; rfl]
    calc (xss.map (fun xs => vsz (ofList xs))).sum ≤ xss.length * slL p r t :=
          MrgKit.sum_le_of_forall _ xss (slL p r t) hxs
      _ = A * B * slL p r t := by rw [hx]
  have h4 : A * B * slL p r t ≤ 8 * (A * t * B * (r + 1) * (p + 1)) + A * B := by
    have h4a : A * B * slL p r t = A * t * B * (r * (2 * p + 6) + 2) + A * B := by
      rw [show slL p r t = t * (r * (2 * p + 6) + 2) + 1 from rfl]; ring
    rw [h4a]
    have h4b : A * t * B * (r * (2 * p + 6) + 2) ≤ A * t * B * (8 * (r + 1) * (p + 1)) :=
      Nat.mul_le_mul_left _ (slL_le_rp r p)
    have h4c : A * t * B * (8 * (r + 1) * (p + 1)) = 8 * (A * t * B * (r + 1) * (p + 1)) := by ring
    omega
  have h5 : 8 * (A * t * B * (r + 1) * (p + 1)) ≤ 8 * axisBd A t B r p k :=
    Nat.mul_le_mul_left 8 (bd_ge_Nrp A t B r p k)
  have h9 : A * B ≤ axisBd A t B r p k := le_trans (AB_le_N A t B ht) (bd_ge_N A t B r p k)
  have h10 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  rw [h2]
  have hsum : (A * B + ((xss.map ofList).map vsz).sum + 1) + 1 ≤ 12 * axisBd A t B r p k := by
    omega
  calc Kf * ((A * B + ((xss.map ofList).map vsz).sum + 1) + 1)
      ≤ Kf * (12 * axisBd A t B r p k) := Nat.mul_le_mul_left Kf hsum
    _ = 12 * (Kf * axisBd A t B r p k) := by ring

/-- The cost of the final `axisSwap23` (with the arguments ordered `A B t`). -/
theorem costSwap2 (A t B r p k Ksw X : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t)
    (hX : X ≤ 9 * axisBd A t B r p k) :
    Ksw * (X + isz (A : ℤ) + isz (B : ℤ) + isz (t : ℤ) + 1) ≤ 13 * (Ksw * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h2 : isz (A : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k A hN (A_le_N A t B ht hB)
  have h3 : isz (B : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k B hN (B_le_N A t B hA ht)
  have h4 : isz (t : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k t hN (t_le_N A t B hA hB)
  have h5 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hsum : X + isz (A : ℤ) + isz (B : ℤ) + isz (t : ℤ) + 1 ≤ 13 * axisBd A t B r p k := by
    omega
  calc Ksw * (X + isz (A : ℤ) + isz (B : ℤ) + isz (t : ℤ) + 1)
      ≤ Ksw * (13 * axisBd A t B r p k) := Nat.mul_le_mul_left Ksw hsum
    _ = 13 * (Ksw * axisBd A t B r p k) := by ring

/-- The cost of the final `axisSwap23`. -/
theorem costSwap (A t B r p k Ksw X : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t)
    (hX : X ≤ 9 * axisBd A t B r p k) :
    Ksw * (X + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1) ≤ 13 * (Ksw * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h2 : isz (A : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k A hN (A_le_N A t B ht hB)
  have h3 : isz (t : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k t hN (t_le_N A t B hA hB)
  have h4 : isz (B : ℤ) ≤ axisBd A t B r p k :=
    isz_nat_le_bd A t B r p k B hN (B_le_N A t B hA ht)
  have h5 : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hsum : X + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1 ≤ 13 * axisBd A t B r p k := by omega
  calc Ksw * (X + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1)
      ≤ Ksw * (13 * axisBd A t B r p k) := Nat.mul_le_mul_left Ksw hsum
    _ = 13 * (Ksw * axisBd A t B r p k) := by ring


/-! ## The assembly of `HasAxis` -/

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- The gathered (slice-major) form of a flat array. -/
def gather (A t B : ℕ) (es : List Val) : List Val := List.flatten (HvdH.slices A t B es)

/-- The `A*B` slices of a gathered array, as values. -/
def chunks (A t B : ℕ) (g : List Val) : List Val :=
  (List.range (A * B)).map fun s => ofList ((g.drop (s * t)).take t)

theorem gather_length (A t B : ℕ) (es : List Val) : (gather A t B es).length = A * t * B :=
  flatten_slices_length A t B es

theorem drop1_eq {α : Type} {a c : α} {l l' : List α} (h : a :: l = c :: l') : l = l' := by
  have := congrArg (List.drop 1) h
  simpa using this

theorem drop2_eq {α : Type} {a b c d : α} {l l' : List α} (h : a :: b :: l = c :: d :: l') :
    l = l' := by
  have := congrArg (List.drop 2) h
  simpa using this

theorem chunks_length (A t B : ℕ) (g : List Val) : (chunks A t B g).length = A * B := by
  simp [chunks]

theorem chunks_getD (A t B : ℕ) (g : List Val) (s : ℕ) (hs : s < A * B) :
    (chunks A t B g).getD s .nil = ofList ((g.drop (s * t)).take t) :=
  getD_map_range _ _ hs

/-- Membership in a gathered array. -/
theorem mem_gather {A t B : ℕ} {es : List Val} {x : Val} (hx : x ∈ gather A t B es) :
    ∃ s j, s < A * B ∧ j < t ∧ x = es.getD ((s / B * t + j) * B + s % B) default := by
  rw [gather] at hx
  rw [List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  rw [HvdH.slices, List.mem_map] at hl
  obtain ⟨s, hs, rfl⟩ := hl
  rw [List.mem_range] at hs
  rw [List.mem_map] at hxl
  obtain ⟨j, hj, rfl⟩ := hxl
  rw [List.mem_range] at hj
  exact ⟨s, j, hs, hj, rfl⟩

/-- The encoded size of a gathered array. -/
theorem vsz_gather_le {A t B : ℕ} {es : List Val} {L : ℕ} (h : es.length = A * t * B)
    (hb : ∀ x ∈ es, vsz x ≤ L) :
    vsz (ofList (gather A t B es)) ≤ A * t * B * (L + 1) + 1 := by
  have hmem : ∀ x ∈ gather A t B es, vsz x ≤ L := by
    intro x hx
    obtain ⟨s, j, hs, hj, rfl⟩ := mem_gather hx
    have hidx : (s / B * t + j) * B + s % B < es.length := by
      rw [h]
      exact slicesIdxLt' A t B s j hs hj
    rw [List.getD_eq_getElem _ _ hidx]
    exact hb _ (List.getElem_mem _)
  exact MrgKit.vsz_ofList_le_of_bound (gather A t B es) L (A * t * B) hmem (by rw [gather_length])

/-- The cost of the transpose when the *middle* shape parameter is `B` (the scatter of `HasAxis`). -/
theorem costGather2 (A t B r p k KT : ℕ) (hA : 0 < A) (hB : 0 < B) (ht : 0 < t) :
    KT * (A * B * t) * (r * (2 * p + 6) + 2) * ((B).size + 1) +
      KT * (A * B * t) * ((A * B * t).size + 1) + KT ≤ 10 * (KT * axisBd A t B r p k) := by
  have hN : 0 < A * t * B := Npos A t B hA hB ht
  have h1 : (B).size + 1 ≤ (A * B * t).size + 2 := by
    have hBt : B ≤ A * B * t := by
      have hAB : 0 < A * t := by positivity
      calc B = 1 * B := (one_mul _).symm
        _ ≤ (A * t) * B := Nat.mul_le_mul_right B hAB
        _ = A * B * t := by ring
    have := Nat.size_le_size hBt; omega
  have h2 : r * (2 * p + 6) + 2 ≤ 8 * (r + 1) * (p + 1) := slL_le_rp r p
  have hs : (A * B * t).size = (A * t * B).size := by
    rw [show A * B * t = A * t * B by ring_nf]
  have h3 : KT * (A * B * t) * (r * (2 * p + 6) + 2) * ((B).size + 1)
      ≤ 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2))) := by
    calc KT * (A * B * t) * (r * (2 * p + 6) + 2) * ((B).size + 1)
        ≤ KT * (A * B * t) * (8 * (r + 1) * (p + 1)) * ((A * B * t).size + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (KT * (A * B * t)) h2) h1
      _ = 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2))) := by
          rw [hs]; ring
  have h4 : 8 * (KT * (A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2)))
      ≤ 8 * (KT * axisBd A t B r p k) :=
    Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left KT (bd_ge_log A t B r p k))
  have h5 : KT * (A * B * t) * ((A * B * t).size + 1) ≤ KT * axisBd A t B r p k := by
    have hle : (A * B * t).size + 1 ≤ (A * B * t).size + 2 := by omega
    calc KT * (A * B * t) * ((A * B * t).size + 1)
        ≤ KT * (A * B * t) * ((A * B * t).size + 2) := Nat.mul_le_mul_left _ hle
      _ = KT * (A * t * B * ((A * t * B).size + 2)) := by rw [hs]; ring
      _ ≤ KT * axisBd A t B r p k := Nat.mul_le_mul_left KT (bd_ge_szN A t B r p k hN)
  have h6 : KT ≤ KT * axisBd A t B r p k := by
    calc KT = KT * 1 := (Nat.mul_one _).symm
      _ ≤ KT * axisBd A t B r p k := Nat.mul_le_mul_left KT (bd_ge_one A t B r p k)
  omega

/-- Sequential composition when the first stage's post is a predicate of the whole stack. -/
theorem WordR_seqE {main : Cmd} {p q : Cmd} {A0 : List Val} {Q R : List Val → Prop}
    {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A0) (fun _ out => Q out) (fun _ => c1))
    (h2 : ∀ mid, Q mid → WordR main q (fun vs => vs = mid) (fun _ out => R out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A0) (fun _ out => R out) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨mid, s2, n1, hQ, he1, hn1, hstk1, hoth1⟩ := h1 A0 rfl s R hR
  obtain ⟨out, s3, n2, hR', he2, hn2, hstk2, hoth2⟩ := h2 mid hQ mid rfl s2 R (by rw [hstk1])
  have e1 : n1 ≤ c1 := hn1
  have e2 : n2 ≤ c2 := hn2
  exact ⟨out, s3, n1 + n2, hR', Eval.seq he1 he2, by show n1 + n2 ≤ c1 + c2; omega, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem hasAxis_of_transpose (hk : KLib) (hl : LayoutLib) (hT : HasAxisTranspose) (h1 : HasFFT1)
    (hfft : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p r t k : ℕ) (sgn : ℤ) (e : ℝ)
      (rest : List Val) (x : Val), IsPow2 r → t = 2 ^ k → t ∣ 2 * r → 2 * r < 2 ^ p →
      (sgn = 1 ∨ sgn = -1) → SlPre p r t x →
      WordR main prog
        (fun vs => vs = x :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ out => ∃ y, out = y :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
          SlPost p r t k sgn e x y ∧ vsz y ≤ slL p r t)
        (fun _ => K * t * (r + 1) * (p + 1) * (k + 1) + K))
    (hgood : ∀ (A t B p r k : ℕ) (sgn : ℤ) (e : ℝ) (u : Arr r) (ws : List (List (ℤ × ℤ)))
      (ys : List Val), ws.length = A * t * B →
      (∀ s < A * B, ApproxSL p r t (sliceVal A t B ws s)
        (fun j c => u ((s / B * t + j) * B + s % B) c) e) →
      (∀ s < A * B, cvecs (sliceVal A t B ws s) =
        ((List.flatten (slices A t B (cvecs ws))).drop (s * t)).take t) →
      List.Forall₂ (SlPost p r t k sgn e)
        ((List.range (A * B)).map (fun s => ofList
          (((List.flatten (slices A t B (cvecs ws))).drop (s * t)).take t))) ys →
      ∀ s < A * B, ∃ vs' : List (List (ℤ × ℤ)),
        ys.getD s .nil = ofList (cvecs vs') ∧ SlOK p r t vs' ∧
        ApproxSL p r t vs' (fun q => dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q) (e + k))
    (hscat : ∀ (p r A t B : ℕ) (sgn : ℤ) (u : Arr r) (E : ℝ) (Vs : List (List (List (ℤ × ℤ)))),
      Vs.length = A * B → (∀ s, s < A * B → (Vs.getD s []).length = t) →
      (∀ w ∈ Vs.flatten, InDiscVec p r w) →
      (∀ s < A * B, ApproxSL p r t (Vs.getD s [])
        (fun q => dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q) E) →
      (scatList A t B Vs.flatten).length = A * t * B ∧
        (∀ w ∈ scatList A t B Vs.flatten, InDiscVec p r w) ∧
        ApproxSL p r (A * t * B) (scatList A t B Vs.flatten) (axisT r t B sgn u) E) :
    HasAxis := by
  obtain ⟨Tp, KT, hTs⟩ := hT
  obtain ⟨fftP, Kff, hfft'⟩ := hfft
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨mapP, Kml, hmap⟩ := hk.mapList
  obtain ⟨chP, Kc, hch⟩ := hl.chunksOf
  obtain ⟨flP, Kf, hfl⟩ := hl.flatten
  obtain ⟨pdP, Kpd, hpd⟩ := axisParamsDown hk
  obtain ⟨puP, Kpu, hpu⟩ := axisParamsUp hk
  obtain ⟨swP, Ksw, hsw⟩ := axisSwap23 hk
  refine ⟨Tp ;;; pdP ;;; pickP 6 ;;; chP ;;; (mapP fftP) ;;; (flP ;;; puP ;;; Tp ;;; swP),
    (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw), ?_⟩
  intro main p r A t B k sgn ws u e rest hIsPow2 htk hdvd hlt hsgn hA hB hwslen hIDv hu
  have hN : 0 < A * t * B := Npos A t B hA hB (by rw [htk]; positivity)
  have htpos : 0 < t := by rw [htk]; positivity
  have hppos : 0 < p := by
    obtain ⟨j, hj1, hj2⟩ := hIsPow2
    have hr2 : 2 ≤ r := by
      rw [hj2]
      cases j with
      | zero => omega
      | succ j' =>
          rw [pow_succ]
          have h1 : 0 < 2 ^ j' := by positivity
          nlinarith
    have h2r : 2 ≤ 2 * r := by omega
    have hp3 : 3 ≤ 2 ^ p := by omega
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h] at hp3; norm_num at hp3
    · exact h
  have hXglen : (gather A t B (cvecs ws)).length = A * t * B := gather_length A t B (cvecs ws)
  have hcslen : ((cvecs ws).length) = A * t * B := by simp [cvecs, hwslen]
  have hmem : ∀ x ∈ gather A t B (cvecs ws), vsz x ≤ r * (2 * p + 6) + 1 := by
    intro x hx
    change x ∈ List.flatten (slices A t B (cvecs ws)) at hx
    rw [List.mem_flatten] at hx
    obtain ⟨l, hl, hxl⟩ := hx
    rw [slices, List.mem_map] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    rw [List.mem_range] at hs
    rw [List.mem_map] at hxl
    obtain ⟨j, hj, rfl⟩ := hxl
    rw [List.mem_range] at hj
    rw [List.getD_eq_getElem _ _ (by rw [hcslen]; exact slicesIdxLt' A t B s j hs hj)]
    simp only [cvecs, List.getElem_map]
    exact vsz_cvecVal_tight p r hppos _ (hIDv _ (List.getElem_mem _))
  have hvXg : vsz (ofList (gather A t B (cvecs ws))) ≤ A * t * B * (r * (2 * p + 6) + 2) + 1 :=
    MrgKit.vsz_ofList_le_of_bound _ (r * (2 * p + 6) + 1) (A * t * B) hmem (by rw [hXglen])
  have hvXg9 : vsz (ofList (gather A t B (cvecs ws))) ≤ 9 * axisBd A t B r p k :=
    vsz_rarr_le_bd A t B r p k _ hN hvXg
  have hbA : isz (A : ℤ) ≤ axisBd A t B r p k := isz_nat_le_bd A t B r p k A hN (A_le_N A t B htpos hB)
  have hbt : isz (t : ℤ) ≤ axisBd A t B r p k := isz_nat_le_bd A t B r p k t hN (t_le_N A t B hA hB)
  have hbB : isz (B : ℤ) ≤ axisBd A t B r p k := isz_nat_le_bd A t B r p k B hN (B_le_N A t B hA htpos)
  have hbk : isz (k : ℤ) ≤ axisBd A t B r p k := isz_nat_le_bd A t B r p k k hN (k_le_N A t B k hA hB htk)
  have hbs : isz sgn = 3 := isz_sgn_le sgn hsgn
  have hbr : isz (r : ℤ) ≤ 3 * axisBd A t B r p k := isz_r_le_bd A t B r p k hN
  have hbp : isz (p : ℤ) ≤ 3 * axisBd A t B r p k := isz_p_le_bd A t B r p k hN
  have hone : 1 ≤ axisBd A t B r p k := bd_ge_one A t B r p k
  have hS1 : WordR main Tp
      (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (gather A t B (cvecs ws)) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ => 10 * (KT * axisBd A t B r p k)) := by
    refine MrgKit.WordR_weaken (hTs main A t B (cvecs ws) (r * (2 * p + 6) + 1)
      (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) ?_ ?_) ?_ ?_ ?_
    · exact hcslen
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact vsz_cvecVal_tight p r hppos w (hIDv w hw)
    · intro vs hv; subst hv; rfl
    · intro vs out hv hq; subst hv; exact hq
    · intro vs _
      exact costGather A t B r p k KT hA hB htpos
  have hS2 : WordR main pdP
      (fun vs => vs = ofList (gather A t B (cvecs ws)) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => 24 * (Kpd * axisBd A t B r p k)) := by
    refine MrgKit.WordR_weaken (hpd main (ofList (gather A t B (cvecs ws))) (.int (A : ℤ))
      (.int (t : ℤ)) (.int (B : ℤ)) (.int (k : ℤ)) (.int sgn) (.int (r : ℤ)) (.int (p : ℤ)) rest)
      ?_ ?_ ?_
    · intro vs hv; subst hv; rfl
    · intro vs out hv hq; subst hv; exact hq
    · intro vs _
      simp only [MrgKit.vsz_int']
      exact costPrms A t B r p k sgn Kpd (vsz (ofList (gather A t B (cvecs ws)))) hA hB htpos htk hsgn hvXg
  have hS3 : WordR main (pickP 6)
      (fun vs => vs = ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = .int (t : ℤ) :: ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => 450 * (Kp * axisBd A t B r p k)) := by
    have hpref : ∀ i < 7, vsz ((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).getD i .nil) ≤ 9 * axisBd A t B r p k := by
      intro i hi
      interval_cases i <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, MrgKit.vsz_int'] <;>
        omega
    have hsum : (((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum ≤ 7 * (9 * axisBd A t B r p k) :=
      MrgKit.vsz_take_sum_le_getD _ 7 _ (fun i hi => hpref i (by omega))
    refine MrgKit.WordR_weaken (MrgKit.pickStep (hpick main) 6 (ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) (by simp)
      (450 * (Kp * axisBd A t B r p k)) ?_) ?_ ?_ ?_
    · have h1 : Kp * (6 + 1) * ((((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum + 1) ≤ (Kp * 7) * (64 * axisBd A t B r p k) := by
        have h2 : (((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum + 1 ≤ 64 * axisBd A t B r p k := by omega
        calc Kp * (6 + 1) * ((((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum + 1)
            = (Kp * 7) * ((((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum + 1) := by ring
          _ ≤ (Kp * 7) * (64 * axisBd A t B r p k) := Nat.mul_le_mul_left _ h2
      calc Kp * (6 + 1) * ((((ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 7).map vsz).sum + 1)
          ≤ (Kp * 7) * (64 * axisBd A t B r p k) := h1
        _ = 448 * (Kp * axisBd A t B r p k) := by ring
        _ ≤ 450 * (Kp * axisBd A t B r p k) := by
            exact Nat.mul_le_mul_right _ (by omega : (448 : ℕ) ≤ 450)
    · intro vs hv; subst hv; rfl
    · intro vs out hv hq; subst hv; exact hq
    · intro vs _; exact le_rfl
  have hS4 : WordR main chP
      (fun vs => vs = .int (t : ℤ) :: ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (chunks A t B (gather A t B (cvecs ws))) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => 16 * (Kc * axisBd A t B r p k)) := by
    refine MrgKit.WordR_weaken (hch main t (gather A t B (cvecs ws)) (by omega) ?_) ?_ ?_ ?_
    · rw [hXglen]; exact ⟨A * B, by ring⟩
    · intro vs hv; subst hv; exact ⟨.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest, rfl⟩
    · intro vs out hv hq
      obtain ⟨r0, hr1, hr2⟩ := hq
      have hr : r0 = .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest := by
        have h1 : .int (t : ℤ) :: ofList (gather A t B (cvecs ws)) :: r0 =
            .int (t : ℤ) :: ofList (gather A t B (cvecs ws)) ::
              (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) :=
          hr1.symm.trans hv
        exact drop2_eq h1
      have hdiv : (gather A t B (cvecs ws)).length / t = A * B := by
        rw [hXglen]
        rw [show A * t * B = (A * B) * t by ring, Nat.mul_div_left _ htpos]
      rw [hr2, hr, hdiv]
      rfl
    · intro vs _
      rw [hXglen]
      exact costChunks A t B r p k Kc (vsz (ofList (gather A t B (cvecs ws)))) hA hB htpos hvXg
  have hS5 : WordR main (mapP fftP)
      (fun vs => vs = ofList (chunks A t B (gather A t B (cvecs ws))) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => ∃ ys : List Val, out = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest ∧
          List.Forall₂ (SlPost p r t k sgn e) (chunks A t B (gather A t B (cvecs ws))) ys)
      (fun _ => (2 * Kff + 9 * Kml) * axisBd A t B r p k) := by
    refine MrgKit.WordR_weaken (hmap main fftP (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) (SlPre p r t)
      (SlPost p r t k sgn e) (Kff * t * (r + 1) * (p + 1) * (k + 1) + Kff) (slL p r t)
      ?_ (chunks A t B (gather A t B (cvecs ws))) ?_) ?_ ?_ ?_
    · intro x hx
      exact hfft' main p r t k sgn e (.int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) x hIsPow2 htk hdvd hlt hsgn hx
    · intro x hx
      have hx' : ∃ s < A * B, ofList ((((gather A t B (cvecs ws))).drop (s * t)).take t) = x := by
        have h := hx
        change x ∈ (List.range (A * B)).map
          (fun s => ofList ((((gather A t B (cvecs ws))).drop (s * t)).take t)) at h
        simpa only [List.mem_map, List.mem_range] using h
      obtain ⟨s, hs, rfl⟩ := hx'
      have hchunk : cvecs (sliceVal A t B ws s) = (((gather A t B (cvecs ws))).drop (s * t)).take t :=
        chunkSliceVal A t B ws hwslen s hs
      have hsl : SlOK p r t (sliceVal A t B ws s) :=
        ⟨sliceVal_length A t B s ws,
          fun w hw => sliceVal_inDisc p r A t B s ws hwslen hIDv hs w hw⟩
      refine ⟨⟨sliceVal A t B ws s, ?_, hsl⟩, ?_⟩
      · rw [hchunk]
      · rw [← hchunk]; exact vsz_of_SlOK p r t hppos _ hsl
    · intro vs hv; subst hv; rfl
    · intro vs out hv hq; subst hv; exact hq
    · intro vs _
      rw [chunks_length]
      exact costMap A t B r p k Kff Kml hA hB htpos
  have hF12 : WordR main (Tp ;;; pdP) (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ out => out = ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => ((10 * KT) + 24 * Kpd) * axisBd A t B r p k) := by
    refine MrgKit.WordR_weaken (MrgKit.WordR_seqC hS1 hS2) (fun vs h => h)
      (fun vs out h1 h2 => h2) ?_
    intro vs _
    rw [show 10 * (KT * axisBd A t B r p k) + 24 * (Kpd * axisBd A t B r p k) = ((10 * KT) + 24 * Kpd) * axisBd A t B r p k by ring_nf]
  have hF123 : WordR main ((Tp ;;; pdP) ;;; pickP 6) (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ out => out = .int (t : ℤ) :: ofList (gather A t B (cvecs ws)) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => (((10 * KT) + 24 * Kpd) + 450 * Kp) * axisBd A t B r p k) := by
    refine MrgKit.WordR_weaken (MrgKit.WordR_seqC hF12 hS3) (fun vs h => h)
      (fun vs out h1 h2 => h2) ?_
    intro vs _
    rw [show ((10 * KT) + 24 * Kpd) * axisBd A t B r p k + 450 * (Kp * axisBd A t B r p k) = (((10 * KT) + 24 * Kpd) + 450 * Kp) * axisBd A t B r p k by ring_nf]
  have hF1234 : WordR main (((Tp ;;; pdP) ;;; pickP 6) ;;; chP) (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (chunks A t B (gather A t B (cvecs ws))) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) (fun _ => ((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) * axisBd A t B r p k) := by
    refine MrgKit.WordR_weaken (MrgKit.WordR_seqC hF123 hS4) (fun vs h => h)
      (fun vs out h1 h2 => h2) ?_
    intro vs _
    rw [show (((10 * KT) + 24 * Kpd) + 450 * Kp) * axisBd A t B r p k + 16 * (Kc * axisBd A t B r p k) = ((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) * axisBd A t B r p k by ring_nf]
  have hF12345 : WordR main ((((Tp ;;; pdP) ;;; pickP 6) ;;; chP) ;;; (mapP fftP))
      (fun vs => vs = ofList (cvecs ws) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ out => ∃ ys : List Val, out = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest ∧
          List.Forall₂ (SlPost p r t k sgn e) (chunks A t B (gather A t B (cvecs ws))) ys)
      (fun _ => (((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) * axisBd A t B r p k) := by
    refine MrgKit.WordR_weaken (WordR_seqE hF1234 (fun mid hm => by subst hm; exact hS5))
      (fun vs h => h) (fun vs out h1 h2 => h2) ?_
    intro vs _
    rw [show ((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) * axisBd A t B r p k + (2 * Kff + 9 * Kml) * axisBd A t B r p k = (((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) * axisBd A t B r p k by ring_nf]
  refine MrgKit.WordR_weaken
    (WordR_seqE (p := Tp ;;; pdP ;;; pickP 6 ;;; chP ;;; (mapP fftP))
      (c2 := 12 * (Kf * axisBd A t B r p k) + 24 * (Kpu * axisBd A t B r p k) + 10 * (KT * axisBd A t B r p k) + 13 * (Ksw * axisBd A t B r p k))
      hF12345 (fun mid hmid => by
      obtain ⟨ys, rfl, hF⟩ := hmid

      have hcont : WordR main (flP ;;; puP ;;; Tp ;;; swP)
          (fun vs => vs = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
          (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = ofList (cvecs ws') :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
          ws'.length = A * t * B ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r (A * t * B) ws' (axisT r t B sgn u) (e + k))
          (fun _ => 12 * (Kf * axisBd A t B r p k) + 24 * (Kpu * axisBd A t B r p k) + 10 * (KT * axisBd A t B r p k) + 13 * (Ksw * axisBd A t B r p k)) := by
          have hy : ys.length = A * B := by
            have h := List.Forall₂.length_eq hF
            rw [← h, chunks_length]
          obtain ⟨Vs, hVslen, hVseq, hG⟩ := exists_sliceList (A := A) (B := B) ys hy
            (fun s vs' => SlOK p r t vs' ∧ ApproxSL p r t vs'
              (fun q => dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q) (e + k))
            (fun s hs => hgood A t B p r k sgn e u ws ys hwslen
              (sliceApprox p r A t B u e ws hwslen hu)
              (fun s0 hs0 => chunkSliceVal A t B ws hwslen s0 hs0) hF s hs)
          have hIDV : ∀ s < A * B, SlOK p r t (Vs.getD s []) := fun s hs => (hG s hs).1
          have hVt : ∀ s, s < A * B → (Vs.getD s []).length = t := fun s hs => (hG s hs).1.1
          have hper : ∀ s < A * B, ApproxSL p r t (Vs.getD s [])
              (fun q => dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q) (e + k) :=
            fun s hs => (hG s hs).2
          have hWlen : (Vs.flatten).length = A * B * t := by
            rw [List.length_flatten]
            have hmap : (Vs.map List.length) = Vs.map (fun _ => t) := by
              apply List.map_congr_left
              intro l hl
              obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
              have hli : Vs.getD i.1 [] = Vs.get i := List.getD_eq_getElem _ _ i.2
              rw [← hi, ← hli]
              exact hVt i.1 (hVslen ▸ i.2)
            rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul, hVslen]
          have hIDflatten : ∀ w ∈ Vs.flatten, InDiscVec p r w := flatten_InDisc Vs hVslen hIDV
          have hvW : vsz (ofList (cvecs Vs.flatten)) ≤ A * t * B * (r * (2 * p + 6) + 2) + 1 :=
            vsz_rarrVal_tight p r (A * t * B) hppos Vs.flatten
              ⟨by rw [hWlen]; ring, hIDflatten⟩
          have hFl : WordR main flP
              (fun vs => vs = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
              (fun _ out => out = ofList (cvecs Vs.flatten) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
              (fun _ => 12 * (Kf * axisBd A t B r p k)) := by
            refine MrgKit.WordR_weaken (hfl main (Vs.map cvecs)) ?_ ?_ ?_
            · intro vs hv
              subst hv
              exact ⟨.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest, by rw [hVseq]⟩
            · intro vs out hv hq
              obtain ⟨r0, hr1, hr2⟩ := hq
              subst hv
              have hr : r0 = .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest := by
                have h1 : ofList ((Vs.map cvecs).map ofList) :: r0 =
                    ofList ys :: (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) :=
                  hr1.symm
                rw [hVseq] at h1
                exact drop1_eq h1
              rw [hr2, hr, ← cvecsFlattenBlocks Vs]
            · intro vs _
              refine costFlatten A t B r p k Kf hA hB htpos (Vs.map cvecs) ?_ ?_
              · simp [hVslen]
              · intro x hx
                obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
                obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
                have hli : Vs.getD i.1 [] = l := by
                  rw [List.getD_eq_getElem _ _ i.2]; exact hi
                rw [← hli]
                exact vsz_of_SlOK p r t hppos _ (hIDV i.1 (hVslen ▸ i.2))
          have hPu : WordR main puP
              (fun vs => vs = ofList (cvecs Vs.flatten) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
              (fun _ out => out = ofList (cvecs Vs.flatten) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ => 24 * (Kpu * axisBd A t B r p k)) := by
            refine MrgKit.WordR_weaken (hpu main (ofList (cvecs Vs.flatten)) (.int (A : ℤ)) (.int (t : ℤ))
              (.int (B : ℤ)) (.int (k : ℤ)) (.int sgn) (.int (r : ℤ)) (.int (p : ℤ)) rest) ?_ ?_ ?_
            · intro vs hv; subst hv; rfl
            · intro vs out hv hq; subst hv; exact hq
            · intro vs _
              simp only [MrgKit.vsz_int']
              exact costPrms A t B r p k sgn Kpu (vsz (ofList (cvecs Vs.flatten))) hA hB htpos htk hsgn hvW
          have hT2 : WordR main Tp
              (fun vs => vs = ofList (cvecs Vs.flatten) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ out => out = ofList (List.flatten (slices A B t (cvecs Vs.flatten))) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ => 10 * (KT * axisBd A t B r p k)) := by
            refine MrgKit.WordR_weaken (hTs main A B t (cvecs Vs.flatten) (r * (2 * p + 6) + 1)
              (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) ?_ ?_) ?_ ?_ ?_
            · simp only [cvecs]; rw [List.length_map]; exact hWlen
            · intro x hx
              obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
              exact vsz_cvecVal_tight p r hppos w (hIDflatten w hw)
            · intro vs hv; subst hv; rfl
            · intro vs out hv hq; subst hv; exact hq
            · intro vs _
              exact costGather2 A t B r p k KT hA hB htpos
          have hSw : WordR main swP
              (fun vs => vs = ofList (List.flatten (slices A B t (cvecs Vs.flatten))) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
            out = ofList (cvecs ws') :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧
            ws'.length = A * t * B ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
            ApproxSL p r (A * t * B) ws' (axisT r t B sgn u) (e + k))
              (fun _ => 13 * (Ksw * axisBd A t B r p k)) := by
            refine MrgKit.WordR_weaken (hsw main (ofList (List.flatten (slices A B t (cvecs Vs.flatten)))) (.int (A : ℤ)) (.int (B : ℤ)) (.int (t : ℤ))
              (.int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)) ?_ ?_ ?_
            · intro vs hv; subst hv; rfl
            · intro vs out hv hq
              subst hv
              have hsc := hscat p r A t B sgn u (e + k) Vs hVslen hVt hIDflatten hper
              refine ⟨scatList A t B Vs.flatten, ?_, hsc.1, hsc.2.1, hsc.2.2⟩
              rw [hq, scatterCvecs A t B Vs.flatten hWlen]
              rfl
            · intro vs _
              simp only [MrgKit.vsz_int']
              have hX : vsz (ofList (List.flatten (slices A B t (cvecs Vs.flatten)))) ≤
                  A * t * B * (r * (2 * p + 6) + 2) + 1 := by
                have h1 : vsz (ofList (List.flatten (slices A B t (cvecs Vs.flatten)))) ≤
                    A * B * t * (r * (2 * p + 6) + 2) + 1 :=
                  vsz_gather_le (A := A) (t := B) (B := t) (es := cvecs Vs.flatten)
                    (L := r * (2 * p + 6) + 1) (by rw [cvecs, List.length_map]; exact hWlen)
                    (fun x hx => by
                      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
                      exact vsz_cvecVal_tight p r hppos w (hIDflatten w hw))
                rwa [show A * B * t * (r * (2 * p + 6) + 2) + 1 =
                  A * t * B * (r * (2 * p + 6) + 2) + 1 by ring_nf] at h1
              exact costSwap2 A t B r p k Ksw _ hA hB htpos (vsz_rarr_le_bd A t B r p k _ hN hX)
          have hA1 : WordR main (flP ;;; puP) (fun vs => vs = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
              (fun _ out => out = ofList (cvecs Vs.flatten) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ => 12 * (Kf * axisBd A t B r p k) + 24 * (Kpu * axisBd A t B r p k)) :=
            MrgKit.WordR_seqC hFl hPu
          have hA2 : WordR main ((flP ;;; puP) ;;; Tp) (fun vs => vs = ofList ys :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
              (fun _ out => out = ofList (List.flatten (slices A B t (cvecs Vs.flatten))) :: .int (A : ℤ) :: .int (B : ℤ) :: .int (t : ℤ) :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
              (fun _ => 12 * (Kf * axisBd A t B r p k) + 24 * (Kpu * axisBd A t B r p k) + 10 * (KT * axisBd A t B r p k)) :=
            MrgKit.WordR_seqC hA1 hT2
          exact WordR_seqE (c2 := 13 * (Ksw * axisBd A t B r p k)) hA2 (fun mid hm => by subst hm; exact hSw)
      exact hcont
      ))
    (fun vs h => h) (fun vs out h1 h2 => h2) ?_
  intro vs _
  rw [show (((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) * axisBd A t B r p k + (12 * (Kf * axisBd A t B r p k) + 24 * (Kpu * axisBd A t B r p k) + 10 * (KT * axisBd A t B r p k) + 13 * (Ksw * axisBd A t B r p k)) = (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw) * axisBd A t B r p k by ring_nf]
  have hsplit : (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw) * axisBd A t B r p k =
      (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw) * (A * t * B) * (r + 1) * (p + 1) * (k + 1) +
        (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw) * (A * t * B) * (r + 1) * (p + 1) * ((A * t * B).size + 2) + (((((((((10 * KT) + 24 * Kpd) + 450 * Kp) + 16 * Kc) + 2 * Kff + 9 * Kml) + 12 * Kf) + 24 * Kpu) + 10 * KT) + 13 * Ksw) := by
    rw [show axisBd A t B r p k = A * t * B * (r + 1) * (p + 1) * (k + 1) +
      A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2) + 1 from rfl]
    ring
  rw [hsplit]

end Work.SynFFT

namespace Work.SynFFT

open HvdH

/-- The final instantiation, checked against the three proved pieces and a *given* transpose
(the transpose itself is `Work.SynFFT.axisTranspose`, `axisTranspose.lean`). -/
example (hk : Work.SynFFT.KLib) (hl : HvdH.LayoutLib) (h1 : Work.SynFFT.HasFFT1)
    (hT : Work.SynFFT.HasAxisTranspose) : Work.SynFFT.HasAxis :=
  hasAxis_of_transpose hk hl hT h1 (fftSliceWord h1)
    (fun A t B p r k sgn e u ws ys hws hsl hchunk hF => sliceGood ws hws hsl hchunk ys hF)
    axisFinalScat

theorem hasAxis (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib) (h1 : Work.SynFFT.HasFFT1) (hasl : Work.SynFFT.AxisTSlicesProp) : Work.SynFFT.HasAxis :=
  hasAxis_of_transpose hk hl axisTranspose h1 (fftSliceWord h1)
    (fun A t B p r k sgn e u ws ys hws hsl hchunk hF => sliceGood ws hws hsl hchunk ys hF)
    axisFinalScat

end Work.SynFFT
