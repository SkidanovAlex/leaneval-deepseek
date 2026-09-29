import Mathlib
import Submission.HvdH.Interfaces

/-!
# 1-D Gaussian resampling: the objects (paper Lemma 4.9)

This module fixes the *mathematical* objects of the one-dimensional resampling word
`Submission/Work/Resample/sliceA1.lean`.  Nothing here is a program: we only define

* the window half-width `m = ⌈√p⌉ · α` and the window length `L = min s (2m+1)`;
* the extended input list `U` of length `s + L`, indexed so that the `k`-th window of
  `L` consecutive entries is centred at `k·s/t`;
* the rounded Gaussian weights `W k i = ⌊2^p · A_{k,i}⌉` where `A_{k,i}` is the real
  entry of `HvdH.resA s t α`;
* the resulting integer map `slPhiFun`, which is the `Φ` of the lemma;

together with the table value `slT` (the static parameter block `P`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `m = (⌈√p⌉) · α`: the paper's window half-width. -/
def slM (p α : ℕ) : ℕ := (Nat.sqrt p + 1) * α

/-- `L = min s (2m+1)`: the number of terms retained for each output. -/
def slL (p α s : ℕ) : ℕ := min s (2 * slM p α + 1)

/-- `h = L/2`: the index at which `u 0` sits in the extended list `slExt`. -/
def slH (p α s : ℕ) : ℕ := slL p α s / 2

/-- The extended input `U` (length `s + L`), `U i = u ((i - h) mod s)`. -/
def slExt (p α s : ℕ) (u : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  (u.drop (s - slH p α s)) ++ u ++ (u.take (slL p α s - slH p α s))

/-- The window start `K k = ⌊(2 k s + t)/(2 t)⌋ = round (k s / t)`. -/
def slK (s t k : ℕ) : ℕ := (2 * k * s + t) / (2 * t)

/-- The real weight of the `i`-th retained term of output `k`. -/
noncomputable def slA (p α s t : ℕ) (k i : ℕ) : ℝ :=
  let j := (slK s t k + i + s - slH p α s) % s
  if h : k < t ∧ j < s then ((HvdH.resA s t α) ⟨k, h.1⟩ ⟨j, h.2⟩).re else 0

/-- The integer weight `⌊2^p · A⌉`. -/
noncomputable def slW (p α s t : ℕ) (k i : ℕ) : ℤ := rnd ((2 : ℝ) ^ p * slA p α s t k i)

/-- The integer map `Φ`: the `k`-th output of the windowed Gaussian for input list `u`. -/
noncomputable def slPhi (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : ℤ × ℤ :=
  let e := slExt p α s u
  ( Int.tdiv (∑ i ∈ Finset.range (slL p α s),
      slW p α s t k i * (e.getD (slK s t k + i) (0, 0)).1) ((2 : ℤ) ^ p),
    Int.tdiv (∑ i ∈ Finset.range (slL p α s),
      slW p α s t k i * (e.getD (slK s t k + i) (0, 0)).2) ((2 : ℤ) ^ p) )

/-- `Φ` as a function of a vector of length `s`. -/
noncomputable def slPhiFun (p α s t : ℕ) : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ) :=
  fun w k => slPhi p α s t (List.ofFn w) k

/-- Advance `d k = K (k+1) - K k` (the window slides by `d k ∈ {0,1}`). -/
def slD (s t k : ℕ) : ℕ := slK s t (k + 1) - slK s t k

/-- One record of the table: the advance and the doubled weights
`[W k 0, W k 0, W k 1, W k 1, …]` (doubled so that each weight can be popped twice). -/
noncomputable def slRec (p α s t : ℕ) (k : ℕ) : HvdH.Val :=
  .cons (.int (slD s t k))
    (HvdH.ofList ((List.ofFn (fun i : Fin (2 * slL p α s) => slW p α s t k ((i : ℕ) / 2))).map
      (fun w => HvdH.Val.int w)))

/-- The static parameter block `P = [slT]` of the resampling word. -/
noncomputable def slT (p α s t : ℕ) : HvdH.Val :=
  HvdH.ofList (List.ofFn (fun k : Fin t => slRec p α s t k))


/-!
## Design notes for the resampling word `q` (read before constructing it)

The word `q` (the second existential of `Work.Resample.sliceA1`) must take

    ofList (u.map cfxVal) :: [slT p α s t] ++ rest          (stack 0)

to

    cvecVal (fun k => slPhiFun p α s t (fun j => u.getD j (0,0)) k) :: [slT p α s t] ++ rest

within cost `K*(t+1)*(sqrt p+1)*(α+1)*(Cm (K*p)+p+1)`, for every `main` with `MulBelow main N Cm`
and `K*p < N`.  Everything is available in the `WordR` + raw-`Ev` idiom of
`Submission/Work/Layout/Move.lean` (`mvVal a b c d` moves one *value* between stacks at cost
`16*(vsz+1)` and restores its buffers) and the stack-0 words of `HvdH.KernelLib`/`IntLib`/`LayoutLib`.

**Shapes in the table.**  `slRec p α s t k = .cons (.int (slD s t k)) (ofList wl)` where
`wl : List Val` has length `2 * slL p α s` and `wl[i] = .int (slW p α s t k (i/2))` (each weight
written **twice**, in *increasing* `i`).  `slT p α s t = ofList [slRec k | k < t]`.  `slD s t k
= slK s t (k+1) - slK s t k ≤ 1` is the number of input elements the window advances by after
output `k` (see `sliceA1Ext`); for `k = t-1` it may be `1`, which is harmless (the final cleanup
empties the element scratch anyway).

**Suggested plan.**

* put a marker `Glyph.mk i` at the bottom of every scratch stack you use, so the frame condition
  `s'.stk k = s.stk k` (k ≠ 0) can be restored by popping down to the markers;
* `LayoutLib.take/drop/append` build `E := ofList (e.map cfxVal)`, `e = slExt p α s u` (duplicate
  the input twice with `KernelLib.dup` and combine `u.drop (s - slH)` and `u.take (slL - slH)`
  around a copy of `u`); `LayoutLib.reverse` the result, then repeatedly
  `KernelLib.unconsV` + `mvVal 0 <scratch>` to load the individual elements of `e` on a scratch
  stack (`unconsV` is O(1) and moves one value at a time, so this costs `O((s+slL) * p)`);
* likewise `LayoutLib.reverse` a `dup` of `slT p α s t` and load the records on a second scratch;
* stack 0 then holds `[.int 0, .int 0, .nil, slT p α s t] ++ rest` (the accumulators `Sx`, `Sy`
  and `OUT`) and `.int p` sits on a third scratch;
* for `k = 0, 1, …, t-1` (records consumed in order): move the record's weight list onto a weight
  scratch in list order, so the **top is `slW k (slL-1)`**; then repeatedly (while the weight
  scratch is non-empty) pop one element `e` from the element scratch, `dup` it onto a done pile,
  `unconsV` it, park its second component, pop the weight **twice** (it is stored twice) and apply
  `.self` (exact integer product) twice, adding the results to `Sx` and `Sy` with `IntLib.add`
  (`roll`/`swap` on the small temporaries); after `slL` elements apply `IntLib.shrT` twice
  (`Int.tdiv _ (2^p)`, matching `slPhi`) and `consV` the resulting `cfxVal` onto `OUT`; finally
  move the whole done pile back onto the element scratch and drop `slD s t k` elements from it;
* the pairing is the one forced by construction: elements and weights are consumed in *reverse*
  order, i.e. `e (slK+i)` with `slW k i`, which is exactly the pairing used in `slPhi`;
* at the end drop `Sx`, `Sy`, `LayoutLib.reverse` `OUT` (the outputs are accumulated in reverse),
  empty every scratch down to its marker and pop the markers.

Costs: `2*Cm (K*p) + O(p)` per element, `O(slL p α s * (Cm (K*p) + p))` per window, plus
`O((s + t*slL) * p)` for setup/cleanup; with `slL ≤ 2*slM+1 ≈ 2α√p` this fits the stated bound
for a suitable absolute `K` (the caller takes `K = max Kp Kq + 1`).
-/

end Work.Resample
