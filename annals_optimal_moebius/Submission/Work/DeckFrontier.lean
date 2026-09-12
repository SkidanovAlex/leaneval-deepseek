import Submission.Work.FrontierArcs
import Submission.Work.DeckFrame
import Submission.PaperBand.Band

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Deck invariance of the flat frontier (DeckFrontier)

G1 (boundedness/finiteness) item 1: the flat frontier is invariant under
the deck map `period a : (x0,x1) ↦ (1−x0, x1+a)` — the symmetry of the
band.  This file proves, under `hf : IsMoebiusEmbedding a f`:

* `periodHomeo a` — `period a` is a HOMEOMORPHISM of the plane (its
  inverse is `periodInv a`, `period_periodInv`/`periodInv_period` green,
  continuity by `fun_prop`);
* `flatSet_period_image` — `period a '' FlatSet f = FlatSet f`
  (`period_mem_stripInterior` + `dN_zero_period_iff`, both directions);
* `interior_flatSet_period_image` — the same for the flat-interior
  (`Homeomorph.image_interior` + the set equality);
* `frontier_period_image_interior` — hence for the frontier of the
  flat-interior (`Homeomorph.image_frontier`, supplied here);
* **`flatFrontier_period_mem`** — membership of the flat-frontier set
  `flatFrontier f := frontier (interior (FlatSet f)) ∩ stripInterior` is
  preserved by `period a` (and, symmetrically, by `periodInv a` —
  `flatFrontier_periodInv_mem`).

The full ℤ-deck invariance then follows:

* `iterate_mem_invariant` — membership in a set invariant under `f` is
  invariant under all ℕ-iterates of `f`;
* `flatFrontier_periodIter_mem` / `flatFrontier_periodInvIter_mem` — the
  `flatFrontier` is invariant under all ℕ-iterates of `period a` resp.
  `periodInv a`;
* `periodIter_even_coord` / `periodInvIter_even_coord` / `periodIter_odd_coord`
  / `periodInvIter_odd_coord` — coordinate forms of the iterates
  (`even`: pure `x1`-shifts by `±2ma`; `odd`: flip + shift by `±(2m+1)a`);
* **`flatFrontier_bandRel_even`** — the even bandRel clause preserves
  `flatFrontier` (`x0 = y0`, `y1 − x1 = (2n)•a`);
* **`flatFrontier_bandRel_odd`** — the odd bandRel clause preserves
  `flatFrontier` (`x0 + y0 = 1`, `y1 − x1 = (2n+1)•a`; negative `n`
  split into `m = 0` (`c = period q`) and `m ≥ 1`
  (`c = periodInv^{2m−1} q`));
* **`flatFrontier_bandRel_inv`** — full deck invariance of the flat
  frontier under the band relation `bandRel a`;
* **`flatFrontier_chunk_equiv`** — every `q ∈ flatFrontier f` is
  `bandRel`-equivalent to a point `c ∈ flatFrontier f ∩ bandChunk a`
  (`exists_bandChunk_equiv` + `flatFrontier_bandRel_inv`).  This is the
  analytic input to the finiteness of the frontier arcs (G1): the
  frontier components in each band chunk are finite (compact chunk +
  `frontierComponent_isolated_locally`), and every component is a
  deck-image of one meeting the chunk.

Build: `lake build Submission.Work.DeckFrontier` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- `period a` is a homeomorphism of the plane. -/
def periodHomeo (a : ℝ) : ℝ² ≃ₜ ℝ² where
  toFun := period a
  invFun := periodInv a
  left_inv := fun x => periodInv_period a x
  right_inv := fun x => period_periodInv a x
  continuous_toFun := by
    change Continuous (fun x : ℝ² => !₂[1 - x 0, x 1 + a])
    fun_prop
  continuous_invFun := by
    change Continuous (fun x : ℝ² => !₂[1 - x 0, x 1 - a])
    fun_prop

/-- Image of a frontier set under a homeomorphism is the frontier of the
image. -/
lemma homeomorph_image_frontier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h '' s) := by
  calc
    h '' frontier s = h.symm ⁻¹' frontier s := h.image_eq_preimage_symm (frontier s)
    _ = frontier (h.symm ⁻¹' s) := h.symm.preimage_frontier s
    _ = frontier (h '' s) := by rw [h.image_eq_preimage_symm]

/-- The inverse period map preserves the strip interior. -/
lemma periodInv_mem_stripInterior (a : ℝ) {x : ℝ²} (hx : x ∈ stripInterior) :
    periodInv a x ∈ stripInterior := by
  rw [stripInterior] at hx ⊢
  dsimp [periodInv]
  constructor <;> linarith [hx.1, hx.2]

/-- The flat set is invariant under the deck map (as a set). -/
lemma flatSet_period_image {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    period a '' FlatSet f = FlatSet f := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hxF, rfl⟩
    have hxS : x ∈ stripInterior := (mem_FlatSet.mp hxF).1
    have hdN : dN f x = 0 := (mem_FlatSet.mp hxF).2
    rw [mem_FlatSet]
    constructor
    · exact period_mem_stripInterior a hxS
    · exact (dN_zero_period_iff hf hxS).mpr hdN
  · intro y hyF
    have hyS : y ∈ stripInterior := (mem_FlatSet.mp hyF).1
    have hdN : dN f y = 0 := (mem_FlatSet.mp hyF).2
    let x : ℝ² := periodInv a y
    have hxS : x ∈ stripInterior := periodInv_mem_stripInterior a hyS
    have hpp : period a x = y := by dsimp [x]; exact period_periodInv a y
    have hiff := dN_zero_period_iff hf hxS
    have hleft : dN f (period a x) = 0 := by rw [hpp]; exact hdN
    have hdx0 : dN f x = 0 := hiff.mp hleft
    refine ⟨x, (mem_FlatSet.mpr ⟨hxS, hdx0⟩), ?_⟩
    exact hpp

/-- The flat interior is invariant under the deck map (as a set). -/
lemma interior_flatSet_period_image {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    period a '' interior (FlatSet f) = interior (FlatSet f) := by
  calc
    period a '' interior (FlatSet f) = interior (period a '' FlatSet f) :=
      (periodHomeo a).image_interior (FlatSet f)
    _ = interior (FlatSet f) := by rw [flatSet_period_image hf]

/-- The frontier of the flat interior is invariant under the deck map
(as a set). -/
lemma frontier_period_image_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    period a '' frontier (interior (FlatSet f)) = frontier (interior (FlatSet f)) := by
  calc
    period a '' frontier (interior (FlatSet f)) = frontier (period a '' interior (FlatSet f)) :=
      homeomorph_image_frontier (periodHomeo a) (interior (FlatSet f))
    _ = frontier (interior (FlatSet f)) := by rw [interior_flatSet_period_image hf]

/-- The flat frontier inside the strip (frontier of the flat interior, in
the strip interior). -/
def flatFrontier (f : ℝ² → ℝ³) : Set ℝ² :=
  frontier (interior (FlatSet f)) ∩ stripInterior

/-- Membership in `flatFrontier` is preserved by the deck map `period`. -/
theorem flatFrontier_period_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {q : ℝ²}
    (hq : q ∈ flatFrontier f) : period a q ∈ flatFrontier f := by
  rcases hq with ⟨hqfr, hqS⟩
  have hq1 : q ∈ frontier (interior (FlatSet f)) := hqfr
  have him := frontier_period_image_interior (f := f) hf
  have hpm : period a q ∈ period a '' frontier (interior (FlatSet f)) := ⟨q, hq1, rfl⟩
  rw [him] at hpm
  exact ⟨hpm, period_mem_stripInterior a hqS⟩

/-- Membership in `flatFrontier` is preserved by the inverse deck map
`periodInv`. -/
theorem flatFrontier_periodInv_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {q : ℝ²}
    (hq : q ∈ flatFrontier f) : periodInv a q ∈ flatFrontier f := by
  rcases hq with ⟨hqfr, hqS⟩
  have him := frontier_period_image_interior (f := f) hf
  have hqin : q ∈ period a '' frontier (interior (FlatSet f)) := by rwa [him]
  rcases hqin with ⟨z, hz, hzq⟩
  have hzq' : z = periodInv a q := by
    have h := periodInv_period a z
    rw [hzq] at h
    exact h.symm
  have hp : periodInv a q ∈ frontier (interior (FlatSet f)) := by
    rw [← hzq']
    exact hz
  exact ⟨hp, periodInv_mem_stripInterior a hqS⟩

/-- Membership in a set invariant under `f` is invariant under all
ℕ-iterates of `f`. -/
lemma iterate_mem_invariant {α : Type*} {S : Set α} {f : α → α}
    (hS : ∀ x : α, x ∈ S → f x ∈ S) (n : ℕ) :
    ∀ x : α, x ∈ S → (f^[n]) x ∈ S := by
  induction n with
  | zero =>
    intro x hx
    simpa using hx
  | succ n ih =>
    intro x hx
    have hfx : f x ∈ S := hS x hx
    have h1 := ih (f x) hfx
    simpa [Function.iterate_succ_apply] using h1

/-- `flatFrontier` is invariant under all ℕ-iterates of the deck map
`period`. -/
lemma flatFrontier_periodIter_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (n : ℕ) {q : ℝ²} (hq : q ∈ flatFrontier f) : Nat.iterate (period a) n q ∈ flatFrontier f :=
  iterate_mem_invariant (S := flatFrontier f) (f := period a)
    (fun _ hx => flatFrontier_period_mem hf hx) n q hq

/-- `flatFrontier` is invariant under all ℕ-iterates of the inverse deck
map `periodInv`. -/
lemma flatFrontier_periodInvIter_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (n : ℕ) {q : ℝ²} (hq : q ∈ flatFrontier f) : Nat.iterate (periodInv a) n q ∈ flatFrontier f :=
  iterate_mem_invariant (S := flatFrontier f) (f := periodInv a)
    (fun _ hx => flatFrontier_periodInv_mem hf hx) n q hq

/-- The even deck step is the double period map (shift by `2a` in `x1`,
no flip): `period (period x) = (x0, x1 + 2a)`. -/
lemma period_twice_coord (a : ℝ) (x : ℝ²) : period a (period a x) = !₂[x 0, x 1 + 2 * a] := by
  ext i <;> fin_cases i <;> simp [period] <;> ring

/-- The even inverse deck step: `periodInv (periodInv x) = (x0, x1 − 2a)`. -/
lemma periodInv_twice_coord (a : ℝ) (x : ℝ²) : periodInv a (periodInv a x) = !₂[x 0, x 1 - 2 * a] := by
  ext i <;> fin_cases i <;> simp [periodInv] <;> ring

/-- The `2m`-th iterate of `period` shifts `x1` by `2·m·a` (no flip):
`period^{2m} q = (q0, q1 + 2m·a)`. -/
lemma periodIter_even_coord (a : ℝ) (m : ℕ) (q : ℝ²) :
    Nat.iterate (period a) (2 * m) q = !₂[q 0, q 1 + 2 * (m : ℝ) * a] := by
  revert q
  induction m with
  | zero =>
    intro q
    ext i <;> fin_cases i <;> simp
  | succ m ih =>
    intro q
    have hsplit : 2 * m.succ = 2 * m + 2 := by omega
    rw [hsplit]
    rw [Function.iterate_add_apply (period a) (2 * m) 2 q]
    have htwo : Nat.iterate (period a) 2 q = !₂[q 0, q 1 + 2 * a] := period_twice_coord a q
    rw [htwo]
    have hq2 := ih !₂[q 0, q 1 + 2 * a]
    rw [hq2]
    ext i <;> fin_cases i <;> simp <;> ring

/-- The `2m`-th iterate of `periodInv` shifts `x1` by `−2·m·a` (no flip):
`periodInv^{2m} q = (q0, q1 − 2m·a)`. -/
lemma periodInvIter_even_coord (a : ℝ) (m : ℕ) (q : ℝ²) :
    Nat.iterate (periodInv a) (2 * m) q = !₂[q 0, q 1 - 2 * (m : ℝ) * a] := by
  revert q
  induction m with
  | zero =>
    intro q
    ext i <;> fin_cases i <;> simp
  | succ m ih =>
    intro q
    have hsplit : 2 * m.succ = 2 * m + 2 := by omega
    rw [hsplit]
    rw [Function.iterate_add_apply (periodInv a) (2 * m) 2 q]
    have htwo : Nat.iterate (periodInv a) 2 q = !₂[q 0, q 1 - 2 * a] := periodInv_twice_coord a q
    rw [htwo]
    have hq2 := ih !₂[q 0, q 1 - 2 * a]
    rw [hq2]
    ext i <;> fin_cases i <;> simp <;> ring

/-- **The EVEN branch of the deck invariance**: if `q ∈ flatFrontier f`
and `c` differs from `q` only by shifting `x1` by an even multiple of
`a` (`q 0 = c 0`, `c 1 − q 1 = (2n)•a`), then `c ∈ flatFrontier f`.
Proof: split `n = m` / `n = -m` (`Int.eq_nat_or_neg`); for `n = m`,
`c = period^{2m} q` (coordinate form `periodIter_even_coord`), and
`Nat.iterate`-invariance (`flatFrontier_periodIter_mem`) applies; the
`n = -m` branch is symmetric with `periodInv` +
`flatFrontier_periodInvIter_mem`. -/
theorem flatFrontier_bandRel_even {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {q c : ℝ²} {n : ℤ} (hq : q ∈ flatFrontier f) (hx0 : q 0 = c 0)
    (hd : c 1 - q 1 = (2 * n) • a) : c ∈ flatFrontier f := by
  rcases Int.eq_nat_or_neg n with ⟨m, hm | hm⟩
  · -- n = m : c = period^{2m} q
    have hoffset : (2 * n : ℤ) • a = 2 * (m : ℝ) * a := by
      rw [hm]
      norm_num
    have hd' : c 1 = q 1 + (2 * n) • a := by linarith
    have hc1 : c 1 = q 1 + 2 * (m : ℝ) * a := by
      rw [hd', hoffset]
    have hceq : c = Nat.iterate (period a) (2 * m) q := by
      rw [periodIter_even_coord]
      ext i <;> fin_cases i <;> simp [hx0, hc1]
    rw [hceq]
    exact flatFrontier_periodIter_mem hf (2 * m) hq
  · -- n = -m : c = periodInv^{2m} q
    have hoffset : (2 * n : ℤ) • a = -(2 * (m : ℝ) * a) := by
      rw [hm]
      norm_num
    have hd' : c 1 = q 1 + (2 * n) • a := by linarith
    have hc1 : c 1 = q 1 - 2 * (m : ℝ) * a := by
      rw [hd']
      rw [hoffset]
      ring
    have hceq : c = Nat.iterate (periodInv a) (2 * m) q := by
      rw [periodInvIter_even_coord]
      ext i <;> fin_cases i <;> simp [hx0, hc1]
    rw [hceq]
    exact flatFrontier_periodInvIter_mem hf (2 * m) hq

/-- The `2m+1`-th iterate of `period` flips `x0` and shifts `x1` by
`(2m+1)·a`: `period^{2m+1} q = (1 − q0, q1 + (2m+1)·a)`. -/
lemma periodIter_odd_coord (a : ℝ) (m : ℕ) (q : ℝ²) :
    Nat.iterate (period a) (2 * m + 1) q = !₂[1 - q 0, q 1 + (2 * (m : ℝ) + 1) * a] := by
  revert q
  induction m with
  | zero =>
    intro q
    have h1 : 2 * 0 + 1 = 1 := by norm_num
    rw [h1]
    simp [period]
  | succ m ih =>
    intro q
    have hsplit : 2 * m.succ + 1 = (2 * m + 1) + 2 := by omega
    rw [hsplit]
    rw [Function.iterate_add_apply (period a) (2 * m + 1) 2 q]
    have htwo : Nat.iterate (period a) 2 q = !₂[q 0, q 1 + 2 * a] := period_twice_coord a q
    rw [htwo]
    have hq2 := ih !₂[q 0, q 1 + 2 * a]
    rw [hq2]
    ext i <;> fin_cases i <;> simp <;> ring

/-- The `2m+1`-th iterate of `periodInv` flips `x0` and shifts `x1` by
`−(2m+1)·a`: `periodInv^{2m+1} q = (1 − q0, q1 − (2m+1)·a)`. -/
lemma periodInvIter_odd_coord (a : ℝ) (m : ℕ) (q : ℝ²) :
    Nat.iterate (periodInv a) (2 * m + 1) q = !₂[1 - q 0, q 1 - (2 * (m : ℝ) + 1) * a] := by
  revert q
  induction m with
  | zero =>
    intro q
    have h1 : 2 * 0 + 1 = 1 := by norm_num
    rw [h1]
    simp [periodInv]
  | succ m ih =>
    intro q
    have hsplit : 2 * m.succ + 1 = (2 * m + 1) + 2 := by omega
    rw [hsplit]
    rw [Function.iterate_add_apply (periodInv a) (2 * m + 1) 2 q]
    have htwo : Nat.iterate (periodInv a) 2 q = !₂[q 0, q 1 - 2 * a] := periodInv_twice_coord a q
    rw [htwo]
    have hq2 := ih !₂[q 0, q 1 - 2 * a]
    rw [hq2]
    ext i <;> fin_cases i <;> simp <;> ring

/-- **The ODD branch of the deck invariance**: if `q ∈ flatFrontier f`
and `c` is the odd-deck image of `q` (`q 0 + c 0 = 1`,
`c 1 − q 1 = (2n+1)•a`), then `c ∈ flatFrontier f`.  Proof: split
`n = m` / `n = −m` (`Int.eq_nat_or_neg`); for `n = m`,
`c = period^{2m+1} q` (`periodIter_odd_coord`) and
`flatFrontier_periodIter_mem` applies; for `n = −m`, `m = 0` gives
`c = period q` (`flatFrontier_period_mem`) and `m ≥ 1` gives
`c = periodInv^{2m−1} q` (`periodInvIter_odd_coord` at `m−1` +
`flatFrontier_periodInvIter_mem`). -/
theorem flatFrontier_bandRel_odd {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {q c : ℝ²} {n : ℤ} (hq : q ∈ flatFrontier f) (hsum : q 0 + c 0 = 1)
    (hd : c 1 - q 1 = (2 * n + 1) • a) : c ∈ flatFrontier f := by
  rcases Int.eq_nat_or_neg n with ⟨m, hm | hm⟩
  · -- n = m ≥ 0 : c = period^{2m+1} q
    have hoffset : (2 * n + 1) • a = (2 * (m : ℝ) + 1) * a := by
      rw [hm]
      rw [zsmul_eq_mul]
      norm_num
    have hd' : c 1 = q 1 + (2 * n + 1) • a := by linarith
    have hc1 : c 1 = q 1 + (2 * (m : ℝ) + 1) * a := by
      rw [hd', hoffset]
    have hc0 : c 0 = 1 - q 0 := by linarith
    have hceq : c = Nat.iterate (period a) (2 * m + 1) q := by
      rw [periodIter_odd_coord]
      ext i <;> fin_cases i <;> simp [hc0, hc1]
    rw [hceq]
    exact flatFrontier_periodIter_mem hf (2 * m + 1) hq
  · -- n = −m
    by_cases hmz : m = 0
    · -- m = 0 : n = 0, c = period q (single flip, shift a)
      have hn0 : n = 0 := by rw [hm, hmz]; simp
      have hoz : (2 * (0 : ℤ) + 1) • a = a := by
        rw [zsmul_eq_mul]
        norm_num
      have hd0 : c 1 - q 1 = a := by
        rw [hd, hn0]
        exact hoz
      have hc1 : c 1 = q 1 + a := by linarith
      have hc0 : c 0 = 1 - q 0 := by linarith
      have hceq : c = period a q := by
        ext i <;> fin_cases i <;> simp [period, hc0, hc1]
      rw [hceq]
      exact flatFrontier_period_mem hf hq
    · -- m ≥ 1 : write m = m' + 1, c = periodInv^{2m'+1} q
      rcases Nat.exists_eq_succ_of_ne_zero hmz with ⟨m', hm's⟩
      have hz : (2 * n + 1 : ℤ) = -(2 * (m' : ℤ) + 1) := by
        rw [hm, hm's, Nat.cast_succ]
        ring
      have hoffset : (2 * n + 1) • a = -(2 * (m' : ℝ) + 1) * a := by
        rw [zsmul_eq_mul]
        have hcoef : ((2 * n + 1 : ℤ) : ℝ) = -(2 * (m' : ℝ) + 1) := by
          rw [hz]
          norm_num
        rw [hcoef]
      have hd' : c 1 = q 1 + (2 * n + 1) • a := by linarith
      have hc1 : c 1 = q 1 - (2 * (m' : ℝ) + 1) * a := by
        rw [hd', hoffset]
        ring
      have hc0 : c 0 = 1 - q 0 := by linarith
      have hceq : c = Nat.iterate (periodInv a) (2 * m' + 1) q := by
        rw [periodInvIter_odd_coord]
        ext i <;> fin_cases i <;> simp [hc0, hc1]
      rw [hceq]
      exact flatFrontier_periodInvIter_mem hf (2 * m' + 1) hq

/-- **Full deck invariance of the flat frontier**: membership in
`flatFrontier f` is preserved by the band relation `bandRel a`
(`flatFrontier_bandRel_even` for the even clauses, `flatFrontier_bandRel_odd`
for the odd clauses). -/
theorem flatFrontier_bandRel_inv {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {q c : ℝ²} (hq : q ∈ flatFrontier f) (hrel : bandRel a q c) : c ∈ flatFrontier f := by
  rcases hrel with ⟨n, hx0, hd⟩ | ⟨n, hsum, hd⟩
  · exact flatFrontier_bandRel_even hf hq hx0 hd
  · exact flatFrontier_bandRel_odd hf hq hsum hd

/-- **Chunk cover of the flat frontier**: every `q ∈ flatFrontier f` is
`bandRel`-equivalent to a point `c` of the flat frontier inside the
compact chunk `bandChunk a` (deck-invariance of `flatFrontier` +
`exists_bandChunk_equiv`). -/
theorem flatFrontier_chunk_equiv {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {q : ℝ²} (hq : q ∈ flatFrontier f) :
    ∃ c : ℝ², c ∈ flatFrontier f ∧ c ∈ bandChunk a := by
  have hqS : q ∈ stripInterior := hq.2
  have hqU : q ∈ unitStrip := stripInterior_subset_unitStrip hqS
  rcases exists_bandChunk_equiv ha hqU with ⟨c, hc, hrel⟩
  refine ⟨c, flatFrontier_bandRel_inv hf hq hrel, hc⟩

end Submission.PaperBand
