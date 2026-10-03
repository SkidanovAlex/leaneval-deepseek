/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The ranges of the coset lifts are pairwise orthogonal

For a subgroup `H ≤ G` and a choice `C : CosetData G H` of right-coset representatives, the
lifts `C.e q : ℓ²(H) →ₗᵢ[ℂ] ℓ²(G)` (`Submission.Work.ORVonNeumann.Rep.CosetData`) attach to each
right coset `H q` a copy of `ℓ²(H)` inside `ℓ²(G)`.  Distinct right cosets give orthogonal
subspaces: for `q ≠ q'` and arbitrary `y y' ∈ ℓ²(H)` one has `⟪C.e q y, C.e q' y'⟫ = 0`.

On the basis vectors this is immediate, because `C.e q (δ_h) = δ_{h q}` and the `δ`'s form an
orthonormal family, while the maps `h ↦ h q` and `h' ↦ h' q'` have disjoint images (their
common value would give two distinct decompositions of one element of `G` as `h · q`).  The
claim for arbitrary `y y'` follows by expanding them in the Hilbert basis `{δ_h}` and using
continuity of the inner product.

## Main result

* `Work.ORVonNeumann.Rep.e_inner_eq_zero` —
  `⟪C.e q y, C.e q' y'⟫ = 0` for `q ≠ q'`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.CosetData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

/-- The inner product is continuous in its second variable: it commutes with infinite sums. -/
lemma inner_tsum_right {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) {ι : Type*} {f : ι → E} (hf : Summable f) :
    inner ℂ x (∑' i, f i) = ∑' i, inner ℂ x (f i) := by
  have h := ContinuousLinearMap.map_tsum (innerSL ℂ x) hf
  simpa using h

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G] {H : Subgroup G}

/-- **Expansion of the coset lift in the Hilbert basis `{δ_h}` of `ℓ²(H)`.**  For every
`y : ℓ²(H)` the vector `C.e q y` is the sum of the images of the basis components of `y`. -/
lemma e_apply_eq_tsum (C : CosetData G H) (q : C.Q) (y : l2 ↥H) :
    C.e q y = ∑' h : ↥H, inner ℂ (deltaG h) y • C.e q (deltaG h) := by
  conv_lhs => rw [← tsum_expansion y]
  change (C.e q).toContinuousLinearMap (∑' h : ↥H, inner ℂ (deltaG h) y • deltaG h)
      = ∑' h : ↥H, inner ℂ (deltaG h) y • C.e q (deltaG h)
  rw [(C.e q).toContinuousLinearMap.map_tsum (hasSum_expansion y).summable]
  apply tsum_congr
  intro h
  rw [map_smul]
  rfl

/-- The image family defining `C.e q y` is summable. -/
lemma summable_e (C : CosetData G H) (q : C.Q) (y : l2 ↥H) :
    Summable (fun h : ↥H => inner ℂ (deltaG h) y • C.e q (deltaG h)) := by
  have := (C.e q).toContinuousLinearMap.summable (hasSum_expansion y).summable
  simpa [map_smul] using this

/-- Distinct cosets give orthogonal basis vectors. -/
lemma inner_e_delta_eq_zero (C : CosetData G H) {q q' : C.Q} (hqq' : q ≠ q')
    (h h' : ↥H) : inner ℂ (C.e q (deltaG h)) (C.e q' (deltaG h')) = 0 := by
  rw [C.e_delta, C.e_delta]
  apply inner_deltaG_of_ne
  intro heq
  have h1 : C.qpart ((h : G) * ((q : C.Q) : G)) = q :=
    C.qpart_eq_of_mul_eq _ (h := h) (q := q) rfl
  have h2 : C.qpart ((h' : G) * ((q' : C.Q) : G)) = q' :=
    C.qpart_eq_of_mul_eq _ (h := h') (q := q') rfl
  rw [heq] at h1
  exact hqq' (h1.symm.trans h2)

theorem e_inner_eq_zero {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {H : Subgroup G} (C : Work.ORVonNeumann.Rep.CosetData G H) {q q' : C.Q} (hqq' : q ≠ q') (y y' : Work.ORVonNeumann.l2 ↥H) : inner ℂ (C.e q y) (C.e q' y') = 0 := by
  have key : ∀ h h' : ↥H, inner ℂ (C.e q (deltaG h)) (C.e q' (deltaG h')) = 0 :=
    fun h h' => inner_e_delta_eq_zero C hqq' h h'
  -- `C.e q (δ_h)` is orthogonal to the whole range of the lift `C.e q'`.
  have h2 : ∀ h : ↥H, inner ℂ (C.e q (deltaG h)) (C.e q' y') = 0 := by
    intro h
    rw [e_apply_eq_tsum C q' y']
    rw [inner_tsum_right _ (summable_e C q' y')]
    have : ∀ h' : ↥H,
        inner ℂ (C.e q (deltaG h)) (inner ℂ (deltaG h') y' • C.e q' (deltaG h')) = 0 := by
      intro h'
      rw [inner_smul_right, key h h', mul_zero]
    rw [tsum_congr this, tsum_zero]
  rw [← inner_conj_symm]
  -- hence `C.e q' y'` is orthogonal to the whole range of the lift `C.e q`.
  have hmain : inner ℂ (C.e q' y') (C.e q y) = 0 := by
    rw [e_apply_eq_tsum C q y]
    rw [inner_tsum_right _ (summable_e C q y)]
    have hh : ∀ h : ↥H, inner ℂ (C.e q' y') (C.e q (deltaG h)) = 0 := by
      intro h
      rw [← inner_conj_symm, h2 h, map_zero]
    have : ∀ h : ↥H, inner ℂ (C.e q' y') (inner ℂ (deltaG h) y • C.e q (deltaG h)) = 0 := by
      intro h
      rw [inner_smul_right, hh h, mul_zero]
    rw [tsum_congr this, tsum_zero]
  rw [hmain]
  simp

end Work.ORVonNeumann.Rep
