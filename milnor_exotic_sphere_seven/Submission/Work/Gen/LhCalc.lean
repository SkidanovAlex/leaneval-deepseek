import Mathlib
import Submission.Work.Gen.crx.Core
import Submission.Work.LerayHirsch.LH
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Kunneth.PointMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The calculus of the Leray–Hirsch summands

`Work.LerayHirsch.lhTerm Z k i x = π^*(x) ⌣ ζ^i` and `lhMap Z k xf = Σ_i lhTerm Z k i (xf i)`
(`Submission/Work/LerayHirsch/LH.lean`) express `H^{2k}(P(Z);ℤ)` in terms of `H^*(B;ℤ)`.

This module collects the structural lemmas about them needed by the `ψ`-analysis of the crux
(`Submission/Work/Gen/NOTES_psi_delta.md`):

* `lhTerm_add`/`lhMap_add`/`lhMap_sum`/`cupChern_sum_right` — linearity;
* `zetaPow_one_eq_zeta`, `lhTerm_one_index` — the `i = 1` summand is multiplication by `ζ`;
* `cupChern_zeta_lhTerm`/`cupChern_zeta2_lhTerm` — multiplying the `i`-th summand by `ζ` (or `ζ²`)
  shifts the Leray–Hirsch index;
* `cupChern_zero_lhMap` — the `H⁰(B)`-module structure: multiplying a Leray–Hirsch combination by
  the pullback of a degree-`0` class multiplies its coefficients.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}

/-! ## Linearity -/

/-- The Leray–Hirsch summand is additive in its coefficient. -/
theorem lhTerm_add (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x y : Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.LerayHirsch.lhTerm Z k i (x + y)
      = Work.LerayHirsch.lhTerm Z k i x + Work.LerayHirsch.lhTerm Z k i y := by
  rw [Work.LerayHirsch.lhTerm_def, Work.LerayHirsch.lhTerm_def, Work.LerayHirsch.lhTerm_def,
    map_add, Work.Whitney.ChernRel.cupChern_add_left,
    Work.Whitney.ChernRel.cohTransport_add]

/-- The Leray–Hirsch map is additive in the coefficient family. -/
theorem lhMap_add (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (F G : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.LerayHirsch.lhMap Z k (fun i => F i + G i)
      = Work.LerayHirsch.lhMap Z k F + Work.LerayHirsch.lhMap Z k G := by
  rw [Work.LerayHirsch.lhMap_apply, Work.LerayHirsch.lhMap_apply, Work.LerayHirsch.lhMap_apply]
  have h : (∑ i, Work.LerayHirsch.lhTerm Z k i (F i + G i))
      = ∑ i, (Work.LerayHirsch.lhTerm Z k i (F i) + Work.LerayHirsch.lhTerm Z k i (G i)) :=
    Finset.sum_congr rfl (fun i _ => lhTerm_add Z k i (F i) (G i))
  rw [h, Finset.sum_add_distrib]

/-- The Leray–Hirsch map is additive over a finite sum of coefficient families. -/
theorem lhMap_sum (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {α : Type} (s : Finset α) (k : ℕ)
    (F : α → (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.LerayHirsch.lhMap Z k (fun i => ∑ a ∈ s, F a i)
      = ∑ a ∈ s, Work.LerayHirsch.lhMap Z k (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Work.LerayHirsch.lhMap_apply, Finset.sum_empty]
      simp [Work.LerayHirsch.lhTerm_zero]
  | insert a s has ih =>
      have h1 : (fun i => ∑ b ∈ insert a s, F b i) = (fun i => F a i + ∑ b ∈ s, F b i) := by
        funext i
        rw [Finset.sum_insert has]
      rw [h1, lhMap_add, ih, Finset.sum_insert has]

/-- The graded product is additive in a finite sum of its second arguments. -/
theorem cupChern_sum_right {B : Type} [TopologicalSpace B] {α : Type} (a b : ℕ)
    (x : Coh ℤ (2 * a) B) (s : Finset α) (f : α → Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b x (∑ i ∈ s, f i)
      = ∑ i ∈ s, Work.Whitney.cupChern a b x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Work.Whitney.cupChern_def,
        Work.Cohomology.cupH'_zero_right]
      exact map_zero (Work.Thom.cohTransportLM _)
  | insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his, Work.Whitney.ChernRel.cupChern_add_right, ih]

/-! ## The `i = 1` summand -/

/-- `ζ¹ = ζ`: the definitional unfolding of `Work.LerayHirsch.zetaPow` at `1`, which is a
`cohTransport`-free statement because `2 * 1` and `2` are definitionally equal. -/
theorem zetaPow_one_eq_zeta (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] :
    Work.LerayHirsch.zetaPow Z 1 = Work.LerayHirsch.zeta Z := by
  show Work.Whitney.cupChern 0 1 (Work.Thom.cohTransport (rfl : 2 * 0 = 2 * 0)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (Work.LerayHirsch.ProjSpace Z))))
      (Work.LerayHirsch.zeta Z) = Work.LerayHirsch.zeta Z
  rw [Work.Gen.cupChern_cast_left (a := 0) (a' := 0) (b := 1)
    (h := (rfl : 2 * 0 = 2 * 0))
    (x := Work.Cohomology.oneH ℤ (Work.Whitney.ssB (Work.LerayHirsch.ProjSpace Z)))
    (y := Work.LerayHirsch.zeta Z)]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ _).trans
    (Work.LerayHirsch.cohTransport_cupChern_one_left 1 (Work.LerayHirsch.zeta Z))

/-- **The `i = 1` Leray–Hirsch summand is multiplication by `ζ`** (the companion of the available
`Work.LerayHirsch.lhTerm_zero_index`, which is the `i = 0` summand). -/
theorem lhTerm_one_index (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {k : ℕ} (hk : 1 ≤ k) (hm : 1 < m) (x : Coh ℤ (2 * (k - 1)) B) :
    Work.LerayHirsch.lhTerm Z k ⟨⟨1, hm⟩, hk⟩ x
      = cohTransport (by omega : 2 * ((k - 1) + 1) = 2 * k)
          (Work.Whitney.cupChern (k - 1) 1
            ((CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * (k - 1))).hom x)
            (Work.LerayHirsch.zeta Z)) := by
  rw [Work.LerayHirsch.lhTerm_def, zetaPow_one_eq_zeta Z]

/-! ## The `ζ`-shift of a Leray–Hirsch summand -/

end

end Work.Gen
