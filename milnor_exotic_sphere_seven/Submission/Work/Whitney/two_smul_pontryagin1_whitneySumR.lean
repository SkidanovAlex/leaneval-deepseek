import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.conjComplexification
import Submission.Work.Whitney.pontryagin1_line
import Submission.Work.Whitney.pontryagin1_whitneySum_line
import Submission.Work.Whitney.complexificationCore_whitneySumR
import Submission.Work.LerayHirsch.whitneySumFormula_one_one_of_topClassMul
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Additivity of `p₁` for a real Whitney sum, from the Whitney formula in degree `2`

The first Pontryagin class of a real bundle is normalised by
`Work.Thom.pontryagin1 Z = - c₂(Z ⊗_ℝ ℂ)`.  Complexification is *additive*
(`Work.Whitney.complexificationCore_whitneySumR`) and the Whitney sum formula in degree `2`
computes the second Chern class of a sum as

  `c₂(Z₁ ⊕ Z₂) = c₂(Z₁) + c₁(Z₁) ⌣ c₁(Z₂) + c₂(Z₂)`.

So for real bundles `E`, `F`,

  `p₁(E ⊕ F) = p₁(E) + p₁(F) - c₁(E_ℂ) ⌣ c₁(F_ℂ)`,

and the correction term is `2`-torsion, because `c₁` of a complexified real bundle is: the
complexification is its own conjugate (`Work.Whitney.conjCore_complexificationCore`) and conjugation
negates odd Chern classes (`Work.Whitney.chernClass_complexification_add_self`).  Hence

  `2 • p₁(E ⊕ F) = 2 • (p₁(E) + p₁(F))`,

which is the sharp integral statement — the factor `2` cannot be removed (see
`README.md`, ADDENDUM W3, and the rank-`(1,1)` instance
`Work.Whitney.two_smul_pontryagin1_whitneySumR_line`).

The content of this module is the bookkeeping: the degree-`2` collapse of
`Work.Whitney.chernProductSum` in arbitrary ranks, and the `2`-torsion cancellation.
The Whitney sum formula itself enters only through the degree-`2` hypothesis `hW2` (which the
WHITNEY chapter supplies), so this lemma is independent of the rest of the formula.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The degree-`2` collapse of the right-hand side of the Whitney formula** in arbitrary ranks:
of the three summands `c_0(Z₁) ⌣ c_2(Z₂)`, `c_1(Z₁) ⌣ c_1(Z₂)`, `c_2(Z₁) ⌣ c_0(Z₂)`, the outer two
are the unit laws `1 ⌣ x = x` and `x ⌣ 1 = x`. -/
theorem chernProductSum_two_eq {B : Type} [TopologicalSpace B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ : ℕ}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    chernProductSum Z₁ Z₂ 2
      = chernClass m₂ 2 Z₂
        + cupChern 1 1 (chernClass m₁ 1 Z₁) (chernClass m₂ 1 Z₂)
        + chernClass m₁ 2 Z₁ := by
  -- The degree cast `n = n` (which is the only kind occurring after the numerical reduction)
  -- is the identity on cohomology.
  have htrans : ∀ {n : ℕ} (h : n = n) (x : Coh ℤ n B), cohTransport h x = x := by
    intro n h x
    rw [Subsingleton.elim h rfl, cohTransport_rfl]
  rw [chernProductSum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos (by norm_num : (0 : ℕ) ≤ 2), dif_pos (by norm_num : (1 : ℕ) ≤ 2),
    dif_pos (by norm_num : (2 : ℕ) ≤ 2)]
  simp only [chernSummand_def, chernClass_zero_eq_oneH, cupChern_def,
    Work.Cohomology.cupH'_one_left, Work.Cohomology.cupH'_one_right, htrans,
    Nat.reduceMul, Nat.add_zero]

/-- **The `2`-torsion cancellation of the correction term**: if `cup` is its own negative
(`cup + cup = 0`, in additive notation) then the mixed term `cup` in the degree-`2` expansion of
`chernProductSum` can simply be dropped when working modulo `2`. -/
theorem two_zsmul_neg_add_cancel {G : Type} [AddCommGroup G] (e f cup : G)
    (hc : cup + cup = 0) :
    (2 : ℤ) • (-(f + cup + e)) = (2 : ℤ) • (-e + -f) := by
  have h2 : (2 : ℤ) • cup = 0 := by rw [two_zsmul]; exact hc
  simp only [smul_add, smul_neg, h2, add_zero]
  abel

/-- **Additivity of `p₁` under a real Whitney sum, modulo `2`.**

`p₁(E ⊕ F) = p₁(E) + p₁(F) - c₁(E_ℂ) ⌣ c₁(F_ℂ)` and the correction is `2`-torsion, so after
multiplying by `2` the correction disappears.  The only input is the degree-`2` Whitney sum formula
for complex bundles (`hW2`) — the rest is the normalisation `p₁ = -c₂(· ⊗_ℝ ℂ)`, the additivity of
complexification, and the `2`-torsion of odd Chern classes of a complexification. -/
theorem two_smul_pontryagin1_whitneySumR
    (hW2 : ∀ {B' : Type} [TopologicalSpace B'] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      {m n : ℕ} (Z₁ : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin m)) ι₁)
      (Z₂ : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin n)) ι₂),
      Work.Thom.chernClass (m + n) 2 (Work.Whitney.whitneySum Z₁ Z₂)
        = Work.Whitney.chernProductSum Z₁ Z₂ 2)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {k l : ℕ} (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι₁)
    (F : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin l)) ι₂) :
    (2 : ℤ) • Work.Thom.pontryagin1 (Work.Whitney.whitneySumR E F)
      = (2 : ℤ) • (Work.Thom.pontryagin1 E + Work.Thom.pontryagin1 F) := by
  -- Unfold the Pontryagin classes and complexify the direct sum.
  rw [Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def,
    Work.Whitney.complexificationCore_whitneySumR]
  -- The Whitney sum formula in degree `2`, and the collapse of its right-hand side.
  rw [hW2 (Work.Thom.complexificationCore E) (Work.Thom.complexificationCore F),
    chernProductSum_two_eq (Work.Thom.complexificationCore E) (Work.Thom.complexificationCore F)]
  -- The correction term `c₁(E_ℂ) ⌣ c₁(F_ℂ)` is `2`-torsion, because `c₁(E_ℂ)` is.
  have hx : Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E)
      + Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E) = 0 :=
    Work.Whitney.chernClass_complexification_add_self (B := B) (k := k) (j := 1) (by decide) E
  have hcup : Work.Whitney.cupChern 1 1
        (Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E))
        (Work.Thom.chernClass l 1 (Work.Thom.complexificationCore F))
      + Work.Whitney.cupChern 1 1
        (Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E))
        (Work.Thom.chernClass l 1 (Work.Thom.complexificationCore F)) = 0 := by
    rw [← Work.Whitney.cupChern_add_left, hx, Work.Whitney.cupChern_zero_left]
  exact two_zsmul_neg_add_cancel _ _ _ hcup

end

end Work.Whitney
