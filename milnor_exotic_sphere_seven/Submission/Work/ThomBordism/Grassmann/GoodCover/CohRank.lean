import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.thomSpaceCohomology_of_lowDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# §4bis, the Thom-space part: `H^{k+8}(Th γ;ℚ)` is finite dimensional of rank `≤ 2`

The lead's request §4bis asks for the non-vacuous `FiniteDimensional` / `Module.rank` forms (since
`Module.finrank ℚ X = 0` on an infinite-dimensional `X`).  For the **Thom space** these are direct
consequences of the bijectivity of `thomSpaceBasisMap` (`ThomSpaceCohomology`, proved in
`GoodCover/thomSpaceCohomology_of_lowDegree.lean`): the two classes `p₁(γ)²⌣U`, `p₂(γ)⌣U` span, so
the module is a quotient of `ℚ × ℚ`.
-/

open scoped Topology TensorProduct
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- The linear map `(a,b) ↦ a • x + b • y`. -/
def spanPairMap (M : Type*) [AddCommMonoid M] [Module ℚ M] (x y : M) : ℚ × ℚ →ₗ[ℚ] M where
  toFun p := p.1 • x + p.2 • y
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c p := by
    show (c * p.1) • x + (c * p.2) • y = c • (p.1 • x + p.2 • y)
    rw [smul_add, smul_smul, smul_smul]

/-- **The two Thom classes span `H^{k+8}(Th γ;ℚ)`.** -/
theorem surjective_thomSpaceSpanMap (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    Function.Surjective (spanPairMap _ ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP1SqU k m U))
      ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP2U k m U))) :=
  (GoodCover.thomSpaceCohomology_of_lowDegree k m hk hm U).2.surjective

/-- **`H^{k+8}(Th γ;ℚ)` is finite dimensional over `ℚ`.** -/
theorem finiteDimensional_thomSpaceCohomology (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology (8 + k) (sset (TautologicalThomSpace k m))) :=
  Module.Finite.of_surjective (spanPairMap _ ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP1SqU k m U))
    ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP2U k m U))) (surjective_thomSpaceSpanMap k m hk hm U)

/-- **`Module.rank ℚ H^{k+8}(Th γ;ℚ) ≤ 2`.** -/
theorem rank_thomSpaceCohomology_le_two (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    Module.rank ℚ
      (Work.SignatureBordism.ratCohomology (8 + k) (sset (TautologicalThomSpace k m))) ≤ 2 := by
  have h := LinearMap.rank_le_of_surjective (spanPairMap _
    ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP1SqU k m U)) ((1 : ℚ) ⊗ₜ[ℤ] (thomSpaceP2U k m U)))
    (surjective_thomSpaceSpanMap k m hk hm U)
  have h2 : Module.rank ℚ (ℚ × ℚ) = 2 := by
    rw [← Module.finrank_eq_rank, Module.finrank_prod, Module.finrank_self]
    norm_num
  rwa [h2] at h

end

end Work.ThomBordism.Grassmann
