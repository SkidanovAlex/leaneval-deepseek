import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.ThomSpaceCoh
import Submission.Work.ThomBordism.Grassmann.lowDegreeCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann.GoodCover

set_option linter.style.haveILetI false

open scoped TensorProduct

noncomputable section

/-! ## A small tensor-product bookkeeping lemma

`TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e` is a `ℤ`-linear equivalence, but both sides carry a
`ℚ`-module structure (from the left factor `ℚ`), and the equivalence is in fact `ℚ`-linear: this is
the pure-tensor computation `q • (a ⊗ x) ↦ (q * a) ⊗ (e x)`.  We record it here because the
transport of `thomBasisMap` to `thomSpaceBasisMap` is exactly this compatibility, applied to the
tensors `1 ⊗ p₁²` and `1 ⊗ p₂`. -/
theorem tensorProduct_congr_refl_smul {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (q : ℚ) (z : ℚ ⊗[ℤ] M) :
    TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e (q • z)
      = q • TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul, TensorProduct.congr_tmul]
      rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Item 2, space level: the rational cohomology of the Thom space in low degrees, and the basis
`p₁(γ)²⌣U`, `p₂(γ)⌣U` of `H^{k+8}(Th γ;ℚ)`.**

This is the space-level counterpart of `Work.ThomBordism.Grassmann.ThomPairCohomology`: the
vanishing `H^{k+j}(Th γ;ℚ) = 0` for `j ∈ {1,2,3,5,6,7}` and the bijectivity of
`thomSpaceBasisMap k m U : ℚ × ℚ → H^{k+8}(Th γ;ℚ)`, `(a,b) ↦ a • p₁(γ)²⌣U + b • p₂(γ)⌣U`.

Route.  Both clauses are the pair-level clauses of
`Work.ThomBordism.Grassmann.thomPairCohomology_of_lowDegree`
(`Work.ThomBordism.Grassmann.lowDegreeCohomology k m` supplies its `LowDegreeCohomology k m` input,
and it is unconditional in `U`) transported along the canonical comparison
`thomSpaceIso k m n (1 ≤ n) : OpenThom γ n ≃ₗ[ℤ] H^n(Th γ;ℤ)` of `GoodCover/ThomSpaceCoh.lean`
(proved in `Torsion/thomSpaceCohomologyIso.lean`, §4ter): tensoring a `ℤ`-linear equivalence with
`ℚ` gives an equivalence of `Work.SignatureBordism.ratCohomology`'s, along which `Subsingleton`
transfers (the underlying maps are surjective).  For the second clause, `thomSpaceBasisMap k m U` is
the composite of `thomBasisMap k m U` with
`TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (thomSpaceIso k m (8+k) _)`, so bijectivity follows from
the bijectivity of `thomBasisMap`.  Every index `n = k + j` occurring here satisfies `1 ≤ n`
(`j ∈ lowDegrees`, `k ≥ 10`), so the `hn` side condition of `thomSpaceCohomologyIso` is discharged by
`omega`. -/
theorem thomSpaceCohomology_of_lowDegree (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (U : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k m) k) :
    Work.ThomBordism.Grassmann.ThomSpaceCohomology k m U := by
  have hpair := thomPairCohomology_of_lowDegree (lowDegreeCohomology k m) hk hm hk hm U
  refine ⟨?_, ?_⟩
  · -- the vanishing: transport `Subsingleton` along the comparison tensored with `ℚ`
    intro j hj
    have h := hpair.1 j hj
    have hj1 : 1 ≤ j := by
      simp only [lowDegrees, Finset.mem_insert, Finset.mem_singleton] at hj
      omega
    refine ⟨fun a b => ?_⟩
    let e := TensorProduct.congr (LinearEquiv.refl ℤ ℚ)
      (thomSpaceIso k m (k + j) (by omega))
    haveI : Subsingleton
        (ℚ ⊗[ℤ] Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle k m)
          (k + j)) := h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [Subsingleton.elim x y]
  · -- the basis: `thomSpaceBasisMap` is `thomBasisMap` followed by the comparison
    have hfun : thomSpaceBasisMap k m U = fun p : ℚ × ℚ =>
        (TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (thomSpaceIso k m (8 + k) (by omega)))
          (thomBasisMap k m U p) := by
      funext p
      simp only [thomSpaceBasisMap, thomBasisMap, thomCupU]
      rw [map_add]
      rw [tensorProduct_congr_refl_smul (e := thomSpaceIso k m (8 + k) (by omega)) (q := p.1)]
      rw [tensorProduct_congr_refl_smul (e := thomSpaceIso k m (8 + k) (by omega)) (q := p.2)]
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, thomSpaceP1SqU, thomSpaceP2U]
    rw [hfun]
    exact ((TensorProduct.congr (LinearEquiv.refl ℤ ℚ)
      (thomSpaceIso k m (8 + k) (by omega))).bijective.comp hpair.2.2)

end

end Work.ThomBordism.Grassmann.GoodCover
