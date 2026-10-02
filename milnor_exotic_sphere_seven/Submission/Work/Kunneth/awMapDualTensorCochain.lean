import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Kunneth.CohKunneth.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The transpose of the Alexander–Whitney map on the tensor cochain `α ⊗ β`

`Work.Kunneth.awMapDualTensorCochain` computes the transpose of the Alexander–Whitney map
`awMap X Y : sChain (sProd X Y) ⟶ tChain X Y` on the tensor cochain
`tensorCochain (sChain X) (sChain Y) (p+q) ⟨(p,q), rfl⟩ α β` of the Koszul tensor product of
`Submission/Work/Kunneth/CohKunneth/Defs.lean`: the result is the cross product cochain
`crossCochain X Y p q α β`.

Equivalently, in terms of the linear functionals on singular chains,

`(α ⊗ β)(Σ_{p+q=n} σ_front ⊗ τ_back) = α(σ_front) · β(τ_back)`.

The proof is the computation rule `tensorCochain_awGen_one` for the value of the tensor cochain on
the Alexander–Whitney chain `awGen` of a simplex of `X ⊗ Y` (the summand of bidegree `(p,q)` of the
Koszul direct sum survives, all others are killed by `tensorCochain_tpLof_eq_zero`), together with
`crossCochain_apply`; the identity of the two functionals is then checked on the generators of the
singular chains, using the coproduct universal property in Mathlib's
`SSet.chainComplex_hom_ext` (`linearMap_ext_genCh` below).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

/-- The Alexander–Whitney generator expansion of the degree-`n` chain of a simplex, indexed by
the bidegrees `pq : tpIdx n` of the Koszul tensor product instead of by `Fin (n+1)`. -/
lemma awGen_hom_one_tpIdx (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n⦌) :
    (awGen X Y n z).hom 1
      = ∑ pq : tpIdx n, tpLof (sChain X) (sChain Y) n pq
          (genCh X (Work.Cohomology.frontFace X pq.1.1 n (by omega) z.1) ⊗ₜ[ℤ]
            genCh Y (backFaceLE Y pq.1.2 n (by omega) z.2)) := by
  rw [awGen_hom_one]
  exact Fintype.sum_equiv (tpIdxEquivFin n).symm _ _ (fun k => rfl)

/-- **The tensor cochain on the Alexander–Whitney chain of a simplex.**  Only the summand of
bidegree `(p,q)` contributes, and the value is `α(σ_front) · β(τ_back)`. -/
theorem tensorCochain_awGen_one (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q)
    (z : (sProd X Y) _⦋p+q⦌) :
    tensorCochain (sChain X) (sChain Y) (p+q) ⟨(p,q), rfl⟩ α β ((awGen X Y (p+q) z).hom 1)
      = Work.Cohomology.genEval ℤ X α (Work.Cohomology.frontFace X p (p+q) (by omega) z.1)
        * Work.Cohomology.genEval ℤ Y β (backFaceLE Y q (p+q) (by omega) z.2) := by
  rw [awGen_hom_one_tpIdx, map_sum]
  rw [Finset.sum_eq_single (⟨(p,q), rfl⟩ : tpIdx (p+q))]
  · rw [tensorCochain_tpLof_tmul]
    simp only [Work.Cohomology.genEval, genCh]
  · intro rs _ hrs
    exact tensorCochain_tpLof_eq_zero _ _ _ _ _ _ hrs _
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Two linear functionals on the singular `n`-chains of a simplicial set agree as soon as they
agree on the generators (the coproduct universal property of `SSet.chainComplexXCofan`). -/
lemma linearMap_ext_genCh {X : SSet} {n : ℕ}
    {f g : ↥((sChain X).X n) →ₗ[ℤ] ℤ}
    (h : ∀ σ, f (genCh X σ) = g (genCh X σ)) : f = g := by
  have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (R := zz)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact h σ
  simpa using congrArg ModuleCat.Hom.hom hfg

theorem awMapDualTensorCochain (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℤ X p) (β : Work.Cohomology.Cochain ℤ Y q) :
    ((Work.Cohomology.dualComplexMap ℤ (sChain (sProd X Y)) (tChain X Y)
        (awMap X Y)).f (p + q)).hom
      (tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β)
      = crossCochain X Y p q α β := by
  rw [Work.Cohomology.dualComplexMap_f]
  change (tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β).comp
      ((awMap X Y).f (p + q)).hom = crossCochain X Y p q α β
  rw [awMap_f]
  apply linearMap_ext_genCh
  intro z
  show tensorCochain (sChain X) (sChain Y) (p + q) ⟨(p, q), rfl⟩ α β
        ((awHom X Y (p + q)).hom (genCh (sProd X Y) z))
      = (crossCochain X Y p q α β) (genCh (sProd X Y) z)
  have h := congrArg (fun (m : zz ⟶ (tChain X Y).X (p+q)) => m.hom 1) (awHom_gen X Y (p+q) z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, tensorCochain_awGen_one]
  exact (crossCochain_apply X Y p q α β z).symm

end

end Work.Kunneth
