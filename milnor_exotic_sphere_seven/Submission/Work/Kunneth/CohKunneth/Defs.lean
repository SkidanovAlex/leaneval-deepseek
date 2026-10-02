import Mathlib
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The class of a cocycle under a cochain map -/

theorem cochHomologyMap_apply_homologyπ (K L : CochainComplex (ModuleCat ℤ) ℕ)
    (f : K ⟶ L) (n : ℕ) (z : ↥(K.cycles n)) :
    (HomologicalComplex.homologyMap f n).hom ((K.homologyπ n).hom z)
      = (L.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom z) := by
  have h := congrArg (fun (m : K.cycles n ⟶ L.homology n) => ModuleCat.Hom.hom m z)
    (HomologicalComplex.homologyπ_naturality f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

theorem coch_iCycles_cyclesMap (K L : CochainComplex (ModuleCat ℤ) ℕ) (f : K ⟶ L) (n : ℕ)
    (z : ↥(K.cycles n)) :
    (L.iCycles n).hom ((HomologicalComplex.cyclesMap f n).hom z)
      = (f.f n).hom ((K.iCycles n).hom z) := by
  have h := congrArg (fun (m : K.cycles n ⟶ L.X n) => ModuleCat.Hom.hom m z)
    (HomologicalComplex.cyclesMap_i f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-! ## The tensor cochain `α ⊗ β` in a single bidegree -/

def tensorCochain (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ) : tpX C D n →ₗ[ℤ] ℤ :=
  (TensorProduct.dualDistrib ℤ ↥(C.X pq.1.1) ↥(D.X pq.1.2) (α ⊗ₜ[ℤ] β)).comp
    ((LinearMap.proj (R := ℤ) (φ := fun rs : tpIdx n => tpSummand C D rs.1.1 rs.1.2) pq).comp
      (DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
        (fun rs => tpSummand C D rs.1.1 rs.1.2)).toLinearMap)

theorem tensorCochain_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ) (x : tpX C D n) :
    tensorCochain C D n pq α β x
      = TensorProduct.dualDistrib ℤ ↥(C.X pq.1.1) ↥(D.X pq.1.2) (α ⊗ₜ[ℤ] β)
          (((DirectSum.linearEquivFunOnFintype ℤ (tpIdx n)
            (fun rs => tpSummand C D rs.1.1 rs.1.2)) x) pq) := by
  rw [tensorCochain]
  rfl

theorem tensorCochain_tpLof (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (z : tpSummand C D pq.1.1 pq.1.2) :
    tensorCochain C D n pq α β (tpLof C D n pq z)
      = TensorProduct.dualDistrib ℤ ↥(C.X pq.1.1) ↥(D.X pq.1.2) (α ⊗ₜ[ℤ] β) z := by
  rw [tensorCochain_apply, DirectSum.linearEquivFunOnFintype_lof, Pi.single_eq_same]

theorem tensorCochain_tpLof_eq_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    {rs : tpIdx n} (h : rs ≠ pq) (z : tpSummand C D rs.1.1 rs.1.2) :
    tensorCochain C D n pq α β (tpLof C D n rs z) = 0 := by
  rw [tensorCochain_apply, DirectSum.linearEquivFunOnFintype_lof,
    Pi.single_eq_of_ne (Ne.symm h)]
  exact map_zero _

theorem tensorCochain_tpLof_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (u : ↥(C.X pq.1.1)) (v : ↥(D.X pq.1.2)) :
    tensorCochain C D n pq α β (tpLof C D n pq (u ⊗ₜ[ℤ] v)) = α u * β v := by
  rw [tensorCochain_tpLof, TensorProduct.dualDistrib_apply]

/-! ## The cocycle property -/

theorem cocycle_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) (γ : ↥(C.X m) →ₗ[ℤ] ℤ)
    (h : (Work.Cohomology.dualComplex ℤ C).d m (m + 1) γ = 0) (w : ↥(C.X (m + 1))) :
    γ ((C.d (m + 1) m).hom w) = 0 := by
  have h' := congrArg (fun (f : ↥(C.X (m + 1)) →ₗ[ℤ] ℤ) => f w) h
  simpa [Work.Cohomology.dualComplex, CochainComplex.of_d, Work.Cohomology.dualDiff,
    ModuleCat.hom_ofHom] using h'

/-- The first (∂ ⊗ 1) term of the Koszul differential is killed by the tensor cochain. -/
theorem tensorCochain_tpDpq_first (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (hα : (Work.Cohomology.dualComplex ℤ C).d pq.1.1 (pq.1.1 + 1) α = 0)
    (rs : tpIdx (n + 1)) (hp : 1 ≤ rs.1.1) (u : ↥(C.X rs.1.1)) (v : ↥(D.X rs.1.2)) :
    tensorCochain C D n pq α β
      (tpLof C D n ⟨(rs.1.1 - 1, rs.1.2), by omega⟩
        (((C.d rs.1.1 (rs.1.1 - 1)).hom u) ⊗ₜ[ℤ] v)) = 0 := by
  by_cases h : (⟨(rs.1.1 - 1, rs.1.2), by omega⟩ : tpIdx n) = pq
  · have e1 : rs.1.1 - 1 = pq.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
    have e2 : rs.1.2 = pq.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
    have hsum : (pq.1.1 + 1) + pq.1.2 = n + 1 := by omega
    have hrs1 : rs.1.1 = pq.1.1 + 1 := by rw [← Nat.sub_add_cancel hp, e1]
    have hrs : rs = ⟨(pq.1.1 + 1, pq.1.2), hsum⟩ := Subtype.ext (Prod.ext hrs1 e2)
    subst hrs
    dsimp only
    refine (tensorCochain_tpLof_tmul C D n pq α β ((C.d (pq.1.1 + 1) pq.1.1).hom u) v).trans ?_
    rw [cocycle_apply C pq.1.1 α hα u, zero_mul]
  · rw [tensorCochain_tpLof_eq_zero C D n pq α β h]

/-- The second ((-1)^p • 1 ⊗ ∂) term of the Koszul differential is killed by the tensor
cochain. -/
theorem tensorCochain_tpDpq_second (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (hβ : (Work.Cohomology.dualComplex ℤ D).d pq.1.2 (pq.1.2 + 1) β = 0)
    (rs : tpIdx (n + 1)) (hq : 1 ≤ rs.1.2) (u : ↥(C.X rs.1.1)) (v : ↥(D.X rs.1.2)) :
    tensorCochain C D n pq α β
      ((-1 : ℤ) ^ rs.1.1 • tpLof C D n ⟨(rs.1.1, rs.1.2 - 1), by omega⟩
        (u ⊗ₜ[ℤ] ((D.d rs.1.2 (rs.1.2 - 1)).hom v))) = 0 := by
  rw [map_zsmul]
  by_cases h : (⟨(rs.1.1, rs.1.2 - 1), by omega⟩ : tpIdx n) = pq
  · have e1 : rs.1.1 = pq.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
    have e2 : rs.1.2 - 1 = pq.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
    have hsum : pq.1.1 + (pq.1.2 + 1) = n + 1 := by omega
    have hrs2 : rs.1.2 = pq.1.2 + 1 := by rw [← Nat.sub_add_cancel hq, e2]
    have hrs : rs = ⟨(pq.1.1, pq.1.2 + 1), hsum⟩ := Subtype.ext (Prod.ext e1 hrs2)
    subst hrs
    dsimp only
    have hh : tensorCochain C D n pq α β
        (tpLof C D n pq (u ⊗ₜ[ℤ] ((D.d (pq.1.2 + 1) pq.1.2).hom v))) = 0 := by
      rw [tensorCochain_tpLof_tmul, cocycle_apply D pq.1.2 β hβ v, mul_zero]
    exact (congrArg (fun w => (-1 : ℤ) ^ pq.1.1 • w) hh).trans (zsmul_zero _)
  · rw [tensorCochain_tpLof_eq_zero C D n pq α β h, zsmul_zero]

theorem tensorCochain_tpDpq_eq_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (hα : (Work.Cohomology.dualComplex ℤ C).d pq.1.1 (pq.1.1 + 1) α = 0)
    (hβ : (Work.Cohomology.dualComplex ℤ D).d pq.1.2 (pq.1.2 + 1) β = 0)
    (rs : tpIdx (n + 1)) (z : tpSummand C D rs.1.1 rs.1.2) :
    tensorCochain C D n pq α β (tpDpq C D n rs z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      rw [tpDpq_tmul, map_add,
        apply_dite (tensorCochain C D n pq α β) (1 ≤ rs.1.1),
        apply_dite (tensorCochain C D n pq α β) (1 ≤ rs.1.2)]
      by_cases hp : 1 ≤ rs.1.1 <;> by_cases hq : 1 ≤ rs.1.2
      · rw [dif_pos hp, dif_pos hq,
          tensorCochain_tpDpq_first C D n pq α β hα rs hp u v,
          tensorCochain_tpDpq_second C D n pq α β hβ rs hq u v]
        simp
      · rw [dif_pos hp, dif_neg hq,
          tensorCochain_tpDpq_first C D n pq α β hα rs hp u v]
        simp
      · rw [dif_neg hp, dif_pos hq,
          tensorCochain_tpDpq_second C D n pq α β hβ rs hq u v]
        simp
      · rw [dif_neg hp, dif_neg hq]
        simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

/-- The differential of the dual complex, on an element. -/
theorem dualComplex_d_apply_hom (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (f : ↥((Work.Cohomology.dualComplex ℤ K).X n)) :
    ((Work.Cohomology.dualComplex ℤ K).d n (n + 1)).hom f
      = f.comp ((K.d (n + 1) n).hom) := by
  rw [Work.Cohomology.dualComplex_d_self]
  exact Work.Cohomology.dualHom_hom_apply ℤ ((K.d (n + 1) n)) f

/-- The tensor cochain vanishes on a Koszul boundary, in the "pure" form. -/
theorem tensorCochain_comp_tpD_eq_zero (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (hα : (Work.Cohomology.dualComplex ℤ C).d pq.1.1 (pq.1.1 + 1) α = 0)
    (hβ : (Work.Cohomology.dualComplex ℤ D).d pq.1.2 (pq.1.2 + 1) β = 0) :
    (tensorCochain C D n pq α β).comp (tpD C D n) = 0 := by
  apply DirectSum.linearMap_ext ℤ
  intro rs
  rw [LinearMap.comp_assoc, tpD_comp_tpLof, LinearMap.zero_comp]
  apply LinearMap.ext
  intro z
  exact tensorCochain_tpDpq_eq_zero C D n pq α β hα hβ rs z

theorem tensorCochain_isCocycle (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (β : ↥(D.X pq.1.2) →ₗ[ℤ] ℤ)
    (hα : (Work.Cohomology.dualComplex ℤ C).d pq.1.1 (pq.1.1 + 1) α = 0)
    (hβ : (Work.Cohomology.dualComplex ℤ D).d pq.1.2 (pq.1.2 + 1) β = 0) :
    (Work.Cohomology.dualComplex ℤ (tpC C D)).d n (n + 1)
      (tensorCochain C D n pq α β) = 0 := by
  rw [dualComplex_d_apply_hom]
  rw [show ((tpC C D).d (n + 1) n) = ModuleCat.ofHom (tpD C D n) from tpC_d C D n]
  rw [ModuleCat.hom_ofHom]
  exact tensorCochain_comp_tpD_eq_zero C D n pq α β hα hβ

/-- The differential of the dual complex of the singular chains of a simplicial set is the
coboundary `Work.Cohomology.cochainDiff` of cochains. -/
theorem dualComplex_d_apply_eq_cochainDiff (X : SSet) (n : ℕ)
    (α : Work.Cohomology.Cochain ℤ X n) :
    ((Work.Cohomology.dualComplex ℤ (sChain X)).d n (n + 1)).hom α
      = Work.Cohomology.cochainDiff ℤ X α := by
  rw [dualComplex_d_apply_hom]
  rfl

/-- The coboundary of a cochain is the differential of the dual complex. -/
theorem cochainDiff_eq_dualComplex_d (X : SSet) (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n) :
    Work.Cohomology.cochainDiff ℤ X α
      = ((Work.Cohomology.dualComplex ℤ (sChain X)).d n (n + 1)).hom α :=
  (dualComplex_d_apply_eq_cochainDiff X n α).symm

/-- The class of a cycle of the dual complex, computed in the `SSetCochainComplex` spelling. -/
theorem cohomologyClassOf_eq_homologyπ_dual (X : SSet) (n : ℕ)
    (z : ↥((Work.Cohomology.dualComplex ℤ (sChain X)).cycles n))
    (h : Work.Cohomology.cochainDiff ℤ X
      ((Work.Cohomology.dualComplex ℤ (sChain X)).iCycles n z) = 0) :
    Work.Cohomology.cohomologyClassOf ℤ X
        ((Work.Cohomology.dualComplex ℤ (sChain X)).iCycles n z) h
      = ((Work.Cohomology.dualComplex ℤ (sChain X)).homologyπ n).hom z :=
  Work.Cohomology.cohomologyClassOf_eq_homologyπ ℤ X n z

end

end Work.Kunneth
