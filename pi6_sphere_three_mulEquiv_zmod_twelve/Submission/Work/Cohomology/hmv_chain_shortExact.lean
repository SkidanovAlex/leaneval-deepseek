import Mathlib
import Submission.Work.Cohomology.relCohMV_honest_prereq
import Submission.Work.Cohomology.Crux.Transgression

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## 1. The canonical identification `cruxMid ≅ relMVUU ⊞ relMVVV`

The canonical middle term `cruxMid = cokernel (τ₂U ⊞ τ₂V)` of the relative Mayer–Vietoris
sequence is the biproduct `cokernel τ₂U ⊞ cokernel τ₂V = relMVUU ⊞ relMVVV`.  We record the
explicit maps `κU, κV` (the projections) and `κU', κV'` (the inclusions) together with their
composition rules. -/

/-- The `U`-projection of the canonical middle term. -/
abbrev mvKappaU (X : TopCat) (A U V : Set X) :
    cruxMid X A U V ⟶ relMVUU X A U V :=
  cokernel.map (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) (relMVτ₂U U V A)
    biprod.fst biprod.fst (biprod.map_fst _ _)

/-- The `V`-projection of the canonical middle term. -/
abbrev mvKappaV (X : TopCat) (A U V : Set X) :
    cruxMid X A U V ⟶ relMVVV X A U V :=
  cokernel.map (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) (relMVτ₂V U V A)
    biprod.snd biprod.snd (biprod.map_snd _ _)

/-- The `U`-inclusion into the canonical middle term. -/
abbrev mvKappaU' (X : TopCat) (A U V : Set X) :
    relMVUU X A U V ⟶ cruxMid X A U V :=
  cokernel.map (relMVτ₂U U V A) (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))
    biprod.inl biprod.inl (biprod.inl_map _ _).symm

/-- The `V`-inclusion into the canonical middle term. -/
abbrev mvKappaV' (X : TopCat) (A U V : Set X) :
    relMVVV X A U V ⟶ cruxMid X A U V :=
  cokernel.map (relMVτ₂V U V A) (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))
    biprod.inr biprod.inr (biprod.inr_map _ _).symm

theorem mvKappaU_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) ≫ mvKappaU X A U V
      = biprod.fst ≫ cokernel.π (relMVτ₂U U V A) :=
  cokernel_π_map _ _ _ _ _

theorem mvKappaV_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) ≫ mvKappaV X A U V
      = biprod.snd ≫ cokernel.π (relMVτ₂V U V A) :=
  cokernel_π_map _ _ _ _ _

theorem mvKappaU'_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂U U V A) ≫ mvKappaU' X A U V
      = biprod.inl ≫ cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) :=
  cokernel_π_map _ _ _ _ _

theorem mvKappaV'_comp (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₂V U V A) ≫ mvKappaV' X A U V
      = biprod.inr ≫ cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) :=
  cokernel_π_map _ _ _ _ _

theorem mvKappaU'_kappaU (X : TopCat) (A U V : Set X) :
    mvKappaU' X A U V ≫ mvKappaU X A U V = 𝟙 (relMVUU X A U V) := by
  apply (cancel_epi (cokernel.π (relMVτ₂U U V A))).1
  rw [← Category.assoc, mvKappaU'_comp, Category.assoc, mvKappaU_comp, ← Category.assoc,
    biprod.inl_fst]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem mvKappaV'_kappaV (X : TopCat) (A U V : Set X) :
    mvKappaV' X A U V ≫ mvKappaV X A U V = 𝟙 (relMVVV X A U V) := by
  apply (cancel_epi (cokernel.π (relMVτ₂V U V A))).1
  rw [← Category.assoc, mvKappaV'_comp, Category.assoc, mvKappaV_comp, ← Category.assoc,
    biprod.inr_snd]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem mvKappaU'_kappaV (X : TopCat) (A U V : Set X) :
    mvKappaU' X A U V ≫ mvKappaV X A U V = 0 := by
  apply (cancel_epi (cokernel.π (relMVτ₂U U V A))).1
  rw [← Category.assoc, mvKappaU'_comp, Category.assoc, mvKappaV_comp, ← Category.assoc,
    biprod.inl_snd]
  simp only [zero_comp, comp_zero]

theorem mvKappaV'_kappaU (X : TopCat) (A U V : Set X) :
    mvKappaV' X A U V ≫ mvKappaU X A U V = 0 := by
  apply (cancel_epi (cokernel.π (relMVτ₂V U V A))).1
  rw [← Category.assoc, mvKappaV'_comp, Category.assoc, mvKappaU_comp, ← Category.assoc,
    biprod.inr_fst]
  simp only [zero_comp, comp_zero]

theorem mvKappa_sum (X : TopCat) (A U V : Set X) :
    mvKappaU X A U V ≫ mvKappaU' X A U V + mvKappaV X A U V ≫ mvKappaV' X A U V
      = 𝟙 (cruxMid X A U V) := by
  apply (cancel_epi (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)))).1
  have hU : cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))
        ≫ (mvKappaU X A U V ≫ mvKappaU' X A U V)
      = biprod.fst ≫ biprod.inl ≫ cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) := by
    rw [← Category.assoc, mvKappaU_comp, Category.assoc, mvKappaU'_comp]
  have hV : cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))
        ≫ (mvKappaV X A U V ≫ mvKappaV' X A U V)
      = biprod.snd ≫ biprod.inr ≫ cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) := by
    rw [← Category.assoc, mvKappaV_comp, Category.assoc, mvKappaV'_comp]
  rw [Preadditive.comp_add, hU, hV]
  simp only [← Category.assoc]
  rw [← Preadditive.add_comp, biprod.total]
  simp only [Category.id_comp, Category.comp_id]

/-! ## 2. The first two maps of the relative Mayer–Vietoris sequence -/

theorem pi_cruxF (X : TopCat) (A U V : Set X) :
    cokernel.π (relMVτ₁ U V A) ≫ cruxF X A U V
      = mvLeftSmall U V ≫ cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) := by
  rw [cruxF]
  exact cokernel_π_map _ _ _ _ _

theorem pi_cruxG (X : TopCat) (A U V : Set X) :
    cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) ≫ cruxG X A U V
      = mvRightSmall U V ≫ cokernel.π (relMVτ₃ U V A) := by
  rw [cruxG]
  exact cokernel_π_map _ _ _ _ _

theorem mvLeftSmall_fst (U V : Set X) :
    mvLeftSmall U V ≫ biprod.fst
      = subInclChain U V (Set.inter_subset_left : U ∩ V ⊆ U) := by
  rw [mvLeftSmall, biprod.lift_fst]

theorem mvLeftSmall_snd (U V : Set X) :
    mvLeftSmall U V ≫ biprod.snd
      = subInclChain U V (Set.inter_subset_right : U ∩ V ⊆ V) := by
  rw [mvLeftSmall, biprod.lift_snd]

theorem gamma_eq_cruxF (X : TopCat) (A U V : Set X) :
    HMV.gamma X A U V = cruxF X A U V ≫ mvKappaU X A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₁ U V A))).1
  rw [HMV.gamma_comp, ← Category.assoc, pi_cruxF, Category.assoc, mvKappaU_comp,
    ← Category.assoc, mvLeftSmall_fst]

theorem delta_eq_cruxF (X : TopCat) (A U V : Set X) :
    HMV.delta X A U V = cruxF X A U V ≫ mvKappaV X A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₁ U V A))).1
  rw [HMV.delta_comp, ← Category.assoc, pi_cruxF, Category.assoc, mvKappaV_comp,
    ← Category.assoc, mvLeftSmall_snd]

/-! ## 3. The second two maps of the relative Mayer–Vietoris sequence -/

theorem alphaU_eq_cruxG (X : TopCat) (A U V : Set X) :
    HMV.alphaU X A U V = mvKappaU' X A U V ≫ cruxG X A U V := by
  apply (cancel_epi (cokernel.π (relMVτ₂U U V A))).1
  rw [HMV.alphaU_comp, ← Category.assoc, mvKappaU'_comp, Category.assoc, pi_cruxG,
    ← Category.assoc, mvRightSmall, biprod.inl_desc]
  rfl

theorem alphaV_eq_cruxG (X : TopCat) (A U V : Set X) :
    HMV.alphaV X A U V = -(mvKappaV' X A U V ≫ cruxG X A U V) := by
  apply (cancel_epi (cokernel.π (relMVτ₂V U V A))).1
  rw [HMV.alphaV_comp, Preadditive.comp_neg, ← Category.assoc, mvKappaV'_comp,
    Category.assoc, pi_cruxG, ← Category.assoc, mvRightSmall, biprod.inr_desc,
    Preadditive.neg_comp, neg_neg]
  rfl

/-! ## 4. The canonical middle term as the biproduct, and the short exact sequence -/

/-- The canonical identification `cruxMid ⟶ relMVUU ⊞ relMVVV` carrying the sign of the
Mayer–Vietoris differential in the `V`-component. -/
abbrev mvPhi (X : TopCat) (A U V : Set X) :
    cruxMid X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V :=
  biprod.lift (mvKappaU X A U V) (-(mvKappaV X A U V))

/-- Its inverse. -/
abbrev mvPsi (X : TopCat) (A U V : Set X) :
    relMVUU X A U V ⊞ relMVVV X A U V ⟶ cruxMid X A U V :=
  biprod.desc (mvKappaU' X A U V) (-(mvKappaV' X A U V))

theorem mvPhi_mvPsi (X : TopCat) (A U V : Set X) :
    mvPhi X A U V ≫ mvPsi X A U V = 𝟙 (cruxMid X A U V) := by
  rw [mvPhi, mvPsi, biprod.lift_desc]
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using mvKappa_sum X A U V

theorem mvPsi_mvKappaU (X : TopCat) (A U V : Set X) :
    mvPsi X A U V ≫ mvKappaU X A U V = biprod.fst := by
  rw [biprod.ext_from_iff]
  constructor
  · rw [← Category.assoc, mvPsi, biprod.inl_desc, mvKappaU'_kappaU, biprod.inl_fst]
  · rw [← Category.assoc, mvPsi, biprod.inr_desc, Preadditive.neg_comp, mvKappaV'_kappaU,
      neg_zero, biprod.inr_fst]

theorem mvPsi_mvKappaV (X : TopCat) (A U V : Set X) :
    mvPsi X A U V ≫ mvKappaV X A U V = -(biprod.snd) := by
  rw [biprod.ext_from_iff]
  constructor
  · rw [← Category.assoc, mvPsi, biprod.inl_desc, mvKappaU'_kappaV, Preadditive.comp_neg,
      biprod.inl_snd, neg_zero]
  · rw [← Category.assoc, mvPsi, biprod.inr_desc, Preadditive.neg_comp, mvKappaV'_kappaV,
      Preadditive.comp_neg, biprod.inr_snd]

theorem mvPsi_mvPhi (X : TopCat) (A U V : Set X) :
    mvPsi X A U V ≫ mvPhi X A U V = 𝟙 (relMVUU X A U V ⊞ relMVVV X A U V) := by
  rw [biprod.ext_to_iff]
  constructor
  · rw [Category.assoc, mvPhi, biprod.lift_fst]
    simp only [Category.id_comp, mvPsi_mvKappaU]
  · rw [Category.assoc, mvPhi, biprod.lift_snd]
    simp only [Category.id_comp, Preadditive.comp_neg, mvPsi_mvKappaV, neg_neg]

/-- The two canonical maps of the relative Mayer–Vietoris sequence, transported along the
identification `cruxMid ≅ relMVUU ⊞ relMVVV`, are `biprod.lift γ (-δ)` and
`biprod.desc αU αV`. -/
theorem cruxF_mvPhi (X : TopCat) (A U V : Set X) :
    cruxF X A U V ≫ mvPhi X A U V
      = biprod.lift (HMV.gamma X A U V) (-(HMV.delta X A U V)) := by
  rw [biprod.ext_to_iff]
  constructor
  · rw [Category.assoc, mvPhi]
    simp only [biprod.lift_fst, gamma_eq_cruxF]
  · rw [Category.assoc, mvPhi]
    simp only [biprod.lift_snd, Preadditive.comp_neg, delta_eq_cruxF]

theorem mvPhi_desc (X : TopCat) (A U V : Set X) :
    mvPhi X A U V ≫ biprod.desc (HMV.alphaU X A U V) (HMV.alphaV X A U V)
      = cruxG X A U V := by
  rw [mvPhi, biprod.lift_desc, alphaU_eq_cruxG, alphaV_eq_cruxG]
  rw [show (-(mvKappaV X A U V)) ≫ (-(mvKappaV' X A U V ≫ cruxG X A U V))
        = (mvKappaV X A U V ≫ mvKappaV' X A U V) ≫ cruxG X A U V from by
      rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc]]
  simp only [← Category.assoc]
  rw [← Preadditive.add_comp, mvKappa_sum]
  simp only [Category.id_comp]

/-- Chain level honest relative Mayer-Vietoris: for the small chain complexes
`relMVUV = C^{U,V}(U∩V, U∩V∩A)`, `relMVUU ⊞ relMVVV = C^{U,V}(U,U∩A) ⊞ C^{U,V}(V,V∩A)` and
`relMVTopC = C^{U,V}(X,A)`, the sequence with the canonical maps
`biprod.lift gamma (-delta)` and `biprod.desc alphaU alphaV` is short exact. -/
theorem hmv_chain_shortExact (X : TopCat) (A U V : Set X)
    (hz : CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Limits.biprod.lift (Work.Cohomology.HMV.gamma X A U V) (-(Work.Cohomology.HMV.delta X A U V)))
      (CategoryTheory.Limits.biprod.desc (Work.Cohomology.HMV.alphaU X A U V) (Work.Cohomology.HMV.alphaV X A U V)) = 0) :
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.biprod.lift (Work.Cohomology.HMV.gamma X A U V) (-(Work.Cohomology.HMV.delta X A U V)))
      (CategoryTheory.Limits.biprod.desc (Work.Cohomology.HMV.alphaU X A U V) (Work.Cohomology.HMV.alphaV X A U V))
      hz).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (cruxShort_shortExact X A U V)
  refine ShortComplex.isoMk ?e₁ ?e₂ ?e₃ ?h₁ ?h₂
  · exact Iso.refl _
  · exact Iso.mk (mvPhi X A U V) (mvPsi X A U V) (mvPhi_mvPsi X A U V) (mvPsi_mvPhi X A U V)
  · exact Iso.refl _
  · rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.id_comp]
    exact (cruxF_mvPhi X A U V).symm
  · rw [show (Iso.refl _).hom = 𝟙 _ from rfl, Category.comp_id]
    exact mvPhi_desc X A U V

end

end Work.Cohomology
