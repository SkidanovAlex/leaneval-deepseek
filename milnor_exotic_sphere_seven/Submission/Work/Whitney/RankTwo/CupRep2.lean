import Mathlib
import Submission.Work.Whitney.RankTwo.CupRep
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.Singular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney.RankTwo
open Work.Thom
open Work.Cohomology

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- The pushforward of singular simplices, in coordinates (proved by `rfl`). -/
theorem toSSetObjEquiv_map_apply' (P P' : TopCat) (g : P ⟶ P') (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj P).obj n) (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    ((TopCat.toSSetObjEquivOld P' n) ((ConcreteCategory.hom ((TopCat.toSSet.map g).app n)) x)) t
      = g (((TopCat.toSSetObjEquivOld P n) x) t) := rfl

theorem continuous_coordA : Continuous (coordA Y) := by
  have h : coordA Y = fun x : X Y => (WithLp.ofLp (tcmSumLin 1 1 x.2)) 0 := rfl
  rw [h]
  fun_prop

theorem continuous_coordB : Continuous (coordB Y) := by
  have h : coordB Y = fun x : X Y => (WithLp.ofLp (tcmSumLin 1 1 x.2)) 1 := rfl
  rw [h]
  fun_prop

/-- `alpha = d alpha0` is a cocycle of the `A`-relative complex. -/
theorem alpha_mem_relKern :
    alpha Y ∈ relKern ℤ (TopCat.of (X Y)) (tcmA Y 1 1) 1 := by
  rw [relDualKern_iff']
  intro y
  have key : (((alpha Y) : ↥((singularChains ℤ (TopCat.of (X Y))).X 1) →ₗ[ℤ] ℤ).comp
      ((inclChains (TopCat.of (X Y)) (tcmA Y 1 1)).f 1).hom) = 0 := by
    apply genEval_ext
    intro τ
    set σ : (ssX Y) _⦋1⦌ := (ConcreteCategory.hom ((TopCat.toSSet.map
      (subtypeIncl (TopCat.of (X Y)) (tcmA Y 1 1))).app (Opposite.op (SimplexCategory.mk 1)))) τ
      with hσ
    have hgen : ((inclChains (TopCat.of (X Y)) (tcmA Y 1 1)).f 1).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(tcmA Y 1 1))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1)
        = ((ssX Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
      rw [inclChains, chainMap_f_eq]
      have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
          ((ssX Y).chainComplex (ModuleCat.of ℤ ℤ)).X 1) => g.hom 1)
        (SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of ↥(tcmA Y 1 1)))
          (Y := TopCat.toSSet.obj (TopCat.of (X Y)))
          (TopCat.toSSet.map (subtypeIncl (TopCat.of (X Y)) (tcmA Y 1 1)))
          (ModuleCat.of ℤ ℤ) τ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    change (alpha Y) (((inclChains (TopCat.of (X Y)) (tcmA Y 1 1)).f 1).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(tcmA Y 1 1))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0
    rw [hgen]
    change genEval ℤ (ssX Y) (alpha Y) σ = 0
    rw [genEval_alpha_eq_signs]
    have hc : ∀ q, ((sEquiv Y 1) σ) q
        = (subtypeIncl (TopCat.of (X Y)) (tcmA Y 1 1))
            ((TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmA Y 1 1)) (Opposite.op (SimplexCategory.mk 1))) τ q) := by
      intro q
      exact toSSetObjEquiv_map_apply' (TopCat.of ↥(tcmA Y 1 1)) (TopCat.of (X Y))
        (subtypeIncl (TopCat.of (X Y)) (tcmA Y 1 1)) (Opposite.op (SimplexCategory.mk 1)) τ q
    have hmem : ∀ q, ((sEquiv Y 1) σ) q ∈ tcmA Y 1 1 := by
      intro q
      rw [hc q]
      exact ((TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmA Y 1 1)) (Opposite.op (SimplexCategory.mk 1))) τ q).2
    have hcont : Continuous fun q : stdSimplex ℝ (Fin 2) => coordA Y (((sEquiv Y 1) σ) q) :=
      (continuous_coordA Y).comp ((sEquiv Y 1) σ).continuous
    have hne : ∀ q, coordA Y (((sEquiv Y 1) σ) q) ≠ 0 :=
      fun q => (coordA_ne_zero_iff Y _).mpr (hmem q)
    have hconst := posOf_const_of_continuous_ne_zero (f := ⟨_, hcont⟩) hne
    by_cases h : 0 < coordA Y (((sEquiv Y 1) σ) (stdSimplex.vertex (1 : Fin 2)))
    · have h0 : 0 < coordA Y (((sEquiv Y 1) σ) (stdSimplex.vertex (0 : Fin 2))) := hconst.mpr h
      rw [posOf_pos h, posOf_pos h0, sub_self]
    · have h0 : ¬ 0 < coordA Y (((sEquiv Y 1) σ) (stdSimplex.vertex (0 : Fin 2))) :=
        fun h0 => h (hconst.mp h0)
      rw [posOf_nonpos h, posOf_nonpos h0, sub_self]
  exact LinearMap.congr_fun key y

/-- `beta = d beta0` is a cocycle of the `C`-relative complex. -/
theorem beta_mem_relKern :
    beta Y ∈ relKern ℤ (TopCat.of (X Y)) (tcmC Y 1 1) 1 := by
  rw [relDualKern_iff']
  intro y
  have key : (((beta Y) : ↥((singularChains ℤ (TopCat.of (X Y))).X 1) →ₗ[ℤ] ℤ).comp
      ((inclChains (TopCat.of (X Y)) (tcmC Y 1 1)).f 1).hom) = 0 := by
    apply genEval_ext
    intro τ
    set σ : (ssX Y) _⦋1⦌ := (ConcreteCategory.hom ((TopCat.toSSet.map
      (subtypeIncl (TopCat.of (X Y)) (tcmC Y 1 1))).app (Opposite.op (SimplexCategory.mk 1)))) τ
      with hσ
    have hgen : ((inclChains (TopCat.of (X Y)) (tcmC Y 1 1)).f 1).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(tcmC Y 1 1))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1)
        = ((ssX Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
      rw [inclChains, chainMap_f_eq]
      have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
          ((ssX Y).chainComplex (ModuleCat.of ℤ ℤ)).X 1) => g.hom 1)
        (SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of ↥(tcmC Y 1 1)))
          (Y := TopCat.toSSet.obj (TopCat.of (X Y)))
          (TopCat.toSSet.map (subtypeIncl (TopCat.of (X Y)) (tcmC Y 1 1)))
          (ModuleCat.of ℤ ℤ) τ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    change (beta Y) (((inclChains (TopCat.of (X Y)) (tcmC Y 1 1)).f 1).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(tcmC Y 1 1))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0
    rw [hgen]
    change genEval ℤ (ssX Y) (beta Y) σ = 0
    rw [genEval_beta_eq_signs]
    have hc : ∀ q, ((sEquiv Y 1) σ) q
        = (subtypeIncl (TopCat.of (X Y)) (tcmC Y 1 1))
            ((TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmC Y 1 1)) (Opposite.op (SimplexCategory.mk 1))) τ q) := by
      intro q
      exact toSSetObjEquiv_map_apply' (TopCat.of ↥(tcmC Y 1 1)) (TopCat.of (X Y))
        (subtypeIncl (TopCat.of (X Y)) (tcmC Y 1 1)) (Opposite.op (SimplexCategory.mk 1)) τ q
    have hmem : ∀ q, ((sEquiv Y 1) σ) q ∈ tcmC Y 1 1 := by
      intro q
      rw [hc q]
      exact ((TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmC Y 1 1)) (Opposite.op (SimplexCategory.mk 1))) τ q).2
    have hcont : Continuous fun q : stdSimplex ℝ (Fin 2) => coordB Y (((sEquiv Y 1) σ) q) :=
      (continuous_coordB Y).comp ((sEquiv Y 1) σ).continuous
    have hne : ∀ q, coordB Y (((sEquiv Y 1) σ) q) ≠ 0 :=
      fun q => (coordB_ne_zero_iff Y _).mpr (hmem q)
    have hconst := posOf_const_of_continuous_ne_zero (f := ⟨_, hcont⟩) hne
    by_cases h : 0 < coordB Y (((sEquiv Y 1) σ) (stdSimplex.vertex (1 : Fin 2)))
    · have h0 : 0 < coordB Y (((sEquiv Y 1) σ) (stdSimplex.vertex (0 : Fin 2))) := hconst.mpr h
      rw [posOf_pos h, posOf_pos h0, sub_self]
    · have h0 : ¬ 0 < coordB Y (((sEquiv Y 1) σ) (stdSimplex.vertex (0 : Fin 2))) :=
        fun h0 => h (hconst.mp h0)
      rw [posOf_nonpos h, posOf_nonpos h0, sub_self]
  exact LinearMap.congr_fun key y

end
end Work.Whitney.RankTwo
