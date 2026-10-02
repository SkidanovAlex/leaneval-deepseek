import Mathlib
import Submission.Work.Whitney.RankTwo.CupRep2
import Submission.Work.Whitney.RankTwo.Basic
import Submission.Work.Whitney.RankTwo.Eval
import Submission.Work.Whitney.RankTwo.Cochains
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Thom.Orientation.pairDelta_flip_one
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney.RankTwo
open Work.Thom
open Work.Thom.Orientation
open Work.Cohomology

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## The rank-one total space `Y × ℝ¹`, its sign `0`-cochain and its differential -/

/-- The total space of the trivial real line bundle over `Y`. -/
abbrev Y1 : Type := Y × EuclideanSpace ℝ (Fin 1)

/-- The singular simplicial set of `Y × ℝ¹`. -/
abbrev ssY1 : SSet := TopCat.toSSet.obj (TopCat.of (Y1 Y))

/-- The singular-simplex equivalence for `Y × ℝ¹`. -/
abbrev eY1 (n : ℕ) :
    (ssY1 Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of (Y1 Y)) :=
  TopCat.toSSetObjEquivOld (TopCat.of (Y1 Y)) (Opposite.op (SimplexCategory.mk n))

/-- The singular simplicial set of the base `Y`. -/
abbrev ssB : SSet := TopCat.toSSet.obj (TopCat.of Y)

/-- The singular-simplex equivalence for `Y`. -/
abbrev eB (n : ℕ) : (ssB Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of Y) :=
  TopCat.toSSetObjEquivOld (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))

/-- The sign of the fibre coordinate of a point of `Y × ℝ¹`. -/
def signFib (p : Y1 Y) : ℤ := posOf (p.2.ofLp 0)

/-- The sign cochain of the trivial line bundle. -/
noncomputable def bt0 : Cochain ℤ (ssY1 Y) 0 :=
  cochainOf (ssY1 Y) 0 (fun σ => signFib Y ((eY1 Y 0) σ default))

@[simp] theorem genEval_bt0 (σ : (ssY1 Y) _⦋0⦌) :
    genEval ℤ (ssY1 Y) (bt0 Y) σ = signFib Y ((eY1 Y 0) σ default) :=
  genEval_cochainOf (ssY1 Y) 0 _ σ

/-- The differential of the sign cochain: a representative of the rank-one Thom class. -/
noncomputable def t1 : Cochain ℤ (ssY1 Y) 1 := cochainDiff ℤ (ssY1 Y) (bt0 Y)

/-- The `0`-simplex at a point. -/
noncomputable def ptSimp1 (x : Y1 Y) : (ssY1 Y) _⦋0⦌ :=
  (eY1 Y 0).symm (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)

@[simp] theorem eY1_ptSimp1 (x : Y1 Y) :
    eY1 Y 0 (ptSimp1 Y x) = ContinuousMap.const (stdSimplex ℝ (Fin 1)) x :=
  (eY1 Y 0).apply_symm_apply _

theorem ptSimp1_default (x : Y1 Y) : (eY1 Y 0 (ptSimp1 Y x)) default = x := rfl

@[simp] theorem genEval_bt0_ptSimp1 (x : Y1 Y) :
    genEval ℤ (ssY1 Y) (bt0 Y) (ptSimp1 Y x) = signFib Y x := by
  rw [genEval_bt0, ptSimp1_default]

theorem bt0_ι_ptSimp1 (x : Y1 Y) :
    (bt0 Y) (((ssY1 Y).ιChainComplex (R := zR) (ptSimp1 Y x)).hom 1) = signFib Y x :=
  genEval_bt0_ptSimp1 Y x

theorem eY1_δ_apply {n : ℕ} (x : (ssY1 Y) _⦋n + 1⦌) (i : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (eY1 Y n) ((ssY1 Y).δ i x) z = (eY1 Y (n + 1)) x (stdSimplex.map i.succAbove z) :=
  TopCat.toSSetObjEquivOld_δ_apply x i z

theorem ssY1_δ_zero_eq_ptSimp1 (σ : (ssY1 Y) _⦋1⦌) :
    (ssY1 Y).δ 0 σ = ptSimp1 Y ((eY1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))) := by
  apply (eY1 Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eY1_δ_apply, eY1_ptSimp1, ContinuousMap.const_apply, map_succAbove0_eq_vertex]

theorem ssY1_δ_one_eq_ptSimp1 (σ : (ssY1 Y) _⦋1⦌) :
    (ssY1 Y).δ 1 σ = ptSimp1 Y ((eY1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))) := by
  apply (eY1 Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [eY1_δ_apply, eY1_ptSimp1, ContinuousMap.const_apply, map_succAbove1_eq_vertex]

theorem bt0_chain (σ : (ssY1 Y) _⦋1⦌) :
    (bt0 Y) ((((ssY1 Y).chainComplex zR).d 1 0).hom
        (((ssY1 Y).ιChainComplex (R := zR) σ).hom 1))
      = (bt0 Y) (((ssY1 Y).ιChainComplex (R := zR) ((ssY1 Y).δ 0 σ)).hom 1)
        - (bt0 Y) (((ssY1 Y).ιChainComplex (R := zR) ((ssY1 Y).δ 1 σ)).hom 1) := by
  show (bt0 Y) ((((ssY1 Y).chainComplex zR).d (0+1) 0).hom
        (((ssY1 Y).ιChainComplex (R := zR) σ).hom 1))
      = (bt0 Y) (((ssY1 Y).ιChainComplex (R := zR) ((ssY1 Y).δ 0 σ)).hom 1)
        - (bt0 Y) (((ssY1 Y).ιChainComplex (R := zR) ((ssY1 Y).δ 1 σ)).hom 1)
  have h := congrArg (fun (g : zR ⟶ ((ssY1 Y).chainComplex zR).X 0) => g.hom (1 : zR))
    (SSet.ιChainComplex_d (ssY1 Y) zR σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  rw [Fin.sum_univ_two]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply]
  norm_num
  rw [sub_eq_add_neg]

/-- The value of `t1` on a `1`-simplex is the difference of the signs at the two endpoints. -/
theorem genEval_t1_eq_signs (σ : (ssY1 Y) _⦋1⦌) :
    genEval ℤ (ssY1 Y) (t1 Y) σ
      = signFib Y ((eY1 Y 1) σ (stdSimplex.vertex (1 : Fin 2)))
        - signFib Y ((eY1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))) := by
  rw [t1, cochainDiff_apply]
  change (bt0 Y) ((((ssY1 Y).chainComplex zR).d 1 0).hom
      (((ssY1 Y).ιChainComplex (R := zR) σ).hom 1)) = _
  rw [bt0_chain, ssY1_δ_zero_eq_ptSimp1, ssY1_δ_one_eq_ptSimp1,
    bt0_ι_ptSimp1, bt0_ι_ptSimp1]

/-- `t1` vanishes on every `1`-simplex on which the fibre coordinate never vanishes. -/
theorem genEval_t1_eq_zero (σ : (ssY1 Y) _⦋1⦌)
    (h : ∀ q, ((eY1 Y 1) σ q).2.ofLp 0 ≠ 0) :
    genEval ℤ (ssY1 Y) (t1 Y) σ = 0 := by
  rw [genEval_t1_eq_signs Y σ]
  simp only [signFib]
  have hcont : Continuous fun q : stdSimplex ℝ (Fin 2) => ((eY1 Y 1) σ q).2.ofLp 0 := by fun_prop
  have hc : (0 < ((eY1 Y 1) σ (stdSimplex.vertex (0 : Fin 2))).2.ofLp 0)
      ↔ (0 < ((eY1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))).2.ofLp 0) :=
    posOf_const_of_continuous_ne_zero (f := ⟨_, hcont⟩) (fun q => h q)
  by_cases h1 : 0 < ((eY1 Y 1) σ (stdSimplex.vertex (1 : Fin 2))).2.ofLp 0
  · rw [posOf_pos h1, posOf_pos (hc.mpr h1), sub_self]
  · rw [posOf_nonpos h1, posOf_nonpos (fun h0 => h1 (hc.mp h0)), sub_self]

/-! ## Evaluating the pullback of a cochain along a continuous map -/

/-- `genEval` of the pullback of a cochain along a continuous map: evaluating the pullback of `α`
on a simplex `σ` is evaluating `α` on the image simplex. -/
theorem genEval_dualChainMap {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (α : Cochain ℤ (TopCat.toSSet.obj Y) n) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    genEval ℤ (TopCat.toSSet.obj X) (((dualChainMap ℤ X Y f).f n).hom α) σ
      = genEval ℤ (TopCat.toSSet.obj Y) α ((TopCat.toSSet.map f).app _ σ) := by
  rw [dualChainMap_f_hom, chainMap_f_eq]
  exact genEval_dualMap ℤ _ α σ

/-! ## The fibre coordinate of a point of the sphere/punctured bundle never vanishes -/

theorem sph_coord_ne_zero (p : ↥(Sph Y 1)) : ((p : Y1 Y).2.ofLp 0) ≠ 0 := by
  intro h
  have h0 : (p : Y1 Y).2 = 0 := (ofLp_zero_iff _).mp h
  have hnorm : ‖(p : Y1 Y).2‖ = 1 := p.2
  rw [h0, norm_zero] at hnorm
  norm_num at hnorm

theorem punct_coord_ne_zero (p : ↥(Punct Y 1)) : ((p : Y1 Y).2.ofLp 0) ≠ 0 :=
  fun h => p.2 ((ofLp_zero_iff _).mp h)

/-! ## Membership of `t1` in the relative kernels -/

theorem t1_mem_relKern_sph : t1 Y ∈ relKern ℤ (TopCat.of (Y1 Y)) (Sph Y 1) 1 := by
  rw [relDualKern_iff']
  intro y
  have key : (((t1 Y) : ↥((singularChains ℤ (TopCat.of (Y1 Y))).X 1) →ₗ[ℤ] ℤ).comp
      ((inclChains (TopCat.of (Y1 Y)) (Sph Y 1)).f 1).hom) = 0 := by
    apply genEval_ext
    intro τ
    set σ : (ssY1 Y) _⦋1⦌ := (ConcreteCategory.hom ((TopCat.toSSet.map
      (subtypeIncl (TopCat.of (Y1 Y)) (Sph Y 1))).app (Opposite.op (SimplexCategory.mk 1)))) τ
      with hσ
    have hgen : ((inclChains (TopCat.of (Y1 Y)) (Sph Y 1)).f 1).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(Sph Y 1))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1)
        = ((ssY1 Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
      rw [inclChains, chainMap_f_eq]
      have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
          ((ssY1 Y).chainComplex (ModuleCat.of ℤ ℤ)).X 1) => g.hom 1)
        (SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of ↥(Sph Y 1)))
          (Y := TopCat.toSSet.obj (TopCat.of (Y1 Y)))
          (TopCat.toSSet.map (subtypeIncl (TopCat.of (Y1 Y)) (Sph Y 1)))
          (ModuleCat.of ℤ ℤ) τ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    change (t1 Y) (((inclChains (TopCat.of (Y1 Y)) (Sph Y 1)).f 1).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(Sph Y 1))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0
    rw [hgen]
    change genEval ℤ (ssY1 Y) (t1 Y) σ = 0
    apply genEval_t1_eq_zero
    intro q
    have hc : (eY1 Y 1) σ q = (subtypeIncl (TopCat.of (Y1 Y)) (Sph Y 1))
        ((TopCat.toSSetObjEquivOld (TopCat.of ↥(Sph Y 1)) (Opposite.op (SimplexCategory.mk 1))) τ q) :=
      toSSetObjEquiv_map_apply' (TopCat.of ↥(Sph Y 1)) (TopCat.of (Y1 Y))
        (subtypeIncl (TopCat.of (Y1 Y)) (Sph Y 1)) (Opposite.op (SimplexCategory.mk 1)) τ q
    rw [hc]
    exact sph_coord_ne_zero Y _
  exact LinearMap.congr_fun key y

theorem t1_mem_relKern_punct : t1 Y ∈ relKern ℤ (TopCat.of (Y1 Y)) (Punct Y 1) 1 := by
  rw [relDualKern_iff']
  intro y
  have key : (((t1 Y) : ↥((singularChains ℤ (TopCat.of (Y1 Y))).X 1) →ₗ[ℤ] ℤ).comp
      ((inclChains (TopCat.of (Y1 Y)) (Punct Y 1)).f 1).hom) = 0 := by
    apply genEval_ext
    intro τ
    set σ : (ssY1 Y) _⦋1⦌ := (ConcreteCategory.hom ((TopCat.toSSet.map
      (subtypeIncl (TopCat.of (Y1 Y)) (Punct Y 1))).app (Opposite.op (SimplexCategory.mk 1)))) τ
      with hσ
    have hgen : ((inclChains (TopCat.of (Y1 Y)) (Punct Y 1)).f 1).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(Punct Y 1))).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1)
        = ((ssY1 Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1 := by
      rw [inclChains, chainMap_f_eq]
      have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
          ((ssY1 Y).chainComplex (ModuleCat.of ℤ ℤ)).X 1) => g.hom 1)
        (SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of ↥(Punct Y 1)))
          (Y := TopCat.toSSet.obj (TopCat.of (Y1 Y)))
          (TopCat.toSSet.map (subtypeIncl (TopCat.of (Y1 Y)) (Punct Y 1)))
          (ModuleCat.of ℤ ℤ) τ)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    change (t1 Y) (((inclChains (TopCat.of (Y1 Y)) (Punct Y 1)).f 1).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(Punct Y 1))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0
    rw [hgen]
    change genEval ℤ (ssY1 Y) (t1 Y) σ = 0
    apply genEval_t1_eq_zero
    intro q
    have hc : (eY1 Y 1) σ q = (subtypeIncl (TopCat.of (Y1 Y)) (Punct Y 1))
        ((TopCat.toSSetObjEquivOld (TopCat.of ↥(Punct Y 1)) (Opposite.op (SimplexCategory.mk 1))) τ q) :=
      toSSetObjEquiv_map_apply' (TopCat.of ↥(Punct Y 1)) (TopCat.of (Y1 Y))
        (subtypeIncl (TopCat.of (Y1 Y)) (Punct Y 1)) (Opposite.op (SimplexCategory.mk 1)) τ q
    rw [hc]
    exact punct_coord_ne_zero Y _
  exact LinearMap.congr_fun key y


/-- The differential commutes with the pullback of cochains along a continuous map. -/
theorem cochainDiff_dualChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Y)) n) :
    ((dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f (n + 1))
        (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of Y)) α)
      = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X))
          (((dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f n) α) := by
  have hc := congrArg ModuleCat.Hom.hom
    ((dualChainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).comm n (n + 1))
  simp only [ModuleCat.hom_comp] at hc
  have h2 := LinearMap.congr_fun hc α
  simp only [LinearMap.comp_apply] at h2
  rw [singularCochain_d_apply, singularCochain_d_apply] at h2
  exact h2.symm


/-! ## The cocycle condition for `t1` -/

theorem restr_apply_t1 (A : Set (Y1 Y)) (hmem : t1 Y ∈ relKern ℤ (TopCat.of (Y1 Y)) A 1) :
    ((restr ℤ (TopCat.of (Y1 Y)) A).f 1) (t1 Y) = 0 := hmem

/-- The differential commutes with the restriction to a subspace. -/
theorem cochainDiff_restr {X : TopCat} (A : Set X) {n : ℕ}
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) :
    cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f n) α)
      = ((restr ℤ X A).f (n + 1)) (cochainDiff ℤ (TopCat.toSSet.obj X) α) := by
  have hc := congrArg ModuleCat.Hom.hom ((restr ℤ X A).comm n (n + 1))
  simp only [ModuleCat.hom_comp] at hc
  have h2 := LinearMap.congr_fun hc α
  simp only [LinearMap.comp_apply] at h2
  rw [singularCochain_d_apply, singularCochain_d_apply] at h2
  exact h2

theorem cochainDiff_zero (X : SSet) (n : ℕ) :
    cochainDiff ℤ X (0 : Cochain ℤ X n) = 0 := by
  change cochainDiffLM ℤ X n 0 = 0
  exact map_zero _

theorem relDiffLM_relKern_eq_zero (X : TopCat) {A : Set X} (n : ℕ) (a : relKern ℤ X A (n+1))
    (h : ((singularCochainComplex ℤ X).d (n+1) (n+2)).hom (a.1) = 0) :
    relDiffLM ℤ X A (n+1) a = 0 := by
  apply Subtype.ext
  rw [relDiffLM_coe, Submodule.coe_zero]
  exact h

theorem relDiffLM_t1_sph (hmem : t1 Y ∈ relKern ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) 1) :
    relDiffLM ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) 1 ⟨t1 Y, hmem⟩ = 0 := by
  refine relDiffLM_relKern_eq_zero (TopCat.of (Y1 Y)) 0 ⟨t1 Y, hmem⟩ ?_
  have h := HomologicalComplex.d_comp_d (singularCochainComplex ℤ (TopCat.of (Y1 Y))) 0 1 2
  have h2 := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 := LinearMap.congr_fun h2 ((bt0 Y) : ((singularCochainComplex ℤ (TopCat.of (Y1 Y))).X 0))
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, t1, singularCochain_d_apply] using h3

theorem relDiffLM_t1_punct (hmem : t1 Y ∈ relKern ℤ (TopCat.of (Y1 Y)) (Punct Y 1) 1) :
    relDiffLM ℤ (TopCat.of (Y1 Y)) (Punct Y 1) 1 ⟨t1 Y, hmem⟩ = 0 := by
  refine relDiffLM_relKern_eq_zero (TopCat.of (Y1 Y)) 0 ⟨t1 Y, hmem⟩ ?_
  have h := HomologicalComplex.d_comp_d (singularCochainComplex ℤ (TopCat.of (Y1 Y))) 0 1 2
  have h2 := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 := LinearMap.congr_fun h2 ((bt0 Y) : ((singularCochainComplex ℤ (TopCat.of (Y1 Y))).X 0))
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, t1, singularCochain_d_apply] using h3

/-- The representative `t1` as an element of the relative kernel of the sphere pair. -/
abbrev t1sphr : relKern ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) 1 :=
  ⟨t1 Y, t1_mem_relKern_sph Y⟩

/-- The representative `t1` as an element of the relative kernel of the punctured pair. -/
abbrev t1punt : relKern ℤ (TopCat.of (Y1 Y)) (Punct Y 1) 1 :=
  ⟨t1 Y, t1_mem_relKern_punct Y⟩

theorem relDiffLM_t1punt : relDiffLM ℤ (TopCat.of (Y1 Y)) (Punct Y 1) 1 (t1punt Y) = 0 :=
  relDiffLM_t1_punct Y (t1_mem_relKern_punct Y)

theorem relDiffLM_t1sphr : relDiffLM ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) 1 (t1sphr Y) = 0 :=
  relDiffLM_t1_sph Y (t1_mem_relKern_sph Y)

/-! ## The sign cochain on the sphere bundle -/

abbrev ssSph : SSet := TopCat.toSSet.obj (TopCat.of ↥(Work.Thom.Sph Y 1))

abbrev eSph (n : ℕ) :
    (ssSph Y) _⦋n⦌ ≃ C(stdSimplex ℝ (Fin (n + 1)), TopCat.of ↥(Work.Thom.Sph Y 1)) :=
  TopCat.toSSetObjEquivOld (TopCat.of ↥(Work.Thom.Sph Y 1)) (Opposite.op (SimplexCategory.mk n))

/-- The restriction of the sign cochain to the rank-one sphere bundle. -/
abbrev bt0Sph : Cochain ℤ (ssSph Y) 0 :=
  ((restr ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1)).f 0) (bt0 Y)

theorem bt0Sph_coc : cochainDiff ℤ (ssSph Y) (bt0Sph Y) = 0 := by
  have h := cochainDiff_restr (X := TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) (n := 0) (bt0 Y)
  rw [h]
  rw [show cochainDiff ℤ (ssY1 Y) (bt0 Y) = t1 Y from rfl]
  exact restr_apply_t1 Y (Work.Thom.Sph Y 1) (t1_mem_relKern_sph Y)

theorem genEval_bt0Sph (τ : (ssSph Y) _⦋0⦌) :
    genEval ℤ (ssSph Y) (bt0Sph Y) τ = signFib Y ((eSph Y 0) τ default) := by
  change genEval ℤ (TopCat.toSSet.obj (TopCat.of ↥(Work.Thom.Sph Y 1)))
    (((dualChainMap ℤ (TopCat.of ↥(Work.Thom.Sph Y 1)) (TopCat.of (Y1 Y))
      (subtypeIncl (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1))).f 0).hom (bt0 Y)) τ
    = signFib Y ((eSph Y 0) τ default)
  rw [genEval_dualChainMap, genEval_bt0]
  congr 1

theorem signFib_sphPlus (y : Y) : signFib Y (y, sphPlus) = 1 := by
  change posOf ((sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 1
  rw [show (sphPlus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (1 : ℝ) from rfl, posOf_pos one_pos]

theorem signFib_sphMinus (y : Y) : signFib Y (y, sphMinus) = 0 := by
  change posOf ((sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0) = 0
  rw [show (sphMinus : EuclideanSpace ℝ (Fin 1)).ofLp 0 = (-1 : ℝ) from rfl,
    posOf_nonpos (by norm_num)]

theorem coe_sigPos_hom (y : Y) :
    (↑((ConcreteCategory.hom (TopCat.ofHom (sigPos (Y := Y)))) y) : Y1 Y) = (y, sphPlus) := rfl

theorem coe_sigNeg_hom (y : Y) :
    (↑((ConcreteCategory.hom (TopCat.ofHom (sigNeg (Y := Y)))) y) : Y1 Y) = (y, sphMinus) := rfl

/-! ## Pullbacks of the sign cochain along the two ends -/

theorem bt0Sph_pullback_sigPos :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (sigPos (Y := Y))))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (bt0Sph Y) = unitCochain ℤ (ssB Y) := by
  apply genEval_ext
  intro σ
  rw [genEval_dualMap, genEval_bt0Sph, genEval_unitCochain]
  rw [toSSetObjEquiv_map_apply', coe_sigPos_hom, signFib_sphPlus]

theorem bt0Sph_pullback_sigNeg :
    ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (sigNeg (Y := Y))))
        (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap (bt0Sph Y) = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_dualMap, genEval_bt0Sph]
  rw [toSSetObjEquiv_map_apply', coe_sigNeg_hom, signFib_sphMinus]
  rfl

/-! ## The class of the sign cochain is `w` -/

theorem cohomologyClassOf_zero (X : SSet) {n : ℕ}
    (h : cochainDiff ℤ X (0 : Cochain ℤ X n) = 0) :
    cohomologyClassOf ℤ X (0 : Cochain ℤ X n) h = 0 := by
  rw [cohomologyClassOf]
  have hz : cocycleOf ℤ X (0 : Cochain ℤ X n) h = 0 := by
    apply iCycles_injective ℤ X n
    rw [iCycles_cocycleOf, map_zero]
  rw [hz, map_zero]

/-- The class of the sign cochain of the sphere bundle, as a class of the pair. -/
noncomputable def bt0SphClass (hb : cochainDiff ℤ (ssSph Y) (bt0Sph Y) = 0) :
    Coh ℤ 0 ↥(Work.Thom.Sph Y 1) :=
  cohomologyClassOf ℤ (ssSph Y) (bt0Sph Y) hb

theorem CohMap_sigPos_bt0Sph (hb : cochainDiff ℤ (ssSph Y) (bt0Sph Y) = 0) :
    (CohMap (sigPos (Y := Y)) ℤ 0).hom (bt0SphClass Y hb)
      = oneH ℤ (ssB Y) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Work.Thom.Sph Y 1))
        (TopCat.ofHom (sigPos (Y := Y)))) 0))
      (cohomologyClassOf ℤ (ssSph Y) (bt0Sph Y) hb)
    = cohomologyClassOf ℤ (ssB Y) (unitCochain ℤ (ssB Y)) (cochainDiff_unitCochain ℤ (ssB Y))
  rw [singularCohomologyMap_classOf ℤ (X := TopCat.of Y) (Y := TopCat.of ↥(Work.Thom.Sph Y 1))
    (TopCat.ofHom (sigPos (Y := Y))) (bt0Sph Y) hb]
  exact cohomologyClassOf_congr ℤ (ssB Y) (bt0Sph_pullback_sigPos Y) _ _

theorem CohMap_sigNeg_bt0Sph (hb : cochainDiff ℤ (ssSph Y) (bt0Sph Y) = 0) :
    (CohMap (sigNeg (Y := Y)) ℤ 0).hom (bt0SphClass Y hb) = 0 := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Work.Thom.Sph Y 1))
        (TopCat.ofHom (sigNeg (Y := Y)))) 0))
      (cohomologyClassOf ℤ (ssSph Y) (bt0Sph Y) hb) = (0 : ↑(Coh ℤ 0 Y))
  rw [singularCohomologyMap_classOf ℤ (X := TopCat.of Y) (Y := TopCat.of ↥(Work.Thom.Sph Y 1))
    (TopCat.ofHom (sigNeg (Y := Y))) (bt0Sph Y) hb]
  refine (cohomologyClassOf_congr ℤ (ssB Y) (bt0Sph_pullback_sigNeg Y) _
    (cochainDiff_zero (ssB Y) 0)).trans ?_
  exact cohomologyClassOf_zero (ssB Y) (cochainDiff_zero (ssB Y) 0)

theorem bt0Sph_class_eq_w (w : Coh ℤ 0 ↥(Work.Thom.Sph Y 1))
    (hwP : (CohMap (sigPos (Y := Y)) ℤ 0).hom w = oneH ℤ (ssB Y))
    (hwN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom w = 0)
    (hb : cochainDiff ℤ (ssSph Y) (bt0Sph Y) = 0) :
    bt0SphClass Y hb = w := by
  have hP := CohMap_sigPos_bt0Sph Y hb
  have hN := CohMap_sigNeg_bt0Sph Y hb
  have hzero : bt0SphClass Y hb - w = 0 := by
    apply eq_zero_of_sigPos_sigNeg_eq_zero (Y := Y)
    · rw [map_sub, hP, hwP, sub_self]
    · rw [map_sub, hN, hwN, sub_self]
  exact sub_eq_zero.mp hzero

/-! ## The class of `t1` on the sphere bundle is the rank-one model class -/

theorem bt0_d_eq_t1 :
    ((singularCochainComplex ℤ (TopCat.of (Y1 Y))).d 0 1).hom (bt0 Y)
      = (t1 Y : ↑((singularCochainComplex ℤ (TopCat.of (Y1 Y))).X 1)) :=
  singularCochain_d_apply ℤ (TopCat.of (Y1 Y)) (bt0 Y)

theorem t1_class_sph : relClassOf ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1)
    ⟨t1 Y, t1_mem_relKern_sph Y⟩ (relDiffLM_t1_sph Y (t1_mem_relKern_sph Y))
      = Mn 1 Y := by
  obtain ⟨w, hwP, hwN, hwδ⟩ := Work.Whitney.Mn_one_eq_pairDelta Y
  have hb := bt0Sph_coc Y
  have hcls : bt0SphClass Y hb = w :=
    bt0Sph_class_eq_w Y w hwP hwN hb
  obtain ⟨hmem', hcoc', hδ⟩ :=
    Work.Sph3Disc.pdmc_pairδ_lift (X := TopCat.of (Y1 Y)) (A := Work.Thom.Sph Y 1) 0
      (bt0Sph Y) hb (bt0 Y) (by rfl)
  have e1 : Mn 1 Y = (ModuleCat.Hom.hom (pairδC (Work.Thom.Sph Y 1) 0)) w := hwδ.symm
  have e2 : (ModuleCat.Hom.hom (pairδC (Work.Thom.Sph Y 1) 0)) w
      = (ModuleCat.Hom.hom (pairδC (Work.Thom.Sph Y 1) 0)) (bt0SphClass Y hb) :=
    congrArg (fun z => (ModuleCat.Hom.hom (pairδC (Work.Thom.Sph Y 1) 0)) z) hcls.symm
  have e3 : (ModuleCat.Hom.hom (pairδC (Work.Thom.Sph Y 1) 0)) (bt0SphClass Y hb)
      = relClassOf ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1)
          ⟨t1 Y, t1_mem_relKern_sph Y⟩ (relDiffLM_t1_sph Y (t1_mem_relKern_sph Y)) :=
    hδ.trans (relClassOf_congr ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) hcoc'
      (relDiffLM_t1_sph Y (t1_mem_relKern_sph Y))
      (Subtype.ext (bt0_d_eq_t1 Y)))
  exact ((e1.trans e2).trans e3).symm

/-! ## The class of `t1` on the punctured bundle is the punctured model class -/

theorem relMapLM_id_val (A₁ A₂ : Set (Y1 Y)) (h : ∀ x ∈ A₁, x ∈ A₂)
    (a : relKern ℤ (TopCat.of (Y1 Y)) A₂ 1) :
    (relMapLM ℤ A₁ A₂ (TopCat.ofHom (ContinuousMap.id (Y1 Y))) h 1 a).1 = a.1 := by
  rw [relMapLM_coe]
  show ((dualChainMap ℤ (TopCat.of (Y1 Y)) (TopCat.of (Y1 Y))
      (TopCat.ofHom (ContinuousMap.id (Y1 Y)))).f 1) (a.1) = a.1
  rw [show (TopCat.ofHom (ContinuousMap.id (Y1 Y))) = 𝟙 (TopCat.of (Y1 Y)) from rfl,
    dualChainMap_id]
  rfl

theorem relCohMap_id_t1 :
    (ModuleCat.Hom.hom (relCohMap (ContinuousMap.id (Y1 Y)) (Work.Thom.Sph Y 1)
        (Punct Y 1) (mem_Sph_punct Y 1) ℤ 1))
      (relClassOf ℤ (TopCat.of (Y1 Y)) (Punct Y 1) (t1punt Y)
        (relDiffLM_t1punt Y))
      = relClassOf ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1)
          (t1sphr Y) (relDiffLM_t1sphr Y) := by
  have h := homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of (Y1 Y)) (X₂ := TopCat.of (Y1 Y))
      (A₁ := Work.Thom.Sph Y 1) (A₂ := Punct Y 1)
      (f := TopCat.ofHom (ContinuousMap.id (Y1 Y))) (h := mem_Sph_punct Y 1)
      (n := 1) (a := t1punt Y) (ha := relDiffLM_t1punt Y)
  refine h.trans ?_
  exact relClassOf_congr ℤ (TopCat.of (Y1 Y)) (Work.Thom.Sph Y 1) _
      (relDiffLM_t1sphr Y)
      (Subtype.ext (relMapLM_id_val Y (Work.Thom.Sph Y 1) (Punct Y 1) (mem_Sph_punct Y 1)
        (t1punt Y)))

theorem t1_class_punct : relClassOf ℤ (TopCat.of (Y1 Y)) (Punct Y 1)
    (t1punt Y) (relDiffLM_t1punt Y)
      = Mpun 1 Y := by
  apply (bijective_jMap Y 1 1).1
  rw [relCohMap_id_t1, Mpun_spec]
  exact t1_class_sph Y

/-! ## The pullback of the model class along `pr₁` is the class of `alpha` -/

theorem dualMap_tcmPr1_bt0 :
    ((dualChainMap ℤ (TopCat.of (X Y)) (TopCat.of (Y1 Y))
      (TopCat.ofHom (tcmPr1 Y 1 1))).f 0) (bt0 Y) = alpha0 Y := by
  apply genEval_ext
  intro σ
  rw [genEval_dualChainMap, genEval_bt0, genEval_alpha0]
  have hpt : (eY1 Y 0) ((TopCat.toSSet.map (TopCat.ofHom (tcmPr1 Y 1 1))).app _ σ) default
      = tcmPr1 Y 1 1 ((sEquiv Y 0) σ default) :=
    toSSetObjEquiv_map_apply' (TopCat.of (X Y)) (TopCat.of (Y1 Y))
      (TopCat.ofHom (tcmPr1 Y 1 1)) (Opposite.op (SimplexCategory.mk 0)) σ default
  rw [hpt]
  show posOf (((tcmPr1 Y 1 1 ((sEquiv Y 0) σ default)).2).ofLp 0)
      = posOf (coordA Y ((sEquiv Y 0) σ default))
  rw [coordA_eq]
  rfl

theorem relMapLM_tcmPr1_t1 :
    relMapLM ℤ (tcmA Y 1 1) (Punct Y 1) (TopCat.ofHom (tcmPr1 Y 1 1))
        (fun x hx => hx) 1 ⟨t1 Y, t1_mem_relKern_punct Y⟩
      = ⟨alpha Y, alpha_mem_relKern Y⟩ := by
  apply Subtype.ext
  rw [relMapLM_coe]
  show ((dualChainMap ℤ (TopCat.of (X Y)) (TopCat.of (Y1 Y))
      (TopCat.ofHom (tcmPr1 Y 1 1))).f 1) (t1 Y) = alpha Y
  rw [show t1 Y = cochainDiff ℤ (ssY1 Y) (bt0 Y) from rfl]
  rw [cochainDiff_dualChainMap]
  rw [dualMap_tcmPr1_bt0]
  rfl

end
end Work.Whitney.RankTwo
