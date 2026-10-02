import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.MvAux.BiprodElem
import Submission.Work.LerayHirsch.MvAux.IsoSquare
import Submission.Work.LerayHirsch.MvAux.HonestDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The two-cover Mayer–Vietoris ladder of `Work.LerayHirsch.Mv_exact`: elementwise lemmas

The ladder of `Submission/Work/LerayHirsch/LhTwoCoverDefs.lean` is written in terms of the
`P`-term `MvP = MvW U ⊞ MvW V` (a biproduct of two products) and the `M`-, `Q`-terms (products of
copies of `H^*(B)` resp. `H^*(U∩V)`).  In this module every map of the ladder is described
elementwise, and the exactness of the ladder is thereby reduced to the honest Mayer–Vietoris
exactness of the single-degree sequences, component by component.
-/

namespace Work.LerayHirsch.MvAux

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

variable {B : Type} [TopologicalSpace B] {m : ℕ} {U V : Set B}

/-- The `P`-term as the explicit product of the two families of cohomology modules. -/
noncomputable def MvPIso (m k : ℕ) (U V : Set B) :=
  ModuleCat.biprodIsoProd (MvW B m k U) (MvW B m k V)

@[simp] theorem MvPIso_def (m k : ℕ) (U V : Set B) :
    MvPIso m k U V = ModuleCat.biprodIsoProd (MvW B m k U) (MvW B m k V) := rfl

/-- The inclusion of the index set of degree `k` into that of degree `k+1`. -/
def lhIdxSucc {m k : ℕ} (i : lhIdx m k) : lhIdx m (k + 1) :=
  ⟨i.1, Nat.le_trans i.2 (Nat.le_succ k)⟩

@[simp] theorem lhIdxSucc_val {m k : ℕ} (i : lhIdx m k) : (lhIdxSucc i : ℕ) = (i : ℕ) := rfl

/-- The element of the explicit product `MvW U × MvW V` with the given components. -/
def mkMvPair (m k : ℕ) (U V : Set B) (u : ↑(MvW B m k U)) (v : ↑(MvW B m k V)) :
    ↑(MvW B m k U) × ↑(MvW B m k V) :=
  (u, v)

@[simp] theorem mkMvPair_fst (m k : ℕ) (U V : Set B) (u : ↑(MvW B m k U)) (v : ↑(MvW B m k V)) :
    (mkMvPair (B := B) (m := m) (k := k) (U := U) (V := V) u v).1 = u := rfl

@[simp] theorem mkMvPair_snd (m k : ℕ) (U V : Set B) (u : ↑(MvW B m k U)) (v : ↑(MvW B m k V)) :
    (mkMvPair (B := B) (m := m) (k := k) (U := U) (V := V) u v).2 = v := rfl

/-- The projection onto the `J`-th component of the `M`-term, as a linear map. -/
theorem MvM_proj_apply (k : ℕ) (J : lhIdx m k) (x : ↑(MvM B m k)) :
    (LinearMap.proj (R := ℤ)
      (φ := fun i : lhIdx m k => ↑(pdCoh (TopCat.of B) (∅ : Set B) (k - 2 * (i : ℕ)))) J) x
      = x J :=
  LinearMap.proj_apply J x

/-! ## Transport along a degree cast -/

/-- Two casts with the same degrees agree (on elements), whatever their proofs. -/
theorem pdCast_apply_congr (X : TopCat) (A : Set X) {k l : ℕ} (p q : k = l)
    (z : ↑(pdCoh X A k)) :
    ModuleCat.Hom.hom (pdCast X A p) z = ModuleCat.Hom.hom (pdCast X A q) z :=
  congrArg (fun r => ModuleCat.Hom.hom (pdCast X A r) z) (Subsingleton.elim p q)

/-- A cast followed by the corresponding cast back is the identity (on elements). -/
theorem pdCast_symm_apply (X : TopCat) (A : Set X) {k l : ℕ} (h : k = l)
    (x : ↑(pdCoh X A l)) :
    ModuleCat.Hom.hom (pdCast X A h) (ModuleCat.Hom.hom (pdCast X A h.symm) x) = x := by
  have h1 : ModuleCat.Hom.hom (pdCast X A h.symm.symm)
      (ModuleCat.Hom.hom (pdCast X A h.symm) x) = x :=
    pdCast_pdCast_symm_apply X A h.symm x
  rwa [pdCast_apply_congr X A h.symm.symm h] at h1

/-- An arbitrary cast followed by an arbitrary cast back is the identity (on elements). -/
theorem pdCast_comp_pdCast_apply (X : TopCat) (A : Set X) {k l : ℕ} (p : k = l) (q : l = k)
    (x : ↑(pdCoh X A l)) :
    ModuleCat.Hom.hom (pdCast X A p) (ModuleCat.Hom.hom (pdCast X A q) x) = x := by
  have hq : ModuleCat.Hom.hom (pdCast X A q) x = ModuleCat.Hom.hom (pdCast X A p.symm) x :=
    pdCast_apply_congr X A q p.symm x
  rw [hq]
  exact pdCast_symm_apply X A p x

/-- A cast is injective. -/
theorem pdCast_eq_zero_iff (X : TopCat) (A : Set X) {k l : ℕ} (h : k = l)
    (y : ↑(pdCoh X A k)) :
    ModuleCat.Hom.hom (pdCast X A h) y = 0 ↔ y = 0 := by
  constructor
  · intro hy
    have h' := congrArg (fun z => ModuleCat.Hom.hom (pdCast X A h.symm) z) hy
    rw [pdCast_pdCast_symm_apply X A h y, map_zero] at h'
    exact h'
  · intro hy
    rw [hy, map_zero]

/-- Restriction commutes with the degree cast (on elements). -/
theorem pdCohRes_pdCast_apply (X : TopCat) (A U : Set X) {k l : ℕ} (h : k = l)
    (z : ↑(pdCoh X A k)) :
    ModuleCat.Hom.hom (pdSubCast X A U h) (ModuleCat.Hom.hom (pdCohRes X A U k) z)
      = ModuleCat.Hom.hom (pdCohRes X A U l) (ModuleCat.Hom.hom (pdCast X A h) z) := by
  have h' := congrArg (fun (φ : pdCoh X A k ⟶ pdCohSub X A U l) => ModuleCat.Hom.hom φ z)
    (pdCohRes_pdCast X A U h)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

/-- The range of the connecting map of the honest sequence. -/
theorem range_honestDelta (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (d : ℕ) :
    (ModuleCat.Hom.hom (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d)).range
      = (ModuleCat.Hom.hom
          (honestF (TopCat.of B) (∅ : Set B) U V (d + 1))).ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    (honest_exact₁ (TopCat.of B) (∅ : Set B) U V hU hV hcov d)

/-- `honestDelta` followed by a restriction is `0`, on elements. -/
theorem pdCohRes_honestDelta_apply (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (d : ℕ) (z : ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) d)) :
    (ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U (d + 1))
        (ModuleCat.Hom.hom (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d) z) = 0)
      ∧ (ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V (d + 1))
        (ModuleCat.Hom.hom (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d) z) = 0) := by
  constructor
  · have h := congrArg (fun (φ : pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) d ⟶
        pdCohSub (TopCat.of B) (∅ : Set B) U (d + 1)) => ModuleCat.Hom.hom φ z)
      (honestDelta_comp_pdCohRes (B := B) (U := U) (V := V) hU hV hcov d).1
    simpa using h
  · have h := congrArg (fun (φ : pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) d ⟶
        pdCohSub (TopCat.of B) (∅ : Set B) V (d + 1)) => ModuleCat.Hom.hom φ z)
      (honestDelta_comp_pdCohRes (B := B) (U := U) (V := V) hU hV hcov d).2
    simpa using h

/-! ## The maps of the ladder, elementwise -/

/-- The first component of `MvF`. -/
theorem MvF_fst_apply (k : ℕ) (x : ↑(MvM B m k)) :
    ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)
        (ModuleCat.Hom.hom (MvF B m k U V) x)
      = ModuleCat.Hom.hom (MvRes B m k U) x := by
  rw [← ModuleCat.comp_apply, MvF_fst]

/-- The second component of `MvF`. -/
theorem MvF_snd_apply (k : ℕ) (x : ↑(MvM B m k)) :
    ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)
        (ModuleCat.Hom.hom (MvF B m k U V) x)
      = ModuleCat.Hom.hom (MvRes B m k V) x := by
  rw [← ModuleCat.comp_apply, MvF_snd]

/-- `MvF` in the product presentation: the pair of the two restrictions. -/
theorem MvPIso_MvF_apply (k : ℕ) (x : ↑(MvM B m k)) :
    ModuleCat.Hom.hom (MvPIso m k U V).hom (ModuleCat.Hom.hom (MvF B m k U V) x)
      = (ModuleCat.Hom.hom (MvRes B m k U) x, ModuleCat.Hom.hom (MvRes B m k V) x) := by
  simp only [MvPIso_def]
  refine Prod.ext ?_ ?_
  · rw [biprodIsoProd_hom_apply_fst, MvF_fst_apply]
  · rw [biprodIsoProd_hom_apply_snd, MvF_snd_apply]

/-- `MvG` in the product presentation: the componentwise difference of the two restrictions to
the overlap. -/
theorem MvG_prod_apply (k : ℕ) (w : ↑(MvW B m k U) × ↑(MvW B m k V)) :
    ModuleCat.Hom.hom (MvG B m k U V) (ModuleCat.Hom.hom (MvPIso m k U V).inv w)
      = fun i : lhIdx m k =>
          ModuleCat.Hom.hom
              (pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left
                (k - 2 * (i : ℕ))) (w.1 i)
            - ModuleCat.Hom.hom
              (pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right
                (k - 2 * (i : ℕ))) (w.2 i) := by
  funext i
  simp only [MvPIso_def]
  rw [MvG, biprod_desc_apply, ModuleCat.hom_neg, LinearMap.neg_apply,
    biprodIsoProd_inv_apply_fst, biprodIsoProd_inv_apply_snd]
  rw [Pi.add_apply]
  rw [Pi.neg_apply]
  rw [MvResOvlU_apply, MvResOvlV_apply]
  rw [sub_eq_add_neg]

/-- Membership in `ker MvF` is componentwise vanishing of the two restrictions. -/
theorem mem_ker_MvF (k : ℕ) (x : ↑(MvM B m k)) :
    x ∈ (MvF B m k U V).hom.ker
      ↔ ∀ i : lhIdx m k,
          ModuleCat.Hom.hom (MvRes B m k U) x i = 0
            ∧ ModuleCat.Hom.hom (MvRes B m k V) x i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i
    have h1 : ModuleCat.Hom.hom (biprod.fst : MvP B m k U V ⟶ MvW B m k U)
        (ModuleCat.Hom.hom (MvF B m k U V) x) = 0 := by
      rw [h]
      exact map_zero _
    have h2 : ModuleCat.Hom.hom (biprod.snd : MvP B m k U V ⟶ MvW B m k V)
        (ModuleCat.Hom.hom (MvF B m k U V) x) = 0 := by
      rw [h]
      exact map_zero _
    rw [MvF_fst_apply] at h1
    rw [MvF_snd_apply] at h2
    exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
  · intro h
    refine eq_zero_of_biprod_components ?_ ?_
    · funext i
      rw [MvF_fst_apply]
      exact (h i).1
    · funext i
      rw [MvF_snd_apply]
      exact (h i).2

/-- The range of `MvF` in the product presentation, componentwise. -/
theorem mem_range_MvF_prod (k : ℕ) (w : ↑(MvW B m k U) × ↑(MvW B m k V)) :
    w ∈ ((MvF B m k U V) ≫ (MvPIso m k U V).hom).hom.range
      ↔ ∀ i : lhIdx m k,
          biprodPair (w.1 i) (w.2 i)
            ∈ (honestF (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ))).hom.range := by
  constructor
  · intro hw i
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hw
    have hx' : (ModuleCat.Hom.hom (MvRes B m k U) x, ModuleCat.Hom.hom (MvRes B m k V) x)
        = w := by
      rw [← hx, ModuleCat.hom_comp, LinearMap.comp_apply, MvPIso_MvF_apply]
    have h1 : w.1 = ModuleCat.Hom.hom (MvRes B m k U) x := (congrArg Prod.fst hx').symm
    have h2 : w.2 = ModuleCat.Hom.hom (MvRes B m k V) x := (congrArg Prod.snd hx').symm
    refine LinearMap.mem_range.mpr ⟨x i, ?_⟩
    rw [h1, h2, MvRes_apply, MvRes_apply, ← honestF_apply_pair]
  · intro hw
    choose y hy using hw
    have hy' : ∀ i : lhIdx m k,
        ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U (k - 2 * (i : ℕ))) (y i) = w.1 i
        ∧ ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V (k - 2 * (i : ℕ))) (y i)
            = w.2 i := by
      intro i
      have h := hy i
      rw [honestF_apply_pair] at h
      exact biprodPair_inj h
    refine LinearMap.mem_range.mpr ⟨fun i => y i, ?_⟩
    have h1 : ModuleCat.Hom.hom (MvRes B m k U) (fun i => y i) = w.1 := by
      funext i
      rw [MvRes_apply]
      exact (hy' i).1
    have h2 : ModuleCat.Hom.hom (MvRes B m k V) (fun i => y i) = w.2 := by
      funext i
      rw [MvRes_apply]
      exact (hy' i).2
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, MvPIso_MvF_apply, h1, h2]

/-- Membership in `ker MvG` in the product presentation, componentwise. -/
theorem mem_ker_MvG_prod (k : ℕ) (w : ↑(MvW B m k U) × ↑(MvW B m k V)) :
    w ∈ ((MvPIso m k U V).inv ≫ (MvG B m k U V)).hom.ker
      ↔ ∀ i : lhIdx m k,
          biprodPair (w.1 i) (w.2 i)
            ∈ (honestG (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ))).hom.ker := by
  have hfun : ModuleCat.Hom.hom (MvG B m k U V) (ModuleCat.Hom.hom (MvPIso m k U V).inv w)
      = fun i : lhIdx m k =>
          ModuleCat.Hom.hom (honestG (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ)))
            (biprodPair (w.1 i) (w.2 i)) := by
    rw [MvG_prod_apply]
    funext i
    exact (honestG_apply_pair (B := B) (U := U) (V := V) (k - 2 * (i : ℕ))
      (w.1 i) (w.2 i)).symm
  rw [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply, hfun]
  constructor
  · intro h i
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : (i : lhIdx m k) →
      ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (i : ℕ))) => f i) h
  · intro h
    funext i
    rw [Pi.zero_apply]
    exact LinearMap.mem_ker.mp (h i)

/-- Membership in the range of `MvG` in the product presentation, componentwise. -/
theorem mem_range_MvG_prod (k : ℕ) (c : ↑(MvQ B m k U V)) :
    c ∈ ((MvPIso m k U V).inv ≫ (MvG B m k U V)).hom.range
      ↔ ∀ i : lhIdx m k,
          c i ∈ (honestG (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ))).hom.range := by
  constructor
  · intro hc i
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hc
    have hci : c i = ModuleCat.Hom.hom (MvG B m k U V)
        (ModuleCat.Hom.hom (MvPIso m k U V).inv w) i := by
      rw [← hw, ModuleCat.hom_comp]
      rfl
    have hcomp : ModuleCat.Hom.hom (MvG B m k U V)
        (ModuleCat.Hom.hom (MvPIso m k U V).inv w) i
        = ModuleCat.Hom.hom (honestG (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ)))
            (biprodPair (w.1 i) (w.2 i)) := by
      rw [MvG_prod_apply]
      exact (honestG_apply_pair (B := B) (U := U) (V := V) (k - 2 * (i : ℕ))
        (w.1 i) (w.2 i)).symm
    rw [hci, hcomp]
    exact LinearMap.mem_range.mpr ⟨biprodPair (w.1 i) (w.2 i), rfl⟩
  · intro hc
    choose z hz using hc
    refine LinearMap.mem_range.mpr
      ⟨mkMvPair m k U V (fun i => (biprodTofstSnd (z i)).1)
        (fun i => (biprodTofstSnd (z i)).2), ?_⟩
    funext i
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, MvG_prod_apply]
    simp only [mkMvPair_fst, mkMvPair_snd]
    rw [← honestG_apply_pair]
    have hz' : biprodPair (biprodTofstSnd (z i)).1 (biprodTofstSnd (z i)).2 = z i :=
      biprodPair_tofstSnd (z i)
    rw [hz']
    exact hz i

/-! ## The map `MvD` -/

/-- The `J`-th component of `MvD`, in the case `2J ≤ k`: the connecting map followed by the degree
cast. -/
theorem MvD_apply_of_le (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (c : ↑(MvQ B m k U V)) (J : lhIdx m (k + 1)) (h : 2 * (J : ℕ) ≤ k)
    (hc : k - 2 * (J : ℕ) + 1 = k + 1 - 2 * (J : ℕ)) :
    ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) c J
      = ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hc)
          (ModuleCat.Hom.hom
            (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (J : ℕ)))
            (c ⟨J.1, h⟩)) := by
  have hcomp : (LinearMap.proj (R := ℤ) J).comp
        (ModuleCat.Hom.hom (MvD B m k U V hU hV hcov))
      = ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hc)
          ∘ₗ ((ModuleCat.Hom.hom
                (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (J : ℕ))))
              ∘ₗ LinearMap.proj (R := ℤ) (⟨J.1, h⟩ : lhIdx m k)) := by
    rw [show ModuleCat.Hom.hom (MvD B m k U V hU hV hcov)
        = LinearMap.pi (fun i : lhIdx m (k + 1) =>
            if h : 2 * (i : ℕ) ≤ k then
              ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B)
                (by omega : k - 2 * (i : ℕ) + 1 = k + 1 - 2 * (i : ℕ)))
                ∘ₗ ((ModuleCat.Hom.hom (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov
                      (k - 2 * (i : ℕ))))
                  ∘ₗ LinearMap.proj (⟨i.1, h⟩ : lhIdx m k))
            else 0) from rfl]
    rw [LinearMap.proj_pi]
    rw [dif_pos h]
  have hcJ := congrArg (fun (f : ↑(MvQ B m k U V) →ₗ[ℤ] ↑(pdCoh (TopCat.of B) (∅ : Set B)
      (k + 1 - 2 * (J : ℕ)))) => f c) hcomp
  rw [LinearMap.comp_apply] at hcJ
  exact hcJ

/-- The `J`-th component of `MvD`, in the case `2J = k+1`. -/
theorem MvD_apply_of_gt (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (c : ↑(MvQ B m k U V)) (J : lhIdx m (k + 1)) (h : ¬ 2 * (J : ℕ) ≤ k) :
    ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) c J = 0 := by
  have hcomp : (LinearMap.proj (R := ℤ) J).comp
        (ModuleCat.Hom.hom (MvD B m k U V hU hV hcov)) = 0 := by
    rw [show ModuleCat.Hom.hom (MvD B m k U V hU hV hcov)
        = LinearMap.pi (fun i : lhIdx m (k + 1) =>
            if h : 2 * (i : ℕ) ≤ k then
              ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B)
                (by omega : k - 2 * (i : ℕ) + 1 = k + 1 - 2 * (i : ℕ)))
                ∘ₗ ((ModuleCat.Hom.hom (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov
                      (k - 2 * (i : ℕ))))
                  ∘ₗ LinearMap.proj (⟨i.1, h⟩ : lhIdx m k))
            else 0) from rfl]
    rw [LinearMap.proj_pi]
    rw [dif_neg h]
  have hcJ := congrArg (fun (f : ↑(MvQ B m k U V) →ₗ[ℤ] ↑(pdCoh (TopCat.of B) (∅ : Set B)
      (k + 1 - 2 * (J : ℕ)))) => f c) hcomp
  rw [LinearMap.comp_apply] at hcJ
  exact hcJ

/-- Membership in `ker MvD`, componentwise vanishing of the connecting maps. -/
theorem mem_ker_MvD (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (c : ↑(MvQ B m k U V)) :
    c ∈ (MvD B m k U V hU hV hcov).hom.ker
      ↔ ∀ i : lhIdx m k,
          ModuleCat.Hom.hom
            (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (i : ℕ))) (c i) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hc i
    have h0 : ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) c (lhIdxSucc i) = 0 := by
      have h := congrArg (fun z => (LinearMap.proj (R := ℤ)
        (φ := fun j : lhIdx m (k + 1) => ↑(pdCoh (TopCat.of B) (∅ : Set B)
          (k + 1 - 2 * (j : ℕ)))) (lhIdxSucc i)) z) hc
      rw [map_zero, MvM_proj_apply] at h
      exact h
    have hone := MvD_apply_of_le (B := B) (U := U) (V := V) hU hV hcov k c (lhIdxSucc i) i.2
      (by have hi : 2 * (i : ℕ) ≤ k := i.2
          simp only [lhIdxSucc_val]
          omega)
    rw [hone] at h0
    exact (pdCast_eq_zero_iff (TopCat.of B) (∅ : Set B) _ _).mp h0
  · intro hc
    funext J
    by_cases h : 2 * (J : ℕ) ≤ k
    · rw [MvD_apply_of_le (B := B) (U := U) (V := V) hU hV hcov k c J h (by omega),
        hc ⟨J.1, h⟩, map_zero]
      rw [Pi.zero_apply]
    · rw [MvD_apply_of_gt (B := B) (U := U) (V := V) hU hV hcov k c J h]
      rw [Pi.zero_apply]

/-- **The range of `MvD`**, componentwise: the two restrictions of `d J` vanish. -/
theorem mem_range_MvD (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ)
    (d : ↑(MvM B m (k + 1))) :
    d ∈ (MvD B m k U V hU hV hcov).hom.range
      ↔ ∀ J : lhIdx m (k + 1),
          ModuleCat.Hom.hom (MvRes B m (k + 1) U) d J = 0
            ∧ ModuleCat.Hom.hom (MvRes B m (k + 1) V) d J = 0 := by
  have hresU : ∀ J : lhIdx m (k + 1),
      ModuleCat.Hom.hom (MvRes B m (k + 1) U) d J
        = ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U
            (k + 1 - 2 * (J : ℕ))) (d J) :=
    fun J => MvRes_apply (k + 1) U d J
  have hresV : ∀ J : lhIdx m (k + 1),
      ModuleCat.Hom.hom (MvRes B m (k + 1) V) d J
        = ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V
            (k + 1 - 2 * (J : ℕ))) (d J) :=
    fun J => MvRes_apply (k + 1) V d J
  constructor
  · intro hd J
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hd
    have hdJ : d J = ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) c J := by rw [hc]
    by_cases h : 2 * (J : ℕ) ≤ k
    · have h1 : ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U
          (k + 1 - 2 * (J : ℕ))) (d J) = 0 := by
        rw [hdJ, MvD_apply_of_le (B := B) (U := U) (V := V) hU hV hcov k c J h (by omega),
          ← pdCohRes_pdCast_apply]
        rw [(pdCohRes_honestDelta_apply (B := B) (U := U) (V := V) hU hV hcov
          (k - 2 * (J : ℕ)) (c ⟨J.1, h⟩)).1, map_zero]
      have h2 : ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V
          (k + 1 - 2 * (J : ℕ))) (d J) = 0 := by
        rw [hdJ, MvD_apply_of_le (B := B) (U := U) (V := V) hU hV hcov k c J h (by omega),
          ← pdCohRes_pdCast_apply]
        rw [(pdCohRes_honestDelta_apply (B := B) (U := U) (V := V) hU hV hcov
          (k - 2 * (J : ℕ)) (c ⟨J.1, h⟩)).2, map_zero]
      exact ⟨by rw [hresU]; exact h1, by rw [hresV]; exact h2⟩
    · have hz0 : ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) c J = 0 :=
        MvD_apply_of_gt (B := B) (U := U) (V := V) hU hV hcov k c J h
      exact ⟨by rw [hresU, hdJ, hz0, map_zero], by rw [hresV, hdJ, hz0, map_zero]⟩
  · intro hd
    have hdU : ∀ J : lhIdx m (k + 1),
        ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U
            (k + 1 - 2 * (J : ℕ))) (d J) = 0 :=
      fun J => (hd J).1
    have hdV : ∀ J : lhIdx m (k + 1),
        ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V
            (k + 1 - 2 * (J : ℕ))) (d J) = 0 :=
      fun J => (hd J).2
    have hmem : ∀ i : lhIdx m k,
        ∃ z : ↑(pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) (k - 2 * (i : ℕ))),
          ModuleCat.Hom.hom
            (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov (k - 2 * (i : ℕ))) z
            = ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B)
                (by have hi : 2 * (i : ℕ) ≤ k := i.2; omega :
                  k + 1 - 2 * (i : ℕ) = k - 2 * (i : ℕ) + 1)) (d (lhIdxSucc i)) := by
      intro i
      have hy : ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B)
            (by have hi : 2 * (i : ℕ) ≤ k := i.2; omega :
              k + 1 - 2 * (i : ℕ) = k - 2 * (i : ℕ) + 1)) (d (lhIdxSucc i))
          ∈ (ModuleCat.Hom.hom
              (honestF (TopCat.of B) (∅ : Set B) U V (k - 2 * (i : ℕ) + 1))).ker := by
        rw [mem_ker_honestF]
        constructor
        · have hU' : ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U
                (k + 1 - 2 * (i : ℕ))) (d (lhIdxSucc i)) = 0 := hdU (lhIdxSucc i)
          rw [← pdCohRes_pdCast_apply]
          rw [hU', map_zero]
        · have hV' : ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V
                (k + 1 - 2 * (i : ℕ))) (d (lhIdxSucc i)) = 0 := hdV (lhIdxSucc i)
          rw [← pdCohRes_pdCast_apply]
          rw [hV', map_zero]
      rw [← range_honestDelta hU hV hcov (k - 2 * (i : ℕ))] at hy
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
      exact ⟨z, hz⟩
    choose z hz using hmem
    refine LinearMap.mem_range.mpr ⟨fun i => z i, ?_⟩
    funext J
    by_cases h : 2 * (J : ℕ) ≤ k
    · rw [MvD_apply_of_le (B := B) (U := U) (V := V) hU hV hcov k (fun i => z i) J h (by omega)]
      rw [hz ⟨J.1, h⟩]
      rw [pdCast_comp_pdCast_apply]
      refine eq_of_heq (Eq.rec (motive := fun x _ => HEq (d x) (d J)) (HEq.refl (d J)) ?_)
      exact (Subtype.ext rfl : lhIdxSucc (⟨J.1, h⟩ : lhIdx m k) = J).symm
    · have hz0 : ModuleCat.Hom.hom (MvD B m k U V hU hV hcov) (fun i => z i) J = 0 :=
        MvD_apply_of_gt (B := B) (U := U) (V := V) hU hV hcov k (fun i => z i) J h
      have hz1 : k + 1 - 2 * (J : ℕ) = 0 := by omega
      have hJ : d J = 0 := by
        have h1 : ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hz1) (d J)
            ∈ (ModuleCat.Hom.hom
              (honestF (TopCat.of B) (∅ : Set B) U V 0)).ker := by
          rw [mem_ker_honestF]
          constructor
          · rw [← pdCohRes_pdCast_apply]
            rw [hdU J, map_zero]
          · rw [← pdCohRes_pdCast_apply]
            rw [hdV J, map_zero]
        rw [honestF_ker_eq_bot hU hV hcov, Submodule.mem_bot] at h1
        have h4 : d J = ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hz1.symm)
            (ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hz1) (d J)) :=
          (pdCast_pdCast_symm_apply (TopCat.of B) (∅ : Set B) hz1 (d J)).symm
        rw [h1, map_zero] at h4
        exact h4
      rw [hz0, hJ]

/-- If the degree is `0`, then the kernel of `honestF` is trivial (at any degree equal to `0`). -/
theorem honestF_apply_eq_zero_of_degree_zero (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {d : ℕ} (hd : d = 0)
    (z : ↑(pdCoh (TopCat.of B) (∅ : Set B) d))
    (hz : z ∈ (ModuleCat.Hom.hom (honestF (TopCat.of B) (∅ : Set B) U V d)).ker) :
    z = 0 := by
  have h1 : ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hd) z
      ∈ (ModuleCat.Hom.hom (honestF (TopCat.of B) (∅ : Set B) U V 0)).ker := by
    rw [mem_ker_honestF] at hz ⊢
    obtain ⟨hz1, hz2⟩ := hz
    constructor
    · rw [← pdCohRes_pdCast_apply]
      rw [hz1, map_zero]
    · rw [← pdCohRes_pdCast_apply]
      rw [hz2, map_zero]
  rw [honestF_ker_eq_bot hU hV hcov, Submodule.mem_bot] at h1
  have h2 : z = ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hd.symm)
      (ModuleCat.Hom.hom (pdCast (TopCat.of B) (∅ : Set B) hd) z) :=
    (pdCast_pdCast_symm_apply (TopCat.of B) (∅ : Set B) hd z).symm
  rw [h1, map_zero] at h2
  exact h2

end Work.LerayHirsch.MvAux
