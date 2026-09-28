import Mathlib
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.DiscPair.collarHomeoA2
import Submission.Work.Serre.DiscPair.collarSetHomotopyEquiv
import Submission.Work.Serre.DiscPair.relPairHomotopic
import Submission.Work.Serre.DiscPair.stepAHomologyIso

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

namespace Aux

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-! ## The collar homeomorphism and the collar projection -/

def cylCollar (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ↥(cylU₀A₂ q) ≃ₜ ↥(cylSet₁ q) :=
  (Work.Serre.DiscPair.collarHomeoA2 D Γ ι f q).choose

theorem cylCollar_mk (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (x : X) (t : unitInterval) (ht : (t : ℝ) < 1/2)
    (hA₂ : Work.Serre.cylMk q (Sum.inl (x, t)) ∈ cylPairA₂ q) :
    cylCollar q ⟨⟨Work.Serre.cylMk q (Sum.inl (x, t)), hA₂⟩,
        (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩
      = ⟨(x, t), ⟨ht, (mem_cylPairA₂_cylMk_inl_iff q x t ht).mp hA₂⟩⟩ :=
  (Work.Serre.DiscPair.collarHomeoA2 D Γ ι f q).choose_spec.1 x t ht hA₂

theorem cylCollar_pairIff (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (y : ↥(cylU₀A₂ q)) :
    y ∈ cylU₀U₁A₂ q ↔ (cylCollar q y).1 ∈ cylSet₂ q :=
  (Work.Serre.DiscPair.collarHomeoA2 D Γ ι f q).choose_spec.2 y

theorem cylCollar_symm (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (x : X) (t : unitInterval) (ht : (t : ℝ) < 1/2) (h : t = 0 ∨ x ∈ cylPairA q) :
    (cylCollar q).symm ⟨(x, t), ⟨ht, h⟩⟩
      = ⟨⟨Work.Serre.cylMk q (Sum.inl (x, t)),
          (mem_cylPairA₂_cylMk_inl_iff q x t ht).mpr h⟩,
        (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩ := by
  rw [← cylCollar_mk q x t ht ((mem_cylPairA₂_cylMk_inl_iff q x t ht).mpr h),
    Homeomorph.symm_apply_apply]

/-- The same, with the membership proof kept generic (so that `rw` can match it). -/
theorem cylCollar_symm' (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (x : X) (t : unitInterval) (hmem : (x, t) ∈ cylSet₁ q) :
    (cylCollar q).symm ⟨(x, t), hmem⟩
      = ⟨⟨Work.Serre.cylMk q (Sum.inl (x, t)),
          (mem_cylPairA₂_cylMk_inl_iff q x t hmem.1).mpr hmem.2⟩,
        (mem_cylU₀_cylMk_inl_iff q x t).mpr hmem.1⟩ :=
  cylCollar_symm q x t hmem.1 hmem.2

def cylSetFst (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylSet₁ q), X) where
  toFun z := z.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

def cylPr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylU₀A₂ q), X) :=
  (cylSetFst q).comp ⟨cylCollar q, (cylCollar q).continuous⟩

theorem cylSet₁_homotopyEquiv_exists (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ∃ e : ContinuousMap.HomotopyEquiv ↥(cylSet₁ q) X, ∀ z, e.toFun z = cylSetFst q z := by
  obtain ⟨e, he⟩ := (Work.Serre.DiscPair.collarSetHomotopyEquiv D Γ ι f q).1
  exact ⟨e, fun z => by rw [he]; rfl⟩

def cylSet₁He (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv ↥(cylSet₁ q) X :=
  (cylSet₁_homotopyEquiv_exists q).choose

theorem cylSet₁He_toFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (cylSet₁He q).toFun = cylSetFst q :=
  ContinuousMap.ext (cylSet₁_homotopyEquiv_exists q).choose_spec

def cylPrHe (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv ↥(cylU₀A₂ q) X :=
  (Homeomorph.toHomotopyEquiv (cylCollar q)).trans (cylSet₁He q)

theorem cylPrHe_toFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (cylPrHe q).toFun = cylPr q := by
  ext y
  show (cylSet₁He q).toFun (cylCollar q y) = cylSetFst q (cylCollar q y)
  rw [cylSet₁He_toFun q]

theorem isIso_chainMap_cylPr (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of ↥(cylU₀A₂ q)) (TopCat.of X)
        (TopCat.ofHom (cylPr q))) k) := by
  have h := Work.Serre.IsRatHomologyIso.of_homotopyEquiv (cylPrHe q) k
  rwa [cylPrHe_toFun q] at h

/-! ## The relative part of the collar -/

def cylSet₂ToSet₁ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ↥(cylSet₂ q) → ↥(cylSet₁ q) :=
  fun z => ⟨z.1, ⟨z.2.2.1, Or.inr z.2.2.2⟩⟩

theorem continuous_cylSet₂ToSet₁ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Continuous (cylSet₂ToSet₁ q) :=
  Continuous.subtype_mk continuous_subtype_val _

def cylPairColl (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ↥(cylU₀U₁A₂ q) ≃ₜ ↥(cylSet₂ q) where
  toFun y := ⟨(cylCollar q y.1).1, (cylCollar_pairIff q y.1).mp y.2⟩
  invFun z := ⟨(cylCollar q).symm (cylSet₂ToSet₁ q z),
    (cylCollar_pairIff q ((cylCollar q).symm (cylSet₂ToSet₁ q z))).mpr (by
      rw [Homeomorph.apply_symm_apply]
      exact z.2)⟩
  left_inv y := by
    refine Subtype.ext ?_
    exact Homeomorph.symm_apply_apply (cylCollar q) y.1
  right_inv z := by
    apply Subtype.ext
    show (cylCollar q ((cylCollar q).symm (cylSet₂ToSet₁ q z))).1 = z.1
    rw [Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp ((cylCollar q).continuous.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk
    (((cylCollar q).symm.continuous).comp (continuous_cylSet₂ToSet₁ q)) _

def cylPairFst (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylSet₂ q), ↥(cylPairA q)) where
  toFun z := ⟨z.1.1, z.2.2.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun z : ↥(cylSet₂ q) => z.1.1) (continuous_fst.comp continuous_subtype_val)
    (fun z => z.2.2.2)

def cylPairProj (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylU₀U₁A₂ q), ↥(cylPairA q)) :=
  (cylPairFst q).comp ⟨cylPairColl q, (cylPairColl q).continuous⟩

theorem cylSet₂_homotopyEquiv_exists (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ∃ e : ContinuousMap.HomotopyEquiv ↥(cylSet₂ q) ↥(cylPairA q),
      ∀ z, e.toFun z = cylPairFst q z := by
  obtain ⟨e, he⟩ := (Work.Serre.DiscPair.collarSetHomotopyEquiv D Γ ι f q).2
  exact ⟨e, fun z => by rw [he]; rfl⟩

def cylSet₂He (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv ↥(cylSet₂ q) ↥(cylPairA q) :=
  (cylSet₂_homotopyEquiv_exists q).choose

theorem cylSet₂He_toFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (cylSet₂He q).toFun = cylPairFst q :=
  ContinuousMap.ext (cylSet₂_homotopyEquiv_exists q).choose_spec

def cylPairHe (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.HomotopyEquiv ↥(cylU₀U₁A₂ q) ↥(cylPairA q) :=
  (Homeomorph.toHomotopyEquiv (cylPairColl q)).trans (cylSet₂He q)

theorem cylPairHe_toFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (cylPairHe q).toFun = cylPairProj q := by
  ext y
  show ((cylSet₂He q).toFun (cylPairColl q y) : X) = ((cylPairFst q) (cylPairColl q y) : X)
  rw [show (cylSet₂He q).toFun = cylPairFst q from cylSet₂He_toFun q]

/-! ## The map `Λ` -/

theorem cylPr_mapsTo (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo (cylPr q) (cylU₀U₁A₂ q) (cylPairA q) :=
  fun y hy => ((cylCollar_pairIff q y).mp hy).2.2

def cylΛ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylU₀A₂ q)) (cylU₀U₁A₂ q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of X) (cylPairA q) :=
  Work.Serre.relChainsRPairMap (cylU₀U₁A₂ q) (cylPairA q) (cylPr q) (cylPr_mapsTo q)

theorem isIso_cylΛ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cylΛ q) m) := by
  refine relChainsRPairMap_homologyMap_isIso (cylU₀U₁A₂ q) (cylPairA q) (cylPr q)
    (cylPr_mapsTo q) m ?_ ?_
  · intro k
    exact isIso_chainMap_cylPr q k
  · intro k
    have h : restrictPair (cylU₀U₁A₂ q) (cylPairA q) (cylPr q) (cylPr_mapsTo q)
        = cylPairProj q := by
      refine ContinuousMap.ext (fun y => ?_)
      refine Subtype.ext ?_
      show cylPr q y.1 = (cylPairColl q y).1.1
      rfl
    rw [h]
    have h2 := Work.Serre.IsRatHomologyIso.of_homotopyEquiv (cylPairHe q) k
    rwa [cylPairHe_toFun q] at h2

/-! ## The excision and Step A isomorphisms, and the map `Φ` -/

def cylΞ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylU₀A₂ q)) (cylU₀U₁A₂ q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylPairA₂ q)) (cylU₁A₂ q) :=
  Work.Serre.relChainsRInclPairMap (TopCat.of ↥(cylPairA₂ q)) (cylU₀A₂ q) (cylU₁A₂ q)

theorem isIso_cylΞ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cylΞ q) m) :=
  Work.Serre.csrExcisionRat (TopCat.of ↥(cylPairA₂ q)) (cylU₀A₂ q) (cylU₁A₂ q)
    ((isOpen_cylU₀ q).preimage continuous_subtype_val)
    ((isOpen_cylU₁ q).preimage continuous_subtype_val)
    (cylU₀A₂_union_cylU₁A₂ q) m

def cylΨ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylPairA₂ q)) (cylU₁A₂ q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q) :=
  Work.Serre.relChainsRPairMap (cylU₁A₂ q) (cylPairUinA₂ q)
    (ContinuousMap.id ↥(cylPairA₂ q)) (cylU₁A₂_mapsTo_cylPairUinA₂ q)

theorem isIso_cylΨ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cylΨ q) m) :=
  Work.Serre.DiscPair.stepAHomologyIso D Γ ι f q
    (cylU₁A₂_mapsTo_cylPairUinA₂ q) m

def cylΩ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylU₀A₂ q)) (cylU₀U₁A₂ q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q) :=
  cylΞ q ≫ cylΨ q

theorem isIso_cylΩ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cylΩ q) m) := by
  rw [cylΩ, HomologicalComplex.homologyMap_comp]
  haveI := isIso_cylΞ q m
  haveI := isIso_cylΨ q m
  infer_instance

theorem cylInclA₂_mapsTo (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo (cylInclA₂ q) (cylPairA q) (cylPairUinA₂ q) :=
  fun x hx => hx

def cylΦ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (cylPairA q) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q) :=
  Work.Serre.relChainsRPairMap (cylPairA q) (cylPairUinA₂ q) (cylInclA₂ q) (cylInclA₂_mapsTo q)

/-! ## The push-down homotopy and the comparison -/

theorem continuous_unitIntervalMulSub_pair :
    Continuous (fun p : unitInterval × unitInterval => Work.Serre.unitIntervalMulSub p.1 p.2) := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : unitInterval × unitInterval => (1 - (p.1 : ℝ)) * (p.2 : ℝ)
  fun_prop

def cylPushFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (p : ↥(cylSet₁ q) × unitInterval) : ↥(cylSet₁ q) :=
  ⟨(p.1.1.1, Work.Serre.unitIntervalMulSub p.2 p.1.1.2),
    ⟨by
      have h1 : ((Work.Serre.unitIntervalMulSub p.2 p.1.1.2 : unitInterval) : ℝ)
          = (1 - (p.2 : ℝ)) * (p.1.1.2 : ℝ) := rfl
      rw [h1]
      have hτ : 0 ≤ (p.1.1.2 : ℝ) := p.1.1.2.2.1
      have hs : (1 - (p.2 : ℝ)) ≤ 1 := by linarith [p.2.2.1]
      have h2 : (1 - (p.2 : ℝ)) * (p.1.1.2 : ℝ) ≤ 1 * (p.1.1.2 : ℝ) :=
        mul_le_mul_of_nonneg_right hs hτ
      have ht : (p.1.1.2 : ℝ) < 1/2 := p.1.2.1
      linarith,
     by
      rcases p.1.2.2 with h0 | hA
      · left
        apply Subtype.ext
        have h1 : ((Work.Serre.unitIntervalMulSub p.2 p.1.1.2 : unitInterval) : ℝ)
            = (1 - (p.2 : ℝ)) * (p.1.1.2 : ℝ) := rfl
        rw [h1]
        have h0' : (p.1.1.2 : ℝ) = 0 := congrArg Subtype.val h0
        rw [h0', mul_zero]
        rfl
      · right; exact hA⟩⟩

theorem continuous_cylPushFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Continuous (cylPushFun q) := by
  refine Continuous.subtype_mk ?_ _
  have ha : Continuous fun p : ↥(cylSet₁ q) × unitInterval => p.1.1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hb : Continuous fun p : ↥(cylSet₁ q) × unitInterval => (p.2, p.1.1.2) :=
    continuous_snd.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))
  exact ha.prodMk (continuous_unitIntervalMulSub_pair.comp hb)

def cylPush (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylSet₁ q) × unitInterval, ↥(cylSet₁ q)) :=
  ⟨cylPushFun q, continuous_cylPushFun q⟩

theorem zero_lt_half_unitInterval : ((0 : unitInterval) : ℝ) < 1/2 := by norm_num

theorem cylPush_zero (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (z : ↥(cylSet₁ q)) : cylPush q (z, 0) = z := by
  show cylPushFun q (z, 0) = z
  apply Subtype.ext
  show ((z.1.1, Work.Serre.unitIntervalMulSub 0 z.1.2) : X × unitInterval) = z.1
  rw [Work.Serre.unitIntervalMulSub_zero_left]

theorem cylPush_one (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (z : ↥(cylSet₁ q)) :
    (cylPush q (z, 1)).1 = (z.1.1, (0 : unitInterval)) := by
  show ((z.1.1, Work.Serre.unitIntervalMulSub 1 z.1.2) : X × unitInterval)
      = (z.1.1, (0 : unitInterval))
  rw [Work.Serre.unitIntervalMulSub_one_left]

def cylHFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (p : unitInterval × ↥(cylU₀A₂ q)) : ↥(cylPairA₂ q) :=
  ((cylCollar q).symm (cylPush q (cylCollar q p.2, p.1))).1

theorem continuous_cylHFun (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Continuous (cylHFun q) := by
  have h1 : Continuous fun p : unitInterval × ↥(cylU₀A₂ q) => cylCollar q p.2 :=
    (cylCollar q).continuous.comp continuous_snd
  have h2 : Continuous fun p : unitInterval × ↥(cylU₀A₂ q) =>
      cylPush q (cylCollar q p.2, p.1) :=
    (cylPush q).continuous.comp (h1.prodMk continuous_fst)
  exact continuous_subtype_val.comp (((cylCollar q).symm.continuous).comp h2)

def cylH (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(unitInterval × ↥(cylU₀A₂ q), ↥(cylPairA₂ q)) :=
  ⟨cylHFun q, continuous_cylHFun q⟩

theorem cylH_zero (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (y : ↥(cylU₀A₂ q)) : cylH q (0, y) = y.1 := by
  show ((cylCollar q).symm (cylPush q (cylCollar q y, 0))).1 = y.1
  rw [cylPush_zero, Homeomorph.symm_apply_apply]

theorem cylH_one (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (y : ↥(cylU₀A₂ q)) :
    cylH q (1, y) = cylInclA₂ q (cylPr q y) := by
  show ((cylCollar q).symm (cylPush q (cylCollar q y, 1))).1 = cylInclA₂ q (cylPr q y)
  have hmem : (((cylCollar q) y).1.1, (0 : unitInterval)) ∈ cylSet₁ q :=
    ⟨zero_lt_half_unitInterval, Or.inl rfl⟩
  have hw : cylPush q (cylCollar q y, 1)
      = (⟨(((cylCollar q) y).1.1, (0 : unitInterval)), hmem⟩ : ↥(cylSet₁ q)) :=
    Subtype.ext (cylPush_one q (cylCollar q y))
  rw [hw, cylCollar_symm']
  rfl

def cylHomotopy (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ContinuousMap.Homotopy
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      ((cylInclA₂ q).comp (cylPr q)) :=
  ContinuousMap.Homotopy.mk (cylH q) (cylH_zero q) (cylH_one q)

theorem cylHomotopy_mem (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (t : unitInterval) (y : ↥(cylU₀A₂ q)) (hy : y ∈ cylU₀U₁A₂ q) :
    cylH q (t, y) ∈ cylPairUinA₂ q := by
  by_cases ht : t = 1
  · subst ht
    rw [cylH_one]
    show cylIncl q (cylPr q y) ∈ cylPairU q
    exact ((cylCollar_pairIff q y).mp hy).2.2
  · have hlt : (0 : ℝ) < 1 - (t : ℝ) := by
      have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht (Subtype.ext h))
      linarith
    have hz2 : (cylCollar q y).1 ∈ cylSet₂ q := (cylCollar_pairIff q y).mp hy
    have hpos : (0 : ℝ) < ((cylCollar q y).1.2 : ℝ) := hz2.1
    have hlt2 : ((cylCollar q y).1.2 : ℝ) < 1/2 := hz2.2.1
    have hA : (cylCollar q y).1.1 ∈ cylPairA q := hz2.2.2
    have hw : (cylPush q (cylCollar q y, t)).1 ∈ cylSet₂ q := by
      refine ⟨?_, ?_, hA⟩
      · show (0 : ℝ) < (Work.Serre.unitIntervalMulSub t (cylCollar q y).1.2 : unitInterval)
        have h1 : ((Work.Serre.unitIntervalMulSub t (cylCollar q y).1.2 : unitInterval) : ℝ)
            = (1 - (t : ℝ)) * ((cylCollar q y).1.2 : ℝ) := rfl
        rw [h1]
        exact mul_pos hlt hpos
      · show ((Work.Serre.unitIntervalMulSub t (cylCollar q y).1.2 : unitInterval) : ℝ) < 1/2
        have h1 : ((Work.Serre.unitIntervalMulSub t (cylCollar q y).1.2 : unitInterval) : ℝ)
            = (1 - (t : ℝ)) * ((cylCollar q y).1.2 : ℝ) := rfl
        rw [h1]
        have hs : (1 - (t : ℝ)) ≤ 1 := by linarith [t.2.1]
        have h2 : (1 - (t : ℝ)) * ((cylCollar q y).1.2 : ℝ) ≤ 1 * ((cylCollar q y).1.2 : ℝ) :=
          mul_le_mul_of_nonneg_right hs (le_of_lt hpos)
        linarith
    have hmem : (cylCollar q).symm (cylPush q (cylCollar q y, t)) ∈ cylU₀U₁A₂ q :=
      (cylCollar_pairIff q _).mpr (by rw [Homeomorph.apply_symm_apply]; exact hw)
    exact cylU₁A₂_subset_cylPairUinA₂ q hmem

theorem cylΞ_eq_pairMap (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    cylΞ q = Work.Serre.relChainsRPairMap (cylU₀U₁A₂ q) (cylU₁A₂ q)
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      (fun y hy => hy) := rfl

theorem cylInclMapsTo (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      (cylU₀U₁A₂ q) (cylPairUinA₂ q) :=
  fun y hy => cylU₁A₂_subset_cylPairUinA₂ q hy

theorem cylΩ_eq_cylΛΦ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (n : ℕ) :
    HomologicalComplex.homologyMap (cylΩ q) n
      = HomologicalComplex.homologyMap (cylΛ q ≫ cylΦ q) n := by
  have hΛΦ : cylΛ q ≫ cylΦ q = Work.Serre.relChainsRPairMap (cylU₀U₁A₂ q) (cylPairUinA₂ q)
      ((cylInclA₂ q).comp (cylPr q)) ((cylInclA₂_mapsTo q).comp (cylPr_mapsTo q)) :=
    Work.Serre.csrPairFunctoriality (cylPr q) (cylInclA₂ q) (cylPr_mapsTo q) (cylInclA₂_mapsTo q)
  have hΩ : cylΩ q = Work.Serre.relChainsRPairMap (cylU₀U₁A₂ q) (cylPairUinA₂ q)
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      (cylInclMapsTo q) := by
    show cylΞ q ≫ cylΨ q = Work.Serre.relChainsRPairMap (cylU₀U₁A₂ q) (cylPairUinA₂ q)
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      (cylInclMapsTo q)
    rw [cylΞ_eq_pairMap q]
    exact Work.Serre.csrPairFunctoriality
      (⟨fun y : ↥(cylU₀A₂ q) => y.1, continuous_subtype_val⟩ : C(↥(cylU₀A₂ q), ↥(cylPairA₂ q)))
      (ContinuousMap.id ↥(cylPairA₂ q)) (fun y hy => hy) (cylU₁A₂_mapsTo_cylPairUinA₂ q)
  rw [hΛΦ, hΩ]
  exact Work.Serre.DiscPair.relPairHomotopic (cylInclMapsTo q)
    ((cylInclA₂_mapsTo q).comp (cylPr_mapsTo q)) (cylHomotopy q)
    (fun t y hy => cylHomotopy_mem q t y hy) n

theorem isIso_cylΦ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cylΦ q) m) := by
  have h : HomologicalComplex.homologyMap (cylΛ q) m ≫ HomologicalComplex.homologyMap (cylΦ q) m
      = HomologicalComplex.homologyMap (cylΩ q) m := by
    rw [← HomologicalComplex.homologyMap_comp, ← cylΩ_eq_cylΛΦ q m]
  haveI h1 : IsIso (HomologicalComplex.homologyMap (cylΛ q) m) := isIso_cylΛ q m
  haveI h2 : IsIso (HomologicalComplex.homologyMap (cylΛ q) m
      ≫ HomologicalComplex.homologyMap (cylΦ q) m) := by
    rw [h]; exact isIso_cylΩ q m
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (cylΛ q) m)
    (HomologicalComplex.homologyMap (cylΦ q) m)

/-! ## Comparison with `subPairMap` -/

def cylUHom (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ↥(cylPairU q) ≃ₜ ↥(cylPairUinA₂ q) where
  toFun x := ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv x := by refine Subtype.ext ?_; rfl
  right_inv y := by refine Subtype.ext ?_; rfl
  continuous_toFun := Continuous.subtype_mk ((cylPairUincl q).continuous) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

def cylUChainIso (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Cohomology.singularChains ℚ (TopCat.of ↥(cylPairU q)) ≅
      Work.Cohomology.singularChains ℚ (TopCat.of ↥(cylPairUinA₂ q)) :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo (cylUHom q))

theorem cylUChainIso_hom_eq (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    cylPairChainInclU q = (cylUChainIso q).hom
      ≫ Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q) := by
  rw [cylPairChainInclU, cylUChainIso, Functor.mapIso_hom, TopCat.isoOfHomeo_hom,
    Work.StemsB.relChainsRIncl, ← Work.Cohomology.chainMap_comp_relChains]
  congr 1

theorem cylUChainIso_inv_eq (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q)
      = (cylUChainIso q).inv ≫ cylPairChainInclU q := by
  rw [cylUChainIso_hom_eq q, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def cylCokIso (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    cokernel (cylPairChainInclU q) ≅
      cokernel (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q)) where
  hom := cokernel.map (cylPairChainInclU q)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q))
    (cylUChainIso q).hom (𝟙 _) (by rw [Category.comp_id]; exact cylUChainIso_hom_eq q)
  inv := cokernel.map (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q)) (cylPairUinA₂ q))
    (cylPairChainInclU q) (cylUChainIso q).inv (𝟙 _)
    (by rw [Category.comp_id]; exact cylUChainIso_inv_eq q)
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (cylPairChainInclU q))).1
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.id_comp,
      Work.Cohomology.cokernel_π_map, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥(cylPairA₂ q))
      (cylPairUinA₂ q)))).1
    rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.id_comp,
      Work.Cohomology.cokernel_π_map, Category.id_comp, Category.comp_id]

/-- **Factoring `cokernel.map` along an isomorphism of the sources.** -/
theorem cokernel_map_factor {C : Type*} [Category C] [HasZeroMorphisms C]
    {P Q A B A' : C} (f : P ⟶ Q) [HasCokernel f] (g : A ⟶ B) [HasCokernel g]
    (g' : A' ⟶ B) [HasCokernel g'] (e : A ≅ A')
    (p : P ⟶ A) (p' : P ⟶ A') (q : Q ⟶ B)
    {w : f ≫ q = p ≫ g} {w' : f ≫ q = p' ≫ g'} (hg : g = e.hom ≫ g')
    (hp : p ≫ e.hom = p') (hg' : g' ≫ 𝟙 B = e.inv ≫ g) :
    cokernel.map f g p q w
      = cokernel.map f g' p' q w' ≫ cokernel.map g' g e.inv (𝟙 B) hg' := by
  apply (cancel_epi (cokernel.π f)).1
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Work.Cohomology.cokernel_π_map,
    Category.assoc, Work.Cohomology.cokernel_π_map, Category.id_comp]

/-- The relative part map `C_*(A) → C_*(A₂,U)` used by `cylΦ`. -/
def cylInclUin (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairA q), ↥(cylPairUinA₂ q)) where
  toFun x := ⟨cylInclA₂ q x.1, cylInclA₂_mapsTo q x.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((cylInclA₂ q).continuous.comp continuous_subtype_val) _

theorem cylUHom_comp (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    TopCat.ofHom (cylInclU q)
      ≫ TopCat.ofHom (⟨cylUHom q, (cylUHom q).continuous⟩ :
          C(↥(cylPairU q), ↥(cylPairUinA₂ q)))
      = TopCat.ofHom (cylInclUin q) := by
  rw [← TopCat.ofHom_comp]
  congr 1

theorem subPairMap_eq (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Serre.DiscPair.subPairMap q = cylΦ q ≫ (cylCokIso q).inv := by
  apply (cancel_epi (cokernel.π
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) (cylPairA q)))).1
  simp only [Work.Serre.DiscPair.subPairMap, cylΦ, Work.Serre.relChainsRPairMap,
    Work.Serre.relChainsRInclPairMap, Work.Serre.csrRelMapOf, cylCokIso]
  conv_rhs => rw [← Category.assoc]
  rw [Work.Cohomology.cokernel_π_map]
  rw [Work.Cohomology.cokernel_π_map]
  rw [Category.assoc, Work.Cohomology.cokernel_π_map, Category.id_comp]

end Aux

/-- **(T2), the crux**: the map of relative chain complexes
`subPairMap q : C_*(X,A;ℚ) → coker(C_*(U;ℚ) → C_*(A₂;ℚ))` induced by `cylIncl q` is a rational
homology isomorphism. -/
theorem subPairMapQuasiIso (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.DiscPair.subPairMap (D := D) (Γ := Γ) (ι := ι) (f := f) q) m) := by
  have h := Aux.subPairMap_eq (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
  rw [h, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (HomologicalComplex.homologyMap (Aux.cylΦ q) m) := Aux.isIso_cylΦ q m
  haveI : IsIso (HomologicalComplex.homologyMap (Aux.cylCokIso q).inv m) := by infer_instance
  infer_instance

end

end Work.Serre.DiscPair
