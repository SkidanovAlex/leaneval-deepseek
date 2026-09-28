import Mathlib
import Submission.Work.Serre.SweepRelDefs

/-!
# The boundary step of the sweep: `∂I^{m+1}` from `∂I^m`

This file proves `Work.Serre.sweepBdrySucc`: given the disk step `SweepRel m` and the sweep of the
boundary `∂I^m`, the sweep of `∂I^{m+1}` holds.

The boundary `∂I^{m+1}` is the union of the bottom face
`F = {z | z (Fin.last m) = 0}` (a copy of `I^m` via `snocPt · 0`) and the *dome*
`D = {z | IsDomePt z}` (= `∂I^{m+1} ∖ relint F`), also a copy of `I^m` via the dome
homeomorphism `e`.  On the rim `F ∩ D = ∂F` the lift is produced by the sweep of `∂I^m`; it is then
extended to `F` and to `D` by the disk step `SweepRel m`, and the two extensions are glued along
the (closed) rim.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The bottom face of `∂I^{m+1}` -/

/-- The point of `∂I^{m+1}` with first coordinates `x` and last coordinate `0`. -/
def bdryFacePt {m : ℕ} (x : Fin m → unitInterval) : ↥(Cube.boundary (Fin (m + 1))) :=
  ⟨snocPt x 0, snocPt_mem_boundary_of_last (x := x) 0 (Or.inl rfl)⟩

theorem continuous_bdryFacePt (m : ℕ) : Continuous (bdryFacePt (m := m)) :=
  Continuous.subtype_mk
    (Continuous.finInsertNth (A := fun _ : Fin (m + 1) => unitInterval) (i := Fin.last m)
      (f := fun _ : Fin m → unitInterval => (0 : unitInterval))
      (g := fun x : Fin m → unitInterval => x) continuous_const continuous_id)
    _

/-- The bottom face of `∂I^{m+1}`, as a continuous map. -/
def bdryFaceMap (m : ℕ) : C(Fin m → unitInterval, ↥(Cube.boundary (Fin (m + 1)))) :=
  ⟨bdryFacePt, continuous_bdryFacePt m⟩

/-- The relative interior of the bottom face, as a subset of `∂I^{m+1}`. -/
def bdryFaceInterior (m : ℕ) : Set ↥(Cube.boundary (Fin (m + 1))) :=
  {z | z.1 (Fin.last m) = 0 ∧ ∀ i : Fin m, 0 < (z.1 i.castSucc : ℝ) ∧ (z.1 i.castSucc : ℝ) < 1}

theorem isOpen_bdryFaceInterior (m : ℕ) : IsOpen (bdryFaceInterior m) := by
  have hcont : Continuous (fun y : Fin (m + 1) → unitInterval => (y (Fin.last m) : ℝ)) :=
    (continuous_apply (Fin.last m)).subtype_val
  have hcont_i : ∀ i : Fin m,
      Continuous (fun y : Fin (m + 1) → unitInterval => (y i.castSucc : ℝ)) :=
    fun i => (continuous_apply i.castSucc).subtype_val
  have hW : IsOpen {y : Fin (m + 1) → unitInterval |
      (y (Fin.last m) : ℝ) < 1 / 2 ∧ ∀ i : Fin m, 0 < (y i.castSucc : ℝ) ∧ (y i.castSucc : ℝ) < 1} := by
    have hEq : {y : Fin (m + 1) → unitInterval | (y (Fin.last m) : ℝ) < 1 / 2 ∧
        ∀ i : Fin m, 0 < (y i.castSucc : ℝ) ∧ (y i.castSucc : ℝ) < 1}
      = {y | (y (Fin.last m) : ℝ) < 1/2} ∩ ⋂ i : Fin m, {y | (y i.castSucc : ℝ) ∈ Set.Ioo 0 1} := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_Ioo]
    rw [hEq]
    exact (isOpen_Iio.preimage hcont).inter
      (isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (hcont_i i)))
  have hsub : bdryFaceInterior m = Subtype.val ⁻¹'
      {y : Fin (m + 1) → unitInterval |
        (y (Fin.last m) : ℝ) < 1 / 2 ∧ ∀ i : Fin m, 0 < (y i.castSucc : ℝ) ∧ (y i.castSucc : ℝ) < 1} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1]; norm_num, h2⟩
    · rintro ⟨h1, h2⟩
      have hy := z.2
      rw [mem_boundary_succ_last_iff] at hy
      rcases hy with (h | h) | h
      · exact ⟨h, h2⟩
      · rw [h] at h1; norm_num at h1
      · rw [Cube.boundary] at h
        obtain ⟨i, hi | hi⟩ := h
        · have hi' : (z.1 i.castSucc : ℝ) = 0 := congrArg Subtype.val hi
          linarith [(h2 i).1]
        · have hi' : (z.1 i.castSucc : ℝ) = 1 := congrArg Subtype.val hi
          linarith [(h2 i).2]
  rw [hsub]
  exact hW.preimage continuous_subtype_val

/-- The dome is closed in the boundary of the cube. -/
theorem isClosed_domePtSet (m : ℕ) :
    IsClosed {z : ↥(Cube.boundary (Fin (m + 1))) | Work.RatHurewicz.IsDomePt z.1} := by
  rw [← isOpen_compl_iff]
  have h : {z : ↥(Cube.boundary (Fin (m + 1))) | Work.RatHurewicz.IsDomePt z.1}ᶜ
      = bdryFaceInterior m := by
    ext z
    constructor
    · intro h
      by_contra hP
      exact h ⟨z.2, hP⟩
    · intro h hdome
      exact hdome.2 h
  rw [h]
  exact isOpen_bdryFaceInterior m

/-! ## The dome inside `∂I^{m+1}` -/

/-- The dome, viewed as a map into the boundary of the cube. -/
def domeMap {m : ℕ}
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
    C(Fin m → unitInterval, ↥(Cube.boundary (Fin (m + 1)))) :=
  ⟨fun x => ⟨(e x).1, (e x).2.1⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp e.continuous⟩

theorem domeMap_apply {m : ℕ}
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z})
    (x : Fin m → unitInterval) :
    (domeMap e x : Fin (m + 1) → unitInterval) = (e x).1 := rfl

theorem domeMap_symm {m : ℕ}
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z})
    (y : ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
    domeMap e (e.symm y) = ⟨y.1, y.2.1⟩ := by
  refine Subtype.ext ?_
  show ((e (e.symm y) : ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :
    Fin (m + 1) → unitInterval) = y.1
  rw [Homeomorph.apply_symm_apply]

/-- On the rim, the dome map and the bottom face map agree. -/
theorem domeMap_eq_bdryFaceMap {m : ℕ} (hm : 1 ≤ m)
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z})
    (he : Work.Serre.IsDomeHomeo hm e) (x : ↥(Cube.boundary (Fin m))) :
    domeMap e x.1 = bdryFaceMap m x.1 :=
  Subtype.ext (he.2.2 x.1 x.2)

/-! ## Elementary facts about `initPt` -/

theorem snocPt_initPt_of_last_eq_zero {m : ℕ} {z : Fin (m + 1) → unitInterval}
    (h : z (Fin.last m) = 0) : snocPt (initPt z) 0 = z := by
  have hh := snocPt_self z
  rw [h] at hh
  exact hh

theorem bdryFaceMap_initPt {m : ℕ} (z : ↥(Cube.boundary (Fin (m + 1))))
    (h : z.1 (Fin.last m) = 0) : bdryFaceMap m (initPt z.1) = z :=
  Subtype.ext (snocPt_initPt_of_last_eq_zero h)

theorem initPt_mem_boundary_of_isDomePt {m : ℕ} {z : Fin (m + 1) → unitInterval}
    (hz : Work.RatHurewicz.IsDomePt z) (h0 : z (Fin.last m) = 0) :
    initPt z ∈ Cube.boundary (Fin m) := by
  by_contra h
  rw [Cube.boundary, Set.mem_ofPred_eq] at h
  simp only [not_exists, not_or] at h
  refine hz.2 ⟨h0, fun i => ⟨?_, ?_⟩⟩
  · have h1 : (z i.castSucc : ℝ) ≠ 0 := fun hc => (h i).1 (Subtype.ext hc)
    exact lt_of_le_of_ne' (z i.castSucc).2.1 h1
  · have h1 : (z i.castSucc : ℝ) ≠ 1 := fun hc => (h i).2 (Subtype.ext hc)
    exact lt_of_le_of_ne (z i.castSucc).2.2 h1

/-! ## The main theorem -/

theorem sweepBdrySucc {m : ℕ} (hm : 1 ≤ m) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hrel : Work.Serre.SweepRel m E B p)
    (hbdry : Work.Serre.Sweep ↥(Cube.boundary (Fin m)) E B p)
    (e : (Fin m → unitInterval) ≃ₜ
      ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z})
    (he : Work.Serre.IsDomeHomeo hm e) :
    Work.Serre.Sweep ↥(Cube.boundary (Fin (m + 1))) E B p := by
  classical
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁
  -- ## the rim
  let rimF : C(↥(Cube.boundary (Fin m)), ↥(Cube.boundary (Fin (m + 1)))) :=
    (bdryFaceMap m).comp ⟨Subtype.val, continuous_subtype_val⟩
  let rimMap3 : C(↥(Cube.boundary (Fin m)) × unitInterval × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval) :=
    ⟨fun x => (rimF x.1, x.2), (rimF.continuous.comp continuous_fst).prodMk continuous_snd⟩
  let rimMap2 : C(↥(Cube.boundary (Fin m)) × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval) :=
    ⟨fun x => (rimF x.1, x.2), (rimF.continuous.comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨Grim, hGrim, hGrim₀, hGrim₁, hGrim₂⟩ :=
    hbdry (H.comp rimMap3) (f₀.comp rimMap2)
      (by
        ext x
        show p (f₀ (rimMap2 x)) = H (rimMap3 (x.1, 0, x.2))
        exact congrFun (congrArg DFunLike.coe h₀) (rimMap2 x))
      (f₁.comp rimMap2)
      (by
        ext x
        show p (f₁ (rimMap2 x)) = H (rimMap3 (x.1, x.2, 0))
        exact congrFun (congrArg DFunLike.coe h₁) (rimMap2 x))
      (f₂.comp rimMap2)
      (by
        ext x
        show p (f₂ (rimMap2 x)) = H (rimMap3 (x.1, x.2, 1))
        exact congrFun (congrArg DFunLike.coe h₂) (rimMap2 x))
      (fun z => c₀ (rimF z)) (fun z => c₁ (rimF z))
  -- ## the bottom face piece
  let fMap3 : C((Fin m → unitInterval) × unitInterval × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval) :=
    ⟨fun x => ((bdryFaceMap m) x.1, x.2),
      ((bdryFaceMap m).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let fMap2 : C((Fin m → unitInterval) × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval) :=
    ⟨fun x => ((bdryFaceMap m) x.1, x.2),
      ((bdryFaceMap m).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let HF : C((Fin m → unitInterval) × unitInterval × unitInterval, B) := H.comp fMap3
  let gF0 : C((Fin m → unitInterval) × unitInterval, E) := f₀.comp fMap2
  let gF1 : C((Fin m → unitInterval) × unitInterval, E) := f₁.comp fMap2
  let gF2 : C((Fin m → unitInterval) × unitInterval, E) := f₂.comp fMap2
  obtain ⟨GF, hGF, hGF₀, hGF₁, hGF₂, hGFrim⟩ :=
    hrel HF gF0
      (by
        ext x
        show p (f₀ (fMap2 x)) = H (fMap3 (x.1, 0, x.2))
        exact congrFun (congrArg DFunLike.coe h₀) (fMap2 x))
      gF1
      (by
        ext x
        show p (f₁ (fMap2 x)) = H (fMap3 (x.1, x.2, 0))
        exact congrFun (congrArg DFunLike.coe h₁) (fMap2 x))
      gF2
      (by
        ext x
        show p (f₂ (fMap2 x)) = H (fMap3 (x.1, x.2, 1))
        exact congrFun (congrArg DFunLike.coe h₂) (fMap2 x))
      (fun z => c₀ (bdryFaceMap m z)) (fun z => c₁ (bdryFaceMap m z))
      Grim
      (by
        ext x
        show p (Grim x) = H (fMap3 (x.1.1, x.2))
        exact congrFun (congrArg DFunLike.coe hGrim) x)
      (fun x b => by
        show Grim (x, 0, b) = f₀ (bdryFaceMap m x.1, b)
        exact hGrim₀ x b)
      (fun x a => by
        show Grim (x, a, 0) = f₁ (bdryFaceMap m x.1, a)
        exact hGrim₁ x a)
      (fun x a => by
        show Grim (x, a, 1) = f₂ (bdryFaceMap m x.1, a)
        exact hGrim₂ x a)
  -- ## the dome piece
  let dMap3 : C((Fin m → unitInterval) × unitInterval × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval) :=
    ⟨fun x => ((domeMap e) x.1, x.2),
      ((domeMap e).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let dMap2 : C((Fin m → unitInterval) × unitInterval,
      ↥(Cube.boundary (Fin (m + 1))) × unitInterval) :=
    ⟨fun x => ((domeMap e) x.1, x.2),
      ((domeMap e).continuous.comp continuous_fst).prodMk continuous_snd⟩
  let HD : C((Fin m → unitInterval) × unitInterval × unitInterval, B) := H.comp dMap3
  let gD0 : C((Fin m → unitInterval) × unitInterval, E) := f₀.comp dMap2
  let gD1 : C((Fin m → unitInterval) × unitInterval, E) := f₁.comp dMap2
  let gD2 : C((Fin m → unitInterval) × unitInterval, E) := f₂.comp dMap2
  have hrimD : ∀ x : ↥(Cube.boundary (Fin m)), domeMap e x.1 = bdryFaceMap m x.1 :=
    fun x => domeMap_eq_bdryFaceMap hm e he x
  obtain ⟨GD, hGD, hGD₀, hGD₁, hGD₂, hGDrim⟩ :=
    hrel HD gD0
      (by
        ext x
        show p (f₀ (dMap2 x)) = H (dMap3 (x.1, 0, x.2))
        exact congrFun (congrArg DFunLike.coe h₀) (dMap2 x))
      gD1
      (by
        ext x
        show p (f₁ (dMap2 x)) = H (dMap3 (x.1, x.2, 0))
        exact congrFun (congrArg DFunLike.coe h₁) (dMap2 x))
      gD2
      (by
        ext x
        show p (f₂ (dMap2 x)) = H (dMap3 (x.1, x.2, 1))
        exact congrFun (congrArg DFunLike.coe h₂) (dMap2 x))
      (fun z => c₀ (domeMap e z)) (fun z => c₁ (domeMap e z))
      Grim
      (by
        ext x
        show p (Grim x) = H (dMap3 (x.1.1, x.2))
        rw [show p (Grim x) = H (bdryFaceMap m x.1.1, x.2) from
          congrFun (congrArg DFunLike.coe hGrim) x]
        show H (bdryFaceMap m x.1.1, x.2) = H (domeMap e x.1.1, x.2)
        rw [hrimD x.1])
      (fun x b => by
        rw [show Grim (x, 0, b) = f₀ (bdryFaceMap m x.1, b) from hGrim₀ x b]
        show f₀ (bdryFaceMap m x.1, b) = f₀ (domeMap e x.1, b)
        rw [hrimD x])
      (fun x a => by
        rw [show Grim (x, a, 0) = f₁ (bdryFaceMap m x.1, a) from hGrim₁ x a]
        show f₁ (bdryFaceMap m x.1, a) = f₁ (domeMap e x.1, a)
        rw [hrimD x])
      (fun x a => by
        rw [show Grim (x, a, 1) = f₂ (bdryFaceMap m x.1, a) from hGrim₂ x a]
        show f₂ (bdryFaceMap m x.1, a) = f₂ (domeMap e x.1, a)
        rw [hrimD x])
  -- ## the glueing
  let Fset : Set (↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval) :=
    {x | x.1.1 (Fin.last m) = 0}
  let Dset : Set (↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval) :=
    {x | Work.RatHurewicz.IsDomePt x.1.1}
  let Ffun : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval → E :=
    fun x => GF (initPt x.1.1, x.2.1, x.2.2)
  let Dfun : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval → E :=
    fun x => if h : Work.RatHurewicz.IsDomePt x.1.1 then
      GD (e.symm ⟨x.1.1, h⟩, x.2.1, x.2.2) else Ffun x
  have hFclosed : IsClosed Fset :=
    isClosed_eq ((continuous_apply (Fin.last m)).comp
      (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hDclosed : IsClosed Dset := (isClosed_domePtSet m).preimage continuous_fst
  have hcover : Fset ∪ Dset = Set.univ := by
    ext x
    rw [Set.mem_union]
    constructor
    · intro _; trivial
    · intro _
      by_cases h : x.1.1 (Fin.last m) = 0
      · exact Or.inl h
      · exact Or.inr ⟨x.1.2, fun h' => h h'.1⟩
  have hFfun_cont : Continuous Ffun := by
    have hinit : Continuous (fun x : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval =>
        initPt x.1.1) :=
      continuous_pi (fun i => (continuous_apply i.castSucc).comp
        (continuous_subtype_val.comp continuous_fst))
    exact GF.continuous.comp (hinit.prodMk continuous_snd)
  have hDfun_on : ContinuousOn Dfun Dset := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hsub : Continuous (fun x : ↥Dset =>
        (Subtype.val x : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval)) :=
      continuous_subtype_val
    have hsub1 : Continuous (fun x : ↥Dset =>
        ((Subtype.val x : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval).1 :
          ↥(Cube.boundary (Fin (m + 1))))) :=
      continuous_fst.comp hsub
    have hsec : Continuous (fun x : ↥Dset => x.1.1.1) :=
      continuous_subtype_val.comp hsub1
    have hfun : Set.domRestrict Dset Dfun =
        fun x : ↥Dset => GD (e.symm (⟨x.1.1.1, x.2⟩ :
          ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}), x.1.2.1, x.1.2.2) := by
      funext x
      change Dfun (Subtype.val x) = _
      show (if h : Work.RatHurewicz.IsDomePt x.1.1.1 then
        GD (e.symm ⟨x.1.1.1, h⟩, x.1.2.1, x.1.2.2) else Ffun x.1) = _
      rw [dif_pos (show Work.RatHurewicz.IsDomePt x.1.1.1 from x.2)]
    rw [hfun]
    have hsymm : Continuous fun x : ↥Dset => e.symm (⟨x.1.1.1, x.2⟩ :
        ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) :=
      e.symm.continuous.comp (Continuous.subtype_mk hsec (fun x => x.2))
    exact GD.continuous.comp (hsymm.prodMk (continuous_snd.comp continuous_subtype_val))
  have hagree : ∀ x ∈ Fset ∩ Dset, Ffun x = Dfun x := by
    rintro x ⟨hF, hD⟩
    have hF' : x.1.1 (Fin.last m) = 0 := hF
    have hD' : Work.RatHurewicz.IsDomePt x.1.1 := hD
    have hy : initPt x.1.1 ∈ Cube.boundary (Fin m) := initPt_mem_boundary_of_isDomePt hD' hF'
    have hsymm : e.symm (⟨x.1.1, hD'⟩ :
        ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) = initPt x.1.1 := by
      have hval : ((e (initPt x.1.1) : ↥{z : Fin (m + 1) → unitInterval |
          Work.RatHurewicz.IsDomePt z}) : Fin (m + 1) → unitInterval) = x.1.1 := by
        calc ((e (initPt x.1.1) : ↥{z : Fin (m + 1) → unitInterval |
                Work.RatHurewicz.IsDomePt z}) : Fin (m + 1) → unitInterval)
            = snocPt (initPt x.1.1) 0 := he.2.2 (initPt x.1.1) hy
          _ = snocPt (initPt x.1.1) (x.1.1 (Fin.last m)) := by rw [hF']
          _ = x.1.1 := snocPt_self x.1.1
      have heq : e (initPt x.1.1) = (⟨x.1.1, hD'⟩ :
          ↥{z : Fin (m + 1) → unitInterval | Work.RatHurewicz.IsDomePt z}) := Subtype.ext hval
      rw [← heq, Homeomorph.symm_apply_apply]
    calc Ffun x = GF (initPt x.1.1, x.2.1, x.2.2) := rfl
      _ = Grim (⟨initPt x.1.1, hy⟩, x.2.1, x.2.2) := hGFrim ⟨initPt x.1.1, hy⟩ x.2.1 x.2.2
      _ = GD (initPt x.1.1, x.2.1, x.2.2) := (hGDrim ⟨initPt x.1.1, hy⟩ x.2.1 x.2.2).symm
      _ = GD (e.symm ⟨x.1.1, hD'⟩, x.2.1, x.2.2) := by rw [hsymm]
      _ = Dfun x := by
            show GD (e.symm ⟨x.1.1, hD'⟩, x.2.1, x.2.2) =
              (if h : Work.RatHurewicz.IsDomePt x.1.1 then
                GD (e.symm ⟨x.1.1, h⟩, x.2.1, x.2.2) else Ffun x)
            rw [dif_pos hD']
  let Gfun : ↥(Cube.boundary (Fin (m + 1))) × unitInterval × unitInterval → E :=
    fun x => if x ∈ Fset then Ffun x else Dfun x
  have hGfun_cont : Continuous Gfun := by
    change Continuous fun x => if x ∈ Fset then Ffun x else Dfun x
    exact continuous_of_isClosed_cover hFclosed hDclosed hcover
      hFfun_cont.continuousOn hDfun_on hagree
  refine ⟨⟨Gfun, hGfun_cont⟩, ?_, ?_, ?_, ?_⟩
  · -- the base map
    ext x
    change p (Gfun x) = H x
    by_cases hx : x ∈ Fset
    · have hF' : x.1.1 (Fin.last m) = 0 := hx
      have h1 : Gfun x = GF (initPt x.1.1, x.2.1, x.2.2) := by
        have h1a : Gfun x = Ffun x := by
          show (if x ∈ Fset then Ffun x else Dfun x) = Ffun x
          exact if_pos hx
        rw [h1a]
      rw [h1]
      rw [show p (GF (initPt x.1.1, x.2.1, x.2.2)) =
        H (bdryFaceMap m (initPt x.1.1), x.2.1, x.2.2) from
        congrFun (congrArg DFunLike.coe hGF) (initPt x.1.1, x.2.1, x.2.2)]
      show H (bdryFaceMap m (initPt x.1.1), x.2.1, x.2.2) = H x
      rw [bdryFaceMap_initPt x.1 hF']
    · have hzD : Work.RatHurewicz.IsDomePt x.1.1 := ⟨x.1.2, fun h' => hx h'.1⟩
      have h1 : Gfun x = GD (e.symm ⟨x.1.1, hzD⟩, x.2.1, x.2.2) := by
        have h1a : Gfun x = Dfun x := by
          show (if x ∈ Fset then Ffun x else Dfun x) = Dfun x
          exact if_neg hx
        have h1b : Dfun x = GD (e.symm ⟨x.1.1, hzD⟩, x.2.1, x.2.2) := by
          show (if h : Work.RatHurewicz.IsDomePt x.1.1 then
            GD (e.symm ⟨x.1.1, h⟩, x.2.1, x.2.2) else Ffun x) =
            GD (e.symm ⟨x.1.1, hzD⟩, x.2.1, x.2.2)
          exact dif_pos hzD
        rw [h1a, h1b]
      rw [h1]
      rw [show p (GD (e.symm ⟨x.1.1, hzD⟩, x.2.1, x.2.2)) =
        H (domeMap e (e.symm ⟨x.1.1, hzD⟩), x.2.1, x.2.2) from
        congrFun (congrArg DFunLike.coe hGD) (e.symm ⟨x.1.1, hzD⟩, x.2.1, x.2.2)]
      show H (domeMap e (e.symm ⟨x.1.1, hzD⟩), x.2.1, x.2.2) = H x
      rw [domeMap_symm e ⟨x.1.1, hzD⟩]
  · -- the face `s = 0`
    intro z t
    change Gfun (z, 0, t) = f₀ (z, t)
    by_cases hz : z.1 (Fin.last m) = 0
    · have hx : ((z, (0 : unitInterval), t)) ∈ Fset := hz
      have h1 : Gfun (z, 0, t) = GF (initPt z.1, 0, t) := by
        have h1a : Gfun (z, 0, t) = Ffun (z, 0, t) := by
          show (if (z, 0, t) ∈ Fset then Ffun (z, 0, t) else Dfun (z, 0, t)) = Ffun (z, 0, t)
          exact if_pos hx
        rw [h1a]
      rw [h1]
      rw [show GF (initPt z.1, 0, t) = f₀ (bdryFaceMap m (initPt z.1), t) from
        hGF₀ (initPt z.1) t]
      show f₀ (bdryFaceMap m (initPt z.1), t) = f₀ (z, t)
      rw [bdryFaceMap_initPt z hz]
    · have hzD : Work.RatHurewicz.IsDomePt z.1 := ⟨z.2, fun h' => hz h'.1⟩
      have hx : ¬ ((z, (0 : unitInterval), t)) ∈ Fset := hz
      have h1 : Gfun (z, 0, t) = GD (e.symm ⟨z.1, hzD⟩, 0, t) := by
        have h1a : Gfun (z, 0, t) = Dfun (z, 0, t) := by
          show (if (z, 0, t) ∈ Fset then Ffun (z, 0, t) else Dfun (z, 0, t)) = Dfun (z, 0, t)
          exact if_neg hx
        have h1b : Dfun (z, 0, t) = GD (e.symm ⟨z.1, hzD⟩, 0, t) := by
          show (if h : Work.RatHurewicz.IsDomePt z.1 then
            GD (e.symm ⟨z.1, h⟩, 0, t) else Ffun (z, 0, t)) = GD (e.symm ⟨z.1, hzD⟩, 0, t)
          exact dif_pos hzD
        rw [h1a, h1b]
      rw [h1]
      rw [show GD (e.symm ⟨z.1, hzD⟩, 0, t) = f₀ (domeMap e (e.symm ⟨z.1, hzD⟩), t) from
        hGD₀ (e.symm ⟨z.1, hzD⟩) t]
      show f₀ (domeMap e (e.symm ⟨z.1, hzD⟩), t) = f₀ (z, t)
      rw [domeMap_symm e ⟨z.1, hzD⟩]
  · -- the face `t = 0`
    intro z s
    change Gfun (z, s, 0) = f₁ (z, s)
    by_cases hz : z.1 (Fin.last m) = 0
    · have hx : ((z, s, (0 : unitInterval))) ∈ Fset := hz
      have h1 : Gfun (z, s, 0) = GF (initPt z.1, s, 0) := by
        have h1a : Gfun (z, s, 0) = Ffun (z, s, 0) := by
          show (if (z, s, 0) ∈ Fset then Ffun (z, s, 0) else Dfun (z, s, 0)) = Ffun (z, s, 0)
          exact if_pos hx
        rw [h1a]
      rw [h1]
      rw [show GF (initPt z.1, s, 0) = f₁ (bdryFaceMap m (initPt z.1), s) from
        hGF₁ (initPt z.1) s]
      show f₁ (bdryFaceMap m (initPt z.1), s) = f₁ (z, s)
      rw [bdryFaceMap_initPt z hz]
    · have hzD : Work.RatHurewicz.IsDomePt z.1 := ⟨z.2, fun h' => hz h'.1⟩
      have hx : ¬ ((z, s, (0 : unitInterval))) ∈ Fset := hz
      have h1 : Gfun (z, s, 0) = GD (e.symm ⟨z.1, hzD⟩, s, 0) := by
        have h1a : Gfun (z, s, 0) = Dfun (z, s, 0) := by
          show (if (z, s, 0) ∈ Fset then Ffun (z, s, 0) else Dfun (z, s, 0)) = Dfun (z, s, 0)
          exact if_neg hx
        have h1b : Dfun (z, s, 0) = GD (e.symm ⟨z.1, hzD⟩, s, 0) := by
          show (if h : Work.RatHurewicz.IsDomePt z.1 then
            GD (e.symm ⟨z.1, h⟩, s, 0) else Ffun (z, s, 0)) = GD (e.symm ⟨z.1, hzD⟩, s, 0)
          exact dif_pos hzD
        rw [h1a, h1b]
      rw [h1]
      rw [show GD (e.symm ⟨z.1, hzD⟩, s, 0) = f₁ (domeMap e (e.symm ⟨z.1, hzD⟩), s) from
        hGD₁ (e.symm ⟨z.1, hzD⟩) s]
      show f₁ (domeMap e (e.symm ⟨z.1, hzD⟩), s) = f₁ (z, s)
      rw [domeMap_symm e ⟨z.1, hzD⟩]
  · -- the face `t = 1`
    intro z s
    change Gfun (z, s, 1) = f₂ (z, s)
    by_cases hz : z.1 (Fin.last m) = 0
    · have hx : ((z, s, (1 : unitInterval))) ∈ Fset := hz
      have h1 : Gfun (z, s, 1) = GF (initPt z.1, s, 1) := by
        have h1a : Gfun (z, s, 1) = Ffun (z, s, 1) := by
          show (if (z, s, 1) ∈ Fset then Ffun (z, s, 1) else Dfun (z, s, 1)) = Ffun (z, s, 1)
          exact if_pos hx
        rw [h1a]
      rw [h1]
      rw [show GF (initPt z.1, s, 1) = f₂ (bdryFaceMap m (initPt z.1), s) from
        hGF₂ (initPt z.1) s]
      show f₂ (bdryFaceMap m (initPt z.1), s) = f₂ (z, s)
      rw [bdryFaceMap_initPt z hz]
    · have hzD : Work.RatHurewicz.IsDomePt z.1 := ⟨z.2, fun h' => hz h'.1⟩
      have hx : ¬ ((z, s, (1 : unitInterval))) ∈ Fset := hz
      have h1 : Gfun (z, s, 1) = GD (e.symm ⟨z.1, hzD⟩, s, 1) := by
        have h1a : Gfun (z, s, 1) = Dfun (z, s, 1) := by
          show (if (z, s, 1) ∈ Fset then Ffun (z, s, 1) else Dfun (z, s, 1)) = Dfun (z, s, 1)
          exact if_neg hx
        have h1b : Dfun (z, s, 1) = GD (e.symm ⟨z.1, hzD⟩, s, 1) := by
          show (if h : Work.RatHurewicz.IsDomePt z.1 then
            GD (e.symm ⟨z.1, h⟩, s, 1) else Ffun (z, s, 1)) = GD (e.symm ⟨z.1, hzD⟩, s, 1)
          exact dif_pos hzD
        rw [h1a, h1b]
      rw [h1]
      rw [show GD (e.symm ⟨z.1, hzD⟩, s, 1) = f₂ (domeMap e (e.symm ⟨z.1, hzD⟩), s) from
        hGD₂ (e.symm ⟨z.1, hzD⟩) s]
      show f₂ (domeMap e (e.symm ⟨z.1, hzD⟩), s) = f₂ (z, s)
      rw [domeMap_symm e ⟨z.1, hzD⟩]

end

end Work.Serre
