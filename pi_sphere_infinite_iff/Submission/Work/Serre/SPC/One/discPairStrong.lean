import Mathlib
import Submission.Work.Serre.SPC.One.DiscDefs
import Submission.Work.Serre.SPC.cubeStrong
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.Cohomology.relChainsMapOf_comp

set_option synthInstance.maxHeartbeats 400000


/-!
# The strong disc statement for the model `1`-cell

This is the `D = 1` case of `Work.Serre.SPC.cubePairStrong`: for a Serre fibration `p : E → B`,
a map `χ : D¹ → B` and a fibre which is homologically `φ`-connected over every point of the
interval, the map of pairs `(χ^*E, χ^*E|_{S⁰}) ⟶ (D¹, S⁰)` is an isomorphism on homology in
degrees `< 1 + φ` and surjective in degree `1 + φ`.

The proof transports `Work.Serre.SPC.cubePairStrong 1` (for the cube `I¹ = Fin 1 → I`) along the
affine homeomorphism `I¹ ≅ D¹`, `x ↦ 2 x₀ - 1`, exactly as
`Submission/Work/Serre/SPC/discStrong.lean` transports the general cube statement along
`I^{n+2} ≅ D^{n+2}`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

/-! ## The affine homeomorphism `I¹ ≅ D¹` -/

/-- The map `I¹ → D¹`, `x ↦ 2 x₀ - 1`. -/
def icOneToD1Fun (x : Work.Stems.Cubical.IC 1) : cellD1 :=
  ⟨2 * ((x 0 : unitInterval) : ℝ) - 1, by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    have h := (x 0).2
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]⟩

@[simp] theorem icOneToD1Fun_coe (x : Work.Stems.Cubical.IC 1) :
    ((icOneToD1Fun x : cellD1) : ℝ) = 2 * ((x 0 : unitInterval) : ℝ) - 1 := rfl

/-- The map `D¹ → I¹`, `t ↦ (t + 1)/2`. -/
def d1ToIcOneFun (t : cellD1) : Work.Stems.Cubical.IC 1 :=
  fun _ => ⟨(t.1 + 1) / 2, by
    have h : dist t.1 0 ≤ 1 := Metric.mem_closedBall.mp t.2
    rw [Real.dist_eq, sub_zero] at h
    constructor <;> nlinarith [abs_le.mp h |>.1, abs_le.mp h |>.2]⟩

@[simp] theorem d1ToIcOneFun_apply (t : cellD1) (i : Fin 1) :
    ((d1ToIcOneFun t i : unitInterval) : ℝ) = (t.1 + 1) / 2 := rfl

/-- The two maps of the affine identification are inverse to each other. -/
@[simp] theorem icOneToD1Fun_d1ToIcOneFun (t : cellD1) :
    icOneToD1Fun (d1ToIcOneFun t) = t := by
  refine Subtype.ext ?_
  show 2 * ((t.1 + 1) / 2) - 1 = t.1
  ring

@[simp] theorem d1ToIcOneFun_icOneToD1Fun (x : Work.Stems.Cubical.IC 1) :
    d1ToIcOneFun (icOneToD1Fun x) = x := by
  funext i
  refine Subtype.ext ?_
  show ((2 * ((x 0 : unitInterval) : ℝ) - 1) + 1) / 2 = ((x i : unitInterval) : ℝ)
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  ring

theorem continuous_icOneToD1Fun : Continuous icOneToD1Fun :=
  Continuous.subtype_mk (by fun_prop) fun x => (icOneToD1Fun x).2

theorem continuous_d1ToIcOneFun : Continuous d1ToIcOneFun := by
  apply continuous_pi
  intro i
  exact Continuous.subtype_mk (by fun_prop) fun t => (d1ToIcOneFun t i).2

/-- The continuous map `I¹ → D¹`, `x ↦ 2 x₀ - 1`. -/
def icOneToD1 : C(Work.Stems.Cubical.IC 1, cellD1) :=
  ⟨icOneToD1Fun, continuous_icOneToD1Fun⟩

/-- The continuous map `D¹ → I¹`, `t ↦ (t + 1)/2`. -/
def d1ToIcOne : C(cellD1, Work.Stems.Cubical.IC 1) :=
  ⟨d1ToIcOneFun, continuous_d1ToIcOneFun⟩

@[simp] theorem icOneToD1_apply (x : Work.Stems.Cubical.IC 1) :
    icOneToD1 x = icOneToD1Fun x := rfl

@[simp] theorem d1ToIcOne_apply (t : cellD1) : d1ToIcOne t = d1ToIcOneFun t := rfl

/-- The affine homeomorphism `I¹ ≅ D¹`, `x ↦ 2 x₀ - 1`. -/
def d1Homeo : Work.Stems.Cubical.IC 1 ≃ₜ cellD1 where
  toFun := icOneToD1
  invFun := d1ToIcOne
  left_inv x := d1ToIcOneFun_icOneToD1Fun x
  right_inv t := icOneToD1Fun_d1ToIcOneFun t
  continuous_toFun := icOneToD1.continuous
  continuous_invFun := d1ToIcOne.continuous

@[simp] theorem d1Homeo_apply (x : Work.Stems.Cubical.IC 1) :
    d1Homeo x = icOneToD1Fun x := rfl

@[simp] theorem d1Homeo_symm_apply (t : cellD1) : d1Homeo.symm t = d1ToIcOneFun t := rfl

/-! ## The homeomorphism carries `∂I¹` onto `S⁰ = {±1}` -/

@[simp] theorem cellS0ToD1_coe (z : Work.Serre.SPC.cellS0) :
    ((Work.Serre.SPC.cellS0ToD1 z : cellD1) : ℝ) = (z : ℝ) := rfl

/-- A point of `I¹` is a boundary point exactly when `2 x₀ - 1 = ±1`. -/
theorem icOneToD1_mem_cellS0Set {x : Work.Stems.Cubical.IC 1} :
    icOneToD1Fun x ∈ cellS0Set ↔ x ∈ Work.Serre.cubeBdryS 1 := by
  rw [Work.Serre.cubeBdryS, Cube.boundary, mem_cellS0Set]
  constructor
  · rintro ⟨z, hz⟩
    have hzR : (z : ℝ) = 2 * ((x 0 : unitInterval) : ℝ) - 1 := by
      have h := congrArg (fun p : cellD1 => (p : ℝ)) hz
      simpa only [cellS0ToD1_coe, icOneToD1Fun_coe] using h
    have hzA : |(z : ℝ)| = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [Real.dist_eq, sub_zero] at h
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hzA with h1 | h1
    · refine ⟨0, Or.inr ?_⟩
      refine Subtype.ext ?_
      have h2 : ((x 0 : unitInterval) : ℝ) = 1 := by linarith [hzR, h1]
      rw [h2]
      norm_num
    · refine ⟨0, Or.inl ?_⟩
      refine Subtype.ext ?_
      have h2 : ((x 0 : unitInterval) : ℝ) = 0 := by linarith [hzR, h1]
      rw [h2]
      norm_num
  · rintro ⟨i, hi⟩
    have hi0 : (x 0 : unitInterval) = 0 ∨ (x 0 : unitInterval) = 1 := by
      have h := hi
      rwa [Subsingleton.elim i 0] at h
    rcases hi0 with h | h
    · refine ⟨⟨-1, by rw [Metric.mem_sphere, Real.dist_eq]; norm_num⟩, ?_⟩
      refine Subtype.ext ?_
      show (-1 : ℝ) = 2 * ((x 0 : unitInterval) : ℝ) - 1
      rw [show ((x 0 : unitInterval) : ℝ) = 0 from congrArg Subtype.val h]
      ring
    · refine ⟨⟨1, by rw [Metric.mem_sphere, Real.dist_eq]; norm_num⟩, ?_⟩
      refine Subtype.ext ?_
      show (1 : ℝ) = 2 * ((x 0 : unitInterval) : ℝ) - 1
      rw [show ((x 0 : unitInterval) : ℝ) = 1 from congrArg Subtype.val h]
      ring

/-- The inverse direction of the boundary correspondence. -/
theorem d1ToIcOneFun_mem_cubeBdryS {t : cellD1} :
    d1ToIcOneFun t ∈ Work.Serre.cubeBdryS 1 ↔ t ∈ cellS0Set := by
  have h := icOneToD1_mem_cellS0Set (x := d1ToIcOneFun t)
  rw [icOneToD1Fun_d1ToIcOneFun] at h
  exact h.symm

/-! ## The homeomorphism of pullbacks -/

/-- **The homeomorphism of pullbacks** `(χ ∘ e)^*E ≅ χ^*E` covering the cube–disc
homeomorphism. -/
def pbH1 {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (χ : C(cellD1, B)) :
    Work.StemsB.Pullback p (χ.comp icOneToD1) ≃ₜ Work.StemsB.Pullback p χ where
  toFun x := ⟨(x.1.1, icOneToD1Fun x.1.2), x.2⟩
  invFun y := ⟨(y.1.1, d1ToIcOneFun y.1.2), by
    show p y.1.1 = χ (icOneToD1Fun (d1ToIcOneFun y.1.2))
    rw [icOneToD1Fun_d1ToIcOneFun]
    exact y.2⟩
  left_inv x := Subtype.ext (by ext <;> simp)
  right_inv y := Subtype.ext (by ext <;> simp)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      (icOneToD1.continuous.comp continuous_subtype_val.snd)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      (d1ToIcOne.continuous.comp continuous_subtype_val.snd)

@[simp] theorem pbH1_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (χ : C(cellD1, B))
    (x : Work.StemsB.Pullback p (χ.comp icOneToD1)) :
    pbH1 p χ x = ⟨(x.1.1, icOneToD1Fun x.1.2), x.2⟩ := rfl

/-- The pullback homeomorphism respects the preimages of the boundary. -/
theorem pbH1_mem {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (χ : C(cellD1, B)) (x : Work.StemsB.Pullback p (χ.comp icOneToD1)) :
    x ∈ Work.Serre.pbPre p (χ.comp icOneToD1) (Work.Serre.cubeBdryS 1)
      ↔ pbH1 p χ x ∈ pbPreOne p χ := by
  show x.1.2 ∈ Work.Serre.cubeBdryS 1 ↔ icOneToD1Fun x.1.2 ∈ cellS0Set
  exact (icOneToD1_mem_cellS0Set (x := x.1.2)).symm

/-! ## The strong disc statement for the `1`-cell -/

theorem discPairStrong {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (hp : Work.StemsB.IsSerreFibration p)
    (χ : ContinuousMap Work.Serre.SPC.cellD1 B) (φ : ℕ)
    (hfib : ∀ y : Work.Serre.SPC.cellD1, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (χ y)))).homology j))
    (h0 : ∀ y : Work.Serre.SPC.cellD1,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p (χ y)))
        (ModuleCat.of ℤ ℤ))) :
    (∀ i : ℕ, i < 1 + φ → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.SPC.One.discPairMap p χ) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.SPC.One.discPairMap p χ) (1 + φ)).hom := by
  classical
  let τ : C(Work.Stems.Cubical.IC 1, B) := χ.comp icOneToD1
  obtain ⟨hcubeIso, hcubeSurj⟩ :=
    Work.Serre.SPC.cubePairStrong 1 E B p hp τ φ
      (fun y j hj hjφ => hfib (icOneToD1 y) j hj hjφ)
      (fun y => h0 (icOneToD1 y))
  let A₁ : Set (Work.StemsB.Pullback p τ) := Work.Serre.pbPre p τ (Work.Serre.cubeBdryS 1)
  let B₁ : Set (Work.StemsB.Pullback p χ) := pbPreOne p χ
  let Bs : Set (Work.Stems.Cubical.IC 1) := Work.Serre.cubeBdryS 1
  let Bd : Set cellD1 := cellS0Set
  let P : TopCat := TopCat.of (Work.StemsB.Pullback p τ)
  let Q : TopCat := TopCat.of (Work.StemsB.Pullback p χ)
  let X : TopCat := TopCat.of (Work.Stems.Cubical.IC 1)
  let Y : TopCat := TopCat.of cellD1
  let Φm : P ⟶ Q := Work.StemsB.sphHomeoHom (pbH1 p χ)
  let hcb : ∀ x ∈ A₁, Φm x ∈ B₁ := fun x hx => (pbH1_mem p χ x).mp hx
  let hcb' : ∀ y ∈ B₁, Work.StemsB.sphHomeoHom (X := Q) (Y := P) (pbH1 p χ).symm y ∈ A₁ :=
    fun y hy => (pbH1_mem p χ ((pbH1 p χ).symm y)).mpr (by
      rw [Homeomorph.apply_symm_apply]; exact hy)
  let Φb : TopCat.of A₁ ⟶ TopCat.of B₁ := Work.StemsB.pairRestrict Φm A₁ B₁ hcb
  let wΦ : Work.Cohomology.subtypeIncl P A₁ ≫ Φm = Φb ≫ Work.Cohomology.subtypeIncl Q B₁ :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Φm A₁ B₁ hcb
  let Gm : Q ⟶ Y := TopCat.ofHom (Work.StemsB.pullbackSnd p χ)
  let Gb : TopCat.of B₁ ⟶ TopCat.of Bd := TopCat.ofHom (discPairMapRel p χ)
  let wG : Work.Cohomology.subtypeIncl Q B₁ ≫ Gm
      = Gb ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  let Fm : P ⟶ X := TopCat.ofHom (Work.StemsB.pullbackSnd p τ)
  let Fb : TopCat.of A₁ ⟶ TopCat.of Bs := TopCat.ofHom (Work.Serre.cubePairMapRel 1 p τ)
  let wF : Work.Cohomology.subtypeIncl P A₁ ≫ Fm
      = Fb ≫ Work.Cohomology.subtypeIncl X Bs := by ext x; rfl
  let Em : X ⟶ Y := Work.StemsB.sphHomeoHom d1Homeo
  let heb : ∀ x ∈ Bs, Em x ∈ Bd := fun x hx => icOneToD1_mem_cellS0Set.mpr hx
  let heb' : ∀ y ∈ Bd, Work.StemsB.sphHomeoHom (X := Y) (Y := X) d1Homeo.symm y ∈ Bs :=
    fun y hy => d1ToIcOneFun_mem_cubeBdryS.mpr hy
  let Eb : TopCat.of Bs ⟶ TopCat.of Bd := Work.StemsB.pairRestrict Em Bs Bd heb
  let wE : Work.Cohomology.subtypeIncl X Bs ≫ Em
      = Eb ≫ Work.Cohomology.subtypeIncl Y Bd :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Em Bs Bd heb
  have hD : Work.Serre.SPC.One.discPairMap p χ
      = Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG := rfl
  have hC : Work.Serre.cubePairMap 1 p τ
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF := rfl
  have hsquare : Φm ≫ Gm = Fm ≫ Em := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsquareB : Φb ≫ Gb = Fb ≫ Eb := by
    apply TopCat.hom_ext
    ext x
    rfl
  have w₁ : Work.Cohomology.subtypeIncl P A₁ ≫ (Φm ≫ Gm)
      = (Φb ≫ Gb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have w₂ : Work.Cohomology.subtypeIncl P A₁ ≫ (Fm ≫ Em)
      = (Fb ≫ Eb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have h1 := Work.Cohomology.relChainsMapOf_comp A₁ B₁ Bd Φm Φb wΦ Gm Gb wG w₁
  have h2 := Work.Cohomology.relChainsMapOf_comp A₁ Bs Bd Fm Fb wF Em Eb wE w₂
  have hm := Work.Serre.SPC.relChainsMapOf_congr' A₁ Bd hsquare hsquareB w₁ w₂
  have hrel : Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ
        ≫ Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF
        ≫ Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE :=
    h1.trans (hm.trans h2.symm)
  haveI hΦI : IsIso (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) :=
    Work.Serre.SPC.isIso_relChainsMapOf_homeo' (X := P) (Y := Q) (pbH1 p χ) A₁ B₁ hcb hcb'
  haveI hEI : IsIso (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) :=
    Work.Serre.SPC.isIso_relChainsMapOf_homeo' (X := X) (Y := Y) d1Homeo Bs Bd heb heb'
  constructor
  · intro i hi
    have hF : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF) i) := by
      rw [← hC]
      exact hcubeIso i hi
    rw [hD]
    have hsq_i := congrArg (fun ψ => HomologicalComplex.homologyMap ψ i) hrel
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq_i
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) i) := inferInstance
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) i) := inferInstance
    exact (Work.Serre.SPC.isIso_iff_of_comm_square _ _ _ _ hsq_i).mpr hF
  · have hF : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF) (1 + φ))) := by
      rw [← hC]
      exact hcubeSurj
    rw [hD]
    have hsq_i := congrArg (fun ψ => HomologicalComplex.homologyMap ψ (1 + φ)) hrel
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq_i
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) (1 + φ)) := inferInstance
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) (1 + φ)) := inferInstance
    exact (Work.Serre.SPC.surjective_iff_of_comm_square _ _ _ _ hsq_i).mpr hF

end

end Work.Serre.SPC.One
