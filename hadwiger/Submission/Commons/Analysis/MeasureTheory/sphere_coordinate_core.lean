import Mathlib
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Commons.Analysis.MeasureTheory.cyl_coord_measure

noncomputable section

open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

private abbrev CylProd (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] := WithLp 2 (ℝ × W)
private abbrev SW (W : Type*) [NormedAddCommGroup W] := Metric.sphere (0 : W) 1
private abbrev Sph (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  Metric.sphere (0 : CylProd W) 1
private abbrev It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
private abbrev S0 (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] : Set (Sph W) :=
  {θ | (θ : CylProd W).ofLp.2 ≠ (0 : W)}

section Geometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

private def cylPt (t : ℝ) (ω : W) : CylProd W :=
  WithLp.toLp 2 (t, Real.sqrt (1 - t ^ 2) • ω)

lemma cylPt_fst (t : ℝ) (ω : W) : (cylPt t ω).ofLp.1 = t := by rfl
lemma cylPt_snd (t : ℝ) (ω : W) : (cylPt t ω).ofLp.2 = Real.sqrt (1 - t ^ 2) • ω := by rfl

lemma norm_sq_cylPt (t : ℝ) (ω : W) (ht : 0 ≤ 1 - t ^ 2) :
    ‖cylPt t ω‖ ^ 2 = t ^ 2 + (1 - t ^ 2) * ‖ω‖ ^ 2 := by
  unfold cylPt
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have hfst : (WithLp.toLp 2 (t, Real.sqrt (1 - t ^ 2) • ω)).fst = t := rfl
  have hsnd : (WithLp.toLp 2 (t, Real.sqrt (1 - t ^ 2) • ω)).snd = Real.sqrt (1 - t ^ 2) • ω := rfl
  rw [hfst, hsnd]
  simp only [norm_smul]
  have h1 : ‖t‖ ^ 2 = t ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖Real.sqrt (1 - t ^ 2)‖ ^ 2 = 1 - t ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (1 - t ^ 2)), Real.sq_sqrt ht]
  rw [h1, mul_pow, h2]

lemma cylPt_mem_sphere {t : ℝ} (ω : W) (ht : 1 - t ^ 2 ≥ 0) (hω : ‖ω‖ = 1) :
    cylPt t ω ∈ (Sph W : Set (CylProd W)) := by
  rw [mem_sphere_zero_iff_norm]
  have hsq : ‖cylPt t ω‖ ^ 2 = 1 := by
    rw [norm_sq_cylPt t ω ht, hω]
    ring
  have hx : ‖cylPt t ω‖ = 1 := by
    have h1 : ‖cylPt t ω‖ ^ 2 = 1 ^ 2 := by simpa using hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with hx | hx
    · exact hx
    · exfalso
      linarith [norm_nonneg (cylPt t ω)]
  simpa [hx]

private def latOf (θ : CylProd W) : ℝ := (θ.ofLp).1
private def dirOf (θ : CylProd W) : W := ‖(θ.ofLp).2‖⁻¹ • (θ.ofLp).2

lemma dirOf_norm_one (θ : CylProd W) (h : (θ.ofLp).2 ≠ (0 : W)) : ‖dirOf θ‖ = 1 := by
  unfold dirOf
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma norm_snd_eq_sqrt {θ : Sph W} (h : (θ : CylProd W).ofLp.2 ≠ (0 : W)) :
    ‖(θ : CylProd W).ofLp.2‖ = Real.sqrt (1 - ((θ : CylProd W).ofLp.1) ^ 2) := by
  have hsphere : ‖(θ : CylProd W)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
  have hx : ‖(θ : CylProd W)‖ ^ 2 =
      (θ : CylProd W).ofLp.1 ^ 2 + ‖(θ : CylProd W).ofLp.2‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    have hfst : (θ : CylProd W).fst = (θ : CylProd W).ofLp.1 := rfl
    have hsnd : (θ : CylProd W).snd = (θ : CylProd W).ofLp.2 := rfl
    rw [hfst, hsnd]
    simp [Real.norm_eq_abs, sq_abs]
  have hsnd' : ‖(θ : CylProd W).ofLp.2‖ ^ 2 = 1 - (θ : CylProd W).ofLp.1 ^ 2 := by
    rw [hsphere] at hx
    nlinarith
  have hwpos : 0 < ‖(θ : CylProd W).ofLp.2‖ := norm_pos_iff.mpr h
  have hpos : 0 < 1 - (θ : CylProd W).ofLp.1 ^ 2 := by nlinarith
  have hsq' : ‖(θ : CylProd W).ofLp.2‖ ^ 2 =
      Real.sqrt (1 - (θ : CylProd W).ofLp.1 ^ 2) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt hpos)]
    exact hsnd'
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq'

lemma latOf_mem {θ : Sph W} (h : (θ : CylProd W).ofLp.2 ≠ (0 : W)) :
    latOf (θ : CylProd W) ∈ Set.Ioo (-1) 1 := by
  have hsphere : ‖(θ : CylProd W)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
  have hx : ‖(θ : CylProd W)‖ ^ 2 = latOf (θ : CylProd W) ^ 2 + ‖(θ : CylProd W).ofLp.2‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    have hfst : (θ : CylProd W).fst = latOf (θ : CylProd W) := rfl
    have hsnd : (θ : CylProd W).snd = (θ : CylProd W).ofLp.2 := rfl
    rw [hfst, hsnd]
    simp [Real.norm_eq_abs, sq_abs]
  have hwpos : 0 < ‖(θ : CylProd W).ofLp.2‖ := norm_pos_iff.mpr h
  have hpos : 0 < 1 - latOf (θ : CylProd W) ^ 2 := by
    rw [hsphere] at hx
    nlinarith
  constructor <;> nlinarith

lemma latOf_cylPt (t : ℝ) (ω : W) : latOf (cylPt t ω) = t := by
  simp [latOf, cylPt]

lemma dirOf_cylPt {t : ℝ} {ω : W} (ht : t ∈ Set.Ioo (-1) 1) (hω : ‖ω‖ = 1) :
    dirOf (cylPt t ω) = ω := by
  unfold dirOf
  rw [cylPt_snd t ω]
  have hsqrt : Real.sqrt (1 - t ^ 2) ≠ 0 := by
    rw [Real.sqrt_ne_zero (by nlinarith [sq_nonneg t, ht.1, ht.2])]
    nlinarith [ht.1, ht.2, sq_nonneg t]
  have hws : ‖Real.sqrt (1 - t ^ 2) • ω‖ = Real.sqrt (1 - t ^ 2) := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg (1 - t ^ 2))]
    rw [hω]
    rw [mul_one]
  rw [hws]
  exact inv_smul_smul₀ hsqrt ω

lemma cylPt_of_lat_dir {θ : Sph W} (h : (θ : CylProd W).ofLp.2 ≠ (0 : W)) :
    cylPt (latOf (θ : CylProd W)) (dirOf (θ : CylProd W)) = (θ : CylProd W) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change Real.sqrt (1 - (θ : CylProd W).ofLp.1 ^ 2) •
        (‖(θ : CylProd W).ofLp.2‖⁻¹ • (θ : CylProd W).ofLp.2) = (θ : CylProd W).ofLp.2
    have hnorm : ‖(θ : CylProd W).ofLp.2‖ = Real.sqrt (1 - (θ : CylProd W).ofLp.1 ^ 2) :=
      norm_snd_eq_sqrt h
    rw [hnorm]
    have hmem : latOf (θ : CylProd W) ∈ Set.Ioo (-1) 1 := latOf_mem h
    have hsqrt : Real.sqrt (1 - (θ : CylProd W).ofLp.1 ^ 2) ≠ 0 := by
      have hx : (θ : CylProd W).ofLp.1 = latOf (θ : CylProd W) := by rfl
      rw [hx]
      rw [Real.sqrt_ne_zero (by nlinarith [sq_nonneg (latOf (θ : CylProd W)), hmem.1, hmem.2])]
      nlinarith [hmem.1, hmem.2, sq_nonneg (latOf (θ : CylProd W))]
    rw [← smul_assoc]
    rw [smul_eq_mul]
    rw [mul_inv_cancel₀ hsqrt]
    simp

private def cylSphere (q : It × SW W) : Sph W :=
  ⟨cylPt q.1.1 q.2.1, by
    refine cylPt_mem_sphere q.2.1 ?_ (mem_sphere_zero_iff_norm.mp q.2.2)
    nlinarith [q.1.2.1, q.1.2.2, sq_nonneg q.1.1]⟩

@[simp] lemma cylSphere_val (q : It × SW W) : ((cylSphere q : Sph W) : CylProd W) = cylPt q.1.1 q.2.1 := by
  rfl

lemma cylSphere_mem_S0 (q : It × SW W) : (cylSphere q : Sph W) ∈ S0 W := by
  change (cylPt q.1.1 q.2.1).ofLp.2 ≠ (0 : W)
  rw [cylPt_snd]
  intro hz
  have hs : Real.sqrt (1 - q.1.1 ^ 2) ≠ 0 := by
    rw [Real.sqrt_ne_zero (by nlinarith [sq_nonneg q.1.1, q.1.2.1, q.1.2.2])]
    nlinarith [q.1.2.1, q.1.2.2, sq_nonneg q.1.1]
  have hw : q.2.1 = 0 := by
    have : Real.sqrt (1 - q.1.1 ^ 2) = 0 ∨ q.2.1 = 0 := smul_eq_zero.mp hz
    rcases this with hsqrt | hw
    · exact (hs hsqrt).elim
    · exact hw
  have hw1 : ‖q.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.2.2
  have : ‖(0 : W)‖ = 1 := by simpa [hw] using hw1
  simpa using this

private def sphCyl (θ : {θ : Sph W // θ ∈ S0 W}) : It × SW W :=
  let x : CylProd W := (θ : Sph W)
  let hx : x.ofLp.2 ≠ (0 : W) := θ.2
  let hmem : x.ofLp.1 ∈ Set.Ioo (-1) 1 := by
    change latOf x ∈ Set.Ioo (-1) 1
    exact latOf_mem hx
  (⟨x.ofLp.1, hmem⟩, ⟨dirOf x, by
    rw [mem_sphere_zero_iff_norm]
    exact dirOf_norm_one x hx⟩)

lemma sphCyl_left_inv (q : It × SW W) : sphCyl ⟨cylSphere q, cylSphere_mem_S0 q⟩ = q := by
  have hmem : q.1.1 ∈ Set.Ioo (-1) 1 := q.1.2
  have hw1 : ‖q.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp q.2.2
  apply Prod.ext
  · apply Subtype.ext
    change latOf (cylPt q.1.1 q.2.1) = q.1.1
    exact latOf_cylPt q.1.1 q.2.1
  · apply Subtype.ext
    change dirOf (cylPt q.1.1 q.2.1) = q.2.1
    exact dirOf_cylPt (t := q.1.1) (ω := q.2.1) hmem hw1

lemma sphCyl_right_inv (θ : {θ : Sph W // θ ∈ S0 W}) :
    cylSphere (sphCyl θ) = θ.1 := by
  apply Subtype.ext
  change cylPt (latOf (θ : CylProd W)) (dirOf (θ : CylProd W)) = (θ : Sph W)
  exact cylPt_of_lat_dir (θ := (θ : Sph W)) (θ : {θ : Sph W // θ ∈ S0 W}).2


end Geometry

section MeasEquiv

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

lemma s0_measurable : MeasurableSet (S0 W) := by
  unfold S0
  have hcont : Continuous fun θ : Sph W => ((θ : CylProd W).ofLp.2 : W) := by
    fun_prop
  exact hcont.measurable (isOpen_ne.measurableSet : MeasurableSet ({w : W | w ≠ (0 : W)}))

private def eFun (q : It × SW W) : {θ : Sph W // θ ∈ S0 W} :=
  ⟨cylSphere q, cylSphere_mem_S0 q⟩

private def eInv (θ : {θ : Sph W // θ ∈ S0 W}) : It × SW W := sphCyl θ

lemma eFun_left_inv (q : It × SW W) : eInv (eFun q) = q := by
  exact sphCyl_left_inv q

lemma eFun_right_inv (θ : {θ : Sph W // θ ∈ S0 W}) : eFun (eInv θ) = θ := by
  apply Subtype.ext
  exact sphCyl_right_inv θ

lemma measurable_cylE : Measurable (fun q : It × SW W => cylPt q.1.1 q.2.1) := by
  let hcoord : It × SW W → ℝ × W := fun q => (q.1.1, (q.2.1 : W))
  have hcoord_meas : Measurable hcoord := by
    exact Measurable.prod (measurable_subtype_coe.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)
  let hmap : ℝ × W → ℝ × W := fun p => (p.1, Real.sqrt (1 - p.1 ^ 2) • p.2)
  have hmap_cont : Continuous hmap := by fun_prop
  let htoFun : ℝ × W → CylProd W := WithLp.toLp 2
  have hto : Continuous htoFun :=
    (WithLp.homeomorphProd 2 ℝ W).symm.continuous
  have hfun : (fun q : It × SW W => cylPt q.1.1 q.2.1)
      = htoFun ∘ hmap ∘ hcoord := by
    funext q
    rfl
  rw [hfun]
  exact (hto.measurable.comp hmap_cont.measurable).comp hcoord_meas

lemma measurable_eFun : Measurable (eFun : It × SW W → {θ : Sph W // θ ∈ S0 W}) := by
  have h : Measurable (fun q : It × SW W => (cylSphere q : CylProd W)) := by
    simpa [cylSphere] using measurable_cylE
  have h1 : Measurable (fun q : It × SW W => (cylSphere q : Sph W)) := Measurable.subtype_mk h
  exact Measurable.subtype_mk h1

private def latTotal (x : CylProd W) : ℝ := x.ofLp.1
private def dirTotal (x : CylProd W) : W := ‖x.ofLp.2‖⁻¹ • x.ofLp.2

lemma measurable_latTotal : Measurable (latTotal : CylProd W → ℝ) := by
  unfold latTotal
  fun_prop

lemma measurable_dirTotal : Measurable (dirTotal : CylProd W → W) := by
  classical
  unfold dirTotal
  have hinv : Measurable (fun c : ℝ => c⁻¹) := by
    exact ContinuousOn.measurable_of_countable_compl (s := ({0}ᶜ : Set ℝ))
      (continuousOn_inv₀ : ContinuousOn (fun c : ℝ => c⁻¹) ({0}ᶜ : Set ℝ)) (by simp)
  have hnorm : Measurable (fun x : CylProd W => ‖x.ofLp.2‖) := by fun_prop
  have hsnd : Measurable (fun x : CylProd W => (x.ofLp.2 : W)) := by fun_prop
  have hmap : Measurable (fun x : CylProd W => (‖x.ofLp.2‖⁻¹, x.ofLp.2) : CylProd W → ℝ × W) := by
    exact Measurable.prod (hinv.comp hnorm) hsnd
  have hsmul : Continuous (fun p : ℝ × W => p.1 • p.2) := by fun_prop
  have hfun : (fun x : CylProd W => ‖x.ofLp.2‖⁻¹ • x.ofLp.2) =
      (fun p : ℝ × W => p.1 • p.2) ∘ (fun x : CylProd W => (‖x.ofLp.2‖⁻¹, x.ofLp.2)) := by
    funext x
    rfl
  rw [hfun]
  exact hsmul.measurable.comp hmap

private def sphVal (θ : {θ : Sph W // θ ∈ S0 W}) : CylProd W := ((θ : Sph W) : CylProd W)

private def invItComp (θ : {θ : Sph W // θ ∈ S0 W}) : It :=
  ⟨latTotal (sphVal θ), by
    change latOf (sphVal θ) ∈ Set.Ioo (-1) 1
    exact latOf_mem θ.2⟩

private def invSWComp (θ : {θ : Sph W // θ ∈ S0 W}) : SW W :=
  ⟨dirTotal (sphVal θ), by
    rw [mem_sphere_zero_iff_norm]
    exact dirOf_norm_one (sphVal θ) θ.2⟩

private def eInv' (θ : {θ : Sph W // θ ∈ S0 W}) : It × SW W := (invItComp θ, invSWComp θ)

lemma eInv_eq_eInv' (θ : {θ : Sph W // θ ∈ S0 W}) : eInv θ = eInv' θ := by
  apply Prod.ext
  · apply Subtype.ext
    dsimp [eInv', invItComp, sphVal, sphCyl, latTotal, latOf]
    rfl
  · apply Subtype.ext
    dsimp [eInv', invSWComp, sphVal, sphCyl, dirTotal, dirOf]
    rfl

lemma measurable_sphVal : Measurable (sphVal : {θ : Sph W // θ ∈ S0 W} → CylProd W) := by
  change Measurable ((Subtype.val : Sph W → CylProd W) ∘
    (Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W))
  exact (measurable_subtype_coe : Measurable (Subtype.val : Sph W → CylProd W)).comp
    (measurable_subtype_coe : Measurable (Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W))

lemma measurable_invItComp : Measurable (invItComp : {θ : Sph W // θ ∈ S0 W} → It) := by
  have hlat : Measurable (fun θ : {θ : Sph W // θ ∈ S0 W} => latTotal (sphVal θ)) :=
    measurable_latTotal.comp measurable_sphVal
  have hmem : ∀ θ : {θ : Sph W // θ ∈ S0 W},
      latTotal (sphVal θ) ∈ Set.Ioo (-1) 1 := by
    intro θ
    change latOf (sphVal θ) ∈ Set.Ioo (-1) 1
    exact latOf_mem θ.2
  change Measurable (fun θ : {θ : Sph W // θ ∈ S0 W} => (⟨latTotal (sphVal θ), hmem θ⟩ : It))
  exact Measurable.subtype_mk hlat

lemma measurable_invSWComp : Measurable (invSWComp : {θ : Sph W // θ ∈ S0 W} → SW W) := by
  have hdir : Measurable (fun θ : {θ : Sph W // θ ∈ S0 W} => dirTotal (sphVal θ)) :=
    measurable_dirTotal.comp measurable_sphVal
  have hmem : ∀ θ : {θ : Sph W // θ ∈ S0 W}, dirTotal (sphVal θ) ∈ (SW W : Set W) := by
    intro θ
    rw [mem_sphere_zero_iff_norm]
    exact dirOf_norm_one (sphVal θ) θ.2
  change Measurable (fun θ : {θ : Sph W // θ ∈ S0 W} => (⟨dirTotal (sphVal θ), hmem θ⟩ : SW W))
  exact Measurable.subtype_mk hdir

lemma measurable_eInv : Measurable (eInv : {θ : Sph W // θ ∈ S0 W} → It × SW W) := by
  have h : Measurable (eInv' : {θ : Sph W // θ ∈ S0 W} → It × SW W) := by
    unfold eInv'
    exact Measurable.prod measurable_invItComp measurable_invSWComp
  have hfun : (eInv : {θ : Sph W // θ ∈ S0 W} → It × SW W) =
      (eInv' : {θ : Sph W // θ ∈ S0 W} → It × SW W) := by
    funext θ
    exact eInv_eq_eInv' θ
  simpa [hfun] using h

/-- The measurable equivalence between the cylinder and the sphere minus poles. -/
private def cylinderEquiv : (It × SW W) ≃ᵐ {θ : Sph W // θ ∈ S0 W} where
  toFun := eFun
  invFun := eInv
  left_inv := eFun_left_inv
  right_inv := eFun_right_inv
  measurable_toFun := measurable_eFun
  measurable_invFun := measurable_eInv

lemma cylinderEquiv_first_coord (q : It × SW W) :
    ((((cylinderEquiv q : {θ : Sph W // θ ∈ S0 W}) : Sph W) : CylProd W).ofLp.1) = q.1.1 := by
  change (cylPt q.1.1 q.2.1).ofLp.1 = q.1.1
  exact cylPt_fst q.1.1 q.2.1

end MeasEquiv



section CylinderMeasure

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

-- measures in the shape used by the final statement
private def cylMuE : MeasureTheory.Measure (It × SW W) :=
  ((((MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
    (fun t => ENNReal.ofReal ((1 - t ^ 2) ^ (((Module.finrank ℝ W : ℝ) - 2) / 2)))).comap
      (Subtype.val : It → ℝ)).prod ((MeasureTheory.volume : MeasureTheory.Measure W).toSphere))

private def muFull : MeasureTheory.Measure ((It × SW W) × Set.Ioi (0 : ℝ)) :=
  (cylMuE.prod (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ W)))

/-- the surface measure on the unit sphere of `CylProd W`. -/
private abbrev sphMeasure : MeasureTheory.Measure (Sph W) :=
  (MeasureTheory.volume : MeasureTheory.Measure (CylProd W)).toSphere

/-- the point of the sphere corresponding to `(t, ω)`. -/
private def eSphere (q : It × SW W) : Sph W := cylSphere q

private lemma measurable_eSphere :
    Measurable (eSphere : It × SW W → Sph W) :=
  measurable_subtype_coe.comp measurable_eFun

private lemma eSphere_val (q : It × SW W) :
    ((eSphere q : Sph W) : CylProd W) = cylPt q.1.1 q.2.1 := rfl

private lemma eSphere_mem_S0 (q : It × SW W) : eSphere q ∈ S0 W := cylSphere_mem_S0 q

private def cylLambda : (It × SW W) × Set.Ioi (0 : ℝ) → CylProd W := fun q =>
  WithLp.toLp 2 (((q.2 : Set.Ioi (0 : ℝ)).1) * (q.1.1 : It).1,
    (((q.2 : Set.Ioi (0 : ℝ)).1) * Real.sqrt (1 - ((q.1.1 : It).1) ^ 2)) • ((q.1.2 : SW W) : W))

/-- the pair-coordinate version of the cylindrical map. -/
private lemma finrank_CylProd : Module.finrank ℝ (CylProd W) = Module.finrank ℝ W + 1 := by
  have h1 : Module.finrank ℝ (CylProd W) = Module.finrank ℝ (ℝ × W) :=
    (WithLp.linearEquiv 2 ℝ (ℝ × W)).finrank_eq
  rw [h1, Module.finrank_prod, Module.finrank_self]
  omega

private lemma volumeIoiPow_lt_one :
    (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ W))
      (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))) =
        ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1)) := by
  have h := MeasureTheory.Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ W)
    (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))
  simpa [one_div] using h

private lemma volumeIoiPow_setOf_lt_one :
    (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ W))
      ({s : Set.Ioi (0 : ℝ) | s.1 < 1}) =
        ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1)) := by
  rw [show ({s : Set.Ioi (0 : ℝ) | s.1 < 1}) = Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)) from rfl]
  exact volumeIoiPow_lt_one

-- the canonical projection of a nonzero vector to the unit sphere (junk at 0)
private def sphProj : CylProd W → CylProd W :=
  ({0} : Set (CylProd W)).piecewise (fun _ => 0) (fun x => ‖x‖⁻¹ • x)

private lemma measurable_sphProj : Measurable (sphProj : CylProd W → CylProd W) := by
  classical
  unfold sphProj
  refine ContinuousOn.measurable_piecewise ?_ ?_ (measurableSet_singleton 0)
  · exact continuousOn_const
  · intro x hx
    have hxne : x ≠ 0 := by simpa using hx
    have hc1 : ContinuousAt (fun y : CylProd W => ‖y‖) x := by fun_prop
    have hc2 : ContinuousAt (fun y : CylProd W => (‖y‖ : ℝ)⁻¹) x :=
      hc1.inv₀ (norm_ne_zero_iff.mpr hxne)
    have hc3 : ContinuousAt (fun y : CylProd W => y) x := continuousAt_id
    exact (hc2.smul hc3).continuousWithinAt

private def cylLambdaPair : (It × SW W) × Set.Ioi (0 : ℝ) → ℝ × W := fun q =>
  ((q.2 : Set.Ioi (0 : ℝ)).1 * (q.1.1 : It).1,
    (((q.2 : Set.Ioi (0 : ℝ)).1 * Real.sqrt (1 - ((q.1.1 : It).1) ^ 2)) • ((q.1.2 : SW W) : W)))

private lemma cylLambda_eq_comp :
    cylLambda = (WithLp.toLp 2 : ℝ × W → CylProd W) ∘ cylLambdaPair := by
  funext q
  rfl

private lemma measurable_cylLambdaPair :
    Measurable (cylLambdaPair : (It × SW W) × Set.Ioi (0 : ℝ) → ℝ × W) := by
  unfold cylLambdaPair
  apply Measurable.prod
  · -- first coordinate s * t
    have hs : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) =>
        (q.2 : Set.Ioi (0 : ℝ)).1) :=
      measurable_subtype_coe.comp measurable_snd
    have ht : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) => (q.1.1 : It).1) :=
      measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
    exact hs.mul ht
  · -- second coordinate
    have hs : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) =>
        (q.2 : Set.Ioi (0 : ℝ)).1) :=
      measurable_subtype_coe.comp measurable_snd
    have ht : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) => (q.1.1 : It).1) :=
      measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
    have hw : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) => ((q.1.2 : SW W) : W)) :=
      measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)
    have hsqrt : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) =>
        Real.sqrt (1 - (q.1.1 : It).1 ^ 2)) := by
      exact Real.continuous_sqrt.measurable.comp (by fun_prop)
    have hsc : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) =>
        (q.2 : Set.Ioi (0 : ℝ)).1 * Real.sqrt (1 - (q.1.1 : It).1 ^ 2)) := hs.mul hsqrt
    -- multiply scalar with vector
    have hsm : Continuous (fun p : ℝ × W => p.1 • p.2) := continuous_smul
    have hpair : Measurable (fun q : (It × SW W) × Set.Ioi (0 : ℝ) =>
        ((q.2 : Set.Ioi (0 : ℝ)).1 * Real.sqrt (1 - (q.1.1 : It).1 ^ 2), ((q.1.2 : SW W) : W))) :=
      Measurable.prod hsc hw
    have hcomp := hsm.measurable.comp hpair
    change Measurable (fun a : (It × SW W) × Set.Ioi (0 : ℝ) =>
      ((a.2 : Set.Ioi (0 : ℝ)).1 * Real.sqrt (1 - (a.1.1 : It).1 ^ 2)) • ((a.1.2 : SW W) : W))
    exact hcomp

private lemma measurable_cylLambda :
    Measurable (cylLambda : (It × SW W) × Set.Ioi (0 : ℝ) → CylProd W) := by
  rw [cylLambda_eq_comp]
  exact (((WithLp.homeomorphProd 2 ℝ W).symm.continuous.measurable :
    Measurable (WithLp.toLp 2 : ℝ × W → CylProd W))).comp measurable_cylLambdaPair

/-- central analytic input: cylindrical coordinates transform volume.
(Proved in the commons; see `Commons.Analysis.MeasureTheory.cyl_coord_measure`.) -/
private lemma cylCoordMeasure :
    MeasureTheory.Measure.map (cylLambda : (It × SW W) × Set.Ioi (0 : ℝ) → CylProd W) muFull =
      MeasureTheory.volume.restrict {x : CylProd W | x.ofLp.2 ≠ (0 : W)} := by
  exact cyl_coord_measure (W := W)

private lemma val_image_measurable {A : Set (Sph W)} (hA : MeasurableSet A) :
    MeasurableSet ((Subtype.val : Sph W → CylProd W) '' A) := by
  have hSmeas : MeasurableSet (Sph W : Set (CylProd W)) := isClosed_sphere.measurableSet
  exact (MeasurableEmbedding.subtype_coe hSmeas).measurableSet_image' hA

private lemma cone_subset_offaxis {A : Set (Sph W)} (hAsub : A ⊆ S0 W) :
    Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A) ⊆
      {x : CylProd W | x.ofLp.2 ≠ (0 : W)} := by
  rintro x ⟨r, hr, y, ⟨θ, hθA, rfl⟩, rfl⟩
  have hθ : ((θ : CylProd W).ofLp.2 : W) ≠ 0 := hAsub hθA
  show (r • (θ : CylProd W)).ofLp.2 ≠ (0 : W)
  rw [show (r • (θ : CylProd W)).ofLp.2 = r • ((θ : CylProd W).ofLp.2) from rfl]
  exact smul_ne_zero (ne_of_gt hr.1) hθ

private lemma cone_smul_val (q : It × SW W) (s : Set.Ioi (0 : ℝ)) :
    cylLambda (q, s) = s.1 • ((eSphere q : Sph W) : CylProd W) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · change ((s.1 * Real.sqrt (1 - q.1.1 ^ 2)) • ((q.2.1 : W))) =
      (s.1 • (Real.sqrt (1 - q.1.1 ^ 2) • ((q.2.1 : W))))
    rw [← smul_assoc, smul_eq_mul]

private lemma cylLambda_mem_cone_iff (A : Set (Sph W)) (q : It × SW W) (s : Set.Ioi (0 : ℝ)) :
    cylLambda (q, s) ∈ Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A) ↔
      s.1 < 1 ∧ eSphere q ∈ A := by
  constructor
  · intro h
    rw [Set.mem_smul] at h
    obtain ⟨r, hr, y, ⟨θ, hθA, rfl⟩, hEq⟩ := h
    rw [cone_smul_val q s] at hEq
    have hnorm1 : ‖s.1 • ((eSphere q : Sph W) : CylProd W)‖ = s.1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt s.2),
        mem_sphere_zero_iff_norm.mp (eSphere q).2, mul_one]
    have hnorm2 : ‖r • ((θ : CylProd W))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr.1),
        mem_sphere_zero_iff_norm.mp θ.2, mul_one]
    have hrs : r = s.1 := by rw [← hnorm2, hEq, hnorm1]
    have hθeq : θ = eSphere q := by
      apply Subtype.ext
      have hthis := hEq
      rw [hrs] at hthis
      have h2 : s.1 ≠ 0 := ne_of_gt s.2
      have := congrArg (fun z : CylProd W => s.1⁻¹ • z) hthis
      simpa [smul_smul, h2] using this
    exact ⟨by rw [← hrs]; exact hr.2, by rw [← hθeq]; exact hθA⟩
  · rintro ⟨hs1, hqA⟩
    rw [Set.mem_smul]
    exact ⟨s.1, ⟨s.2, hs1⟩, ((eSphere q : Sph W) : CylProd W), ⟨eSphere q, hqA, rfl⟩,
      (cone_smul_val q s).symm⟩

private lemma cylLambda_preimage_cone (A : Set (Sph W)) :
    cylLambda ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A)) =
      (eSphere ⁻¹' A) ×ˢ {s : Set.Ioi (0 : ℝ) | s.1 < 1} := by
  ext p
  obtain ⟨q, s⟩ := p
  rw [Set.mem_preimage, Set.mem_prod, Set.mem_preimage, Set.mem_setOf_eq, and_comm]
  exact cylLambda_mem_cone_iff A q s

private lemma cone_measurable {A : Set (Sph W)} (hA : MeasurableSet A) :
    MeasurableSet (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A)) := by
  have hvalA : MeasurableSet ((Subtype.val : Sph W → CylProd W) '' A) := val_image_measurable hA
  have hpre : MeasurableSet (sphProj ⁻¹' ((Subtype.val : Sph W → CylProd W) '' A)) :=
    measurable_sphProj hvalA
  have hball : MeasurableSet {x : CylProd W | ‖x‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hne : MeasurableSet ({0} : Set (CylProd W))ᶜ := (measurableSet_singleton 0).compl
  have hset : Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A) =
      ({x : CylProd W | ‖x‖ < 1} ∩ ({0} : Set (CylProd W))ᶜ) ∩
        (sphProj ⁻¹' ((Subtype.val : Sph W → CylProd W) '' A)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
      have hθn : ‖(θ : CylProd W)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
      have hrne : r ≠ 0 := ne_of_gt hr.1
      have hθne : (θ : CylProd W) ≠ 0 := by
        intro h0
        rw [h0] at hθn
        norm_num at hθn
      have hxne : r • (θ : CylProd W) ≠ 0 := smul_ne_zero hrne hθne
      have hnorm : ‖r • (θ : CylProd W)‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hθn, mul_one]
      have hproj : sphProj (r • (θ : CylProd W)) = (θ : CylProd W) := by
        unfold sphProj
        rw [Set.piecewise_eq_of_notMem (s := ({0} : Set (CylProd W)))
          (f := fun _ : CylProd W => (0 : CylProd W)) (g := fun y : CylProd W => ‖y‖⁻¹ • y)
          (i := r • (θ : CylProd W)) (by simpa using hxne)]
        rw [hnorm, inv_smul_smul₀ hrne]
      refine ⟨⟨?_, by simpa using hxne⟩, ?_⟩
      · change ‖r • (θ : CylProd W)‖ < 1
        rw [hnorm]
        exact hr.2
      · change sphProj (r • (θ : CylProd W)) ∈
          (Subtype.val : Sph W → CylProd W) '' A
        rw [hproj]
        exact ⟨θ, hθ, rfl⟩
    · rintro ⟨⟨hball, hne0⟩, hproj⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne0
      obtain ⟨θ, hθ, hθeq⟩ := hproj
      rw [Set.mem_smul]
      have hxne : x ≠ 0 := hne0
      have hprojval : sphProj x = ‖x‖⁻¹ • x := by
        unfold sphProj
        rw [Set.piecewise_eq_of_notMem (s := ({0} : Set (CylProd W)))
          (f := fun _ : CylProd W => (0 : CylProd W)) (g := fun y : CylProd W => ‖y‖⁻¹ • y)
          (i := x) (by simpa using hxne)]
      rw [hprojval] at hθeq
      refine ⟨‖x‖, ⟨norm_pos_iff.mpr hxne, hball⟩, (θ : CylProd W), ⟨θ, hθ, rfl⟩, ?_⟩
      rw [hθeq]
      exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hxne) x
  rw [hset]
  exact (hball.inter hne).inter hpre

private lemma cone_volume {A : Set (Sph W)} (hA : MeasurableSet A) (hAsub : A ⊆ S0 W) :
    (MeasureTheory.volume : MeasureTheory.Measure (CylProd W))
        (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A)) =
      cylMuE (W := W) (eSphere ⁻¹' A) *
        ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1)) := by
  set cone := Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A)
  have hconemeas : MeasurableSet cone := cone_measurable hA
  have hconesub : cone ⊆ {x : CylProd W | x.ofLp.2 ≠ (0 : W)} := cone_subset_offaxis hAsub
  have h1 : (MeasureTheory.volume : MeasureTheory.Measure (CylProd W)) cone =
      (MeasureTheory.Measure.map (cylLambda : (It × SW W) × Set.Ioi (0 : ℝ) → CylProd W)
        muFull) cone := by
    rw [cylCoordMeasure]
    rw [MeasureTheory.Measure.restrict_apply hconemeas, Set.inter_eq_left.mpr hconesub]
  have h2 : (MeasureTheory.Measure.map (cylLambda : (It × SW W) × Set.Ioi (0 : ℝ) → CylProd W)
      muFull) cone = muFull (cylLambda ⁻¹' cone) :=
    MeasureTheory.Measure.map_apply measurable_cylLambda hconemeas
  rw [h1, h2]
  rw [cylLambda_preimage_cone A]
  rw [muFull, MeasureTheory.Measure.prod_prod]
  rw [volumeIoiPow_setOf_lt_one]

private lemma sphereCoordSlice_sphere (A : Set (Sph W)) (hA : MeasurableSet A) (hAsub : A ⊆ S0 W) :
    sphMeasure (W := W) A = cylMuE (W := W) (eSphere ⁻¹' A) := by
  have hto : sphMeasure (W := W) A =
      (↑(Module.finrank ℝ (CylProd W)) : ℝ≥0∞) *
        (MeasureTheory.volume : MeasureTheory.Measure (CylProd W))
          (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : Sph W → CylProd W) '' A)) := by
    show (MeasureTheory.volume : MeasureTheory.Measure (CylProd W)).toSphere A = _
    exact Measure.toSphere_apply' (μ := (MeasureTheory.volume : MeasureTheory.Measure (CylProd W))) hA
  rw [hto, cone_volume hA hAsub, finrank_CylProd]
  have hcomp : (↑(Module.finrank ℝ W + 1) : ℝ≥0∞) *
      ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1)) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    have hreal : ((Module.finrank ℝ W + 1 : ℕ) : ℝ) * (1 / ((Module.finrank ℝ W : ℝ) + 1)) = 1 := by
      push_cast
      field_simp
    rw [hreal]
    simp
  calc (↑(Module.finrank ℝ W + 1) : ℝ≥0∞) *
        (cylMuE (W := W) (eSphere ⁻¹' A) * ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1)))
      = ((↑(Module.finrank ℝ W + 1) : ℝ≥0∞) *
          ENNReal.ofReal (1 / ((Module.finrank ℝ W : ℝ) + 1))) * cylMuE (W := W) (eSphere ⁻¹' A) := by
            rw [mul_comm (cylMuE (W := W) (eSphere ⁻¹' A)) _, mul_assoc]
    _ = 1 * cylMuE (W := W) (eSphere ⁻¹' A) := by rw [hcomp]
    _ = cylMuE (W := W) (eSphere ⁻¹' A) := one_mul _

end CylinderMeasure


section FinalAssembly

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]

private lemma eFun_val (q : It × SW W) :
    ((eFun q : {θ : Sph W // θ ∈ S0 W}) : Sph W) = eSphere q := rfl

private lemma eFun_preimage (C : Set {θ : Sph W // θ ∈ S0 W}) :
    (eFun ⁻¹' C) = (eSphere ⁻¹' ((Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W) '' C)) := by
  ext q
  rw [Set.mem_preimage, Set.mem_preimage]
  constructor
  · intro hq
    exact ⟨eFun q, hq, rfl⟩
  · rintro ⟨θ, hθC, hθq⟩
    have heq : eFun q = θ := by
      apply Subtype.ext
      rw [eFun_val q]
      exact hθq.symm
    rwa [heq]

lemma sphere_coordinate_core_aux :
    MeasureTheory.Measure.map (cylinderEquiv : (It × SW W) → {θ : Sph W // θ ∈ S0 W})
        (cylMuE (W := W)) =
      (sphMeasure (W := W)).comap
        (Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W) := by
  apply MeasureTheory.Measure.ext
  intro C hC
  change (MeasureTheory.Measure.map (eFun : It × SW W → {θ : Sph W // θ ∈ S0 W})
      (cylMuE (W := W))) C =
    (MeasureTheory.Measure.comap (Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W)
      (sphMeasure (W := W))) C
  rw [MeasureTheory.Measure.map_apply measurable_eFun hC]
  rw [comap_subtype_coe_apply s0_measurable]
  rw [eFun_preimage C]
  have himg : MeasurableSet ((Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W) '' C) := by
    exact (MeasurableEmbedding.subtype_coe s0_measurable).measurableSet_image' hC
  have hsub : ((Subtype.val : {θ : Sph W // θ ∈ S0 W} → Sph W) '' C) ⊆ S0 W := by
    rintro θ ⟨θ₀, hθ₀, rfl⟩
    exact θ₀.2
  rw [← sphereCoordSlice_sphere _ himg hsub]

end FinalAssembly


/-- The core cylindrical-coordinate decomposition of the spherical surface
measure on the unit sphere of `WithLp 2 (ℝ × W)` (Hadwiger §31 development):
the open sphere minus its two poles is measurably equivalent to
`(Ioo (-1) 1) × S_W` carrying the cylindrical product measure, by the
coordinate map `(t, ω) ↦ (t, √(1-t²) ω)`. -/
lemma sphere_coordinate_core
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    let E := WithLp 2 (ℝ × W)
    let S := Metric.sphere (0 : E) 1
    let SW := Metric.sphere (0 : W) 1
    let expo : ℝ := (((Module.finrank ℝ W : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let tau : MeasureTheory.Measure ℝ :=
      (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal (rho t))
    let cylμ : MeasureTheory.Measure (It × SW) :=
      (tau.comap (Subtype.val : It → ℝ)).prod (MeasureTheory.volume.toSphere)
    let S0 : Set S := {θ | ((θ : E).ofLp.2 : W) ≠ 0}
    let μS0 : MeasureTheory.Measure {θ : S // θ ∈ S0} :=
      (MeasureTheory.volume.toSphere : MeasureTheory.Measure S).comap
        (Subtype.val : {θ : S // θ ∈ S0} → S)
    ∃ e : (It × SW) ≃ᵐ {θ : S // θ ∈ S0},
      MeasureTheory.Measure.map (⇑e) cylμ = μS0 ∧
      (∀ q : It × SW, ((((e q : {θ : S // θ ∈ S0}) : S) : E).ofLp.1) = q.1.1) := by
  refine ⟨cylinderEquiv (W := W), ?_, ?_⟩
  · exact sphere_coordinate_core_aux (W := W)
  · intro q
    exact cylinderEquiv_first_coord q

end Commons.Analysis.MeasureTheory
