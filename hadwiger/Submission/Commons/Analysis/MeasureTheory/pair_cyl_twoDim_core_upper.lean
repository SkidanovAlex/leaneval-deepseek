import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.RingTheory.Finiteness.Prod

set_option maxHeartbeats 1000000

open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

noncomputable section

namespace Commons.Analysis.MeasureTheory

/-! ## The two-dimensional change of variables `(t,s) ↦ (s·t, s·√(1−t²))`

We prove the measure-level identity requested in
`Commons.Analysis.MeasureTheory.pair_cyl_twoDim_core_upper`.
The proof goes through Mathlib's Jacobian change-of-variables theorem
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` for the smooth map
`F (t,s) = (s·t, s·√(1−t²))` on the strip `U = (-1,1) × (0,∞)`
(`det F' = s/√(1−t²)`), together with the elementary `rpow` identity
`(1−t²)^((d−2)/2) · s^d = (s/√(1−t²)) · (s√(1−t²))^(d−1)` on `U`,
and the fact that `F` maps `U` bijectively onto the upper half plane `V`. -/

/-- The strip `(-1,1) × (0,∞)`. -/
private abbrev twoDimU : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Ioo (-1) 1 ∧ 0 < p.2}

/-- The upper half plane. -/
private abbrev twoDimV : Set (ℝ × ℝ) := {p | 0 < p.2}

/-- The two-dimensional map `F (t,s) = (s t, s √(1-t²))`. -/
private abbrev twoDimF (p : ℝ × ℝ) : ℝ × ℝ := (p.2 * p.1, p.2 * Real.sqrt (1 - p.1 ^ 2))

private abbrev twoDimDensL (d : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2) * p.2 ^ d)

private abbrev twoDimDensR (d : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (p.2 ^ (d - 1))

/-! ### A general pushforward lemma for densities -/

/-- Pushing a measure with density `g ∘ f` forward along a measurable `f` amounts to
multiplying by `g` after pushing `μ` forward. -/
private lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) {g : β → ℝ≥0∞} (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) = (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, MeasureTheory.withDensity_apply _ (hf hs),
    MeasureTheory.withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
  simp only [Function.comp_apply]

/-! ### Elementary facts about the strip -/

private lemma twoDimU_pos {t : ℝ} (hlo : -1 < t) (hhi : t < 1) : 0 < 1 - t ^ 2 := by
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 + t := by linarith
  nlinarith [mul_pos h1 h2]

private lemma twoDimU_measurable : MeasurableSet twoDimU := by
  have h : twoDimU = (Prod.fst ⁻¹' Set.Ioo (-1) 1) ∩ (Prod.snd ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext p; simp [twoDimU, Set.mem_Ioo, Set.mem_Ioi, and_comm]
  rw [h]
  exact (measurableSet_Ioo.preimage (measurable_fst)).inter
        (measurableSet_Ioi.preimage (measurable_snd))

private lemma twoDimF_measurable : Measurable twoDimF := by
  unfold twoDimF
  fun_prop

private lemma twoDimDensR_measurable (d : ℕ) : Measurable (twoDimDensR d) := by
  unfold twoDimDensR
  fun_prop

/-! ### The two-dimensional substitution `(t,s) ↦ (s t, s √(1-t²))` -/

/-- For `a q : ℝ` with `q > 0`, the point `(a/√(a²+q²), √(a²+q²))` lies in the strip and is
mapped to `(a,q)` by `F`. -/
private lemma exists_param (a q : ℝ) (hq : 0 < q) :
    ∃ t s : ℝ, t ∈ Set.Ioo (-1) 1 ∧ 0 < s ∧ twoDimF (t, s) = (a, q) := by
  have hs2pos : 0 < a ^ 2 + q ^ 2 := by nlinarith [sq_nonneg a, sq_pos_of_pos hq]
  have hs2le : 0 ≤ a ^ 2 + q ^ 2 := le_of_lt hs2pos
  let s : ℝ := Real.sqrt (a ^ 2 + q ^ 2)
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 hs2pos
  have hsq : s ^ 2 = a ^ 2 + q ^ 2 := by dsimp [s]; rw [Real.sq_sqrt hs2le]
  have ht2 : (a / s) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (pow_pos hs 2)]
    rw [hsq]; nlinarith [sq_pos_of_pos hq]
  have htabs : |a / s| < 1 := abs_lt_of_sq_lt_sq (by simpa using ht2) zero_le_one
  have htIoo : a / s ∈ Set.Ioo (-1) 1 := ⟨(abs_lt.mp htabs).1, (abs_lt.mp htabs).2⟩
  have hmain : 1 - (a / s) ^ 2 = (q / s) ^ 2 := by
    rw [div_pow, div_pow]
    field_simp [ne_of_gt hs]
    rw [hsq]; ring
  have hsqrt : Real.sqrt (1 - (a / s) ^ 2) = q / s := by
    rw [hmain, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hq hs)]
  refine ⟨a / s, s, htIoo, hs, ?_⟩
  show (s * (a / s), s * Real.sqrt (1 - (a / s) ^ 2)) = (a, q)
  rw [hsqrt]
  refine Prod.ext ?_ ?_
  · field_simp [ne_of_gt hs]
  · field_simp [ne_of_gt hs]

private lemma twoDimF_injOn : InjOn twoDimF twoDimU := by
  rintro ⟨t1, s1⟩ ht1 ⟨t2, s2⟩ ht2 hF
  simp only [twoDimU, Set.mem_ofPred_eq] at ht1 ht2
  rcases ht1 with ⟨htt1, hs1⟩
  rcases ht2 with ⟨htt2, hs2⟩
  rcases htt1 with ⟨hlo1, hhi1⟩
  rcases htt2 with ⟨hlo2, hhi2⟩
  have hb1sq : Real.sqrt (1 - t1 ^ 2) ^ 2 = 1 - t1 ^ 2 :=
    Real.sq_sqrt (le_of_lt (twoDimU_pos hlo1 hhi1))
  have hb2sq : Real.sqrt (1 - t2 ^ 2) ^ 2 = 1 - t2 ^ 2 :=
    Real.sq_sqrt (le_of_lt (twoDimU_pos hlo2 hhi2))
  simp only [twoDimF, Prod.mk.injEq] at hF
  rcases hF with ⟨ha, hq⟩
  have hsq1 : s1 ^ 2 = s2 ^ 2 := by
    have hsquare : (s1 * t1) ^ 2 + (s1 * Real.sqrt (1 - t1 ^ 2)) ^ 2
        = (s2 * t2) ^ 2 + (s2 * Real.sqrt (1 - t2 ^ 2)) ^ 2 := by rw [ha, hq]
    have hL : (s1 * t1) ^ 2 + (s1 * Real.sqrt (1 - t1 ^ 2)) ^ 2 = s1 ^ 2 := by
      rw [mul_pow, mul_pow, hb1sq]; ring
    have hR : (s2 * t2) ^ 2 + (s2 * Real.sqrt (1 - t2 ^ 2)) ^ 2 = s2 ^ 2 := by
      rw [mul_pow, mul_pow, hb2sq]; ring
    linarith
  have hs1eq : s1 = s2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq1 with h | h
    · exact h
    · exfalso; linarith
  refine Prod.ext ?_ hs1eq
  have ha' : s1 * t1 = s1 * t2 := by rw [← hs1eq] at ha; exact ha
  exact mul_left_cancel₀ (ne_of_gt hs1) ha'

private lemma twoDimF_image : twoDimF '' twoDimU = twoDimV := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    simp only [twoDimU, Set.mem_ofPred_eq] at hp
    exact mul_pos hp.2 (Real.sqrt_pos.2 (twoDimU_pos hp.1.1 hp.1.2))
  · intro hq
    rcases q with ⟨a, qq⟩
    simp only [twoDimV, Set.mem_ofPred_eq] at hq
    obtain ⟨t, s, ht, hs, hF⟩ := exists_param a qq hq
    exact ⟨(t, s), by simp only [twoDimU, Set.mem_ofPred_eq]; exact ⟨ht, hs⟩, hF⟩

/-! ### The real `rpow` identity -/

private lemma jac_density_real (d : ℕ) (hd : 1 ≤ d) {t s : ℝ}
    (ht : t ∈ Set.Ioo (-1) 1) (hs : 0 < s) :
    |s / Real.sqrt (1 - t ^ 2)| * (s * Real.sqrt (1 - t ^ 2)) ^ (d - 1)
      = (1 - t ^ 2) ^ (((d : ℝ) - 2) / 2) * s ^ d := by
  set a : ℝ := 1 - t ^ 2 with hadef
  have hapos : 0 < a := by rw [hadef]; exact twoDimU_pos ht.1 ht.2
  set b : ℝ := Real.sqrt a with hbdef
  have hbpos : 0 < b := by rw [hbdef]; exact Real.sqrt_pos.2 hapos
  have hba : b = a ^ (1 / 2 : ℝ) := by rw [hbdef, Real.sqrt_eq_rpow]
  rw [abs_of_pos (div_pos hs hbpos)]
  rw [← Real.rpow_natCast (s * b) (d - 1), ← Real.rpow_natCast s d]
  have hy : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by simpa using Nat.cast_sub hd
  rw [hy]
  rw [Real.mul_rpow (le_of_lt hs) (le_of_lt hbpos)]
  have hcombine : s / b * (s ^ ((d : ℝ) - 1) * b ^ ((d : ℝ) - 1))
      = s ^ (d : ℝ) * b ^ ((d : ℝ) - 2) := by
    have h2 : b ^ ((d : ℝ) - 2) = b ^ ((d : ℝ) - 1) / b := by
      have hh : (d : ℝ) - 2 = ((d : ℝ) - 1) - 1 := by ring
      rw [hh, Real.rpow_sub hbpos ((d : ℝ) - 1) 1, Real.rpow_one]
    have h1 : s ^ (d : ℝ) = s * s ^ ((d : ℝ) - 1) := by
      conv_lhs => rw [show (d : ℝ) = 1 + ((d : ℝ) - 1) from by ring]
      rw [Real.rpow_add hs 1 ((d : ℝ) - 1), Real.rpow_one]
    rw [h1, h2, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hcombine]
  have hbpow : b ^ ((d : ℝ) - 2) = a ^ (((d : ℝ) - 2) / 2) := by
    rw [hba, ← Real.rpow_mul (le_of_lt hapos) (1 / 2) ((d : ℝ) - 2)]
    congr 1
    ring
  rw [hbpow, mul_comm]

/-! ### The Jacobian determinant of `F` -/

/-- Candidate derivative of `F` at `p`. -/
private def twoDimDF (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-(p.2 * p.1) / Real.sqrt (1 - p.1 ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + Real.sqrt (1 - p.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The determinant of `twoDimDF p`, written as an explicit real expression. -/
private abbrev twoDimDet (p : ℝ × ℝ) : ℝ :=
  p.2 * Real.sqrt (1 - p.1 ^ 2)
    - p.1 * (-(p.2 * p.1) / Real.sqrt (1 - p.1 ^ 2))

private lemma twoDimDet_measurable :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal |twoDimDet p|) := by
  unfold twoDimDet
  fun_prop

private lemma twoDimDF_eq_matrix (p : ℝ × ℝ) :
    twoDimDF p = (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![p.2, p.1; -(p.2 * p.1) / Real.sqrt (1 - p.1 ^ 2),
          Real.sqrt (1 - p.1 ^ 2)]).toContinuousLinearMap := by
  rw [twoDimDF, Matrix.toLin_finTwoProd_toContinuousLinearMap]

private lemma twoDimDF_det_expr (p : ℝ × ℝ) : (twoDimDF p).det = twoDimDet p := by
  rw [twoDimDF_eq_matrix]
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]

private lemma hasDerivAt_sqrt_one_sub_sq (t : ℝ) (ht : 0 < 1 - t ^ 2) :
    HasDerivAt (fun u : ℝ => Real.sqrt (1 - u ^ 2)) (-(t / Real.sqrt (1 - t ^ 2))) t := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * t)) t := by
    have hsub : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (0 - 2 * t ^ (2 - 1)) t :=
      (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub (hasDerivAt_pow 2 t)
    convert hsub using 1
    norm_num
  have h2 : HasDerivAt (fun u : ℝ => Real.sqrt (1 - u ^ 2))
      (1 / (2 * Real.sqrt (1 - t ^ 2)) * -(2 * t)) t := by
    have h := (Real.hasDerivAt_sqrt (x := 1 - t ^ 2) (ne_of_gt ht)).comp t h1
    convert! h using 1
  have hval : (1 / (2 * Real.sqrt (1 - t ^ 2)) * -(2 * t)) = -(t / Real.sqrt (1 - t ^ 2)) := by
    field_simp
  rwa [hval] at h2

private lemma hasFDerivAt_twoDimF (p : ℝ × ℝ) (hp : 0 < 1 - p.1 ^ 2) :
    HasFDerivAt twoDimF (twoDimDF p) p := by
  have hderiv := hasDerivAt_sqrt_one_sub_sq p.1 hp
  have hcomp1 : HasFDerivAt (fun p : ℝ × ℝ => p.2 * p.1)
      (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hasFDerivAt_snd (p := p)).mul (hasFDerivAt_fst (p := p))
  have hcomp2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 * Real.sqrt (1 - p.1 ^ 2))
      (p.2 • (-(p.1 / Real.sqrt (1 - p.1 ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        + Real.sqrt (1 - p.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hasFDerivAt_snd (p := p)).mul (hderiv.comp_hasFDerivAt p (hasFDerivAt_fst (p := p)))
  have hcoef : p.2 * (-(p.1 / Real.sqrt (1 - p.1 ^ 2))) = -(p.2 * p.1) / Real.sqrt (1 - p.1 ^ 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hcomp2' : HasFDerivAt (fun p : ℝ × ℝ => p.2 * Real.sqrt (1 - p.1 ^ 2))
      ((-(p.2 * p.1) / Real.sqrt (1 - p.1 ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + Real.sqrt (1 - p.1 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    rw [← hcoef, ← smul_smul]
    exact hcomp2
  unfold twoDimDF
  exact HasFDerivAt.prodMk hcomp1 hcomp2'

private lemma twoDimDF_det (p : ℝ × ℝ) (hp : 0 < 1 - p.1 ^ 2) :
    (twoDimDF p).det = p.2 / Real.sqrt (1 - p.1 ^ 2) := by
  have hb : Real.sqrt (1 - p.1 ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hbsq : (Real.sqrt (1 - p.1 ^ 2)) ^ 2 = 1 - p.1 ^ 2 := Real.sq_sqrt (le_of_lt hp)
  rw [twoDimDF_det_expr]
  simp only [twoDimDet]
  field_simp
  rw [hbsq]
  ring

/-! ### The pointwise density identity -/

private lemma density_identity (d : ℕ) (hd : 1 ≤ d) (p : ℝ × ℝ) (hp : p ∈ twoDimU) :
    ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2) * p.2 ^ d) =
      ENNReal.ofReal |(twoDimDF p).det| *
        ENNReal.ofReal ((p.2 * Real.sqrt (1 - p.1 ^ 2)) ^ (d - 1)) := by
  have ht : p.1 ∈ Set.Ioo (-1) 1 := hp.1
  have hs : 0 < p.2 := hp.2
  have hbpos : 0 < Real.sqrt (1 - p.1 ^ 2) := Real.sqrt_pos.2 (twoDimU_pos ht.1 ht.2)
  rw [twoDimDF_det p (twoDimU_pos ht.1 ht.2), abs_of_pos (div_pos hs hbpos)]
  rw [← ENNReal.ofReal_mul (le_of_lt (div_pos hs hbpos))]
  congr 1
  have hj := jac_density_real d hd ht hs
  rw [abs_of_pos (div_pos hs hbpos)] at hj
  exact hj.symm

/-! ### The main theorem -/

theorem pair_cyl_twoDim_core_upper (d : ℕ) (hd : 1 ≤ d) :
    let U : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Ioo (-1) 1 ∧ 0 < p.2}
    let V : Set (ℝ × ℝ) := {p | 0 < p.2}
    let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 * p.1, p.2 * Real.sqrt (1 - p.1 ^ 2))
    MeasureTheory.Measure.map F ((MeasureTheory.volume.restrict U).withDensity
        (fun p => ENNReal.ofReal ((1 - p.1 ^ 2) ^ (((d : ℝ) - 2) / 2) * p.2 ^ d))) =
      (MeasureTheory.volume.restrict V).withDensity (fun p => ENNReal.ofReal (p.2 ^ (d - 1))) := by
  simp only
  change MeasureTheory.Measure.map twoDimF
      ((MeasureTheory.volume.restrict twoDimU).withDensity (twoDimDensL d)) =
    (MeasureTheory.volume.restrict twoDimV).withDensity (twoDimDensR d)
  have hUmeas : MeasurableSet twoDimU := twoDimU_measurable
  have hFmeas : Measurable twoDimF := twoDimF_measurable
  have hinj : InjOn twoDimF twoDimU := twoDimF_injOn
  have himage : twoDimF '' twoDimU = twoDimV := twoDimF_image
  have hderiv : ∀ p ∈ twoDimU, HasFDerivWithinAt twoDimF (twoDimDF p) twoDimU p :=
    fun p hp => (hasFDerivAt_twoDimF p (twoDimU_pos hp.1.1 hp.1.2)).hasFDerivWithinAt
  -- the Jacobian theorem
  have hJac := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure (ℝ × ℝ)) hUmeas.nullMeasurableSet hderiv hinj
  -- rewrite the det-density as a measurable function
  have hdetfun : (fun p : ℝ × ℝ => ENNReal.ofReal |(twoDimDF p).det|)
      = fun p : ℝ × ℝ => ENNReal.ofReal |twoDimDet p| := by
    funext p; rw [twoDimDF_det_expr]
  have hf_ae : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal |(twoDimDF p).det|)
      (volume.restrict twoDimU) := by
    rw [hdetfun]
    exact twoDimDet_measurable.aemeasurable
  have hg_ae : AEMeasurable (fun p : ℝ × ℝ => twoDimDensR d (twoDimF p))
      (volume.restrict twoDimU) := by
    have hmeas : Measurable (fun p : ℝ × ℝ => twoDimDensR d (twoDimF p)) := by
      unfold twoDimDensR twoDimF
      fun_prop
    exact hmeas.aemeasurable
  -- step 1: replace the density by `|det| * densR ∘ F` on `U`
  have hL1 : (MeasureTheory.volume.restrict twoDimU).withDensity (twoDimDensL d) =
      (MeasureTheory.volume.restrict twoDimU).withDensity
        (fun p => ENNReal.ofReal |(twoDimDF p).det| * twoDimDensR d (twoDimF p)) := by
    apply MeasureTheory.withDensity_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with p hp
    have h := density_identity d hd p hp
    simpa only [twoDimDensL, twoDimDensR, twoDimF] using h
  -- step 2: split the density
  have hL2 : (MeasureTheory.volume.restrict twoDimU).withDensity
        (fun p => ENNReal.ofReal |(twoDimDF p).det| * twoDimDensR d (twoDimF p)) =
      ((MeasureTheory.volume.restrict twoDimU).withDensity
        (fun p => ENNReal.ofReal |(twoDimDF p).det|)).withDensity
        (fun p => twoDimDensR d (twoDimF p)) := by
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal |(twoDimDF p).det| * twoDimDensR d (twoDimF p))
        = (fun p : ℝ × ℝ => ENNReal.ofReal |(twoDimDF p).det|) * (fun p : ℝ × ℝ => twoDimDensR d (twoDimF p))
        from by funext p; rfl]
    rw [MeasureTheory.withDensity_mul₀ hf_ae hg_ae]
  -- step 3: push the Jacobian part forward, then add the density
  have hL3 : MeasureTheory.Measure.map twoDimF
        (((MeasureTheory.volume.restrict twoDimU).withDensity
          (fun p => ENNReal.ofReal |(twoDimDF p).det|)).withDensity
          (fun p => twoDimDensR d (twoDimF p))) =
      (MeasureTheory.Measure.map twoDimF
          ((MeasureTheory.volume.restrict twoDimU).withDensity
            (fun p => ENNReal.ofReal |(twoDimDF p).det|))).withDensity (twoDimDensR d) :=
    map_withDensity_comp _ hFmeas (twoDimDensR_measurable d)
  calc
    MeasureTheory.Measure.map twoDimF
        ((MeasureTheory.volume.restrict twoDimU).withDensity (twoDimDensL d))
        = MeasureTheory.Measure.map twoDimF
            ((MeasureTheory.volume.restrict twoDimU).withDensity
              (fun p => ENNReal.ofReal |(twoDimDF p).det| * twoDimDensR d (twoDimF p))) := by
          rw [hL1]
    _ = MeasureTheory.Measure.map twoDimF
            (((MeasureTheory.volume.restrict twoDimU).withDensity
              (fun p => ENNReal.ofReal |(twoDimDF p).det|)).withDensity
              (fun p => twoDimDensR d (twoDimF p))) := by rw [hL2]
    _ = (MeasureTheory.Measure.map twoDimF
            ((MeasureTheory.volume.restrict twoDimU).withDensity
              (fun p => ENNReal.ofReal |(twoDimDF p).det|))).withDensity (twoDimDensR d) := hL3
    _ = (MeasureTheory.volume.restrict (twoDimF '' twoDimU)).withDensity (twoDimDensR d) := by
          rw [hJac]
    _ = (MeasureTheory.volume.restrict twoDimV).withDensity (twoDimDensR d) := by rw [himage]

end Commons.Analysis.MeasureTheory