/-
# `Work.FIArea3.JointCount.volume_convexHull_angSector_le_large`

Volume bound for the convex hull of an angular annular sector whose angular width is at
least `π`.

The sector `{a < ‖z‖ ≤ b, α < arg z ≤ β}` is contained in the closed ball of radius `b`
intersected with the half-plane `{z | b cos h ≤ Re (z * conj n)}`, where `m = (α+β)/2`,
`h = (β-α)/2` and `n = exp (i m)`.  The convex hull of the outer arc is exactly the part of
the disk cut out by the chord joining `b e^{iα}` and `b e^{iβ}`, whose area is
`(b²/2)(2h - sin 2h) = (b²/2)(θ - sin θ)` with `θ = β - α`.  The area of the complementary
circular segment is computed by subtracting from the corresponding polar sector the inscribed
triangle (`volume_convexHull_zero_pair`).
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.angSector
import Submission.Work.FIArea3.JointCount.polarBand_volume
import Submission.Work.FIArea3.JointCount.volume_argRegion_le

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The closed right sector `{‖z‖ ≤ b, |arg z| ≤ γ}`. -/
def sectorArg (γ b : ℝ) : Set ℂ := {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ}

/-- The closed right cap `{‖z‖ ≤ b, b cos γ ≤ re z}`. -/
def capArg (γ b : ℝ) : Set ℂ := {z : ℂ | ‖z‖ ≤ b ∧ b * Real.cos γ ≤ z.re}

/-- The (open) triangular region `{‖z‖ ≤ b, |arg z| ≤ γ, re z < b cos γ}`. -/
def triArg (γ b : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ ∧ z.re < b * Real.cos γ}

/-! ## The cap is the sector minus the triangle -/

lemma capArg_subset_sectorArg {γ b : ℝ} (hb : 0 < b) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ Real.pi / 2) : capArg γ b ⊆ sectorArg γ b := by
  intro z hz
  rw [capArg, Set.mem_ofPred_eq] at hz
  obtain ⟨hzn, hzre⟩ := hz
  rw [sectorArg, Set.mem_ofPred_eq]
  refine ⟨hzn, ?_⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [Complex.arg_zero, Set.mem_Icc]
    exact ⟨by linarith, hγ0⟩
  · have hγcos : 0 ≤ Real.cos γ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hγ0, Real.pi_pos], hγ1⟩
    have hre0 : 0 ≤ z.re := le_trans (mul_nonneg hb.le hγcos) hzre
    have hkey : Real.cos γ * ‖z‖ ≤ z.re := by
      calc Real.cos γ * ‖z‖ ≤ Real.cos γ * b := mul_le_mul_of_nonneg_left hzn hγcos
        _ = b * Real.cos γ := by ring
        _ ≤ z.re := hzre
    have hcos : Real.cos γ ≤ Real.cos z.arg := by
      rw [Complex.cos_arg hz0, le_div_iff₀ (norm_pos_iff.mpr hz0)]
      linarith [hkey]
    have hargabs : |z.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre0
    have hmain : |z.arg| ≤ γ := by
      by_contra h
      push Not at h
      have h2 : Real.cos |z.arg| < Real.cos γ :=
        Real.cos_lt_cos_of_nonneg_of_le_pi hγ0 (by linarith [hargabs, Real.pi_pos]) h
      rw [Real.cos_abs] at h2
      linarith [h2, hcos]
    rw [Set.mem_Icc]
    exact abs_le.mp hmain

lemma sectorArg_sdiff_triArg {γ b : ℝ} (hb : 0 < b) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ Real.pi / 2) : sectorArg γ b \ triArg γ b = capArg γ b := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hzt⟩
    rw [sectorArg, Set.mem_ofPred_eq] at hz
    obtain ⟨hzn, hzarg⟩ := hz
    rw [capArg, Set.mem_ofPred_eq]
    refine ⟨hzn, ?_⟩
    by_contra h
    push Not at h
    exact hzt ⟨hzn, hzarg, h⟩
  · intro z hz
    refine ⟨capArg_subset_sectorArg hb hγ0 hγ1 hz, ?_⟩
    rw [capArg, Set.mem_ofPred_eq] at hz
    rw [triArg, Set.mem_ofPred_eq]
    rintro ⟨-, -, hlt⟩
    linarith [hz.2, hlt]

/-! ## Volume of the closed sector -/

lemma volume_sectorArg {γ b : ℝ} (hb : 0 ≤ b) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    volume (sectorArg γ b) = ENNReal.ofReal (b ^ 2 * γ) := by
  set pb : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ b ∧ z.arg ∈ Set.Icc (-γ) γ} with hpb
  have hpb_sub : pb ⊆ sectorArg γ b := fun z hz => ⟨hz.2.1, hz.2.2⟩
  have hsub : sectorArg γ b ⊆ pb ∪ ({0} : Set ℂ) := by
    rintro z ⟨hzn, hzarg⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Or.inr rfl
    · exact Or.inl ⟨norm_pos_iff.mpr hz0, hzn, hzarg⟩
  have hle : volume (sectorArg γ b) ≤ volume pb := by
    calc volume (sectorArg γ b) ≤ volume (pb ∪ ({0} : Set ℂ)) := measure_mono hsub
      _ ≤ volume pb + volume ({0} : Set ℂ) := measure_union_le _ _
      _ = volume pb := by simp
  have hge : volume pb ≤ volume (sectorArg γ b) := measure_mono hpb_sub
  have hpbval : volume pb = ENNReal.ofReal (b ^ 2 * γ) := by
    have hp := polarBand_volume 0 b (Set.Icc (-γ) γ) (le_refl 0) hb measurableSet_Icc
    rw [hpb, hp]
    have hI : Set.Icc (-γ) γ ∩ Set.Ioo (-Real.pi) Real.pi = Set.Icc (-γ) γ := by
      refine Set.inter_eq_left.mpr ?_
      intro t ht
      rw [Set.mem_Icc] at ht
      rw [Set.mem_Ioo]
      exact ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
    rw [hI, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    congr 1
    ring
  exact le_antisymm (hle.trans_eq hpbval) (hpbval.ge.trans hge)

/-! ## Volume of the triangular region -/

lemma volume_triArg_le {γ b : ℝ} (hb : 0 ≤ b) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ Real.pi / 2) :
    (volume (triArg γ b)).toReal ≤ b ^ 2 / 2 :=
  volume_argRegion_le b γ hb hγ0 hγ1

/-! ## Auxiliary measure facts -/

lemma volume_line_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hS : ({q : ℝ × ℝ | q.1 = c}) = ({c} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext q; simp
  have hmeas : MeasurableSet ({q : ℝ × ℝ | q.1 = c}) :=
    hS.symm ▸ (measurableSet_singleton c).prod MeasurableSet.univ
  have hnull : volume ({q : ℝ × ℝ | q.1 = c}) = 0 := by
    rw [hS, MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h1 : Complex.measurableEquivRealProd ⁻¹' {q : ℝ × ℝ | q.1 = c}
      = {z : ℂ | z.re = c} := by
    ext z; simp [Complex.measurableEquivRealProd_apply]
  rw [← h1, (Complex.volume_preserving_equiv_real_prod).measure_preimage hmeas.nullMeasurableSet,
    hnull]

lemma ofReal_sub_ofReal_le (a q : ℝ) :
    ENNReal.ofReal a - ENNReal.ofReal q ≤ ENNReal.ofReal (a - q) := by
  by_cases hq : 0 ≤ q
  · rw [ENNReal.ofReal_sub a hq]
  · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hq)), tsub_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith [not_le.mp hq])

/-! ## The half-plane/disk bound -/

lemma volume_ball_inter_halfplane_le {γ b : ℝ} (hb : 0 < b) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ Real.pi / 2) :
    (volume (Metric.closedBall 0 b ∩ {z : ℂ | -b * Real.cos γ ≤ z.re})).toReal
      ≤ b ^ 2 * (Real.pi - γ + 1 / 2) := by
  set Ball : Set ℂ := Metric.closedBall 0 b with hBall
  set capNeg : Set ℂ := Ball ∩ {z : ℂ | z.re < -b * Real.cos γ} with hcapNeg
  set posCap : Set ℂ := Ball ∩ {z : ℂ | b * Real.cos γ < z.re} with hposCap
  have hE : Ball ∩ {z : ℂ | -b * Real.cos γ ≤ z.re} = Ball \ capNeg := by
    ext z
    rw [hcapNeg, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => absurd h3.2 (not_lt.mpr h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, le_of_not_gt (fun h3 => h2 ⟨h1, h3⟩)⟩
  have hballv : volume Ball = ENNReal.ofReal (b ^ 2 * Real.pi) := by
    rw [hBall, Complex.volume_closedBall]
    have h1 : (↑NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
      rw [← ENNReal.ofReal_coe_nnreal]; rfl
    rw [h1, ← ENNReal.ofReal_pow hb.le 2, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ b ^ 2)]
  have hfin : volume Ball ≠ ⊤ := by
    rw [hBall]; exact Metric.isBounded_closedBall.measure_lt_top.ne
  have hcapn_eq : volume capNeg = volume posCap := by
    have h := Measure.addHaar_smul (volume : Measure ℂ) (-1) capNeg
    rw [Complex.finrank_real_complex] at h
    rw [show ((-1 : ℝ) ^ (2 : ℕ)) = 1 by norm_num, abs_one, ENNReal.ofReal_one, one_mul] at h
    rw [← h]
    congr 1
    ext z
    simp only [hcapNeg, hposCap, Set.mem_smul_set, Set.mem_inter_iff, Set.mem_ofPred_eq, hBall,
      Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, hyz⟩
      rw [neg_one_smul] at hyz
      rw [← hyz]
      refine ⟨?_, ?_⟩
      · rw [norm_neg]; exact hy1
      · rw [Complex.neg_re]; linarith
    · rintro ⟨hz1, hz2⟩
      refine ⟨-z, ⟨?_, ?_⟩, ?_⟩
      · rwa [norm_neg]
      · rw [Complex.neg_re]; linarith
      · rw [neg_one_smul, neg_neg]
  have hpos_eq : posCap = capArg γ b \ {z : ℂ | z.re = b * Real.cos γ} := by
    ext z
    simp only [hposCap, hBall, capArg, Metric.mem_closedBall, dist_zero_right, Set.mem_inter_iff,
      Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.le⟩, h2.ne'⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, lt_of_le_of_ne h2 (Ne.symm h3)⟩
  have hcapn : volume capNeg = volume (capArg γ b) := by
    rw [hcapn_eq, hpos_eq, measure_sdiff_null (volume_line_re_eq (b * Real.cos γ))]
  have htrimeas : NullMeasurableSet (triArg γ b) volume := by
    rw [triArg]; measurability
  have htri_sub : triArg γ b ⊆ sectorArg γ b := fun z hz => ⟨hz.1, hz.2.1⟩
  have htri_fin : volume (triArg γ b) ≠ ⊤ := by
    have hbdd : Bornology.IsBounded (triArg γ b) := by
      refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := 0) (r := b)) ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz.1
    exact hbdd.measure_lt_top.ne
  have hcapEq : volume (capArg γ b) = volume (sectorArg γ b) - volume (triArg γ b) := by
    rw [← sectorArg_sdiff_triArg hb hγ0 hγ1]
    exact measure_sdiff htri_sub htrimeas htri_fin
  have htrile : volume (triArg γ b) ≤ ENNReal.ofReal (b ^ 2 / 2) :=
    (ENNReal.le_ofReal_iff_toReal_le htri_fin (by positivity)).mpr
      (volume_triArg_le hb.le hγ0 hγ1)
  have hcapge : ENNReal.ofReal (b ^ 2 * (γ - 1 / 2)) ≤ volume (capArg γ b) := by
    have hq : (0:ℝ) ≤ b ^ 2 / 2 := by positivity
    rw [hcapEq, volume_sectorArg hb.le hγ0 hγ1]
    calc ENNReal.ofReal (b ^ 2 * (γ - 1 / 2))
        = ENNReal.ofReal (b ^ 2 * γ - b ^ 2 / 2) := by
          rw [show b ^ 2 * (γ - 1 / 2) = b ^ 2 * γ - b ^ 2 / 2 by ring]
      _ = ENNReal.ofReal (b ^ 2 * γ) - ENNReal.ofReal (b ^ 2 / 2) :=
          ENNReal.ofReal_sub (b ^ 2 * γ) hq
      _ ≤ ENNReal.ofReal (b ^ 2 * γ) - volume (triArg γ b) := tsub_le_tsub_left htrile _
  have hcap1 : capNeg ⊆ Ball := by rw [hcapNeg]; exact Set.inter_subset_left
  have hcapm : NullMeasurableSet capNeg volume := by rw [hcapNeg]; measurability
  have hcapf : volume capNeg ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hcap1)
  have hE2 : volume (Ball ∩ {z : ℂ | -b * Real.cos γ ≤ z.re}) = volume Ball - volume capNeg := by
    rw [hE]; exact measure_sdiff hcap1 hcapm hcapf
  have hchain : volume (Ball ∩ {z : ℂ | -b * Real.cos γ ≤ z.re})
      ≤ ENNReal.ofReal (b ^ 2 * (Real.pi - γ + 1 / 2)) := by
    calc volume (Ball ∩ {z : ℂ | -b * Real.cos γ ≤ z.re})
        = ENNReal.ofReal (b ^ 2 * Real.pi) - volume (capArg γ b) := by rw [hE2, hballv, hcapn]
      _ ≤ ENNReal.ofReal (b ^ 2 * Real.pi) - ENNReal.ofReal (b ^ 2 * (γ - 1 / 2)) :=
          tsub_le_tsub_left hcapge _
      _ ≤ ENNReal.ofReal (b ^ 2 * Real.pi - b ^ 2 * (γ - 1 / 2)) :=
          ofReal_sub_ofReal_le _ _
      _ = ENNReal.ofReal (b ^ 2 * (Real.pi - γ + 1 / 2)) := by congr 1; ring
  have hfin' : (0:ℝ) ≤ Real.pi - γ + 1 / 2 := by linarith [Real.pi_pos, hγ1]
  calc (volume (Ball ∩ {z : ℂ | -b * Real.cos γ ≤ z.re})).toReal
      ≤ (ENNReal.ofReal (b ^ 2 * (Real.pi - γ + 1 / 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
    _ = b ^ 2 * (Real.pi - γ + 1 / 2) := ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg b) hfin')

/-! ## The half-plane containment of the sector -/

lemma re_mul_nc (z : ℂ) (m : ℝ) :
    (z * ((Real.cos m : ℂ) - (Real.sin m : ℂ) * Complex.I)).re
      = ‖z‖ * Real.cos (z.arg - m) := by
  rw [Complex.mul_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_sub]
  rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z, Real.cos_sub]
  ring

lemma norm_cos_sub_sin_mul_I (m : ℝ) :
    ‖((Real.cos m : ℂ) - (Real.sin m : ℂ) * Complex.I)‖ = 1 := by
  rw [show ((Real.cos m : ℂ) - (Real.sin m : ℂ) * Complex.I)
      = Complex.cos ((-m : ℝ) : ℂ) + Complex.sin ((-m : ℝ) : ℂ) * Complex.I by
        simp [Complex.ofReal_cos, Complex.ofReal_sin]; ring]
  exact Complex.norm_cos_add_sin_mul_I (-m)

/-! ## The main theorem -/

theorem volume_convexHull_angSector_le_large (a b α β : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) (hαβ : α ≤ β) (hℓ : Real.pi ≤ β - α) :
    (MeasureTheory.volume (convexHull ℝ (angSector a b (Set.Ioc α β)))).toReal
      ≤ b ^ 2 / 2 * ((β - α) + 1) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set m : ℝ := (α + β) / 2 with hm
  set h : ℝ := (β - α) / 2 with hh
  set γ : ℝ := Real.pi - h with hγ
  have hh_ge : Real.pi / 2 ≤ h := by rw [hh]; linarith
  have hh_le : h ≤ Real.pi := by rw [hh]; linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ ≤ Real.pi / 2 := by rw [hγ]; linarith
  set nc : ℂ := (Real.cos m : ℂ) - (Real.sin m : ℂ) * Complex.I with hnc
  have hnc_norm : ‖nc‖ = 1 := norm_cos_sub_sin_mul_I m
  -- containment of the sector
  have hsub : angSector a b (Set.Ioc α β) ⊆
      Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re} := by
    intro z hz
    rw [angSector, Set.mem_ofPred_eq] at hz
    obtain ⟨hza, hzb, hzarg⟩ := hz
    rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    refine ⟨hzb, ?_⟩
    have hkey : (z * nc).re = ‖z‖ * Real.cos (z.arg - m) := by rw [hnc]; exact re_mul_nc z m
    rw [hkey]
    have harg : z.arg - m ∈ Set.Icc (-h) h := by
      rw [Set.mem_Ioc] at hzarg
      rw [Set.mem_Icc, hm, hh]; constructor <;> linarith [hzarg.1, hzarg.2]
    have hle : |z.arg - m| ≤ h := abs_le.mpr harg
    have hcos : Real.cos h ≤ Real.cos (z.arg - m) := by
      have h' := Real.cos_le_cos_of_nonneg_of_le_pi (x := |z.arg - m|) (y := h)
        (abs_nonneg _) hh_le hle
      rwa [Real.cos_abs] at h'
    have hcosh0 : Real.cos h ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hh_ge (by linarith)
    have h1 : b * Real.cos h ≤ ‖z‖ * Real.cos h := by nlinarith [hzb, hcosh0]
    calc b * Real.cos h ≤ ‖z‖ * Real.cos h := h1
      _ ≤ ‖z‖ * Real.cos (z.arg - m) := mul_le_mul_of_nonneg_left hcos (norm_nonneg z)
  -- convexity of the containing set
  let g : ℂ →ₗ[ℝ] ℝ :=
    (nc.re : ℝ) • (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) - (nc.im : ℝ) • (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)
  have hg : ∀ z : ℂ, g z = (z * nc).re := by
    intro z
    have h1 : g z = nc.re * z.re - nc.im * z.im := by
      simp only [g, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [show (↑Complex.reCLM : ℂ →ₗ[ℝ] ℝ) z = z.re from rfl,
          show (↑Complex.imCLM : ℂ →ₗ[ℝ] ℝ) z = z.im from rfl]
    rw [h1, Complex.mul_re]; ring
  have hH0conv : Convex ℝ {z : ℂ | b * Real.cos h ≤ (z * nc).re} := by
    rw [show {z : ℂ | b * Real.cos h ≤ (z * nc).re}
        = g ⁻¹' (Set.Ici (b * Real.cos h)) by
      ext z; rw [Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq, hg]]
    exact (convex_Ici _).linear_preimage g
  have hconv : Convex ℝ (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re}) :=
    (convex_closedBall 0 b).inter hH0conv
  have hHullSub : convexHull ℝ (angSector a b (Set.Ioc α β)) ⊆
      Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re} :=
    convexHull_min hsub hconv
  -- the rotation
  let c : Circle := ⟨nc, by simp [Submonoid.unitSphere, hnc_norm]⟩
  have hcval : (c : ℂ) = nc := rfl
  have hBalle : (rotation c) ⁻¹' (Metric.closedBall 0 b) = Metric.closedBall 0 b := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero, rotation_apply,
      hcval, norm_mul, hnc_norm, one_mul]
  have hH0 : {z : ℂ | b * Real.cos h ≤ (z * nc).re}
      = (rotation c) ⁻¹' {w : ℂ | b * Real.cos h ≤ w.re} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, rotation_apply, hcval]
    rw [mul_comm z nc]
  have hrot : volume (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re})
      = volume (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ z.re}) := by
    have hset : Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re}
        = (rotation c) ⁻¹' (Metric.closedBall 0 b ∩ {w : ℂ | b * Real.cos h ≤ w.re}) := by
      rw [Set.preimage_inter, hBalle, hH0]
    rw [hset]
    exact (LinearIsometryEquiv.measurePreserving (rotation c)).measure_preimage (by measurability)
  have hcap2 : volume (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ z.re})
      = volume (Metric.closedBall 0 b ∩ {z : ℂ | -b * Real.cos γ ≤ z.re}) := by
    have hcos : Real.cos γ = -Real.cos h := by rw [hγ, Real.cos_pi_sub]
    have hval : -b * Real.cos γ = b * Real.cos h := by rw [hcos]; ring
    rw [hval]
  have hfin2 : volume (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re}) ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  have hcri := volume_ball_inter_halfplane_le hb hγ0 hγ1
  calc (volume (convexHull ℝ (angSector a b (Set.Ioc α β)))).toReal
      ≤ (volume (Metric.closedBall 0 b ∩ {z : ℂ | b * Real.cos h ≤ (z * nc).re})).toReal :=
        ENNReal.toReal_mono hfin2 (measure_mono hHullSub)
    _ = (volume (Metric.closedBall 0 b ∩ {z : ℂ | -b * Real.cos γ ≤ z.re})).toReal := by
        rw [hrot, hcap2]
    _ ≤ b ^ 2 * (Real.pi - γ + 1 / 2) := hcri
    _ = b ^ 2 / 2 * ((β - α) + 1) := by rw [hγ, hh]; ring

end

end Work.FIArea3.JointCount
