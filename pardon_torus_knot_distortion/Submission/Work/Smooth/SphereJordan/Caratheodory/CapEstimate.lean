import Mathlib
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapGeometry
import Submission.Work.Smooth.SphereJordan.Caratheodory.LengthArea

/-!
# The length–area estimate for a cap of the unit disc

This file carries out, for the disc version of the length–area principle, the estimates that
Garnett–Marshall use to prove the boundary continuity of the Riemann map of a Jordan domain.

The cap `𝔻 ∩ B(1,s)` of the unit disc at the boundary point `1` is traversed by the arc
`τ ↦ capPt s τ = 1 - s * exp(τ * I)`, `τ ∈ (-arccos (s/2), arccos (s/2))`.  Writing

  `capLen f s = ∫⁻ τ in (-α, α), ofReal (s * ‖deriv f (capPt s τ)‖)`

for the length of the image of this arc under a holomorphic `f`, the main results are

* `lintegral_cap_polar` — the polar change of variables for the cap;
* `capLen_mul_self_le` — Cauchy–Schwarz, `(capLen f s)² ≤ 2π s ∫ ‖f'‖²`;
* `lintegral_capLen_le` — `∫₀^{1/2} (capLen f s)² / s ≤ 2π ∫_{cap} ‖f'‖²`;
* `exists_capLen_le` — hence there are arbitrarily small `s` with arbitrarily small `capLen f s`;
* `exists_tendsto_capPt` — the two ends of the image arc converge.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

namespace Work.Smooth.SphereJordan.Caratheodory

/-! ## The two parametrisations of the circle around `1` -/

/-- The circle of radius `s` around `1`, with the angle measured from the direction pointing
away from the origin. -/
def capPtP (s θ : ℝ) : ℂ := 1 + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

lemma capPt_eq_capPtP_add (s τ : ℝ) : capPt s τ = capPtP s (τ + Real.pi) := by
  have h : (((τ + Real.pi : ℝ)) : ℂ) * Complex.I =
      (τ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [capPt, capPtP, h, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma capPt_eq_capPtP_sub (s τ : ℝ) : capPt s τ = capPtP s (τ - Real.pi) := by
  have h : (((τ - Real.pi : ℝ)) : ℂ) * Complex.I =
      (τ : ℂ) * Complex.I - (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [capPt, capPtP, h, Complex.exp_sub, Complex.exp_pi_mul_I]
  field_simp
  ring

/-- On `[0, π]` the cosine is strictly decreasing, in `iff` form. -/
lemma cos_lt_cos_iff_of_nonneg_of_le_pi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haπ : a ≤ Real.pi) (hbπ : b ≤ Real.pi) : Real.cos a < Real.cos b ↔ b < a := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · exact absurd h (not_lt.mpr (le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi ha hbπ hlt)))
    · rw [heq] at h; exact absurd h (lt_irrefl _)
  · intro h
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hb haπ h

/-- The arc of the circle of radius `s` around `1` inside the unit disc, in the `capPtP`
parametrisation: it is the union of the two intervals adjacent to `±π`. -/
lemma capArcP_set {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ({θ : ℝ | Real.cos θ < -(s / 2)} ∩ Set.Ioo (-Real.pi) Real.pi) =
      (Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
        Set.Ioo (Real.pi - capAlpha s) Real.pi) := by
  have hα0 : 0 < capAlpha s := capAlpha_pos hs2
  have hαπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have hcos : Real.cos (Real.pi - capAlpha s) = -(s / 2) := by
    rw [Real.cos_pi_sub, cos_capAlpha hs hs2]
  have key : ∀ θ : ℝ, θ ∈ Set.Ioo (-Real.pi) Real.pi →
      (Real.cos θ < -(s / 2) ↔ Real.pi - capAlpha s < |θ|) := by
    intro θ hθ
    rw [Set.mem_Ioo] at hθ
    have h1 : |θ| < Real.pi := abs_lt.mpr hθ
    have h2 : 0 ≤ |θ| := abs_nonneg θ
    have h3 : 0 < Real.pi - capAlpha s := by linarith
    have h4 : |θ| ≤ Real.pi := le_of_lt h1
    have h5 : Real.pi - capAlpha s ≤ Real.pi := by linarith
    rw [← hcos, ← Real.cos_abs]
    exact cos_lt_cos_iff_of_nonneg_of_le_pi h2 h3.le h4 h5
  ext θ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_union]
  constructor
  · rintro ⟨hc, h1, h2⟩
    have h := (key θ ⟨h1, h2⟩).mp hc
    rcases lt_abs.mp h with h' | h'
    · right; exact ⟨h', h2⟩
    · left; exact ⟨h1, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨(key θ ⟨h1, by linarith⟩).mpr ?_, h1, by linarith⟩
      rw [abs_of_neg (by linarith)]
      linarith
    · refine ⟨(key θ ⟨by linarith, h2⟩).mpr ?_, by linarith, h2⟩
      rw [abs_of_nonneg (by linarith)]
      linarith

/-! ## The length of the image of the arc -/

/-- The length of the image under `f` of the arc `capPt s (-α(s), α(s))`, as a lower integral. -/
def capLen (f : ℂ → ℂ) (s : ℝ) : ENNReal :=
  ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s), ENNReal.ofReal (s * ‖deriv f (capPt s τ)‖)


/-! ## The "plus" parametrisation against the unit disc -/

lemma capPtP_apply (s θ : ℝ) :
    capPtP s θ = 1 + (s : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  simp [capPtP, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma capPtP_sub_one (s θ : ℝ) :
    capPtP s θ - 1 = (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [capPtP]

lemma norm_capPtP_sub_one (s θ : ℝ) : ‖capPtP s θ - 1‖ = |s| := by
  rw [capPtP_sub_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

lemma sq_norm_capPtP (s θ : ℝ) : ‖capPtP s θ‖ ^ 2 = 1 + s ^ 2 + 2 * s * Real.cos θ := by
  have hre : (capPtP s θ).re = 1 + s * Real.cos θ := by
    simp [capPtP, Complex.exp_ofReal_mul_I_re]
  have him : (capPtP s θ).im = s * Real.sin θ := by
    simp [capPtP, Complex.exp_ofReal_mul_I_im]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma capPtP_mem_ball_iff {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (θ : ℝ) :
    capPtP s θ ∈ Metric.ball (0 : ℂ) 1 ↔ Real.cos θ < -(s / 2) := by
  rw [Metric.mem_ball, dist_zero_right]
  have h := sq_norm_capPtP s θ
  constructor
  · intro hlt
    have h1 : ‖capPtP s θ‖ ^ 2 < 1 := by nlinarith [norm_nonneg (capPtP s θ)]
    rw [h] at h1
    nlinarith [hs]
  · intro hlt
    have h1 : ‖capPtP s θ‖ ^ 2 < 1 := by rw [h]; nlinarith [hs, hs2]
    nlinarith [norm_nonneg (capPtP s θ)]

lemma capPt_periodic (s τ : ℝ) : capPt s (τ + 2 * Real.pi) = capPt s τ := by
  have h : (((τ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
      (τ : ℂ) * Complex.I + (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [capPt, capPt, h, Complex.exp_add]
  have h2 : Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
        ((Real.pi : ℂ) * Complex.I) + ((Real.pi : ℂ) * Complex.I) from by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [h2, mul_one]

/-! ## The polar-coordinate identity for the cap -/

/-- Fubini for a product set. -/
lemma lintegral_prod_set {F : ℝ × ℝ → ENNReal} (hF : AEMeasurable F (volume.prod volume))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ p in A ×ˢ B, F p = ∫⁻ s in A, ∫⁻ θ in B, F (s, θ) := by
  have hvol : (volume : MeasureTheory.Measure (ℝ × ℝ)) = MeasureTheory.volume.prod
      MeasureTheory.volume := rfl
  rw [hvol, ← lintegral_indicator (hA.prod hB)]
  rw [lintegral_prod _ (hF.indicator (hA.prod hB))]
  rw [← lintegral_indicator hA]
  refine lintegral_congr fun s => ?_
  by_cases hsa : s ∈ A
  · rw [Set.indicator_of_mem hsa, ← lintegral_indicator hB]
    refine lintegral_congr fun θ => ?_
    by_cases hθb : θ ∈ B
    · rw [Set.indicator_of_mem (show (s, θ) ∈ A ×ˢ B from ⟨hsa, hθb⟩),
        Set.indicator_of_mem hθb]
    · rw [Set.indicator_of_notMem (fun h => hθb h.2), Set.indicator_of_notMem hθb]
  · rw [Set.indicator_of_notMem hsa]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    refine Eventually.of_forall fun θ => ?_
    show (A ×ˢ B).indicator F (s, θ) = 0
    rw [Set.indicator_of_notMem (fun h => hsa h.1)]

/-- The polar-coordinate identity for the cap `𝔻 ∩ B(1,1/2)`, in the parametrisation
`θ ↦ 1 + s e^{iθ}` (whose angle runs over `(-π,π)`). -/
theorem lintegral_cap_polar_P {g : ℂ → ENNReal} (hg : Measurable g) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2), g z
      = ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2),
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal s * (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2)).indicator g
              (capPtP s θ) := by
  classical
  set S : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2) with hS
  have hSmeas : MeasurableSet S := measurableSet_ball.inter measurableSet_ball
  have hcontF : Continuous (fun p : ℝ × ℝ => 1 + Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hpt : ∀ p : ℝ × ℝ, 1 + Complex.polarCoord.symm p = capPtP p.1 p.2 := by
    intro p
    simp only [Complex.polarCoord_symm_apply, capPtP, Complex.exp_mul_I, Complex.ofReal_cos,
      Complex.ofReal_sin]
  set F : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal p.1 * (S.indicator g)
    (1 + Complex.polarCoord.symm p) with hF
  have hFmeas : AEMeasurable F (volume.prod volume) := by
    rw [hF]
    exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hg.indicator hSmeas).comp hcontF.measurable)).aemeasurable
  -- ## The identity, before restricting the outer variable
  have key : ∫⁻ z in S, g z
      = ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F (s, θ) := by
    have h1 : ∫⁻ z in S, g z = ∫⁻ z, (S.indicator g) z := (lintegral_indicator hSmeas g).symm
    have h2 : ∫⁻ z, (S.indicator g) z
        = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, F p := by
      rw [lintegral_polar_comp (S.indicator g) 1]
    rw [h1, h2, lintegral_prod_set hFmeas measurableSet_Ioi measurableSet_Ioo]
  rw [key]
  -- ## The outer variable is restricted to `(0, 1/2)`
  have hzero : ∀ s ∉ Set.Ioo (0 : ℝ) (1 / 2),
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F (s, θ)) = 0 := by
    intro s hs
    rw [Set.mem_Ioo] at hs
    push Not at hs
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    refine Eventually.of_forall fun θ => ?_
    show ENNReal.ofReal s * (S.indicator g) (1 + Complex.polarCoord.symm (s, θ)) = 0
    rw [hpt (s, θ)]
    by_cases hpos : 0 < s
    · have hle : (1 / 2 : ℝ) ≤ s := hs hpos
      have hnot : capPtP s θ ∉ S := by
        intro hmem
        have h2 := hmem.2
        rw [Metric.mem_ball, dist_eq_norm, norm_capPtP_sub_one, abs_of_pos hpos] at h2
        linarith
      rw [Set.indicator_of_notMem hnot]; ring
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hpos)]; ring
  have hrestrict : ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F (s, θ)
      = ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F (s, θ) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) (1 / 2)))]
    refine lintegral_congr fun s => ?_
    by_cases h1 : s ∈ Set.Ioi (0 : ℝ) <;> by_cases h2 : s ∈ Set.Ioo (0 : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, hzero s h2]
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 h.1)]
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 h.1)]
  rw [hrestrict]
  refine lintegral_congr fun s => lintegral_congr fun θ => ?_
  show ENNReal.ofReal s * (S.indicator g) (1 + Complex.polarCoord.symm (s, θ))
    = ENNReal.ofReal s * (S.indicator g) (capPtP s θ)
  rw [hpt (s, θ)]

/-- The inner integral of the polar identity for a fixed `s ∈ (0,1/2)`, rewritten on the arc
`(-α(s), α(s))` of the `capPt`-parametrisation. -/
theorem cap_inner_eq {g : ℂ → ENNReal} {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal s * (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2)).indicator g
          (capPtP s θ))
      = ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s), ENNReal.ofReal s * g (capPt s τ) := by
  classical
  obtain ⟨hs0, hslt⟩ := hs
  set S : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2) with hS
  have hsub : ∀ θ : ℝ, capPtP s θ ∈ S ↔ Real.cos θ < -(s / 2) := by
    intro θ
    rw [hS, Set.mem_inter_iff, capPtP_mem_ball_iff hs0 (by linarith), Metric.mem_ball,
      dist_eq_norm, norm_capPtP_sub_one, abs_of_pos hs0]
    exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
  have harc : Set.Ioo (-Real.pi) Real.pi ∩ {θ : ℝ | Real.cos θ < -(s / 2)} =
      (Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
        Set.Ioo (Real.pi - capAlpha s) Real.pi) := by
    rw [Set.inter_comm]
    exact capArcP_set hs0 (by linarith)
  have hstep : (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal s * (S.indicator g) (capPtP s θ))
      = ∫⁻ θ in (Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
          Set.Ioo (Real.pi - capAlpha s) Real.pi), ENNReal.ofReal s * g (capPtP s θ) := by
    rw [← lintegral_indicator (measurableSet_Ioo : MeasurableSet (Set.Ioo (-Real.pi) Real.pi)),
      ← lintegral_indicator (measurableSet_Ioo.union measurableSet_Ioo)]
    refine lintegral_congr fun θ => ?_
    by_cases hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi
    · rw [Set.indicator_of_mem hθ]
      by_cases hc : Real.cos θ < -(s / 2)
      · have hmem : θ ∈ Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
            Set.Ioo (Real.pi - capAlpha s) Real.pi := by
          rw [← harc]; exact ⟨hθ, hc⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hsub θ).mpr hc)]
      · have hmem : θ ∉ Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
            Set.Ioo (Real.pi - capAlpha s) Real.pi := by
          intro h
          rw [← harc] at h
          exact hc h.2
        rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun h => hc ((hsub θ).mp h))]
        ring
    · have hmem : θ ∉ Set.Ioo (-Real.pi) (-Real.pi + capAlpha s) ∪
          Set.Ioo (Real.pi - capAlpha s) Real.pi := by
        intro h
        rw [← harc] at h
        exact hθ h.1
      rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hmem]
  rw [hstep]
  have hdisj : Disjoint (Set.Ioo (-Real.pi) (-Real.pi + capAlpha s))
      (Set.Ioo (Real.pi - capAlpha s) Real.pi) := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    simp only [Set.mem_Ioo] at h1 h2
    have := capAlpha_lt_pi hs0
    linarith
  rw [lintegral_union measurableSet_Ioo hdisj]
  have hcap : ∀ θ : ℝ, capPt s (θ + Real.pi) = capPtP s θ := by
    intro θ
    have h := capPt_eq_capPtP_sub s (θ + Real.pi)
    rwa [show θ + Real.pi - Real.pi = θ from by ring] at h
  have hper : ∀ τ : ℝ, ENNReal.ofReal s * g (capPt s (τ + Real.pi + Real.pi))
      = ENNReal.ofReal s * g (capPt s τ) := by
    intro τ
    rw [show τ + Real.pi + Real.pi = τ + 2 * Real.pi from by ring, capPt_periodic]
  have e1 : ∫⁻ θ in Set.Ioo (-Real.pi) (-Real.pi + capAlpha s),
        ENNReal.ofReal s * g (capPtP s θ)
      = ∫⁻ τ in Set.Ioo (0 : ℝ) (capAlpha s), ENNReal.ofReal s * g (capPt s τ) := by
    have h := lintegral_Ioo_add_right (fun τ : ℝ => ENNReal.ofReal s * g (capPt s τ))
      (-Real.pi) (-Real.pi + capAlpha s) Real.pi
    rw [show -Real.pi + Real.pi = (0 : ℝ) from by ring,
      show -Real.pi + capAlpha s + Real.pi = capAlpha s from by ring] at h
    rw [h]
    refine lintegral_congr fun θ => ?_
    rw [hcap]
  have e2 : ∫⁻ θ in Set.Ioo (Real.pi - capAlpha s) Real.pi,
        ENNReal.ofReal s * g (capPtP s θ)
      = ∫⁻ τ in Set.Ioo (-(capAlpha s)) 0, ENNReal.ofReal s * g (capPt s τ) := by
    have h := lintegral_Ioo_add_right
      (fun τ : ℝ => ENNReal.ofReal s * g (capPt s (τ + Real.pi)))
      (-(capAlpha s)) 0 Real.pi
    rw [show -(capAlpha s) + Real.pi = Real.pi - capAlpha s from by ring,
      show (0 : ℝ) + Real.pi = Real.pi from by ring] at h
    simp only [hper] at h
    rw [← h]
    refine lintegral_congr fun θ => ?_
    rw [hcap]
  rw [e1, e2, lintegral_Ioo_split (fun τ : ℝ => ENNReal.ofReal s * g (capPt s τ))
    (a := -(capAlpha s)) (b := capAlpha s) (c := 0)
    (by have := capAlpha_pos (show s < 2 by linarith); linarith)
    (by have := capAlpha_pos (show s < 2 by linarith); linarith)]
  exact add_comm _ _

/-- **Polar-coordinate identity for the cap at `1`.** -/
theorem lintegral_cap_polar {g : ℂ → ENNReal} (hg : Measurable g) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (1 / 2), g z
      = ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2),
          ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
            ENNReal.ofReal s * g (capPt s τ) := by
  rw [lintegral_cap_polar_P hg]
  refine lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo)] with s hs
  exact cap_inner_eq hs


/-! ## Cauchy–Schwarz for the length of the image of the arc -/

/-- Cauchy–Schwarz for `lintegral`s, in the form needed below. -/
lemma lintegral_mul_self_le {h : ℝ → ENNReal} {S : Set ℝ}
    (hh : AEMeasurable h (volume.restrict S)) :
    (∫⁻ x in S, h x) * (∫⁻ x in S, h x) ≤ (volume S) * ∫⁻ x in S, h x * h x := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq hh
    (aemeasurable_const (b := (1 : ENNReal)))
  have h3 : (∫⁻ a in S, (1 : ENNReal)) = volume S := by
    rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hpow : ∀ x : ℝ, h x ^ (2 : ℝ) = h x * h x := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have h2 : (∫⁻ x in S, h x) ≤
      (∫⁻ x in S, h x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (volume S) ^ (1 / 2 : ℝ) := by
    convert h1 using 2
    · exact (mul_one _).symm
    · rw [ENNReal.one_rpow, h3]
  have hA : ∀ A : ENNReal, A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
    intro A
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num),
      show (1/2 : ℝ) + 1/2 = 1 from by norm_num, ENNReal.rpow_one]
  calc (∫⁻ x in S, h x) * (∫⁻ x in S, h x)
      ≤ ((∫⁻ x in S, h x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (volume S) ^ (1 / 2 : ℝ)) *
        ((∫⁻ x in S, h x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (volume S) ^ (1 / 2 : ℝ)) :=
        mul_le_mul' h2 h2
    _ = (volume S) * ∫⁻ x in S, h x * h x := by
        rw [show (∫⁻ x in S, h x ^ (2 : ℝ)) = ∫⁻ x in S, h x * h x from
          lintegral_congr fun x => hpow x]
        set A : ENNReal := ∫⁻ x in S, h x * h x
        set B : ENNReal := volume S
        rw [show A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ))
            = (A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) * (B ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ))
            from by ring,
          hA A, hA B, mul_comm B A]


/-! ## The length–area estimate -/

/-- **The pointwise Cauchy–Schwarz bound** for the length of the image of the arc. -/
theorem capLen_sq_div_le (f : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    capLen f s * capLen f s * (ENNReal.ofReal s)⁻¹ ≤ ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
        ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2) := by
  have hderiv : Measurable (fun τ : ℝ => deriv f (capPt s τ)) :=
    (measurable_deriv f).comp (continuous_capPt s).measurable
  set h : ℝ → ENNReal := fun τ => ENNReal.ofReal (s * ‖deriv f (capPt s τ)‖) with hh
  have hmeas : AEMeasurable h (volume.restrict (Set.Ioo (-(capAlpha s)) (capAlpha s))) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hderiv.norm)).aemeasurable
  have hcs := lintegral_mul_self_le (S := Set.Ioo (-(capAlpha s)) (capAlpha s)) hmeas
  have hvol : volume (Set.Ioo (-(capAlpha s)) (capAlpha s)) ≤ ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioo]
    refine ENNReal.ofReal_le_ofReal ?_
    have := capAlpha_lt_pi hs
    linarith
  have hsq : ∀ τ : ℝ, h τ * h τ = ENNReal.ofReal s *
      (ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)) := by
    intro τ
    rw [hh]
    rw [show ENNReal.ofReal s * (ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2))
        = ENNReal.ofReal (s * (s * ‖deriv f (capPt s τ)‖ ^ 2)) from by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]]
    rw [show ENNReal.ofReal (s * ‖deriv f (capPt s τ)‖) * ENNReal.ofReal (s * ‖deriv f (capPt s τ)‖)
        = ENNReal.ofReal ((s * ‖deriv f (capPt s τ)‖) * (s * ‖deriv f (capPt s τ)‖)) from
      (ENNReal.ofReal_mul (by positivity)).symm]
    congr 1
    ring
  have hsq_meas : Measurable (fun τ : ℝ => ‖deriv f (capPt s τ)‖ ^ 2) := by
    have h2 : (fun τ : ℝ => ‖deriv f (capPt s τ)‖ ^ 2)
        = fun τ => ‖deriv f (capPt s τ)‖ * ‖deriv f (capPt s τ)‖ := by
      funext τ; rw [pow_two]
    rw [h2]
    exact hderiv.norm.mul hderiv.norm
  have hmeas2 : Measurable (fun τ : ℝ => ENNReal.ofReal s *
      ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp hsq_meas)
  have hmul : (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s), h τ * h τ)
      = ENNReal.ofReal s * (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
          ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)) := by
    rw [lintegral_congr fun τ => hsq τ, lintegral_const_mul _ hmeas2]
  have hcap : capLen f s = ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s), h τ := rfl
  have hspos : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  calc capLen f s * capLen f s * (ENNReal.ofReal s)⁻¹
      ≤ ((volume (Set.Ioo (-(capAlpha s)) (capAlpha s))) *
          (ENNReal.ofReal s * (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
            ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)))) *
          (ENNReal.ofReal s)⁻¹ := by
        rw [hcap, ← hmul]
        exact mul_le_mul' hcs le_rfl
    _ = (volume (Set.Ioo (-(capAlpha s)) (capAlpha s))) *
          (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
            ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)) := by
        have hred : (ENNReal.ofReal s * (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
              ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2))) *
              (ENNReal.ofReal s)⁻¹
            = ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
              ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2) := by
          rw [mul_assoc, mul_comm (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
              ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)),
            ← mul_assoc, ENNReal.mul_inv_cancel hspos hstop, one_mul]
        rw [mul_assoc, hred]
    _ ≤ ENNReal.ofReal (2 * Real.pi) * (∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
          ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2)) :=
        mul_le_mul' hvol le_rfl

/-- **The length–area estimate.** -/
theorem lintegral_capLen_le (f : ℂ → ℂ) :
    ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2), capLen f s * capLen f s * (ENNReal.ofReal s)⁻¹
      ≤ ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) := by
  have hderiv : Measurable (fun z : ℂ => ENNReal.ofReal (‖deriv f z‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h2 : (fun z : ℂ => ‖deriv f z‖ ^ 2) = fun z => ‖deriv f z‖ * ‖deriv f z‖ := by
      funext z; rw [pow_two]
    rw [h2]
    exact (measurable_deriv f).norm.mul (measurable_deriv f).norm
  have h1 : ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2), capLen f s * capLen f s * (ENNReal.ofReal s)⁻¹
      ≤ ∫⁻ s in Set.Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ τ in Set.Ioo (-(capAlpha s)) (capAlpha s),
            ENNReal.ofReal s * ENNReal.ofReal (‖deriv f (capPt s τ)‖ ^ 2) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo)] with s hs
    exact capLen_sq_div_le f hs.1 (by linarith [hs.2])
  refine le_trans h1 ?_
  rw [lintegral_const_mul' (ENNReal.ofReal (2 * Real.pi)) _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ?_
  rw [← lintegral_cap_polar hderiv]
  exact lintegral_mono_set Set.inter_subset_left


/-- **Extraction of small arcs.**  If the energy of `f` over the unit disc is finite, then for
every `ε > 0` and every `δ > 0` there is `s ∈ (0, δ)` for which the image under `f` of the arc
`capPt s (-α(s), α(s))` has length at most `ε`. -/
theorem exists_capLen_le (f : ℂ → ℂ)
    (hfin : ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) < ⊤) :
    ∀ ε > 0, ∀ δ > 0, ∃ s ∈ Set.Ioo (0 : ℝ) δ, capLen f s ≤ ENNReal.ofReal ε := by
  intro ε hε δ hδ
  set C : ENNReal := ENNReal.ofReal (2 * Real.pi) *
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) with hC
  have hCtop : C < ⊤ := by
    rw [hC]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C < ((N + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ε ^ 2 / 2) := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_of_lt hCtop)
    have hc : (0 : ℝ) < ε ^ 2 / 2 := by positivity
    refine ⟨⌊(n : ℝ) / (ε ^ 2 / 2)⌋₊, ?_⟩
    have hlt : (n : ℝ) < ((⌊(n : ℝ) / (ε ^ 2 / 2)⌋₊ + 1 : ℕ) : ℝ) * (ε ^ 2 / 2) := by
      have h4 : (n : ℝ) / (ε ^ 2 / 2) < (⌊(n : ℝ) / (ε ^ 2 / 2)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h5 := mul_lt_mul_of_pos_right h4 hc
      rw [div_mul_cancel₀ _ (ne_of_gt hc)] at h5
      push_cast
      exact h5
    calc C < (n : ENNReal) := hn
      _ = ENNReal.ofReal (n : ℝ) := (ENNReal.ofReal_natCast n).symm
      _ < ENNReal.ofReal (((⌊(n : ℝ) / (ε ^ 2 / 2)⌋₊ + 1 : ℕ) : ℝ) * (ε ^ 2 / 2)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt
      _ = ((⌊(n : ℝ) / (ε ^ 2 / 2)⌋₊ + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ε ^ 2 / 2) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  set δ' : ℝ := min δ (1/2) with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact lt_min hδ (by norm_num : (0:ℝ) < 1/2)
  have hδ'le : δ' ≤ 1 / 2 := by rw [hδ'def]; exact min_le_right _ _
  have hδ'led : δ' ≤ δ := by rw [hδ'def]; exact min_le_left _ _
  set A : ℝ → ENNReal := fun s => capLen f s * capLen f s * (ENNReal.ofReal s)⁻¹ with hA
  have hpt : ∀ s ∈ Set.Ioo (0:ℝ) δ', ENNReal.ofReal (ε^2) * (ENNReal.ofReal s)⁻¹ ≤ A s := by
    intro s hs
    have hsδ : s ∈ Set.Ioo (0:ℝ) δ := ⟨hs.1, lt_of_lt_of_le hs.2 hδ'led⟩
    have h1 : ENNReal.ofReal ε ≤ capLen f s := le_of_lt (hcon s hsδ)
    have h2 : ENNReal.ofReal (ε^2) ≤ capLen f s * capLen f s := by
      have := mul_le_mul' h1 h1
      rwa [show ENNReal.ofReal ε * ENNReal.ofReal ε = ENNReal.ofReal (ε^2) from by
        rw [← ENNReal.ofReal_mul (le_of_lt hε), pow_two]] at this
    rw [hA]
    exact mul_le_mul' h2 le_rfl
  have hmem : ∀ j : ℕ, Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j) ⊆ Set.Ioo (0:ℝ) δ' := by
    intro j s hs
    rw [Set.mem_Ioo] at hs ⊢
    constructor
    · have : 0 < δ' / 2^(j+1) := by positivity
      linarith [hs.1]
    · have h2 : δ' / 2^j ≤ δ' := by
        have hge1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^j)]
        nlinarith [hge1, hδ'pos]
      linarith [hs.2, h2]
  have hsub12 : ∀ j : ℕ, Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j) ⊆ Set.Ioo (0:ℝ) (1/2) := by
    intro j s hs
    have h := hmem j hs
    rw [Set.mem_Ioo] at h ⊢
    exact ⟨h.1, lt_of_lt_of_le h.2 hδ'le⟩
  have hlb : ∀ j : ℕ, ENNReal.ofReal (ε^2/2) ≤ ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), A s := by
    intro j
    have h1 : ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j),
          ENNReal.ofReal (ε^2) * (ENNReal.ofReal s)⁻¹
        ≤ ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), A s :=
      lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
        exact hpt s (hmem j hs))
    refine le_trans ?_ h1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have h2 : ENNReal.ofReal (1/2) ≤ ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j),
        (ENNReal.ofReal s)⁻¹ := by
      have hcj : (0:ℝ) < (2:ℝ)^j := by positivity
      have h3 : ∀ s ∈ Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j),
          ENNReal.ofReal ((2:ℝ)^j / δ') ≤ (ENNReal.ofReal s)⁻¹ := by
        intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs.1.le
        rw [← ENNReal.ofReal_inv_of_pos hs0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h5 : s ≤ δ' / 2^j := le_of_lt hs.2
        rw [le_div_iff₀ hcj] at h5
        rw [div_le_iff₀ hδ'pos]
        have h7 : s⁻¹ * δ' ≥ (2:ℝ)^j := by
          calc s⁻¹ * δ' ≥ s⁻¹ * (s * (2:ℝ)^j) := mul_le_mul_of_nonneg_left h5 (by positivity)
            _ = (2:ℝ)^j := by
                rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs0), one_mul]
        exact h7
      calc ENNReal.ofReal (1/2)
          = ENNReal.ofReal ((2:ℝ)^j / δ') * ENNReal.ofReal (δ' / 2^(j+1)) := by
            have hp : (2:ℝ)^(j+1) = (2:ℝ)^j * 2 := pow_succ 2 j
            have hr : (2:ℝ)^j / δ' * (δ' / 2^(j+1)) = 1/2 := by
              rw [hp]
              field_simp [hδ'pos.ne']
            rw [← hr]
            exact ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^j / δ')
        _ = ENNReal.ofReal ((2:ℝ)^j / δ') *
              volume (Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j)) := by
            have hp : (2:ℝ)^(j+1) = (2:ℝ)^j * 2 := pow_succ 2 j
            have h2j : (2:ℝ)^j ≠ 0 := by positivity
            have hv : δ' / 2^j - δ' / 2^(j+1) = δ' / 2^(j+1) := by
              rw [hp]
              field_simp [hδ'pos.ne', h2j]
              ring
            rw [Real.volume_Ioo, hv]
        _ = ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), ENNReal.ofReal ((2:ℝ)^j / δ') := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), (ENNReal.ofReal s)⁻¹ :=
            lintegral_mono_ae (by
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
              exact h3 s hs)
    calc ENNReal.ofReal (ε^2/2)
        = ENNReal.ofReal (ε^2) * ENNReal.ofReal (1/2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal (ε^2) * (∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j),
            (ENNReal.ofReal s)⁻¹) := mul_le_mul' le_rfl h2
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N+1)) : Set ℕ)
      (fun j => Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j)) := by
    intro i _ k _ hik
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Ioo] at hx hx'
    rcases lt_or_gt_of_ne hik with hlt | hlt
    · have hle : (2:ℝ)^(i+1) ≤ 2^k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h1 : δ' / 2^k ≤ δ' / 2^(i+1) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hδ'pos.le
        exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2^k) (by positivity : (0:ℝ) < 2^(i+1))).mpr hle
      linarith [hx.1, hx'.2, h1]
    · have hle : (2:ℝ)^(k+1) ≤ 2^i := pow_le_pow_right₀ (by norm_num) (by omega)
      have h1 : δ' / 2^i ≤ δ' / 2^(k+1) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hδ'pos.le
        exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2^i) (by positivity : (0:ℝ) < 2^(k+1))).mpr hle
      linarith [hx'.1, hx.2, h1]
  have hsum : ((N + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ε^2/2) ≤ C := by
    calc ((N + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ε^2/2)
        = ∑ j ∈ Finset.range (N+1), ENNReal.ofReal (ε^2/2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ Finset.range (N+1), ∫⁻ s in Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), A s :=
          Finset.sum_le_sum fun j _ => hlb j
      _ = ∫⁻ s in ⋃ j ∈ Finset.range (N+1), Set.Ioo (δ' / 2^(j+1)) (δ' / 2^j), A s := by
          rw [lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
      _ ≤ ∫⁻ s in Set.Ioo (0:ℝ) (1/2), A s :=
          lintegral_mono_set (Set.iUnion₂_subset fun j _ => hsub12 j)
      _ ≤ C := by rw [hC]; exact lintegral_capLen_le f
  exact absurd hN (not_lt.mpr hsum)

end Work.Smooth.SphereJordan.Caratheodory
