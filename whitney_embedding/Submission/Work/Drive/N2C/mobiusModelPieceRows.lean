import Mathlib
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusModelImSubmersion
import Submission.Work.Drive.N2Lead.mobius_upperArcs
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobius_pushedStar
import Submission.Work.Drive.N2Lead.mobiusArcSmooth
import Submission.Work.N2Lead.absDerivSmoothTransitionLeTwo
import Submission.Work.Drive.N2Lead.modelPicRate
import Submission.Work.Drive.N2Lead.mobiusUpperModelRate
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2Lead

noncomputable section

/-!
# The two model-piece rows of the twisted Möbius picture

This file proves `Work.Drive.N2C.mobiusModelPieceRows`: on the model region of the saddle window, at
the level `f p + 3η/2`, the planar picture of a `df`-critical point

* is off the real axis (`(proj2 (mobiusTwisted … y)).im ≠ 0`), and
* is not tangent to the ray through the origin: the `proj2`-velocity along any non-zero
  `ker df`-direction is never a real multiple of the value.

The proof splits the picture into the plane model `modelPic η δ a' ε Dp εp` of
`N2Lead.modelPicDefs` (the model region factors through the chart coordinate `Z`), and uses:

* `N2Lead.modelPic_level_local` (the sign of `saddlePsi` relative to `mobiusRho` is locally constant
  along a level, so the picture restricted to the level is one of the two pushed arcs);
* the *uniform* threshold form `pushedStarUniform` of `N2Lead.mobius_pushedStarIcc` — the push size
  `D₀` there is independent of the band half width `εp`, which is what allows the quantifier order
  `∃ εp₀, ∃ D₀, ∀ εp ≤ εp₀, ∀ D ≥ D₀` of the target;
* `N2Lead.rate_step` and `N2Lead.not_realMultiple_of_det` for the determinant form of the tangent row.
-/

/-- **The uniform threshold behind `mobius_pushedStar`.**  For a `C¹` curve `g` with strictly
increasing `x`-coordinate and `y`-coordinate of constant sign `εs = ±1` on `Icc a b`, the push row
of `N2Lead.mobius_pushedStarIcc` admits an `εp₀` and a `D₀` such that for **every** `εp ≤ εp₀` and
**every** `D ≥ D₀` the pushed `y`-coordinate keeps the sign `εs` and the pushed angular rate keeps
the strict sign `-εs`.  The point is that the witnesses can be chosen independently: `D₀` is built
from the rate bound and the `x`-derivative bound of the *unpushed* curve, hence does not depend on
`εp`. -/
theorem pushedStarUniform {g : ℝ → E3} {εs a b : ℝ}
    (hg : ContDiff ℝ 1 g) (hεs : εs = 1 ∨ εs = -1) (hab : a ≤ b)
    (hgx : ∀ w ∈ Set.Icc a b, 0 < deriv (fun u : ℝ => g u 0) w)
    (hgy : ∀ w ∈ Set.Icc a b, 0 < εs * g w 1) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ → ∀ D : ℝ, D₀ ≤ D → ∀ t ∈ Set.Icc a b,
        0 < εs * (pushY D εp 1 (g t)) 1 ∧
        εs * ((pushY D εp 1 (g t)) 0 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t
          - (pushY D εp 1 (g t)) 1 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t) < 0 := by
  have hIcc_ne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  -- the `y`-coordinate of `g` does not vanish on the compact parameter interval
  have habs : ∀ w ∈ Set.Icc a b, |g w 1| = εs * g w 1 := by
    intro w hw
    rcases hεs with rfl | rfl
    · rw [one_mul]; exact abs_of_pos (by linarith [hgy w hw])
    · rw [neg_one_mul]; exact abs_of_neg (by linarith [hgy w hw])
  have hcont_abs : Continuous (fun w : ℝ => |g w 1|) := (continuous_coord hg 1).abs
  obtain ⟨w₀, hw₀mem, hw₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcont_abs.continuousOn
  have hm_pos : 0 < |g w₀ 1| := by rw [habs w₀ hw₀mem]; exact hgy w₀ hw₀mem
  -- a bound on the angular rate over the compact interval
  obtain ⟨M, hMnonneg, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Set.Icc a b, |mobiusRate g w| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_mobiusRate hg).continuousOn
    exact ⟨max M 0, le_max_right _ _,
      fun w hw => le_trans (by simpa [Real.norm_eq_abs] using hM w hw) (le_max_left _ _)⟩
  -- a strictly positive lower bound on the `x`-derivative over the compact interval
  obtain ⟨t₀, ht₀mem, ht₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne (continuous_deriv_coord hg 0).continuousOn
  have hc_pos : 0 < deriv (fun u : ℝ => g u 0) t₀ := hgx t₀ ht₀mem
  have hD₀pos : 0 < M / deriv (fun u : ℝ => g u 0) t₀ + 1 := by positivity
  refine ⟨|g w₀ 1| / 2, by linarith, M / deriv (fun u : ℝ => g u 0) t₀ + 1,
    le_of_lt hD₀pos, ?_⟩
  intro εp hεp hεp_le D hD
  have hDpos : 0 < D := by linarith
  -- the whole interval lies in the good side of the band
  have hregion : ∀ w ∈ Set.Icc a b, εp ≤ εs * g w 1 := by
    intro w hw
    have h1 : |g w₀ 1| ≤ |g w 1| := hw₀min hw
    have h2 : 2 * εp ≤ |g w₀ 1| := by linarith
    rw [← habs w hw]; linarith
  have hsq : εs * εs = 1 := by rcases hεs with rfl | rfl <;> norm_num
  intro t ht
  have hgt : εp < εs * g t 1 := by
    have h1 : |g w₀ 1| ≤ |g t 1| := hw₀min ht
    have h2 : 2 * εp ≤ |g w₀ 1| := by linarith
    rw [← habs t ht]; linarith
  have hev : ∀ᶠ u in 𝓝 t, εp ≤ εs * g u 1 := by
    have h := ((continuous_const.mul (continuous_coord hg 1)).continuousAt).tendsto
      (Ici_mem_nhds hgt)
    filter_upwards [h] with u hu
    simpa using hu
  -- the pushed coordinates and their derivatives
  have hXd : deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t = deriv (fun u : ℝ => g u 0) t := by
    rw [show (fun u : ℝ => (pushY D εp 1 (g u)) 0) = (fun u : ℝ => g u 0) from
      funext (fun u => by simp)]
  have hYd : deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t = deriv (fun u : ℝ => g u 1) t := by
    rw [show (fun u : ℝ => (pushY D εp 1 (g u)) 1)
          = (fun u : ℝ => pushProf D εp 1 (g u 1)) from funext (fun u => by simp)]
    exact deriv_pushProf_one_comp_of_sign hεs hεp hev
  have hXv : (pushY D εp 1 (g t)) 0 = g t 0 := by simp
  have hYv : (pushY D εp 1 (g t)) 1 = g t 1 + εs * D := by
    rw [show (pushY D εp 1 (g t)) 1 = pushProf D εp 1 (g t 1) from by simp]
    exact pushProf_one_eq_of_sign hεs hεp (hregion t ht)
  refine ⟨?_, ?_⟩
  · rw [hYv, mul_add, ← mul_assoc, hsq, one_mul]
    linarith [hregion t ht, hDpos]
  · rw [hXd, hYd, hXv, hYv]
    have hMt : |mobiusRate g t| ≤ M := hMbound t ht
    have hct : deriv (fun u : ℝ => g u 0) t₀ ≤ deriv (fun u : ℝ => g u 0) t := ht₀min ht
    have heA : εs * mobiusRate g t ≤ M := by
      rcases hεs with rfl | rfl
      · calc (1 : ℝ) * mobiusRate g t = mobiusRate g t := one_mul _
          _ ≤ |mobiusRate g t| := le_abs_self _
          _ ≤ M := hMt
      · calc (-1 : ℝ) * mobiusRate g t = -mobiusRate g t := neg_one_mul _
          _ ≤ |mobiusRate g t| := neg_le_abs _
          _ ≤ M := hMt
    have hDc : M + deriv (fun u : ℝ => g u 0) t₀ ≤ D * deriv (fun u : ℝ => g u 0) t₀ := by
      have h1 : (M / deriv (fun u : ℝ => g u 0) t₀ + 1) * deriv (fun u : ℝ => g u 0) t₀
          = M + deriv (fun u : ℝ => g u 0) t₀ := by
        rw [add_mul, div_mul_cancel₀ M hc_pos.ne', one_mul]
      calc M + deriv (fun u : ℝ => g u 0) t₀
          = (M / deriv (fun u : ℝ => g u 0) t₀ + 1) * deriv (fun u : ℝ => g u 0) t₀ := h1.symm
        _ ≤ D * deriv (fun u : ℝ => g u 0) t₀ :=
            mul_le_mul_of_nonneg_right hD hc_pos.le
    -- the pushed rate is the original rate minus `D * x'`
    have hkey : εs * (g t 0 * deriv (fun u : ℝ => g u 1) t
        - (g t 1 + εs * D) * deriv (fun u : ℝ => g u 0) t)
        = εs * mobiusRate g t - D * deriv (fun u : ℝ => g u 0) t := by
      simp only [mobiusRate]
      linear_combination (-(D * deriv (fun u : ℝ => g u 0) t)) * hsq
    rw [hkey]
    have hstep : D * deriv (fun u : ℝ => g u 0) t₀ ≤ D * deriv (fun u : ℝ => g u 0) t :=
      mul_le_mul_of_nonneg_left hct hDpos.le
    linarith

/-- **The two model-picture rows with a uniform threshold.**  The conclusion is
`N2Lead.modelPicRate` with the quantifier order `∃ εp₀, ∃ D₀, ∀ εp ≤ εp₀, ∀ D ≥ D₀`, and with the
extra row `(modelPic … ζ).im ≠ 0` (the pushed arcs keep their `y`-sign). -/
theorem modelPicRowsUniform {η δ s a' ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    (hs : 0 < s) (ha' : 0 < a') (hε : 0 < ε)
    (hαsm : ContDiff ℝ 1 (mobiusAlpha η δ s a' ε))
    (hβsm : ContDiff ℝ 1 (mobiusBeta η δ s a' ε))
    (hαy : ∀ w ∈ Set.Icc (-2) 2, 0 < (mobiusAlpha η δ s a' ε w) 1)
    (hβy : ∀ w ∈ Set.Icc (-2) 2, (mobiusBeta η δ s a' ε w) 1 < 0)
    (hαx : ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun u : ℝ => (mobiusAlpha η δ s a' ε u) 0) w)
    (hβx : ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun u : ℝ => (mobiusBeta η δ s a' ε u) 0) w) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ → ∀ Dp : ℝ, D₀ ≤ Dp →
        ∀ (ζ w : ℂ), ζ ≠ 0 → (ζ ^ 2).re = s → |(ζ ^ 2).im| < 39 / 20 →
          (2 * ζ * w).re = 0 → w ≠ 0 →
            (modelPic η δ a' ε Dp εp ζ).im ≠ 0 ∧
            ¬ (∃ t : ℝ, (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) w
                = t • (modelPic η δ a' ε Dp εp ζ)) := by
  -- Step 1: the uniform rate rows of the two pushed arcs on `[-2,2]`
  obtain ⟨εpα, hεpα, Dα, hDα, hαrow⟩ :=
    pushedStarUniform (g := mobiusAlpha η δ s a' ε) (εs := (1 : ℝ)) (a := (-2 : ℝ)) (b := 2)
      hαsm (Or.inl rfl) (by norm_num) hαx (fun w hw => by simpa using hαy w hw)
  obtain ⟨εpβ, hεpβ, Dβ, hDβ, hβrow⟩ :=
    pushedStarUniform (g := mobiusBeta η δ s a' ε) (εs := (-1 : ℝ)) (a := (-2 : ℝ)) (b := 2)
      hβsm (Or.inr rfl) (by norm_num) hβx (fun w hw => by
        have h := hβy w hw
        simp only [neg_one_mul]
        linarith)
  refine ⟨min εpα εpβ, lt_min hεpα hεpβ, max Dα Dβ, le_max_of_le_left hDα, ?_⟩
  intro εp hεp hεple Dp hDp ζ w hζ hre him hperp hw
  set w₀ : ℝ := (ζ ^ 2).im with hw₀
  set μ : ℝ := (2 * ζ * w).im with hμ
  have hw₀mem : w₀ ∈ Set.Icc (-2 : ℝ) 2 := by
    have h1 := abs_lt.mp (by rw [hw₀]; exact him : |w₀| < 39 / 20)
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨ε₀, hε₀, hζeq⟩ := exists_levelRho_eq hζ hre
  rw [← hw₀] at hζeq
  -- the tangent data
  have h2ζw : 2 * ζ * w = (μ : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using hperp
    · simp [hμ]
  have hμne : μ ≠ 0 := by
    intro h0
    have hzero : (2 : ℂ) * ζ * w = 0 := by rw [h2ζw, h0]; simp
    have h2ζne : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ
    rcases mul_eq_zero.mp hzero with h | h
    · exact h2ζne h
    · exact hw h
  have hw_eq : w = μ • (Complex.I / (2 * ζ)) := by
    have h2ζne : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ
    have hdiv : w = (μ : ℂ) * Complex.I / (2 * ζ) := by
      rw [eq_div_iff h2ζne]
      rw [← h2ζw]
      ring
    rw [hdiv, Complex.real_smul, mul_div_assoc']
  -- the differentiability of the picture
  have hdiff : DifferentiableAt ℝ (modelPic η δ a' ε Dp εp) ζ :=
    (contDiff_modelPic (η := η) (δ := δ) (a' := a') (ε := ε) (Dp := Dp) (εp := εp) hδ hδ₂)
      |>.differentiable (by simp) |>.differentiableAt
  rcases modelPic_level_local (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp)
      (εp := εp) (ε₀ := ε₀) (w₀ := w₀) hδ hδ₂ hs hε₀ with ⟨hsp, hev⟩ | ⟨hsp, hev⟩
  · -- the `α` branch (the sign `-1`)
    have hval : modelPic η δ a' ε Dp εp ζ
        = proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε w₀)) := by
      rw [hζeq]
      exact modelPic_of_saddlePsi_eq_neg hsp
    have hchain : HasDerivAt (fun u : ℝ => modelPic η δ a' ε Dp εp (ε₀ * levelRho s u))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ := by
      have hρ' : HasDerivAt (fun u : ℝ => ε₀ * levelRho s u)
          (ε₀ * (Complex.I / (2 * levelRho s w₀))) w₀ :=
        (hasDerivAt_levelRho (s := s) hs w₀).const_mul (ε₀ : ℂ)
      have hfd : HasFDerivAt (modelPic η δ a' ε Dp εp)
          (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (ε₀ * levelRho s w₀) := by
        rw [hζeq.symm]
        exact hdiff.hasFDerivAt
      have hc : Complex.I / (2 * ζ) = ε₀ * (Complex.I / (2 * levelRho s w₀)) := by
        have hx : levelRho s w₀ ≠ 0 := levelRho_ne_zero (u := w₀) hs
        have hesq : (ε₀ : ℂ) * (ε₀ : ℂ) = 1 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        have hene : (ε₀ : ℂ) ≠ 0 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        rw [hζeq]
        field_simp
        rw [pow_two]
        exact hesq.symm
      rw [hc]
      exact hfd.comp_hasDerivAt w₀ hρ'
    have hg : HasDerivAt (fun u : ℝ => proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε u)))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ :=
      hchain.congr_of_eventuallyEq (by
        filter_upwards [hev] with u hu
        exact hu.symm)
    obtain ⟨hpos, hrow⟩ :=
      hαrow εp hεp (le_trans hεple (min_le_left _ _)) Dp
        (le_trans (le_max_left _ _) hDp) w₀ hw₀mem
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 : (pushY Dp εp 1 (mobiusAlpha η δ s a' ε w₀)) 1 = 0 := by
        have h2 : (proj2 (pushY Dp εp 1 (mobiusAlpha η δ s a' ε w₀))).im = 0 := by
          rw [← hval]; exact h0
        simpa [proj2] using h2
      rw [h1, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · intro ht
      exact not_realMultiple_of_det
        (rate_step (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp) (εp := εp)
          (ζ := ζ) (w := w) (u₀ := w₀) (μ := μ) (g := mobiusAlpha η δ s a' ε) (εs := 1)
          hg hval hμne hw_eq hrow (Or.inl rfl)) ht
  · -- the `β` branch (the sign `+1`)
    have hval : modelPic η δ a' ε Dp εp ζ
        = proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε w₀)) := by
      rw [hζeq]
      exact modelPic_of_saddlePsi_eq hsp
    have hchain : HasDerivAt (fun u : ℝ => modelPic η δ a' ε Dp εp (ε₀ * levelRho s u))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ := by
      have hρ' : HasDerivAt (fun u : ℝ => ε₀ * levelRho s u)
          (ε₀ * (Complex.I / (2 * levelRho s w₀))) w₀ :=
        (hasDerivAt_levelRho (s := s) hs w₀).const_mul (ε₀ : ℂ)
      have hfd : HasFDerivAt (modelPic η δ a' ε Dp εp)
          (fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (ε₀ * levelRho s w₀) := by
        rw [hζeq.symm]
        exact hdiff.hasFDerivAt
      have hc : Complex.I / (2 * ζ) = ε₀ * (Complex.I / (2 * levelRho s w₀)) := by
        have hx : levelRho s w₀ ≠ 0 := levelRho_ne_zero (u := w₀) hs
        have hesq : (ε₀ : ℂ) * (ε₀ : ℂ) = 1 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        have hene : (ε₀ : ℂ) ≠ 0 := by
          rcases hε₀ with rfl | rfl <;> norm_num
        rw [hζeq]
        field_simp
        rw [pow_two]
        exact hesq.symm
      rw [hc]
      exact hfd.comp_hasDerivAt w₀ hρ'
    have hg : HasDerivAt (fun u : ℝ => proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε u)))
        ((fderiv ℝ (modelPic η δ a' ε Dp εp) ζ) (Complex.I / (2 * ζ))) w₀ :=
      hchain.congr_of_eventuallyEq (by
        filter_upwards [hev] with u hu
        exact hu.symm)
    obtain ⟨hpos, hrow⟩ :=
      hβrow εp hεp (le_trans hεple (min_le_right _ _)) Dp
        (le_trans (le_max_right _ _) hDp) w₀ hw₀mem
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 : (pushY Dp εp 1 (mobiusBeta η δ s a' ε w₀)) 1 = 0 := by
        have h2 : (proj2 (pushY Dp εp 1 (mobiusBeta η δ s a' ε w₀))).im = 0 := by
          rw [← hval]; exact h0
        simpa [proj2] using h2
      rw [h1, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · intro ht
      exact not_realMultiple_of_det
        (rate_step (η := η) (δ := δ) (s := s) (a' := a') (ε := ε) (Dp := Dp) (εp := εp)
          (ζ := ζ) (w := w) (u₀ := w₀) (μ := μ) (g := mobiusBeta η δ s a' ε) (εs := -1)
          hg hval hμne hw_eq hrow (Or.inr rfl)) ht

theorem mobiusModelPieceRows {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ Real.sqrt (S.a' ^ 2 + Work.Drive.N2.packetEta D η)) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ →
      ∀ Dp : ℝ, D₀ ≤ Dp →
      ∀ (y : M) (v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y),
        f y = f p + 3 * η / 2 →
        y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20) →
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
        v ≠ 0 →
        (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)).im ≠ 0 ∧
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)) := by
  -- ## the constants
  set δ : ℝ := 1 / 20 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; norm_num
  have hδ₁ : δ < 1 / 10 := by rw [hδdef]; norm_num
  have hδ₂ : δ < 1 / 2 := by rw [hδdef]; norm_num
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  have hs : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hηs₁ : ηs < 3 / 800 := by
    rw [hηsdef]; exact packetEta_lt_three_eightieth D hsmall
  have hηs₂ : ηs < 1 / 10 := by linarith
  -- ## the bound on the slope of the smooth transition
  have hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ (3 : ℝ) :=
    fun x => le_trans (Work.N2Lead.absDerivSmoothTransitionLeTwo x) (by norm_num)
  have hsmall' : 4 * (3 : ℝ) * ηs ≤ δ := by rw [hδdef]; linarith
  -- ## the arc rows
  obtain ⟨harc1, harc2⟩ := mobius_upperArcs (η := ηs) (δ := δ) (s := ηs) (a' := S.a') (ε := ε)
    (C₀ := 3) hδ hδ₁ hs hηs₂ hs le_rfl hC₀ hsmall' S.ha'pos hε hεa
  have hαsm : ContDiff ℝ 1 (mobiusAlpha ηs δ ηs S.a' ε) :=
    mobiusAlpha_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := ε) hδ hδ₂ hs
  have hβsm : ContDiff ℝ 1 (mobiusBeta ηs δ ηs S.a' ε) :=
    mobiusBeta_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := ε) hδ hδ₂ hs
  have hαy : ∀ w ∈ Set.Icc (-2) 2, 0 < (mobiusAlpha ηs δ ηs S.a' ε w) 1 :=
    fun w hw => (harc1 w hw).1
  have hβy : ∀ w ∈ Set.Icc (-2) 2, (mobiusBeta ηs δ ηs S.a' ε w) 1 < 0 :=
    fun w hw => (harc1 w hw).2
  have hαx : ∀ w ∈ Set.Icc (-2) 2,
      0 < deriv (fun u : ℝ => (mobiusAlpha ηs δ ηs S.a' ε u) 0) w :=
    fun w hw => (harc2 w hw).1
  have hβx : ∀ w ∈ Set.Icc (-2) 2,
      0 < deriv (fun u : ℝ => (mobiusBeta ηs δ ηs S.a' ε u) 0) w :=
    fun w hw => (harc2 w hw).2
  -- ## the uniform model rows
  obtain ⟨εp₀, hεp₀pos, D₀, hD₀nn, hrows⟩ :=
    modelPicRowsUniform (η := ηs) (δ := δ) (s := ηs) (a' := S.a') (ε := ε)
      hs hδ hδ₂ hs S.ha'pos hε hαsm hβsm hαy hβy hαx hβx
  refine ⟨εp₀, hεp₀pos, D₀, hD₀nn, ?_⟩
  intro εp hεp hεple Dp hDp y v hy hreg hv hvne
  -- ## the geometric data at `y`
  have hUopen : IsOpen (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) :=
    isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)
  have hZdiff : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) S.Z y :=
    (S.hZsm.contMDiffAt (hUopen.mem_nhds hreg.1)).mdifferentiableAt (by simp)
  have hZc : ContinuousAt S.Z y := hZdiff.continuousAt
  have hζre : ((S.Z y) ^ 2).re = ηs := by
    have hlaw := lam0_sq_mul_packetEta (D := D) S
    have hne : S.lam0 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt S.hlam0pos)
    have h2 : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = S.lam0 ^ 2 * ηs := by
      have h3 : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = 3 * η / 2 := by
        have h4 := S.hlev y hreg.1
        rw [hy] at h4
        linarith
      rw [h3, hlaw]
    exact mul_left_cancel₀ hne h2
  have hζne : S.Z y ≠ 0 := by
    intro h0
    have hpos : 0 < ((S.Z y) ^ 2).re := by rw [hζre]; exact hs
    rw [h0] at hpos; simp at hpos
  have hζim : |((S.Z y) ^ 2).im| < 39 / 20 := hreg.2
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) S.Z y v := ⟨_, rfl⟩
  have hwne : w ≠ 0 := by
    intro h0
    refine hvne (S.hZimm y hreg.1 ?_)
    rw [← hwdef, h0, map_zero]
    rfl
  -- ## the level condition, transported to the chart
  have hμ : (2 * S.Z y * w).re = 0 := by
    have hfeq : f =ᶠ[𝓝 y] (fun z : M => f p + S.lam0 ^ 2 * ((S.Z z) ^ 2).re) := by
      filter_upwards [hUopen.mem_nhds hreg.1] with z hz
      exact S.hlev z hz
    have h1p : mfderiv (𝓡 2) 𝓘(ℝ,ℝ)
        (fun z : M => f p + S.lam0 ^ 2 * ((S.Z z) ^ 2).re) y v = 0 := by
      rw [← hfeq.mfderiv_eq_v433]; exact hv
    have hqc : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ)
        (fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y) :=
      (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
    have h1raw : (fderiv ℝ (fun ζ : ℂ => S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y))
        (mfderiv (𝓡 2) 𝓘(ℝ,ℂ) S.Z y v) = 0 := by
      have h1' : mfderiv (𝓡 2) 𝓘(ℝ,ℝ)
          ((fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) ∘ S.Z) y v = 0 := h1p
      rw [mfderiv_comp_apply (f := S.Z)
        (g := fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) y hqc hZdiff v] at h1'
      rw [mfderiv_eq_fderiv, fderiv_const_add] at h1'
      exact h1'
    have h1'' : (fderiv ℝ (fun ζ : ℂ => S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y)) w = 0 := by
      rw [hwdef]; exact h1raw
    rw [Work.Drive.N2.fderiv_smul_sq_re_apply] at h1''
    rcases mul_eq_zero.mp h1'' with h | h
    · exact absurd h (pow_ne_zero 2 (ne_of_gt S.hlam0pos))
    · exact h
  -- ## the germ equality with the plane model
  have hsplit : ∀ᶠ z in 𝓝 y, |((S.Z z) ^ 2).im| < 39 / 20 := by
    have hφ : ContinuousAt (fun ζ : ℂ => |(ζ ^ 2).im|) (S.Z y) :=
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.pow 2))).continuousAt
    exact (hφ.tendsto.comp hZc.tendsto) (isOpen_Iio.mem_nhds hreg.2)
  have hgerm : (fun z : M => Work.Drive.N2Lead.proj2
        (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z))
      =ᶠ[𝓝 y] (fun z : M => modelPic ηs δ S.a' ε Dp εp (S.Z z)) := by
    filter_upwards [hUopen.mem_nhds hreg.1, hsplit] with z hz1 hz2
    have hmem : z ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20) := ⟨hz1, hz2⟩
    simp only [Work.Drive.N2Lead.mobiusTwisted, Work.Drive.N2Lead.mobiusWindowDrawing,
      Work.Drive.N2Lead.modelPic, if_pos hmem, hηsdef, hδdef]
  have hval : Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
      = modelPic ηs δ S.a' ε Dp εp (S.Z y) := hgerm.eq_of_nhds
  -- ## the chain rule
  have hKdiff : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (modelPic ηs δ S.a' ε Dp εp) (S.Z y) :=
    ((contDiff_modelPic (η := ηs) (δ := δ) (a' := S.a') (ε := ε) (Dp := Dp) (εp := εp)
      hδ hδ₂).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hchain : (fderiv ℝ (modelPic ηs δ S.a' ε Dp εp) (S.Z y)) w
      = mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => modelPic ηs δ S.a' ε Dp εp (S.Z z)) y v := by
    have h := mfderiv_comp_apply (f := S.Z) (g := modelPic ηs δ S.a' ε Dp εp) y hKdiff hZdiff v
    simp only [mfderiv_eq_fderiv] at h
    rw [hwdef]
    exact h.symm
  -- ## the two rows
  obtain ⟨him, hrate⟩ := hrows εp hεp hεple Dp hDp (S.Z y) w hζne hζre hζim hμ hwne
  refine ⟨?_, ?_⟩
  · intro h0
    exact him (by rw [← hval]; exact h0)
  · rintro ⟨t, ht⟩
    have hkey : mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => modelPic ηs δ S.a' ε Dp εp (S.Z z)) y v
        = t • (modelPic ηs δ S.a' ε Dp εp (S.Z y)) := by
      have hc : (mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
            (fun z : M => modelPic ηs δ S.a' ε Dp εp (S.Z z)) y) v
          = (mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2
              (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y) v :=
        congrArg (fun L : TangentSpace (𝓡 2) y →L[ℝ] ℂ => L v) hgerm.mfderiv_eq_v433.symm
      exact hc.trans (ht.trans (congrArg (fun z : ℂ => t • z) hval))
    have hfin : (fderiv ℝ (modelPic ηs δ S.a' ε Dp εp) (S.Z y)) w
        = t • (modelPic ηs δ S.a' ε Dp εp (S.Z y)) := by
      rw [hchain]; exact hkey
    exact hrate ⟨t, hfin⟩

end

end Work.Drive.N2C
