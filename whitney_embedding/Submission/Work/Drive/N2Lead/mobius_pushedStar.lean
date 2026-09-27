import Mathlib
import Submission.Work.Drive.N2Lead.mobiusArcDefs
import Submission.Work.Drive.N2Lead.twistToolkit

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## The compactness step behind `mobius_pushedStar`

The push `pushY D εp 1` has the vertical profile `pushProf D εp 1` of `twistToolkit.lean`.  On the
side of the band where the level lies (`εs * y ≥ εp`, `εs = ±1`) the profile is the *rigid*
translation `y ↦ y + εs * D`, so the angular rate `x · y' - y · x'` of the pushed curve becomes
`(x · y' - y · x') - εs * D · x'`, and the strictly positive derivative `x'` together with a bound on
`x · y' - y · x'` over the compact parameter interval `Icc (-2) 2` gives the threshold `D₀`. -/

/-- The **angular rate** `x * y' - y * x'` of the planar projection of a curve `g : ℝ → ℝ³`, i.e. the
derivative of the argument of `x + i y` along `g`.  It is the quantity whose sign is the
star-shapedness certificate `StarAboutZero`. -/
def mobiusRate (g : ℝ → E3) (w : ℝ) : ℝ :=
  g w 0 * deriv (fun u : ℝ => g u 1) w - g w 1 * deriv (fun u : ℝ => g u 0) w

/-- The vertical profile of the push at `s = 1` is the rigid translation `y ↦ y + D` on the far side
`εp ≤ y` of the band. -/
theorem pushProf_one_eq_of_le {D εp : ℝ} (hεp : 0 < εp) {y : ℝ} (hy : εp ≤ y) :
    pushProf D εp 1 y = y + D := by
  rw [pushProf_eq_of_one_le hεp hy, Real.smoothTransition.one_of_one_le le_rfl, one_mul]

/-- The vertical profile of the push at `s = 1` is the rigid translation `y ↦ y - D` on the far side
`y ≤ -εp` of the band. -/
theorem pushProf_one_eq_of_nonpos {D εp : ℝ} (hεp : 0 < εp) {y : ℝ} (hy : y ≤ -εp) :
    pushProf D εp 1 y = y - D := by
  rw [pushProf_eq_of_nonpos hεp hy, Real.smoothTransition.one_of_one_le le_rfl, one_mul]

/-- The sign form of the two lemmas above: on the side `εp ≤ εs * y` (`εs = ±1`) the profile is the
rigid translation `y ↦ y + εs * D`. -/
theorem pushProf_one_eq_of_sign {D εp εs y : ℝ} (hεs : εs = 1 ∨ εs = -1) (hεp : 0 < εp)
    (hy : εp ≤ εs * y) : pushProf D εp 1 y = y + εs * D := by
  rcases hεs with rfl | rfl
  · rw [pushProf_one_eq_of_le hεp (by simpa using hy), one_mul]
  · rw [pushProf_one_eq_of_nonpos hεp (by linarith), neg_one_mul]; ring

/-- Consequently, on the side of the band, the derivative of the pushed `y`-coordinate is the
derivative of the original one: the two functions agree near `t`. -/
theorem deriv_pushProf_one_comp_of_sign {g : ℝ → E3} {D εp εs t : ℝ}
    (hεs : εs = 1 ∨ εs = -1) (hεp : 0 < εp) (hreg : ∀ᶠ u in 𝓝 t, εp ≤ εs * g u 1) :
    deriv (fun u : ℝ => pushProf D εp 1 (g u 1)) t = deriv (fun u : ℝ => g u 1) t := by
  have hev : (fun u : ℝ => pushProf D εp 1 (g u 1)) =ᶠ[𝓝 t] (fun u : ℝ => g u 1 + εs * D) := by
    filter_upwards [hreg] with u hu
    exact pushProf_one_eq_of_sign hεs hεp hu
  rw [hev.deriv_eq, deriv_add_const]

theorem continuous_coord {g : ℝ → E3} (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    Continuous (fun w : ℝ => g w i) :=
  (EuclideanSpace.proj i).continuous.comp hg.continuous

/-- For a `C¹` curve the derivative of a coordinate is again continuous: `t ↦ (fderiv g t) 1` is a
continuous linear functional applied to a fixed vector, and `fderiv g` is continuous because `g` is
`C¹`. -/
theorem continuous_deriv_coord {g : ℝ → E3} (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    Continuous (deriv (fun u : ℝ => g u i)) := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => g u i) :=
    ContDiff.continuousLinearMap_comp (EuclideanSpace.proj i) hg
  have h2 := h1.continuous_fderiv (by norm_num)
  exact h2.clm_apply continuous_const

/-- The angular rate `mobiusRate g` is continuous for a `C¹` curve. -/
theorem continuous_mobiusRate {g : ℝ → E3} (hg : ContDiff ℝ 1 g) :
    Continuous (mobiusRate g) := by
  have h := (continuous_coord hg 0).mul (continuous_deriv_coord hg 1)
  have h' := (continuous_coord hg 1).mul (continuous_deriv_coord hg 0)
  exact h.sub h'

end


open scoped Manifold ContDiff Topology in
/-- **Tier `D2d.4c`: the push makes the twisted arcs star-shaped about the origin.**

For a `C¹` curve `g : ℝ → ℝ³` whose `x`-coordinate is strictly increasing in the parameter and which
lies strictly in an open half-plane `εs * g t 1 > 0` (`εs = ±1`), the vertical push `pushY D εp 1`
(rigid off `|for y| < εp`, shifting a point by `εs * D` when `εs * y > 0`) makes the angular rate
`x y' - y x'` have the constant sign `-εs` on `Icc (-2) 2`, for every push size `D` above a threshold
`D₀` and every half-width `εp` below a threshold `εp₀`.  Consequently
`StarAboutZero (pushY D εp 1 ∘ g) (Icc (-2) 2)`.

This is the compactness step of `N2Lead/NOTES_LEAD_mobiusSaddle.md` §2.4/`D2d.4`: the rate becomes
`(x y' - y x') - εs * D * x'`, and `0 < c ≤ x'`, `|x y' - y x'| ≤ M` on the compact parameter interval
give `D₀`; `εp₀` is the minimum of `|g · 1|`.  It is applied to the two arcs of
`Work.Drive.N2Lead.mobius_upperArcs` (`εs = 1` for the arc `α = twist (-ρ)`, `εs = -1` for
`β = twist (ρ)`) and, in the assembly, also to the polar side pieces of the parked picture, which is
why the statement is made for an abstract `g` rather than for the arcs alone. -/
theorem mobius_pushedStar {g : ℝ → E3} {εs : ℝ}
    (hg : ContDiff ℝ 1 g) (hεs : εs = 1 ∨ εs = -1)
    (hgx : ∀ w ∈ Set.Icc (-2) 2, 0 < deriv (fun u : ℝ => g u 0) w)
    (hgy : ∀ w ∈ Set.Icc (-2) 2, 0 < εs * g w 1) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ →
      ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        StarAboutZero (fun t : ℝ => pushY D εp 1 (g t)) (Set.Icc (-2) 2) ∧
          ∀ t ∈ Set.Icc (-2) 2,
            εs * ((pushY D εp 1 (g t)) 0 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t
              - (pushY D εp 1 (g t)) 1 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t) < 0 := by
  have hIcc_ne : (Set.Icc (-2:ℝ) 2).Nonempty := ⟨0, by constructor <;> norm_num⟩
  -- the `y`-coordinate of `g` does not vanish on the compact parameter interval
  have habs : ∀ w ∈ Set.Icc (-2:ℝ) 2, |g w 1| = εs * g w 1 := by
    intro w hw
    rcases hεs with rfl | rfl
    · rw [one_mul]; exact abs_of_pos (by linarith [hgy w hw])
    · rw [neg_one_mul]; exact abs_of_neg (by linarith [hgy w hw])
  have hcont_abs : Continuous (fun w : ℝ => |g w 1|) := (continuous_coord hg 1).abs
  obtain ⟨w₀, hw₀mem, hw₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcont_abs.continuousOn
  have hm_pos : 0 < |g w₀ 1| := by rw [habs w₀ hw₀mem]; exact hgy w₀ hw₀mem
  refine ⟨|g w₀ 1| / 2, by linarith, ?_⟩
  intro εp hεp hεp_le
  -- the whole interval lies in the good side of the band
  have hregion : ∀ w ∈ Set.Icc (-2:ℝ) 2, εp ≤ εs * g w 1 := by
    intro w hw
    have h1 : |g w₀ 1| ≤ |g w 1| := hw₀min hw
    have h2 : 2 * εp ≤ |g w₀ 1| := by linarith
    rw [← habs w hw]; linarith
  -- a bound on the angular rate over the compact interval
  obtain ⟨M, hMnonneg, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Set.Icc (-2:ℝ) 2, |mobiusRate g w| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_mobiusRate hg).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
    exact le_trans (by simpa [Real.norm_eq_abs] using hM w hw) (le_max_left _ _)
  -- a strictly positive lower bound on the `x`-derivative over the compact interval
  obtain ⟨t₀, ht₀mem, ht₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne (continuous_deriv_coord hg 0).continuousOn
  have hc_pos : 0 < deriv (fun u : ℝ => g u 0) t₀ := hgx t₀ ht₀mem
  have hD₀pos : 0 < M / deriv (fun u : ℝ => g u 0) t₀ + 1 := by positivity
  refine ⟨M / deriv (fun u : ℝ => g u 0) t₀ + 1, hD₀pos, ?_⟩
  intro D hD
  have hDpos : 0 < D := by linarith
  -- the pointwise sign of the pushed angular rate
  have hmain : ∀ t ∈ Set.Icc (-2:ℝ) 2,
      εs * ((pushY D εp 1 (g t)) 0 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t
        - (pushY D εp 1 (g t)) 1 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t) < 0 := by
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
    rw [hXd, hYd, hXv, hYv]
    -- the threshold
    have hsq : εs * εs = 1 := by rcases hεs with rfl | rfl <;> norm_num
    have hMt : |mobiusRate g t| ≤ M := hMbound t ht
    have hct : deriv (fun u : ℝ => g u 0) t₀ ≤ deriv (fun u : ℝ => g u 0) t := ht₀min ht
    have heA : εs * mobiusRate g t ≤ M := by
      rcases hεs with rfl | rfl
      · calc (1:ℝ) * mobiusRate g t = mobiusRate g t := one_mul _
          _ ≤ |mobiusRate g t| := le_abs_self _
          _ ≤ M := hMt
      · calc (-1:ℝ) * mobiusRate g t = -mobiusRate g t := neg_one_mul _
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
  refine ⟨?_, hmain⟩
  -- `StarAboutZero` is the case analysis on the sign of `-εs`
  rcases hεs with rfl | rfl
  · right
    intro t ht
    simpa using hmain t ht
  · left
    intro t ht
    have := hmain t ht
    linarith


end Work.Drive.N2Lead
