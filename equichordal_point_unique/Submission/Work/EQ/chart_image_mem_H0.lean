import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

open Metric Set Complex

/-- **Existence of a local continuous `k`-th root of `(w - u)/κ`.**

For `k > 0`, `κ ≠ 0`, `t ≠ 0` and `‖t‖ < ρ`, there is a radius `ε > 0` and a function
`r : ℂ → ℂ` which is continuous on `ball (u + κ t^k) ε`, takes the value `t` at `u + κ t^k`,
maps that ball into the punctured disc `ball 0 ρ \ {0}`, and is a `k`-th root of `(· - u)/κ` there:
`(r w)^k = (w - u)/κ` for all `w ∈ ball (u + κ t^k) ε`.

The construction is `r w = t * exp ((1/k) * log ((w - u)/(κ t^k)))` on a ball on which
`(w - u)/(κ t^k)` stays in the slit plane (near `1`, since `u + κ t^k - u = κ t^k`); continuity of
`Complex.log` there gives the continuity, `exp`/`log` give the `k`-th root identity, and the
`MapsTo` part is a shrinking of the radius using continuity at `u + κ t^k`. -/
theorem chart_root_local_aux {k : ℕ} (hk : 0 < k) {u κ : ℂ} (hκ : κ ≠ 0) {t : ℂ}
    (ht0 : 0 < ‖t‖) {ρ : ℝ} (htρ : ‖t‖ < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℂ → ℂ, ContinuousOn r (Metric.ball (u + κ * t ^ k) ε) ∧
      r (u + κ * t ^ k) = t ∧
      Set.MapsTo r (Metric.ball (u + κ * t ^ k) ε) (Metric.ball 0 ρ \ {0}) ∧
      ∀ w ∈ Metric.ball (u + κ * t ^ k) ε, (r w) ^ k = (w - u) / κ := by
  have htne : t ≠ 0 := norm_pos_iff.mp ht0
  have htpow : t ^ k ≠ 0 := pow_ne_zero k htne
  let w0 : ℂ := u + κ * t ^ k
  let D : ℂ := κ * t ^ k
  have hD0 : D ≠ 0 := by dsimp only [D]; exact mul_ne_zero hκ htpow
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have hw0sub : w0 - u = D := by dsimp only [w0, D]; ring
  let G : ℂ → ℂ := fun w => (w - u) / D
  let hh : ℂ → ℂ := fun w => Complex.exp ((k : ℂ)⁻¹ * Complex.log (G w))
  let r : ℂ → ℂ := fun w => t * hh w
  have hGcont : ContinuousOn G (Metric.ball w0 (‖D‖ / 2)) := by
    dsimp only [G]
    exact (continuousOn_id.sub continuousOn_const).div_const D
  have hslit : ∀ w ∈ Metric.ball w0 (‖D‖ / 2), G w ∈ Complex.slitPlane := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hz : ‖(w - w0) / D‖ < 1 / 2 := by
      rw [norm_div, div_lt_iff₀ hDpos]
      linarith
    have hGw : G w = 1 + (w - w0) / D := by
      dsimp only [G]
      have h1 : w - u = (w - w0) + D := by rw [← hw0sub]; ring
      rw [h1, add_div, div_self hD0]; ring
    have hre : 0 < (G w).re := by
      rw [hGw, Complex.add_re, Complex.one_re]
      have h2 : -(((w - w0) / D).re) ≤ ‖(w - w0) / D‖ := by
        have := (abs_le.mp (Complex.abs_re_le_norm ((w - w0) / D))).1
        linarith
      linarith
    exact Or.inl hre
  have hlogcont : ContinuousOn (fun w => Complex.log (G w)) (Metric.ball w0 (‖D‖ / 2)) :=
    hGcont.clog hslit
  have hhcont : ContinuousOn hh (Metric.ball w0 (‖D‖ / 2)) := by
    dsimp only [hh]
    exact Complex.continuous_exp.comp_continuousOn (hlogcont.const_mul (k : ℂ)⁻¹)
  have hrcont : ContinuousOn r (Metric.ball w0 (‖D‖ / 2)) := by
    dsimp only [r]
    exact hhcont.const_mul t
  have hG1 : G w0 = 1 := by dsimp only [G]; rw [hw0sub, div_self hD0]
  have hhw0 : hh w0 = 1 := by
    dsimp only [hh]
    rw [hG1, Complex.log_one, mul_zero, Complex.exp_zero]
  have hrw0 : r w0 = t := by dsimp only [r]; rw [hhw0, mul_one]
  have hrpow : ∀ w ∈ Metric.ball w0 (‖D‖ / 2), (r w) ^ k = (w - u) / κ := by
    intro w hw
    have hGw : G w ≠ 0 := Complex.slitPlane_ne_zero (hslit w hw)
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
    have hp : (hh w) ^ k = G w := by
      dsimp only [hh]
      rw [← Complex.exp_nat_mul]
      have harg : (k : ℂ) * ((k : ℂ)⁻¹ * Complex.log (G w)) = Complex.log (G w) := by
        rw [← mul_assoc, mul_inv_cancel₀ hkC, one_mul]
      rw [harg, Complex.exp_log hGw]
    dsimp only [r]
    rw [mul_pow, hp]
    dsimp only [G, D]
    field_simp
  have hδ : 0 < min ‖t‖ (ρ - ‖t‖) / 2 := by
    have hρt : 0 < ρ - ‖t‖ := sub_pos.mpr htρ
    exact div_pos (lt_min ht0 hρt) two_pos
  have hcontAt : ContinuousAt r w0 :=
    hrcont.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hDpos)))
  obtain ⟨ε₂, hε₂pos, hε₂⟩ :=
    Metric.continuousAt_iff.mp hcontAt (min ‖t‖ (ρ - ‖t‖) / 2) hδ
  refine ⟨min (‖D‖ / 2) ε₂, lt_min (half_pos hDpos) hε₂pos, r, ?_, hrw0, ?_, ?_⟩
  · exact hrcont.mono (Metric.ball_subset_ball (min_le_left _ _))
  · intro w hw
    have hwm : ‖w - w0‖ < min (‖D‖ / 2) ε₂ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
    have hw1 : w ∈ Metric.ball w0 (‖D‖ / 2) := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hwm (min_le_left _ _)
    have hwlt : ‖w - w0‖ < ‖D‖ / 2 := lt_of_lt_of_le hwm (min_le_left _ _)
    have hw2 : dist w w0 < ε₂ := by
      rw [dist_eq_norm]; exact lt_of_lt_of_le hwm (min_le_right _ _)
    have hdist : dist (r w) t < min ‖t‖ (ρ - ‖t‖) / 2 := by
      have := hε₂ hw2; rwa [hrw0] at this
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖r w - t‖ < min ‖t‖ (ρ - ‖t‖) / 2 := by rwa [dist_eq_norm] at hdist
      have h3 : ‖r w‖ ≤ ‖r w - t‖ + ‖t‖ := by
        calc ‖r w‖ = ‖(r w - t) + t‖ := by ring_nf
          _ ≤ ‖r w - t‖ + ‖t‖ := norm_add_le _ _
      have h4 : min ‖t‖ (ρ - ‖t‖) ≤ ρ - ‖t‖ := min_le_right _ _
      linarith
    · intro hzero
      rw [Set.mem_singleton_iff] at hzero
      have hwu : w ≠ u := by
        intro hwu
        have hDle : ‖D‖ ≤ ‖w - u‖ + ‖w - w0‖ := by
          have := norm_sub_le (w - u) (w - w0)
          rwa [show (w - u) - (w - w0) = D by rw [← hw0sub]; ring] at this
        have hpos : 0 < ‖w - u‖ := by linarith
        rw [hwu, sub_self, norm_zero] at hpos
        exact lt_irrefl 0 hpos
      have hne : (w - u) / κ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hwu) hκ
      have hp := hrpow w hw1
      rw [hzero, zero_pow (ne_of_gt hk)] at hp
      exact hne hp.symm
  · intro w hw
    exact hrpow w (Metric.ball_subset_ball (min_le_left _ _) hw)

/-- **The values of a punctured chart lie in `H0`.**

Let `E` be a chain family on a punctured disc with `ψ₁ (E t) = u + κ t ^ k`, `u ≠ 0`, `κ ≠ 0`, and
let `e` be a reparametrisation of `E` with `ψ₁ (e ζ) = u + κ' ζ ^ k` whose image contains all of `E`
on the punctured disc of radius `τ ≤ ρ`.  Then every value of `e` on the punctured unit disc lies in
`H0`.

Route: `e ζ = E t` for some `t` in the punctured disc, and `ψ₁ (E t) = u + κ t ^ k ≠ u`; near
`w₀ = ψ₁ (E t) ≠ u` there is a holomorphic `k`-th root `r` of `(w - u) / κ` with `r w₀ = t`, and
the map `w ↦ E (r w)` is a continuous local section of `ψ₁` through `E t` whose values are chains,
so `E t ∈ H0` by the definition of `H0`. -/
theorem chart_image_mem_H0 {a : ℝ} {h : ℂ → ℂ} {u : ℂ} {κ : ℂ} {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {E : ℂ → Work.EQ.ChainData}
    (hE : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → Work.EQ.IsChain a h (E t))
    (hψ : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → (E t).2.1 = u + κ * t ^ k)
    (hcont : ContinuousOn E (Metric.ball (0 : ℂ) ρ \ {0}))
    {κ' : ℂ} (hκ' : κ' ≠ 0) {e : ℂ → Work.EQ.ChainData} {τ : ℝ} (hτ : 0 < τ) (hτρ : τ ≤ ρ)
    (hψe : ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, (e ζ).2.1 = u + κ' * ζ ^ k)
    (him : ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, ∃ t : ℂ, 0 < ‖t‖ ∧ ‖t‖ < τ ∧ E t = e ζ)
    (hκ : κ ≠ 0) (hk : 0 < k) (hu : u ≠ 0) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, e ζ ∈ Work.EQ.H0 a h := by
  intro ζ hζ
  obtain ⟨t, ht0, htt, hEt⟩ := him ζ hζ
  have htρ : ‖t‖ < ρ := lt_of_lt_of_le htt hτρ
  let w0 : ℂ := u + κ * t ^ k
  have hp1 : (e ζ).2.1 = w0 := by
    dsimp only [w0]; rw [← hEt]; exact hψ t ht0 htρ
  obtain ⟨ε₁, hε₁pos, r, hrcont, hrw0, hrmaps, hrpow⟩ :=
    chart_root_local_aux hk hκ ht0 htρ
  have hcont' : ContinuousOn r (Metric.ball w0 ε₁) := hrcont
  have hrmaps' : Set.MapsTo r (Metric.ball w0 ε₁) (Metric.ball 0 ρ \ {0}) := hrmaps
  have hrpow' : ∀ w ∈ Metric.ball w0 ε₁, (r w) ^ k = (w - u) / κ := hrpow
  refine ⟨ε₁, hε₁pos, (fun w => E (r w)), ?_, ?_, ?_⟩
  · rw [hp1]
    exact hcont.comp hcont' hrmaps'
  · show E (r ((e ζ).2.1)) = e ζ
    rw [hp1, hrw0, hEt]
  · intro ξ hξ
    rw [hp1] at hξ
    have hξmem := hrmaps' hξ
    have hrne : r ξ ≠ 0 := by
      intro hz
      exact hξmem.2 (by simpa using hz)
    have hr0 : 0 < ‖r ξ‖ := norm_pos_iff.mpr hrne
    have hrρ : ‖r ξ‖ < ρ := by
      have := hξmem.1
      rwa [Metric.mem_ball, dist_zero_right] at this
    refine ⟨hE (r ξ) hr0 hrρ, ?_⟩
    have hpsi := hψ (r ξ) hr0 hrρ
    have hpw := hrpow' ξ hξ
    rw [hpsi, hpw]
    field_simp
    ring

end Work.EQ
