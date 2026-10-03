import Mathlib
import Submission.Work.Param.Basic
import Submission.Work.Escape.exists_differentiableOn_ball_clog

namespace Work.Param

open Work.Escape
open Filter
open scoped Topology

noncomputable section

/-- **One step of the analytic continuation of the Koenigs map.**  Suppose `ψ` is holomorphic on
`Metric.ball 0 R` (`0 < R`), satisfies `Q l (ψ w) = ψ (l * w)` there, with `ψ 0 = 0`,
`deriv ψ 0 = 1`, and suppose moreover that the critical value `-l^2/4` is not attained by `ψ` on
that ball.  Then `ψ` extends, with the same functional equation and the same normalisation, to the
ball of radius `R / ‖l‖ > R`; on `Metric.ball 0 R` the extension agrees with `ψ`. -/
theorem extend_step {l : ℂ} (hl : ‖l‖ < 1) (hl0 : l ≠ 0) {R : ℝ} (hR : 0 < R) {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ (Metric.ball 0 R)) (hψ0 : ψ 0 = 0) (hψ' : deriv ψ 0 = 1)
    (heq : ∀ w ∈ Metric.ball 0 R, Q l (ψ w) = ψ (l * w))
    (hv : ∀ w ∈ Metric.ball 0 R, ψ w ≠ -(l ^ 2) / 4) :
    ∃ ψ' : ℂ → ℂ, DifferentiableOn ℂ ψ' (Metric.ball 0 (R / ‖l‖)) ∧ ψ' 0 = 0 ∧
      deriv ψ' 0 = 1 ∧
      (∀ w ∈ Metric.ball 0 (R / ‖l‖), Q l (ψ' w) = ψ' (l * w)) ∧
      (∀ w ∈ Metric.ball 0 R, ψ' w = ψ w) := by
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hlne : ‖l‖ ≠ 0 := ne_of_gt hlpos
  set ρ : ℝ := R / ‖l‖ with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact div_pos hR hlpos
  have hRρ : R < ρ := by
    rw [hρ, lt_div_iff₀ hlpos]
    exact mul_lt_of_lt_one_right hR hl
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) ρ :=
    Metric.ball_subset_ball (le_of_lt hRρ)
  -- * the comparison disc maps into the original one
  have hmaps : Set.MapsTo (fun w : ℂ => l * w) (Metric.ball 0 ρ) (Metric.ball 0 R) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    calc ‖l * w‖ = ‖l‖ * ‖w‖ := norm_mul l w
      _ < ‖l‖ * ρ := mul_lt_mul_of_pos_left hw hlpos
      _ = R := by
          rw [hρ, mul_comm]
          exact div_mul_cancel₀ R hlne
  -- * the function whose holomorphic logarithm we take
  have hgdiff : DifferentiableOn ℂ (fun w : ℂ => l * w) (Metric.ball 0 ρ) :=
    differentiableOn_id.const_mul l
  have hFdiff : DifferentiableOn ℂ (fun w : ℂ => ψ (l * w) + l ^ 2 / 4) (Metric.ball 0 ρ) :=
    (hψ.comp hgdiff hmaps).add_const (l ^ 2 / 4)
  have hFne : ∀ z ∈ Metric.ball 0 ρ, ψ (l * z) + l ^ 2 / 4 ≠ 0 := by
    intro z hz h0
    exact hv (l * z) (hmaps hz) (by linear_combination h0)
  obtain ⟨L, hLdiff, hLexp, _hLre⟩ := exists_differentiableOn_ball_clog hFdiff hFne
  -- * a holomorphic square root of `ψ (l ·) + l²/4`
  set S : ℂ → ℂ := fun w => Complex.exp (L w / 2) with hS
  have hSdiff : DifferentiableOn ℂ S (Metric.ball 0 ρ) := by
    rw [hS]; exact (hLdiff.div_const 2).cexp
  have hSsq : ∀ w ∈ Metric.ball 0 ρ, S w ^ 2 = ψ (l * w) + l ^ 2 / 4 := by
    intro w hw
    have h1 : S w ^ 2 = Complex.exp (L w) := by
      rw [hS, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [h1, hLexp w hw]
  have hS0sq : S 0 ^ 2 = l ^ 2 / 4 := by
    have h := hSsq 0 (Metric.mem_ball_self hρpos)
    rw [mul_zero, hψ0, zero_add] at h
    exact h
  have hS0ne : S 0 ≠ 0 := by
    intro h
    have hl2 : l ^ 2 = 0 := by
      have h' : l ^ 2 / 4 = 0 := by rw [← hS0sq, h]; ring
      calc l ^ 2 = l ^ 2 / 4 * 4 := by ring
        _ = 0 := by rw [h']; ring
    exact hl0 (by apply mul_self_eq_zero.mp; rwa [pow_two] at hl2)
  -- * correct the square root so that it takes the value `l/2` at `0`
  set c : ℂ := l / (2 * S 0) with hc
  have hc2 : c ^ 2 = 1 := by
    rw [hc, div_pow]
    have hden : (2 * S 0) ^ 2 = l ^ 2 := by rw [mul_pow, hS0sq]; ring
    rw [hden]
    exact div_self (pow_ne_zero 2 hl0)
  have hcS0 : c * S 0 = l / 2 := by
    rw [hc]; field_simp
  -- * the extension
  set ψ' : ℂ → ℂ := fun w => -(l / 2) + c * S w with hψ'def
  have hψ'diff : DifferentiableOn ℂ ψ' (Metric.ball 0 ρ) := by
    rw [hψ'def]
    exact (hSdiff.const_mul c).const_add (-(l / 2))
  have hψ'0 : ψ' 0 = 0 := by
    change -(l / 2) + c * S 0 = 0
    rw [hcS0]; ring
  have hS2sq : ∀ w ∈ Metric.ball 0 ρ, (c * S w) ^ 2 = ψ (l * w) + l ^ 2 / 4 := by
    intro w hw
    rw [mul_pow, hc2, one_mul]
    exact hSsq w hw
  have hS_at : HasDerivAt S (deriv S 0) 0 :=
    (hSdiff.differentiableAt (Metric.ball_mem_nhds 0 hρpos)).hasDerivAt
  have hψ_at : HasDerivAt ψ (deriv ψ 0) 0 :=
    ((hψ 0 (Metric.mem_ball_self hR)).differentiableAt (Metric.ball_mem_nhds 0 hR)).hasDerivAt
  have hSderiv : deriv S 0 = c := by
    have hpow : deriv (fun w : ℂ => S w ^ 2) 0 = 2 * S 0 * deriv S 0 := by
      have h := (hS_at.pow 2).deriv
      rw [show (S ^ 2 : ℂ → ℂ) = (fun w => S w ^ 2) from rfl] at h
      simpa using h
    have hFderiv : deriv (fun w : ℂ => ψ (l * w) + l ^ 2 / 4) 0 = l := by
      have hinner : HasDerivAt (fun w : ℂ => l * w) l 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul l
      have hcomp : HasDerivAt (fun w : ℂ => ψ (l * w)) (deriv ψ 0 * l) 0 := by
        have hψ_at' : HasDerivAt ψ (deriv ψ 0) ((fun w : ℂ => l * w) 0) := by
          simpa using hψ_at
        exact hψ_at'.comp 0 hinner
      have h2 : HasDerivAt (fun w : ℂ => ψ (l * w) + l ^ 2 / 4) (deriv ψ 0 * l) 0 :=
        hcomp.add_const (l ^ 2 / 4)
      have h3 := h2.deriv
      rw [hψ'] at h3
      simpa using h3
    have hev : (fun w : ℂ => S w ^ 2) =ᶠ[𝓝 0] (fun w : ℂ => ψ (l * w) + l ^ 2 / 4) := by
      filter_upwards [Metric.ball_mem_nhds 0 hρpos] with w hw
      exact hSsq w hw
    have hEq := hev.deriv_eq
    rw [hpow, hFderiv] at hEq
    rw [hc, eq_div_iff (mul_ne_zero (by norm_num) hS0ne),
      mul_comm (deriv S 0) (2 * S 0)]
    exact hEq
  have hψ'deriv : deriv ψ' 0 = 1 := by
    have hd : HasDerivAt ψ' 1 0 := by
      rw [hψ'def]
      have h1 : HasDerivAt (fun w : ℂ => c * S w) (c * deriv S 0) 0 := hS_at.const_mul c
      have h2 : HasDerivAt (fun w : ℂ => -(l / 2) + c * S w) (c * deriv S 0) 0 :=
        h1.const_add (-(l / 2))
      rw [hSderiv] at h2
      rw [show c * c = 1 from by rw [← pow_two]; exact hc2] at h2
      exact h2
    exact hd.deriv
  -- * the functional equation on the smaller disc
  have hQ : ∀ w ∈ Metric.ball 0 ρ, Q l (ψ' w) = ψ (l * w) := by
    intro w hw
    have h1 : Q l (ψ' w) = -(l ^ 2) / 4 + (c * S w) ^ 2 := by
      simp only [hψ'def, Q]; ring
    rw [h1, hS2sq w hw]
    ring
  -- * agreement with `ψ` on the original disc
  have hJdiff : DifferentiableOn ℂ (fun w : ℂ => ψ' w + ψ w + l) (Metric.ball 0 R) :=
    ((hψ'diff.mono hsub).add hψ).add_const l
  have hJcont : ContinuousAt (fun w : ℂ => ψ' w + ψ w + l) 0 :=
    hJdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hR)
  have hJne : ∀ᶠ w in 𝓝 0, ψ' w + ψ w + l ≠ 0 :=
    hJcont.eventually_ne (by simpa [hψ'0, hψ0] using hl0)
  have hprod : ∀ w ∈ Metric.ball 0 R, (ψ' w - ψ w) * (ψ' w + ψ w + l) = 0 := by
    intro w hw
    have h1 : Q l (ψ' w) = ψ (l * w) := hQ w (hsub hw)
    have h2 : Q l (ψ w) = ψ (l * w) := heq w hw
    have hd : Q l (ψ' w) - Q l (ψ w) = 0 := by rw [h1, h2, sub_self]
    have hexp : Q l (ψ' w) - Q l (ψ w) = (ψ' w - ψ w) * (ψ' w + ψ w + l) := by
      simp only [Q]; ring
    rwa [hexp] at hd
  have hev0 : (fun w : ℂ => ψ' w - ψ w) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds 0 hR, hJne] with w hw hJw
    exact (mul_eq_zero.mp (hprod w hw)).resolve_right hJw
  have hg_an : AnalyticOnNhd ℂ (fun w : ℂ => ψ' w - ψ w) (Metric.ball 0 R) :=
    ((hψ'diff.mono hsub).sub hψ).analyticOnNhd Metric.isOpen_ball
  have hEq0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hg_an
    Metric.isPreconnected_ball (Metric.mem_ball_self hR) hev0
  have hψ'eq : ∀ w ∈ Metric.ball 0 R, ψ' w = ψ w := by
    intro w hw
    have := hEq0 hw
    simpa only [Pi.zero_apply, sub_eq_zero] using this
  have hψ'feq : ∀ w ∈ Metric.ball 0 ρ, Q l (ψ' w) = ψ' (l * w) := by
    intro w hw
    rw [hQ w hw]
    exact (hψ'eq (l * w) (hmaps hw)).symm
  exact ⟨ψ', hψ'diff, hψ'0, hψ'deriv, hψ'feq, hψ'eq⟩

end

end Work.Param
