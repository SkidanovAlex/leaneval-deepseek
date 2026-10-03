import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour

/-!
# A closed curve has a periodic argument exactly when its lift is periodic

For a continuous `1`-periodic nowhere vanishing `f : ℝ → ℂ` and any continuous lift `θ` of `f`
through `exp`, the curve has a continuous `1`-periodic argument (`HasArgPeriodic f`) if and only if
`θ` itself is `1`-periodic.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set Filter

open scoped Topology

/-- `D t = θ t - Re (θ t) - i ψ t` is continuous whenever `θ` and `ψ` are. -/
private lemma continuous_D {θ : ℝ → ℂ} (hθc : Continuous θ) {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    Continuous fun t => θ t - ((θ t).re : ℂ) - (ψ t : ℂ) * Complex.I :=
  (hθc.sub (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hθc))).sub
    ((Complex.continuous_ofReal.comp hψc).mul continuous_const)

/-- A continuous complex function whose exponential is constantly `1` is constant. -/
private lemma eq_const_of_exp_eq_one {D : ℝ → ℂ} (hDc : Continuous D)
    (hDexp : ∀ t, Complex.exp (D t) = 1) (t : ℝ) : D t = D 0 := by
  have hclosed : IsClosed {s : ℝ | D s = D 0} := isClosed_eq hDc continuous_const
  have hopen : IsOpen {s : ℝ | D s = D 0} := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hU : Metric.ball (D s) (2 * Real.pi) ∈ 𝓝 (D s) :=
      Metric.ball_mem_nhds _ (by linarith [Real.pi_pos])
    have hpre : D ⁻¹' (Metric.ball (D s) (2 * Real.pi)) ∈ 𝓝 s :=
      hDc.continuousAt.preimage_mem_nhds hU
    refine Filter.mem_of_superset hpre (fun y hy => ?_)
    have hy' : ‖D y - D s‖ < 2 * Real.pi := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hy
    show D y = D 0
    have hexp : Complex.exp (D y - D s) = 1 := by
      rw [Complex.exp_sub, hDexp y, hDexp s, div_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : (((n : ℂ) * (2 * Real.pi * Complex.I))).im = (n : ℝ) * (2 * Real.pi) := by
      rw [Complex.mul_im]
      simp
    have habs : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      have h1 : |(((n : ℂ) * (2 * Real.pi * Complex.I))).im| ≤
          ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ := Complex.abs_im_le_norm _
      rw [him, abs_mul, abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi)] at h1
      rw [hn] at hy'
      exact lt_of_le_of_lt h1 hy'
    have hn0 : n = 0 := by
      have h2 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
      by_contra hnne
      have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have := Int.one_le_abs hnne
        exact_mod_cast this
      linarith
    rw [hn0] at hn
    have hzero : D y - D s = 0 := by simpa using hn
    rw [sub_eq_zero] at hzero
    rw [hzero, hs]
  rcases isPreconnected_univ.subset_or_subset hopen hclosed.isOpen_compl disjoint_compl_right
    (by rw [union_compl_self]) with h | h
  · exact h (mem_univ t)
  · exfalso
    exact h (mem_univ 0) rfl

/-- **The (imaginary part of a) lift of a closed curve gives a periodic argument when the lift is
periodic, and conversely.** -/
theorem hasArg_iff_arg_lift {f : ℝ → ℂ} (hf : Continuous f) (hper : ∀ t, f (t + 1) = f t)
    (hnz : ∀ t, f t ≠ 0) {θ : ℝ → ℂ} (hθc : Continuous θ) (hθ : ∀ t, Complex.exp (θ t) = f t) :
    (HasArgPeriodic f ↔ ∀ t, θ (t + 1) = θ t) := by
  constructor
  · -- a periodic argument forces the lift to be periodic
    rintro ⟨ψ, hψc, hψper, hψrep⟩
    -- `exp (θ t - Re θ t - i ψ t) = 1`
    have hDexp : ∀ t, Complex.exp (θ t - ((θ t).re : ℂ) - (ψ t : ℂ) * Complex.I) = 1 := by
      intro t
      have hlog : Complex.exp (((θ t).re : ℂ) + (ψ t : ℂ) * Complex.I) = f t := by
        rw [Complex.exp_add, ← Complex.ofReal_exp]
        rw [show Real.exp (θ t).re = ‖f t‖ from by rw [← Complex.norm_exp, hθ t]]
        exact (hψrep t).symm
      have hsplit : θ t - ((θ t).re : ℂ) - (ψ t : ℂ) * Complex.I =
          θ t - (((θ t).re : ℂ) + (ψ t : ℂ) * Complex.I) := by ring
      rw [hsplit, Complex.exp_sub, hθ t, hlog, div_self (hnz t)]
    have hDconst := fun t => eq_const_of_exp_eq_one
      (continuous_D hθc hψc) hDexp t
    -- the imaginary parts agree, and then `exp` forces the whole lifting relation
    have him : ∀ t, (θ (t + 1)).im = (θ t).im := by
      intro t
      have h1 := hDconst (t + 1)
      have h2 := hDconst t
      have h3 : θ (t + 1) - ((θ (t + 1)).re : ℂ) - (ψ (t + 1) : ℂ) * Complex.I =
          θ t - ((θ t).re : ℂ) - (ψ t : ℂ) * Complex.I := by rw [h1, h2]
      have him' := congrArg Complex.im h3
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, sub_zero, hψper t] at him'
      linarith
    intro t
    have hdiff : Complex.exp (θ (t + 1) - θ t) = 1 := by
      rw [Complex.exp_sub, hθ (t + 1), hθ t, hper t, div_self (hnz t)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hdiff
    have him' : (θ (t + 1)).im - (θ t).im = (n : ℝ) * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa [Complex.mul_im] using this
    rw [him t, sub_self] at him'
    have hn0 : n = 0 := by
      have h2π : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
      have h := him'.symm
      rcases mul_eq_zero.mp h with h' | h'
      · exact_mod_cast h'
      · exact absurd h' (ne_of_gt h2π)
    rw [hn0] at hn
    have : θ (t + 1) - θ t = 0 := by simpa using hn
    exact sub_eq_zero.mp this
  · -- a periodic lift is a periodic argument
    intro hθper
    refine ⟨fun t => (θ t).im, ?_, ?_, ?_⟩
    · exact Complex.continuous_im.comp hθc
    · intro t
      show (θ (t + 1)).im = (θ t).im
      rw [hθper t]
    · intro t
      have hnorm : Real.exp (θ t).re = ‖f t‖ := by
        rw [← Complex.norm_exp, hθ t]
      have hz : θ t = ((θ t).re : ℂ) + ((θ t).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      calc f t = Complex.exp (θ t) := (hθ t).symm
        _ = Complex.exp ((θ t).re : ℂ) * Complex.exp (((θ t).im : ℂ) * Complex.I) := by
              conv_lhs => rw [hz]
              rw [Complex.exp_add]
        _ = ((Real.exp (θ t).re : ℝ) : ℂ) * Complex.exp (((θ t).im : ℂ) * Complex.I) := by
              rw [Complex.ofReal_exp]
        _ = ((‖f t‖ : ℝ) : ℂ) * Complex.exp (((θ t).im : ℂ) * Complex.I) := by
              rw [hnorm]

end Work.HornSC.CellBoundaryJordan
