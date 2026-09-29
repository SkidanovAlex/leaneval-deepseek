import Mathlib

/-!
# Measurability of a parameter-dependent holomorphic derivative

Given `W ⊆ ℂ` open, `g : ℂ → ℝ → ℂ` jointly continuous on `W × univ` and
holomorphic in its first variable on `W`, the (parameterized) derivative
`x ↦ deriv (fun z => g z x) z₀` at a point `z₀ ∈ W` is a measurable function
of the real parameter `x`.

The proof realizes the derivative as a pointwise limit of difference
quotients along a sequence `hₙ → 0`, `hₙ ≠ 0`, chosen inside a small ball
around `z₀` contained in `W`. Each difference quotient is measurable (being
built from joint continuity), and a pointwise limit of measurable functions
is measurable.
-/

namespace Work.TMComp.MAnalytic

open Set Filter
open scoped Topology

theorem measurable_deriv_param {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ → ℂ}
    (hg : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2) (W ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => g z x) W) {z₀ : ℂ} (hz₀ : z₀ ∈ W) :
    Measurable (fun x : ℝ => deriv (fun z => g z x) z₀) := by
  -- Each slice `x ↦ g z x` is measurable for `z ∈ W`.
  have hmeas_z : ∀ z ∈ W, Measurable (fun x : ℝ => g z x) := by
    intro z hz
    have hcont : Continuous (fun x : ℝ => (z, x)) :=
      Continuous.prodMk continuous_const continuous_id
    have hmap : Set.MapsTo (fun x : ℝ => (z, x)) Set.univ (W ×ˢ (Set.univ : Set ℝ)) :=
      fun x _ => ⟨hz, trivial⟩
    have hc : ContinuousOn ((fun p : ℂ × ℝ => g p.1 p.2) ∘ (fun x : ℝ => (z, x))) Set.univ :=
      hg.comp hcont.continuousOn hmap
    rw [show ((fun p : ℂ × ℝ => g p.1 p.2) ∘ (fun x : ℝ => (z, x))) = (fun x => g z x) from rfl] at hc
    exact (continuousOn_univ.mp hc).measurable
  -- A ball around `z₀` inside `W`.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo z₀ hz₀
  have hr2 : (0:ℝ) < r / 2 := by linarith
  -- The sequence `t n = (r/2)/(n+1) → 0`, all of whose terms keep `z₀ + t n` in the ball.
  let t : ℕ → ℝ := fun n => (r / 2) / ((n : ℝ) + 1)
  have ht_ne : ∀ n, t n ≠ 0 := by
    intro n
    have h1 : (r/2) ≠ 0 := ne_of_gt hr2
    have h2 : ((n:ℝ)+1) ≠ 0 := by positivity
    exact div_ne_zero h1 h2
  have ht_pos : ∀ n, 0 < t n := by
    intro n; exact div_pos hr2 (by positivity)
  have ht_tend : Tendsto t atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (r / 2) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (r / 2)
    have h1 := (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (r/2)/(n:ℝ)) 1).mpr h0
    simpa [t, Nat.cast_add, Nat.cast_one] using h1
  let h_seq : ℕ → ℂ := fun n => (t n : ℂ)
  have hh : Tendsto h_seq atTop (𝓝[≠] (0:ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp ht_tend
      simpa [h_seq] using h1
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (ht_ne n)
  have hW : ∀ n, z₀ + h_seq n ∈ W := by
    intro n
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hz : z₀ + h_seq n - z₀ = ((t n : ℝ) : ℂ) := by simp [h_seq]
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht_pos n)]
    have hle : (r/2) / ((n:ℝ)+1) ≤ r/2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  -- The difference quotients.
  let F : ℕ → ℝ → ℂ := fun n x => (h_seq n)⁻¹ • (g (z₀ + h_seq n) x - g z₀ x)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    have h1 : Measurable (fun x : ℝ => g (z₀ + h_seq n) x) := hmeas_z _ (hW n)
    have h2 : Measurable (fun x : ℝ => g z₀ x) := hmeas_z _ hz₀
    exact (h1.sub h2).const_mul _
  have hpoint : ∀ x : ℝ, Tendsto (fun n => F n x) atTop (𝓝 (deriv (fun z => g z x) z₀)) := by
    intro x
    have hd : DifferentiableAt ℂ (fun z => g z x) z₀ :=
      (hhol x).differentiableAt (hWo.mem_nhds hz₀)
    have hslope := hd.hasDerivAt.tendsto_slope_zero
    have hcomp := hslope.comp hh
    have hfun : ((fun t : ℂ => t⁻¹ • ((fun z => g z x) (z₀ + t) - (fun z => g z x) z₀)) ∘ h_seq)
        = (fun n => F n x) := rfl
    rw [hfun] at hcomp
    exact hcomp
  have hT : Tendsto F atTop (𝓝 (fun x : ℝ => deriv (fun z => g z x) z₀)) :=
    tendsto_pi_nhds.mpr hpoint
  exact measurable_of_tendsto_metrizable hFmeas hT

end Work.TMComp.MAnalytic
