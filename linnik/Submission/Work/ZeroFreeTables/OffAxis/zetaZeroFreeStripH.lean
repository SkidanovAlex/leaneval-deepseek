import Mathlib

namespace Work.ZeroFreeTables.OffAxis

open Complex Filter Topology

/-- **Zeros of `ζ` stay off a strip around `Re s ≥ 1` at bounded height.**

For every height bound `T ≥ 0` there is `ε₀ > 0` (depending on `T`) such that `ζ` has no zeros
in `{s : |Im s| ≤ T, 1 - ε₀ ≤ Re s ≤ 2}`.

This is the quantitative form of the classical fact that `ζ` has no zeros in the closed
half-plane `Re s ≥ 1`.  By compactness it suffices to know non-vanishing on the closed
half-plane: if there were zeros with `1 - 1/(n+1) ≤ Re s`, `|Im s| ≤ T` for every `n`, a
convergent subsequence would produce a zero in `Re s ≥ 1` (the point `s = 1` is excluded by the
residue `(s-1)ζ(s) → 1`, since `ζ` vanishes to no order there), contradicting
`riemannZeta_ne_zero_of_one_le_re`. -/
theorem zetaZeroFreeStripH (T : ℝ) (hT : 0 ≤ T) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (t σ : ℝ), |t| ≤ T → 1 - ε₀ ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  by_contra h
  push Not at h
  -- `h : ∀ ε > 0, ∃ t σ, |t| ≤ T ∧ 1 - ε ≤ σ ∧ σ ≤ 2 ∧ ζ (σ + I * t) = 0`
  have h' : ∀ n : ℕ, ∃ t σ : ℝ, |t| ≤ T ∧ 1 - 1 / ((n : ℝ) + 1) ≤ σ ∧ σ ≤ 2 ∧
      riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) = 0 :=
    fun n => h (1 / ((n : ℝ) + 1)) (by positivity)
  choose t σ hP using h'
  let z : ℕ → ℂ := fun n => (σ n : ℂ) + Complex.I * (t n : ℂ)
  have hzP : ∀ n, riemannZeta (z n) = 0 := fun n => by simpa [z] using (hP n).2.2.2
  -- The sequence of alleged zeros lies in the compact rectangle `0 ≤ re ≤ 2`, `-T ≤ im ≤ T`.
  let K : Set ℂ := {w : ℂ | w.re ∈ Set.Icc (0:ℝ) 2 ∧ w.im ∈ Set.Icc (-T) T}
  have hKc : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨?_, ?_⟩
    · exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    · refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 2 + T)).subset ?_
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |w.re| ≤ 2 := abs_le.mpr ⟨by linarith [hw.1.1], hw.1.2⟩
      have h2 : |w.im| ≤ T := abs_le.mpr ⟨hw.2.1, hw.2.2⟩
      calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ ≤ 2 + T := by linarith
  have hzK : ∀ n, z n ∈ K := fun n => by
    have h0 : (0:ℝ) ≤ σ n := by
      have ha : (1:ℝ) ≤ (n : ℝ) + 1 := by
        have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact ha
      linarith [(hP n).2.1]
    have hzre : (z n).re = σ n := by simp [z]
    have hzim : (z n).im = t n := by simp [z]
    show (z n).re ∈ Set.Icc (0:ℝ) 2 ∧ (z n).im ∈ Set.Icc (-T) T
    simp only [Set.mem_Icc]
    exact ⟨⟨by rw [hzre]; exact h0, by rw [hzre]; exact (hP n).2.2.1⟩,
      by rw [hzim]; exact abs_le.mp (hP n).1⟩
  obtain ⟨a, haK, φ, hφmono, hlim⟩ := hKc.tendsto_subseq (x := z) hzK
  have hlim' : Tendsto (fun n => (σ (φ n) : ℂ) + Complex.I * (t (φ n) : ℂ)) atTop (𝓝 a) := by
    simpa [z, Function.comp_def] using hlim
  have hσlim : Tendsto (fun n => σ (φ n)) atTop (𝓝 a.re) := by
    have hh := (Complex.continuous_re.tendsto a).comp hlim'
    simpa [Function.comp_def] using hh
  have htlim : Tendsto (fun n => t (φ n)) atTop (𝓝 a.im) := by
    have hh := (Complex.continuous_im.tendsto a).comp hlim'
    simpa [Function.comp_def] using hh
  -- The limit point satisfies `1 ≤ re a`, since `1 - 1/(φ n + 1) ≤ σ (φ n) → re a`.
  have ha1 : 1 ≤ a.re := by
    have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hdiv : Tendsto (fun n => (1:ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφtop
    have hone : Tendsto (fun n => (1:ℝ) - 1 / ((φ n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact le_of_tendsto_of_tendsto' hone hσlim (fun n => (hP (φ n)).2.1)
  rcases eq_or_ne a 1 with ha | ha
  · -- `a = 1`: the alleged zeros converge to the pole, contradicting the residue formula.
    subst ha
    have hz1 : ∀ n, z (φ n) ≠ 1 := fun n hn =>
      riemannZeta_one_ne_zero (by rw [← hn]; exact hzP (φ n))
    have hseq : Tendsto (fun n => z (φ n)) atTop (𝓝[≠] (1:ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun n => z (φ n)) hlim
        (Filter.Eventually.of_forall hz1)
    have hres : Tendsto (fun n => (z (φ n) - 1) * riemannZeta (z (φ n))) atTop (𝓝 (1:ℂ)) :=
      riemannZeta_residue_one.comp hseq
    have hz0 : Tendsto (fun n => (z (φ n) - 1) * riemannZeta (z (φ n))) atTop (𝓝 (0:ℂ)) :=
      Tendsto.congr' (Filter.Eventually.of_forall fun n => by simp [hzP (φ n)])
        tendsto_const_nhds
    exact one_ne_zero (tendsto_nhds_unique hres hz0)
  · -- `a ≠ 1`: continuity of `ζ` at `a` turns the zeros into a zero with `re a ≥ 1`.
    have hcont : Tendsto (fun n => riemannZeta (z (φ n))) atTop (𝓝 (riemannZeta a)) := by
      have hh := (differentiableAt_riemannZeta ha).continuousAt.tendsto.comp hlim
      simpa [Function.comp_def] using hh
    have hz0 : Tendsto (fun n => riemannZeta (z (φ n))) atTop (𝓝 (0:ℂ)) :=
      Tendsto.congr' (Filter.Eventually.of_forall fun n => (hzP (φ n)).symm) tendsto_const_nhds
    exact riemannZeta_ne_zero_of_one_le_re ha1 (tendsto_nhds_unique hcont hz0)

end Work.ZeroFreeTables.OffAxis
