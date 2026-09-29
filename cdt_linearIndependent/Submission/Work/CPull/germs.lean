import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.even_descent
import Submission.Work.CPull.pullbackMero_mulX
import Submission.Work.CPull.pullbackMero_tq
import Submission.Work.CPull.pullbackMero_intY

/-!
# Area CPull — germ forms of the pullback constructions

A *germ* of a pullback is the datum `∃ N, DifferentiableOn ℂ N (ball 0 1) ∧
∀ᶠ z in 𝓝 0, HasSum (Σₙ (coeffₙ f) · Ψ z ^ n) (N z)`, i.e. `PullbackMero f Ψ` with denominator
`1` and the numerator exhibited.  This is the form in which the integration/`tq`/`X·` steps of the
CPull development consume their input, so every case of the assembly produces germ data.

* `germ_of_even`: an even holomorphic `E` on the disc whose germ at `0` is `Σₙ aₙ · Ψ (z^2)ⁿ`
  descends through the square map to a germ for `Σₙ aₙ · Ψ(w)ⁿ` (`even_descent`).
* `pullbackMero_of_germ`: a germ gives `PullbackMero` with denominator `1` (the converse of the
  general contract; the useful direction is the one above).
* `germ_mulX`, `germ_tq`, `germ_intY`: the germ-level forms of `pullbackMero_mulX`,
  `pullbackMero_tq`, `pullbackMero_intY`.
* `Phi_ne_one_of_rel`: `Φ z ≠ 1` on the disc, from the lift relations (needed by the logs).
* `B6_eq_intY`, `B7_eq_intY`: the definitions `B₆ = ∫ B₃/y`, `B₇ = ∫ B₄/y`.
-/

namespace Work.CPull

open Complex Metric Filter
open PowerSeries
open scoped Topology NNReal ENNReal BigOperators

/-! ## square roots -/

lemma sq_sqrt_c (w : ℂ) : (Complex.sqrt w) ^ 2 = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [sqrt_eq_exp hw, pow_two, ← Complex.exp_add,
      show Complex.log w / 2 + Complex.log w / 2 = Complex.log w by ring,
      Complex.exp_log hw]

/-! ## the reduction: an even germ on `z ^ 2` descends to a germ -/

lemma germ_of_even {Ψ : ℂ → ℂ} {f : PowerSeries ℚ} {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E (Metric.ball 0 1))
    (heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z)
    (hgerm : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ (z ^ 2) ^ n) (E z)) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ),
        HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ w ^ n) (N w) := by
  obtain ⟨N, hN, hNz⟩ := even_descent E hE heven
  refine ⟨N, hN, ?_⟩
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hgerm
  set r : ℝ := min ε 1 with hrdef
  have hrpos : 0 < r := lt_min hεpos one_pos
  refine Filter.Eventually.mono
    (Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0:ℝ) < r ^ 2)) ?_
  intro w hw
  have hwn : ‖w‖ < r ^ 2 := by simpa [dist_eq_norm] using hw
  set z : ℂ := Complex.sqrt w with hzdef
  have hzsq : z ^ 2 = w := by rw [hzdef]; exact sq_sqrt_c w
  have hzn : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hzsq]
  have hzr : ‖z‖ < r := by
    have h1 : ‖z‖ ^ 2 < r ^ 2 := by rw [hzn]; exact hwn
    nlinarith [norm_nonneg z, hrpos, h1]
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_right _ _)
  have hzeps : dist z 0 < ε := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_left _ _)
  have h := hε hzeps
  rw [hzsq] at h
  rw [← hNz z hzmem] at h
  rw [hzsq] at h
  simpa using h

/-- A germ for `f` along `Ψ` with a globally holomorphic numerator gives `PullbackMero f Ψ`
(with denominator `1`). -/
lemma pullbackMero_of_germ {f : PowerSeries ℚ} {Ψ : ℂ → ℂ}
    (h : ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ),
        HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    Submission.CDTPlan.PullbackMero f Ψ := by
  obtain ⟨N, hN, hg⟩ := h
  exact ⟨1, N, by simp, hN, by simpa using hg⟩

/-! ## `Φ z ≠ 1` from the lift relations -/

/-- The lift relation forces `Φ z ≠ 1` (else `φ_C (z^2) = 1` and `φ_C (z^2) = 0`). -/
lemma Phi_ne_one_of_rel (Φ : ℂ → ℂ)
    (hrel : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Φ z + Φ (-z) = Submission.CDTPlan.phiC (z ^ 2) ∧
      Φ z * Φ (-z) = Submission.CDTPlan.phiC (z ^ 2))
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : Φ z ≠ 1 := by
  intro hc
  have h1 := (hrel z hz).1
  have h2 := (hrel z hz).2
  rw [hc, one_mul] at h2
  rw [hc] at h1
  have : (1 : ℂ) = 0 := by linear_combination h1 - h2
  exact one_ne_zero this


theorem germ_mulX {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    ∃ N' : ℂ → ℂ, DifferentiableOn ℂ N' (Metric.ball 0 1) ∧
      ∀ᶠ z in 𝓝 (0:ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (PowerSeries.X * f) : ℚ) : ℂ) * Ψ z ^ n) (N' z) := by
  -- denominator `1`, numerator `Ψ · N`
  refine ⟨fun z => Ψ z * N z, hΨ.mul hN, ?_⟩
  filter_upwards [hgerm] with z hz
  -- shift the convergent series by one place: multiply by `Ψ z`
  have h1 : HasSum (fun m : ℕ => ((PowerSeries.coeff m f : ℚ) : ℂ) * Ψ z ^ (m + 1))
      (Ψ z * N z) := by
    have h2 := hz.mul_left (Ψ z)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h2
  -- keep the finitely many vanished terms, so that the series is indexed from `0`
  set d : ℕ → ℂ := fun k =>
    if 1 ≤ k then ((PowerSeries.coeff (k - 1) f : ℚ) : ℂ) * Ψ z ^ k else 0 with hd
  have hdshift : HasSum (fun m => d (m + 1)) (Ψ z * N z) := by
    refine h1.congr_fun fun m => ?_
    simp [hd, Nat.le_add_left 1 m]
  have hdzero : d 0 = 0 := by simp [hd]
  have hdsum : HasSum d (Ψ z * N z) := by
    rw [← (hasSum_nat_add_iff' (f := d) (g := Ψ z * N z) 1)]
    rw [Finset.sum_range_one, hdzero, sub_zero]
    exact hdshift
  -- identify the summands with the coefficients of `X * f`
  refine hdsum.congr_fun fun n => ?_
  rw [coeff_mulX]
  by_cases h : 1 ≤ n <;> simp [hd, h]

theorem germ_tq {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ} (k : ℕ)
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨ0 : Ψ 0 = 0)
    (hΨne : ∀ z ∈ Metric.ball (0:ℂ) 1, Ψ z = 0 → z = 0)
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    ∃ N' : ℂ → ℂ, DifferentiableOn ℂ N' (Metric.ball 0 1) ∧
      ∀ᶠ z in 𝓝 (0:ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (Submission.CDTPlan.tq k f) : ℚ) : ℂ) * Ψ z ^ n) (N' z) := by
  classical
  set c : ℕ → ℂ := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ) with hc
  have hgerm' : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => c n * Ψ z ^ n) (N z) := hgerm
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hgerm'
  -- a point `z₁ ≠ 0` inside the neighbourhood of validity, and `w₀ = Ψ z₁ ≠ 0`
  set z₁ : ℂ := (((min ε 1) / 2 : ℝ) : ℂ) with hz₁def
  have hz₁norm : ‖z₁‖ = min ε 1 / 2 := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hz₁ε : dist z₁ 0 < ε := by
    rw [dist_zero_right, hz₁norm]
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    linarith
  have hz₁1 : ‖z₁‖ < 1 := by
    rw [hz₁norm]
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    linarith
  have hz₁ne : z₁ ≠ 0 := by
    intro hh
    have h0 : ‖z₁‖ = 0 := by rw [hh]; simp
    rw [hz₁norm] at h0
    have h2 : 0 < min ε 1 := lt_min hεpos one_pos
    linarith
  have hz₁mem : z₁ ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz₁1
  have hΨz₁ : Ψ z₁ ≠ 0 := fun h => hz₁ne (hΨne z₁ hz₁mem h)
  set w₀ : ℂ := Ψ z₁ with hw₀def
  have hw₀ : w₀ ≠ 0 := hΨz₁
  -- the tail series converges at the non-zero point `w₀`
  have hshift : HasSum (fun n : ℕ => c (n + k) * w₀ ^ n)
      ((N z₁ - ∑ i ∈ Finset.range k, c i * w₀ ^ i) / w₀ ^ k) :=
    hasSum_tail_eq k hw₀ (hε hz₁ε)
  -- hence it is holomorphic near `0`
  obtain ⟨H, R, hRpos, -, hHdiff, hH0, hHsum⟩ :=
    analyticOn_of_hasSum_at (g := fun n : ℕ => c (n + k)) (w₀ := w₀) hw₀ hshift
  have hH0' : H 0 = c k := by simpa using hH0
  have hΨcont : ContinuousAt Ψ 0 := hΨ.continuousOn.continuousAt (Metric.ball_mem_nhds 0 one_pos)
  -- a disc on which `Ψ` takes values in the disc of convergence of `H`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ z : ℂ, ‖z‖ < δ₀ → ‖Ψ z‖ < ‖w₀‖ / 2 := by
    have hcm := Metric.continuousAt_iff.mp hΨcont (‖w₀‖ / 2) (by positivity)
    obtain ⟨d, hdpos, hd⟩ := hcm
    refine ⟨d, hdpos, fun z hz => ?_⟩
    have h := hd (by simpa [dist_eq_norm] using hz)
    rwa [hΨ0, dist_zero_right] at h
  set δ : ℝ := min δ₀ (min ε 1) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min hεpos one_pos)
  have hδle₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleε : δ ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle1 : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hwpos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  -- the truncated series and the candidate quotient
  set T : ℂ → ℂ := fun w => ∑ i ∈ Finset.range k, c i * w ^ i with hTdef
  set g : ℂ → ℂ := fun z => (N z - T (Ψ z)) / Ψ z ^ k with hgdef
  -- the germ identity on the punctured disc
  have hgerm_eq : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → g z = H (Ψ z) := by
    intro z hz0 hzδ
    have hzε : dist z 0 < ε := by
      rw [dist_zero_right]; exact lt_of_lt_of_le hzδ hδleε
    have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzδ hδle1
    have hzmem : z ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hzne : Ψ z ≠ 0 := fun hzero => hz0.ne' (by rw [hΨne z hzmem hzero]; simp)
    have hs1 : HasSum (fun n : ℕ => c (n + k) * Ψ z ^ n) (H (Ψ z)) :=
      hHsum (Ψ z) (by have := hδ₀ z (lt_of_lt_of_le hzδ hδle₀); linarith [hwpos])
    have hs2 := hasSum_tail_eq (c := c) k hzne (hε hzε)
    rw [hgdef]
    exact hs2.unique hs1
  -- the removable-singularity extension
  set N' : ℂ → ℂ := Function.update g 0 (c k) with hN'def
  refine ⟨N', ?_, ?_⟩
  · refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (f := N') (s := Metric.ball 0 1) (c := 0) (Metric.ball_mem_nhds 0 one_pos)).mp ⟨?_, ?_⟩
    · -- differentiable on the punctured disc
      have hTdiff : DifferentiableOn ℂ T Set.univ := by
        rw [hTdef]
        refine DifferentiableOn.fun_sum (u := Finset.range k)
          (A := fun i w => c i * w ^ i) (fun i _ => ?_)
        exact (differentiableOn_const (c i)).mul (differentiableOn_id.pow i)
      have hTcomp : DifferentiableOn ℂ (fun z => T (Ψ z)) (Metric.ball (0:ℂ) 1 \ {0}) :=
        hTdiff.comp (hΨ.mono (fun z hz => hz.1)) (fun z _ => trivial)
      have hnum : DifferentiableOn ℂ (fun z => N z - T (Ψ z)) (Metric.ball (0:ℂ) 1 \ {0}) :=
        (hN.mono (fun z hz => hz.1)).sub hTcomp
      have hden : DifferentiableOn ℂ (fun z => Ψ z ^ k) (Metric.ball (0:ℂ) 1 \ {0}) :=
        (hΨ.pow k).mono (fun z hz => hz.1)
      have hgdiff : DifferentiableOn ℂ g (Metric.ball (0:ℂ) 1 \ {0}) := by
        rw [hgdef]
        exact hnum.div hden (fun z hz => pow_ne_zero k (fun h => hz.2 (by simpa using hΨne z hz.1 h)))
      exact hgdiff.congr (fun z hz => by
        rw [hN'def, Function.update_apply, if_neg (fun h => hz.2 (by simpa using h))])
    · -- continuity at `0`
      have hHc : ContinuousAt H (Ψ 0) := by
        rw [hΨ0]; exact hHdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hRpos)
      have hHcont : ContinuousAt (fun z => H (Ψ z)) 0 := hHc.comp hΨcont
      refine hHcont.congr ?_
      refine Filter.Eventually.mono (Metric.ball_mem_nhds 0 hδpos) (fun z hz => ?_)
      have hzδ : ‖z‖ < δ := by simpa using hz
      simp only []
      rcases eq_or_ne z 0 with rfl | hzne
      · simp [hN'def, hΨ0, hH0']
      · rw [hN'def, Function.update_apply, if_neg hzne]
        exact (hgerm_eq z (norm_pos_iff.mpr hzne) hzδ).symm
  · -- the germ of the pullback
    refine Filter.Eventually.mono (Metric.ball_mem_nhds 0 hδpos) (fun z hz => ?_)
    have hzδ : ‖z‖ < δ := by simpa using hz
    have hcoeff : ∀ n : ℕ,
        ((PowerSeries.coeff n (Submission.CDTPlan.tq k f) : ℚ) : ℂ) = c (n + k) := by
      intro n
      rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk, hc]
    rw [show (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDTPlan.tq k f) : ℚ) : ℂ) * Ψ z ^ n)
        = fun n : ℕ => c (n + k) * Ψ z ^ n from funext (fun n => by rw [hcoeff n])]
    rcases eq_or_ne z 0 with rfl | hzne
    · have hfun : (fun n : ℕ => c (n + k) * Ψ 0 ^ n) = fun n : ℕ => if n = 0 then c k else 0 := by
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [hΨ0]
        · simp [hΨ0, hn, zero_pow hn]
      rw [hN'def, Function.update_apply, if_pos rfl, hfun]
      exact hasSum_ite_eq 0 (c k)
    · have hs : HasSum (fun n : ℕ => c (n + k) * Ψ z ^ n) (H (Ψ z)) :=
        hHsum (Ψ z) (by have := hδ₀ z (lt_of_lt_of_le hzδ hδle₀); linarith [hwpos])
      rw [hN'def, Function.update_apply, if_neg hzne, hgerm_eq z (norm_pos_iff.mpr hzne) hzδ]
      exact hs

theorem germ_intY {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    ∃ N' : ℂ → ℂ, DifferentiableOn ℂ N' (Metric.ball 0 1) ∧
      ∀ᶠ z in 𝓝 (0:ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (Submission.CDTPlan.intY f) : ℚ) : ℂ) * Ψ z ^ n) (N' z) := by
  classical
  set a : ℕ → ℂ := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ) with ha
  have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n (Submission.CDTPlan.intY f) : ℚ) : ℂ)
      = (if n = 0 then 0 else a (n - 1) / (n : ℂ)) := by
    intro n
    rw [coeff_intY]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, if_neg hn, Rat.cast_div, ha]
      push_cast
      ring
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hgerm
  set α : ℝ := min δ 1 / 2 with hαdef
  have hαpos : 0 < α := by
    have h1 : 0 < min δ 1 := lt_min hδpos one_pos
    rw [hαdef]; linarith
  have hαδ : α < δ := by
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    rw [hαdef]; linarith
  have hα1 : α < 1 := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    rw [hαdef]; linarith
  obtain ⟨z₀, hz₀mem, hz₀max, L, hL0, hLb⟩ := exists_bounds_closedBall hΨ hαpos hα1
  have hz₀δ : dist z₀ 0 < δ := by
    have h1 : dist z₀ 0 ≤ α := Metric.mem_closedBall.mp hz₀mem
    linarith
  have hsum_z₀ : Summable fun k : ℕ => ‖a k‖ * ‖Ψ z₀‖ ^ k := by
    have hh := hδ hz₀δ
    simpa [a, norm_mul, norm_pow] using hh.summable.norm
  have hshift : Summable fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * ‖Ψ z₀‖ ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using hsum_z₀
  have hu : Summable fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * ‖Ψ z₀‖ ^ (n - 1)) * L :=
    hshift.mul_right L
  have h0 : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ 0 ^ n := by
    have hh := hδ (show dist (0 : ℂ) 0 < δ by rw [dist_zero_right]; simpa using hδpos)
    exact summable_intY_shift (Ψ 0) hh.summable
  have hbN : ∀ z ∈ Metric.ball (0 : ℂ) α, HasSum (fun k : ℕ => a k * Ψ z ^ k) (N z) := by
    intro z hz
    have h1 : dist z 0 < α := Metric.mem_ball.mp hz
    exact hδ (by linarith)
  have hgerm_deriv := germ_hasDerivAt hΨ hαpos hα1 (norm_nonneg (Ψ z₀)) hL0 hz₀max hLb hu hbN h0
  -- the primitive of `(deriv Ψ) · N`
  have hderivN : DifferentiableOn ℂ (fun z => deriv Ψ z * N z) (Metric.ball 0 1) :=
    (hΨ.deriv Metric.isOpen_ball).mul hN
  obtain ⟨H, hH0, hHderiv⟩ := hderivN.isExactOn_ball.with_val_at 0 0
  set Cc : ℂ := ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ 0 ^ n with hCdef
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) α := by
    rw [Metric.mem_ball, dist_zero_right]; simpa using hαpos
  have hsub1 : Metric.ball (0 : ℂ) α ⊆ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hα1.le
  have hconst : ∀ z ∈ Metric.ball (0 : ℂ) α,
      (∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n) = H z + Cc := by
    intro z hz
    have hKderiv : ∀ w ∈ Metric.ball (0 : ℂ) α,
        HasDerivAt ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n)
          - H) 0 w := by
      intro w hw
      have h1 : HasDerivAt (fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n)
          (deriv Ψ w * N w) w := hgerm_deriv w hw
      have h2 : HasDerivAt H (deriv Ψ w * N w) w := hHderiv w (hsub1 hw)
      simpa only [sub_self] using h1.sub h2
    have hdiff : DifferentiableOn ℂ
        ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n) - H)
        (Metric.ball (0 : ℂ) α) :=
      fun w hw => (hKderiv w hw).differentiableAt.differentiableWithinAt
    have hzero : ∀ w ∈ Metric.ball (0 : ℂ) α,
        deriv ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n) - H) w = 0 :=
      fun w hw => (hKderiv w hw).deriv
    have hconstK := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℂ) α).isPreconnected hdiff hzero h0mem hz
    rw [Pi.sub_apply, hH0, sub_zero, Pi.sub_apply] at hconstK
    have : (∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n) - H z = Cc := by
      rw [hCdef]
      exact hconstK.symm
    linear_combination this
  refine ⟨fun z => H z + Cc, ?_, ?_⟩
  · refine DifferentiableOn.add ?_ (differentiableOn_const Cc)
    exact fun z hz => (hHderiv z hz).differentiableAt.differentiableWithinAt
  · refine Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hαpos) ?_
    intro z hz
    have hzsum : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n :=
      summable_intY_shift (Ψ z) (hbN z hz).summable
    have hHasSum : HasSum (fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n)
        (H z + Cc) := by
      have h1 := hzsum.hasSum
      rwa [hconst z hz] at h1
    simpa only [hcoeff, Polynomial.eval_one, div_one] using hHasSum

/-! ## the coefficient of `tq`, and `B₆ = ∫ B₃/y`, `B₇ = ∫ B₄/y` -/

lemma coeff_tq (k n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff n (Submission.CDTPlan.tq k f) = PowerSeries.coeff (n + k) f := by
  rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk]

lemma B6_eq_intY :
    Submission.CDTPlan.B6
      = Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 Submission.CDTPlan.B3) := by
  ext n
  rw [coeff_intY]
  rcases n with _ | m
  · simp [Submission.CDTPlan.B6, PowerSeries.coeff_mk]
  · rw [if_neg (Nat.succ_ne_zero m), coeff_tq, Nat.add_sub_cancel]
    simp only [Submission.CDTPlan.B6, Submission.CDTPlan.B3, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    push_cast
    field_simp

lemma B7_eq_intY :
    Submission.CDTPlan.B7
      = Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 Submission.CDTPlan.B4) := by
  ext n
  rw [coeff_intY]
  rcases n with _ | m
  · simp [Submission.CDTPlan.B7, PowerSeries.coeff_mk]
  · rw [if_neg (Nat.succ_ne_zero m), coeff_tq, Nat.add_sub_cancel]
    simp only [Submission.CDTPlan.B7, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]

end Work.CPull
