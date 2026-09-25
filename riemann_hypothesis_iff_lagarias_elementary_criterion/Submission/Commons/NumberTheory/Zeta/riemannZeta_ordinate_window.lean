import Mathlib
import Submission.Commons.NumberTheory.Zeta.riemannZeta_local_zeroCount
import Submission.Commons.Algebra.BigOperators.card_le_finsum_of_one_le
import Submission.Commons.Analysis.Complex.one_le_divisor_of_analytic_zero

open Complex Filter Metric MeromorphicOn Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- `log (T + 6.5) + 1 ≤ 2 * (log T + 1)` for `T ≥ 5`. -/
private lemma aux_log_T {T : ℝ} (hT : 5 ≤ T) :
    Real.log (T + 6.5) + 1 ≤ 2 * (Real.log T + 1) := by
  have hle : T + 6.5 ≤ T ^ 2 := by nlinarith
  have h1 : Real.log (T + 6.5) ≤ Real.log (T ^ 2) :=
    Real.log_le_log (by linarith) hle
  rw [Real.log_pow] at h1
  have h2 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  nlinarith [h1]

theorem riemannZeta_ordinate_window (h : RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 5 ≤ T → ∃ S : Finset ℝ,
      (∀ s ∈ S, T - 1 ≤ s ∧ s ≤ T + 2) ∧
      (S.card : ℝ) ≤ c * (Real.log T + 1) ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → T - 1 ≤ ρ.im → ρ.im ≤ T + 2 → ρ.im ∈ S) := by
  classical
  have _ := h
  rcases riemannZeta_local_zeroCount with ⟨c0, hc0pos, hc0⟩
  refine ⟨2 * c0, by positivity, ?_⟩
  intro T hT
  set t : ℝ := T + 1 / 2 with ht_def
  have ht_nonneg : 0 ≤ t := by rw [ht_def]; linarith
  have ht3 : 3 < t := by rw [ht_def]; linarith
  have ht5 : 5 ≤ |t| := by rw [abs_of_nonneg ht_nonneg]; rw [ht_def]; linarith
  have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
  -- analyticity of ζ on the closed ball
  have h1not : (1 : ℂ) ∉ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
    intro hmem
    have hd : ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ (3 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    have him : |((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))).im| ≤
        ‖(1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := Complex.abs_im_le_norm _
    have him' : ((1 : ℂ) - ((2 : ℂ) + Complex.I * (t : ℂ))).im = -t := by simp
    rw [him', abs_neg] at him
    linarith
  have hζan : AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) := by
    refine analyticOn_riemannZeta.mono ?_
    intro z hz hz1
    exact h1not (hz1 ▸ hz)
  have hUpre : IsPreconnected (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) :=
    (Metric.isConnected_closedBall (x := (2 : ℂ) + Complex.I * (t : ℂ))
      (r := (3 : ℝ)) (by norm_num)).isPreconnected
  have hc_mem : ((2 : ℂ) + Complex.I * (t : ℂ)) ∈
      Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
    simp [Metric.mem_closedBall]
  have hcc_ne : riemannZeta ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  -- the divisor of the completed zeta function
  let D : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor completedRiemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) u
  have hDdef : ∀ u : ℂ, D u = MeromorphicOn.divisor riemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) u := by
    intro u
    dsimp only [D]
    exact divisor_completedRiemannZeta_eq_riemannZeta t ht5 u
  have hfinD : Function.HasFiniteSupport D := by
    dsimp only [D]
    exact (MeromorphicOn.divisor completedRiemannZeta
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ))).finiteSupport
        (isCompact_closedBall _ (3 : ℝ))
  have hfinD' : (Function.support D).Finite := hfinD
  let F : Finset ℂ := hfinD'.toFinset
  have hFmem : ∀ u : ℂ, u ∈ F ↔ D u ≠ 0 := by
    intro u
    change u ∈ hfinD'.toFinset ↔ D u ≠ 0
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  -- cardinality bound on `F`
  have hcardF_le : (F.card : ℝ) ≤ ∑ᶠ x : ℂ, ((D x : ℤ) : ℝ) := by
    refine Commons.Algebra.BigOperators.card_le_finsum_of_one_le ?_ ?_ F ?_
    · intro x
      rw [hDdef x]
      exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζan x)
    · rw [Function.HasFiniteSupport]
      exact hfinD'.subset (by
        intro x hx
        rw [Function.mem_support] at hx ⊢
        exact fun h0 => hx (by simp [h0]))
    · intro x hx
      have hDne : D x ≠ 0 := (hFmem x).mp hx
      have h0 : (0 : ℤ) ≤ D x := by
        rw [hDdef x]
        exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hζan x
      have h1 : (1 : ℤ) ≤ D x := by omega
      exact_mod_cast h1
  have hstrip : (∑ᶠ x : ℂ, ((D x : ℤ) : ℝ)) ≤ c0 * (Real.log (|t| + 6) + 1) := by
    dsimp only [D]
    exact hc0 t ht5
  have hlog_eq : Real.log (|t| + 6) = Real.log (T + 6.5) := by
    congr 1
    rw [ht_abs, ht_def]
    ring
  have hcardF : (F.card : ℝ) ≤ c0 * (Real.log (T + 6.5) + 1) := by
    rw [← hlog_eq]
    exact hcardF_le.trans hstrip
  -- the finset `S`
  let Zf : Finset ℂ := F.filter (fun ρ => ρ.re = 1 / 2 ∧ T - 1 ≤ ρ.im ∧ ρ.im ≤ T + 2)
  let S : Finset ℝ := Zf.image (fun ρ => ρ.im)
  refine ⟨S, ?hsub, ?hcard, ?hcontain⟩
  · intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨ρ, hρZf, rfl⟩ := hs
    have hρ := (Finset.mem_filter.mp hρZf).2
    exact ⟨hρ.2.1, hρ.2.2⟩
  · have hcardS : S.card ≤ Zf.card := by
      dsimp only [S]; exact Finset.card_image_le
    have hcardZf : Zf.card ≤ F.card := by
      dsimp only [Zf]; exact Finset.card_filter_le _ _
    calc (S.card : ℝ) ≤ (Zf.card : ℝ) := by exact_mod_cast hcardS
      _ ≤ (F.card : ℝ) := by exact_mod_cast hcardZf
      _ ≤ c0 * (Real.log (T + 6.5) + 1) := hcardF
      _ ≤ (2 * c0) * (Real.log T + 1) := by
            have hlog := aux_log_T hT
            calc c0 * (Real.log (T + 6.5) + 1) ≤ c0 * (2 * (Real.log T + 1)) :=
                  mul_le_mul_of_nonneg_left hlog hc0pos.le
              _ = (2 * c0) * (Real.log T + 1) := by ring
  · intro ρ hζ hre hlo hhi
    have hρball : ρ ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hre' : (ρ - ((2 : ℂ) + Complex.I * (t : ℂ))).re = ρ.re - 2 := by simp
      have him' : (ρ - ((2 : ℂ) + Complex.I * (t : ℂ))).im = ρ.im - t := by simp
      have hsq : ‖ρ - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 < 9 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre', him', hre]
        have h2 : (ρ.im - t) ^ 2 ≤ 9 / 4 := by
          have habs : |ρ.im - t| ≤ (3 / 2 : ℝ) := by
            rw [abs_le]
            constructor <;> [linarith; linarith]
          have := pow_le_pow_left₀ (abs_nonneg (ρ.im - t)) habs 2
          rw [sq_abs] at this
          nlinarith [this]
        nlinarith [h2]
      nlinarith [norm_nonneg (ρ - ((2 : ℂ) + Complex.I * (t : ℂ))), hsq]
    have hdiv1 : (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) (3 : ℝ)) ρ :=
      Commons.Analysis.Complex.one_le_divisor_of_analytic_zero hUpre hζan hc_mem hcc_ne hρball hζ
    have hDne : D ρ ≠ 0 := by
      rw [hDdef ρ]
      omega
    have hρF : ρ ∈ F := (hFmem ρ).mpr hDne
    have hρZf : ρ ∈ Zf := by
      dsimp only [Zf]
      exact Finset.mem_filter.mpr ⟨hρF, hre, hlo, hhi⟩
    dsimp only [S]
    exact Finset.mem_image.mpr ⟨ρ, hρZf, rfl⟩

end

end Commons.NumberTheory.Zeta
