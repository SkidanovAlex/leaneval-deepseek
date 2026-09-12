import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Complex

open Filter
open scoped Topology

theorem exists_ball_factorization_of_analyticAt_zero {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hf : AnalyticAt ℂ f c) (hfc : f c = 0)
    (hnc : ¬ Filter.Eventually (fun z => f z = 0) (nhds c)) :
    ∃ (R : ℝ) (k : ℕ) (ψ : ℂ → ℂ), 0 < R ∧ R < ρ ∧ 1 ≤ k ∧
      (∀ z ∈ Metric.ball c R, AnalyticAt ℂ ψ z) ∧
      (∀ z ∈ Metric.ball c R, ψ z ≠ 0) ∧
      ∀ z ∈ Metric.ball c R, f z = (z - c) ^ k * ψ z := by
  classical
  -- Near `c`, `f` factors as `(z - c)^k * g z` with `g` analytic at `c` and `g c ≠ 0`.
  obtain ⟨k, g, hg_an, hgc, hg_eq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnc
  have hg_eq_c : f c = (c - c) ^ k • g c := hg_eq.self_of_nhds
  -- Since `f c = 0` and `g c ≠ 0`, the order of vanishing `k` is at least one.
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    simp only [hk0, pow_zero, sub_self, one_smul] at hg_eq_c
    exact hgc (hg_eq_c.symm.trans hfc)
  -- A ball around `c` on which the factorization holds.
  obtain ⟨r₁, hr₁pos, hr₁⟩ : ∃ r > 0, ∀ z, dist z c < r → f z = (z - c) ^ k * g z := by
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp hg_eq
    exact ⟨r, hr, fun z hz => by simpa [smul_eq_mul] using h hz⟩
  -- A punctured ball around `c` on which `f` does not vanish.
  obtain ⟨r₂, hr₂pos, hr₂⟩ : ∃ r > 0, ∀ z, dist z c < r → z ≠ c → f z ≠ 0 := by
    have hne : ∀ᶠ z in 𝓝[{c}ᶜ] c, f z ≠ 0 :=
      hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnc
    rw [eventually_nhdsWithin_iff] at hne
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp hne
    exact ⟨r, hr, fun z hz hzc => h hz (by simpa using hzc)⟩
  -- A ball around `c` on which `f` is analytic.
  obtain ⟨r₃, hr₃pos, hf_an⟩ : ∃ r > 0, AnalyticOnNhd ℂ f (Metric.ball c r) :=
    hf.exists_ball_analyticOnNhd
  let R : ℝ := min (min r₁ r₂) (min r₃ (ρ / 2))
  have hR_le_r₁ : R ≤ r₁ := by
    simp only [R]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR_le_r₂ : R ≤ r₂ := by
    simp only [R]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hR_le_r₃ : R ≤ r₃ := by
    simp only [R]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRpos : 0 < R := by
    simp only [R]
    exact lt_min (lt_min hr₁pos hr₂pos) (lt_min hr₃pos (by linarith))
  have hRlt : R < ρ := by
    have h2 : R ≤ ρ / 2 := by
      simp only [R]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨R, k, fun z => if z = c then g c else f z / (z - c) ^ k, hRpos, hRlt, hk1, ?_, ?_, ?_⟩
  · -- analyticity of the cofactor
    intro z hz
    by_cases hzc : z = c
    · -- at the centre: `ψ` agrees with `g` near `c`
      rw [hzc]
      apply hg_an.congr
      filter_upwards [Metric.ball_mem_nhds c hr₁pos] with w hw
      by_cases hwc : w = c
      · rw [hwc]; simp
      · have h1 : f w = (w - c) ^ k * g w := hr₁ w (Metric.mem_ball.mp hw)
        simp only [if_neg hwc]
        rw [h1, mul_div_cancel_left₀ _ (pow_ne_zero k (sub_ne_zero.mpr hwc))]
    · -- away from the centre: `ψ` is a quotient of analytic functions
      have hzan : AnalyticAt ℂ f z := hf_an z (Metric.ball_subset_ball hR_le_r₃ hz)
      have hsub : AnalyticAt ℂ (fun x : ℂ => x - c) z := by fun_prop
      refine (hzan.div (hsub.pow k)
        (pow_ne_zero k (sub_ne_zero.mpr hzc))).congr ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hzc)] with w hw
      have hw' : ¬(w = c) := by simpa using hw
      simp only [Pi.div_apply, Pi.pow_apply, if_neg hw']
  · -- non-vanishing of the cofactor
    intro z hz
    by_cases hzc : z = c
    · rw [hzc]; simpa using hgc
    · have hfz : f z ≠ 0 := hr₂ z (Metric.mem_ball.mp (Metric.ball_subset_ball hR_le_r₂ hz)) hzc
      simp only [if_neg hzc]
      exact div_ne_zero hfz (pow_ne_zero k (sub_ne_zero.mpr hzc))
  · -- the factorization itself
    intro z hz
    by_cases hzc : z = c
    · rw [hzc, hfc, sub_self, zero_pow (Nat.pos_iff_ne_zero.mp hk1), zero_mul]
    · simp only [if_neg hzc]
      rw [← mul_div_assoc,
        mul_div_cancel_left₀ _ (pow_ne_zero k (sub_ne_zero.mpr hzc))]

end Commons.Analysis.Complex