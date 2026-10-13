import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.IsEpsSolPQ

theorem eq_zero_of_le_mul_intervalIntegral {φ : ℝ → ℝ} {c T M : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hint : MeasureTheory.IntegrableOn φ (Set.Icc 0 T))
    (hnn : ∀ τ ∈ Set.Icc 0 T, 0 ≤ φ τ) (hbd : ∀ τ ∈ Set.Icc 0 T, φ τ ≤ M)
    (h : ∀ τ ∈ Set.Icc 0 T, φ τ ≤ c * ∫ s in (0 : ℝ)..τ, φ s) :
    ∀ τ ∈ Set.Icc 0 T, φ τ = 0 := by
  -- We prove the stronger statement `φ τ ≤ M * (c * τ) ^ n / n !` for every `n`,
  -- by induction on `n`: the inductive hypothesis is integrated against `h` and the
  -- exact value `∫_0^τ (c s)^n ds = c^n τ^{n+1}/(n+1)` produces the next factorial.
  -- Letting `n → ∞` (the bounds tend to `0`) and using `φ ≥ 0` gives `φ τ = 0`.
  have key : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      φ τ ≤ M * (c * τ) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro τ hτ
      simpa using hbd τ hτ
    | succ n ih =>
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hτT : τ ≤ T := hτ.2
      -- `φ` is interval-integrable on `[0,τ]`
      have hIntφ : IntervalIntegrable φ MeasureTheory.volume (0 : ℝ) τ :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hτ0).2
          (hint.mono_set (Set.Icc_subset_Icc_right hτT))
      -- the comparison function is continuous, hence interval-integrable
      have hIntg : IntervalIntegrable
          (fun s : ℝ => M * (c * s) ^ n / (n.factorial : ℝ)) MeasureTheory.volume (0 : ℝ) τ :=
        ((by fun_prop : ContinuousOn
            (fun s : ℝ => M * (c * s) ^ n / (n.factorial : ℝ)) (Set.Icc (0 : ℝ) τ))).intervalIntegrable_of_Icc hτ0
      -- the inductive hypothesis on `[0,τ]`
      have hpt : ∀ s ∈ Set.Icc (0 : ℝ) τ, φ s ≤ M * (c * s) ^ n / (n.factorial : ℝ) := by
        intro s hs
        exact ih s ⟨hs.1, le_trans hs.2 hτT⟩
      have hmono : (∫ s in (0 : ℝ)..τ, φ s)
          ≤ ∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ) :=
        intervalIntegral.integral_mono_on hτ0 hIntφ hIntg hpt
      -- the exact value of the comparison integral
      have hInt : (∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ))
          = M * c ^ n * τ ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        have h1 : (∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ))
            = (M / (n.factorial : ℝ)) * c ^ n * (∫ s in (0 : ℝ)..τ, s ^ n) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro s _
          show M * (c * s) ^ n / (n.factorial : ℝ) = M / (n.factorial : ℝ) * c ^ n * s ^ n
          rw [mul_pow]; ring
        rw [h1, integral_pow]
        have h0 : (0 : ℝ) ^ (n + 1) = 0 := by simp
        rw [h0, sub_zero]
        have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfac]
        field_simp
      calc φ τ ≤ c * ∫ s in (0 : ℝ)..τ, φ s := h τ hτ
        _ ≤ c * ∫ s in (0 : ℝ)..τ, M * (c * s) ^ n / (n.factorial : ℝ) :=
              mul_le_mul_of_nonneg_left hmono hc
        _ = c * (M * c ^ n * τ ^ (n + 1) / ((n + 1).factorial : ℝ)) := by rw [hInt]
        _ = M * (c * τ) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
              rw [mul_pow, pow_succ]; ring
  intro τ hτ
  -- the bounds `M * (c * τ)^n / n!` tend to `0`
  have hlim : Filter.Tendsto (fun n : ℕ => M * (c * τ) ^ n / (n.factorial : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (c * τ)).const_mul M
    simpa [mul_div_assoc] using h
  have hle0 : φ τ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => key n τ hτ))
  exact le_antisymm hle0 (hnn τ hτ)

end Work.FTS.StrongEps.IsEpsSolPQ
