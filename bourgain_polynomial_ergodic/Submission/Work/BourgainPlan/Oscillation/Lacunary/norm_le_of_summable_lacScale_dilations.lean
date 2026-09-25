import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

namespace Work.BourgainPlan.Oscillation.Lacunary

open Filter

/-- If for every `θ ∈ (0,1]` the lacunary dilation family `i ↦ ‖H₂(⌊ρ^i⌋·θ)‖²` is summable with
total mass at most `A²`, then `‖H₂‖` is bounded by `A` on all of `(0,∞)`.

Indeed, the scales `⌊ρ^i⌋` are unbounded, so for a given `u > 0` we may pick `i` with
`u ≤ ⌊ρ^i⌋` and test the hypothesis at `θ = u / ⌊ρ^i⌋ ∈ (0,1]`.  At that `θ` the `i`-th summand is
exactly `‖H₂ u‖²`, hence `‖H₂ u‖² ≤ A²`. -/
theorem norm_le_of_summable_lacScale_dilations (ρ : ℝ) (hρ : 1 < ρ) (A : ℝ) (hA : 0 ≤ A)
    (H₂ : ℝ → ℂ)
    (h : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      Summable (fun i : ℕ => ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
      ∑' i : ℕ, ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2) :
    ∀ u : ℝ, 0 < u → ‖H₂ u‖ ≤ A := by
  intro u hu
  -- The lacunary scales `⌊ρ^i⌋` are unbounded.
  have hunbdd : ∃ i : ℕ, u ≤ (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) := by
    have hge : ∀ᶠ i in Filter.atTop, 2 * u ≤ ρ ^ i :=
      (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop (2 * u)
    obtain ⟨i, hi⟩ := hge.exists
    refine ⟨i, ?_⟩
    have hhalf := Work.BourgainPlan.Oscillation.lacScale_ge_half ρ hρ i
    linarith
  obtain ⟨i, hi⟩ := hunbdd
  have hN1 : 1 ≤ Work.BourgainPlan.Oscillation.lacScale ρ i :=
    Work.BourgainPlan.Oscillation.one_le_lacScale ρ (le_of_lt hρ) i
  have hNpos : (0:ℝ) < (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  set θ : ℝ := u / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) with hθ
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos hu hNpos
  have hθle : θ ≤ 1 := by rw [hθ, div_le_one hNpos]; exact hi
  obtain ⟨hsum, hbound⟩ := h θ ⟨hθpos, hθle⟩
  -- The `i`-th summand is `‖H₂ u‖²`.
  have heq : (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ = u := by
    rw [hθ]; field_simp
  have hterm : ‖H₂ u‖ ^ 2 ≤ A ^ 2 := by
    have h1 : ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2
        ≤ ∑' j : ℕ, ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) * θ)‖ ^ 2 :=
      hsum.le_tsum i (fun j _ => sq_nonneg _)
    rw [heq] at h1
    exact le_trans h1 hbound
  have hsqrt := Real.sqrt_le_sqrt hterm
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hA] at hsqrt

end Work.BourgainPlan.Oscillation.Lacunary
