import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.uniform_separation_radius

set_option linter.unusedVariables false

namespace Work.EQ

open Complex Filter Metric Set

/-- **A family of chains over `ψ₁ = u + κ t ^ k` with no rotational collisions near `0` gives a
punctured chart.**

`E : ℂ → ChainData` is continuous on the punctured disc of radius `ρ`, has
`ψ₁ (E t) = u + κ t ^ k`, and is meromorphic at `0` in every coordinate (`hmer`).  Suppose (`hsep`)
that for every `k`-th root of unity `ω ≠ 1` the collision set `{t : E (ω t) = E t}` avoids some
punctured disc around `0`.

Then `e (ζ) := E (τ ζ)` for a small enough `τ` is the analytic half of a punctured chart with
exponent `k` and scale `κ' = κ τ ^ k`: it is injective on the punctured unit disc, continuous,
meromorphic at `0` in every coordinate, has `(e ζ).2.1 = u + κ' ζ ^ k`, and agrees with `E` on the
punctured disc of radius `τ` (in both directions).  (The caller still has to add the
`e ζ ∈ H0 a h` clause; `a` and `h` do not occur here.)

Injectivity: `e ζ₁ = e ζ₂` gives `ζ₂ ^ k = ζ₁ ^ k`, hence `ζ₂ = ω ζ₁` with `ω ^ k = 1`, and
`E (ω τ ζ₁) = E (τ ζ₁)`; choosing `τ` below all the finitely many `hsep` radii (and below `ρ`) makes
`ω = 1` and hence `ζ₁ = ζ₂`.

`hsep` is deliberately stated in this *pointwise-radius* form rather than as "the germ of
`E (ω ·) - E (·)` is nonzero": `ChainData` has infinitely many coordinates and `hmer` is a
coordinatewise condition at `0`, so the collision sets of the individual coordinates can shrink at
different rates, and a family can have collisions at points accumulating at `0` without any single
punctured disc on which `E (ω t) = E t` holds throughout. -/
theorem exists_chart_of_family {u : ℂ} (hu : u ≠ 0) {κ : ℂ} (hκ : κ ≠ 0)
    {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) {E : ℂ → Work.EQ.ChainData}
    (hψ : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ → (E t).2.1 = u + κ * t ^ k)
    (hcont : ContinuousOn E (Metric.ball (0:ℂ) ρ \ {0}))
    (hmer : ∀ n : ℤ, MeromorphicAt (fun t => ((E t).1 n).1) 0 ∧
      MeromorphicAt (fun t => ((E t).1 n).2) 0 ∧ MeromorphicAt (fun t => (E t).2.2) 0)
    (hsep : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → E (ω * t) ≠ E t) :
    ∃ (τ : ℝ) (_ : 0 < τ) (_ : τ ≤ ρ) (κ' : ℂ) (_ : κ' ≠ 0) (e : ℂ → Work.EQ.ChainData),
      (∀ ζ ∈ Metric.ball (0:ℂ) 1 \ {0}, (e ζ).2.1 = u + κ' * ζ ^ k) ∧
      Set.InjOn e (Metric.ball (0:ℂ) 1 \ {0}) ∧
      ContinuousOn e (Metric.ball (0:ℂ) 1 \ {0}) ∧
      (∀ n : ℤ, MeromorphicAt (fun ζ => ((e ζ).1 n).1) 0 ∧
        MeromorphicAt (fun ζ => ((e ζ).1 n).2) 0) ∧
      MeromorphicAt (fun ζ => (e ζ).2.2) 0 ∧
      (∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ → ∃ ζ, 0 < ‖ζ‖ ∧ ‖ζ‖ < 1 ∧ e ζ = E t) ∧
      (∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < 1 →
        ∃ t : ℂ, 0 < ‖t‖ ∧ ‖t‖ < τ ∧ E t = e ζ) := by
  classical
  -- a single separation radius valid for every `k`-th root of unity `ω ≠ 1`
  obtain ⟨τ, hτpos, hτρ, hsep'⟩ :=
    uniform_separation_radius hk hρ (P := fun ω t => E (ω * t) ≠ E t) hsep
  have hτ_ne : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτpos.ne'
  have hnormτ : ‖(τ : ℂ)‖ = τ := by simp [abs_of_pos hτpos]
  have hκ' : κ * (τ : ℂ) ^ k ≠ 0 := mul_ne_zero hκ (pow_ne_zero k hτ_ne)
  have hψe : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 →
      (E ((τ : ℂ) * ζ)).2.1 = u + (κ * (τ : ℂ) ^ k) * ζ ^ k := by
    intro ζ hζne hζ
    have hnorm : ‖(τ : ℂ) * ζ‖ = τ * ‖ζ‖ := by rw [norm_mul, hnormτ]
    have ht0 : 0 < ‖(τ : ℂ) * ζ‖ := by
      rw [hnorm]; exact mul_pos hτpos (norm_pos_iff.mpr hζne)
    have htρ : ‖(τ : ℂ) * ζ‖ < ρ := by rw [hnorm]; nlinarith [hζ, hτpos, hτρ]
    rw [hψ ((τ : ℂ) * ζ) ht0 htρ, mul_pow]
    ring
  refine ⟨τ, hτpos, hτρ, κ * (τ : ℂ) ^ k, hκ', fun ζ => E ((τ : ℂ) * ζ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the `ψ₁` coordinate of `e`
    intro ζ hζ
    exact hψe ζ (by simpa using hζ.2)
      (by simpa [Metric.mem_ball, dist_zero_right] using hζ.1)
  · -- injectivity of `e`
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    have heq' : E ((τ : ℂ) * ζ₁) = E ((τ : ℂ) * ζ₂) := heq
    have h1 : ‖ζ₁‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ₁.1
    have h2 : ‖ζ₂‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ₂.1
    have hz₁ : ζ₁ ≠ 0 := by simpa using hζ₁.2
    have hz₂ : ζ₂ ≠ 0 := by simpa using hζ₂.2
    have hp : ζ₁ ^ k = ζ₂ ^ k := by
      have hA := hψe ζ₁ hz₁ h1
      have hB := hψe ζ₂ hz₂ h2
      have hmid : (E ((τ : ℂ) * ζ₁)).2.1 = (E ((τ : ℂ) * ζ₂)).2.1 := by rw [heq']
      rw [hA, hB] at hmid
      exact mul_left_cancel₀ hκ' (add_left_cancel hmid)
    set ω : ℂ := ζ₂ / ζ₁ with hω
    have hωk : ω ^ k = 1 := by
      rw [hω, div_pow, ← hp, div_self (pow_ne_zero k hz₁)]
    have hωζ : ω * ζ₁ = ζ₂ := by rw [hω]; exact div_mul_cancel₀ ζ₂ hz₁
    by_cases hω1 : ω = 1
    · rw [hω1, one_mul] at hωζ; exact hωζ
    · exfalso
      have ht0 : 0 < ‖(τ : ℂ) * ζ₁‖ := by
        rw [norm_mul, hnormτ]; exact mul_pos hτpos (norm_pos_iff.mpr hz₁)
      have htlt : ‖(τ : ℂ) * ζ₁‖ < τ := by
        rw [norm_mul, hnormτ]; nlinarith [h1, hτpos]
      apply hsep' ω hωk hω1 ((τ : ℂ) * ζ₁) ht0 htlt
      have hstep : ω * ((τ : ℂ) * ζ₁) = (τ : ℂ) * ζ₂ := by rw [← hωζ]; ring
      rw [hstep, ← heq']
  · -- continuity of `e`
    have hg : ContinuousOn (fun ζ : ℂ => (τ : ℂ) * ζ) (Metric.ball (0:ℂ) 1 \ {0}) :=
      (continuous_const.mul continuous_id).continuousOn
    refine hcont.comp hg ?_
    intro ζ hζ
    have h1 : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ.1
    have hz : ζ ≠ 0 := by simpa using hζ.2
    refine ⟨?_, ?_⟩
    · simp only [Metric.mem_ball, dist_zero_right]
      rw [norm_mul, hnormτ]; nlinarith [h1, hτpos, hτρ]
    · simp only [Set.mem_singleton_iff]
      exact mul_ne_zero hτ_ne hz
  · -- coordinatewise meromorphy at `0`
    intro n
    refine ⟨?_, ?_⟩
    · have h := (hmer n).1
      have h2 : MeromorphicAt (fun t => ((E t).1 n).1) ((τ : ℂ) * 0) := by simpa using h
      simpa [Function.comp_def] using
        h2.comp_analyticAt (x := 0) (g := fun ζ : ℂ => (τ : ℂ) * ζ) (by fun_prop)
    · have h := (hmer n).2.1
      have h2 : MeromorphicAt (fun t => ((E t).1 n).2) ((τ : ℂ) * 0) := by simpa using h
      simpa [Function.comp_def] using
        h2.comp_analyticAt (x := 0) (g := fun ζ : ℂ => (τ : ℂ) * ζ) (by fun_prop)
  · have h := (hmer 0).2.2
    have h2 : MeromorphicAt (fun t => (E t).2.2) ((τ : ℂ) * 0) := by simpa using h
    simpa [Function.comp_def] using
      h2.comp_analyticAt (x := 0) (g := fun ζ : ℂ => (τ : ℂ) * ζ) (by fun_prop)
  · -- `e` is surjective onto the image of `E` on the punctured disc of radius `τ`
    intro t ht0 htlt
    refine ⟨(τ : ℂ)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hnormτ]
      exact mul_pos (inv_pos.mpr hτpos) ht0
    · have hlt' : τ⁻¹ * ‖t‖ < τ⁻¹ * τ := mul_lt_mul_of_pos_left htlt (inv_pos.mpr hτpos)
      rw [inv_mul_cancel₀ hτpos.ne'] at hlt'
      rw [norm_mul, norm_inv, hnormτ]
      exact hlt'
    · change E ((τ : ℂ) * ((τ : ℂ)⁻¹ * t)) = E t
      have : (τ : ℂ) * ((τ : ℂ)⁻¹ * t) = t := by
        rw [← mul_assoc, mul_inv_cancel₀ hτ_ne, one_mul]
      rw [this]
  · intro ζ hζ0 hζ1
    refine ⟨(τ : ℂ) * ζ, ?_, ?_, rfl⟩
    · rw [norm_mul, hnormτ]; exact mul_pos hτpos hζ0
    · rw [norm_mul, hnormτ]; nlinarith [hζ1, hτpos]

end Work.EQ
