import Submission.NBody.LYZIntegral
import Submission.NBody.LYZBound
import Submission.Commons.Analysis.InnerProductSpace.lyz_segment_distance_bound
import Mathlib

/-!
# The key geometric observation (Liu--Yan--Zhou, Lemma 5.1)

Given an `m_λ`-geodesic `γ` joining `x` to `x* + S b`, together with the length bound
`l(γ) ≤ S + Ψ(S)`, one controls the *position* of `γ` inside the cone of angle `≈ Ψ̄` around
the direction `b`:

* at the time `τ₁` where `‖γ - x*‖` last equals `S/2`, the curve is within `4√(SΨ)` of the
  midpoint `x* + (S/2)b`;
* for every `t` between `τ₁` and `τ`, the curve is within `6√(SΨ)` of the ray `x* + ℝ₊ b`.

Both are proved from the abstract length interface (`len`, with the chord bound and additivity)
and two elementary planar lemmas proved in the shared commons.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The midpoint estimate** (Liu--Yan--Zhou, Lemma 5.1, first part): if `p` is equidistant from
`x*` and `y`, `q` is at distance `S/2` from `x*`, `‖y - x*‖ = S` and `‖q - p‖ ≤ 2Ψ`, then `q` is
within `4√(SΨ)` of the midpoint of `[x*, y]`. -/
lemma lyz_midpoint_bound' {xstar y p q : F} {S Ψ : ℝ} (hS : 0 < S) (hΨ : 0 ≤ Ψ)
    (hy : ‖y - xstar‖ = S) (hp : ‖p - xstar‖ = ‖p - y‖) (hq : ‖q - xstar‖ = S / 2)
    (hqp : ‖q - p‖ ≤ 2 * Ψ) :
    ‖q - (xstar + ((1:ℝ) / 2) • (y - xstar))‖ ≤ 4 * Real.sqrt (S * Ψ) := by
  set D : F := y - xstar with hD
  set u : F := ((1:ℝ) / 2) • D with hu
  set P : F := p - xstar with hP
  have hDnorm : ‖D‖ = S := by rw [hD]; exact hy
  have hunorm : ‖u‖ = S / 2 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), hDnorm]
    ring
  have hPnorm : ‖P‖ = ‖P - D‖ := by
    have h1 : P - D = p - y := by rw [hP, hD]; abel
    rw [h1, hP]
    exact hp
  -- perpendicular-bisector identity
  have hperp : inner ℝ (P - u) u = 0 := by
    have h1 : ‖P‖ ^ 2 = ‖P - D‖ ^ 2 := by rw [hPnorm]
    rw [norm_sub_sq_real P D] at h1
    have h2 : 2 * inner ℝ P D = ‖D‖ ^ 2 := by linarith [h1]
    have h3 : inner ℝ P u = ‖u‖ ^ 2 := by
      rw [hu, real_inner_smul_right]
      have h4 : inner ℝ P D = ‖D‖ ^ 2 / 2 := by linarith [h2]
      rw [h4, hunorm, hDnorm]
      ring
    rw [inner_sub_left, h3, real_inner_self_eq_norm_sq, sub_self]
  have hkey : inner ℝ (q - xstar - u) u = inner ℝ (q - p) u := by
    have h1 : q - xstar - u = (q - p) + (P - u) := by rw [hP]; abel
    rw [h1, inner_add_left, hperp, add_zero]
  have hnorm : ‖q - xstar - u‖ ^ 2 = -2 * inner ℝ (q - p) u := by
    have h1 : ‖q - xstar - u‖ ^ 2
        = ‖q - xstar‖ ^ 2 - 2 * inner ℝ (q - xstar) u + ‖u‖ ^ 2 := norm_sub_sq_real _ _
    have h2 : inner ℝ (q - xstar) u = inner ℝ (q - xstar - u) u + ‖u‖ ^ 2 := by
      rw [show inner ℝ (q - xstar - u) u = inner ℝ (q - xstar) u - inner ℝ u u from
        inner_sub_left _ _ _, real_inner_self_eq_norm_sq]
      ring
    rw [h1, h2, hkey, hq, hunorm]
    ring
  have hb : -2 * inner ℝ (q - p) u ≤ 2 * S * Ψ := by
    have h1 : -(‖q - p‖ * ‖u‖) ≤ inner ℝ (q - p) u :=
      (abs_le.mp (abs_real_inner_le_norm (q - p) u)).1
    have h3 : ‖q - p‖ * ‖u‖ ≤ S * Ψ := by
      rw [hunorm]
      nlinarith [hqp, hΨ, hS.le]
    have h5 : -(S * Ψ) ≤ inner ℝ (q - p) u := (neg_le_neg h3).trans h1
    have h6 : (2:ℝ) * S * Ψ = 2 * (S * Ψ) := by ring
    rw [h6]
    linarith
  have hsq : ‖q - xstar - u‖ ^ 2 ≤ (4 * Real.sqrt (S * Ψ)) ^ 2 := by
    rw [hnorm]
    have h4 : (4 * Real.sqrt (S * Ψ)) ^ 2 = 16 * (S * Ψ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ S * Ψ)]
      norm_num
    rw [h4]
    nlinarith [hb, hS.le, hΨ]
  have hgoal : q - (xstar + ((1:ℝ) / 2) • (y - xstar)) = q - xstar - u := by
    rw [hu, hD]
    abel
  rw [hgoal]
  calc ‖q - xstar - u‖ = Real.sqrt (‖q - xstar - u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((4 * Real.sqrt (S * Ψ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 4 * Real.sqrt (S * Ψ) := Real.sqrt_sq (by positivity)

/-- The midpoint of a segment expressed as an affine combination of the endpoints. -/
lemma affine_comb (c v : F) (s u w : ℝ) :
    (1 - s) • (c + u • v) + s • (c + w • v) = c + ((1 - s) * u + s * w) • v := by
  simp only [smul_add, smul_smul]
  module

/-- **Liu--Yan--Zhou, Lemma 5.1, first part** (abstract form): the curve at the last time at
which it crosses the sphere of radius `S/2` is close to the midpoint of `[x*, γ τ]`. -/
theorem lyz_obs_midpoint {γ : ℝ → F} {len : ℝ → ℝ → ℝ} {xstar : F} {S Ψ τ τ₁ τ₂ : ℝ}
    (hS : 0 < S) (hΨ : 0 ≤ Ψ) (hΨS : Ψ ≤ S / 2)
    (hτ₁0 : 0 ≤ τ₁) (hτ₁τ : τ₁ ≤ τ) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂τ : τ₂ ≤ τ)
    (hlen_add : ∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ → len a c = len a b + len b c)
    (hlen_chord : ∀ a b, 0 ≤ a → a ≤ b → b ≤ τ → ‖γ b - γ a‖ ≤ len a b)
    (hlen_total : len 0 τ ≤ S + Ψ) (hx0 : ‖γ 0 - xstar‖ ≤ Ψ)
    (hy : ‖γ τ - xstar‖ = S) (hq : ‖γ τ₁ - xstar‖ = S / 2)
    (hp : ‖γ τ₂ - xstar‖ = ‖γ τ₂ - γ τ‖) (ht₂ge : S / 2 ≤ ‖γ τ₂ - xstar‖) :
    ‖γ τ₁ - (xstar + ((1:ℝ) / 2) • (γ τ - xstar))‖ ≤ 4 * Real.sqrt (S * Ψ) := by
  have hτ₂0 : 0 ≤ τ₂ := le_trans hτ₁0 hτ₁₂
  have hlen0τ₂ : len 0 τ = len 0 τ₂ + len τ₂ τ := hlen_add 0 τ₂ τ le_rfl hτ₂0 hτ₂τ le_rfl
  have hlen0τ₁ : len 0 τ = len 0 τ₁ + len τ₁ τ := hlen_add 0 τ₁ τ le_rfl hτ₁0 hτ₁τ le_rfl
  have hlenτ₁τ₂ : len τ₁ τ = len τ₁ τ₂ + len τ₂ τ := hlen_add τ₁ τ₂ τ hτ₁0 hτ₁₂ hτ₂τ le_rfl
  -- `‖p - x*‖ ≤ (S + 2Ψ)/2`
  have hp_bound : ‖γ τ₂ - xstar‖ ≤ (S + 2 * Ψ) / 2 := by
    have h1 : ‖γ τ₂ - xstar‖ ≤ ‖γ τ₂ - γ 0‖ + ‖γ 0 - xstar‖ := by
      calc ‖γ τ₂ - xstar‖ = ‖(γ τ₂ - γ 0) + (γ 0 - xstar)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖γ τ₂ - γ 0‖ + ‖γ 0 - xstar‖ := norm_add_le _ _
    have h2 : ‖γ τ₂ - γ 0‖ ≤ len 0 τ₂ := by simpa using hlen_chord 0 τ₂ le_rfl hτ₂0 hτ₂τ
    have h3 : ‖γ τ₂ - γ τ‖ ≤ len τ₂ τ := by
      rw [norm_sub_rev]; exact hlen_chord τ₂ τ hτ₂0 hτ₂τ le_rfl
    have h4 : ‖γ τ₂ - γ τ‖ = ‖γ τ₂ - xstar‖ := hp.symm
    linarith [h1, h2, h3, h4, hlen_total]
  -- `‖q - p‖ ≤ 2Ψ`
  have hq_dist : ‖γ τ₁ - γ τ₂‖ ≤ 2 * Ψ := by
    have h1 : ‖γ τ₁ - γ 0‖ ≤ len 0 τ₁ := by simpa using hlen_chord 0 τ₁ le_rfl hτ₁0 hτ₁τ
    have h2 : ‖γ τ₁ - xstar‖ ≤ ‖γ τ₁ - γ 0‖ + ‖γ 0 - xstar‖ := by
      calc ‖γ τ₁ - xstar‖ = ‖(γ τ₁ - γ 0) + (γ 0 - xstar)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖γ τ₁ - γ 0‖ + ‖γ 0 - xstar‖ := norm_add_le _ _
    have h3 : ‖γ τ₂ - γ τ‖ ≤ len τ₂ τ := by
      rw [norm_sub_rev]; exact hlen_chord τ₂ τ hτ₂0 hτ₂τ le_rfl
    have h4 : ‖γ τ₂ - γ τ‖ = ‖γ τ₂ - xstar‖ := hp.symm
    have h5 : len τ₁ τ₂ ≤ 2 * Ψ := by linarith
    refine (norm_sub_rev (γ τ₁) (γ τ₂)).le.trans ?_
    exact (hlen_chord τ₁ τ₂ hτ₁0 hτ₁₂ hτ₂τ).trans h5
  exact lyz_midpoint_bound' (F := F) hS hΨ hy hp hq hq_dist

/-- **Liu--Yan--Zhou, Lemma 5.1, second part** (abstract form): the curve stays close to the ray
`x* + ℝ₊ (γ τ - x*)`. -/
theorem lyz_obs_ray {γ : ℝ → F} {len : ℝ → ℝ → ℝ} {xstar : F} {S Ψ τ τ₁ τ₂ t : ℝ}
    (hS : 0 < S) (hΨ : 0 ≤ Ψ) (hΨS : Ψ ≤ S / 2)
    (hτ₁0 : 0 ≤ τ₁) (hτ₁τ : τ₁ ≤ τ) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂τ : τ₂ ≤ τ)
    (htτ₁ : τ₁ ≤ t) (htτ : t ≤ τ)
    (hlen_add : ∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ τ → len a c = len a b + len b c)
    (hlen_chord : ∀ a b, 0 ≤ a → a ≤ b → b ≤ τ → ‖γ b - γ a‖ ≤ len a b)
    (hlen_total : len 0 τ ≤ S + Ψ) (hx0 : ‖γ 0 - xstar‖ ≤ Ψ)
    (hy : ‖γ τ - xstar‖ = S) (hq : ‖γ τ₁ - xstar‖ = S / 2)
    (hp : ‖γ τ₂ - xstar‖ = ‖γ τ₂ - γ τ‖) (ht₂ge : S / 2 ≤ ‖γ τ₂ - xstar‖) :
    ∃ c : ℝ, 0 ≤ c ∧
      ‖γ t - (xstar + c • (γ τ - xstar))‖ ≤ 6 * Real.sqrt (S * Ψ) := by
  have hτ₂0 : 0 ≤ τ₂ := le_trans hτ₁0 hτ₁₂
  have hlen0τ₂ : len 0 τ = len 0 τ₂ + len τ₂ τ := hlen_add 0 τ₂ τ le_rfl hτ₂0 hτ₂τ le_rfl
  have hlen0τ₁ : len 0 τ = len 0 τ₁ + len τ₁ τ := hlen_add 0 τ₁ τ le_rfl hτ₁0 hτ₁τ le_rfl
  have hlenτ₁τ : len τ₁ τ = len τ₁ τ₂ + len τ₂ τ := hlen_add τ₁ τ₂ τ hτ₁0 hτ₁₂ hτ₂τ le_rfl
  -- the two chord bounds needed by the elementary lemmas
  have hsep : S / 2 ≤ ‖γ τ₁ - γ τ‖ := by
    have h1 : ‖γ τ - xstar‖ ≤ ‖γ τ - γ τ₁‖ + ‖γ τ₁ - xstar‖ := by
      calc ‖γ τ - xstar‖ = ‖(γ τ - γ τ₁) + (γ τ₁ - xstar)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖γ τ - γ τ₁‖ + ‖γ τ₁ - xstar‖ := norm_add_le _ _
    rw [hy, hq] at h1
    have := norm_sub_rev (γ τ) (γ τ₁)
    linarith [h1, this]
  have hlen_t : ‖γ t - γ τ₁‖ + ‖γ t - γ τ‖ ≤ S / 2 + 2 * Ψ := by
    have h1 : ‖γ t - γ τ₁‖ ≤ len τ₁ t := hlen_chord τ₁ t hτ₁0 htτ₁ htτ
    have h2 : ‖γ t - γ τ‖ ≤ len t τ := by
      rw [norm_sub_rev]; exact hlen_chord t τ (le_trans hτ₁0 htτ₁) htτ le_rfl
    have h3 : len τ₁ t + len t τ = len τ₁ τ := (hlen_add τ₁ t τ hτ₁0 htτ₁ htτ le_rfl).symm
    have h4 : ‖γ τ₂ - γ τ‖ ≤ len τ₂ τ := by
      rw [norm_sub_rev]; exact hlen_chord τ₂ τ hτ₂0 hτ₂τ le_rfl
    have h5 : ‖γ τ₂ - xstar‖ ≤ len τ₂ τ := by rw [hp]; exact h4
    have h6 : len 0 τ₁ ≥ S / 2 - Ψ := by
      have h7 : ‖γ τ₁ - γ 0‖ ≤ len 0 τ₁ := by simpa using hlen_chord 0 τ₁ le_rfl hτ₁0 hτ₁τ
      have h8 : ‖γ τ₁ - xstar‖ ≤ ‖γ τ₁ - γ 0‖ + ‖γ 0 - xstar‖ := by
        calc ‖γ τ₁ - xstar‖ = ‖(γ τ₁ - γ 0) + (γ 0 - xstar)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖γ τ₁ - γ 0‖ + ‖γ 0 - xstar‖ := norm_add_le _ _
      linarith [h7, h8, hq, hx0]
    linarith [h1, h2, h3, h5, h6, hlen_total, ht₂ge]
  -- the closest point of `[γ τ₁, γ τ]` to `γ t`
  obtain ⟨t₀, ht₀, hmin₀⟩ : ∃ t₀ ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖γ t - (γ τ₁ + t₀ • (γ τ - γ τ₁))‖ ≤ ‖γ t - (γ τ₁ + s • (γ τ - γ τ₁))‖ := by
    have hcont : ContinuousOn (fun s : ℝ => ‖γ t - (γ τ₁ + s • (γ τ - γ τ₁))‖) (Set.Icc 0 1) := by
      fun_prop
    obtain ⟨s, hs, hsmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hcont
    exact ⟨s, hs, fun u hu => hsmin hu⟩
  have hdist : ‖γ t - (γ τ₁ + t₀ • (γ τ - γ τ₁))‖ ≤ 2 * Real.sqrt (S * Ψ) :=
    Commons.Analysis.InnerProductSpace.lyz_segment_distance_bound (F := F) ht₀ hS hΨ hΨS hsep
      hlen_t hmin₀
  -- the midpoint bound
  have hmid : ‖γ τ₁ - (xstar + ((1:ℝ) / 2) • (γ τ - xstar))‖ ≤ 4 * Real.sqrt (S * Ψ) :=
    lyz_obs_midpoint (F := F) hS hΨ hΨS hτ₁0 hτ₁τ hτ₁₂ hτ₂τ hlen_add
      hlen_chord hlen_total hx0 hy hq hp ht₂ge
  refine ⟨(1 - t₀) * ((1:ℝ) / 2) + t₀, ?_, ?_⟩
  · nlinarith [ht₀.1, ht₀.2]
  · have hbound : ‖γ τ₁ - (xstar + ((1:ℝ) / 2) • (γ τ - xstar))‖ ≤ 4 * Real.sqrt (S * Ψ) := hmid
    have hc : (1 - t₀) • (xstar + ((1:ℝ) / 2) • (γ τ - xstar)) + t₀ • γ τ
        = xstar + ((1 - t₀) * ((1:ℝ) / 2) + t₀) • (γ τ - xstar) := by
      have h1 : (1 - t₀) * ((1:ℝ) / 2) + t₀ = (1 - t₀) * ((1:ℝ) / 2) + t₀ * 1 := by ring
      rw [h1, ← affine_comb xstar (γ τ - xstar) t₀ (1 / 2 : ℝ) (1 : ℝ)]
      rw [one_smul, add_comm xstar (γ τ - xstar), sub_add_cancel]
    have hstep : ‖(γ τ₁ + t₀ • (γ τ - γ τ₁))
        - (xstar + ((1 - t₀) * ((1:ℝ) / 2) + t₀) • (γ τ - xstar))‖ ≤ 4 * Real.sqrt (S * Ψ) := by
      have hz : γ τ₁ + t₀ • (γ τ - γ τ₁) = (1 - t₀) • γ τ₁ + t₀ • γ τ := by
        rw [smul_sub]
        module
      have hdiff : ((1 - t₀) • γ τ₁ + t₀ • γ τ)
          - ((1 - t₀) • (xstar + ((1:ℝ) / 2) • (γ τ - xstar)) + t₀ • γ τ)
          = (1 - t₀) • (γ τ₁ - (xstar + ((1:ℝ) / 2) • (γ τ - xstar))) := by
        module
      rw [hz, ← hc, hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ht₀.2] : (0:ℝ) ≤ 1 - t₀)]
      calc (1 - t₀) * ‖γ τ₁ - (xstar + ((1:ℝ) / 2) • (γ τ - xstar))‖
          ≤ 1 * (4 * Real.sqrt (S * Ψ)) := by
            refine mul_le_mul ?_ hbound (norm_nonneg _) (by norm_num)
            linarith [ht₀.1]
        _ = 4 * Real.sqrt (S * Ψ) := by ring
    calc ‖γ t - (xstar + ((1 - t₀) * ((1:ℝ) / 2) + t₀) • (γ τ - xstar))‖
        ≤ ‖γ t - (γ τ₁ + t₀ • (γ τ - γ τ₁))‖
          + ‖(γ τ₁ + t₀ • (γ τ - γ τ₁))
            - (xstar + ((1 - t₀) * ((1:ℝ) / 2) + t₀) • (γ τ - xstar))‖ := by
          rw [← sub_add_sub_cancel]
          exact norm_add_le _ _
      _ ≤ 2 * Real.sqrt (S * Ψ) + 4 * Real.sqrt (S * Ψ) := add_le_add hdist hstep
      _ ≤ 6 * Real.sqrt (S * Ψ) := by
          have := Real.sqrt_nonneg (S * Ψ); linarith

end Abstract

end Submission.NBody
