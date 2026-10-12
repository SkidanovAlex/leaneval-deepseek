import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.TauRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.tauTilde_lip` — Lipschitz growth of `τ̃`

`τ̃` is radial, and the hypotheses pin it down completely on the region of
interest: the threshold `ρ₀` dominates `(d s ℓ)⁻¹`, so for `‖k‖ ≥ ρ₀` both
arguments `‖k‖/(2sℓ)⁻¹ = 2sℓ‖k‖ ≥ 2` and `‖k‖/(2dsℓ)⁻¹ = 2dsℓ‖k‖ ≥ 2` lie in
the quadratic regime of `φ`.  There

`τ̃ k = (1-ε_T)((‖k‖ - 3a/2)² + c₀a²) + ε_T((‖k‖ - 3b/2)² + c₀b²)`,
`a = (2sℓ)⁻¹`, `b = (2dsℓ)⁻¹`,

so the difference telescopes to

`τ̃ p - τ̃ q = (‖p‖-‖q‖)(‖p‖+‖q‖ - 3((1-ε_T)a + ε_T b))`,

and the bracket is between `0` and `‖p‖+‖q‖` because
`3((1-ε_T)a + ε_T b) ≤ ρ₀ ≤ ‖p‖, ‖q‖`.  With `|‖p‖-‖q‖| ≤ ‖p-q‖` this is the
stated Lipschitz bound.
-/

namespace Work.BoseGateFS

theorem tauTilde_lip {φ : ℝ → ℝ}
    (hφge : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    (hφquad : ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ r : ℝ, 2 ≤ r → φ r = (r - 3 / 2) ^ 2 + c₀)
    {eT s d ℓ ρ₀ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hℓ : 0 < ℓ) (hρ₀ : (d * s * ℓ)⁻¹ ≤ ρ₀)
    (hC : 3 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹) ≤ ρ₀)
    {p q : EuclideanSpace ℝ (Fin 3)} (hp : ρ₀ ≤ ‖p‖) (hq : ρ₀ ≤ ‖q‖) :
    |Work.BoseGateFS.tauTilde φ eT s d ℓ p - Work.BoseGateFS.tauTilde φ eT s d ℓ q|
      ≤ 2 * (‖p‖ + ‖q‖) * ‖p - q‖ := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := hφquad
  -- On the region `‖k‖ ≥ ρ₀`, `τ̃ k` is an explicit quadratic form of `‖k‖`.
  have hsub : ∀ k : EuclideanSpace ℝ (Fin 3), ρ₀ ≤ ‖k‖ →
      Work.BoseGateFS.tauTilde φ eT s d ℓ k
        = (1 - eT) * ((‖k‖ - 3 / 2 * (2 * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * s * ℓ)⁻¹) ^ 2)
          + eT * ((‖k‖ - 3 / 2 * (2 * d * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * d * s * ℓ)⁻¹) ^ 2) := by
    intro k hk
    -- `‖k‖ ≥ ρ₀ ≥ (dsℓ)⁻¹` puts both arguments of `φ` above the threshold `2`.
    have hK1 : 2 ≤ ‖k‖ / (2 * s * ℓ)⁻¹ := by
      have hstep : (d * s * ℓ)⁻¹ * (2 * s * ℓ) ≤ ‖k‖ * (2 * s * ℓ) :=
        mul_le_mul_of_nonneg_right (le_trans hρ₀ hk) (by positivity)
      have hcalc : (d * s * ℓ)⁻¹ * (2 * s * ℓ) = 2 / d := by field_simp
      have hfin : 2 ≤ ‖k‖ * (2 * s * ℓ) := by
        have h2d : (2 : ℝ) ≤ 2 / d := by rw [le_div_iff₀ hd0]; linarith
        linarith [hcalc ▸ hstep]
      rwa [div_eq_mul_inv, inv_inv]
    have hK2 : 2 ≤ ‖k‖ / (2 * d * s * ℓ)⁻¹ := by
      have hstep : (d * s * ℓ)⁻¹ * (2 * d * s * ℓ) ≤ ‖k‖ * (2 * d * s * ℓ) :=
        mul_le_mul_of_nonneg_right (le_trans hρ₀ hk) (by positivity)
      have hcalc : (d * s * ℓ)⁻¹ * (2 * d * s * ℓ) = 2 := by field_simp
      have hfin : 2 ≤ ‖k‖ * (2 * d * s * ℓ) := by linarith [hcalc ▸ hstep]
      rwa [div_eq_mul_inv, inv_inv]
    rw [Work.BoseGateFS.tauTilde, hc₀ _ hK1, hc₀ _ hK2]
    field_simp
  -- The quadratic form telescopes.
  have hdiff : ∀ u v : ℝ,
      ((1 - eT) * ((u - 3 / 2 * (2 * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * s * ℓ)⁻¹) ^ 2)
        + eT * ((u - 3 / 2 * (2 * d * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * d * s * ℓ)⁻¹) ^ 2))
      - ((1 - eT) * ((v - 3 / 2 * (2 * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * s * ℓ)⁻¹) ^ 2)
        + eT * ((v - 3 / 2 * (2 * d * s * ℓ)⁻¹) ^ 2 + c₀ * ((2 * d * s * ℓ)⁻¹) ^ 2))
      = (u - v) * (u + v - 3 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹)) := by
    intro u v; ring
  rw [hsub p hp, hsub q hq, hdiff (‖p‖) (‖q‖), abs_mul]
  have hA0 : 0 ≤ 3 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹) := by
    have h1 : 0 ≤ (1 - eT) * (2 * s * ℓ)⁻¹ := mul_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ eT * (2 * d * s * ℓ)⁻¹ := mul_nonneg heT0 (by positivity)
    linarith
  have hup : 0 ≤ ‖p‖ + ‖q‖ - 3 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹) := by
    linarith [hC, hp]
  rw [abs_of_nonneg hup]
  have hnorm : |‖p‖ - ‖q‖| ≤ ‖p - q‖ := abs_norm_sub_norm_le p q
  calc |‖p‖ - ‖q‖| * (‖p‖ + ‖q‖ - 3 * ((1 - eT) * (2 * s * ℓ)⁻¹ + eT * (2 * d * s * ℓ)⁻¹))
      ≤ ‖p - q‖ * (‖p‖ + ‖q‖) := by
        refine mul_le_mul hnorm ?_ hup (norm_nonneg _)
        linarith [hA0]
    _ ≤ 2 * (‖p‖ + ‖q‖) * ‖p - q‖ := by
        nlinarith [norm_nonneg (p - q), norm_nonneg p, norm_nonneg q]

end Work.BoseGateFS
