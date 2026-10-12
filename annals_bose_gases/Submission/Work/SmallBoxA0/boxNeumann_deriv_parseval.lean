import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.SmallBoxA0.sin_parseval_shifted
import Submission.Work.SmallBoxFourierBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `boxNeumann` Dirichlet-form (derivative) Parseval identity

`Work.SmallBoxA0.boxNeumann_deriv_parseval`:

    ∫_{−ℓ/2}^{ℓ/2} (g')² = ∑_{k≥0} ((kπ/ℓ)²) · (2/ℓ)·(∫_{−ℓ/2}^{ℓ/2} g·u_k)² ,

where `u_k = boxNeumann ℓ k` is the Neumann (cosine) mode
`cos ((kπ/ℓ)(x+ℓ/2))`.

This is the spectral identity `‖g'‖² = Σ_k λ_k ⟨g,u_k⟩²/‖u_k‖²` for the
Neumann Laplacian `−d²/dx²` on the centred interval: the eigenvalues are
`λ_k = (kπ/ℓ)²` and the squared mode norms are `‖u_0‖² = ℓ`, `‖u_k‖² = ℓ/2`
(`k ≥ 1`), so the `k`-th term carries the weight `2/ℓ`.  The constant mode
drops out because `λ_0 = 0`.

The proof routes through the **Dirichlet (sine) basis**.  Writing
`s_k(x) = sin ((kπ/ℓ)(x+ℓ/2))` (which vanishes at both endpoints), the sine
basis Parseval (`Work.SmallBoxA0.sin_parseval_shifted`, the sine companion of
`BoseGases.boxNeumann_parseval`) applied to `F = g'` gives

    ∫ (g')² = ∑_k (2/ℓ)(∫ g'·s_k)² ,

and one integration by parts (the boundary term dies since `s_k(±ℓ/2) = 0`)
gives `∫ g'·s_k = −(kπ/ℓ)∫ g·u_k`, so

    ∫ (g')² = ∑_k (2/ℓ)(kπ/ℓ)²(∫ g·u_k)² .
-/

namespace Work.SmallBoxA0

open MeasureTheory Set
open scoped Real BigOperators Topology ContDiff
open Submission BoseGases

/-- **Integration by parts against the Neumann sine.**  For a `C²` function `g`
the boundary term of `g·sin((kπ/ℓ)(x+ℓ/2))` vanishes at both endpoints, so

    ∫_{−ℓ/2}^{ℓ/2} g'(x) sin((kπ/ℓ)(x+ℓ/2)) dx
      = −(kπ/ℓ) ∫_{−ℓ/2}^{ℓ/2} g(x) boxNeumann ℓ k x dx .

This is the `L²`-adjoint pairing relating the Dirichlet form to the Neumann mode. -/
lemma deriv_mul_sin_ibp_aux {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (k : ℕ) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2),
        deriv g x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))
      = - ((k : ℝ) * Real.pi / ℓ) *
          (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ k x) := by
  set a : ℝ := (k : ℝ) * Real.pi / ℓ with ha
  have hderiv_g : ∀ x ∈ Set.uIcc (-(ℓ / 2)) (ℓ / 2), HasDerivAt g (deriv g x) x := by
    intro x _
    exact (hg.differentiable (by norm_num) x).hasDerivAt
  have hderiv_sin : ∀ x ∈ Set.uIcc (-(ℓ / 2)) (ℓ / 2),
      HasDerivAt (fun y : ℝ => Real.sin (a * (y + ℓ / 2))) (a * Real.cos (a * (x + ℓ / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => a * (y + ℓ / 2)) a x := by
      simpa using ((hasDerivAt_id x).add_const (ℓ / 2)).const_mul a
    simpa [mul_comm] using h1.sin
  have hint_g : IntervalIntegrable (deriv g) volume (-(ℓ / 2)) (ℓ / 2) :=
    (hg.continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hint_sin : IntervalIntegrable (fun x : ℝ => a * Real.cos (a * (x + ℓ / 2)))
      volume (-(ℓ / 2)) (ℓ / 2) := by
    apply Continuous.intervalIntegrable
    continuity
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := fun y : ℝ => Real.sin (a * (y + ℓ / 2)))
    (u' := deriv g) (v' := fun x : ℝ => a * Real.cos (a * (x + ℓ / 2)))
    hderiv_g hderiv_sin hint_g hint_sin
  have hb1 : Real.sin (a * (ℓ / 2 + ℓ / 2)) = 0 := by
    have h : a * (ℓ / 2 + ℓ / 2) = (k : ℝ) * Real.pi := by
      rw [ha]; field_simp; ring
    rw [h, Real.sin_nat_mul_pi]
  have hb2 : Real.sin (a * (-(ℓ / 2) + ℓ / 2)) = 0 := by
    have h : a * (-(ℓ / 2) + ℓ / 2) = 0 := by ring
    rw [h, Real.sin_zero]
  have hkey : (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * (a * Real.cos (a * (x + ℓ / 2))))
      = - ∫ x in (-(ℓ / 2))..(ℓ / 2), deriv g x * Real.sin (a * (x + ℓ / 2)) := by
    rw [hIBP, hb1, hb2]
    ring
  have hconst : (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * (a * Real.cos (a * (x + ℓ / 2))))
      = a * ∫ x in (-(ℓ / 2))..(ℓ / 2), g x * Real.cos (a * (x + ℓ / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hcos_eq : (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * Real.cos (a * (x + ℓ / 2)))
      = ∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ k x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp [boxNeumann, ha]
  have hmain : (∫ x in (-(ℓ / 2))..(ℓ / 2), deriv g x * Real.sin (a * (x + ℓ / 2)))
      = -a * (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ k x) := by
    rw [hcos_eq] at hconst
    linarith [hkey, hconst]
  simpa [ha] using hmain

/-- The `boxNeumann` Dirichlet-form Parseval identity. -/
lemma boxNeumann_deriv_parseval {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (deriv g x) ^ 2)
      = ∑' k : ℕ, ((k : ℝ) * π / ℓ) ^ 2 *
          ((2 / ℓ) * (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ k x) ^ 2) := by
  have hdg : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hsp := sin_parseval_shifted (ℓ := ℓ) hℓ (F := deriv g) hdg
  rw [hsp]
  apply tsum_congr
  intro k
  rw [deriv_mul_sin_ibp_aux (ℓ := ℓ) hℓ hg k]
  ring

end Work.SmallBoxA0
