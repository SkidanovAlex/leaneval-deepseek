import Mathlib
import Submission.Work.GM.Affine.far_part_defs

/-!
# The window pair mass is dominated by the `m₁`-sum of the far weight (pointwise)

The window pairs `Pwin T M₁ M₃ B ξ` are the pairs `(m₁,ℓ)` with `m₁ ∈ R1 M₁` and
`2/M₃ < |ℓ - ξ/m₁| ≤ B/M₃`.  Each such pair contributes

`aTerm K M₂ M₃ f ξ (m₁,ℓ) = |m₁|⁻¹ * Bsum f M₂ (ξ/m₁) * (M₃ * ψ̂₁ K (M₃(ℓ - ξ/m₁)))`,

and its squared norm factorises exactly as

`‖aTerm‖² = (1/m₁² * ‖Bsum f M₂ (ξ/m₁)‖²) * (M₃² * ‖ψ̂₁ K (M₃(ξ/m₁ - ℓ))‖²)`,

using only that `ψ̂₁` is even (`psi1hat_even_aux`) and `Complex.normSq` of a real is the
square.  Because the `ℓ` of `Pwin` are additionally restricted to the finite range
`|ℓ| ≤ Lwin T M₁ M₃ B` and satisfy the window condition, the finite sum over `Pwin`
is at most the `m₁`-sum of the *full* `ℓ`-sum over `ℤ` of those factorised terms,
restricted to the window condition.  This is the pointwise ingredient for the window
part of `ghatFar`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `psi1 K` is even. -/
lemma psi1_even_aux (K x : ℝ) : psi1 K (-x) = psi1 K x := by
  unfold psi1
  rw [show K + 1 - -x = K + 1 + x by ring, show K + 1 + -x = K + 1 - x by ring, mul_comm]

/-- The Fourier transform `ψ̂₁ = psi1hat K` is even. -/
lemma psi1hat_even_aux (K u : ℝ) : psi1hat K (-u) = psi1hat K u := by
  set f : ℝ → ℂ := fun t => ((psi1 K t : ℝ) : ℂ) with hf
  have hcomp : f ∘ (fun x : ℝ => -x) = f := by funext t; simp [hf, psi1_even_aux]
  have key := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f u
  rw [show (⇑(LinearIsometryEquiv.neg ℝ) : ℝ → ℝ) = fun x => -x from rfl, hcomp] at key
  rw [psi1hat, psi1hat]
  simpa [hf] using key.symm

/-- The squared norm of `aTerm` factorises. -/
lemma normSq_aTerm (K M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (m ℓ : ℤ) :
    ‖aTerm K M₂ M₃ f ξ (m, ℓ)‖^2
      = (1/(m:ℝ)^2 * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2)
        * (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) := by
  have hpsi : psi1hat K (M₃ * ((ℓ:ℝ) - ξ/(m:ℝ)))
      = psi1hat K (M₃ * (ξ/(m:ℝ) - (ℓ:ℝ))) := by
    rw [show M₃ * ((ℓ:ℝ) - ξ/(m:ℝ)) = -(M₃ * (ξ/(m:ℝ) - (ℓ:ℝ))) by ring, psi1hat_even_aux]
  simp only [aTerm, hpsi, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal]
  have habs : |(m:ℝ)| * |(m:ℝ)| = (m:ℝ) * (m:ℝ) := by rw [← sq, ← sq, sq_abs]
  rw [habs, ← sq, ← sq]
  ring

/-- The contribution of a single `m₁` to the window pair mass, bounded by the `m₁`-th
term of the `Bsum`/`ψ̂₁` sum. -/
lemma winPairMass_per_m (K M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (m : ℤ) (L : ℤ) :
    ENNReal.ofReal (∑ ℓ ∈ Finset.Icc (-L) L,
        (if 2 / M₃ < |((ℓ:ℝ) - ξ/(m:ℝ))| ∧ |((ℓ:ℝ) - ξ/(m:ℝ))| ≤ B/M₃
          then ‖aTerm K M₂ M₃ f ξ (m, ℓ)‖^2 else 0))
      ≤ ENNReal.ofReal (1/(m:ℝ)^2 * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2) *
        ∑' ℓ : ℤ, (if 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)|
          then ENNReal.ofReal (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) else 0) := by
  set A : ℝ := 1/(m:ℝ)^2 * ‖Bsum f M₂ (ξ/(m:ℝ))‖^2 with hA
  have key : ∀ ℓ : ℤ,
      ENNReal.ofReal (if (2 / M₃ < |((ℓ:ℝ) - ξ/(m:ℝ))| ∧ |((ℓ:ℝ) - ξ/(m:ℝ))| ≤ B/M₃)
          then ‖aTerm K M₂ M₃ f ξ (m, ℓ)‖^2 else 0)
        ≤ ENNReal.ofReal A * (if 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)|
            then ENNReal.ofReal (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) else 0) := by
    intro ℓ
    by_cases hQ : (2 / M₃ < |((ℓ:ℝ) - ξ/(m:ℝ))| ∧ |((ℓ:ℝ) - ξ/(m:ℝ))| ≤ B/M₃)
    · rw [if_pos hQ]
      have hcond : 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)| := by rw [abs_sub_comm]; exact hQ.1
      rw [if_pos hcond, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ A)]
      apply ENNReal.ofReal_le_ofReal
      rw [hA]
      exact le_of_eq (normSq_aTerm K M₂ M₃ f ξ m ℓ)
    · rw [if_neg hQ]
      simp
  rw [ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => by split <;> positivity)]
  calc ∑ ℓ ∈ Finset.Icc (-L) L, ENNReal.ofReal (if (2 / M₃ < |((ℓ:ℝ) - ξ/(m:ℝ))| ∧
          |((ℓ:ℝ) - ξ/(m:ℝ))| ≤ B/M₃) then ‖aTerm K M₂ M₃ f ξ (m, ℓ)‖^2 else 0)
      ≤ ∑ ℓ ∈ Finset.Icc (-L) L, ENNReal.ofReal A * (if 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)|
            then ENNReal.ofReal (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) else 0) :=
        Finset.sum_le_sum (fun ℓ _ => key ℓ)
    _ = ENNReal.ofReal A * ∑ ℓ ∈ Finset.Icc (-L) L, (if 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)|
            then ENNReal.ofReal (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) else 0) :=
        (Finset.mul_sum (Finset.Icc (-L) L) _ (ENNReal.ofReal A)).symm
    _ ≤ ENNReal.ofReal A * ∑' ℓ : ℤ, (if 2 / M₃ < |ξ/(m:ℝ) - (ℓ:ℝ)|
            then ENNReal.ofReal (M₃^2 * ‖psi1hat K (M₃*(ξ/(m:ℝ) - (ℓ:ℝ)))‖^2) else 0) :=
        mul_le_mul_right (ENNReal.sum_le_tsum _) _

theorem winPairMass_pointwise_le (K T M₁ M₂ M₃ B : ℝ) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    (f : ℝ → ℝ) (ξ : ℝ) :
    ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
      ≤ ∑ m₁ ∈ R1 M₁,
          ENNReal.ofReal (1 / (m₁ : ℝ) ^ 2 * ‖Bsum f M₂ (ξ / (m₁ : ℝ))‖ ^ 2) *
            (∑' ℓ : ℤ, (if 2 / M₃ < |ξ / (m₁ : ℝ) - (ℓ : ℝ)| then
              ENNReal.ofReal (M₃ ^ 2 * ‖psi1hat K (M₃ * (ξ / (m₁ : ℝ) - (ℓ : ℝ)))‖ ^ 2) else 0)) := by
  have hM₁pos : 0 < M₁ := hM₁
  have hM₃pos : 0 < M₃ := hM₃
  rw [Pwin, Finset.sum_filter]
  rw [show (R1 M₁).product (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B))
      = R1 M₁ ×ˢ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B) from rfl]
  rw [Finset.sum_product]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun m _ => Finset.sum_nonneg (fun ℓ _ => by split <;> positivity))]
  apply Finset.sum_le_sum
  intro m _
  exact winPairMass_per_m K M₂ M₃ B f ξ m (Lwin T M₁ M₃ B)

end

end Work.GM.Affine
