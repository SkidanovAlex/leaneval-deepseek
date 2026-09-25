import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

/-!
# The `n`-fold circle convolution is bounded by the product of the sup bounds

If each factor `F i` is bounded on the circle by `a i ≥ 0`, then the `n`-fold convolution
`✻_i F i` is bounded (uniformly in `ξ`) by the product `∏ i, a i`.

The proof is the evident induction on `n`, using
`‖∫‖ ≤ ∫ ‖·‖` (`norm_integral_le_integral_norm`) and the fact that the Haar measure on the
circle is a probability measure, so that the integral of the constant `∏_{i<n} a i * a n` is
that same constant.  No measurability of the `F i` is needed: if a factor is not integrable the
Bochner integral is `0` and the inequality holds trivially, which is exactly what
`integral_mono_of_nonneg` (needing only the integrability of the *constant* majorant) exploits.
-/

open MeasureTheory Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The `n`-fold circle convolution `circConvFin n F` is bounded by `∏ i, a i` whenever each
factor `F i` is bounded by `a i ≥ 0`. -/
theorem norm_circConvFin_le {n : ℕ} {F : Fin n → Circle → ℂ} {a : Fin n → ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i ξ, ‖F i ξ‖ ≤ a i) (ξ : Circle) :
    ‖circConvFin n F ξ‖ ≤ ∏ i, a i := by
  suffices H : ∀ n, ∀ (F : Fin n → Circle → ℂ) (a : Fin n → ℝ),
      (∀ i, 0 ≤ a i) → (∀ i ξ, ‖F i ξ‖ ≤ a i) → ∀ ξ, ‖circConvFin n F ξ‖ ≤ ∏ i, a i from
    H n F a ha0 ha ξ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F a ha0 ha ξ
    rcases n with _ | _ | k
    · rw [show circConvFin 0 F = fun _ => (1 : ℂ) from rfl]
      simp
    · rw [show circConvFin 1 F = F 0 from rfl]
      simpa using ha 0 ξ
    · have hdef : circConvFin (k + 2) F =
          circConv (circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc))
            (F (Fin.last (k + 1))) := rfl
      rw [hdef]
      have ihA : ∀ η, ‖circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc) η‖ ≤
          ∏ i : Fin (k + 1), a i.castSucc :=
        fun η => ih (k + 1) (by omega) (fun i : Fin (k + 1) => F i.castSucc)
          (fun i => a i.castSucc) (fun i => ha0 i.castSucc) (fun i η => ha i.castSucc η) η
      have hP0 : 0 ≤ ∏ i : Fin (k + 1), a i.castSucc :=
        Finset.prod_nonneg (fun i _ => ha0 i.castSucc)
      have hbound : ∫ η, (‖circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc) η‖ *
            ‖F (Fin.last (k + 1)) (ξ - η)‖) ∂AddCircle.haarAddCircle ≤
          (∏ i : Fin (k + 1), a i.castSucc) * a (Fin.last (k + 1)) :=
        le_trans (integral_mono_of_nonneg
          (f := fun η => ‖circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc) η‖ *
            ‖F (Fin.last (k + 1)) (ξ - η)‖)
          (g := fun _ => (∏ i : Fin (k + 1), a i.castSucc) * a (Fin.last (k + 1)))
          (Filter.Eventually.of_forall fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (integrable_const (μ := AddCircle.haarAddCircle) _)
          (Filter.Eventually.of_forall fun η =>
            mul_le_mul (ihA η) (ha (Fin.last (k + 1)) (ξ - η)) (norm_nonneg _) hP0))
          (le_of_eq (by rw [integral_const]; simp))
      calc ‖circConv (circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc))
              (F (Fin.last (k + 1))) ξ‖
          ≤ ∫ η, ‖circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc) η *
              F (Fin.last (k + 1)) (ξ - η)‖ ∂AddCircle.haarAddCircle :=
            norm_integral_le_integral_norm _
        _ = ∫ η, (‖circConvFin (k + 1) (fun i : Fin (k + 1) => F i.castSucc) η‖ *
              ‖F (Fin.last (k + 1)) (ξ - η)‖) ∂AddCircle.haarAddCircle :=
            integral_congr_ae (Filter.Eventually.of_forall fun η => norm_mul _ _)
        _ ≤ (∏ i : Fin (k + 1), a i.castSucc) * a (Fin.last (k + 1)) := hbound
        _ = ∏ i : Fin (k + 2), a i :=
            (Fin.prod_univ_castSucc (fun i : Fin (k + 2) => a i)).symm

end Work.BourgainPlan.IonescuWainger
