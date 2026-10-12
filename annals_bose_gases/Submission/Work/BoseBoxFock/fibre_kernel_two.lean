import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_fibre_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fibre_kernel_two` — the two-coordinate fibre form of a pair kernel

The third term of block II of the FS `Q₂` row (`potPairRows_kernelExpanded`) is a `pairSet` sum of
triple integrals in which the pair kernel is evaluated at **two coordinates of the same
configuration**: `K (x p.1) (x p.2)`.  To feed the kernel-limit error estimate
(`K1exp_sub_K1lim_pairing_le`, whose variable is a function `G : ℝ³ × ℝ³ → ℂ` integrated over
`boxL × boxL`) that integral must be written as `∫_w ∫_{w'} K w w' · G w w'`.

This module performs exactly that reduction: for `K : ℝ³ → ℝ³ → ℂ`, `H : (Fin n → ℝ³) → ℂ` and
`i ≠ j` with `x ↦ K (x i) (x j) * H x` integrable,

    ∫_x K (x i) (x j) · H x
      = ∫_w ∫_{w'} K w w' · (∫_{x'} H (fun k => if k = i then w else if k = j then w' else x' k))

where `x'` runs over the remaining coordinates `{k // k ≠ i ∧ k ≠ j}`.

The proof is the measure-preserving coordinate split `Work.BoseBoxFock.integral_fibre_two`
followed by pulling the (now constant) kernel value `K w w'` out of the inner integral
(`MeasureTheory.integral_const_mul`, which needs no integrability hypothesis).

In the consumer, `H` is the state representative (measurable, bounded, and `HasCompactSupport`
thanks to `Function.support Θ ⊆ Work.MB.boxPow n ℓ`), `K` is measurable and bounded, and the
integrability hypothesis follows from those (the support of `x ↦ K (x i) (x j) * H x` is contained
in `tsupport H`, which is compact, hence of finite measure).

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The two-coordinate fibre form of a pair kernel.** -/
theorem fibre_kernel_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {K : E3 → E3 → ℂ} {H : (Fin n → E3) → ℂ}
    (hG : MeasureTheory.Integrable (fun x : Fin n → E3 => K (x i) (x j) * H x)) :
    (∫ x : Fin n → E3, K (x i) (x j) * H x)
      = ∫ w : E3, ∫ w' : E3, K w w' *
          (∫ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
            H (fun k => if h : k = i then w
                        else if h' : k = j then w' else x' ⟨k, h, h'⟩)) := by
  classical
  rw [integral_fibre_two hij hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  beta_reduce
  rw [show (fun x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3 =>
        K ((fun k => if h : k = i then w else if h' : k = j then w' else x' ⟨k, h, h'⟩) i)
          ((fun k => if h : k = i then w else if h' : k = j then w' else x' ⟨k, h, h'⟩) j)
        * H (fun k => if h : k = i then w else if h' : k = j then w' else x' ⟨k, h, h'⟩))
      = (fun x' => K w w' * H (fun k => if h : k = i then w
          else if h' : k = j then w' else x' ⟨k, h, h'⟩))
      from by
        funext x'
        simp [Ne.symm hij]]
  exact MeasureTheory.integral_const_mul (K w w') _

end Work.BoseBoxFock
