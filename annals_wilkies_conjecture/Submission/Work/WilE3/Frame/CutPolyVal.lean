/-
  annals_wilkies_conjecture, AREA E3, count half: the value of a cut form at a complex point.

  `cutPoly ι μ x = Σ_{i : U k ι} C (μ i) * (X i - C (x i))` is the real affine form through `x` in
  the `ιᶜ`-coordinates; its complexified evaluation at `z` is `Σ_i μ i * (z_i - x_i)`.  In
  particular it vanishes at `toC x`, and along the straightened curve
  `t ↦ Ψ (u₀ + t • w_ℂ, 0)` it equals `t * Σ_i μ i w_i`.
-/
import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.eaEvalC_toC

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {k r j : ℕ}

/-- Complexified evaluation of a cut form: `eaEvalC c (cutPoly ι μ x) z = Σ_i μ i * (z_i - x_i)`. -/
theorem eaEvalC_cutPoly (c : EAChain k r) (ι : Fin j → Fin k) (μ : U k ι → ℝ)
    (x : Fin k → ℝ) (z : Fin k → ℂ) :
    Work.WilE3.eaEvalC c (cutPoly ι μ x) z =
      ∑ i : U k ι, (μ i : ℂ) * (z i.1 - (x i.1 : ℂ)) := by
  simp only [cutPoly, map_sum, map_mul, map_sub, Work.WilE3.API.eaEvalC_eq,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', Work.WilE3.API.eaPsi, Sum.elim_inl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (algebraMap ℝ ℂ) (μ i) = (μ i : ℂ) from rfl,
    show (algebraMap ℝ ℂ) (x i.1) = (x i.1 : ℂ) from rfl]

/-- A cut form vanishes at `x`. -/
theorem eaEvalC_cutPoly_toC (c : EAChain k r) (ι : Fin j → Fin k) (μ : U k ι → ℝ)
    (x : Fin k → ℝ) : Work.WilE3.eaEvalC c (cutPoly ι μ x) (toC x) = 0 := by
  rw [eaEvalC_cutPoly]
  exact Finset.sum_eq_zero fun i _ => by simp [toC]

end

end Work.WilE3.Frame
