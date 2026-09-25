/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `‖∂̄f‖²_{L²_φ}` as a double sum of the real pairings `rpair0`

This file proves `Work.Hormander.Weights.normSq2_dbarForm_rpair0`, the `rpair0`
variant of `Work.Hormander.Weights.normSq2_dbarForm`: for a real `C¹` weight `φ`
and a compactly supported `C¹` `(0,1)`-form `f`,

  `‖∂̄f‖²_{L²_φ} = (1/2) · Σ_{j,k} rpair0 φ (∂̄f)_{jk} (∂̄f)_{jk}`

with the *real* pairing `rpair0 φ u v = ∫ Re (u z · conj (v z)) e^{-φ z}` instead
of `Re ⟪u,v⟫_{L²_φ}`.  Since `rpair0 φ u u = ‖u‖²_{L²_φ}`, the diagonal terms are
exactly the weighted integrals `∫ ‖(∂̄f)_{jk} z‖² e^{-φ z}`.

The factor `1/2` in front of the double sum is the constant appearing in the
definition of `normSq2`, following the antisymmetric (orthonormal basis)
convention `Σ_{j<k} ‖F j k‖² = (1/2) Σ_{j,k} ‖F j k‖²`.
-/
import Mathlib
import Submission.Work.Hormander.Weights.normSq2_dbarForm
import Submission.Work.Hormander.Weights.Rint

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

theorem normSq2_dbarForm_rpair0 {n : ℕ} (φ : Cn n → ℝ) (f : Form1 n) (hφ : ContDiff ℝ 1 φ)
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    normSq2 φ (dbarForm f)
      = (1 / 2) * ∑ j, ∑ k,
          rpair0 φ (dbarForm f j k) (dbarForm f j k) := by
  -- integrability of every weighted coefficient squared norm
  have hint : ∀ j k, Integrable (fun z => ‖dbarForm f j k z‖ ^ 2 * wn n φ z) := by
    intro j k
    have hcont : Continuous (fun z => dbarForm f j k z) :=
      (continuous_dbarCoord (hf j) k).sub (continuous_dbarCoord (hf k) j)
    have hcs : HasCompactSupport (fun z => dbarForm f j k z) :=
      (hasCompactSupport_dbarCoord (hfs j) k).sub (hasCompactSupport_dbarCoord (hfs k) j)
    exact integrable_normSq_mul_wn hcont hcs hφ
  -- the left hand side, with the finite sums pulled out of the integral
  have hL : normSq2 φ (dbarForm f)
      = (1 / 2) * ∑ j, ∑ k, ∫ z, ‖dbarForm f j k z‖ ^ 2 * wn n φ z := by
    rw [normSq2]
    rw [show (fun z => ((1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z)
        = fun z => (1 / 2) * ((∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z) from by
          funext z; ring]
    rw [integral_const_mul]
    congr 1
    rw [show (fun z => (∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2) * wn n φ z)
        = fun z => ∑ j, ∑ k, ‖dbarForm f j k z‖ ^ 2 * wn n φ z from by
          funext z
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]]
    rw [MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j z => ∑ k, ‖dbarForm f j k z‖ ^ 2 * wn n φ z)
        (fun j _ => MeasureTheory.integrable_finsetSum Finset.univ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_finsetSum Finset.univ
        (f := fun k z => ‖dbarForm f j k z‖ ^ 2 * wn n φ z)
        (fun k _ => hint j k)]
  -- the right hand side, via the diagonal pairing identity
  have hR : (1 / 2) * ∑ j, ∑ k, rpair0 φ (dbarForm f j k) (dbarForm f j k)
      = (1 / 2) * ∑ j, ∑ k, ∫ z, ‖dbarForm f j k z‖ ^ 2 * wn n φ z := by
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [rpair0_self]
    rfl
  exact hL.trans hR.symm

end Work.Hormander.Weights
