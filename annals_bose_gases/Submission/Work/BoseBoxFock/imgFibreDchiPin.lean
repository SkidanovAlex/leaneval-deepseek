import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imagesFibre
import Submission.Work.BoseBoxFock.pairRowDirChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreDchiPin`

The fibre Dirichlet content `imgFibreDχ ℓ p F` is the *slot-`p.1` summand* of the full `χ`-weighted
Dirichlet content `pinDirChi ℓ Θ` of the (complexified) pin `Θ = (fun x => ((F x : ℝ) : ℂ))`:

    imgFibreDχ ℓ p F = ∫_{abox n ℓ} χ_ℓ(x_{p.1})² Σ_j (∂_{p.1,j} F x)² ,
    pinDirChi ℓ Θ    = ∫_{abox n ℓ} Σ_i Σ_j χ_ℓ(x_i)² ‖∂_{i,j} Θ x‖² ,

and `‖∂_{i,j} Θ x‖² = (∂_{i,j} F x)²` because the derivative of the complexification of a real
function is the complexification of its derivative.  Hence the inequality is the elementary
observation that a nonnegative summand is bounded by the whole finite sum.

Everything here is proved directly: the only measure-theoretic input is that continuous functions
are integrable on `abox n ℓ` (which is compact *for every* side `ℓ`, including `ℓ ≤ 0`; the
corpus's `abox_compact` requires `0 < ℓ`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Xn" => Submission.BoseGases.X

/-- **`abox N ℓ` is compact for every side `ℓ`.**  The corpus's `abox_compact` requires `0 < ℓ`;
here no sign hypothesis is available.  Proof: `abox N ℓ` is closed (`abox_isClosed`) and contained
in `abox N (|ℓ| + 1)`, which is compact. -/
theorem isCompact_aboxAll (N : ℕ) (ℓ : ℝ) : IsCompact (Submission.BoseGases.abox N ℓ) := by
  refine IsCompact.of_isClosed_subset
    (Submission.BoseGases.abox_compact N (show (0 : ℝ) < |ℓ| + 1 by positivity))
    (Submission.BoseGases.abox_isClosed N ℓ) ?_
  intro x hx
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  have hxi : x i ∈ Submission.BoseGases.acube ℓ := hx i
  rw [Submission.BoseGases.mem_acube_iff] at hxi ⊢
  intro m
  obtain ⟨h1, h2⟩ := hxi m
  have h3 : -ℓ ≤ |ℓ| := neg_le_abs ℓ
  have h4 : ℓ ≤ |ℓ| := le_abs_self ℓ
  exact ⟨by linarith, by linarith⟩

/-- A continuous function on `X n` is integrable over `abox n ℓ`, for **every** `ℓ`. -/
theorem integrableOn_abox_of_continuous_all {n : ℕ} {ℓ : ℝ} {f : Xn n → ℝ}
    (hf : Continuous f) : IntegrableOn f (Submission.BoseGases.abox n ℓ) :=
  ContinuousOn.integrableOn_compact (isCompact_aboxAll n ℓ) hf.continuousOn

theorem imgFibreDchiPin {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n}
    {F : Submission.BoseGases.X n → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Work.BoseBoxFock.imgFibreDχ ℓ p F
      ≤ Work.BoseBoxFock.pinDirChi ℓ (fun x => ((F x : ℝ) : ℂ)) := by
  set Θ : Xn n → ℂ := fun x => ((F x : ℝ) : ℂ) with hΘdef
  -- the derivative of the complexification is the complexification of the derivative
  have hcpx : ∀ (v x : Xn n), fderiv ℝ Θ x v = ((fderiv ℝ F x v : ℝ) : ℂ) := by
    intro v x
    have h1 : HasFDerivAt Θ ((Complex.ofRealCLM).comp (fderiv ℝ F x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp _
        ((hF.differentiable (by simp) x).hasFDerivAt)
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  have hnorm : ∀ (v : Xn n) (x : Xn n), ‖fderiv ℝ Θ x v‖ ^ 2 = (fderiv ℝ F x v) ^ 2 := by
    intro v x
    rw [hcpx v x, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  -- the pointwise inequality: a nonnegative summand is at most the whole sum
  have hpt : ∀ x : Xn n,
      (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2
        ≤ ∑ i : Fin n, ∑ j : Fin 3,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
              * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2 := by
    intro x
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      (Finset.single_le_sum (f := fun i : Fin n => ∑ j : Fin 3,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
            * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
        (Finset.mem_univ p.1))
    · rw [hnorm (slotDirVec p.1 j) x]
  -- continuity (hence integrability on the box) of both integrands
  have hderiv : Continuous (fun x : Xn n => fderiv ℝ F x) := hF.continuous_fderiv (by simp)
  have hcont1 : Continuous (fun x : Xn n => (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2
      * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply p.1)).pow 2).mul
      (continuous_finsetSum _ fun j _ => (hderiv.clm_apply continuous_const).pow 2)
  have hcont2 : Continuous (fun x : Xn n => ∑ i : Fin n, ∑ j : Fin 3,
      (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
        * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2) := by
    have hfun : (fun x : Xn n => ∑ i : Fin n, ∑ j : Fin 3,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
            * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2)
        = fun x : Xn n => ∑ i : Fin n, ∑ j : Fin 3,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
              * (fderiv ℝ F x (slotDirVec i j)) ^ 2 := by
      funext x
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        (by rw [hnorm (slotDirVec i j) x])
    rw [hfun]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2).mul
      ((hderiv.clm_apply continuous_const).pow 2)
  have hfint : IntegrableOn (fun x : Xn n => (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2
      * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    integrableOn_abox_of_continuous_all (n := n) (ℓ := ℓ) hcont1
  have hgint : IntegrableOn (fun x : Xn n => ∑ i : Fin n, ∑ j : Fin 3,
      (Submission.BoseGases.chiScale ℓ (x i)) ^ 2
        * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    integrableOn_abox_of_continuous_all (n := n) (ℓ := ℓ) hcont2
  rw [imgFibreDχ, pinDirChi]
  exact MeasureTheory.setIntegral_mono hfint hgint hpt

end Work.BoseBoxFock
