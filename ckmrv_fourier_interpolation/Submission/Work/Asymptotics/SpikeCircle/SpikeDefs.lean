import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf


noncomputable section
open UpperHalfPlane
open scoped Topology Manifold

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels Work.Residues

def jlDiff (τ : UpperHalfPlane) : ℂ → ℂ :=
  fun w => jInvariantFun τ - jInvariantFun (UpperHalfPlane.ofComplex w)

def D1 (τ : UpperHalfPlane) : ℂ → ℂ := dslope (jlDiff τ) ((τ : ℂ) - 1)

def D2 (τ : UpperHalfPlane) : ℂ → ℂ := dslope (jlDiff τ) ((τ : ℂ) + 1)

def Tleft (τ : UpperHalfPlane) (w : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * (D1 τ w - D2 τ w)

def Wlift (ℓ : LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (w : ℂ) : ℂ :=
  DeltaFun τ * DeltaFun (UpperHalfPlane.ofComplex w) *
    (AfunFun ℓ d τ (UpperHalfPlane.ofComplex w) - Tleft τ w)

/-- The principal part subtracted in the statement. -/
def PP (τ ζ : UpperHalfPlane) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    (1 / ((ζ : ℂ) - ((τ : ℂ) - 1)) - 1 / ((ζ : ℂ) - ((τ : ℂ) + 1)))

/-! ## Elementary coercion lemmas -/

lemma im_sub_one (τ : UpperHalfPlane) : (((τ : ℂ) - 1)).im = τ.im := by
  rw [Complex.sub_im, Complex.one_im, sub_zero, UpperHalfPlane.coe_im]

lemma im_add_one (τ : UpperHalfPlane) : (((τ : ℂ) + 1)).im = τ.im := by
  rw [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im]

lemma ofComplex_sub_one (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex ((τ : ℂ) - 1) = ((-1 : ℝ) +ᵥ τ : UpperHalfPlane) := by
  have h := UpperHalfPlane.ofComplex_apply_of_im_pos (z := (τ : ℂ) - 1)
    (by rw [im_sub_one]; exact τ.im_pos)
  rw [h]
  exact UpperHalfPlane.ext (by rw [UpperHalfPlane.coe_vadd]; push_cast; ring)

lemma ofComplex_add_one (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex ((τ : ℂ) + 1) = ((1 : ℝ) +ᵥ τ : UpperHalfPlane) := by
  have h := UpperHalfPlane.ofComplex_apply_of_im_pos (z := (τ : ℂ) + 1)
    (by rw [im_add_one]; exact τ.im_pos)
  rw [h]
  exact UpperHalfPlane.ext (by rw [UpperHalfPlane.coe_vadd]; push_cast; ring)

lemma ofComplex_self (τ : UpperHalfPlane) :
    UpperHalfPlane.ofComplex (τ : ℂ) = τ :=
  UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos

lemma coe_neg_one_vadd (τ : UpperHalfPlane) :
    ((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = (τ : ℂ) - 1 := by
  rw [UpperHalfPlane.coe_vadd]; push_cast; ring

lemma coe_one_vadd (τ : UpperHalfPlane) :
    ((((1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.coe_vadd]; push_cast; ring

/-! ## The values of `AfunFun` at the three special points -/

lemma AfunFun_eq_div (ℓ : LogLambdaData) (d : ℕ) (τ z : UpperHalfPlane) :
    AfunFun ℓ d τ z = KfunClear ℓ d τ z / (DeltaFun τ * DeltaFun z ^ dpow d) := by
  rw [AfunFun, AfunPlus, AfunMinus, KfunClear]
  ring

lemma AfunFun_self (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    AfunFun ℓ d τ τ = 0 := by
  rw [AfunFun_eq_div, KaxisMid.KbcAux2.KfunClear_self ℓ d hd τ]
  simp

lemma AfunFun_pos (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    AfunFun ℓ d τ ((1 : ℝ) +ᵥ τ) = (1 / (2 * (Real.pi : ℂ))) * jprime ((1 : ℝ) +ᵥ τ) := by
  have h1 := AfunPlus_neg_one d hd ((1 : ℝ) +ᵥ τ)
  have h2 := AfunMinus_neg_one ℓ d hd ((1 : ℝ) +ᵥ τ)
  rw [show ((-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) : UpperHalfPlane) = τ from by
    rw [← add_vadd]; norm_num] at h1 h2
  rw [AfunFun, h1, h2]
  ring

lemma AfunFun_neg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    AfunFun ℓ d τ ((-1 : ℝ) +ᵥ τ) = -(1 / (2 * (Real.pi : ℂ))) * jprime ((-1 : ℝ) +ᵥ τ) := by
  have h1 := AfunFun_vadd_one ℓ d hd ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ : UpperHalfPlane) = τ from by
    rw [← add_vadd]; norm_num] at h1
  exact h1

