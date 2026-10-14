import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllipticEst.DzCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `z² ∂_zz Ψ = D_z²Ψ - D_z Ψ` pointwise (the two slice derivatives involved being the
`z → Ψ z θ` and `z → ∂_zΨ z θ` ones). -/
theorem zsq_pzIter2_eq (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ := by
  have hd : deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z
      = Work.Spaces.pz Ψ z θ + z * deriv (fun z' => Work.Spaces.pz Ψ z' θ) z := by
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
        = (fun z' : ℝ => z') * (fun z' => Work.Spaces.pz Ψ z' θ) := by
      funext x; rfl
    rw [hfun]
    have h := deriv_mul (c := fun z' : ℝ => z')
      (d := fun z' => Work.Spaces.pz Ψ z' θ) (x := z) differentiableAt_id h2
    simpa using h
  have hA : Work.Spaces.DzIter 2 Ψ z θ
      = z * deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z := by
    have h : Work.Spaces.pz (Work.Spaces.Dz Ψ) z θ
        = deriv (fun z' => z' * Work.Spaces.pz Ψ z' θ) z := rfl
    have h' : Work.Spaces.DzIter 2 Ψ z θ = z * Work.Spaces.pz (Work.Spaces.Dz Ψ) z θ := rfl
    rw [h', h]
  have hB : Work.Spaces.pzIter 2 Ψ z θ = deriv (fun z' => Work.Spaces.pz Ψ z' θ) z := rfl
  have hC : Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ := rfl
  rw [hA, hB, hC, hd]
  ring


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceIntegrable7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the open interval `Iθo = (0, π/2)` -/

/-- `sin (2θ)` is positive on `Iθo`. -/
private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])





/-! ## Domination by the singular weight -/


/-! ## The theorem -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.gCSpanDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The odd and even monomial families -/

/-- `X k` is the even monomial `x ↦ x ^ (2k)`. -/
def X (k : ℕ) : ℝ → ℝ := fun x => x ^ (2 * k)

/-- `Y k` is the odd monomial `x ↦ x ^ (2k+1)`. -/
def Y (k : ℕ) : ℝ → ℝ := fun x => x ^ (2 * k + 1)

/-- The span of the even monomials `x ^ (2j)`, `j ≤ k`. -/
def evenSpan (k : ℕ) : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (X '' Set.Iic k)

/-- The span of the odd monomials `x ^ (2j+1)`, `j ≤ k`. -/
def oddSpan (k : ℕ) : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Y '' Set.Iic k)

/-! ## Multiplication by the identity function -/

/-- Multiplication of a function by the identity function, as an `ℝ`-linear map. -/
def mulX : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := fun x => x * f x
  map_add' f g := by funext x; simp [Pi.add_apply, mul_add]
  map_smul' c f := by funext x; simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

lemma mulX_apply (f : ℝ → ℝ) (x : ℝ) : mulX f x = x * f x := rfl

/-- `mulX` maps the `k`-th even monomial to the `k`-th odd monomial. -/
lemma mulX_X (k : ℕ) : mulX (X k) = Y k := by
  funext x
  rw [mulX_apply, X, Y, pow_succ']

/-- `mulX` maps the `k`-th odd monomial to the `(k+1)`-st even monomial. -/
lemma mulX_Y (k : ℕ) : mulX (Y k) = X (k + 1) := by
  funext x
  rw [mulX_apply, X, Y, ← pow_succ' x (2 * k + 1),
    show 2 * k + 1 + 1 = 2 * (k + 1) by omega]

/-- `mulX` maps `evenSpan k` into `oddSpan k`. -/
lemma mulX_evenSpan_le (k : ℕ) : Submodule.map mulX (evenSpan k) ≤ oddSpan k := by
  rw [evenSpan, Submodule.map_span, Submodule.span_le]
  rintro g ⟨f, ⟨j, hj, rfl⟩, rfl⟩
  rw [mulX_X]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

/-- `mulX` maps `oddSpan k` into `evenSpan (k+1)`. -/
lemma mulX_oddSpan_le (k : ℕ) : Submodule.map mulX (oddSpan k) ≤ evenSpan (k + 1) := by
  rw [oddSpan, Submodule.map_span, Submodule.span_le]
  rintro g ⟨f, ⟨j, hj, rfl⟩, rfl⟩
  rw [mulX_Y]
  exact Submodule.subset_span
    ⟨j + 1, Set.mem_Iic.mpr (Nat.succ_le_succ (Set.mem_Iic.mp hj)), rfl⟩

lemma mulX_mem_of_mem_evenSpan {k : ℕ} {f : ℝ → ℝ} (hf : f ∈ evenSpan k) :
    mulX f ∈ oddSpan k := mulX_evenSpan_le k ⟨f, hf, rfl⟩

lemma mulX_mem_of_mem_oddSpan {k : ℕ} {f : ℝ → ℝ} (hf : f ∈ oddSpan k) :
    mulX f ∈ evenSpan (k + 1) := mulX_oddSpan_le k ⟨f, hf, rfl⟩


/-! ## Monotonicity, generators, and the successor decomposition -/

lemma evenSpan_mono {k m : ℕ} (h : k ≤ m) : evenSpan k ≤ evenSpan m := by
  rw [evenSpan, evenSpan, Submodule.span_le]
  rintro g ⟨j, hj, rfl⟩
  exact Submodule.subset_span ⟨j, le_trans hj h, rfl⟩

lemma oddSpan_mono {k m : ℕ} (h : k ≤ m) : oddSpan k ≤ oddSpan m := by
  rw [oddSpan, oddSpan, Submodule.span_le]
  rintro g ⟨j, hj, rfl⟩
  exact Submodule.subset_span ⟨j, le_trans hj h, rfl⟩

lemma X_mem (k : ℕ) : X k ∈ evenSpan k :=
  Submodule.subset_span ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩

lemma Y_mem (k : ℕ) : Y k ∈ oddSpan k :=
  Submodule.subset_span ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩

lemma Iic_succ (k : ℕ) : Set.Iic (k + 1) = insert (k + 1) (Set.Iic k) := by
  ext j; simp only [Set.mem_Iic, Set.mem_insert_iff]; omega

lemma oddSpan_succ (k : ℕ) : oddSpan (k + 1) = ℝ ∙ Y (k + 1) ⊔ oddSpan k := by
  unfold oddSpan
  rw [Iic_succ, Set.image_insert_eq, Submodule.span_insert]

/-! ## The even/odd indexed Gegenbauer polynomials and their recurrences -/

/-- `A k = gC (2k)`, the even-indexed Gegenbauer polynomial. -/
def A (k : ℕ) : ℝ → ℝ := fun x => gC (2 * k) x

/-- `B k = gC (2k+1)`, the odd-indexed Gegenbauer polynomial. -/
def B (k : ℕ) : ℝ → ℝ := fun x => gC (2 * k + 1) x

/-- The coefficient `(2n+5)/(n+2)` of the recurrence at `n = 2k`. -/
def cfA (k : ℕ) : ℝ := (2 * ((2 * k : ℕ) : ℝ) + 5) / (((2 * k : ℕ) : ℝ) + 2)

/-- The coefficient `(n+3)/(n+2)` of the recurrence at `n = 2k`. -/
def cfB (k : ℕ) : ℝ := (((2 * k : ℕ) : ℝ) + 3) / (((2 * k : ℕ) : ℝ) + 2)

/-- The coefficient `(2n+5)/(n+2)` of the recurrence at `n = 2k+1`. -/
def cfC (k : ℕ) : ℝ := (2 * ((2 * k + 1 : ℕ) : ℝ) + 5) / (((2 * k + 1 : ℕ) : ℝ) + 2)

/-- The coefficient `(n+3)/(n+2)` of the recurrence at `n = 2k+1`. -/
def cfD (k : ℕ) : ℝ := (((2 * k + 1 : ℕ) : ℝ) + 3) / (((2 * k + 1 : ℕ) : ℝ) + 2)

lemma cfA_pos (k : ℕ) : 0 < cfA k := by rw [cfA]; positivity
lemma cfC_pos (k : ℕ) : 0 < cfC k := by rw [cfC]; positivity


/-- The recurrence for the even-indexed family, pointwise. -/
lemma A_succ_pt (k : ℕ) (x : ℝ) : A (k + 1) x = cfA k * (x * B k x) - cfB k * A k x := by
  have hne : (((2 * k : ℕ) : ℝ) + 2) ≠ 0 := by positivity
  have hx : gC (2 * k + 2) x
      = ((2 * ((2 * k : ℕ) : ℝ) + 5) * x * gC (2 * k + 1) x
          - (((2 * k : ℕ) : ℝ) + 3) * gC (2 * k) x) / (((2 * k : ℕ) : ℝ) + 2) :=
    (eq_div_iff hne).mpr (by rw [mul_comm]; exact gC_rec (2 * k) x)
  show gC (2 * k + 2) x = cfA k * (x * gC (2 * k + 1) x) - cfB k * gC (2 * k) x
  rw [hx, cfA, cfB, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
  congr 1
  ring

/-- The recurrence for the odd-indexed family, pointwise. -/
lemma B_succ_pt (k : ℕ) (x : ℝ) :
    B (k + 1) x = cfC k * (x * A (k + 1) x) - cfD k * B k x := by
  have hne : (((2 * k + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
  have hx : gC ((2 * k + 1) + 2) x
      = ((2 * ((2 * k + 1 : ℕ) : ℝ) + 5) * x * gC ((2 * k + 1) + 1) x
          - (((2 * k + 1 : ℕ) : ℝ) + 3) * gC (2 * k + 1) x) / (((2 * k + 1 : ℕ) : ℝ) + 2) :=
    (eq_div_iff hne).mpr (by rw [mul_comm]; exact gC_rec (2 * k + 1) x)
  show gC ((2 * k + 1) + 2) x
      = cfC k * (x * gC (2 * (k + 1)) x) - cfD k * gC (2 * k + 1) x
  rw [hx, cfC, cfD, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div]
  congr 1
  ring

/-- The recurrence for the even-indexed family. -/
lemma A_succ (k : ℕ) : A (k + 1) = cfA k • mulX (B k) - cfB k • A k := by
  funext x
  rw [A_succ_pt k x]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]


/-! ## The leading coefficients `a` and `c` -/

/-- `c k` is the coefficient of `x ^ (2k+1)` in `gC (2k+1)`; it is defined so that
`B k - c k • Y k ∈ oddSpan (k-1)`. -/
def c : ℕ → ℝ := fun k => Nat.rec 3 (fun j cj => cfC j * (cfA j * cj)) k

/-- `a k` is the coefficient of `x ^ (2k)` in `gC (2k)`; it is defined so that
`A k - a k • X k ∈ evenSpan (k-1)`. -/
def a : ℕ → ℝ := fun k => Nat.rec 1 (fun j _ => cfA j * c j) k

lemma c_zero : c 0 = 3 := rfl

lemma c_succ (k : ℕ) : c (k + 1) = cfC k * (cfA k * c k) := rfl


lemma a_succ (k : ℕ) : a (k + 1) = cfA k * c k := rfl

lemma c_pos : ∀ k : ℕ, 0 < c k := by
  intro k
  induction k with
  | zero => rw [c_zero]; norm_num
  | succ k ih => rw [c_succ]; exact mul_pos (cfC_pos k) (mul_pos (cfA_pos k) ih)

lemma c_ne_zero (k : ℕ) : c k ≠ 0 := ne_of_gt (c_pos k)

/-! ## The two tail identities -/

/-- The algebraic core of the first induction step: the tail of `A (k+1)` (its difference from
its leading term) is the `mulX`-image of the tail of `B k`. -/
lemma A_tail (k : ℕ) :
    A (k + 1) - a (k + 1) • X (k + 1)
      = cfA k • mulX (B k - c k • Y k) - cfB k • A k := by
  funext x
  have hXY : x * Y k x = X (k + 1) x := by
    rw [← mulX_apply (Y k) x]; exact congrFun (mulX_Y k) x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]
  rw [A_succ_pt k x, a_succ k, ← hXY]
  ring

/-- The algebraic core of the second induction step: the tail of `B (k+1)` is the `mulX`-image
of the tail of `A (k+1)`. -/
lemma B_tail (k : ℕ) :
    B (k + 1) - c (k + 1) • Y (k + 1)
      = cfC k • mulX (A (k + 1) - a (k + 1) • X (k + 1)) - cfD k • B k := by
  funext x
  have hXY : x * X (k + 1) x = Y (k + 1) x := by
    rw [← mulX_apply (X (k + 1)) x]; exact congrFun (mulX_X (k + 1)) x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulX_apply]
  rw [B_succ_pt k x, c_succ k, a_succ k, ← hXY]
  ring

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.H2W.PsiSlices.DilateOps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-- The dilation of a datum of the self-similar variable: `(Dil lam F) z θ = F (lam * z) θ`. -/
def Dil (lam : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => F (lam * z) θ

@[simp] theorem Dil_apply (lam : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Dil lam F z θ = F (lam * z) θ := rfl

/-! ## The radial derivative `∂_z` and the Euler operator `D_z` -/

/-- The plain radial derivative of a dilated datum.  No differentiability hypothesis: both
`deriv`'s are junk simultaneously. -/
theorem pz_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.pz (fun z θ => F (lam * z) θ)
      = fun z θ => lam * Work.Spaces.pz F (lam * z) θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => F ζ θ) z

/-- The radial derivative of `c` times a dilated datum. -/
theorem pz_const_mul_dilate (F : ℝ → ℝ → ℝ) (c lam : ℝ) :
    Work.Spaces.pz (fun z θ => c * F (lam * z) θ)
      = fun z θ => c * (lam * Work.Spaces.pz F (lam * z) θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (x := z) (v := fun z' => F (lam * z') θ) c]
  congr 1
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => F ζ θ) z

/-- The iterated radial derivative of a dilated datum picks up `lam ^ n`. -/
theorem dilate_pzIter (F : ℝ → ℝ → ℝ) (lam : ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => F (lam * z) θ)
      = fun z θ => lam ^ n * Work.Spaces.pzIter n F (lam * z) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_const_mul_dilate]
      funext z θ
      rw [Work.Spaces.pzIter_succ, pow_succ]
      ring



/-! ## The angular operators `∂_θ`, `D_θ` and the mixed operators -/






/-! ## The elliptic operator and the moment condition -/

/-- The `α = 0` part of the elliptic operator is invariant under dilation (definitional, since
it only involves `pthIter` and `tan θ`). -/
theorem Lzero_dilate (F : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Elliptic.Lzero (fun z θ => F (lam * z) θ)
      = fun z θ => Work.Elliptic.Lzero F (lam * z) θ := by
  funext z θ
  rfl

/-- **The elliptic operator `bslOp α` is invariant under dilation of the radial variable**:
it is an Euler-type operator, so `z ↦ lam z` maps it into itself. -/
theorem bslOp_dilate (α lam : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Work.Elliptic.bslOp α (fun z θ => Ψ (lam * z) θ)
      = fun z θ => Work.Elliptic.bslOp α Ψ (lam * z) θ := by
  funext z θ
  simp only [Work.Elliptic.bslOp]
  rw [show Work.Spaces.pzIter 2 (fun z θ => Ψ (lam * z) θ) z θ
        = lam ^ 2 * Work.Spaces.pzIter 2 Ψ (lam * z) θ from
      congrFun (congrFun (dilate_pzIter Ψ lam 2) z) θ,
      show Work.Spaces.pz (fun z θ => Ψ (lam * z) θ) z θ
        = lam * Work.Spaces.pz Ψ (lam * z) θ from
      congrFun (congrFun (pz_dilate Ψ lam) z) θ,
      show Work.Elliptic.Lzero (fun z θ => Ψ (lam * z) θ) z θ
        = Work.Elliptic.Lzero Ψ (lam * z) θ from
      congrFun (congrFun (Lzero_dilate Ψ lam) z) θ]
  ring



end Work.H2W.PsiSlices
end
-- ===== merged: Submission.Work.H2W.zeroMeanPoincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W


end Work.H2W
end
end
-- ===== merged: Submission.Work.LWP.BKM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## Divergence at the left endpoint -/




/-! ## The BKM integral -/


/-! ## Divergence of the BKM integral at a maximal time -/





/-! ## Monotonicity of the BKM integral -/





end Work.LWP
end
-- ===== merged: Submission.Work.LWP.BiotSavart.crossMeasDichotomy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open MeasureTheory

/-- The cross product of two ae strongly measurable `ℝ³`-valued functions is ae strongly
measurable. -/
theorem aestronglyMeasurable_crossProduct {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g h : α → Fin 3 → ℝ} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun y => crossProduct (g y) (h y)) μ := by
  have hgm : ∀ i : Fin 3, AEMeasurable (fun y => (g y) i) μ :=
    fun i => ((continuous_apply i).comp_aestronglyMeasurable hg).aemeasurable
  have hhm : ∀ i : Fin 3, AEMeasurable (fun y => (h y) i) μ :=
    fun i => ((continuous_apply i).comp_aestronglyMeasurable hh).aemeasurable
  rw [aestronglyMeasurable_iff_aemeasurable]
  refine AEMeasurable.of_eval (fun i => ?_)
  fin_cases i <;>
    simp only [cross_apply, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;>
    first
      | exact ((hgm 1).mul (hhm 2)).sub ((hgm 2).mul (hhm 1))
      | exact ((hgm 2).mul (hhm 0)).sub ((hgm 0).mul (hhm 2))
      | exact ((hgm 0).mul (hhm 1)).sub ((hgm 1).mul (hhm 0))

/-- The dot product of two ae strongly measurable `ℝ³`-valued functions is ae strongly
measurable. -/
theorem aestronglyMeasurable_dotProduct {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {g h : α → Fin 3 → ℝ} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun y => g y ⬝ᵥ h y) μ := by
  have hgc : ∀ i : Fin 3, AEStronglyMeasurable (fun y => (g y) i) μ :=
    fun i => (continuous_apply i).comp_aestronglyMeasurable hg
  have hhc : ∀ i : Fin 3, AEStronglyMeasurable (fun y => (h y) i) μ :=
    fun i => (continuous_apply i).comp_aestronglyMeasurable hh
  convert Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3))
    (fun i _ => (hgc i).mul (hhc i)) using 1
  ext y
  simp only [dotProduct, Finset.sum_apply]
  rfl

theorem crossMeasDichotomy {ω : Work.LWP.R3 → Work.LWP.R3} {z z' : Work.LWP.R3} (hzz' : z ≠ z')
    (h₁ : MeasureTheory.AEStronglyMeasurable (fun y : Work.LWP.R3 => crossProduct (ω y) (z - y)) MeasureTheory.volume)
    (h₂ : MeasureTheory.AEStronglyMeasurable (fun y : Work.LWP.R3 => crossProduct (ω y) (z' - y)) MeasureTheory.volume) :
    MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume := by
  set f : Work.LWP.R3 → (Fin 3 → ℝ) := fun y => WithLp.ofLp (ω y) with hf
  set a : Work.LWP.R3 → (Fin 3 → ℝ) := fun y => WithLp.ofLp (z - y) with ha
  set D : (Fin 3 → ℝ) := WithLp.ofLp (z' - z) with hD
  have hDne : D ≠ 0 := by
    intro h
    have h1 : WithLp.ofLp (z' - z) = (0 : Fin 3 → ℝ) := hD ▸ h
    have h2 : WithLp.ofLp (z' - z) = WithLp.ofLp (0 : Work.LWP.R3) := by simpa using h1
    have h3 : z' - z = 0 := WithLp.ofLp_injective 2 h2
    exact hzz' (sub_eq_zero.mp h3).symm
  have hkey : ∀ y : Work.LWP.R3, WithLp.ofLp (z' - y) - WithLp.ofLp (z - y) = D := by
    intro y; rw [hD]; simp only [WithLp.ofLp_sub]; abel
  have hP1 : AEStronglyMeasurable (fun y => crossProduct (f y) (a y)) volume := h₁
  have hP2 : AEStronglyMeasurable (fun y => crossProduct (f y) D) volume := by
    have hd21 : AEStronglyMeasurable (fun y =>
        crossProduct (f y) (WithLp.ofLp (z' - y)) - crossProduct (f y) (WithLp.ofLp (z - y))) volume :=
      h₂.sub h₁
    refine hd21.congr ?_
    filter_upwards with y
    rw [← map_sub, hkey y]
  have ha_cont : Continuous a := by
    rw [ha]
    exact (EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp (continuous_const.sub continuous_id)
  have hA_cont : Continuous (fun y : Work.LWP.R3 => D ⬝ᵥ (a y)) :=
    continuous_const.dotProduct ha_cont
  have hAA_cont : Continuous (fun y : Work.LWP.R3 => (a y) ⬝ᵥ (a y)) := ha_cont.dotProduct ha_cont
  have hG1 : AEStronglyMeasurable (fun y => crossProduct (crossProduct (f y) (a y)) D) volume :=
    (LinearMap.continuous_of_finiteDimensional
      (f := (LinearMap.flip crossProduct) D)).comp_aestronglyMeasurable hP1
  have hBf : AEStronglyMeasurable (fun y => (crossProduct (crossProduct (f y) (a y)) D) ⬝ᵥ (a y)) volume :=
    aestronglyMeasurable_dotProduct hG1 ha_cont.aestronglyMeasurable
  have hG2 : AEStronglyMeasurable (fun y => crossProduct (crossProduct (f y) D) (a y)) volume :=
    aestronglyMeasurable_crossProduct hP2 ha_cont.aestronglyMeasurable
  have hCf : AEStronglyMeasurable (fun y => (crossProduct (crossProduct (f y) D) (a y)) ⬝ᵥ D) volume :=
    aestronglyMeasurable_dotProduct hG2 continuous_const.aestronglyMeasurable
  set num : Work.LWP.R3 → ℝ := fun y =>
    ((crossProduct (crossProduct (f y) (a y)) D) ⬝ᵥ (a y)) * (D ⬝ᵥ D)
      + (D ⬝ᵥ (a y)) * ((crossProduct (crossProduct (f y) D) (a y)) ⬝ᵥ D) with hnum
  set den : Work.LWP.R3 → ℝ := fun y =>
    (D ⬝ᵥ D) * ((a y) ⬝ᵥ (a y)) - (D ⬝ᵥ (a y)) * (D ⬝ᵥ (a y)) with hden
  set rhs : Work.LWP.R3 → (Fin 3 → ℝ) := fun y =>
    (D ⬝ᵥ D)⁻¹ • crossProduct D (crossProduct (f y) D)
      + ((num y / den y) * (D ⬝ᵥ D)⁻¹) • D with hrhs
  have hnum_meas : AEStronglyMeasurable num volume := by
    rw [hnum]
    exact (hBf.mul continuous_const.aestronglyMeasurable).add
      (hA_cont.aestronglyMeasurable.mul hCf)
  have hden_meas : AEStronglyMeasurable den volume := by
    rw [hden]
    exact (continuous_const.aestronglyMeasurable.mul hAA_cont.aestronglyMeasurable).sub
      (hA_cont.aestronglyMeasurable.mul hA_cont.aestronglyMeasurable)
  have hcross1 : AEStronglyMeasurable (fun y => crossProduct D (crossProduct (f y) D)) volume :=
    (LinearMap.continuous_of_finiteDimensional (f := crossProduct D)).comp_aestronglyMeasurable hP2
  have hrhs_meas : AEStronglyMeasurable rhs volume := by
    rw [hrhs]
    exact (hcross1.const_smul (D ⬝ᵥ D)⁻¹).add
      (((hnum_meas.div₀ hden_meas).mul continuous_const.aestronglyMeasurable).smul_const D)
  have hgood : ∀ᵐ y ∂volume, crossProduct D (a y) ≠ 0 := by
    rw [ae_iff]
    have hset : {y : Work.LWP.R3 | ¬ (crossProduct D (a y) ≠ 0)} =
        {y : Work.LWP.R3 | crossProduct D (a y) = 0} := by
      ext y; simp
    rw [hset]
    exact volume_setOf_cross_eq_zero (z' - z) z (sub_ne_zero.mpr hzz'.symm)
  have hpt : f =ᵐ[volume] rhs := by
    filter_upwards [hgood] with y hy
    rw [hrhs, hnum, hden]
    exact crossRecover (f y) (a y) D hDne hy
  have hfAESM : AEStronglyMeasurable f volume := hrhs_meas.congr hpt.symm
  have hωeq : ω = fun y => WithLp.toLp 2 (f y) := by
    funext y; rw [hf]
  rw [hωeq]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_aestronglyMeasurable hfAESM

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.BiotSavart.farField_decay_const =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory WithLp
open scoped Matrix

namespace Work.LWP.BiotSavart

theorem farField_decay_const {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖biotSavart ω x‖ ≤ (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2 := by
  intro x hx
  -- the integrand of the Newtonian-potential Biot–Savart operator
  let W : R3 → R3 := fun y => WithLp.toLp 2 ((‖x - y‖ ^ (3:ℕ))⁻¹ • crossProduct (ω y) (x - y))
  have hbs : biotSavart ω x = (4 * Real.pi)⁻¹ • ∫ y, W y := rfl
  -- the integrand vanishes off `closedBall 0 R`
  have hzero : ∀ y, y ∉ Metric.closedBall (0:R3) R → W y = 0 := by
    intro y hy
    have hωy : ω y = 0 := by
      by_contra hne
      exact hy (hsupp y hne)
    simp only [W, hωy]
    simp
  have h1 : ‖(4 * Real.pi)⁻¹ • ∫ y, W y‖ = (4 * Real.pi)⁻¹ * ‖∫ y, W y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : ‖∫ y, W y‖ = ‖∫ y in Metric.closedBall (0:R3) R, W y‖ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f := W) hzero]
  -- the pointwise bound `‖W y‖ ≤ 4M/‖x‖²` on the ball
  have h3 : ‖∫ y in Metric.closedBall (0:R3) R, W y‖
      ≤ (4 / ‖x‖ ^ 2 * M) * Measure.real volume (Metric.closedBall (0:R3) R) := by
    apply norm_setIntegral_le_of_norm_le_const
    · rw [EuclideanSpace.volume_closedBall_fin_three]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (n := 3) ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
    · intro y hy
      have hy' : ‖y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      exact integrand_norm_le hR hM hω hx hy'
  rw [hbs, h1, h2]
  calc (4 * Real.pi)⁻¹ * ‖∫ y in Metric.closedBall (0:R3) R, W y‖
      ≤ (4 * Real.pi)⁻¹ * ((4 / ‖x‖ ^ 2 * M) * Measure.real volume (Metric.closedBall (0:R3) R)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (4/3) * M * R^3 / ‖x‖^2 := by
        rw [volume_closedBall_real R hR]
        have hpi : (4 * Real.pi)⁻¹ * 4 * (Real.pi * 4 / 3) = (4/3 : ℝ) := by
          have h : (4 * Real.pi)⁻¹ * (4 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
          calc (4 * Real.pi)⁻¹ * 4 * (Real.pi * 4 / 3)
              = ((4 * Real.pi)⁻¹ * (4 * Real.pi)) * (4/3) := by ring
            _ = 4/3 := by rw [h, one_mul]
        have hrewrite : (4 * Real.pi)⁻¹ * ((4 / ‖x‖ ^ 2 * M) * (R^3 * (Real.pi * 4 / 3)))
            = ((4*Real.pi)⁻¹ * 4 * (Real.pi*4/3)) * (M * R^3 * (‖x‖^2)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
        rw [hrewrite, hpi]
        ring

end Work.LWP.BiotSavart
end
-- ===== merged: Submission.Work.LWP.LocalExistence =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## Locality: regularity on the strips gives regularity on the half-open interval -/


/-! ## Local well-posedness -/



/-! ## Restriction of a solution to a subinterval -/




end Work.LWP
end
-- ===== merged: Submission.Work.Spaces.HardyZLin.hardyZ_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.HardyZLin

open MeasureTheory


end Work.Spaces.HardyZLin
end
-- ===== merged: Submission.Work.Spaces.mixed_sq_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Measurability and continuity of the two factors of the mixed summand

The summand `(D_z^j D_θ^i f · W)²` is the pointwise square of the product of
`θ ↦ D_z^j D_θ^i f z θ` and `θ ↦ W(α,z,θ)`.  The second factor has the algebraic
form `w z · sin(2θ)^{-γ/2}`, so it is (everywhere) measurable; the first factor is
continuous on `Iθ` because `f` is smooth on a neighbourhood of the closed quadrant,
hence so are all its `D`-iterates. -/

/-- The angular slice of the weight, `θ ↦ W(α,z,θ)`, is measurable. -/
private lemma measurable_Wt_right (α z : ℝ) : Measurable (fun θ : ℝ => Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    measurable_const.mul hpow
  simpa [Wt, wTheta] using this

/-- For `z ∈ Iz`, the angular slice `θ ↦ D_z^j D_θ^i f z θ` of a smooth function is
continuous on the closed interval `Iθ`. -/
private lemma continuousOn_mixed_slice {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) (i j : ℕ)
    {z : ℝ} (hz : z ∈ Iz) : ContinuousOn (fun θ : ℝ => mixed j i f z θ) Iθ := by
  have hsm' : SmoothNbhd (mixed j i f) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm i) j
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (mixed j i f)) (z, θ) :=
    hsm'.contDiffAt (isOpen_nbhU.mem_nhds (mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-- The squared weighted mixed derivative `(D_z^j D_θ^i f · W)²` of an `H⁴`-function is
integrable in `θ` on `Iθ`, for `1 ≤ i` and `i + j ≤ 4`.  It is one of the summands of
`HkIntegrand α 4 f z`, which is integrable on `Iθ` by `HkMem α 4 f`. -/
theorem mixed_sq_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.HkMem α 4 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ MeasureTheory.volume := by
  have hcont := continuousOn_mixed_slice hsm i j hz
  have haesm1 : AEStronglyMeasurable (fun θ : ℝ => mixed j i f z θ) (volume.restrict Iθ) :=
    hcont.aestronglyMeasurable (show MeasurableSet Iθ from measurableSet_Icc)
  have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Wt α z θ) (volume.restrict Iθ) :=
    (measurable_Wt_right α z).aestronglyMeasurable
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (mixed j i f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := by
    have h : AEStronglyMeasurable (fun θ : ℝ => mixed j i f z θ * Wt α z θ)
        (volume.restrict Iθ) := haesm1.mul haesm2
    exact h.pow 2
  -- Pointwise domination by the full `H⁴`-integrand, which is integrable by hypothesis.
  refine (hmem.1 z hz).mono' haesm (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

end Work.Spaces
end
end
