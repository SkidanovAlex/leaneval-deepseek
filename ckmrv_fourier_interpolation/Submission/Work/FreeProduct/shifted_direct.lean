import Mathlib
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.shifted_orbit_corollary
import Submission.Work.FreeProduct.shifted_core_plus
import Submission.Work.FreeProduct.shifted_core_minus
import Submission.Work.FreeProduct.Tnu_mul_eq_zero
import Submission.Work.FreeProduct.IdealIpDirect

/-!
# Directness of `(T - ν)²·RR + X(T - ν)²·RR` in `ℂ[ℤ/2 ∗ ℤ/3]`

This is the shifted (parameter `ν`) form of CKMRV Proposition 3.1 in the free-product picture:
the sum `(T - ν)²·RR + X·(T - ν)²·RR` is direct, i.e.

  `(T - ν)² * a + X * (T - ν)² * b = 0  →  a = 0 ∧ b = 0`

whenever `ν ≠ 0` and `1 ± ν³ ≠ 0`.

The proof is exactly the assembly of `Work.FreeProduct.idealI_direct`, with `T - 1` replaced by
`T - ν` throughout:

* from the hypothesis one deduces `(1 + X) * ((T-ν)² * (a + b)) = 0` and
  `(1 - X) * ((T-ν)² * (a - b)) = 0`;
* the kernels of `1 ± X` are the ranges of `X ∓ 1`, so `(T-ν)² (a+b) = (X-1) w₁` and
  `(T-ν)² (a-b) = (X+1) w₂`;
* the two *degree-two* directness statements `(T-ν)² u = (X ∓ 1) w → u = 0` are reduced, using
  the decompositions `T - ν = (X - 1)Y + (Y - ν)` and `T - ν = (X + 1)Y - (Y + ν)` together with
  the scalar identities `MUv ν (Y - ν) = 1 - ν³` and `MUpv ν (Y + ν) = 1 + ν³`, to the *degree-one*
  shifted core lemmas `shifted_core_minus`/`shifted_core_plus`, and then `T - ν` is injective
  (`Tnu_mul_eq_zero`);
* `a + b = 0` and `a - b = 0` give `a = b = 0`.
-/

set_option linter.unusedSimpArgs false

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-! ## Scalar identities and decompositions of `T - ν` -/

/-- `MUv ν * (Y - ν) = (1 - ν³) • 1`. -/
lemma MUv_mul_Y_sub (ν : ℂ) : MUv ν * (Y - ν • (1 : RR)) = (1 - ν ^ 3) • (1 : RR) := by
  simp only [MUv_apply, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, Y_mul_Y, Y_mul_Y2, Y2_mul_Y,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

/-- `MUpv ν * (Y + ν) = (1 + ν³) • 1`. -/
lemma MUpv_mul_Y_add (ν : ℂ) : MUpv ν * (Y + ν • (1 : RR)) = (1 + ν ^ 3) • (1 : RR) := by
  simp only [MUpv_apply, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, Y_mul_Y, Y_mul_Y2, Y2_mul_Y,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

/-- `T - ν = (X - 1)Y + (Y - ν)`. -/
lemma Tnu_eq_sub (ν : ℂ) : Tnu ν = (X - 1) * Y + (Y - ν • (1 : RR)) := by
  rw [Tnu_apply, show (TT : RR) = X * Y from X_mul_Y.symm]
  noncomm_ring

/-- `T - ν = (X + 1)Y - (Y + ν)`. -/
lemma Tnu_eq_add (ν : ℂ) : Tnu ν = (X + 1) * Y - (Y + ν • (1 : RR)) := by
  rw [Tnu_apply, show (TT : RR) = X * Y from X_mul_Y.symm]
  noncomm_ring

/-! ## The kernels of `1 ± X` -/

/-- `ker (1 + X) = (X - 1)·RR`. -/
lemma ker_one_add_X {v : RR} (h : (1 + X) * v = 0) : ∃ w, v = (X - 1) * w := by
  have hXv : X * v = -v := by
    have h1 := h
    rw [add_mul, one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  refine ⟨(2 : ℂ)⁻¹ • (X * v), ?_⟩
  have key : (X - 1) * (X * v) = (2 : ℂ) • v := by
    rw [two_smul ℂ v, sub_mul, one_mul]
    have h2 : X * (X * v) = v := by rw [← mul_assoc, X_mul_X, one_mul]
    rw [h2, hXv, sub_neg_eq_add]
  rw [mul_smul_comm, key, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- `ker (1 - X) = (X + 1)·RR`. -/
lemma ker_one_sub_X {v : RR} (h : (1 - X) * v = 0) : ∃ w, v = (X + 1) * w := by
  have hXv : X * v = v := by
    have h1 := h
    rw [sub_mul, one_mul] at h1
    exact (sub_eq_zero.mp h1).symm
  refine ⟨(2 : ℂ)⁻¹ • (X * v), ?_⟩
  have key : (X + 1) * (X * v) = (2 : ℂ) • v := by
    rw [two_smul ℂ v, add_mul, one_mul]
    have h2 : X * (X * v) = v := by rw [← mul_assoc, X_mul_X, one_mul]
    rw [h2, hXv]
  rw [mul_smul_comm, key, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-! ## The degree-two shifted directness statements -/

/-- `(T - ν)² u = (X - 1) w → u = 0`, for `ν ≠ 0`, `1 - ν³ ≠ 0`. -/
lemma shifted_Tnu_sq_Im_direct {ν : ℂ} (hν : ν ≠ 0) (hν3 : 1 - ν ^ 3 ≠ 0)
    {u w : RR} (h : Tnu ν ^ 2 * u = (X - 1) * w) : u = 0 := by
  set v : RR := Tnu ν * u with hv
  have hvv : Tnu ν * v = (X - 1) * w := by
    rw [hv, ← mul_assoc, ← pow_two]; exact h
  have hstep : (Y - ν • (1 : RR)) * v = (X - 1) * (w - Y * v) := by
    have h0 : Tnu ν * v = (X - 1) * w := hvv
    rw [Tnu_eq_sub ν, add_mul, mul_assoc] at h0
    rw [mul_sub, eq_sub_iff_add_eq, ← h0]
    abel
  have hM : (1 - ν ^ 3) • v = MUv ν * (X - 1) * (w - Y * v) := by
    have h1 : MUv ν * ((Y - ν • (1 : RR)) * v) = MUv ν * ((X - 1) * (w - Y * v)) :=
      congrArg (fun z : RR => MUv ν * z) hstep
    calc (1 - ν ^ 3) • v
        = ((1 - ν ^ 3) • (1 : RR)) * v := by rw [smul_mul_assoc, one_mul]
      _ = (MUv ν * (Y - ν • (1 : RR))) * v := by rw [MUv_mul_Y_sub ν]
      _ = MUv ν * ((Y - ν • (1 : RR)) * v) := by rw [mul_assoc]
      _ = MUv ν * ((X - 1) * (w - Y * v)) := h1
      _ = MUv ν * (X - 1) * (w - Y * v) := by rw [mul_assoc]
  have hv' : v = MUv ν * (X - 1) * ((1 - ν ^ 3)⁻¹ • (w - Y * v)) := by
    calc v = (1 - ν ^ 3)⁻¹ • ((1 - ν ^ 3) • v) := by rw [smul_smul, inv_mul_cancel₀ hν3, one_smul]
      _ = (1 - ν ^ 3)⁻¹ • (MUv ν * (X - 1) * (w - Y * v)) := by rw [hM]
      _ = MUv ν * (X - 1) * ((1 - ν ^ 3)⁻¹ • (w - Y * v)) := by rw [← mul_smul_comm]
  have hcore : Tnu ν * u = 0 := shifted_core_minus hν hν3 (by rw [← hv]; exact hv')
  exact Tnu_mul_eq_zero hν hcore

/-- `(T - ν)² u = (X + 1) w → u = 0`, for `ν ≠ 0`, `1 + ν³ ≠ 0`. -/
lemma shifted_Tnu_sq_Ip_direct {ν : ℂ} (hν : ν ≠ 0) (hν3 : 1 + ν ^ 3 ≠ 0)
    {u w : RR} (h : Tnu ν ^ 2 * u = (X + 1) * w) : u = 0 := by
  set v : RR := Tnu ν * u with hv
  have hvv : Tnu ν * v = (X + 1) * w := by
    rw [hv, ← mul_assoc, ← pow_two]; exact h
  have hstep : (Y + ν • (1 : RR)) * v = (X + 1) * (Y * v - w) := by
    have h0 : Tnu ν * v = (X + 1) * w := hvv
    rw [Tnu_eq_add ν, sub_mul, mul_assoc] at h0
    rw [mul_sub, eq_sub_iff_add_eq, ← h0]
    abel
  have hM : (1 + ν ^ 3) • v = MUpv ν * (X + 1) * (Y * v - w) := by
    have h1 : MUpv ν * ((Y + ν • (1 : RR)) * v) = MUpv ν * ((X + 1) * (Y * v - w)) :=
      congrArg (fun z : RR => MUpv ν * z) hstep
    calc (1 + ν ^ 3) • v
        = ((1 + ν ^ 3) • (1 : RR)) * v := by rw [smul_mul_assoc, one_mul]
      _ = (MUpv ν * (Y + ν • (1 : RR))) * v := by rw [MUpv_mul_Y_add ν]
      _ = MUpv ν * ((Y + ν • (1 : RR)) * v) := by rw [mul_assoc]
      _ = MUpv ν * ((X + 1) * (Y * v - w)) := h1
      _ = MUpv ν * (X + 1) * (Y * v - w) := by rw [mul_assoc]
  have hv' : v = MUpv ν * (X + 1) * ((1 + ν ^ 3)⁻¹ • (Y * v - w)) := by
    calc v = (1 + ν ^ 3)⁻¹ • ((1 + ν ^ 3) • v) := by rw [smul_smul, inv_mul_cancel₀ hν3, one_smul]
      _ = (1 + ν ^ 3)⁻¹ • (MUpv ν * (X + 1) * (Y * v - w)) := by rw [hM]
      _ = MUpv ν * (X + 1) * ((1 + ν ^ 3)⁻¹ • (Y * v - w)) := by rw [← mul_smul_comm]
  have hcore : Tnu ν * u = 0 := shifted_core_plus hν hν3 (by rw [← hv]; exact hv')
  exact Tnu_mul_eq_zero hν hcore

/-! ## The target -/

theorem shifted_direct {ν : ℂ} (hν : ν ≠ 0) (hν3p : 1 + ν ^ 3 ≠ 0) (hν3m : 1 - ν ^ 3 ≠ 0)
    {a b : Work.FreeProduct.RR}
    (h : Work.FreeProduct.Tnu ν ^ 2 * a + Work.FreeProduct.X * Work.FreeProduct.Tnu ν ^ 2 * b = 0) :
    a = 0 ∧ b = 0 := by
  set A : RR := Tnu ν ^ 2 with hA
  have hmain : A * a + X * A * b = 0 := by rw [hA]; exact h
  have hab1 : A * a = -(X * (A * b)) := by
    rw [eq_neg_iff_add_eq_zero, ← mul_assoc]; exact hmain
  have hab2 : X * (A * a) = -(A * b) := by
    rw [hab1, mul_neg]
    have hX : X * (X * (A * b)) = A * b := by rw [← mul_assoc, X_mul_X, one_mul]
    rw [hX]
  have hsum : (1 + X) * (A * (a + b)) = 0 := by
    have e : (1 + X) * (A * (a + b)) = (A * a + A * b) + (X * (A * a) + X * (A * b)) := by
      noncomm_ring
    rw [e, hab2, hab1]
    abel
  have hdiff : (1 - X) * (A * (a - b)) = 0 := by
    have e : (1 - X) * (A * (a - b)) = (A * a - A * b) + (-(X * (A * a)) + X * (A * b)) := by
      noncomm_ring
    rw [e, hab2, hab1]
    abel
  obtain ⟨w1, hw1⟩ := ker_one_add_X hsum
  obtain ⟨w2, hw2⟩ := ker_one_sub_X hdiff
  have hab : a + b = 0 := shifted_Tnu_sq_Im_direct hν hν3m hw1
  have hsb : a - b = 0 := shifted_Tnu_sq_Ip_direct hν hν3p hw2
  have ha : a = 0 := by
    have h2 : (2 : ℂ) • a = 0 := by
      have he : (2 : ℂ) • a = (a + b) + (a - b) := by rw [two_smul ℂ a]; abel
      rw [he, hab, hsb, add_zero]
    have h3 : (2 : ℂ)⁻¹ • ((2 : ℂ) • a) = 0 := by rw [h2]; simp
    rw [smul_smul] at h3
    rw [show (2 : ℂ)⁻¹ * 2 = 1 by norm_num, one_smul] at h3
    exact h3
  have hb : b = 0 := by rw [ha, zero_add] at hab; exact hab
  exact ⟨ha, hb⟩

end

end Work.FreeProduct
