import Mathlib
import Submission.Commons.Analysis.Differential.ode_pullback_mobius

namespace Commons.Analysis.Differential

open PowerSeries

noncomputable section

/-- The involutive Möbius map `u = X/(X−1)`. -/
def ode_invU : PowerSeries ℚ := PowerSeries.X * (PowerSeries.X - 1)⁻¹

/-- The unit `e = X − 1`. -/
def ode_invE : PowerSeries ℚ := PowerSeries.X - 1

/-- The pulled-back second-order operator appearing in the statement. -/
def ode_invM (g : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X * (8 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2
      * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) g)
    + ((8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * (PowerSeries.X - 1))
      * (PowerSeries.derivative (R := ℚ)) g
    + (3 * (2 * PowerSeries.X + 1)) * g

lemma ode_invE_ne : PowerSeries.constantCoeff ode_invE ≠ 0 := by
  unfold ode_invE; simp

lemma ode_invU_hasSubst : PowerSeries.HasSubst ode_invU := by
  unfold ode_invU
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp

/-! ## Elementary unit identities for `e = X − 1` -/

lemma ode_invE_mul_inv : ode_invE * ode_invE⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ ode_invE_ne

lemma ode_invE_inv_mul : ode_invE⁻¹ * ode_invE = 1 :=
  PowerSeries.inv_mul_cancel _ ode_invE_ne

lemma ode_invE_inv_pow_mul_pow (n : ℕ) : (ode_invE⁻¹) ^ n * ode_invE ^ n = 1 := by
  rw [← mul_pow, ode_invE_inv_mul, one_pow]

lemma ode_invE_pow_mul_inv_pow (n : ℕ) : ode_invE ^ n * (ode_invE⁻¹) ^ n = 1 := by
  rw [mul_comm, ode_invE_inv_pow_mul_pow]

lemma ode_invE_pow_mul_left_cancel {a b : PowerSeries ℚ} {n : ℕ}
    (h : ode_invE ^ n * a = ode_invE ^ n * b) : a = b := by
  have h' := congrArg (fun z => (ode_invE⁻¹) ^ n * z) h
  rw [← mul_assoc, ← mul_assoc, ode_invE_inv_pow_mul_pow, one_mul, one_mul] at h'
  exact h'

/-! ## The relations `e · u = X`, `e · (1−u) = −1`, … -/

lemma ode_invE_mul_U : ode_invE * ode_invU = PowerSeries.X := by
  calc ode_invE * (PowerSeries.X * ode_invE⁻¹)
      = PowerSeries.X * (ode_invE * ode_invE⁻¹) := by ring
    _ = PowerSeries.X * 1 := by rw [ode_invE_mul_inv]
    _ = PowerSeries.X := by ring

lemma ode_invE_mul_one_sub_U : ode_invE * (1 - ode_invU) = -1 := by
  calc ode_invE * (1 - ode_invU) = ode_invE - ode_invE * ode_invU := by ring
    _ = ode_invE - PowerSeries.X := by rw [ode_invE_mul_U]
    _ = -1 := by unfold ode_invE; ring

lemma ode_invE_mul_one_sub_9U : ode_invE * (1 - 9 * ode_invU) = -(8 * PowerSeries.X + 1) := by
  calc ode_invE * (1 - 9 * ode_invU) = ode_invE - 9 * (ode_invE * ode_invU) := by ring
    _ = ode_invE - 9 * PowerSeries.X := by rw [ode_invE_mul_U]
    _ = -(8 * PowerSeries.X + 1) := by unfold ode_invE; ring

lemma ode_invE_mul_three_U_sub_one : ode_invE * (3 * ode_invU - 1) = 2 * PowerSeries.X + 1 := by
  calc ode_invE * (3 * ode_invU - 1) = 3 * (ode_invE * ode_invU) - ode_invE := by ring
    _ = 3 * PowerSeries.X - ode_invE := by rw [ode_invE_mul_U]
    _ = 2 * PowerSeries.X + 1 := by unfold ode_invE; ring

lemma ode_invE_sq_mul_U : ode_invE ^ 2 * ode_invU = ode_invE * PowerSeries.X := by
  calc ode_invE ^ 2 * ode_invU = ode_invE * (ode_invE * ode_invU) := by ring
    _ = ode_invE * PowerSeries.X := by rw [ode_invE_mul_U]

lemma ode_invE_sq_mul_U_sq : ode_invE ^ 2 * ode_invU ^ 2 = PowerSeries.X ^ 2 := by
  calc ode_invE ^ 2 * ode_invU ^ 2 = (ode_invE * ode_invU) ^ 2 := by ring
    _ = PowerSeries.X ^ 2 := by rw [ode_invE_mul_U]

lemma ode_invE_sq_mul_quad :
    ode_invE ^ 2 * (1 - 20 * ode_invU + 27 * ode_invU ^ 2)
      = 8 * PowerSeries.X ^ 2 + 18 * PowerSeries.X + 1 := by
  calc ode_invE ^ 2 * (1 - 20 * ode_invU + 27 * ode_invU ^ 2)
      = ode_invE ^ 2 - 20 * (ode_invE ^ 2 * ode_invU) + 27 * (ode_invE ^ 2 * ode_invU ^ 2) := by
        ring
    _ = ode_invE ^ 2 - 20 * (ode_invE * PowerSeries.X) + 27 * PowerSeries.X ^ 2 := by
          rw [ode_invE_sq_mul_U, ode_invE_sq_mul_U_sq]
    _ = 8 * PowerSeries.X ^ 2 + 18 * PowerSeries.X + 1 := by unfold ode_invE; ring

/-! ## Derivatives of `e` and the scaled chain rule data -/

lemma ode_invE_deriv : (PowerSeries.derivative (R := ℚ)) ode_invE = 1 := by
  unfold ode_invE; simp

lemma ode_invE_sq_deriv : (PowerSeries.derivative (R := ℚ)) (ode_invE ^ 2) = 2 * ode_invE := by
  rw [PowerSeries.derivative_pow, ode_invE_deriv]
  simp

lemma ode_invE_deriv_mul_U : ode_invE * (PowerSeries.derivative (R := ℚ)) ode_invU = 1 - ode_invU := by
  have h : (PowerSeries.derivative (R := ℚ)) (ode_invE * ode_invU)
      = (PowerSeries.derivative (R := ℚ)) PowerSeries.X := by rw [ode_invE_mul_U]
  rw [Derivation.leibniz, ode_invE_deriv, PowerSeries.derivative_X] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [eq_sub_iff_add_eq]
  simpa [mul_comm] using h

lemma ode_invE_sq_deriv_U : ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) ode_invU = -1 := by
  calc ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) ode_invU
      = ode_invE * (ode_invE * (PowerSeries.derivative (R := ℚ)) ode_invU) := by ring
    _ = ode_invE * (1 - ode_invU) := by rw [ode_invE_deriv_mul_U]
    _ = -1 := ode_invE_mul_one_sub_U

lemma ode_inv_hunit : (PowerSeries.derivative (R := ℚ)) ode_invU * (-(ode_invE ^ 2)) = 1 := by
  rw [mul_neg, mul_comm ((PowerSeries.derivative (R := ℚ)) ode_invU) (ode_invE ^ 2), ode_invE_sq_deriv_U,
    neg_neg]

/-- The scaled chain rule: `(ψ·d/dX)^i (f ∘ u) = ((d/dX)^i f) ∘ u` with `ψ = 1/u' = −e²`. -/
lemma ode_inv_iterate (f : PowerSeries ℚ) (i : ℕ) :
    ((fun g : PowerSeries ℚ => (-(ode_invE ^ 2)) * (PowerSeries.derivative (R := ℚ)) g) ^[i])
        (f.subst ode_invU)
      = (((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g) ^[i]) f).subst ode_invU :=
  Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled ℚ f ode_invU (-(ode_invE ^ 2)) i
    ode_invU_hasSubst ode_inv_hunit

lemma ode_inv_p (f : PowerSeries ℚ) :
    ((PowerSeries.derivative (R := ℚ)) f).subst ode_invU
      = -(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)) := by
  have h := ode_inv_iterate f 1
  simpa only [Function.iterate_one, neg_mul] using h.symm

lemma ode_inv_q (f : PowerSeries ℚ) :
    ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)).subst ode_invU
      = ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
        + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU) := by
  have h := ode_inv_iterate f 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h
  have hd : (PowerSeries.derivative (R := ℚ))
        ((-(ode_invE ^ 2)) * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
      = (-(2 * ode_invE)) * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)
        + (-(ode_invE ^ 2))
            * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)) := by
    rw [Derivation.leibniz, map_neg, ode_invE_sq_deriv]
    simp only [smul_eq_mul]
    ring
  rw [hd] at h
  rw [← h]
  ring

/-! ## Substitution of the original operator's coefficients -/

lemma ode_inv_subst_a2 :
    PowerSeries.subst ode_invU ode_a2 = ode_invU * (1 - ode_invU) * (1 - 9 * ode_invU) := by
  have hu := ode_invU_hasSubst
  unfold ode_a2
  rw [← PowerSeries.coe_substAlgHom hu]
  simp only [map_mul, map_sub, map_one, map_ofNat, PowerSeries.substAlgHom_X hu]

lemma ode_inv_subst_a1 :
    PowerSeries.subst ode_invU ode_a1 = 1 - 20 * ode_invU + 27 * ode_invU ^ 2 := by
  have hu := ode_invU_hasSubst
  unfold ode_a1
  rw [← PowerSeries.coe_substAlgHom hu]
  simp only [map_add, map_sub, map_mul, map_one, map_ofNat, map_pow, PowerSeries.substAlgHom_X hu]

lemma ode_inv_subst_a0 : PowerSeries.subst ode_invU ode_a0 = 3 * (3 * ode_invU - 1) := by
  have hu := ode_invU_hasSubst
  unfold ode_a0
  rw [← PowerSeries.coe_substAlgHom hu]
  simp only [map_mul, map_sub, map_one, map_ofNat, PowerSeries.substAlgHom_X hu]

lemma ode_invE_cube_mul_A : ode_invE ^ 3 * (PowerSeries.subst ode_invU ode_a2)
    = PowerSeries.X * (8 * PowerSeries.X + 1) := by
  rw [ode_inv_subst_a2]
  calc ode_invE ^ 3 * (ode_invU * (1 - ode_invU) * (1 - 9 * ode_invU))
      = (ode_invE * ode_invU) * (ode_invE * (1 - ode_invU)) * (ode_invE * (1 - 9 * ode_invU)) := by
        ring
    _ = PowerSeries.X * (-1) * (-(8 * PowerSeries.X + 1)) := by
          rw [ode_invE_mul_U, ode_invE_mul_one_sub_U, ode_invE_mul_one_sub_9U]
    _ = PowerSeries.X * (8 * PowerSeries.X + 1) := by ring

lemma ode_invE_sq_mul_B : ode_invE ^ 2 * (PowerSeries.subst ode_invU ode_a1)
    = 8 * PowerSeries.X ^ 2 + 18 * PowerSeries.X + 1 := by
  rw [ode_inv_subst_a1]
  exact ode_invE_sq_mul_quad

lemma ode_invE_mul_C : ode_invE * (PowerSeries.subst ode_invU ode_a0)
    = 3 * (2 * PowerSeries.X + 1) := by
  rw [ode_inv_subst_a0]
  calc ode_invE * (3 * (3 * ode_invU - 1)) = 3 * (ode_invE * (3 * ode_invU - 1)) := by ring
    _ = 3 * (2 * PowerSeries.X + 1) := by rw [ode_invE_mul_three_U_sub_one]

/-! ## The main pull-back identity -/

/-- Expansion of the substituted left-hand side `(L f) ∘ u`. -/
lemma ode_inv_expand (f : PowerSeries ℚ) :
    (ode_pb_L f).subst ode_invU
      = (PowerSeries.subst ode_invU ode_a2)
            * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
        + (PowerSeries.subst ode_invU ode_a1)
            * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
        + (PowerSeries.subst ode_invU ode_a0) * (f.subst ode_invU) := by
  unfold ode_pb_L
  rw [PowerSeries.subst_add ode_invU_hasSubst, PowerSeries.subst_add ode_invU_hasSubst,
    PowerSeries.subst_mul ode_invU_hasSubst, PowerSeries.subst_mul ode_invU_hasSubst,
    PowerSeries.subst_mul ode_invU_hasSubst, ode_inv_q f, ode_inv_p f]

lemma ode_inv_key_expanded (f : PowerSeries ℚ) :
    ode_invM (f.subst ode_invU)
      = ode_invE * ((PowerSeries.subst ode_invU ode_a2)
            * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
          + (PowerSeries.subst ode_invU ode_a1)
              * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
          + (PowerSeries.subst ode_invU ode_a0) * (f.subst ode_invU)) := by
  apply ode_invE_pow_mul_left_cancel (n := 3)
  have lhs_eq : ode_invE ^ 3 * ode_invM (f.subst ode_invU)
      = PowerSeries.X * (8 * PowerSeries.X + 1) * ode_invE ^ 5
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
        + (8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * ode_invE ^ 4
          * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)
        + 3 * (2 * PowerSeries.X + 1) * ode_invE ^ 3 * (f.subst ode_invU) := by
    unfold ode_invM ode_invE
    ring
  have rhs_eq : ode_invE ^ 3 * (ode_invE * ((PowerSeries.subst ode_invU ode_a2)
            * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
          + (PowerSeries.subst ode_invU ode_a1)
              * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
          + (PowerSeries.subst ode_invU ode_a0) * (f.subst ode_invU)))
      = PowerSeries.X * (8 * PowerSeries.X + 1) * ode_invE ^ 5
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
        + (8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * ode_invE ^ 4
          * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)
        + 3 * (2 * PowerSeries.X + 1) * ode_invE ^ 3 * (f.subst ode_invU) := by
    calc ode_invE ^ 3 * (ode_invE * ((PowerSeries.subst ode_invU ode_a2)
            * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
          + (PowerSeries.subst ode_invU ode_a1)
              * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
          + (PowerSeries.subst ode_invU ode_a0) * (f.subst ode_invU)))
        = (ode_invE ^ 3 * (PowerSeries.subst ode_invU ode_a2))
            * (ode_invE * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
          + (ode_invE ^ 2 * (PowerSeries.subst ode_invU ode_a1))
              * (ode_invE ^ 2 * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))))
          + (ode_invE * (PowerSeries.subst ode_invU ode_a0)) * (ode_invE ^ 3 * (f.subst ode_invU)) := by
            ring
      _ = PowerSeries.X * (8 * PowerSeries.X + 1)
            * (ode_invE * (ode_invE ^ 4 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
               + 2 * ode_invE ^ 3 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)))
          + (8 * PowerSeries.X ^ 2 + 18 * PowerSeries.X + 1)
              * (ode_invE ^ 2 * (-(ode_invE ^ 2 * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))))
          + 3 * (2 * PowerSeries.X + 1) * (ode_invE ^ 3 * (f.subst ode_invU)) := by
            rw [ode_invE_cube_mul_A, ode_invE_sq_mul_B, ode_invE_mul_C]
      _ = PowerSeries.X * (8 * PowerSeries.X + 1) * ode_invE ^ 5
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (f.subst ode_invU))
        + (8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * ode_invE ^ 4
          * (PowerSeries.derivative (R := ℚ)) (f.subst ode_invU)
        + 3 * (2 * PowerSeries.X + 1) * ode_invE ^ 3 * (f.subst ode_invU) := by
            ring
  exact lhs_eq.trans rhs_eq.symm

lemma ode_inv_key (f : PowerSeries ℚ) :
    ode_invM (f.subst ode_invU) = ode_invE * (ode_pb_L f).subst ode_invU := by
  rw [ode_inv_expand f]
  exact ode_inv_key_expanded f

end

theorem ode_pullback_involution (f : PowerSeries ℚ)
    (h : PowerSeries.X * (1 - PowerSeries.X) * (1 - PowerSeries.C 9 * PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)
          + (1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2)
            * (PowerSeries.derivative (R := ℚ)) f
          + PowerSeries.C 3 * (PowerSeries.C 3 * PowerSeries.X - 1) * f = 0) :
    PowerSeries.X * (8 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2
        * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
            (f.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹)))
      + ((8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * (PowerSeries.X - 1))
        * (PowerSeries.derivative (R := ℚ)) (f.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹))
      + (3 * (2 * PowerSeries.X + 1)) * (f.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹)) = 0 := by
  change ode_invM (f.subst ode_invU) = 0
  have hu := ode_invU_hasSubst
  have hL : ode_pb_L f = 0 := h
  have hz : PowerSeries.subst ode_invU (0 : PowerSeries ℚ) = 0 := by
    have h' := map_zero (PowerSeries.substAlgHom (R := ℚ) hu)
    rwa [PowerSeries.coe_substAlgHom] at h'
  rw [ode_inv_key f, hL, hz, mul_zero]

end Commons.Analysis.Differential
