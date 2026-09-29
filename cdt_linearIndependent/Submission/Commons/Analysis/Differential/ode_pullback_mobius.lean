import Mathlib.RingTheory.PowerSeries.Inverse
import Submission.Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero
import Submission.Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X

namespace Commons.Analysis.Differential

open PowerSeries

noncomputable section

/-- The Möbius substitution `ψ = X/(1−X)`, the inverse of `φ = X/(1+X)`. -/
def ode_mobPsi : PowerSeries ℚ := PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹

/-- The Möbius map `φ = X/(1+X)` that is pulled back. -/
def ode_mobPhi : PowerSeries ℚ := PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹

/-- The unit twist `1/(1+X)`. -/
def ode_mobU : PowerSeries ℚ := ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹

/-- The scaled-derivative multiplier `w = (1−X)² = 1/ψ′`. -/
def ode_mobW : PowerSeries ℚ := ((1 : PowerSeries ℚ) - PowerSeries.X) ^ 2

/-- The `g''` coefficient of the transformed operator. -/
def ode_b2 : PowerSeries ℚ :=
  PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)

/-- The `g'` coefficient of the transformed operator. -/
def ode_b1 : PowerSeries ℚ := 1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2

/-- The `g` coefficient of the transformed operator. -/
def ode_b0 : PowerSeries ℚ := -2 - 8 * PowerSeries.X

/-- The `f''` coefficient of the original operator. -/
def ode_a2 : PowerSeries ℚ := PowerSeries.X * (1 - PowerSeries.X) * (1 - 9 * PowerSeries.X)

/-- The `f'` coefficient of the original operator. -/
def ode_a1 : PowerSeries ℚ := 1 - 20 * PowerSeries.X + 27 * PowerSeries.X ^ 2

/-- The `f` coefficient of the original operator. -/
def ode_a0 : PowerSeries ℚ := 3 * (3 * PowerSeries.X - 1)

/-- The left hand side of the original (`x`-space) differential equation. -/
def ode_pb_L (f : PowerSeries ℚ) : PowerSeries ℚ :=
  ode_a2 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)
    + ode_a1 * (PowerSeries.derivative (R := ℚ)) f + ode_a0 * f

/-- The left hand side of the pulled-back differential equation. -/
def ode_pb_M (g : PowerSeries ℚ) : PowerSeries ℚ :=
  ode_b2 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) g)
    + ode_b1 * (PowerSeries.derivative (R := ℚ)) g + ode_b0 * g

/-- `ψ`-substituted form of `ode_b2`. -/
def ode_e2 : PowerSeries ℚ := ode_mobPsi * (1 - 8 * ode_mobPsi) * (1 + ode_mobPsi)

/-- `ψ`-substituted form of `ode_b1`. -/
def ode_e1 : PowerSeries ℚ := 1 - 14 * ode_mobPsi - 24 * ode_mobPsi ^ 2

/-- `ψ`-substituted form of `ode_b0`. -/
def ode_e0 : PowerSeries ℚ := -2 - 8 * ode_mobPsi

/-- Explicit form of `w·d/dX ((1−X)·f)`. -/
def ode_q1 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  -f + (1 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) f

/-- Explicit form of `w·d/dX (w·d/dX ((1−X)·f))`. -/
def ode_q2 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  2 * f - 4 * (1 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) f
    + (1 - PowerSeries.X) ^ 2 * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)

/-! ## Elementary properties of the Möbius substitution -/

lemma ode_mobPsi_hasSubst : PowerSeries.HasSubst ode_mobPsi := by
  unfold ode_mobPsi
  exact PowerSeries.HasSubst.mul_left (PowerSeries.HasSubst.X')

lemma ode_mobPhi_hasSubst : PowerSeries.HasSubst ode_mobPhi := by
  unfold ode_mobPhi
  exact PowerSeries.HasSubst.mul_left (PowerSeries.HasSubst.X')

lemma ode_one_sub_X_mul_mobPsi : (1 - PowerSeries.X) * ode_mobPsi = PowerSeries.X := by
  unfold ode_mobPsi
  calc (1 - PowerSeries.X) * (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = PowerSeries.X * ((1 - PowerSeries.X) * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) := by
          ring
    _ = PowerSeries.X * 1 := by rw [PowerSeries.mul_inv_cancel]; simp
    _ = PowerSeries.X := by ring

lemma ode_mobPsi_constantCoeff : PowerSeries.constantCoeff ode_mobPsi = 0 := by
  unfold ode_mobPsi; simp

lemma ode_mobPsi_coeff_one : PowerSeries.coeff 1 ode_mobPsi = 1 := by
  unfold ode_mobPsi
  rw [mul_comm PowerSeries.X ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹]
  rw [Commons.RingTheory.PowerSeries.coeff_mul_X]
  simp [PowerSeries.constantCoeff_inv]

lemma ode_mobPsi_subst_injective :
    Function.Injective (PowerSeries.subst (R := ℚ) ode_mobPsi) :=
  Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero ode_mobPsi_constantCoeff
    (by rw [ode_mobPsi_coeff_one]; exact isUnit_one)

/-! ## Substitution of constants and of `(1+X)⁻¹` -/

lemma ode_subst_one : PowerSeries.subst ode_mobPsi (1 : PowerSeries ℚ) = 1 := by
  have h := map_one (PowerSeries.substAlgHom (R := ℚ) ode_mobPsi_hasSubst)
  rwa [PowerSeries.coe_substAlgHom] at h

lemma ode_subst_zero : PowerSeries.subst ode_mobPsi (0 : PowerSeries ℚ) = 0 := by
  have h := map_zero (PowerSeries.substAlgHom (R := ℚ) ode_mobPsi_hasSubst)
  rwa [PowerSeries.coe_substAlgHom] at h

lemma ode_subst_natCast (n : ℕ) :
    PowerSeries.subst ode_mobPsi (n : PowerSeries ℚ) = n := by
  have h := map_natCast (PowerSeries.substAlgHom (R := ℚ) ode_mobPsi_hasSubst) n
  rwa [PowerSeries.coe_substAlgHom] at h

lemma ode_subst_neg (x : PowerSeries ℚ) :
    PowerSeries.subst ode_mobPsi (-x) = -PowerSeries.subst ode_mobPsi x := by
  have h := map_neg (PowerSeries.substAlgHom (R := ℚ) ode_mobPsi_hasSubst) x
  rw [PowerSeries.coe_substAlgHom] at h
  exact h

lemma ode_subst_2 : PowerSeries.subst ode_mobPsi (2 : PowerSeries ℚ) = 2 := by
  rw [show (2 : PowerSeries ℚ) = ((2 : ℕ) : PowerSeries ℚ) from rfl]; exact ode_subst_natCast 2

lemma ode_subst_8 : PowerSeries.subst ode_mobPsi (8 : PowerSeries ℚ) = 8 := by
  rw [show (8 : PowerSeries ℚ) = ((8 : ℕ) : PowerSeries ℚ) from rfl]; exact ode_subst_natCast 8

lemma ode_subst_14 : PowerSeries.subst ode_mobPsi (14 : PowerSeries ℚ) = 14 := by
  rw [show (14 : PowerSeries ℚ) = ((14 : ℕ) : PowerSeries ℚ) from rfl]; exact ode_subst_natCast 14

lemma ode_subst_24 : PowerSeries.subst ode_mobPsi (24 : PowerSeries ℚ) = 24 := by
  rw [show (24 : PowerSeries ℚ) = ((24 : ℕ) : PowerSeries ℚ) from rfl]; exact ode_subst_natCast 24

lemma ode_mobPsi_add_one : ode_mobPsi + 1 = ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by
  have hcc : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - PowerSeries.X) ≠ 0 := by simp
  have hmul : ((1 : PowerSeries ℚ) - PowerSeries.X) * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hcc
  have h2 : (ode_mobPsi + 1) * (1 - PowerSeries.X) = 1 := by
    calc (ode_mobPsi + 1) * (1 - PowerSeries.X)
        = (1 - PowerSeries.X) * ode_mobPsi + (1 - PowerSeries.X) := by ring
      _ = PowerSeries.X + (1 - PowerSeries.X) := by rw [ode_one_sub_X_mul_mobPsi]
      _ = 1 := by ring
  calc ode_mobPsi + 1 = (ode_mobPsi + 1) * 1 := by ring
    _ = (ode_mobPsi + 1)
          * (((1 : PowerSeries ℚ) - PowerSeries.X) * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) := by
          rw [hmul]
    _ = ((ode_mobPsi + 1) * ((1 : PowerSeries ℚ) - PowerSeries.X))
          * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by ring
    _ = 1 * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by rw [h2]
    _ = ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by ring

lemma ode_subst_mobPsi_X_add_one_inv :
    PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ = 1 - PowerSeries.X := by
  have hcc : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) + 1) ≠ 0 := by simp
  have hmul : ((PowerSeries.X : PowerSeries ℚ) + 1) * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hcc
  have key : PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
      * (ode_mobPsi + 1) = 1 := by
    have h := congrArg (PowerSeries.subst ode_mobPsi) hmul
    simp only [PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_add ode_mobPsi_hasSubst,
      PowerSeries.subst_X ode_mobPsi_hasSubst, ode_subst_one] at h
    rw [mul_comm]
    exact h
  have h2 : (ode_mobPsi + 1) * (1 - PowerSeries.X) = 1 := by
    calc (ode_mobPsi + 1) * (1 - PowerSeries.X)
        = (1 - PowerSeries.X) * ode_mobPsi + (1 - PowerSeries.X) := by ring
      _ = PowerSeries.X + (1 - PowerSeries.X) := by rw [ode_one_sub_X_mul_mobPsi]
      _ = 1 := by ring
  calc PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
      = (PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) * 1 := by ring
    _ = (PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹)
          * ((ode_mobPsi + 1) * (1 - PowerSeries.X)) := by rw [h2]
    _ = ((PowerSeries.subst ode_mobPsi ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) * (ode_mobPsi + 1))
          * (1 - PowerSeries.X) := by ring
    _ = 1 * (1 - PowerSeries.X) := by rw [key]
    _ = 1 - PowerSeries.X := by ring

lemma ode_subst_mobPsi_mobPhi : PowerSeries.subst ode_mobPsi ode_mobPhi = PowerSeries.X := by
  unfold ode_mobPhi
  rw [PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_X ode_mobPsi_hasSubst]
  rw [ode_subst_mobPsi_X_add_one_inv]
  rw [mul_comm ode_mobPsi (1 - PowerSeries.X), ode_one_sub_X_mul_mobPsi]

/-! ## Derivative and chain-rule data -/

lemma ode_deriv_mobPsi : (PowerSeries.derivative (R := ℚ)) ode_mobPsi =
    (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) ^ 2 := by
  have heq : ode_mobPsi = ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ - 1 := by
    rw [← ode_mobPsi_add_one]; ring
  rw [heq, map_sub, PowerSeries.derivative_inv']
  simp

lemma ode_deriv_mobPsi_mul_mobW :
    (PowerSeries.derivative (R := ℚ)) ode_mobPsi * ode_mobW = 1 := by
  rw [ode_deriv_mobPsi]
  unfold ode_mobW
  rw [← mul_pow, PowerSeries.inv_mul_cancel ((1 : PowerSeries ℚ) - PowerSeries.X) (by simp)]
  norm_num

lemma ode_deriv_one_sub_X_sq :
    (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) ^ 2) = -2 * (1 - PowerSeries.X) := by
  rw [PowerSeries.derivative_pow]
  simp

/-- The chain rule in the form we use it: `(Dⁱ G) ∘ ψ = (w·D)ⁱ (G ∘ ψ)`. -/
lemma ode_subst_mobPsi_iterate (G : PowerSeries ℚ) (i : ℕ) :
    PowerSeries.subst ode_mobPsi (((fun g : PowerSeries ℚ => (PowerSeries.derivative (R := ℚ)) g)^[i]) G)
      = ((fun g : PowerSeries ℚ => ode_mobW * (PowerSeries.derivative (R := ℚ)) g)^[i])
          (PowerSeries.subst ode_mobPsi G) :=
  (Commons.RingTheory.PowerSeries.iterate_subst_deriv_scaled ℚ G ode_mobPsi ode_mobW i
    ode_mobPsi_hasSubst ode_deriv_mobPsi_mul_mobW).symm

/-! ## The substitution acts on the coefficients as expected -/

lemma ode_subst_mobPsi_b2 : PowerSeries.subst ode_mobPsi ode_b2 = ode_e2 := by
  unfold ode_e2 ode_b2
  simp only [PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_add ode_mobPsi_hasSubst,
    PowerSeries.subst_sub ode_mobPsi_hasSubst, PowerSeries.subst_X ode_mobPsi_hasSubst,
    ode_subst_one, ode_subst_8]

lemma ode_subst_mobPsi_b1 : PowerSeries.subst ode_mobPsi ode_b1 = ode_e1 := by
  unfold ode_e1 ode_b1
  simp only [PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_sub ode_mobPsi_hasSubst,
    PowerSeries.subst_X ode_mobPsi_hasSubst, PowerSeries.subst_pow ode_mobPsi_hasSubst,
    ode_subst_one, ode_subst_14, ode_subst_24]

lemma ode_subst_mobPsi_b0 : PowerSeries.subst ode_mobPsi ode_b0 = ode_e0 := by
  unfold ode_e0 ode_b0
  simp only [PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_sub ode_mobPsi_hasSubst,
    PowerSeries.subst_X ode_mobPsi_hasSubst, ode_subst_neg, ode_subst_2, ode_subst_8]

/-! ## Clearing the `(1−X)` denominator -/

lemma ode_c2 : (1 - PowerSeries.X) ^ 3 * ode_e2 = PowerSeries.X * (1 - 9 * PowerSeries.X) := by
  unfold ode_e2
  have hA : (1 - PowerSeries.X) * (1 - 8 * ode_mobPsi) = 1 - 9 * PowerSeries.X := by
    calc (1 - PowerSeries.X) * (1 - 8 * ode_mobPsi)
        = (1 - PowerSeries.X) - 8 * ((1 - PowerSeries.X) * ode_mobPsi) := by ring
      _ = 1 - 9 * PowerSeries.X := by rw [ode_one_sub_X_mul_mobPsi]; ring
  have hB : (1 - PowerSeries.X) * (1 + ode_mobPsi) = 1 := by
    calc (1 - PowerSeries.X) * (1 + ode_mobPsi)
        = (1 - PowerSeries.X) + (1 - PowerSeries.X) * ode_mobPsi := by ring
      _ = 1 := by rw [ode_one_sub_X_mul_mobPsi]; ring
  calc (1 - PowerSeries.X) ^ 3 * (ode_mobPsi * (1 - 8 * ode_mobPsi) * (1 + ode_mobPsi))
      = ((1 - PowerSeries.X) * ode_mobPsi) * ((1 - PowerSeries.X) * (1 - 8 * ode_mobPsi))
          * ((1 - PowerSeries.X) * (1 + ode_mobPsi)) := by ring
    _ = PowerSeries.X * (1 - 9 * PowerSeries.X) * 1 := by
          rw [ode_one_sub_X_mul_mobPsi, hA, hB]
    _ = PowerSeries.X * (1 - 9 * PowerSeries.X) := by ring

lemma ode_c1 :
    (1 - PowerSeries.X) ^ 2 * ode_e1
      = (1 - PowerSeries.X) ^ 2 - 14 * PowerSeries.X * (1 - PowerSeries.X)
          - 24 * PowerSeries.X ^ 2 := by
  unfold ode_e1
  have hp : (1 - PowerSeries.X) ^ 2 * ode_mobPsi = PowerSeries.X * (1 - PowerSeries.X) := by
    calc (1 - PowerSeries.X) ^ 2 * ode_mobPsi
        = ((1 - PowerSeries.X) * ode_mobPsi) * (1 - PowerSeries.X) := by ring
      _ = PowerSeries.X * (1 - PowerSeries.X) := by rw [ode_one_sub_X_mul_mobPsi]
  have hp2 : (1 - PowerSeries.X) ^ 2 * ode_mobPsi ^ 2 = PowerSeries.X ^ 2 := by
    calc (1 - PowerSeries.X) ^ 2 * ode_mobPsi ^ 2
        = ((1 - PowerSeries.X) * ode_mobPsi) ^ 2 := by ring
      _ = PowerSeries.X ^ 2 := by rw [ode_one_sub_X_mul_mobPsi]
  calc (1 - PowerSeries.X) ^ 2 * (1 - 14 * ode_mobPsi - 24 * ode_mobPsi ^ 2)
      = (1 - PowerSeries.X) ^ 2 - 14 * ((1 - PowerSeries.X) ^ 2 * ode_mobPsi)
          - 24 * ((1 - PowerSeries.X) ^ 2 * ode_mobPsi ^ 2) := by ring
    _ = (1 - PowerSeries.X) ^ 2 - 14 * PowerSeries.X * (1 - PowerSeries.X)
          - 24 * PowerSeries.X ^ 2 := by rw [hp, hp2]; ring

lemma ode_c0 : (1 - PowerSeries.X) * ode_e0 = -2 - 6 * PowerSeries.X := by
  unfold ode_e0
  calc (1 - PowerSeries.X) * (-2 - 8 * ode_mobPsi)
      = -2 * (1 - PowerSeries.X) - 8 * ((1 - PowerSeries.X) * ode_mobPsi) := by ring
    _ = -2 - 6 * PowerSeries.X := by rw [ode_one_sub_X_mul_mobPsi]; ring

/-! ## The explicit expansions of the scaled derivatives -/

lemma ode_d1 (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) * f) = ode_q1 f := by
  unfold ode_q1
  rw [Derivation.leibniz]
  simp
  ring

lemma ode_dq1 (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (ode_q1 f)
      = -2 * (PowerSeries.derivative (R := ℚ)) f
        + (1 - PowerSeries.X) * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f) := by
  unfold ode_q1
  rw [map_add, map_neg, Derivation.leibniz]
  simp
  ring

lemma ode_P1_expand (f : PowerSeries ℚ) :
    ode_mobW * (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) * f)
      = (1 - PowerSeries.X) ^ 2 * ode_q1 f := by
  unfold ode_mobW
  rw [ode_d1]

lemma ode_P2_expand (f : PowerSeries ℚ) :
    ode_mobW * (PowerSeries.derivative (R := ℚ)) (ode_mobW * (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) * f))
      = (1 - PowerSeries.X) ^ 3 * ode_q2 f := by
  rw [ode_P1_expand, Derivation.leibniz, ode_deriv_one_sub_X_sq]
  simp only [smul_eq_mul]
  rw [ode_dq1]
  unfold ode_q2 ode_q1 ode_mobW
  ring

/-! ## The main computation -/

lemma ode_subst_mobPsi_G (f : PowerSeries ℚ) :
    PowerSeries.subst ode_mobPsi (ode_mobU * f.subst ode_mobPhi) = (1 - PowerSeries.X) * f := by
  unfold ode_mobU
  rw [PowerSeries.subst_mul ode_mobPsi_hasSubst, ode_subst_mobPsi_X_add_one_inv]
  rw [PowerSeries.subst_comp_subst_apply ode_mobPhi_hasSubst ode_mobPsi_hasSubst,
    ode_subst_mobPsi_mobPhi, PowerSeries.X_subst]

lemma ode_subst_mobPsi_L_mode (f : PowerSeries ℚ) :
    PowerSeries.subst ode_mobPsi (ode_pb_M (ode_mobU * f.subst ode_mobPhi))
      = (1 - PowerSeries.X) * ode_pb_L f := by
  have hG := ode_subst_mobPsi_G f
  have h1 : PowerSeries.subst ode_mobPsi
        ((PowerSeries.derivative (R := ℚ)) (ode_mobU * f.subst ode_mobPhi))
      = ode_mobW * (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) * f) := by
    have h := ode_subst_mobPsi_iterate (ode_mobU * f.subst ode_mobPhi) 1
    rw [hG] at h
    simpa only [Function.iterate_one] using h
  have h2 : PowerSeries.subst ode_mobPsi
        ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) (ode_mobU * f.subst ode_mobPhi)))
      = ode_mobW * (PowerSeries.derivative (R := ℚ))
          (ode_mobW * (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X) * f)) := by
    have h := ode_subst_mobPsi_iterate (ode_mobU * f.subst ode_mobPhi) 2
    rw [hG] at h
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using h
  unfold ode_pb_M
  rw [PowerSeries.subst_add ode_mobPsi_hasSubst, PowerSeries.subst_add ode_mobPsi_hasSubst,
    PowerSeries.subst_mul ode_mobPsi_hasSubst, PowerSeries.subst_mul ode_mobPsi_hasSubst,
    PowerSeries.subst_mul ode_mobPsi_hasSubst,
    h2, h1, hG, ode_subst_mobPsi_b2, ode_subst_mobPsi_b1, ode_subst_mobPsi_b0,
    ode_P2_expand, ode_P1_expand]
  have hA : ode_e2 * ((1 - PowerSeries.X) ^ 3 * ode_q2 f)
      = PowerSeries.X * (1 - 9 * PowerSeries.X) * ode_q2 f := by
    rw [show ode_e2 * ((1 - PowerSeries.X) ^ 3 * ode_q2 f)
        = ((1 - PowerSeries.X) ^ 3 * ode_e2) * ode_q2 f from by ring, ode_c2]
  have hB : ode_e1 * ((1 - PowerSeries.X) ^ 2 * ode_q1 f)
      = ((1 - PowerSeries.X) ^ 2 - 14 * PowerSeries.X * (1 - PowerSeries.X)
          - 24 * PowerSeries.X ^ 2) * ode_q1 f := by
    rw [show ode_e1 * ((1 - PowerSeries.X) ^ 2 * ode_q1 f)
        = ((1 - PowerSeries.X) ^ 2 * ode_e1) * ode_q1 f from by ring, ode_c1]
  have hC : ode_e0 * ((1 - PowerSeries.X) * f) = (-2 - 6 * PowerSeries.X) * f := by
    rw [show ode_e0 * ((1 - PowerSeries.X) * f)
        = ((1 - PowerSeries.X) * ode_e0) * f from by ring, ode_c0]
  rw [hA, hB, hC]
  unfold ode_pb_L ode_a2 ode_a1 ode_a0 ode_q1 ode_q2
  ring

end

theorem ode_pullback_mobius (f : PowerSeries ℚ)
    (h : PowerSeries.X * (1 - PowerSeries.X) * (1 - PowerSeries.C 9 * PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)
          + (1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2)
            * (PowerSeries.derivative (R := ℚ)) f
          + PowerSeries.C 3 * (PowerSeries.C 3 * PowerSeries.X - 1) * f = 0) :
    PowerSeries.X * (1 - PowerSeries.C 8 * PowerSeries.X) * (1 + PowerSeries.X)
        * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
            (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
              * f.subst (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹)))
      + (1 - PowerSeries.C 14 * PowerSeries.X - PowerSeries.C 24 * PowerSeries.X ^ 2)
        * (PowerSeries.derivative (R := ℚ)) (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
            * f.subst (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹))
      + (-PowerSeries.C 2 - PowerSeries.C 8 * PowerSeries.X)
        * (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
            * f.subst (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹)) = 0 := by
  change ode_pb_M (ode_mobU * f.subst ode_mobPhi) = 0
  have hL : ode_pb_L f = 0 := h
  have hkey := ode_subst_mobPsi_L_mode f
  have hzero : PowerSeries.subst ode_mobPsi (ode_pb_M (ode_mobU * f.subst ode_mobPhi)) = 0 := by
    rw [hkey, hL, mul_zero]
  exact ode_mobPsi_subst_injective
    (show PowerSeries.subst ode_mobPsi (ode_pb_M (ode_mobU * f.subst ode_mobPhi))
        = PowerSeries.subst ode_mobPsi (0 : PowerSeries ℚ) from by rw [hzero, ode_subst_zero])

end Commons.Analysis.Differential