/-
# The twisted carries of the blocks `T^n`

`Work.Asymptotics.TwistOddBlocks` defines the candidate twisted carries `TpowA n i`, `TpowB n i`
of the blocks `T^n` (`n ≥ 0`) by the cocycle recursion.  This file proves

* `TpowA_flat` / `TpowB_flat`: the flat formula
  `TpowA n i = ∑_{m<n} tvecA (n-1-m) i * ofSL (T^m)`, which exhibits the support of the carry;
* `Tpow_spec`: `carryCombOdd (TpowA n i) (TpowB n i) = twist (T^n) i`;
* `Tpow_bound`, `Tpow_bound_Frob`: polynomial bounds for `coeffNorm` and `supportFrobLe`.

Together with the ℤ-indexed blocks `TblockA/B` and the blocks `S T^k` these are the inputs of
the final assembly of `Work.Asymptotics.carry_twist_odd`.
-/
import Mathlib
import Submission.Work.Asymptotics.TwistOddBlocks
import Submission.Work.Asymptotics.TwistOddLetters
import Submission.Work.Asymptotics.twist_atomT_odd
import Submission.Work.Asymptotics.oddMT_pow_entry_bound
import Submission.Work.Asymptotics.CarryBoundBasic

set_option maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The representation on the powers of `T` -/

theorem sigmaHom_S : sigmaHom ModularGroup.S = oddMS := by
  rw [sigmaHom_eq_SigmaOdd, SigmaOdd_ofSL, oddRep_S]

theorem sigmaHom_T_zpow (n : ℕ) :
    sigmaHom (ModularGroup.T ^ (n : ℤ)) = oddMT ^ n := by
  rw [sigmaHom_eq_SigmaOdd, SigmaOdd_ofSL, zpow_natCast, map_pow, oddRep_T]

/-- `σ(T^{-n}) = oddMT⁻¹ ^ n`.  Matrices are only a monoid, so the negative powers are handled
through the uniqueness of the inverse inside the monoid rather than by `map_zpow`. -/
theorem sigmaHom_T_zpow_neg (n : ℕ) :
    sigmaHom (ModularGroup.T ^ (-(n : ℤ))) = oddMTi ^ n := by
  have hT : sigmaHom (ModularGroup.T) = oddMT := by
    simpa using sigmaHom_T_zpow 1
  have hinv : sigmaHom ((ModularGroup.T : SL(2,ℤ))⁻¹) = oddMTi := by
    have h : sigmaHom ((ModularGroup.T : SL(2,ℤ)) * ModularGroup.T⁻¹) = 1 := by
      rw [mul_inv_cancel, map_one]
    rw [map_mul, hT] at h
    calc sigmaHom ((ModularGroup.T : SL(2,ℤ))⁻¹)
        = 1 * sigmaHom ((ModularGroup.T : SL(2,ℤ))⁻¹) := (one_mul _).symm
      _ = (oddMTi * oddMT) * sigmaHom ((ModularGroup.T : SL(2,ℤ))⁻¹) := by rw [oddMTi_mul_oddMT]
      _ = oddMTi * (oddMT * sigmaHom ((ModularGroup.T : SL(2,ℤ))⁻¹)) := mul_assoc _ _ _
      _ = oddMTi * 1 := by rw [h]
      _ = oddMTi := mul_one _
  induction n with
  | zero =>
    rw [show ((-(↑(0 : ℕ)) : ℤ)) = (0 : ℤ) by norm_num, zpow_zero, map_one, pow_zero]
  | succ k ih =>
    have hz : (ModularGroup.T : SL(2,ℤ)) ^ (-(((k : ℤ) + 1)))
        = ModularGroup.T ^ (-(k : ℤ)) * ModularGroup.T⁻¹ := by
      rw [show (-(((k : ℤ) + 1))) = (-(k : ℤ)) + (-1) by ring, _root_.zpow_add, _root_.zpow_neg_one]
    rw [show ((-(↑(k + 1)) : ℤ)) = -(((k : ℤ) + 1)) by push_cast; ring, hz, map_mul, hinv, ih,
      pow_succ]

/-! ## The flat formula for the block carries -/

theorem TpowA_flat (n : ℕ) (i : Fin 6) :
    TpowA n i = ∑ m ∈ Finset.range n,
      tvecA (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ)) := by
  induction n with
  | zero => rw [TpowA_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [TpowA_succ, ih, Finset.sum_mul, Finset.sum_range_succ']
    have hf0 : tvecA (n + 1 - 1 - 0) i * ofSL (ModularGroup.T ^ (((0 : ℕ)) : ℤ)) = tvecA n i := by
      rw [show (((0 : ℕ)) : ℤ) = (0 : ℤ) by norm_num, zpow_zero, ofSL_one, mul_one]
      try congr 1
    rw [hf0, add_comm (tvecA n i)]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m < n := Finset.mem_range.mp hm
    have hidx : n - 1 - m = n + 1 - 1 - (m + 1) := by omega
    have hm1 : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hidx, hm1, mul_assoc, ← ofSL_mul, ← _root_.zpow_add_one]

theorem TpowB_flat (n : ℕ) (i : Fin 6) :
    TpowB n i = ∑ m ∈ Finset.range n,
      tvecB (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ)) := by
  induction n with
  | zero => rw [TpowB_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    rw [TpowB_succ, ih, Finset.sum_mul, Finset.sum_range_succ']
    have hf0 : tvecB (n + 1 - 1 - 0) i * ofSL (ModularGroup.T ^ (((0 : ℕ)) : ℤ)) = tvecB n i := by
      rw [show (((0 : ℕ)) : ℤ) = (0 : ℤ) by norm_num, zpow_zero, ofSL_one, mul_one]
      try congr 1
    rw [hf0, add_comm (tvecB n i)]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m < n := Finset.mem_range.mp hm
    have hidx : n - 1 - m = n + 1 - 1 - (m + 1) := by omega
    have hm1 : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    rw [hidx, hm1, mul_assoc, ← ofSL_mul, ← _root_.zpow_add_one]

/-! ## The cocycle identity for the block carries -/

theorem Tpow_spec :
    ∀ n : ℕ, ∀ i : Fin 6,
      carryCombOdd (TpowA n i) (TpowB n i) = twist (ModularGroup.T ^ (n : ℤ)) i := by
  intro n
  induction n with
  | zero =>
    intro i
    rw [TpowA_zero, TpowB_zero, carryCombOdd_zero,
      show ((0 : ℕ) : ℤ) = (0 : ℤ) by norm_num, zpow_zero, twist_one]
  | succ n ih =>
    intro i
    rw [TpowA_succ, TpowB_succ, tvecA, tvecB, carryCombOdd_add, carryCombOdd_sum_univ,
      carryCombOdd_mul_of, ih i]
    have hsum : (∑ j : Fin 6, (oddMT ^ n) i j • carryCombOdd (atomTA j) (atomTB j))
        = ∑ j : Fin 6, (sigmaHom (ModularGroup.T ^ (n : ℤ))) i j • twist ModularGroup.T j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [twist_atomT_odd.1 j, ← sigmaHom_T_zpow n]
    rw [hsum, ← twist_cocycle (ModularGroup.T ^ (n : ℤ)) ModularGroup.T i,
      show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, _root_.zpow_add_one]

/-! ## Bounds -/

/-- A bound `C * x ^ N` with real exponent becomes a bound with natural constant and exponent,
for `x ≥ 1`. -/
lemma rpow_to_pow {C : ℝ} (hC : 0 ≤ C) {N : ℝ} (hN : 0 ≤ N) :
    ∃ C' N' : ℕ, ∀ x : ℝ, 1 ≤ x → C * x ^ N ≤ C' * x ^ N' := by
  refine ⟨⌈C⌉₊ + 1, ⌈N⌉₊, fun x hx => ?_⟩
  have h1 : C ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil C]
  have h2 : N ≤ ((⌈N⌉₊ : ℕ) : ℝ) := Nat.le_ceil N
  have hx0 : (0 : ℝ) < x := by linarith
  have hstep : x ^ N ≤ x ^ (⌈N⌉₊ : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx h2
    rwa [Real.rpow_natCast] at h
  calc C * x ^ N ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) * x ^ N :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hx0) N)
    _ ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) * x ^ (⌈N⌉₊ : ℕ) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The entrywise growth of the powers of `oddMT`, with natural constant and exponent. -/
lemma oddMT_entry_bound_nat :
    ∃ C N : ℕ, ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((oddMT ^ m) i j)‖ ≤ C * (2 + (m : ℝ)) ^ N := by
  obtain ⟨C0, N0, hC0, hN0, h⟩ := oddMT_pow_entry_bound
  obtain ⟨C1, N1, h1⟩ := rpow_to_pow hC0 hN0
  refine ⟨C1, N1, fun m i j => ?_⟩
  have hm : (1 : ℝ) ≤ 2 + (m : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc ‖((oddMT ^ m) i j)‖ ≤ C0 * (1 + (m : ℝ)) ^ N0 := h.1 m i j
    _ ≤ C0 * (2 + (m : ℝ)) ^ N0 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by linarith) hN0) hC0
    _ ≤ C1 * (2 + (m : ℝ)) ^ N1 := h1 _ hm

/-- A version of `oddMT_entry_bound_nat` in terms of `1 + Frob (T^m)`. -/
lemma oddMT_entry_bound_nat_Frob :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((oddMT ^ m) i j)‖ ≤ C * (1 + Frob (ModularGroup.T ^ (m : ℤ))) ^ N := by
  obtain ⟨C, N, h⟩ := oddMT_entry_bound_nat
  refine ⟨(3 : ℝ) ^ N * C, by positivity, N, fun m i j => ?_⟩
  have hF : (m : ℝ) ≤ Frob (ModularGroup.T ^ (m : ℤ)) := by
    have h1 := abs_le_Frob_T_zpow (m : ℤ)
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m)] at h1
    exact h1
  have h2 : (2 : ℝ) + (m : ℝ) ≤ 3 * (1 + Frob (ModularGroup.T ^ (m : ℤ))) := by linarith
  have h3 : (0 : ℝ) ≤ 2 + (m : ℝ) := by positivity
  calc ‖((oddMT ^ m) i j)‖ ≤ (C : ℝ) * (2 + (m : ℝ)) ^ N := h m i j
    _ ≤ (C : ℝ) * (3 * (1 + Frob (ModularGroup.T ^ (m : ℤ)))) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (Nat.cast_nonneg C)
    _ = ((3 : ℝ) ^ N * C) * (1 + Frob (ModularGroup.T ^ (m : ℤ))) ^ N := by
        rw [mul_pow]
        ring

/-- A finite sum of reals over `range n` with each term bounded by `B`. -/
lemma sum_range_le_mul {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (h : ∀ m ∈ Finset.range n, f m ≤ B) :
    ∑ m ∈ Finset.range n, f m ≤ (n : ℝ) * B := by
  calc ∑ m ∈ Finset.range n, f m ≤ ∑ _m ∈ Finset.range n, B := Finset.sum_le_sum h
    _ = (n : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `coeffNorm` of the rotated atom vector. -/
lemma coeffNorm_tvecA_le {Cm Nm : ℕ} {A : ℝ}
    (hCm : ∀ m : ℕ, ∀ i j : Fin 6, ‖((oddMT ^ m) i j)‖ ≤ Cm * (2 + (m : ℝ)) ^ Nm)
    (hA : ∀ i : Fin 6, coeffNorm (atomTA i) ≤ A) {k n : ℕ} (hk : k ≤ n) (i : Fin 6) :
    coeffNorm (tvecA k i) ≤ 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
  have hkn : (2 : ℝ) + (k : ℝ) ≤ 2 + (n : ℝ) := by
    have : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
    linarith
  have hbk : (0 : ℝ) ≤ 2 + (k : ℝ) := by positivity
  rw [tvecA]
  calc coeffNorm (∑ j : Fin 6, (oddMT ^ k) i j • atomTA j)
      ≤ ∑ j : Fin 6, ‖((oddMT ^ k) i j)‖ * coeffNorm (atomTA j) := coeffNorm_smul_sum_le _ _ _
    _ ≤ ∑ _j : Fin 6, ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ‖((oddMT ^ k) i j)‖ ≤ (Cm : ℝ) * (2 + (n : ℝ)) ^ Nm :=
          le_trans (hCm k i j)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbk hkn Nm) (Nat.cast_nonneg Cm))
        exact mul_le_mul h1 (hA j) (coeffNorm_nonneg _) (by positivity)
    _ = 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `coeffNorm` of the rotated atom vector (second component). -/
lemma coeffNorm_tvecB_le {Cm Nm : ℕ} {A : ℝ}
    (hCm : ∀ m : ℕ, ∀ i j : Fin 6, ‖((oddMT ^ m) i j)‖ ≤ Cm * (2 + (m : ℝ)) ^ Nm)
    (hA : ∀ i : Fin 6, coeffNorm (atomTB i) ≤ A) {k n : ℕ} (hk : k ≤ n) (i : Fin 6) :
    coeffNorm (tvecB k i) ≤ 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
  have hkn : (2 : ℝ) + (k : ℝ) ≤ 2 + (n : ℝ) := by
    have : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
    linarith
  have hbk : (0 : ℝ) ≤ 2 + (k : ℝ) := by positivity
  rw [tvecB]
  calc coeffNorm (∑ j : Fin 6, (oddMT ^ k) i j • atomTB j)
      ≤ ∑ j : Fin 6, ‖((oddMT ^ k) i j)‖ * coeffNorm (atomTB j) := coeffNorm_smul_sum_le _ _ _
    _ ≤ ∑ _j : Fin 6, ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ‖((oddMT ^ k) i j)‖ ≤ (Cm : ℝ) * (2 + (n : ℝ)) ^ Nm :=
          le_trans (hCm k i j)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbk hkn Nm) (Nat.cast_nonneg Cm))
        exact mul_le_mul h1 (hA j) (coeffNorm_nonneg _) (by positivity)
    _ = 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Polynomial bounds for the block carries `TpowA`, `TpowB`.** -/
theorem Tpow_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, ∀ i : Fin 6,
      coeffNorm (TpowA n i) ≤ C * (2 + (n : ℝ)) ^ N ∧
      coeffNorm (TpowB n i) ≤ C * (2 + (n : ℝ)) ^ N ∧
      supportFrobLe (TpowA n i) (C * (2 + (n : ℝ)) ^ N) ∧
      supportFrobLe (TpowB n i) (C * (2 + (n : ℝ)) ^ N) := by
  obtain ⟨Cm, Nm, hCm⟩ := oddMT_entry_bound_nat
  have hA : ∀ i : Fin 6, coeffNorm (atomTA i) ≤ (4 : ℝ) := fun i => (twist_atomT_odd.2 i).1
  have hB : ∀ i : Fin 6, coeffNorm (atomTB i) ≤ (4 : ℝ) := fun i => (twist_atomT_odd.2 i).2.1
  have hSA : ∀ i : Fin 6, supportFrobLe (atomTA i) (8 : ℝ) := fun i => (twist_atomT_odd.2 i).2.2.1
  have hSB : ∀ i : Fin 6, supportFrobLe (atomTB i) (8 : ℝ) := fun i => (twist_atomT_odd.2 i).2.2.2
  refine ⟨24 * (Cm : ℝ) + 8, by positivity, Nm + 1, fun n i => ?_⟩
  have hb1 : (1 : ℝ) ≤ 2 + (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- the coefficient bound
  have hcoe : (0 : ℝ) ≤ 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * 4 := by positivity
  have hstep : ∀ m ∈ Finset.range n,
      coeffNorm (tvecA (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ)))
        ≤ 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * 4 := by
    intro m hm
    refine le_trans (coeffNorm_mul_of_le _ _) ?_
    exact coeffNorm_tvecA_le hCm hA (by have := Finset.mem_range.mp hm; omega) i
  have hstepB : ∀ m ∈ Finset.range n,
      coeffNorm (tvecB (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ)))
        ≤ 6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * 4 := by
    intro m hm
    refine le_trans (coeffNorm_mul_of_le _ _) ?_
    exact coeffNorm_tvecB_le hCm hB (by have := Finset.mem_range.mp hm; omega) i
  have harith : (n : ℝ) * (6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * 4)
      ≤ (24 * (Cm : ℝ) + 8) * (2 + (n : ℝ)) ^ (Nm + 1) := by
    have h3 : (0 : ℝ) ≤ 24 * (Cm : ℝ) * (2 + (n : ℝ)) ^ Nm := by positivity
    calc (n : ℝ) * (6 * ((Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * 4)
        = (24 * (Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * (n : ℝ) := by ring
      _ ≤ (24 * (Cm : ℝ) * (2 + (n : ℝ)) ^ Nm) * (2 + (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) h3
      _ = 24 * (Cm : ℝ) * (2 + (n : ℝ)) ^ (Nm + 1) := by rw [pow_succ]; ring
      _ ≤ (24 * (Cm : ℝ) + 8) * (2 + (n : ℝ)) ^ (Nm + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
  have hup : (8 : ℝ) * (2 + (n : ℝ)) ≤ (24 * (Cm : ℝ) + 8) * (2 + (n : ℝ)) ^ (Nm + 1) := by
    have h6 : (2 : ℝ) + (n : ℝ) ≤ (2 + (n : ℝ)) ^ (Nm + 1) := by
      calc (2 + (n : ℝ)) = (2 + (n : ℝ)) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (2 + (n : ℝ)) ^ (Nm + 1) := pow_le_pow_right₀ hb1 (by omega)
    calc (8 : ℝ) * (2 + (n : ℝ)) ≤ (24 * (Cm : ℝ) + 8) * (2 + (n : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          linarith
      _ ≤ (24 * (Cm : ℝ) + 8) * (2 + (n : ℝ)) ^ (Nm + 1) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
  -- the support bound
  have hFrob : ∀ m ∈ Finset.range n, Frob (ModularGroup.T ^ (m : ℤ)) ≤ 2 + (n : ℝ) := by
    intro m hm
    have hm' : m < n := Finset.mem_range.mp hm
    rw [Frob_T_zpow]
    have h2 : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_of_lt hm')
    have h3 : (m : ℝ) ^ 2 + 2 ≤ (2 + (n : ℝ)) ^ 2 := by nlinarith
    calc Real.sqrt ((m : ℝ) ^ 2 + 2) ≤ Real.sqrt ((2 + (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt h3
      _ = 2 + (n : ℝ) := Real.sqrt_sq (by linarith)
  have hstepSA : ∀ m ∈ Finset.range n,
      supportFrobLe (tvecA (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ))) (8 * (2 + (n : ℝ))) := by
    intro m hm
    have h1 := supportFrobLe_mul_of
      (supportFrobLe_smul_sum Finset.univ (fun j : Fin 6 => (oddMT ^ (n - 1 - m)) i j)
        (atomTA) (fun j _ => hSA j)) (ModularGroup.T ^ (m : ℤ))
    refine supportFrobLe_mono h1 ?_
    exact mul_le_mul_of_nonneg_left (hFrob m hm) (by norm_num)
  have hstepSB : ∀ m ∈ Finset.range n,
      supportFrobLe (tvecB (n - 1 - m) i * ofSL (ModularGroup.T ^ (m : ℤ))) (8 * (2 + (n : ℝ))) := by
    intro m hm
    have h1 := supportFrobLe_mul_of
      (supportFrobLe_smul_sum Finset.univ (fun j : Fin 6 => (oddMT ^ (n - 1 - m)) i j)
        (atomTB) (fun j _ => hSB j)) (ModularGroup.T ^ (m : ℤ))
    refine supportFrobLe_mono h1 ?_
    exact mul_le_mul_of_nonneg_left (hFrob m hm) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TpowA_flat]
    exact le_trans (coeffNorm_sum_le (Finset.range n) _)
      (le_trans (sum_range_le_mul hstep) harith)
  · rw [TpowB_flat]
    exact le_trans (coeffNorm_sum_le (Finset.range n) _)
      (le_trans (sum_range_le_mul hstepB) harith)
  · rw [TpowA_flat]
    exact supportFrobLe_mono (supportFrobLe_sum _ _ hstepSA) hup
  · rw [TpowB_flat]
    exact supportFrobLe_mono (supportFrobLe_sum _ _ hstepSB) hup

/-- The block bound in terms of `1 + Frob (T^n)`. -/
theorem Tpow_bound_Frob :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, ∀ i : Fin 6,
      coeffNorm (TpowA n i) ≤ C * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N ∧
      coeffNorm (TpowB n i) ≤ C * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N ∧
      supportFrobLe (TpowA n i) (C * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N) ∧
      supportFrobLe (TpowB n i) (C * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N) := by
  obtain ⟨C, hC, N, h⟩ := Tpow_bound
  refine ⟨C * 3 ^ N, by positivity, N, fun n i => ?_⟩
  have hF : (n : ℝ) ≤ Frob (ModularGroup.T ^ (n : ℤ)) := by
    have h1 := abs_le_Frob_T_zpow (n : ℤ)
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)] at h1
    exact h1
  have h2 : (2 : ℝ) + (n : ℝ) ≤ 3 * (1 + Frob (ModularGroup.T ^ (n : ℤ))) := by linarith
  have h3 : (0 : ℝ) ≤ 2 + (n : ℝ) := by positivity
  have hmain : C * (2 + (n : ℝ)) ^ N
      ≤ (C * 3 ^ N) * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N := by
    calc C * (2 + (n : ℝ)) ^ N ≤ C * (3 * (1 + Frob (ModularGroup.T ^ (n : ℤ)))) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) hC
      _ = (C * 3 ^ N) * (1 + Frob (ModularGroup.T ^ (n : ℤ))) ^ N := by
          rw [mul_pow]; ring
  exact ⟨le_trans (h n i).1 hmain, le_trans (h n i).2.1 hmain,
    supportFrobLe_mono (h n i).2.2.1 hmain, supportFrobLe_mono (h n i).2.2.2 hmain⟩

end Work.Asymptotics
