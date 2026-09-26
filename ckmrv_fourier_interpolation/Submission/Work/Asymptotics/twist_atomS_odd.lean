import Mathlib
import Submission.Work.Asymptotics.TwistOddBlocks
import Submission.Work.Asymptotics.TwistOddDefs
import Submission.Work.Asymptotics.OddSigmaMatrices
import Submission.Work.Asymptotics.oddSigma_matrices
import Submission.Work.Asymptotics.CarryBoundBasic
import Submission.Work.Asymptotics.CarryBoundAtom
import Submission.Work.Asymptotics.carry_bound_odd
import Submission.Work.Asymptotics.PropagateBounds.Defs

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm
open Work.Kernels

/-! ## Auxiliary ring identities around the twist `1 - z`, `z = -I` -/

private lemma one_sub_Rneg_comm_S (x : R) : (1 - Rneg) * x = x * (1 - Rneg) := by
  rw [sub_mul, one_mul, mul_sub, mul_one, Work.Residues.Rneg_comm x]

private lemma one_sub_Rneg_mul_Rneg_add_one_S : (1 - Rneg) * (Rneg + 1) = 0 := by
  have h : Rneg * Rneg = (1 : R) := Work.Residues.Rneg_mul_Rneg
  calc (1 - Rneg) * (Rneg + 1)
      = (1 - Rneg) * Rneg + (1 - Rneg) * 1 := by rw [mul_add]
    _ = (Rneg - Rneg * Rneg) + (1 - Rneg) := by rw [sub_mul, one_mul, mul_one]
    _ = 0 := by rw [h]; noncomm_ring

/-- Twisting the three-generator combination `carryCombO a b c` by `1 - z` kills the third
generator and produces the two-generator combination `carryCombOdd` of the twisted carries. -/
private lemma twist_mul_carryCombO_S (a b c : R) :
    (1 - Rneg) * carryCombO a b c
      = carryCombOdd ((1 - Rneg) * a) ((1 - Rneg) * b) := by
  have h1 : (1 - Rneg) * ((R_T - 1) ^ 2 * a) = (R_T - 1) ^ 2 * ((1 - Rneg) * a) := by
    rw [← mul_assoc, one_sub_Rneg_comm_S, mul_assoc]
  have h2 : (1 - Rneg) * (R_S * (R_T - 1) ^ 2 * b)
      = R_S * (R_T - 1) ^ 2 * ((1 - Rneg) * b) := by
    rw [← mul_assoc, one_sub_Rneg_comm_S, mul_assoc]
  have h3 : (1 - Rneg) * ((Rneg + 1) * c) = 0 := by
    rw [← mul_assoc, one_sub_Rneg_mul_Rneg_add_one_S, zero_mul]
  simp only [carryCombO, carryCombOdd]
  rw [mul_add, mul_add, h1, h2, h3, add_zero]

/-! ## The two components of the twisted carry of the atom `S` -/

private lemma atomSA_eq (i : Fin 6) : atomSA i = (1 - Rneg) * (atomS i).1 := by
  fin_cases i <;> simp only [atomSA, atomS]
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_pos (by decide)] <;> first | rfl | noncomm_ring

private lemma atomSB_eq (i : Fin 6) : atomSB i = (1 - Rneg) * (atomS i).2.1 := by
  fin_cases i <;> simp only [atomSB, atomS]
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring

/-! ## The `ℓ¹`-norms of the atom components -/

private lemma cN_S_Tinv_1 : coeffNorm (R_Tinv : R) ≤ 1 := coeffNorm_of_le (ModularGroup.T)⁻¹

private lemma cN_S_Tinv_RS_1 : coeffNorm (R_Tinv * R_S : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le R_Tinv ModularGroup.S) cN_S_Tinv_1

private lemma cN_S_neg_Tinv_1 : coeffNorm (-R_Tinv : R) ≤ 1 :=
  le_trans (coeffNorm_neg_le _) cN_S_Tinv_1

private lemma cN_S_zero_1 : coeffNorm (0 : R) ≤ 1 := by
  rw [coeffNorm_zero]; norm_num

private lemma cN_atomS_fst (i : Fin 6) : coeffNorm (atomS i).1 ≤ 1 := by
  fin_cases i <;> simp only [atomS] <;>
    first
      | exact cN_S_zero_1 | exact cN_S_Tinv_RS_1 | exact cN_S_neg_Tinv_1

private lemma cN_atomS_snd (i : Fin 6) : coeffNorm (atomS i).2.1 ≤ 1 := by
  fin_cases i <;> simp only [atomS] <;>
    first
      | exact cN_S_zero_1 | exact cN_S_Tinv_RS_1 | exact cN_S_neg_Tinv_1

/-! ## The Frobenius support bounds of the atom components -/

private lemma Frob_S_Tinv_eq : Frob ((ModularGroup.T)⁻¹ : SL(2,ℤ)) = Real.sqrt 3 := by
  rw [← _root_.zpow_neg_one (ModularGroup.T), Frob_T_zpow]
  norm_num

private lemma sF_S_Tinv_4 : supportFrobLe (R_Tinv : R) 4 :=
  supportFrobLe_mono (supportFrobLe_of_le (ModularGroup.T)⁻¹) (by
    rw [Frob_S_Tinv_eq]
    nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3])

private lemma sF_S_neg_Tinv_4 : supportFrobLe (-R_Tinv : R) 4 :=
  supportFrobLe_neg sF_S_Tinv_4

private lemma sF_S_Tinv_RS_4 : supportFrobLe (R_Tinv * R_S : R) 4 := by
  have h : supportFrobLe (R_Tinv : R) (Real.sqrt 3) :=
    supportFrobLe_mono (supportFrobLe_of_le (ModularGroup.T)⁻¹) (le_of_eq Frob_S_Tinv_eq)
  have h2 : supportFrobLe (R_Tinv * R_S : R) (Real.sqrt 3 * Frob ModularGroup.S) :=
    supportFrobLe_mul_of h ModularGroup.S
  refine supportFrobLe_mono h2 ?_
  rw [Frob_S]
  exact sqrt_mul_sqrt_le 3 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma sF_S_zero_4 : supportFrobLe (0 : R) 4 := supportFrobLe_zero 4

private lemma sF_atomS_fst (i : Fin 6) : supportFrobLe (atomS i).1 4 := by
  fin_cases i <;> simp only [atomS] <;>
    first
      | exact sF_S_zero_4 | exact sF_S_Tinv_RS_4 | exact sF_S_neg_Tinv_4

private lemma sF_atomS_snd (i : Fin 6) : supportFrobLe (atomS i).2.1 4 := by
  fin_cases i <;> simp only [atomS] <;>
    first
      | exact sF_S_zero_4 | exact sF_S_Tinv_RS_4 | exact sF_S_neg_Tinv_4

/-! ## Twisting a single component -/

/-- Twisting by `1 - z` at most doubles the `ℓ¹`-norm. -/
private lemma coeffNorm_one_sub_Rneg_mul_S (x : R) :
    coeffNorm ((1 - Rneg) * x) ≤ 2 * coeffNorm x := by
  have h1 : (1 - Rneg) * x = x + -(Rneg * x) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  rw [h1]
  refine le_trans (coeffNorm_add_le x (-(Rneg * x))) ?_
  have h2 : coeffNorm (Rneg * x) ≤ coeffNorm x := by
    rw [Work.Residues.Rneg_comm x, Work.Residues.Rneg_eq_of]
    exact coeffNorm_mul_of_le x (-1)
  linarith [coeffNorm_neg_le (Rneg * x)]

/-- Twisting by `1 - z` multiplies the support Frobenius bound by at most `Frob (-1) = √2`
(in particular a bound of `4` becomes a bound of `8`). -/
private lemma supportFrobLe_one_sub_Rneg_mul_S {x : R} (hx : supportFrobLe x 4) :
    supportFrobLe ((1 - Rneg) * x) 8 := by
  have h1 : (1 - Rneg) * x = x + -(Rneg * x) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have hneg : supportFrobLe (-(Rneg * x)) 8 := by
    refine supportFrobLe_neg ?_
    have h2 : Rneg * x = x * MonoidAlgebra.of ℂ SL(2,ℤ) (-1 : SL(2,ℤ)) := by
      rw [Work.Residues.Rneg_comm x, Work.Residues.Rneg_eq_of]
    rw [h2]
    refine supportFrobLe_mono (supportFrobLe_mul_of (x := x) (K := 4) hx (-1 : SL(2,ℤ))) ?_
    rw [Frob_neg_one]
    nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]
  rw [h1]
  exact supportFrobLe_mono (supportFrobLe_add hx hneg) (by norm_num)

/-! ## The main statement -/

/-- The twisted carries of the atom `S` (the components `atomSA`, `atomSB` are explicit, defined
in `Submission/Work/Asymptotics/TwistOddBlocks.lean`: `atomSA i` is `(1-z)T⁻¹S` for `i = 1`,
`-(1-z)T⁻¹` for `i = 5` and zero otherwise; `atomSB i` is `-(1-z)T⁻¹` for `i = 2`,
`(1-z)T⁻¹S` for `i = 4` and zero otherwise).

Here `twist γ i = (1 - Rneg) * rowDiffOdd γ i` and
`carryCombOdd a b = (R_T - 1)^2 * a + R_S * (R_T - 1)^2 * b`, both defined in
`Submission/Work/Asymptotics/TwistOddDefs.lean`; `σ(S) = oddMS` by `sigmaHom_eq_SigmaOdd`
followed by `Sigma_ofSL` and `oddRep_S`.

The proof expands `rowDiffOdd S i = MpElem i * R_S - ∑ j, σ(S)_{ij} • MpElem j` with
`MpElem = (1, T⁻¹, STS, S, ST⁻¹, TS)`, and uses `R_S * R_S = Rneg`,
`(R_T - 1)^2 * R_Tinv = R_T - 2 + R_Tinv` and the centrality of `1 - Rneg`. -/
theorem twist_atomS_odd :
    (∀ i : Fin 6, carryCombOdd (atomSA i) (atomSB i) = twist ModularGroup.S i) ∧
    (∀ i : Fin 6, coeffNorm (atomSA i) ≤ 4 ∧ coeffNorm (atomSB i) ≤ 4 ∧
      supportFrobLe (atomSA i) 8 ∧ supportFrobLe (atomSB i) 8) := by
  constructor
  · intro i
    rw [show twist ModularGroup.S i = (1 - Rneg) * rowDiffOdd ModularGroup.S i from rfl,
      ← atomS_spec i, twist_mul_carryCombO_S, atomSA_eq i, atomSB_eq i]
  · intro i
    have h1 : coeffNorm ((1 - Rneg) * (atomS i).1) ≤ 4 := by
      calc coeffNorm ((1 - Rneg) * (atomS i).1) ≤ 2 * coeffNorm (atomS i).1 :=
            coeffNorm_one_sub_Rneg_mul_S _
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (cN_atomS_fst i) (by norm_num)
        _ ≤ 4 := by norm_num
    have h2 : coeffNorm ((1 - Rneg) * (atomS i).2.1) ≤ 4 := by
      calc coeffNorm ((1 - Rneg) * (atomS i).2.1) ≤ 2 * coeffNorm (atomS i).2.1 :=
            coeffNorm_one_sub_Rneg_mul_S _
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (cN_atomS_snd i) (by norm_num)
        _ ≤ 4 := by norm_num
    exact ⟨by rw [atomSA_eq i]; exact h1, by rw [atomSB_eq i]; exact h2,
      by rw [atomSA_eq i]; exact supportFrobLe_one_sub_Rneg_mul_S (sF_atomS_fst i),
      by rw [atomSB_eq i]; exact supportFrobLe_one_sub_Rneg_mul_S (sF_atomS_snd i)⟩

end Work.Asymptotics
