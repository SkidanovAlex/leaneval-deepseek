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

private lemma one_sub_Rneg_comm (x : R) : (1 - Rneg) * x = x * (1 - Rneg) := by
  rw [sub_mul, one_mul, mul_sub, mul_one, Work.Residues.Rneg_comm x]

private lemma one_sub_Rneg_mul_Rneg_add_one : (1 - Rneg) * (Rneg + 1) = 0 := by
  have h : Rneg * Rneg = (1 : R) := Work.Residues.Rneg_mul_Rneg
  calc (1 - Rneg) * (Rneg + 1)
      = (1 - Rneg) * Rneg + (1 - Rneg) * 1 := by rw [mul_add]
    _ = (Rneg - Rneg * Rneg) + (1 - Rneg) := by rw [sub_mul, one_mul, mul_one]
    _ = 0 := by rw [h]; noncomm_ring

/-- Twisting the three-generator combination `carryCombO a b c` by `1 - z` kills the third
generator and produces the two-generator combination `carryCombOdd` of the twisted carries. -/
private lemma twist_mul_carryCombO (a b c : R) :
    (1 - Rneg) * carryCombO a b c
      = carryCombOdd ((1 - Rneg) * a) ((1 - Rneg) * b) := by
  have h1 : (1 - Rneg) * ((R_T - 1) ^ 2 * a) = (R_T - 1) ^ 2 * ((1 - Rneg) * a) := by
    rw [← mul_assoc, one_sub_Rneg_comm, mul_assoc]
  have h2 : (1 - Rneg) * (R_S * (R_T - 1) ^ 2 * b)
      = R_S * (R_T - 1) ^ 2 * ((1 - Rneg) * b) := by
    rw [← mul_assoc, one_sub_Rneg_comm, mul_assoc]
  have h3 : (1 - Rneg) * ((Rneg + 1) * c) = 0 := by
    rw [← mul_assoc, one_sub_Rneg_mul_Rneg_add_one, zero_mul]
  simp only [carryCombO, carryCombOdd]
  rw [mul_add, mul_add, h1, h2, h3, add_zero]

/-! ## The two components of the twisted carry of the atom `T` -/

private lemma atomTA_eq (i : Fin 6) : atomTA i = (1 - Rneg) * (atomT i).1 := by
  fin_cases i <;> simp only [atomTA, atomT]
  · rw [if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring

private lemma atomTB_eq (i : Fin 6) : atomTB i = (1 - Rneg) * (atomT i).2.1 := by
  fin_cases i <;> simp only [atomTB, atomT]
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_pos (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_neg (by decide)] <;> first | rfl | noncomm_ring
  · rw [if_neg (by decide), if_pos (by decide)] <;> first | rfl | noncomm_ring

/-! ## The `ℓ¹`-norms of the atom components -/

private lemma cN_Tinv_1 : coeffNorm (R_Tinv : R) ≤ 1 := coeffNorm_of_le (ModularGroup.T)⁻¹

private lemma cN_Tinv_RS_1 : coeffNorm (R_Tinv * R_S : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le R_Tinv ModularGroup.S) cN_Tinv_1

private lemma cN_neg_Tinv_RS_1 : coeffNorm (-(R_Tinv * R_S) : R) ≤ 1 :=
  le_trans (coeffNorm_neg_le _) cN_Tinv_RS_1

private lemma cN_zero_1 : coeffNorm (0 : R) ≤ 1 := by
  rw [coeffNorm_zero]; norm_num

private lemma cN_atomT_fst (i : Fin 6) : coeffNorm (atomT i).1 ≤ 1 := by
  fin_cases i <;> simp only [atomT] <;>
    first
      | exact cN_Tinv_1 | exact cN_zero_1 | exact cN_Tinv_RS_1

private lemma cN_atomT_snd (i : Fin 6) : coeffNorm (atomT i).2.1 ≤ 1 := by
  fin_cases i <;> simp only [atomT] <;>
    first
      | exact cN_Tinv_1 | exact cN_zero_1 | exact cN_neg_Tinv_RS_1

/-! ## The Frobenius support bounds of the atom components -/

private lemma Frob_Tinv_eq : Frob ((ModularGroup.T)⁻¹ : SL(2,ℤ)) = Real.sqrt 3 := by
  rw [← _root_.zpow_neg_one (ModularGroup.T), Frob_T_zpow]
  norm_num

private lemma sF_Tinv_4 : supportFrobLe (R_Tinv : R) 4 :=
  supportFrobLe_mono (supportFrobLe_of_le (ModularGroup.T)⁻¹) (by
    rw [Frob_Tinv_eq]
    nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3])

private lemma sF_Tinv_RS_4 : supportFrobLe (R_Tinv * R_S : R) 4 := by
  have h : supportFrobLe (R_Tinv : R) (Real.sqrt 3) :=
    supportFrobLe_mono (supportFrobLe_of_le (ModularGroup.T)⁻¹) (le_of_eq Frob_Tinv_eq)
  have h2 : supportFrobLe (R_Tinv * R_S : R) (Real.sqrt 3 * Frob ModularGroup.S) :=
    supportFrobLe_mul_of h ModularGroup.S
  refine supportFrobLe_mono h2 ?_
  rw [Frob_S]
  exact sqrt_mul_sqrt_le 3 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma sF_neg_Tinv_RS_4 : supportFrobLe (-(R_Tinv * R_S) : R) 4 :=
  supportFrobLe_neg sF_Tinv_RS_4

private lemma sF_zero_4 : supportFrobLe (0 : R) 4 := supportFrobLe_zero 4

private lemma sF_atomT_fst (i : Fin 6) : supportFrobLe (atomT i).1 4 := by
  fin_cases i <;> simp only [atomT] <;>
    first
      | exact sF_Tinv_4 | exact sF_zero_4 | exact sF_Tinv_RS_4

private lemma sF_atomT_snd (i : Fin 6) : supportFrobLe (atomT i).2.1 4 := by
  fin_cases i <;> simp only [atomT] <;>
    first
      | exact sF_Tinv_4 | exact sF_zero_4 | exact sF_neg_Tinv_RS_4

/-! ## Twisting a single component -/

/-- Twisting by `1 - z` at most doubles the `ℓ¹`-norm. -/
private lemma coeffNorm_one_sub_Rneg_mul (x : R) :
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
private lemma supportFrobLe_one_sub_Rneg_mul {x : R} (hx : supportFrobLe x 4) :
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

/-- The twisted carries of the atom `T` (the two components `atomTA`, `atomTB` are explicit,
defined in `Submission/Work/Asymptotics/TwistOddBlocks.lean` as differences of group
monomials: `atomTA i` is `(1-z)T⁻¹` for `i = 0`, `(1-z)T⁻¹S` for `i = 2` and zero otherwise;
`atomTB i` is `(1-z)T⁻¹` for `i = 3`, `-(1-z)T⁻¹S` for `i = 5` and zero otherwise).

Here `twist γ i = (1 - Rneg) * rowDiffOdd γ i` and
`carryCombOdd a b = (R_T - 1)^2 * a + R_S * (R_T - 1)^2 * b`, both defined in
`Submission/Work/Asymptotics/TwistOddDefs.lean`.

The proof expands `rowDiffOdd T i = MpElem i * R_T - ∑ j, σ(T)_{ij} • MpElem j` with
`σ(T)_{ij} = oddMT i j` (`sigmaHom_eq_SigmaOdd` followed by `Sigma_ofSL` and `oddRep_T`), uses
`MpElem = (1, T⁻¹, STS, S, ST⁻¹, TS)` and the group-ring identities
`(R_T - 1)^2 * R_Tinv = R_T - 2 + R_Tinv`, `(S*T)^2 = T⁻¹*S`, `T*S*T = -(S*T⁻¹*S)` (the last
two `by decide` as elements of `SL(2,ℤ)`), and the centrality of `1 - Rneg`. -/
theorem twist_atomT_odd :
    (∀ i : Fin 6, carryCombOdd (atomTA i) (atomTB i) = twist ModularGroup.T i) ∧
    (∀ i : Fin 6, coeffNorm (atomTA i) ≤ 4 ∧ coeffNorm (atomTB i) ≤ 4 ∧
      supportFrobLe (atomTA i) 8 ∧ supportFrobLe (atomTB i) 8) := by
  constructor
  · intro i
    rw [show twist ModularGroup.T i = (1 - Rneg) * rowDiffOdd ModularGroup.T i from rfl,
      ← atomT_spec i, twist_mul_carryCombO, atomTA_eq i, atomTB_eq i]
  · intro i
    have h1 : coeffNorm ((1 - Rneg) * (atomT i).1) ≤ 4 := by
      calc coeffNorm ((1 - Rneg) * (atomT i).1) ≤ 2 * coeffNorm (atomT i).1 :=
            coeffNorm_one_sub_Rneg_mul _
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (cN_atomT_fst i) (by norm_num)
        _ ≤ 4 := by norm_num
    have h2 : coeffNorm ((1 - Rneg) * (atomT i).2.1) ≤ 4 := by
      calc coeffNorm ((1 - Rneg) * (atomT i).2.1) ≤ 2 * coeffNorm (atomT i).2.1 :=
            coeffNorm_one_sub_Rneg_mul _
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (cN_atomT_snd i) (by norm_num)
        _ ≤ 4 := by norm_num
    exact ⟨by rw [atomTA_eq i]; exact h1, by rw [atomTB_eq i]; exact h2,
      by rw [atomTA_eq i]; exact supportFrobLe_one_sub_Rneg_mul (sF_atomT_fst i),
      by rw [atomTB_eq i]; exact supportFrobLe_one_sub_Rneg_mul (sF_atomT_snd i)⟩

end Work.Asymptotics
