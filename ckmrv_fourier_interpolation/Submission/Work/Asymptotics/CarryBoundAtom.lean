/-
# Explicit carries for the atoms `T`, `S`

The reduction of `γ ∈ SL(2,ℤ)` modulo `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` is built from the
explicit computations `rowDiff R_T i` and `rowDiff R_S i` (`Submission.Work.Residues.rowDiff_R_T_mem`,
`...IdealImDefs.rowDiff_R_S_mem`).  This file packages them as the *atom carries*

* `carryAtomT i`, `carryAtomS i` : triples `(a,b,c)` of group-algebra elements with
  `(T-I)²a + S(T-I)²b + (z-1)c = rowDiff (of μ) i` for `μ = T`, `μ = S` and every row `i`,

together with the uniform bound `CB _ 1 100`: each component has `ℓ¹`-norm at most `1` and
support Frobenius norm at most `100`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryBoundDefs

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues

private lemma monomial_mul (g h : SL(2,ℤ)) :
    (MonoidAlgebra.single g (1 : ℂ) : R) * MonoidAlgebra.single h (1 : ℂ)
      = MonoidAlgebra.single (g * h) (1 : ℂ) := by
  rw [MonoidAlgebra.single_mul_single]; simp

private lemma two_smul_one_eq : (2 : ℂ) • (1 : R) = (2 : R) :=
  (Algebra.algebraMap_eq_smul_one (2 : ℂ)).symm

private lemma Rneg_smul_mul (A B X : R) : Rneg * (A * B * X) = A * B * (Rneg * X) := by
  rw [Rneg_comm (A * B * X), mul_assoc, Rneg_comm X]

private lemma rowDiff_aux2a :
    R_S * (R_T - 1)^2 * (R_S * R_T * R_S * R_T)
      = R_S * R_T * R_S - 2 * Rneg + Rneg * (R_T * R_S * R_T) := by
  rw [show (R_T - 1)^2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
  rw [show R_S * (R_T * R_T - 2 * R_T + 1) * (R_S * R_T * R_S * R_T)
      = R_S * (R_T * (R_T * R_S * R_T * R_S * R_T))
        - 2 * (R_S * (R_T * R_S * R_T * R_S * R_T))
        + (R_S * R_S) * (R_T * R_S * R_T) by noncomm_ring]
  rw [Work.Residues.R_TSTST, Work.Residues.R_S_mul_R_S_eq]
  noncomm_ring

private lemma rowDiff_aux2b :
    R_S * (R_T - 1)^2 * (Rneg * (R_S * R_T * R_S * R_T))
      = Rneg * (R_S * R_T * R_S) - 2 + R_T * R_S * R_T := by
  rw [← Rneg_smul_mul R_S ((R_T - 1)^2) (R_S * R_T * R_S * R_T)]
  rw [rowDiff_aux2a]
  rw [show Rneg * (R_S * R_T * R_S - 2 * Rneg + Rneg * (R_T * R_S * R_T))
      = Rneg * (R_S * R_T * R_S) - 2 * (Rneg * Rneg) + (Rneg * Rneg) * (R_T * R_S * R_T)
      by noncomm_ring]
  rw [Work.Residues.Rneg_mul_Rneg]
  simp

private lemma rowDiff_aux5 :
    R_S * R_T * R_S * R_T + R_T * R_S - 2 * R_S
      = (R_T - 1)^2 * (R_S * R_T * R_S * R_T) := by
  rw [show (R_T - 1)^2 = R_T * R_T - 2 * R_T + 1 by noncomm_ring]
  rw [show (R_T * R_T - 2 * R_T + 1) * (R_S * R_T * R_S * R_T)
      = R_T * (R_T * R_S * R_T * R_S * R_T) - 2 * (R_T * R_S * R_T * R_S * R_T)
        + (R_S * R_T * R_S * R_T) by noncomm_ring]
  rw [Work.Residues.R_TSTST]
  noncomm_ring

/-! ## The row values -/

private lemma rowDiff_of_T_0 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 0 = 0 := by
  rw [rowDiff_T_zero]

private lemma rowDiff_of_T_1 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 1 = (R_T - 1)^2 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T = R_T from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_T]
  show Work.Residues.M6 1 * R_T - ∑ j, Work.Modular.sigmaT 1 j • Work.Residues.M6 j = _
  simp [Work.Residues.M6, Work.Modular.sigmaT, Fin.sum_univ_six, two_smul]
  rw [← monomial_mul ModularGroup.T ModularGroup.T]
  noncomm_ring

private lemma rowDiff_of_T_2 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 2
      = R_S * (R_T - 1)^2 * (Rneg * (R_S * R_T * R_S * R_T))
        + (Rneg - 1) * (-(R_S * R_T * R_S)) := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T = R_T from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_T]
  have hL : Work.Residues.M6 2 * R_T - ∑ j, Work.Modular.sigmaT 2 j • Work.Residues.M6 j
      = R_T * R_S * R_T - 2 + R_S * R_T * R_S := by
    simp [Work.Residues.M6, Work.Modular.sigmaT, Fin.sum_univ_six]
    rw [two_smul_one_eq]
    noncomm_ring
  rw [hL, rowDiff_aux2b]
  noncomm_ring

private lemma rowDiff_of_T_3 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 3 = 0 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T = R_T from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_T]
  simp [Work.Residues.M6, Work.Modular.sigmaT, Fin.sum_univ_six]

private lemma rowDiff_of_T_4 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 4
      = R_S * (R_T - 1)^2 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T = R_T from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_T]
  show Work.Residues.M6 4 * R_T - ∑ j, Work.Modular.sigmaT 4 j • Work.Residues.M6 j = _
  simp [Work.Residues.M6, Work.Modular.sigmaT, Fin.sum_univ_six, two_smul]
  rw [← monomial_mul (ModularGroup.S * ModularGroup.T) ModularGroup.T,
    ← monomial_mul ModularGroup.S ModularGroup.T]
  noncomm_ring

private lemma rowDiff_of_T_5 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) 5
      = (R_T - 1)^2 * (R_S * R_T * R_S * R_T) := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T = R_T from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_T]
  have hL : Work.Residues.M6 5 * R_T - ∑ j, Work.Modular.sigmaT 5 j • Work.Residues.M6 j
      = R_S * R_T * R_S * R_T + R_T * R_S - 2 * R_S := by
    simp [Work.Residues.M6, Work.Modular.sigmaT, Fin.sum_univ_six, two_smul]
    noncomm_ring
  rw [hL, rowDiff_aux5]

private lemma rowDiff_of_S_0 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 0 = 0 :=
  rowDiff_S_zero

private lemma rowDiff_of_S_1 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 1 = 0 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S = R_S from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_S]
  simp [Work.Residues.M6, Work.Modular.sigmaS, Fin.sum_univ_six, mul_assoc]

private lemma rowDiff_of_S_2 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 2
      = (Rneg - 1) * R_T := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S = R_S from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_S]
  have hsum : (∑ j, Work.Modular.sigmaS 2 j • Work.Residues.M6 j : R) = R_T := by
    simp [Work.Residues.M6, Work.Modular.sigmaS, Fin.sum_univ_six]
  rw [hsum]
  have heq : Work.Residues.M6 2 * R_S - R_T = R_T * (Rneg - 1) := by
    show (R_T * R_S) * R_S - R_T = R_T * (Rneg - 1)
    rw [mul_assoc, Work.Residues.R_S_mul_R_S_eq, mul_sub, mul_one]
  rw [heq, mul_Rneg_sub_one_comm']

private lemma rowDiff_of_S_3 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 3
      = Rneg - 1 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S = R_S from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_S]
  have hsum : (∑ j, Work.Modular.sigmaS 3 j • Work.Residues.M6 j : R) = 1 := by
    simp [Work.Residues.M6, Work.Modular.sigmaS, Fin.sum_univ_six]
  rw [hsum]
  have heq : Work.Residues.M6 3 * R_S - 1 = Rneg - 1 := by
    show R_S * R_S - 1 = Rneg - 1
    rw [Work.Residues.R_S_mul_R_S_eq]
  exact heq

private lemma rowDiff_of_S_4 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 4 = 0 := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S = R_S from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_S]
  simp [Work.Residues.M6, Work.Modular.sigmaS, Fin.sum_univ_six, mul_assoc]

private lemma rowDiff_of_S_5 :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) 5
      = (Rneg - 1) * (R_S * R_T) := by
  rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S = R_S from rfl,
    Work.Residues.rowDiff, Work.Residues.sigmaR_R_S]
  have hsum : (∑ j, Work.Modular.sigmaS 5 j • Work.Residues.M6 j : R) = R_S * R_T := by
    simp [Work.Residues.M6, Work.Modular.sigmaS, Fin.sum_univ_six]
  rw [hsum]
  have heq : Work.Residues.M6 5 * R_S - R_S * R_T = (R_S * R_T) * (Rneg - 1) := by
    show (R_S * R_T * R_S) * R_S - R_S * R_T = (R_S * R_T) * (Rneg - 1)
    rw [mul_assoc, Work.Residues.R_S_mul_R_S_eq, mul_sub, mul_one]
  rw [heq, mul_Rneg_sub_one_comm']

/-! ## The atom carries and their defining equations -/

/-- The carry of the atom `T` in each of the six rows. -/
noncomputable def carryAtomT : Fin 6 → R × R × R := fun i =>
  if i = 1 then (1, 0, 0)
  else if i = 2 then
    (0, Work.Residues.Rneg * (R_S * R_T * R_S * R_T), -(R_S * R_T * R_S))
  else if i = 4 then (0, 1, 0)
  else if i = 5 then (R_S * R_T * R_S * R_T, 0, 0)
  else (0, 0, 0)

/-- The carry of the atom `S` in each of the six rows. -/
noncomputable def carryAtomS : Fin 6 → R × R × R := fun i =>
  if i = 2 then (0, 0, R_T)
  else if i = 3 then (0, 0, 1)
  else if i = 5 then (0, 0, R_S * R_T)
  else (0, 0, 0)

theorem carryAtomT_spec (i : Fin 6) :
    carryComb (carryAtomT i).1 (carryAtomT i).2.1 (carryAtomT i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) i := by
  fin_cases i
  · show carryComb (carryAtomT (0 : Fin 6)).1 (carryAtomT (0 : Fin 6)).2.1
        (carryAtomT (0 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (0 : Fin 6)
    rw [rowDiff_of_T_0]
    simp [carryAtomT, carryComb]
  · show carryComb (carryAtomT (1 : Fin 6)).1 (carryAtomT (1 : Fin 6)).2.1
        (carryAtomT (1 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (1 : Fin 6)
    rw [rowDiff_of_T_1]
    simp [carryAtomT, carryComb]
  · show carryComb (carryAtomT (2 : Fin 6)).1 (carryAtomT (2 : Fin 6)).2.1
        (carryAtomT (2 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (2 : Fin 6)
    rw [rowDiff_of_T_2]
    simp [carryAtomT, carryComb]
  · show carryComb (carryAtomT (3 : Fin 6)).1 (carryAtomT (3 : Fin 6)).2.1
        (carryAtomT (3 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (3 : Fin 6)
    rw [rowDiff_of_T_3]
    simp [carryAtomT, carryComb]
  · show carryComb (carryAtomT (4 : Fin 6)).1 (carryAtomT (4 : Fin 6)).2.1
        (carryAtomT (4 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (4 : Fin 6)
    rw [rowDiff_of_T_4]
    simp [carryAtomT, carryComb]
  · show carryComb (carryAtomT (5 : Fin 6)).1 (carryAtomT (5 : Fin 6)).2.1
        (carryAtomT (5 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.T) (5 : Fin 6)
    rw [rowDiff_of_T_5]
    simp [carryAtomT, carryComb]

theorem carryAtomS_spec (i : Fin 6) :
    carryComb (carryAtomS i).1 (carryAtomS i).2.1 (carryAtomS i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) i := by
  fin_cases i
  · show carryComb (carryAtomS (0 : Fin 6)).1 (carryAtomS (0 : Fin 6)).2.1
        (carryAtomS (0 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (0 : Fin 6)
    rw [rowDiff_of_S_0]
    simp [carryAtomS, carryComb]
  · show carryComb (carryAtomS (1 : Fin 6)).1 (carryAtomS (1 : Fin 6)).2.1
        (carryAtomS (1 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (1 : Fin 6)
    rw [rowDiff_of_S_1]
    simp [carryAtomS, carryComb]
  · show carryComb (carryAtomS (2 : Fin 6)).1 (carryAtomS (2 : Fin 6)).2.1
        (carryAtomS (2 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (2 : Fin 6)
    rw [rowDiff_of_S_2]
    simp [carryAtomS, carryComb]
  · show carryComb (carryAtomS (3 : Fin 6)).1 (carryAtomS (3 : Fin 6)).2.1
        (carryAtomS (3 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (3 : Fin 6)
    rw [rowDiff_of_S_3]
    simp [carryAtomS, carryComb]
  · show carryComb (carryAtomS (4 : Fin 6)).1 (carryAtomS (4 : Fin 6)).2.1
        (carryAtomS (4 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (4 : Fin 6)
    rw [rowDiff_of_S_4]
    simp [carryAtomS, carryComb]
  · show carryComb (carryAtomS (5 : Fin 6)).1 (carryAtomS (5 : Fin 6)).2.1
        (carryAtomS (5 : Fin 6)).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) ModularGroup.S) (5 : Fin 6)
    rw [rowDiff_of_S_5]
    simp [carryAtomS, carryComb]


/-! ## The `ℓ¹`/support bounds for the atom carries -/

lemma coeffNorm_neg_le (x : R) : coeffNorm (-x) ≤ coeffNorm x := by
  have hx : -x = (-1 : ℂ) • x := by simp
  rw [hx]
  simpa using coeffNorm_smul_le (-1) x

lemma supportFrobLe_neg {x : R} {K : ℝ} (h : supportFrobLe x K) : supportFrobLe (-x) K := by
  have hx : -x = (-1 : ℂ) • x := by simp
  rw [hx]
  exact supportFrobLe_smul (-1) h

/-- Left multiplication by a group element does not increase `coeffNorm`. -/
lemma coeffNorm_of_mul_le (g : SL(2,ℤ)) (x : R) :
    coeffNorm (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x) ≤ coeffNorm x := by
  classical
  have hcoeff : ∀ h : SL(2,ℤ),
      (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff h = x.coeff (g⁻¹ * h) := by
    intro h
    conv_lhs => rw [MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_apply]
    simp
  have hsupp : ∀ h ∈ (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff.support,
      g⁻¹ * h ∈ x.coeff.support := by
    intro h hh
    rw [Finsupp.mem_support_iff] at hh ⊢
    rw [hcoeff h] at hh
    exact hh
  have hinj : Set.InjOn (fun h : SL(2,ℤ) => g⁻¹ * h)
      ↑(MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff.support :=
    fun a _ b _ hab => mul_left_cancel hab
  have h1 : coeffNorm (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x)
      = ∑ h ∈ (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff.support, ‖x.coeff (g⁻¹ * h)‖ := by
    simp only [coeffNorm]
    exact Finset.sum_congr rfl fun h _ => by rw [hcoeff h]
  have h2 : ∑ k ∈ ((MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff.support).image (fun h => g⁻¹ * h),
        ‖x.coeff k‖ ≤ ∑ k ∈ x.coeff.support, ‖x.coeff k‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => by obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hk; exact hsupp h hh)
      (fun _ _ _ => by positivity)
  have h3 : ∑ k ∈ ((MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff.support).image (fun h => g⁻¹ * h),
        ‖x.coeff k‖ = coeffNorm (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x) := by
    rw [h1, Finset.sum_image hinj]
  rw [← h3, coeffNorm]
  exact h2

/-- Left multiplication by a group element scales the support bound by `Frob g`. -/
lemma supportFrobLe_of_mul_le {x : R} {K : ℝ} (g : SL(2,ℤ)) (h : supportFrobLe x K) :
    supportFrobLe (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x) (Frob g * K) := by
  classical
  have hcoeff : ∀ h : SL(2,ℤ),
      (MonoidAlgebra.of ℂ (SL(2,ℤ)) g * x).coeff h = x.coeff (g⁻¹ * h) := by
    intro h
    conv_lhs => rw [MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.single_mul_apply]
    simp
  intro h0 hh
  rw [Finsupp.mem_support_iff, hcoeff] at hh
  have hk : g⁻¹ * h0 ∈ x.coeff.support := by rwa [Finsupp.mem_support_iff]
  have heq : h0 = g * (g⁻¹ * h0) := by rw [mul_inv_cancel_left]
  rw [heq]
  exact le_trans (Frob_mul_le g _) (mul_le_mul_of_nonneg_left (h _ hk) (Frob_nonneg g))

lemma Frob_one : Frob (1 : SL(2,ℤ)) = Real.sqrt 2 := by
  rw [show (1 : SL(2,ℤ)) = ModularGroup.T ^ (0 : ℤ) from (zpow_zero _).symm, Frob_T_zpow]
  congr 1
  push_cast
  norm_num

/-- A monomial has support in a single group element. -/
lemma supportFrobLe_of_le (g : SL(2,ℤ)) :
    supportFrobLe (MonoidAlgebra.of ℂ (SL(2,ℤ)) g) (Frob g) := by
  intro γ hγ
  have hcoeff : (MonoidAlgebra.of ℂ (SL(2,ℤ)) g).coeff = Finsupp.single g (1 : ℂ) := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  rw [hcoeff, Finsupp.mem_support_iff] at hγ
  have hγg : γ = g := by
    by_contra h
    exact hγ (by simp [h])
  rw [hγg]

/-- `√a · √b ≤ c` whenever `a b ≤ c ^ 2` and `a, b, c ≥ 0`. -/
lemma sqrt_mul_sqrt_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b ≤ c ^ 2) : Real.sqrt a * Real.sqrt b ≤ c := by
  rw [← Real.sqrt_mul ha]
  exact Real.sqrt_le_iff.mpr ⟨hc, h⟩

lemma sq_sqrt_two : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

lemma sq_sqrt_three : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)

private lemma cN_of (g : SL(2,ℤ)) : coeffNorm (MonoidAlgebra.of ℂ (SL(2,ℤ)) g) ≤ 1 :=
  coeffNorm_of_le g

private lemma cN_zero : coeffNorm (0 : R) ≤ 1 := by rw [coeffNorm_zero]; norm_num

private lemma cN_RS : coeffNorm (R_S : R) ≤ 1 := cN_of ModularGroup.S

private lemma cN_RT : coeffNorm (R_T : R) ≤ 1 := cN_of ModularGroup.T

private lemma cN_one : coeffNorm (1 : R) ≤ 1 := cN_of 1

private lemma cN_STS : coeffNorm (R_S * R_T * R_S : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le (R_S * R_T) ModularGroup.S)
    (le_trans (coeffNorm_mul_of_le R_S ModularGroup.T) cN_RS)

private lemma cN_STST : coeffNorm (R_S * R_T * R_S * R_T : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le (R_S * R_T * R_S) ModularGroup.T) cN_STS

private lemma cN_RS_RT : coeffNorm (R_S * R_T : R) ≤ 1 :=
  le_trans (coeffNorm_mul_of_le R_S ModularGroup.T) cN_RS

private lemma cN_Rneg_STST :
    coeffNorm (Work.Residues.Rneg * (R_S * R_T * R_S * R_T) : R) ≤ 1 :=
  le_trans (coeffNorm_of_mul_le (-1 : SL(2,ℤ)) _) cN_STST

private lemma cN_neg_STS : coeffNorm (-(R_S * R_T * R_S) : R) ≤ 1 :=
  le_trans (coeffNorm_neg_le _) cN_STS

private lemma sF_RS : supportFrobLe (R_S : R) (Real.sqrt 2) := by
  refine supportFrobLe_mono (supportFrobLe_of_le ModularGroup.S) ?_
  rw [Frob_S]

private lemma sF_RT : supportFrobLe (R_T : R) (Real.sqrt 3) := by
  refine supportFrobLe_mono (supportFrobLe_of_le ModularGroup.T) ?_
  rw [Frob_T]

private lemma sF_of_one : supportFrobLe (1 : R) (Real.sqrt 2) := by
  refine supportFrobLe_mono (supportFrobLe_of_le 1) ?_
  rw [Frob_one]

private lemma sF_one : supportFrobLe (1 : R) 100 :=
  supportFrobLe_mono sF_of_one (by nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2])

private lemma sF_RT' : supportFrobLe (R_T : R) 100 :=
  supportFrobLe_mono sF_RT (by nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3])

private lemma sF_RS_RT : supportFrobLe (R_S * R_T : R) (Real.sqrt 2 * Real.sqrt 3) := by
  have h := supportFrobLe_mul_of sF_RS ModularGroup.T
  refine supportFrobLe_mono h ?_
  rw [Frob_T]

private lemma sF_RS_RT_100 : supportFrobLe (R_S * R_T : R) 100 :=
  supportFrobLe_mono sF_RS_RT (by
    nlinarith [sq_sqrt_two, sq_sqrt_three, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3])

private lemma sF_STS : supportFrobLe (R_S * R_T * R_S : R)
    (Real.sqrt 2 * Real.sqrt 3 * Real.sqrt 2) := by
  have h := supportFrobLe_mul_of (supportFrobLe_mul_of sF_RS ModularGroup.T) ModularGroup.S
  refine supportFrobLe_mono h ?_
  rw [Frob_S, Frob_T]

private lemma sF_STS_100 : supportFrobLe (R_S * R_T * R_S : R) 100 :=
  supportFrobLe_mono sF_STS (by
    nlinarith [sq_sqrt_two, sq_sqrt_three, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3])

private lemma sF_STST : supportFrobLe (R_S * R_T * R_S * R_T : R)
    (Real.sqrt 2 * Real.sqrt 3 * Real.sqrt 2 * Real.sqrt 3) := by
  have h := supportFrobLe_mul_of
    (supportFrobLe_mul_of (supportFrobLe_mul_of sF_RS ModularGroup.T) ModularGroup.S)
    ModularGroup.T
  refine supportFrobLe_mono h ?_
  rw [Frob_S, Frob_T]

private lemma sF_STST_100 : supportFrobLe (R_S * R_T * R_S * R_T : R) 100 :=
  supportFrobLe_mono sF_STST (by
    nlinarith [sq_sqrt_two, sq_sqrt_three, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3])

private lemma sF_Rneg_STST :
    supportFrobLe (Work.Residues.Rneg * (R_S * R_T * R_S * R_T) : R) 100 := by
  have h := supportFrobLe_of_mul_le (-1 : SL(2,ℤ)) sF_STST
  refine supportFrobLe_mono h ?_
  rw [Frob_neg_one]
  have hA : Real.sqrt 2 * Real.sqrt 3 ≤ (4 : ℝ) :=
    sqrt_mul_sqrt_le 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB : Real.sqrt 2 ≤ (4 : ℝ) := by nlinarith [sq_sqrt_two, Real.sqrt_nonneg 2]
  have hC : Real.sqrt 3 ≤ (4 : ℝ) := by nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3]
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt 3 := by positivity
  calc Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt 3 * Real.sqrt 2 * Real.sqrt 3)
      = Real.sqrt 2 * ((Real.sqrt 2 * Real.sqrt 3) * (Real.sqrt 2 * Real.sqrt 3)) := by ring
    _ ≤ 4 * (4 * 4) := mul_le_mul hB (mul_le_mul hA hA h0 (by norm_num)) (by positivity)
        (by norm_num)
    _ ≤ 100 := by norm_num

private lemma sF_neg_STS : supportFrobLe (-(R_S * R_T * R_S) : R) 100 :=
  supportFrobLe_mono (supportFrobLe_neg sF_STS) (by
    nlinarith [sq_sqrt_two, sq_sqrt_three, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3])

private lemma CB_zeroT : CB ((0, 0, 0) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_zero, cN_zero, supportFrobLe_zero 100, supportFrobLe_zero 100,
    supportFrobLe_zero 100⟩

private lemma CB_one_r : CB ((1, 0, 0) : R × R × R) 1 100 :=
  ⟨cN_one, cN_zero, cN_zero, sF_one, supportFrobLe_zero 100, supportFrobLe_zero 100⟩

private lemma CB_one_mid : CB ((0, 1, 0) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_one, cN_zero, supportFrobLe_zero 100, sF_one, supportFrobLe_zero 100⟩

private lemma CB_P2 :
    CB ((0, Work.Residues.Rneg * (R_S * R_T * R_S * R_T), -(R_S * R_T * R_S)) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_Rneg_STST, cN_neg_STS, supportFrobLe_zero 100, sF_Rneg_STST, sF_neg_STS⟩

private lemma CB_STST : CB ((R_S * R_T * R_S * R_T, 0, 0) : R × R × R) 1 100 :=
  ⟨cN_STST, cN_zero, cN_zero, sF_STST_100, supportFrobLe_zero 100, supportFrobLe_zero 100⟩

private lemma CB_S_RT : CB ((0, 0, R_T) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_zero, cN_RT, supportFrobLe_zero 100, supportFrobLe_zero 100, sF_RT'⟩

private lemma CB_S_one : CB ((0, 0, 1) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_zero, cN_one, supportFrobLe_zero 100, supportFrobLe_zero 100, sF_one⟩

private lemma CB_S_RSRT : CB ((0, 0, R_S * R_T) : R × R × R) 1 100 :=
  ⟨cN_zero, cN_zero, cN_RS_RT, supportFrobLe_zero 100, supportFrobLe_zero 100, sF_RS_RT_100⟩

theorem carryAtomT_bound (i : Fin 6) : CB (carryAtomT i) 1 100 := by
  fin_cases i
  · show CB (carryAtomT (0 : Fin 6)) 1 100
    rw [show carryAtomT (0 : Fin 6) = ((0, 0, 0) : R × R × R) from by simp [carryAtomT]]
    exact CB_zeroT
  · show CB (carryAtomT (1 : Fin 6)) 1 100
    rw [show carryAtomT (1 : Fin 6) = ((1, 0, 0) : R × R × R) from by simp [carryAtomT]]
    exact CB_one_r
  · show CB (carryAtomT (2 : Fin 6)) 1 100
    rw [show carryAtomT (2 : Fin 6)
        = ((0, Work.Residues.Rneg * (R_S * R_T * R_S * R_T), -(R_S * R_T * R_S)) : R × R × R) from by
      simp [carryAtomT]]
    exact CB_P2
  · show CB (carryAtomT (3 : Fin 6)) 1 100
    rw [show carryAtomT (3 : Fin 6) = ((0, 0, 0) : R × R × R) from by simp [carryAtomT]]
    exact CB_zeroT
  · show CB (carryAtomT (4 : Fin 6)) 1 100
    rw [show carryAtomT (4 : Fin 6) = ((0, 1, 0) : R × R × R) from by simp [carryAtomT]]
    exact CB_one_mid
  · show CB (carryAtomT (5 : Fin 6)) 1 100
    rw [show carryAtomT (5 : Fin 6) = ((R_S * R_T * R_S * R_T, 0, 0) : R × R × R) from by
      simp [carryAtomT]]
    exact CB_STST

theorem carryAtomS_bound (i : Fin 6) : CB (carryAtomS i) 1 100 := by
  fin_cases i
  · show CB (carryAtomS (0 : Fin 6)) 1 100
    rw [show carryAtomS (0 : Fin 6) = ((0, 0, 0) : R × R × R) from by simp [carryAtomS]]
    exact CB_zeroT
  · show CB (carryAtomS (1 : Fin 6)) 1 100
    rw [show carryAtomS (1 : Fin 6) = ((0, 0, 0) : R × R × R) from by simp [carryAtomS]]
    exact CB_zeroT
  · show CB (carryAtomS (2 : Fin 6)) 1 100
    rw [show carryAtomS (2 : Fin 6) = ((0, 0, R_T) : R × R × R) from by simp [carryAtomS]]
    exact CB_S_RT
  · show CB (carryAtomS (3 : Fin 6)) 1 100
    rw [show carryAtomS (3 : Fin 6) = ((0, 0, 1) : R × R × R) from by simp [carryAtomS]]
    exact CB_S_one
  · show CB (carryAtomS (4 : Fin 6)) 1 100
    rw [show carryAtomS (4 : Fin 6) = ((0, 0, 0) : R × R × R) from by simp [carryAtomS]]
    exact CB_zeroT
  · show CB (carryAtomS (5 : Fin 6)) 1 100
    rw [show carryAtomS (5 : Fin 6) = ((0, 0, R_S * R_T) : R × R × R) from by simp [carryAtomS]]
    exact CB_S_RSRT

end Work.Asymptotics
