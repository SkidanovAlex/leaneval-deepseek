/-
# The explicit odd-weight representation and the twisted odd carries (definitions)

Algebraic interface for the twisted odd-weight reduction used in
`Work.Asymptotics.carry_twist_odd`:

* `oddRep` is the explicit monoid homomorphism `SL(2,ℤ) →* M₆(ℂ)` with `S ↦ oddMS`,
  `T ↦ oddMT` (constructed from the classical presentation of `SL(2,ℤ)`), `SigmaOdd` its
  linear extension to the group algebra `R = ℂ[SL(2,ℤ)]`;
* `sigmaHom_eq_SigmaOdd` identifies the representation `sigmaHom` of `exists_sigma_odd` with
  `SigmaOdd ∘ ofSL`, which makes the odd reductions computable;
* `carryCombOdd` is the two-generator combination `(T-1)²a + S(T-1)²b` of the odd ideal
  (the third generator `1+z` acts by zero at odd weight, and the twist `1-z` kills it);
* `twist` is the twisted error vector `(1-z) · rowDiffOdd γ i`, which lies in
  `(T-1)²R + S(T-1)²R` and satisfies the cocycle law `twist_cocycle`, the negation law
  `twist_neg` and the inversion law `twist_inv` used to run the reduction along a word.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.OddSigmaMatrices
import Submission.Work.Asymptotics.oddSigma_matrices
import Submission.Work.Asymptotics.indep_Mp_idealIOdd
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.OddCocycle
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Asymptotics.CarryBoundBasic
import Submission.Work.GroupTheory.SL2Z_lift

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The explicit representation -/

theorem oddMS_pow_four : oddMS ^ 4 = (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  obtain ⟨hmm, -, -, -, -⟩ := oddSigma_matrices
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two oddMS, hmm]
  simp

theorem oddMS_sq_eq : oddMS ^ 2 = (oddMS * oddMT) ^ 3 := by
  obtain ⟨hmm, hcube, -, -, -⟩ := oddSigma_matrices
  rw [pow_two oddMS, hmm, hcube]

/-- The explicit odd-weight representation of `SL(2,ℤ)`: `S ↦ oddMS`, `T ↦ oddMT`, so that
`z = -I ↦ -1`. -/
def oddRep : Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix (Fin 6) (Fin 6) ℂ :=
  Classical.choose (Work.GroupTheory.SL2Z_lift oddMS oddMT oddMS_pow_four oddMS_sq_eq)

theorem oddRep_S : oddRep ModularGroup.S = oddMS :=
  (Classical.choose_spec (Work.GroupTheory.SL2Z_lift oddMS oddMT oddMS_pow_four
    oddMS_sq_eq)).1

theorem oddRep_T : oddRep ModularGroup.T = oddMT :=
  (Classical.choose_spec (Work.GroupTheory.SL2Z_lift oddMS oddMT oddMS_pow_four
    oddMS_sq_eq)).2

theorem oddRep_neg_one : oddRep (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -1 := by
  have hSS : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = ModularGroup.S * ModularGroup.S := by
    decide
  rw [hSS, map_mul, oddRep_S]
  exact oddSigma_matrices.1

/-- The linear extension of the explicit representation to the group algebra. -/
def SigmaOdd : R →ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ := Sigma oddRep

lemma SigmaOdd_ofSL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SigmaOdd (ofSL γ) = oddRep γ := Sigma_ofSL oddRep γ

lemma SigmaOdd_MpElem (i : Fin 6) : SigmaOdd (MpElem i) = oddMu i :=
  Sigma_Mp (f := oddRep) i oddRep_S oddRep_T

/-- The `0`-th row of `SigmaOdd` kills the odd ideal. -/
theorem SigmaOdd_row0_eq_zero {x : R} (hx : x ∈ idealIOdd) : (SigmaOdd x) 0 = 0 := by
  obtain ⟨hmm, -, hrow1, hrow2, -⟩ := oddSigma_matrices
  exact Sigma_idealIOdd_row0 (f := oddRep) x oddRep_S oddRep_T hx hrow1 hrow2 hmm

/-- **The representation `sigmaHom` of `exists_sigma_odd` is the explicit representation.** -/
theorem sigmaHom_eq_SigmaOdd (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    sigmaHom γ = SigmaOdd (ofSL γ) := by
  change sigmaHom γ = Sigma oddRep (ofSL γ)
  ext i j
  have hx : rowDiffOdd γ i ∈ idealIOdd := rowDiffOdd_mem_idealIOdd γ i
  obtain ⟨hmm, -, hrow1, hrow2, -⟩ := oddSigma_matrices
  have hz := Sigma_idealIOdd_row0 (f := oddRep) (rowDiffOdd γ i) oddRep_S oddRep_T hx
    hrow1 hrow2 hmm
  have hrow : ((Sigma oddRep) (rowDiffOdd γ i)) 0 j = 0 := by
    rw [hz]; rfl
  have hexp : (Sigma oddRep) (rowDiffOdd γ i)
      = (Sigma oddRep) (MpElem i) * (Sigma oddRep) (ofSL γ)
        - ∑ l : Fin 6, (sigmaHom γ) i l • (Sigma oddRep) (MpElem l) := by
    rw [rowDiffOdd, map_sub, map_mul, map_sum]
    simp only [map_smul]
  rw [hexp] at hrow
  have hmp : ∀ l : Fin 6, (Sigma oddRep) (MpElem l) = oddMu l :=
    fun l => Sigma_Mp l oddRep_S oddRep_T
  simp only [hmp] at hrow
  have hodd : ∀ l t : Fin 6, (oddMu l) 0 t = if t = l then (1 : ℂ) else 0 :=
    fun l t => oddSigma_matrices.2.2.2.2 l t
  have h1 : (oddMu i * (Sigma oddRep) (ofSL γ)) 0 j = ((Sigma oddRep) (ofSL γ)) i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hodd i i, if_pos rfl, one_mul]
    · intro b _ hb; rw [hodd i b, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h2 : (∑ l : Fin 6, (sigmaHom γ) i l • oddMu l) 0 j = (sigmaHom γ) i j := by
    rw [Matrix.sum_apply, Finset.sum_eq_single j]
    · rw [Matrix.smul_apply, smul_eq_mul, hodd j j, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Matrix.smul_apply, smul_eq_mul, hodd b j, if_neg (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  simp only [Matrix.sub_apply] at hrow
  rw [h1, h2] at hrow
  exact (sub_eq_zero.mp hrow).symm

theorem sigmaHom_neg_one :
    sigmaHom (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -1 := by
  change sigmaHom (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(1 : Matrix (Fin 6) (Fin 6) ℂ)
  rw [sigmaHom_eq_SigmaOdd]
  change Sigma oddRep (ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) = -1
  rw [Sigma_ofSL, oddRep_neg_one]

lemma sigmaHom_neg_one_apply (i j : Fin 6) :
    (sigmaHom (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) i j
      = if i = j then (-1 : ℂ) else 0 := by
  rw [sigmaHom_neg_one]
  simp only [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, neg_zero]

lemma sum_smul_neg_one (X : Fin 6 → R) (i : Fin 6) :
    (∑ j : Fin 6, (sigmaHom (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) i j • X j)
      = - X i := by
  rw [Finset.sum_eq_single i]
  · rw [sigmaHom_neg_one_apply i i, if_pos rfl]
    simp
  · intro b _ hb
    rw [sigmaHom_neg_one_apply i b, if_neg (Ne.symm hb)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

lemma sum_smul_one (X : Fin 6 → R) (i : Fin 6) :
    (∑ j : Fin 6, (sigmaHom (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) i j • X j)
      = X i := by
  rw [map_one, Finset.sum_eq_single i]
  · rw [Matrix.one_apply, if_pos rfl, one_smul]
  · intro b _ hb; rw [Matrix.one_apply, if_neg (Ne.symm hb), zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ## The twisted odd carries -/

/-- The two-generator defect combination `(T-1)²a + S(T-1)²b` of the odd ideal. -/
def carryCombOdd (a b : R) : R := (R_T - 1) ^ 2 * a + R_S * (R_T - 1) ^ 2 * b

@[simp] lemma carryCombOdd_zero : carryCombOdd 0 0 = 0 := by
  simp [carryCombOdd]

lemma carryCombOdd_add (a b a' b' : R) :
    carryCombOdd (a + a') (b + b') = carryCombOdd a b + carryCombOdd a' b' := by
  simp only [carryCombOdd]; noncomm_ring

lemma carryCombOdd_smul (c : ℂ) (a b : R) :
    carryCombOdd (c • a) (c • b) = c • carryCombOdd a b := by
  simp only [carryCombOdd, mul_smul_comm, smul_add]

lemma carryCombOdd_mul_of (a b : R) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    carryCombOdd (a * ofSL g) (b * ofSL g) = carryCombOdd a b * ofSL g := by
  simp only [carryCombOdd]; noncomm_ring

/-- The twisted error vector of the odd reduction: `(1-z)·rowDiffOdd γ i`, `z = -I`. -/
def twist (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin 6) : R :=
  (1 - Rneg) * rowDiffOdd γ i

/-- The cocycle law for the twisted error vector, inherited from `rowDiffOdd_mul`. -/
theorem twist_cocycle (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin 6) :
    twist (γ * δ) i
      = (∑ j : Fin 6, (sigmaHom γ) i j • twist δ j) + twist γ i * ofSL δ := by
  simp only [twist, rowDiffOdd_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => Algebra.mul_smul_comm _ _ _
  · rw [mul_assoc]

lemma twist_one (i : Fin 6) : twist (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) i = 0 := by
  rw [twist, rowDiffOdd, ofSL_one, mul_one]
  rw [sum_smul_one (fun j => MpElem j) i, sub_self, mul_zero]

lemma twist_neg_one (i : Fin 6) : twist (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) i = 0 := by
  rw [twist, rowDiffOdd]
  rw [show ofSL (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = Work.Residues.Rneg from rfl]
  rw [sum_smul_neg_one (fun j => MpElem j) i]
  rw [sub_neg_eq_add]
  have h1 : MpElem i * Work.Residues.Rneg + MpElem i
      = MpElem i * (Work.Residues.Rneg + 1) := by
    rw [mul_add, mul_one]
  have h2 : MpElem i * (Work.Residues.Rneg + 1)
      = (Work.Residues.Rneg + 1) * MpElem i := by
    rw [mul_add, mul_one, add_mul, one_mul, Work.Residues.Rneg_comm (MpElem i)]
  rw [h1, h2, ← mul_assoc]
  have hzero : (1 - Work.Residues.Rneg) * (Work.Residues.Rneg + 1) = 0 := by
    rw [sub_mul, one_mul, mul_add, mul_one, Work.Residues.Rneg_mul_Rneg]
    abel
  rw [hzero, zero_mul]

/-- The twisted error vector is odd. -/
theorem twist_neg (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin 6) :
    twist (-γ) i = - twist γ i := by
  have hneg : (-γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ := by rw [neg_one_mul]
  rw [hneg, twist_cocycle, twist_neg_one i, zero_mul, add_zero]
  rw [sum_smul_neg_one (fun j => twist γ j) i]

/-- The inversion law for the twisted error vector. -/
theorem twist_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin 6) :
    twist γ⁻¹ i = - (∑ j : Fin 6, (sigmaHom γ⁻¹) i j • twist γ j) * ofSL γ⁻¹ := by
  have h := twist_cocycle γ⁻¹ γ i
  rw [inv_mul_cancel, twist_one] at h
  have hB : twist γ⁻¹ i * ofSL γ
      = -(∑ j : Fin 6, (sigmaHom γ⁻¹) i j • twist γ j) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h.symm
  calc twist γ⁻¹ i
      = (twist γ⁻¹ i * ofSL γ) * ofSL γ⁻¹ := by
        rw [mul_assoc, ← ofSL_mul, mul_inv_cancel, ofSL_one, mul_one]
    _ = (-(∑ j : Fin 6, (sigmaHom γ⁻¹) i j • twist γ j)) * ofSL γ⁻¹ := by rw [hB]
    _ = - (∑ j : Fin 6, (sigmaHom γ⁻¹) i j • twist γ j) * ofSL γ⁻¹ := by rw [neg_mul]

end Work.Asymptotics
