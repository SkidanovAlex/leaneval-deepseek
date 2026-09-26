/-
# Linear independence of the six classes `Mp_i` modulo the odd defect ideal

This file proves `Work.Asymptotics.indep_Mp_idealIOdd`: the six elements
`MpElem i = single (Mp i) 1` of `R = ℂ[SL(2,ℤ)]` are linearly independent modulo the
odd-weight defect ideal

  `idealIOdd = IdealI + augIdealOdd = ((T-I)²R + S(T-I)²R) + (1+z)R`,  `z = -I`,

i.e. the classes of `1, T⁻¹, STS, S, ST⁻¹, TS` are linearly independent in `R/𝓘_odd`.

The proof follows CKMRV (proof of Proposition 3.2(1)).  One exhibits six linear functionals
on `R` which annihilate `𝓘_odd` and whose values on the six `MpElem i` form an invertible
matrix.  The functionals are the "first row" functionals of the six-dimensional "odd"
representation `σ` of `SL(2,ℤ)` given by the explicit matrices `oddMS`, `oddMT` of
`Submission.Work.Asymptotics.OddSigmaMatrices` (with `S ↦ oddMS`, `T ↦ oddMT`, `-I ↦ -1`).
Existence of that representation follows from the classical presentation
`SL(2,ℤ) = ⟨S, T | S ^ 4 = 1, S ^ 2 = (S * T) ^ 3⟩`
(`Work.GroupTheory.SL2Z_lift`), and the five matrix identities it needs are
`Work.Asymptotics.oddSigma_matrices`.

* `Sigma` is the linear extension of the representation to an algebra homomorphism
  `R →ₐ[ℂ] M₆(ℂ)`;
* `Sigma_idealIOdd_row0` : the `0`-th row of `Sigma f x` vanishes for `x ∈ 𝓘_odd`;
* `Sigma_Mp_row` : the value matrix on the six basis elements is the identity.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.OddSigmaMatrices
import Submission.Work.Asymptotics.oddSigma_matrices
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.GroupTheory.SL2Z_lift

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

section Assembly

def Sigma (f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ) : R →ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  (MonoidAlgebra.lift ℂ (Matrix (Fin 6) (Fin 6) ℂ) SL(2, ℤ)) f

lemma Sigma_ofSL (f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ) (γ : SL(2, ℤ)) :
    Sigma f (ofSL γ) = f γ := by
  have h : ofSL γ = MonoidAlgebra.of ℂ SL(2, ℤ) γ := rfl
  rw [h, Sigma, MonoidAlgebra.lift_of]

lemma RT_eq : (R_T : R) = ofSL ModularGroup.T := rfl
lemma RS_eq : (R_S : R) = ofSL ModularGroup.S := rfl

lemma one_eq_ofSL_one : (1 : R) = ofSL (1 : SL(2, ℤ)) := by
  rw [ofSL, MonoidAlgebra.one_def]

lemma row_zero_mul {A B : Matrix (Fin 6) (Fin 6) ℂ} (hA : A 0 = 0) : (A * B) 0 = 0 := by
  funext j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [congr_fun hA k, Pi.zero_apply, zero_mul]

variable {f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ}

lemma Sigma_RT_sub_one (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (R_T - 1) = oddMT - 1 := by
  rw [RT_eq, one_eq_ofSL_one, map_sub, Sigma_ofSL, Sigma_ofSL, map_one, hT]

lemma Sigma_RS (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f R_S = oddMS := by
  rw [RS_eq, Sigma_ofSL, hS]

lemma Sigma_RT2_row0 (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (hrow : ∀ j : Fin 6, ((oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) :
    (Sigma f ((R_T - 1) ^ 2)) 0 = 0 := by
  have h1 : Sigma f ((R_T - 1) ^ 2) = (oddMT - 1) ^ 2 := by
    rw [pow_two, map_mul, Sigma_RT_sub_one hS hT, ← pow_two]
  rw [h1]
  funext j
  exact hrow j

lemma Sigma_RT2_mul_row0 (a : R) (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (hrow : ∀ j : Fin 6, ((oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) :
    (Sigma f ((R_T - 1) ^ 2 * a)) 0 = 0 := by
  rw [map_mul]
  exact row_zero_mul (Sigma_RT2_row0 hS hT hrow)

lemma Sigma_RS_RT2_row0 (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (hrow : ∀ j : Fin 6, (oddMS * (oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) :
    (Sigma f (R_S * (R_T - 1) ^ 2)) 0 = 0 := by
  have h1 : Sigma f (R_S * (R_T - 1) ^ 2) = oddMS * (oddMT - 1) ^ 2 := by
    rw [map_mul, Sigma_RS hS hT, pow_two, map_mul, Sigma_RT_sub_one hS hT, ← pow_two]
  rw [h1]
  funext j
  exact hrow j

lemma Sigma_RS_RT2_mul_row0 (a : R) (hS : f ModularGroup.S = oddMS)
    (hT : f ModularGroup.T = oddMT)
    (hrow : ∀ j : Fin 6, (oddMS * (oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) :
    (Sigma f (R_S * (R_T - 1) ^ 2 * a)) 0 = 0 := by
  rw [map_mul]
  exact row_zero_mul (Sigma_RS_RT2_row0 hS hT hrow)

lemma Sigma_Rneg (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (h : oddMS * oddMS = -1) : Sigma f Rneg = -1 := by
  have hSS : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [show (Rneg : R) = ofSL (-1 : SL(2,ℤ)) from rfl, Sigma_ofSL, hSS, map_mul, hS, h]

lemma Sigma_Rneg_add_one (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (h : oddMS * oddMS = -1) : Sigma f (Rneg + 1) = 0 := by
  rw [map_add, Sigma_Rneg hS hT h, map_one, neg_add_cancel]

lemma Sigma_aug_row0 (a : R) (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT)
    (h : oddMS * oddMS = -1) :
    (Sigma f ((Rneg + 1) * a)) 0 = 0 := by
  rw [map_mul, Sigma_Rneg_add_one hS hT h, zero_mul]
  rfl

/-- vanishing of the first-row functionals on the ideal `𝓘 = (T-I)²R + S(T-I)²R` -/
lemma Sigma_IdealI_row0 (a : R) (hS : f ModularGroup.S = oddMS)
    (hT : f ModularGroup.T = oddMT) (ha : a ∈ Work.Kernels.IdealI)
    (hrow1 : ∀ j : Fin 6, ((oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0)
    (hrow2 : ∀ j : Fin 6, (oddMS * (oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) :
    (Sigma f a) 0 = 0 := by
  obtain ⟨u, v, huv⟩ := mem_span2.mp ha
  rw [huv, map_add]
  funext j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  rw [congr_fun (Sigma_RT2_mul_row0 u hS hT hrow1) j,
    congr_fun (Sigma_RS_RT2_mul_row0 v hS hT hrow2) j]
  simp

/-- vanishing of the first-row functionals on the augmentation ideal `(1+z)R` -/
lemma Sigma_augIdealOdd_row0 (c : R) (hS : f ModularGroup.S = oddMS)
    (hT : f ModularGroup.T = oddMT) (hmm : oddMS * oddMS = -1) (hc : c ∈ augIdealOdd) :
    (Sigma f c) 0 = 0 := by
  induction hc using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, s, rfl⟩ := hy
    rw [map_mul, map_mul, Sigma_Rneg_add_one hS hT hmm, mul_zero, zero_mul]
    rfl
  | zero => rw [map_zero]; rfl
  | add y z _ _ hy hz =>
    rw [map_add]
    funext j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    rw [congr_fun hy j, congr_fun hz j]
    simp
  | smul b y _ hy =>
    rw [map_smul]
    funext j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    rw [congr_fun hy j]
    simp

/-- the first-row functionals vanish on the whole odd ideal -/
theorem Sigma_idealIOdd_row0 (x : R) (hS : f ModularGroup.S = oddMS)
    (hT : f ModularGroup.T = oddMT) (hx : x ∈ idealIOdd)
    (hrow1 : ∀ j : Fin 6, ((oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0)
    (hrow2 : ∀ j : Fin 6, (oddMS * (oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0)
    (hmm : oddMS * oddMS = -1) : (Sigma f x) 0 = 0 := by
  rw [show idealIOdd = Work.Kernels.IdealI ⊔ augIdealOdd from rfl] at hx
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  funext j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  rw [congr_fun (Sigma_IdealI_row0 a hS hT ha hrow1 hrow2) j,
    congr_fun (Sigma_augIdealOdd_row0 c hS hT hmm hc) j]
  simp

end Assembly

end Work.Asymptotics

namespace Work.Asymptotics

open Work.Kernels

section Assembly3

variable {f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ}

lemma Sigma_Tinv (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    f (ModularGroup.T)⁻¹ = oddMT⁻¹ := by
  have h : oddMT * f (ModularGroup.T)⁻¹ = 1 := by
    rw [← hT, ← map_mul, mul_inv_cancel, map_one]
  exact (Matrix.inv_eq_right_inv h).symm

lemma Sigma_Mp_zero (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (0 : Fin 6)) = oddMu (0 : Fin 6) := by
  have h : MpElem (0 : Fin 6) = ofSL (1 : SL(2,ℤ)) := by
    rw [show MpElem (0 : Fin 6) = ofSL (Mp (0 : Fin 6)) from rfl,
      show Mp (0 : Fin 6) = (1 : SL(2,ℤ)) from by decide]
  rw [h, Sigma_ofSL, map_one]
  simp [oddMu]

lemma Sigma_Mp_one (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (1 : Fin 6)) = oddMu (1 : Fin 6) := by
  have h : MpElem (1 : Fin 6) = ofSL ((ModularGroup.T)⁻¹) := by
    rw [show MpElem (1 : Fin 6) = ofSL (Mp (1 : Fin 6)) from rfl,
      show Mp (1 : Fin 6) = (ModularGroup.T)⁻¹ from by decide]
  rw [h, Sigma_ofSL, Sigma_Tinv hS hT]
  simp [oddMu]

lemma Sigma_Mp_two (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (2 : Fin 6)) = oddMu (2 : Fin 6) := by
  have h : MpElem (2 : Fin 6) = ofSL (ModularGroup.S * ModularGroup.T * ModularGroup.S) := by
    rw [show MpElem (2 : Fin 6) = ofSL (Mp (2 : Fin 6)) from rfl,
      show Mp (2 : Fin 6) = ModularGroup.S * ModularGroup.T * ModularGroup.S from by decide]
  rw [h, Sigma_ofSL, map_mul, map_mul, hS, hT]
  simp only [oddMu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  rfl

lemma Sigma_Mp_three (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (3 : Fin 6)) = oddMu (3 : Fin 6) := by
  have h : MpElem (3 : Fin 6) = ofSL (ModularGroup.S) := by
    rw [show MpElem (3 : Fin 6) = ofSL (Mp (3 : Fin 6)) from rfl,
      show Mp (3 : Fin 6) = ModularGroup.S from by decide]
  rw [h, Sigma_ofSL, hS]
  simp [oddMu]

lemma Sigma_Mp_four (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (4 : Fin 6)) = oddMu (4 : Fin 6) := by
  have h : MpElem (4 : Fin 6) = ofSL (ModularGroup.S * (ModularGroup.T)⁻¹) := by
    rw [show MpElem (4 : Fin 6) = ofSL (Mp (4 : Fin 6)) from rfl,
      show Mp (4 : Fin 6) = ModularGroup.S * (ModularGroup.T)⁻¹ from by decide]
  rw [h, Sigma_ofSL, map_mul, hS, Sigma_Tinv hS hT]
  simp [oddMu]

lemma Sigma_Mp_five (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem (5 : Fin 6)) = oddMu (5 : Fin 6) := by
  have h : MpElem (5 : Fin 6) = ofSL (ModularGroup.T * ModularGroup.S) := by
    rw [show MpElem (5 : Fin 6) = ofSL (Mp (5 : Fin 6)) from rfl,
      show Mp (5 : Fin 6) = ModularGroup.T * ModularGroup.S from by decide]
  rw [h, Sigma_ofSL, map_mul, hT, hS]
  simp [oddMu]

lemma Sigma_Mp (i : Fin 6) (hS : f ModularGroup.S = oddMS) (hT : f ModularGroup.T = oddMT) :
    Sigma f (MpElem i) = oddMu i := by
  fin_cases i
  · exact Sigma_Mp_zero hS hT
  · exact Sigma_Mp_one hS hT
  · exact Sigma_Mp_two hS hT
  · exact Sigma_Mp_three hS hT
  · exact Sigma_Mp_four hS hT
  · exact Sigma_Mp_five hS hT

/-- the value matrix of the six first-row functionals on the six basis elements is the
identity -/
theorem Sigma_Mp_row (i j : Fin 6) (hS : f ModularGroup.S = oddMS)
    (hT : f ModularGroup.T = oddMT)
    (hrow3 : ∀ i j : Fin 6, oddMu i 0 j = if j = i then 1 else 0) :
    (Sigma f (MpElem i)) 0 j = if j = i then 1 else 0 := by
  rw [Sigma_Mp i hS hT, hrow3 i j]

end Assembly3

end Work.Asymptotics

namespace Work.Asymptotics

open Work.Kernels

section Assembly4

variable {f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ}

/-- **The linear independence, given the representation and the five matrix identities.** -/
theorem indep_Mp_idealIOdd_aux
    (hmat : (oddMS * oddMS = -1) ∧ ((oddMS * oddMT) ^ 3 = -1) ∧
      (∀ j : Fin 6, ((oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) ∧
      (∀ j : Fin 6, (oddMS * (oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) ∧
      (∀ i j : Fin 6, oddMu i 0 j = if j = i then 1 else 0))
    (hlift : ∃ f : SL(2, ℤ) →* Matrix (Fin 6) (Fin 6) ℂ,
      f ModularGroup.S = oddMS ∧ f ModularGroup.T = oddMT) :
    LinearIndependent ℂ
      (fun i : Fin 6 => Submodule.mkQ idealIOdd (MpElem i)) := by
  obtain ⟨hmm, hcube, hrow1, hrow2, hrow3⟩ := hmat
  obtain ⟨f, hS, hT⟩ := hlift
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hx : ∑ i, g i • MpElem i ∈ idealIOdd := by
    rw [← Submodule.Quotient.mk_eq_zero idealIOdd]
    show Submodule.mkQ idealIOdd (∑ i, g i • MpElem i) = 0
    have h : Submodule.mkQ idealIOdd (∑ i, g i • MpElem i)
        = ∑ i, g i • Submodule.mkQ idealIOdd (MpElem i) := by
      rw [map_sum (Submodule.mkQ idealIOdd) (fun i => g i • MpElem i) Finset.univ]
      simp only [map_smul]
    rw [h, hg]
  have h0 : (Sigma f (∑ i, g i • MpElem i)) 0 j = 0 :=
    congr_fun (Sigma_idealIOdd_row0 _ hS hT hx hrow1 hrow2 hmm) j
  have hval : (Sigma f (∑ i, g i • MpElem i)) 0 j = g j := by
    rw [map_sum (Sigma f) (fun i => g i • MpElem i) Finset.univ]
    simp only [Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Sigma_Mp_row j j hS hT hrow3]
      simp
    · intro b _ hb
      rw [Sigma_Mp_row b j hS hT hrow3]
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [← hval]
  exact h0

end Assembly4

/-- **Linear independence of the six `Mp` classes modulo the odd defect ideal.** -/
theorem indep_Mp_idealIOdd :
    LinearIndependent ℂ
      (fun i : Fin 6 => Submodule.mkQ Work.Asymptotics.idealIOdd (Work.Asymptotics.MpElem i)) := by
  obtain ⟨hmm, hcube, hrow1, hrow2, hrow3⟩ := oddSigma_matrices
  have h4 : oddMS ^ 4 = (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two oddMS, hmm]
    simp
  have h2 : oddMS ^ 2 = (oddMS * oddMT) ^ 3 := by
    rw [pow_two oddMS, hmm, hcube]
  obtain ⟨f, hfS, hfT⟩ := Work.GroupTheory.SL2Z_lift oddMS oddMT h4 h2
  exact indep_Mp_idealIOdd_aux ⟨hmm, hcube, hrow1, hrow2, hrow3⟩ ⟨f, hfS, hfT⟩

end Work.Asymptotics

end
