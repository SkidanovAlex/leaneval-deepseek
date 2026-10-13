/-
  WilG1 / Plumb / SsetMem.

  `Sset` is an `Ω`-set whenever `graphOf f` is: the `Ω`-bookkeeping of the construction of
  `DerivDefs`.  Every piece of `innerSet` is a hypersurface, a positivity set of a polynomial or a
  reindexed copy of `graphOf f`, and the quantifier chain is a chain of projections and
  complements, so the format is a fixed numeral and the degree is affine in `D`.
-/
import Mathlib
import Submission.Work.WilG1.Plumb.DerivDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section
open Classical

namespace Work.WilG1.Plumb

open WilkiesDesign WilkiesConjecture

variable {S : WilkiesDesign.SOMin}

/-! ## 1. Numerical intersection and union at a common format -/

theorem inter_same {S : WilkiesDesign.SOMin} {n a D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a D₁ n) (hY : Y ∈ S.Ω a D₂ n) : X ∩ Y ∈ S.Ω (a + 1) (D₁ + D₂) n := by
  have h := S.inter (fun t : Fin 2 => if t = 0 then D₁ else D₂)
    (fun t : Fin 2 => if t = 0 then X else Y) (by
      intro t
      fin_cases t
      · simpa using hX
      · simpa using hY)
  rw [show (∑ t : Fin 2, (if t = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; simp] at h
  rw [show (⋂ t : Fin 2, (if t = 0 then X else Y)) = X ∩ Y from
    Work.WilG1.Omega.iInter_fin_two X Y] at h
  exact h

theorem union_same {S : WilkiesDesign.SOMin} {n a D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a D₁ n) (hY : Y ∈ S.Ω a D₂ n) : X ∪ Y ∈ S.Ω a (D₁ + D₂) n := by
  have h := S.union (fun t : Fin 2 => if t = 0 then D₁ else D₂)
    (fun t : Fin 2 => if t = 0 then X else Y) (by
      intro t
      fin_cases t
      · simpa using hX
      · simpa using hY)
  rw [show (∑ t : Fin 2, (if t = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; simp] at h
  rw [show (⋃ t : Fin 2, (if t = 0 then X else Y)) = X ∪ Y from
    Work.WilG1.Omega.iUnion_fin_two X Y] at h
  exact h

theorem inter_fin {S : WilkiesDesign.SOMin} {n k a D₀ : ℕ} (A : Fin k → Set (Fin n → ℝ))
    (hA : ∀ i, A i ∈ S.Ω a D₀ n) : (⋂ i, A i) ∈ S.Ω (a + 1) (k * D₀) n := by
  have h := Work.WilG1.Omega.inter_mem (S := S) (D := 0) (b := Polynomial.C D₀) A
    (fun i => by simpa using hA i)
  simpa using h

/-! ## 2. The bookkeeping constants -/

/-- The `D`-offset produced by the two reindexings of `graphOf f`. -/
abbrev KK (N : ℕ) : ℕ := 32 * (bigDim N + (N + 1))

/-- A format dominating the five pieces of `innerSet`. -/
abbrev AA (N F : ℕ) : ℕ := F + 64 * (bigDim N + (N + 1)) + 64 + (bigDim N + 5)

/-- The format after `∀ y u w` (i.e. after projecting `innerSetᶜ` out). -/
abbrev A0 (N F : ℕ) : ℕ := (AA N F + 1) + 1 + (N + 2) + 1

abbrev A1 (N F : ℕ) : ℕ := A0 N F + 1

abbrev A2 (N F : ℕ) : ℕ := A1 N F + 1 + 1

abbrev A3 (N F : ℕ) : ℕ := A2 N F + 1

abbrev AFR (N F : ℕ) : ℕ := A3 N F + 1

abbrev DEG0 (N D : ℕ) : ℕ := (((N * 4 + 4) + (D + KK N + 32)) + (D + KK N + 32)) + 6

abbrev DEG1 (N D : ℕ) : ℕ := 3 + DEG0 N D

abbrev DEG2 (N D : ℕ) : ℕ := 3 + DEG1 N D

/-! ## 3. Arithmetic facts about the constants -/

theorem fourN_le_KK (N : ℕ) : 4 * N ≤ KK N := by
  unfold KK bigDim
  omega

theorem N4_le_deg (N D : ℕ) : N * 4 ≤ D + KK N + 32 := by
  have h := fourN_le_KK N
  omega

theorem le_AA_one (N F : ℕ) : F + 64 * (bigDim N + (N + 1)) + 64 ≤ AA N F := by
  unfold AA
  omega

theorem le_AA_two (N F : ℕ) : bigDim N + 2 ≤ AA N F := by
  unfold AA
  omega

theorem le_AA_three (N F : ℕ) : bigDim N + 3 ≤ AA N F := by
  unfold AA
  omega

theorem le_AA_five (N F : ℕ) : bigDim N + 5 ≤ AA N F := by
  unfold AA
  omega

theorem le_A0_posD (N F : ℕ) : aDim N + 2 ≤ A0 N F := by
  unfold A0 AA aDim bigDim
  omega

theorem le_A2_posE (N F : ℕ) : bDim N + 2 ≤ A2 N F := by
  unfold A2 A1 A0 AA bDim bigDim
  omega

/-! ## 4. The five pieces -/

def agreePoly (N : ℕ) (j : Fin N) : MvPolynomial (Fin (bigDim N)) ℝ :=
  MvPolynomial.X (yIdx N j) - MvPolynomial.X (xIdx N j)

theorem agreePoly_totalDegree (N : ℕ) (j : Fin N) : (agreePoly N j).totalDegree ≤ 1 := by
  rw [agreePoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩

theorem agreeSet_eq (N : ℕ) (i : Fin N) :
    agreeSet N i = ⋂ j : Fin N, (if j = i then (Set.univ : Set (Fin (bigDim N) → ℝ))
      else {z : Fin (bigDim N) → ℝ | MvPolynomial.eval z (agreePoly N j) = 0}) := by
  ext z
  simp only [agreeSet, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h j
    by_cases hj : j = i
    · simp [hj]
    · rw [if_neg hj]
      simp only [Set.mem_ofPred_eq, agreePoly, MvPolynomial.eval_sub, MvPolynomial.eval_X]
      rw [sub_eq_zero]
      exact h j hj
  · intro h j hj
    have hh := h j
    rw [if_neg hj] at hh
    simp only [Set.mem_ofPred_eq, agreePoly, MvPolynomial.eval_sub, MvPolynomial.eval_X] at hh
    rw [sub_eq_zero] at hh
    exact hh

theorem agreeSet_mem {S : WilkiesDesign.SOMin} {N : ℕ} (i : Fin N) :
    agreeSet N i ∈ S.Ω (bigDim N + 5) (N * 4) (bigDim N) := by
  rw [agreeSet_eq]
  refine inter_fin (k := N) (a := bigDim N + 4) (D₀ := 4) _ ?_
  intro j
  by_cases hj : j = i
  · rw [if_pos hj]
    exact Work.WilG5.univ_mem (S := S) (n := bigDim N)
  · rw [if_neg hj]
    have h := Work.WilG1.Omega.hyp_mem (S := S) (n := bigDim N) 0 (agreePoly N j)
    have htd := agreePoly_totalDegree N j
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_C]
    omega

def badPoly (N : ℕ) (i : Fin N) : MvPolynomial (Fin (bigDim N)) ℝ :=
  (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2 - MvPolynomial.X (dIdx N) ^ 2

theorem badPoly_totalDegree (N : ℕ) (i : Fin N) : (badPoly N i).totalDegree ≤ 2 := by
  rw [badPoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    have h : (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
        MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩
    omega
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]

theorem badSet_mem {S : WilkiesDesign.SOMin} {N : ℕ} (i : Fin N) :
    badSet N i ∈ S.Ω (bigDim N + 2) 4 (bigDim N) := by
  have hset : badSet N i =
      {z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (-(badPoly N i))} := by
    ext z
    rw [badSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq, badPoly]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_neg]
    constructor <;> intro h <;> linarith
  rw [hset]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := bigDim N) 0 (-(badPoly N i))
  refine Work.WilG1.Omega.mono h le_rfl ?_
  rw [MvPolynomial.totalDegree_neg]
  have htd := badPoly_totalDegree N i
  simp only [Polynomial.eval_C]
  omega

def ineqPoly (N : ℕ) (i : Fin N) : MvPolynomial (Fin (bigDim N)) ℝ :=
  MvPolynomial.X (eIdx N) ^ 2 * (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2
    - (MvPolynomial.X (uIdx N) - MvPolynomial.X (wIdx N)
        - MvPolynomial.X (cIdx N) * (MvPolynomial.X (yIdx N i)
          - MvPolynomial.X (xIdx N i))) ^ 2

theorem ineqPoly_totalDegree (N : ℕ) (i : Fin N) : (ineqPoly N i).totalDegree ≤ 4 := by
  have hsub : (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i) :
      MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩
  have hu : (MvPolynomial.X (uIdx N) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have hw : (MvPolynomial.X (wIdx N) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have hc : (MvPolynomial.X (cIdx N) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have he : (MvPolynomial.X (eIdx N) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have h1 : (MvPolynomial.X (eIdx N) ^ 2 *
      (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2 :
      MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 4 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h2 : ((MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2 :
        MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 2 := by
      refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
      omega
    have h3 : ((MvPolynomial.X (eIdx N)) ^ 2 : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 2 := by
      refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
      omega
    omega
  have h2 : ((MvPolynomial.X (uIdx N) - MvPolynomial.X (wIdx N)
      - MvPolynomial.X (cIdx N) * (MvPolynomial.X (yIdx N i)
        - MvPolynomial.X (xIdx N i))) ^ 2 : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 4 := by
    have hinner : (MvPolynomial.X (uIdx N) - MvPolynomial.X (wIdx N)
        - MvPolynomial.X (cIdx N) * (MvPolynomial.X (yIdx N i)
          - MvPolynomial.X (xIdx N i)) : MvPolynomial (Fin (bigDim N)) ℝ).totalDegree ≤ 2 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · refine le_trans (le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hu hw)) (by omega)
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        omega
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    omega
  rw [ineqPoly]
  exact le_trans (MvPolynomial.totalDegree_sub _ _) (max_le h1 h2)

theorem ineqSet_mem {S : WilkiesDesign.SOMin} {N : ℕ} (i : Fin N) :
    ineqSet N i ∈ S.Ω (bigDim N + 3) 6 (bigDim N) := by
  have hset : ineqSet N i =
      {z : Fin (bigDim N) → ℝ | 0 ≤ MvPolynomial.eval z (ineqPoly N i)} := by
    ext z
    rw [ineqSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq, ineqPoly]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset]
  have hcompl : {z : Fin (bigDim N) → ℝ | 0 ≤ MvPolynomial.eval z (ineqPoly N i)} =
      ({z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (-(ineqPoly N i))})ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, MvPolynomial.eval_neg]
    constructor <;> intro h <;> linarith
  rw [hcompl]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := bigDim N) 0 (-(ineqPoly N i))
  have h' : {z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (-(ineqPoly N i))} ∈
      S.Ω (bigDim N + 2) 6 (bigDim N) := by
    refine Work.WilG1.Omega.mono h le_rfl ?_
    rw [MvPolynomial.totalDegree_neg]
    have htd := ineqPoly_totalDegree N i
    simp only [Polynomial.eval_C]
    omega
  exact S.compl h'

theorem grYSet_mem {S : WilkiesDesign.SOMin} {N F D : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : graphOf f ∈ S.Ω F D (N+1)) :
    grYSet N f ∈ S.Ω (F + 64 * (bigDim N + (N + 1)) + 64) (D + KK N + 32) (bigDim N) := by
  have h := Work.WilG5.coordPre_mem (S := S) (ι := lastMapY N) hf
  simpa [grYSet, KK] using h

theorem grXSet_mem {S : WilkiesDesign.SOMin} {N F D : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : graphOf f ∈ S.Ω F D (N+1)) :
    grXSet N f ∈ S.Ω (F + 64 * (bigDim N + (N + 1)) + 64) (D + KK N + 32) (bigDim N) := by
  have h := Work.WilG5.coordPre_mem (S := S) (ι := lastMapX N) hf
  simpa [grXSet, KK] using h

/-! ## 5. The inner set -/

theorem innerSet_mem {S : WilkiesDesign.SOMin} {N F D : ℕ} {f : (Fin N → ℝ) → ℝ} (i : Fin N)
    (hf : graphOf f ∈ S.Ω F D (N+1)) :
    innerSet N i f ∈ S.Ω (AA N F + 1) (DEG0 N D) (bigDim N) := by
  have h1 : (agreeSet N i)ᶜ ∈ S.Ω (AA N F + 1) (N * 4) (bigDim N) :=
    S.compl (Work.WilG1.Omega.mono (agreeSet_mem (S := S) i) (le_AA_five N F) le_rfl)
  have h2 : (badSet N i)ᶜ ∈ S.Ω (AA N F + 1) 4 (bigDim N) :=
    S.compl (Work.WilG1.Omega.mono (badSet_mem (S := S) i) (le_AA_two N F) le_rfl)
  have h3 : (grYSet N f)ᶜ ∈ S.Ω (AA N F + 1) (D + KK N + 32) (bigDim N) :=
    S.compl (Work.WilG1.Omega.mono (grYSet_mem (S := S) hf) (le_AA_one N F) le_rfl)
  have h4 : (grXSet N f)ᶜ ∈ S.Ω (AA N F + 1) (D + KK N + 32) (bigDim N) :=
    S.compl (Work.WilG1.Omega.mono (grXSet_mem (S := S) hf) (le_AA_one N F) le_rfl)
  have h5 : ineqSet N i ∈ S.Ω (AA N F + 1) 6 (bigDim N) :=
    Work.WilG1.Omega.mono (ineqSet_mem (S := S) i) (le_trans (le_AA_three N F) (by omega)) le_rfl
  have h12 : (agreeSet N i)ᶜ ∪ (badSet N i)ᶜ ∈
      S.Ω (AA N F + 1) (N * 4 + 4) (bigDim N) := union_same h1 h2
  have h123 : ((agreeSet N i)ᶜ ∪ (badSet N i)ᶜ) ∪ (grYSet N f)ᶜ ∈
      S.Ω (AA N F + 1) ((N * 4 + 4) + (D + KK N + 32)) (bigDim N) := union_same h12 h3
  have h1234 : (((agreeSet N i)ᶜ ∪ (badSet N i)ᶜ) ∪ (grYSet N f)ᶜ) ∪ (grXSet N f)ᶜ ∈
      S.Ω (AA N F + 1) (((N * 4 + 4) + (D + KK N + 32)) + (D + KK N + 32)) (bigDim N) :=
    union_same h123 h4
  have h12345 : ((((agreeSet N i)ᶜ ∪ (badSet N i)ᶜ) ∪ (grYSet N f)ᶜ) ∪ (grXSet N f)ᶜ)
      ∪ ineqSet N i ∈ S.Ω (AA N F + 1) (DEG0 N D) (bigDim N) :=
    union_same h1234 h5
  simpa [innerSet, DEG0] using h12345

/-! ## 6. The quantifier chain -/

theorem Sset_omega_aux {S : WilkiesDesign.SOMin} {N F D : ℕ} {f : (Fin N → ℝ) → ℝ} (i : Fin N)
    (hf : graphOf f ∈ S.Ω F D (N + 1)) :
    ∃ a : ℕ, ∃ b : Polynomial ℕ, Sset N i f ∈ S.Ω a (b.eval D) (N + 1) := by
  have hin : innerSet N i f ∈ S.Ω (AA N F + 1) (DEG0 N D) (bigDim N) :=
    innerSet_mem (S := S) i hf
  have hinc : (innerSet N i f)ᶜ ∈ S.Ω (AA N F + 1 + 1) (DEG0 N D) (bigDim N) := S.compl hin
  have hpj : projYSet N i f ∈ S.Ω (A0 N F) (DEG0 N D) (aDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := aDim N) (N + 2) (AA N F + 1 + 1)
      (DEG0 N D) hinc
    have h' := S.compl h
    simpa [projYSet, A0] using h'
  have hposd : posDSet N ∈ S.Ω (A0 N F) 3 (aDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := aDim N) 0
      (MvPolynomial.X (dIdxA N) : MvPolynomial (Fin (aDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posDSet] using h) (le_A0_posD N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hI1 : posDSet N ∩ projYSet N i f ∈ S.Ω (A1 N F) (DEG1 N D) (aDim N) := by
    have h := inter_same hposd hpj
    simpa [A1, DEG1] using h
  have hpd : projDSet N i f ∈ S.Ω (A1 N F + 1) (DEG1 N D) (bDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := bDim N) 1 (A1 N F) (DEG1 N D) hI1
    simpa [projDSet] using h
  have hpdc : (projDSet N i f)ᶜ ∈ S.Ω (A1 N F + 1 + 1) (DEG1 N D) (bDim N) := S.compl hpd
  have hpse : posESet N ∈ S.Ω (A2 N F) 3 (bDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := bDim N) 0
      (MvPolynomial.X (eIdxB N) : MvPolynomial (Fin (bDim N)) ℝ)
    exact Work.WilG1.Omega.mono (by simpa [posESet] using h) (le_A2_posE N F)
      (by simp [MvPolynomial.totalDegree_X])
  have hpdc' : (projDSet N i f)ᶜ ∈ S.Ω (A2 N F) (DEG1 N D) (bDim N) := by
    simpa [A2] using hpdc
  have hI2 : posESet N ∩ (projDSet N i f)ᶜ ∈ S.Ω (A3 N F) (DEG2 N D) (bDim N) := by
    have h := inter_same hpse hpdc'
    simpa [A3, DEG2] using h
  have hSs : Sset N i f ∈ S.Ω (AFR N F + 1) (DEG2 N D) (N + 1) := by
    have h := Work.WilG5.projN_mem (S := S) (n := N + 1) 1 (A3 N F) (DEG2 N D) hI2
    have h' := S.compl h
    simpa [Sset, AFR] using h'
  have hb : (Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * KK N + N * 4 + 80)).eval D
      = DEG2 N D := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  refine ⟨AFR N F + 1, Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * KK N + N * 4 + 80), ?_⟩
  rw [hb]
  exact hSs

end Work.WilG1.Plumb
