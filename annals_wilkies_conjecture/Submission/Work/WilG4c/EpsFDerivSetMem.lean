/-
  WilG4c — `EpsFDerivSetMem`: `epsFDerivSet` is an `Ω`-set.

  The construction is laid out in `Submission.Work.WilG4c.EpsSetDefs`:
  `EpsSet N φ` is built from `graphOf φ` by complements, projections and polynomial
  positivity sets, and `EpsSet N φ = epsFDerivSet N φ` (`EpsSet_eq_epsFDerivSet`, which uses
  the analytic lemma `hasFDerivAt_iff_epsPoly` and the set-level reduction
  `forall_asm_innerSet_iff`).

  This file contains the `Ω`-bookkeeping: the memberships of the four pieces of `innerSet`,
  and the quantifier chain `∀ y u w` / `∃ δ > 0` / `∀ ε > 0` as projections and complements.
-/
import Mathlib
import Submission.Work.WilG4c.SgnEqDefs
import Submission.Work.WilG4c.EpsSetDefs
import Submission.Work.WilG4c.hasFDerivAt_iff_epsPoly
import Submission.Work.WilG4c.forall_asm_innerSet_iff
import Submission.Work.WilG4c.hypSet_mem
import Submission.Work.WilG4c.ineqSet_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesConjecture

variable {S : WilkiesDesign.SOMin}

/-! ## 1. Numerics: union / intersection at a common format -/

theorem union_same {n a D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
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

theorem inter_same {n a D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
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

/-! ## 2. Numerical costs -/

/-- The format cost of reindexing `graphOf φ` into the big space. -/
def Kg (N F : ℕ) : ℕ := F + 64 * (bigDim N + (N + 1)) + 64

/-- The degree cost of reindexing `graphOf φ` into the big space. -/
def Lg (N D : ℕ) : ℕ := D + 32 * (bigDim N + (N + 1)) + 32

theorem graphYSet_mem {N F D : ℕ} {φ : (Fin N → ℝ) → ℝ}
    (hf : graphOf φ ∈ S.Ω F D (N + 1)) :
    graphYSet N φ ∈ S.Ω (Kg N F) (Lg N D) (bigDim N) := by
  have h := Work.WilG5.coordPre_mem (S := S) (ι := lastMapY N) hf
  simpa [graphYSet, Kg, Lg] using h

theorem graphXSet_mem {N F D : ℕ} {φ : (Fin N → ℝ) → ℝ}
    (hf : graphOf φ ∈ S.Ω F D (N + 1)) :
    graphXSet N φ ∈ S.Ω (Kg N F) (Lg N D) (bigDim N) := by
  have h := Work.WilG5.coordPre_mem (S := S) (ι := lastMapX N) hf
  simpa [graphXSet, Kg, Lg] using h

/-! ## 3. The formats of the quantifier chain -/

/-- A format dominating the four pieces of `innerSet`. -/
def Aall (N F A1 A2 : ℕ) : ℕ := max (A1 + 1) (max (Kg N F + 1) A2)

/-- The format after taking the complement of `innerSet`. -/
def Agp (N F A1 A2 : ℕ) : ℕ := Aall N F A1 A2 + 1

/-- The format of `projYSet`. -/
def Apj (N F A1 A2 : ℕ) : ℕ := Agp N F A1 A2 + (N + 2) + 1

/-- A format dominating `posDSet` and `projYSet`. -/
def Ad (N F A1 A2 : ℕ) : ℕ := max (aDim N + 2) (Apj N F A1 A2)

/-- The format of `projDSet`. -/
def Apd (N F A1 A2 : ℕ) : ℕ := Ad N F A1 A2 + 1 + 1

/-- The format of `projDSetᶜ`. -/
def Apdc (N F A1 A2 : ℕ) : ℕ := Apd N F A1 A2 + 1

/-- A format dominating `posESet` and `projDSetᶜ`. -/
def Ae (N F A1 A2 : ℕ) : ℕ := max (bDim N + 2) (Apdc N F A1 A2)

/-- The format after the last projection. -/
def Aep (N F A1 A2 : ℕ) : ℕ := Ae N F A1 A2 + 1 + 1

/-- The format of `EpsSet`. -/
def Afin (N F A1 A2 : ℕ) : ℕ := Aep N F A1 A2 + 1

/-- The degree of `EpsSet`: `2 * D` plus a constant. -/
def Cin (N B1 B2 : ℕ) : ℕ := B1 + B2 + 2 * Lg N 0 + 6

/-- The degree after the four unions (and the first projection). -/
def ds0 (N D B1 B2 : ℕ) : ℕ := ((B1 + Lg N D) + Lg N D) + B2

/-- The degree after intersecting with `posDSet`. -/
def ds1 (N D B1 B2 : ℕ) : ℕ := 3 + ds0 N D B1 B2

/-- The degree after intersecting with `posESet`. -/
def ds2 (N D B1 B2 : ℕ) : ℕ := 3 + ds1 N D B1 B2

theorem ds2_le_Cin (N D B1 B2 : ℕ) : ds2 N D B1 B2 ≤ 2 * D + Cin N B1 B2 := by
  simp only [ds2, ds1, ds0, Cin, Lg]
  omega

theorem le_Aall_one (N F A1 A2 : ℕ) : A1 + 1 ≤ Aall N F A1 A2 := by
  unfold Aall; exact le_max_left _ _

theorem le_Aall_two (N F A1 A2 : ℕ) : Kg N F + 1 ≤ Aall N F A1 A2 := by
  unfold Aall; exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem le_Aall_three (N F A1 A2 : ℕ) : A2 ≤ Aall N F A1 A2 := by
  unfold Aall; exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem le_Ad_one (N F A1 A2 : ℕ) : aDim N + 2 ≤ Ad N F A1 A2 := by
  unfold Ad; exact le_max_left _ _

theorem le_Ad_two (N F A1 A2 : ℕ) : Apj N F A1 A2 ≤ Ad N F A1 A2 := by
  unfold Ad; exact le_max_right _ _

theorem le_Ae_one (N F A1 A2 : ℕ) : bDim N + 2 ≤ Ae N F A1 A2 := by
  unfold Ae; exact le_max_left _ _

theorem le_Ae_two (N F A1 A2 : ℕ) : Apdc N F A1 A2 ≤ Ae N F A1 A2 := by
  unfold Ae; exact le_max_right _ _

/-! ## 4. The quantifier chain -/

/-- Given the two polynomial pieces, the whole chain produces `EpsSet N φ` from `graphOf φ`,
with format independent of `D` and degree `2 * D + Cin N B1 B2`. -/
theorem EpsSet_mem_of (S : WilkiesDesign.SOMin) (N F : ℕ) {A1 B1 A2 B2 : ℕ}
    (h1 : hypSet N ∈ S.Ω A1 B1 (bigDim N))
    (h2 : ineqSet N ∈ S.Ω A2 B2 (bigDim N)) :
    ∀ (D : ℕ) (φ : (Fin N → ℝ) → ℝ), graphOf φ ∈ S.Ω F D (N + 1) →
      EpsSet N φ ∈ S.Ω (Afin N F A1 A2) (2 * D + Cin N B1 B2) (N + N) := by
  intro D φ hf
  have hh : (hypSet N)ᶜ ∈ S.Ω (Aall N F A1 A2) B1 (bigDim N) :=
    Work.WilG1.Omega.mono (S.compl h1) (le_Aall_one N F A1 A2) le_rfl
  have hgy : (graphYSet N φ)ᶜ ∈ S.Ω (Aall N F A1 A2) (Lg N D) (bigDim N) :=
    Work.WilG1.Omega.mono (S.compl (graphYSet_mem (S := S) hf)) (le_Aall_two N F A1 A2) le_rfl
  have hgx : (graphXSet N φ)ᶜ ∈ S.Ω (Aall N F A1 A2) (Lg N D) (bigDim N) :=
    Work.WilG1.Omega.mono (S.compl (graphXSet_mem (S := S) hf)) (le_Aall_two N F A1 A2) le_rfl
  have hi : ineqSet N ∈ S.Ω (Aall N F A1 A2) B2 (bigDim N) :=
    Work.WilG1.Omega.mono h2 (le_Aall_three N F A1 A2) le_rfl
  have hU1 : (hypSet N)ᶜ ∪ (graphYSet N φ)ᶜ ∈
      S.Ω (Aall N F A1 A2) (B1 + Lg N D) (bigDim N) := union_same hh hgy
  have hU2 : ((hypSet N)ᶜ ∪ (graphYSet N φ)ᶜ) ∪ (graphXSet N φ)ᶜ ∈
      S.Ω (Aall N F A1 A2) ((B1 + Lg N D) + Lg N D) (bigDim N) := union_same hU1 hgx
  have hU3 : (((hypSet N)ᶜ ∪ (graphYSet N φ)ᶜ) ∪ (graphXSet N φ)ᶜ) ∪ ineqSet N ∈
      S.Ω (Aall N F A1 A2) (ds0 N D B1 B2) (bigDim N) :=
    union_same hU2 hi
  have hin : innerSet N φ ∈ S.Ω (Aall N F A1 A2) (ds0 N D B1 B2) (bigDim N) := by
    simpa [innerSet] using hU3
  have hinc : (innerSet N φ)ᶜ ∈ S.Ω (Agp N F A1 A2) (ds0 N D B1 B2) (bigDim N) := by
    have h := S.compl hin
    simpa [Agp] using h
  have hpj : projYSet N φ ∈ S.Ω (Apj N F A1 A2) (ds0 N D B1 B2) (aDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := aDim N) (N + 2) (Agp N F A1 A2)
      (ds0 N D B1 B2) hinc
    have h' := S.compl h
    simpa [projYSet, Apj, Agp] using h'
  have hposd : posDSet N ∈ S.Ω (aDim N + 2) 3 (aDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := aDim N) 0
      (MvPolynomial.X (dIdxA N) : MvPolynomial (Fin (aDim N)) ℝ)
    refine Work.WilG1.Omega.mono (by simpa [posDSet] using h) le_rfl ?_
    simp [MvPolynomial.totalDegree_X]
  have hI1 : posDSet N ∩ projYSet N φ ∈ S.Ω (Ad N F A1 A2 + 1) (ds1 N D B1 B2) (aDim N) :=
    inter_same (Work.WilG1.Omega.mono hposd (le_Ad_one N F A1 A2) le_rfl)
      (Work.WilG1.Omega.mono hpj (le_Ad_two N F A1 A2) le_rfl)
  have hpd : projDSet N φ ∈ S.Ω (Apd N F A1 A2) (ds1 N D B1 B2) (bDim N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := bDim N) 1 (Ad N F A1 A2 + 1)
      (ds1 N D B1 B2) hI1
    simpa [projDSet, Apd, Ad] using h
  have hpdc : (projDSet N φ)ᶜ ∈ S.Ω (Apdc N F A1 A2) (ds1 N D B1 B2) (bDim N) := by
    have h := S.compl hpd
    simpa [Apdc, Apd] using h
  have hpse : posESet N ∈ S.Ω (bDim N + 2) 3 (bDim N) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := bDim N) 0
      (MvPolynomial.X (eIdxB N) : MvPolynomial (Fin (bDim N)) ℝ)
    refine Work.WilG1.Omega.mono (by simpa [posESet] using h) le_rfl ?_
    simp [MvPolynomial.totalDegree_X]
  have hI2 : posESet N ∩ (projDSet N φ)ᶜ ∈ S.Ω (Ae N F A1 A2 + 1) (ds2 N D B1 B2) (bDim N) :=
    inter_same (Work.WilG1.Omega.mono hpse (le_Ae_one N F A1 A2) le_rfl)
      (Work.WilG1.Omega.mono hpdc (le_Ae_two N F A1 A2) le_rfl)
  have heps : EpsSet N φ ∈ S.Ω (Afin N F A1 A2) (ds2 N D B1 B2) (N + N) := by
    have h := Work.WilG5.projN_mem (S := S) (n := N + N) 1 (Ae N F A1 A2 + 1)
      (ds2 N D B1 B2) hI2
    have h' := S.compl h
    simpa [EpsSet, Afin, Aep, Ae] using h'
  exact Work.WilG1.Omega.mono heps le_rfl (ds2_le_Cin N D B1 B2)

/-! ## 5. `EpsSet` is `epsFDerivSet` -/

/-- Unfolding `EpsSet` for an arbitrary point `p` of `ℝ^{N+N}`. -/
theorem mem_EpsSet_iff_p {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (p : Fin (N + N) → ℝ) :
    p ∈ EpsSet N φ ↔ ∀ ε > 0, ∃ δ > 0, ∀ (y : Fin N → ℝ) (u w : ℝ),
      asm N (fun j => p (Fin.castAdd N j)) (fun i => p (Fin.natAdd N i)) ε δ y u w ∈
        innerSet N φ := by
  have hp : Fin.append (fun j : Fin N => p (Fin.castAdd N j))
      (fun i : Fin N => p (Fin.natAdd N i)) = p := by
    funext k
    refine Fin.addCases (motive := fun k => Fin.append (fun j : Fin N => p (Fin.castAdd N j))
      (fun i : Fin N => p (Fin.natAdd N i)) k = p k) ?_ ?_ k
    · intro i; rw [Fin.append_left]
    · intro i; rw [Fin.append_right]
  have h1 : p ∈ EpsSet N φ ↔ (Fin.append (fun j : Fin N => p (Fin.castAdd N j))
      (fun i : Fin N => p (Fin.natAdd N i))) ∈ EpsSet N φ := by rw [hp]
  rw [h1]
  exact mem_EpsSet_iff (N := N) φ (fun j => p (Fin.castAdd N j)) (fun i => p (Fin.natAdd N i))

/-- The set identity `EpsSet N φ = epsFDerivSet N φ`, from the analytic lemma (`hAn`) and the
set-level reduction of the `∀ y u w` block (`hRed`). -/
theorem EpsSet_eq_epsFDerivSet_of
    (hAn : ∀ {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ),
      HasFDerivAt φ L x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y : Fin N → ℝ,
        (∑ i, (y i - x i) ^ 2 < δ ^ 2) →
        (φ y - φ x - L (y - x)) ^ 2 ≤ ε ^ 2 * ∑ i, (y i - x i) ^ 2)
    (hRed : ∀ {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (x c : Fin N → ℝ) (ε δ : ℝ),
      (∀ (y : Fin N → ℝ) (u w : ℝ),
          asm N x c ε δ y u w ∈ innerSet N φ) ↔
        (∀ y : Fin N → ℝ, (∑ i, (y i - x i) ^ 2 < δ ^ 2) →
          (φ y - φ x - ∑ i, c i * (y i - x i)) ^ 2 ≤ ε ^ 2 * ∑ i, (y i - x i) ^ 2))
    (N : ℕ) (φ : (Fin N → ℝ) → ℝ) :
    EpsSet N φ = epsFDerivSet N φ := by
  ext p
  rw [mem_EpsSet_iff_p, mem_epsFDerivSet]
  have hAn' := hAn (φ := φ) (L := Lin (fun i : Fin N => p (Fin.natAdd N i)))
    (x := fun j : Fin N => p (Fin.castAdd N j))
  rw [hAn']
  have hRed' := hRed (φ := φ) (x := fun j : Fin N => p (Fin.castAdd N j))
    (c := fun i : Fin N => p (Fin.natAdd N i))
  have hLin : ∀ y : Fin N → ℝ,
      Lin (fun i : Fin N => p (Fin.natAdd N i))
        (y - fun j : Fin N => p (Fin.castAdd N j)) =
      ∑ i, p (Fin.natAdd N i) * (y i - p (Fin.castAdd N i)) := by
    intro y
    rw [Lin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.sub_apply]
  simp only [hRed', hLin]

/-- The set identity `EpsSet N φ = epsFDerivSet N φ`. -/
theorem EpsSet_eq_epsFDerivSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) :
    EpsSet N φ = epsFDerivSet N φ :=
  EpsSet_eq_epsFDerivSet_of hasFDerivAt_iff_epsPoly forall_asm_innerSet_iff N φ

/-- Evaluation of the degree polynomial used for `epsFDerivSet`. -/
theorem bb_eval (N B1 B2 D : ℕ) :
    (Polynomial.C 2 * Polynomial.X + Polynomial.C (Cin N B1 B2)).eval D
      = 2 * D + Cin N B1 B2 := by
  simp

theorem EpsFDerivSetMem (S : WilkiesDesign.SOMin) (N F : ℕ) :
    ∃ (A : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
        WilkiesDesign.graphOf φ ∈ S.Ω F D (N + 1) →
        Work.WilG4c.epsFDerivSet N φ ∈ S.Ω A (b.eval D) (N + N) := by
  obtain ⟨A1, B1, h1⟩ := hypSet_mem S N
  obtain ⟨A2, B2, h2⟩ := ineqSet_mem S N
  have hEps := EpsSet_mem_of S N F h1 h2
  refine ⟨Afin N F A1 A2, Polynomial.C 2 * Polynomial.X + Polynomial.C (Cin N B1 B2), ?_⟩
  intro D φ hf
  rw [← EpsSet_eq_epsFDerivSet]
  have hmem := hEps D φ hf
  rw [bb_eval]
  exact hmem

end Work.WilG4c
