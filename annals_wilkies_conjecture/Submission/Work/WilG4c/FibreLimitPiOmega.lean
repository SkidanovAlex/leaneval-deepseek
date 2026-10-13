/-
  WilG4c / `FibreLimitPiOmega` — the `Ω`-membership chain for the general-`n` fibre-limit
  construction: from `A ∈ S.Ω F D`, conclude `BsetP p n A ∈ S.Ω (F + fmtA) (D + degK)`.
-/
import Mathlib
import Submission.Work.WilG4c.FibreLimitPiChar
import Submission.Work.WilG4a.CD.fibLimDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0

variable {p n : ℕ}

/-! ## 0  Format / degree constants -/

/-- The format constant of the construction. -/
def Bc0 (p n : ℕ) : ℕ := 2 * ((NB p n) + (Wp p n)) + 1
/-- The format of `G1`. -/
def Bg1 (p n : ℕ) : ℕ := Bc0 p n + 5 + (n + 2)
/-- The format constant of the final fibre-limit set. -/
def fmtA (p n : ℕ) : ℕ := Bg1 p n + 7
/-- The degree constant of the final fibre-limit set. -/
def degK (n : ℕ) : ℕ := 14 + 5 * (n + 1)

/-! ## 1  Degree bookkeeping -/

lemma td_negX_le {N : ℕ} (i : Fin N) :
    (-MvPolynomial.X i : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  rw [MvPolynomial.totalDegree_neg]
  exact le_of_eq (MvPolynomial.totalDegree_X i)

lemma td_sub_le {N : ℕ} (i j : Fin N) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_of_eq (MvPolynomial.totalDegree_X i), le_of_eq (MvPolynomial.totalDegree_X j)⟩

lemma td_sq_le {σ : Type*} {R : Type*} [CommSemiring R]
    {A : MvPolynomial σ R} (hA : A.totalDegree ≤ 1) : (A ^ 2).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_pow A 2) ?_
  calc 2 * A.totalDegree ≤ 2 * 1 := Nat.mul_le_mul_left 2 hA
    _ = 2 := rfl

/-! ## 2  The atoms -/

theorem pPullP_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    pPullP p n A ∈ S.Ω (F + Bc0 p n) (D + 2) (NB p n) := by
  have h := Work.WilG4a.subst_mem S (iotaP p n) hA
  rwa [show pPullP p n A = {x : Fin (NB p n) → ℝ | x ∘ (iotaP p n) ∈ A} from rfl,
    Bc0]

theorem pPosEP_mem (S : SOMin) (p n : ℕ) :
    pPosEP p n ∈ S.Ω (NB p n + 3) 3 (NB p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (NB p n)
    (-MvPolynomial.X (eIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ)
  rw [show {x : Fin (NB p n) → ℝ |
        MvPolynomial.eval x (-MvPolynomial.X (eIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ) < 0}
      = pPosEP p n from by
    ext z
    simp only [pPosEP, Set.mem_setOf_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
    exact neg_lt_zero] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have := td_negX_le (eIdxP p n); omega

theorem pRneP_mem (S : SOMin) (p n : ℕ) :
    pRneP p n ∈ S.Ω (NB p n + 1) 1 (NB p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (NB p n)
    (MvPolynomial.X (rIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ)
  rw [show {x : Fin (NB p n) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (rIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ) ≠ 0}
      = pRneP p n from by
    ext z
    simp only [pRneP, Set.mem_setOf_eq, MvPolynomial.eval_X]] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  exact le_of_eq (MvPolynomial.totalDegree_X (rIdxP p n))

theorem pSqP_mem (S : SOMin) (p n : ℕ) (j : Fin (n+1)) :
    pSqP p n j ∈ S.Ω (NB p n + 2) 4 (NB p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_le S (NB p n)
    ((MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j)) ^ 2 -
      (MvPolynomial.X (rIdxP p n)) ^ 2 : MvPolynomial (Fin (NB p n)) ℝ)
  rw [show {x : Fin (NB p n) → ℝ | MvPolynomial.eval x
        ((MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j)) ^ 2 -
          (MvPolynomial.X (rIdxP p n)) ^ 2 : MvPolynomial (Fin (NB p n)) ℝ) ≤ 0}
      = pSqP p n j from by
    ext z
    simp only [pSqP, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro hh <;> linarith] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have hA : ((MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j) :
      MvPolynomial (Fin (NB p n)) ℝ) ^ 2).totalDegree ≤ 2 := td_sq_le (td_sub_le _ _)
  have hB : ((MvPolynomial.X (rIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ) ^ 2).totalDegree
      ≤ 2 := td_sq_le (le_of_eq (MvPolynomial.totalDegree_X _))
  have htd : ((MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j)) ^ 2 -
      (MvPolynomial.X (rIdxP p n)) ^ 2 : MvPolynomial (Fin (NB p n)) ℝ).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hA hB)
  omega

theorem pSqAllP_mem (S : SOMin) (p n : ℕ) :
    pSqAllP p n ∈ S.Ω (NB p n + 3) (4 * (n + 1)) (NB p n) := by
  have h := Work.WilG1.Omega.inter_mem (S := S) (k := n+1) (a := NB p n + 2)
    (b := Polynomial.C 4) (D := 0) (fun j => pSqP p n j)
    (fun j => by simpa using pSqP_mem S p n j)
  refine Work.WilG1.Omega.mono h le_rfl ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C]; omega

theorem pYneqP_mem (S : SOMin) (p n : ℕ) (j : Fin (n+1)) :
    pYneqP p n j ∈ S.Ω (NB p n + 1) 1 (NB p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (NB p n)
    (MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j) :
      MvPolynomial (Fin (NB p n)) ℝ)
  rw [show {x : Fin (NB p n) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (yIdxP p n j) - MvPolynomial.X (y0IdxP p n j) :
          MvPolynomial (Fin (NB p n)) ℝ) ≠ 0}
      = pYneqP p n j from by
    ext z
    simp only [pYneqP, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
    constructor
    · intro hh hc; exact hh (by rw [hc]; ring)
    · intro hh hc; exact hh (by linarith)] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  exact td_sub_le (yIdxP p n j) (y0IdxP p n j)

theorem pYneP_mem (S : SOMin) (p n : ℕ) :
    pYneP p n ∈ S.Ω (NB p n + 1) (n + 1) (NB p n) := by
  have h := Work.WilG1.Omega.union_mem (S := S) (k := n+1) (a := NB p n + 1)
    (b := Polynomial.C 1) (D := 0) (fun j => pYneqP p n j)
    (fun j => by simpa using pYneqP_mem S p n j)
  refine Work.WilG1.Omega.mono h le_rfl ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C]; omega

theorem pEpsP_mem (S : SOMin) (p n : ℕ) :
    pEpsP p n ∈ S.Ω (NB p n + 3) 4 (NB p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (NB p n)
    ((MvPolynomial.X (eIdxP p n)) ^ 2 -
      (MvPolynomial.X (vIdxP p n) - MvPolynomial.X (v0IdxP p n)) ^ 2 :
        MvPolynomial (Fin (NB p n)) ℝ)
  rw [show {x : Fin (NB p n) → ℝ | MvPolynomial.eval x
        ((MvPolynomial.X (eIdxP p n)) ^ 2 -
          (MvPolynomial.X (vIdxP p n) - MvPolynomial.X (v0IdxP p n)) ^ 2 :
            MvPolynomial (Fin (NB p n)) ℝ) < 0}
      = pEpsP p n from by
    ext z
    simp only [pEpsP, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro hh <;> linarith] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have hA : ((MvPolynomial.X (eIdxP p n) : MvPolynomial (Fin (NB p n)) ℝ) ^ 2).totalDegree
      ≤ 2 := td_sq_le (le_of_eq (MvPolynomial.totalDegree_X _))
  have hB : ((MvPolynomial.X (vIdxP p n) - MvPolynomial.X (v0IdxP p n) :
      MvPolynomial (Fin (NB p n)) ℝ) ^ 2).totalDegree ≤ 2 := td_sq_le (td_sub_le _ _)
  have htd : ((MvPolynomial.X (eIdxP p n)) ^ 2 -
      (MvPolynomial.X (vIdxP p n) - MvPolynomial.X (v0IdxP p n)) ^ 2 :
        MvPolynomial (Fin (NB p n)) ℝ).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hA hB)
  omega

/-! ## 3  The big set and the chain of projections -/

/-- Format padding helper: the atoms at the small formats fit under `F + Bc0`. -/
theorem small_le (F p n : ℕ) : NB p n + 4 ≤ F + Bc0 p n := by
  simp only [Bc0, NB, W2, W1, Wp]; omega

theorem BigSetP_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    BigSetP p n A ∈ S.Ω (F + Bc0 p n + 5) (D + 10 + 5 * (n+1)) (NB p n) := by
  have h1 : pPullP p n A ∈ S.Ω (F + Bc0 p n) (D + 2) (NB p n) :=
    pPullP_mem (S := S) (hA := hA)
  have h2 : pPosEP p n ∈ S.Ω (F + Bc0 p n) 3 (NB p n) :=
    Work.WilG1.Omega.mono (pPosEP_mem S p n)
      (by simp only [Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have h3 : pRneP p n ∈ S.Ω (F + Bc0 p n) 1 (NB p n) :=
    Work.WilG1.Omega.mono (pRneP_mem S p n)
      (by simp only [Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have h4 : pSqAllP p n ∈ S.Ω (F + Bc0 p n) (4 * (n+1)) (NB p n) :=
    Work.WilG1.Omega.mono (pSqAllP_mem S p n)
      (by simp only [Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have h5 : pYneP p n ∈ S.Ω (F + Bc0 p n) (n+1) (NB p n) :=
    Work.WilG1.Omega.mono (pYneP_mem S p n)
      (by simp only [Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have h6 : pEpsP p n ∈ S.Ω (F + Bc0 p n) 4 (NB p n) :=
    Work.WilG1.Omega.mono (pEpsP_mem S p n)
      (by simp only [Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have s1 : pPullP p n A ∩ pPosEP p n ∈
      S.Ω (F + Bc0 p n + 1) (D + 2 + 3) (NB p n) :=
    Work.WilG4a.CD.inter2_same (S := S) h1 h2
  have h3' : pRneP p n ∈ S.Ω (F + Bc0 p n + 1) 1 (NB p n) :=
    Work.WilG1.Omega.mono h3 (by omega) le_rfl
  have s2 : (pPullP p n A ∩ pPosEP p n) ∩ pRneP p n ∈
      S.Ω (F + Bc0 p n + 2) ((D + 2 + 3) + 1) (NB p n) :=
    Work.WilG4a.CD.inter2_same (S := S) s1 h3'
  have h4' : pSqAllP p n ∈ S.Ω (F + Bc0 p n + 2) (4 * (n+1)) (NB p n) :=
    Work.WilG1.Omega.mono h4 (by omega) le_rfl
  have s3 : ((pPullP p n A ∩ pPosEP p n) ∩ pRneP p n) ∩ pSqAllP p n ∈
      S.Ω (F + Bc0 p n + 3) (((D + 2 + 3) + 1) + 4 * (n+1)) (NB p n) :=
    Work.WilG4a.CD.inter2_same (S := S) s2 h4'
  have h5' : pYneP p n ∈ S.Ω (F + Bc0 p n + 3) (n+1) (NB p n) :=
    Work.WilG1.Omega.mono h5 (by omega) le_rfl
  have s4 : (((pPullP p n A ∩ pPosEP p n) ∩ pRneP p n) ∩ pSqAllP p n) ∩ pYneP p n ∈
      S.Ω (F + Bc0 p n + 4) ((((D + 2 + 3) + 1) + 4 * (n+1)) + (n+1)) (NB p n) :=
    Work.WilG4a.CD.inter2_same (S := S) s3 h5'
  have h6' : pEpsP p n ∈ S.Ω (F + Bc0 p n + 4) 4 (NB p n) :=
    Work.WilG1.Omega.mono h6 (by omega) le_rfl
  have s5 : ((((pPullP p n A ∩ pPosEP p n) ∩ pRneP p n) ∩ pSqAllP p n) ∩ pYneP p n)
      ∩ pEpsP p n ∈
      S.Ω (F + Bc0 p n + 5) (((((D + 2 + 3) + 1) + 4 * (n+1)) + (n+1)) + 4) (NB p n) :=
    Work.WilG4a.CD.inter2_same (S := S) s4 h6'
  exact Work.WilG1.Omega.mono s5 (by omega) (by omega)

theorem G1P_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    G1P p n A ∈ S.Ω (F + Bg1 p n) (D + 10 + 5 * (n+1)) (W2 p n) := by
  have h := BigSetP_mem (S := S) (hA := hA)
  have h2 := Work.WilG4a.projLastIter_mem (S := S) (D := D + 10 + 5 * (n+1))
    (n := W2 p n) (m := n+2) (F := F + Bc0 p n + 5) h
  rw [G1P]
  refine Work.WilG1.Omega.mono h2 ?_ le_rfl
  simp only [Bg1, Bc0]; omega

theorem rIdx2_ne_mem (S : SOMin) (p n : ℕ) :
    {ξ : Fin (W2 p n) → ℝ | ξ (rIdx2 p n) ≠ 0} ∈ S.Ω (W2 p n + 1) 1 (W2 p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_ne S (W2 p n)
    (MvPolynomial.X (rIdx2 p n) : MvPolynomial (Fin (W2 p n)) ℝ)
  rw [show {x : Fin (W2 p n) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (rIdx2 p n) : MvPolynomial (Fin (W2 p n)) ℝ) ≠ 0}
      = {ξ : Fin (W2 p n) → ℝ | ξ (rIdx2 p n) ≠ 0} from by
    ext z; simp only [Set.mem_setOf_eq, MvPolynomial.eval_X]] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  exact le_of_eq (MvPolynomial.totalDegree_X (rIdx2 p n))

theorem KsetP_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    KsetP p n A ∈ S.Ω (F + Bg1 p n + 2) (D + 11 + 5 * (n+1)) (W2 p n) := by
  have hg := G1P_mem (S := S) (hA := hA)
  have h1 : {ξ : Fin (W2 p n) → ℝ | ξ (rIdx2 p n) ≠ 0} ∈
      S.Ω (F + Bg1 p n + 1) 1 (W2 p n) :=
    Work.WilG1.Omega.mono (rIdx2_ne_mem S p n)
      (by simp only [Bg1, Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have h2 : (G1P p n A)ᶜ ∈ S.Ω (F + Bg1 p n + 1) (D + 10 + 5 * (n+1)) (W2 p n) :=
    S.compl hg
  have hs := Work.WilG4a.CD.inter2_same (S := S) h1 h2
  exact Work.WilG1.Omega.mono hs (by omega) (by omega)

theorem P1P_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    P1P p n A ∈ S.Ω (F + Bg1 p n + 3) (D + 11 + 5 * (n+1)) (W1 p n) := by
  have h := KsetP_mem (S := S) (hA := hA)
  have hs := S.proj h
  exact Work.WilG1.Omega.mono hs (by omega) (by omega)

theorem eIdx1_pos_mem (S : SOMin) (p n : ℕ) :
    {ξ : Fin (W1 p n) → ℝ | 0 < ξ (eIdx1 p n)} ∈ S.Ω (W1 p n + 3) 3 (W1 p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (W1 p n)
    (-MvPolynomial.X (eIdx1 p n) : MvPolynomial (Fin (W1 p n)) ℝ)
  rw [show {x : Fin (W1 p n) → ℝ |
        MvPolynomial.eval x (-MvPolynomial.X (eIdx1 p n) : MvPolynomial (Fin (W1 p n)) ℝ) < 0}
      = {ξ : Fin (W1 p n) → ℝ | 0 < ξ (eIdx1 p n)} from by
    ext z
    simp only [Set.mem_setOf_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X]
    exact neg_lt_zero] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have := td_negX_le (eIdx1 p n); omega

theorem P2P_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    P2P p n A ∈ S.Ω (F + Bg1 p n + 5) (D + 14 + 5 * (n+1)) (W1 p n) := by
  have hp1 := P1P_mem (S := S) (hA := hA)
  have h1 : (P1P p n A)ᶜ ∈ S.Ω (F + Bg1 p n + 4) (D + 11 + 5 * (n+1)) (W1 p n) :=
    S.compl hp1
  have h2 : {ξ : Fin (W1 p n) → ℝ | 0 < ξ (eIdx1 p n)} ∈ S.Ω (F + Bg1 p n + 4) 3 (W1 p n) :=
    Work.WilG1.Omega.mono (eIdx1_pos_mem S p n)
      (by simp only [Bg1, Bc0, NB, W2, W1, Wp]; omega) le_rfl
  have hs : ((P1P p n A)ᶜ ∩ {ξ : Fin (W1 p n) → ℝ | 0 < ξ (eIdx1 p n)}) ∈
      S.Ω ((F + Bg1 p n + 4) + 1) ((D + 11 + 5 * (n+1)) + 3) (W1 p n) :=
    Work.WilG4a.CD.inter2_same (S := S) h1 h2
  exact Work.WilG1.Omega.mono hs (by omega) (by omega)

theorem BcP_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    BcP p n A ∈ S.Ω (F + Bg1 p n + 6) (D + 14 + 5 * (n+1)) (Wp p n) := by
  have h := P2P_mem (S := S) (hA := hA)
  have hs := S.proj h
  exact Work.WilG1.Omega.mono hs (by omega) (by omega)

theorem BsetP_mem {S : SOMin} {F D : ℕ} {A : Set (Fin (Wp p n) → ℝ)}
    (hA : A ∈ S.Ω F D (Wp p n)) :
    BsetP p n A ∈ S.Ω (F + fmtA p n) (D + degK n) (Wp p n) := by
  have h := BcP_mem (S := S) (hA := hA)
  have hc : (BcP p n A)ᶜ ∈ S.Ω (F + Bg1 p n + 6 + 1) (D + 14 + 5 * (n+1)) (Wp p n) :=
    S.compl h
  refine Work.WilG1.Omega.mono hc (by simp only [fmtA, Bg1, Bc0]; omega) ?_
  simp only [degK]; omega

end Work.WilG4c
