import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.FibreBallMemDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign

/-! ## 1  The constants -/

/-- The format charged by one substitution atom (`Work.WilG4a.subst_mem`). -/
def fbC1 (p n : ℕ) : ℕ := 2 * (FBN p n + FBa p n) + 2

/-- A format bound covering all the small polynomial atoms. -/
def fbM (p n : ℕ) : ℕ := fbC1 p n + FBN p n + FBa p n + FBk n + 20

/-- The format constant `A` of the main theorem. -/
def FBA (p n : ℕ) : ℕ := fbM p n + 7 + 2 * FBk n

/-- The degree constant `C` of the main theorem. -/
def FBC (p n : ℕ) : ℕ := 8 + 4 * FBk n

/-! ## 2  The polynomial atoms -/

/-- `ε > 0` in the big space. -/
theorem fbPosE_mem (S : SOMin) (p n : ℕ) :
    {z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)} ∈ S.Ω (FBN p n + 3) 3 (FBN p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (FBN p n)
    (-MvPolynomial.X (fbE p n) : MvPolynomial (Fin (FBN p n)) ℝ)
  have hset : {x : Fin (FBN p n) → ℝ | MvPolynomial.eval x
        (-MvPolynomial.X (fbE p n) : MvPolynomial (Fin (FBN p n)) ℝ) < 0}
      = {z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X,
      neg_lt_zero]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]

/-- The squared ball condition `(y j - y₀ j)² < ε²`. -/
theorem fbSq_mem (S : SOMin) (p n : ℕ) (j : Fin (FBk n)) :
    {z : Fin (FBN p n) → ℝ | (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2}
      ∈ S.Ω (FBN p n + 3) 4 (FBN p n) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (FBN p n)
    ((MvPolynomial.X (fbY p n j) - MvPolynomial.X (fbY0 p n j)) ^ 2 -
      (MvPolynomial.X (fbE p n)) ^ 2 : MvPolynomial (Fin (FBN p n)) ℝ)
  have hset : {x : Fin (FBN p n) → ℝ | MvPolynomial.eval x
        ((MvPolynomial.X (fbY p n j) - MvPolynomial.X (fbY0 p n j)) ^ 2 -
          (MvPolynomial.X (fbE p n)) ^ 2 : MvPolynomial (Fin (FBN p n)) ℝ) < 0}
      = {z : Fin (FBN p n) → ℝ |
          (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    constructor <;> intro hh <;> linarith
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  have h1 : ((MvPolynomial.X (fbY p n j) - MvPolynomial.X (fbY0 p n j) :
      MvPolynomial (Fin (FBN p n)) ℝ) ^ 2).totalDegree ≤ 2 :=
    Work.WilG4c.td_sq_le (Work.WilG4c.td_sub_le (fbY p n j) (fbY0 p n j))
  have h2 : ((MvPolynomial.X (fbE p n) : MvPolynomial (Fin (FBN p n)) ℝ) ^ 2).totalDegree ≤ 2 :=
    Work.WilG4c.td_sq_le (le_of_eq (MvPolynomial.totalDegree_X _))
  have h3 : ((MvPolynomial.X (fbY p n j) - MvPolynomial.X (fbY0 p n j)) ^ 2 -
      (MvPolynomial.X (fbE p n)) ^ 2 : MvPolynomial (Fin (FBN p n)) ℝ).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le h1 h2)
  omega

/-- `ε > 0` in the space `(w, y₀, ε)`. -/
theorem fbPosE1_mem (S : SOMin) (p n : ℕ) :
    {ξ : Fin (FBa p n + FBk n + 1) → ℝ | 0 < ξ (fbE1 p n)}
      ∈ S.Ω (FBa p n + FBk n + 1 + 3) 3 (FBa p n + FBk n + 1) := by
  have h := Work.WilkiesH.Omega.omega_poly_lt S (FBa p n + FBk n + 1)
    (-MvPolynomial.X (fbE1 p n) : MvPolynomial (Fin (FBa p n + FBk n + 1)) ℝ)
  have hset : {x : Fin (FBa p n + FBk n + 1) → ℝ | MvPolynomial.eval x
        (-MvPolynomial.X (fbE1 p n) : MvPolynomial (Fin (FBa p n + FBk n + 1)) ℝ) < 0}
      = {ξ : Fin (FBa p n + FBk n + 1) → ℝ | 0 < ξ (fbE1 p n)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_neg, MvPolynomial.eval_X,
      neg_lt_zero]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]

/-! ## 3  The `Ω`-chain -/

/-- The big bad set is `Ω`-definable. -/
theorem FB_bad_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    FibreBallBad p n V ∈ S.Ω (F + fbM p n + 3) (D + 5 + 4 * FBk n) (FBN p n) := by
  -- the pullback of `Vᶜ` along the coordinate map `fbSigma`
  have hVc : Vᶜ ∈ S.Ω (F + 1) D (FBa p n) := S.compl hV
  have hNotV : {z : Fin (FBN p n) → ℝ |
      (fun j : Fin (FBa p n) => z (fbSigma p n j)) ∈ Vᶜ}
      ∈ S.Ω (F + fbC1 p n) (D + 2) (FBN p n) := by
    have h := Work.WilG4a.subst_mem S (fbSigma p n) hVc
    have h2 : (F + 1) + 2 * (FBN p n + FBa p n) + 1 = F + fbC1 p n := by
      simp only [fbC1]; ring
    rwa [h2] at h
  -- the two polynomial atoms, raised to the common format `F + fbM`
  have hPos : {z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)}
      ∈ S.Ω (F + fbM p n) 3 (FBN p n) :=
    Work.WilG1.Omega.mono (fbPosE_mem S p n)
      (by simp only [fbM, fbC1, FBN, FBa, FBk]; omega) le_rfl
  have hSqJ : ∀ j : Fin (FBk n), {z : Fin (FBN p n) → ℝ |
      (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2}
      ∈ S.Ω (F + fbM p n) 4 (FBN p n) := fun j =>
    Work.WilG1.Omega.mono (fbSq_mem S p n j)
      (by simp only [fbM, fbC1, FBN, FBa, FBk]; omega) le_rfl
  have hSqAll : (⋂ j : Fin (FBk n), {z : Fin (FBN p n) → ℝ |
      (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2})
      ∈ S.Ω (F + fbM p n + 1) (FBk n * 4) (FBN p n) := by
    have h := S.inter (F := F + fbM p n) (D := fun _ : Fin (FBk n) => (4 : ℕ))
      (A := fun j : Fin (FBk n) => {z : Fin (FBN p n) → ℝ |
        (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2}) hSqJ
    have hsum : (∑ _ : Fin (FBk n), (4 : ℕ)) = FBk n * 4 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    rwa [hsum] at h
  have hSub : ({z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)} ∩
      (⋂ j : Fin (FBk n), {z : Fin (FBN p n) → ℝ |
        (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2}))
      ∈ S.Ω (F + fbM p n + 2) (3 + FBk n * 4) (FBN p n) := by
    have h1 : {z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)}
        ∈ S.Ω (F + fbM p n + 1) 3 (FBN p n) :=
      Work.WilG1.Omega.mono hPos (by omega) le_rfl
    exact Work.WilG1.Omega.mono (Work.WilG4a.CD.inter2_same (S := S) h1 hSqAll)
      (by omega) (by omega)
  have hNotV2 : {z : Fin (FBN p n) → ℝ |
      (fun j : Fin (FBa p n) => z (fbSigma p n j)) ∈ Vᶜ}
      ∈ S.Ω (F + fbM p n + 2) (D + 2) (FBN p n) :=
    Work.WilG1.Omega.mono hNotV (by simp only [fbM, fbC1, FBN, FBa, FBk]; omega) le_rfl
  have hset : (({z : Fin (FBN p n) → ℝ | 0 < z (fbE p n)} ∩
        (⋂ j : Fin (FBk n), {z : Fin (FBN p n) → ℝ |
          (z (fbY p n j) - z (fbY0 p n j)) ^ 2 < (z (fbE p n)) ^ 2})) ∩
        {z : Fin (FBN p n) → ℝ |
          (fun j : Fin (FBa p n) => z (fbSigma p n j)) ∈ Vᶜ})
      = FibreBallBad p n V := by
    ext z
    simp only [FibreBallBad, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff]
    tauto
  rw [← hset]
  exact Work.WilG1.Omega.mono (Work.WilG4a.CD.inter2_same (S := S) hSub hNotV2)
    (by omega) (by omega)

/-- Forgetting the running point. -/
theorem FB_D1_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    FB_D1 p n V ∈ S.Ω (F + fbM p n + 3 + FBk n) (D + 5 + 4 * FBk n)
      (FBa p n + FBk n + 1) := by
  have h := FB_bad_mem S p n F D V hV
  have h2 := Work.WilG4a.projLastIter_mem (S := S) (D := D + 5 + 4 * FBk n)
    (n := FBa p n + FBk n + 1) (m := FBk n) (F := F + fbM p n + 3) h
  exact Work.WilG1.Omega.mono h2 le_rfl le_rfl

/-- The negation step. -/
theorem FB_D2_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    FB_D2 p n V ∈ S.Ω (F + fbM p n + 5 + FBk n) (D + 8 + 4 * FBk n)
      (FBa p n + FBk n + 1) := by
  have hD1 := FB_D1_mem S p n F D V hV
  have hD1c : (FB_D1 p n V)ᶜ ∈ S.Ω (F + fbM p n + 4 + FBk n) (D + 5 + 4 * FBk n)
      (FBa p n + FBk n + 1) :=
    Work.WilG1.Omega.mono (S.compl hD1) (by omega) le_rfl
  have hPos1 : {ξ : Fin (FBa p n + FBk n + 1) → ℝ | 0 < ξ (fbE1 p n)}
      ∈ S.Ω (F + fbM p n + 4 + FBk n) 3 (FBa p n + FBk n + 1) :=
    Work.WilG1.Omega.mono (fbPosE1_mem S p n)
      (by simp only [fbM, fbC1, FBN, FBa, FBk]; omega) le_rfl
  have hset : ({ξ : Fin (FBa p n + FBk n + 1) → ℝ | 0 < ξ (fbE1 p n)} ∩
      (FB_D1 p n V)ᶜ) = FB_D2 p n V := rfl
  rw [← hset]
  exact Work.WilG1.Omega.mono (Work.WilG4a.CD.inter2_same (S := S) hPos1 hD1c)
    (by omega) (by omega)

/-- Forgetting the radius. -/
theorem FB_D3_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    FB_D3 p n V ∈ S.Ω (F + fbM p n + 6 + FBk n) (D + 8 + 4 * FBk n) (FBa p n + FBk n) := by
  have h := FB_D2_mem S p n F D V hV
  exact Work.WilG1.Omega.mono (S.proj h) (by omega) le_rfl

/-- Forgetting the centre. -/
theorem FB_W_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    FB_W p n V ∈ S.Ω (F + fbM p n + 6 + 2 * FBk n) (D + 8 + 4 * FBk n) (FBa p n) := by
  have h := FB_D3_mem S p n F D V hV
  have h2 := Work.WilG4a.projLastIter_mem (S := S) (D := D + 8 + 4 * FBk n)
    (n := FBa p n) (m := FBk n) (F := F + fbM p n + 6 + FBk n) h
  exact Work.WilG1.Omega.mono h2 (by omega) le_rfl

/-- Re-attaching the unused last coordinate. -/
theorem FB_prod_mem (S : SOMin) (p n F D : ℕ) (V : Set (Fin (FBa p n) → ℝ))
    (hV : V ∈ S.Ω F D (FBa p n)) :
    {z : Fin (FBa p n + 1) → ℝ | Fin.init z ∈ FB_W p n V}
      ∈ S.Ω (F + FBA p n) (D + FBC p n) (FBa p n + 1) := by
  have h := FB_W_mem S p n F D V hV
  exact Work.WilG1.Omega.mono (S.prod_right h)
    (by simp only [FBA, fbM, fbC1, FBN, FBa, FBk]; omega)
    (by simp only [FBC, FBk]; omega)

/-! ## 4  The semantics of the chain -/

section Semantics

variable {p n : ℕ}

lemma fbW_eq (i : Fin (FBa p n)) :
    fbW p n i = Fin.castAdd (FBk n) (Fin.castSucc (Fin.castAdd (FBk n) i)) := by
  apply Fin.ext
  simp only [fbW, Fin.val_mk, Fin.val_castAdd, Fin.val_castSucc]

lemma fbY0_eq (i : Fin (FBk n)) :
    fbY0 p n i = Fin.castAdd (FBk n) (Fin.castSucc (Fin.natAdd (FBa p n) i)) := by
  apply Fin.ext
  simp only [fbY0, Fin.val_mk, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd]

lemma fbE_eq : fbE p n = Fin.castAdd (FBk n) (Fin.last (FBa p n + FBk n)) := by
  apply Fin.ext
  simp only [fbE, Fin.val_mk, Fin.val_castAdd, Fin.val_last]

lemma fbY_eq (i : Fin (FBk n)) :
    fbY p n i = Fin.natAdd (FBa p n + FBk n + 1) i := by
  apply Fin.ext
  simp only [fbY, Fin.val_mk, Fin.val_natAdd]

lemma fbE1_eq : fbE1 p n = Fin.last (FBa p n + FBk n) := by
  apply Fin.ext
  simp only [fbE1, Fin.val_mk, Fin.val_last]

lemma fbBig_w (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) (i : Fin (FBa p n)) :
    fbBig p n w y₀ ε y (fbW p n i) = w i := by
  rw [fbW_eq, fbBig, Fin.append_left, Fin.snoc_castSucc, Fin.append_left]

lemma fbBig_y0 (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) (i : Fin (FBk n)) :
    fbBig p n w y₀ ε y (fbY0 p n i) = y₀ i := by
  rw [fbY0_eq, fbBig, Fin.append_left, Fin.snoc_castSucc, Fin.append_right]

lemma fbBig_e (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) :
    fbBig p n w y₀ ε y (fbE p n) = ε := by
  rw [fbE_eq, fbBig, Fin.append_left, Fin.snoc_last]

lemma fbBig_y (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) (i : Fin (FBk n)) :
    fbBig p n w y₀ ε y (fbY p n i) = y i := by
  rw [fbY_eq, fbBig, Fin.append_right]

lemma fbBig_sigma (w : Fin (FBa p n) → ℝ) (y₀ : Fin (FBk n) → ℝ) (ε : ℝ)
    (y : Fin (FBk n) → ℝ) :
    (fun j : Fin (FBa p n) => fbBig p n w y₀ ε y (fbSigma p n j)) = fibPt w y := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hsig : fbSigma p n (Fin.castAdd (FBk n) i) = fbW p n (Fin.castAdd (FBk n) i) := by
      rw [fbSigma, dif_pos (by simp only [Fin.val_castAdd]; exact i.isLt)]
      apply Fin.ext
      simp only [fbW, Fin.val_mk]
    rw [hsig, fbBig_w, fibPt, Fin.append_left, parPt_apply]
  · have hsig : fbSigma p n (Fin.natAdd p i) = fbY p n i := by
      rw [fbSigma, dif_neg (by simp only [Fin.val_natAdd]; omega)]
      apply Fin.ext
      simp only [fbY, Fin.val_mk, Fin.val_natAdd]
      omega
    rw [hsig, fbBig_y, fibPt, Fin.append_right]

/-- The membership of a `fbBig` point in the big bad set, in semantic form. -/
lemma fbBig_mem_Bad_iff (V : Set (Fin (FBa p n) → ℝ)) (w : Fin (FBa p n) → ℝ)
    (y₀ : Fin (FBk n) → ℝ) (ε : ℝ) (y : Fin (FBk n) → ℝ) :
    fbBig p n w y₀ ε y ∈ FibreBallBad p n V ↔ 0 < ε ∧ dist y y₀ < ε ∧ fibPt w y ∉ V := by
  simp only [FibreBallBad, Set.mem_ofPred_eq, fbBig_e w y₀ ε y, fbBig_sigma w y₀ ε y,
    fbBig_y w y₀ ε y, fbBig_y0 w y₀ ε y]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rw [dist_pi_lt_iff h1]
    intro j
    have hj := sq_lt_sq.mp (h2 j)
    rw [Real.dist_eq]
    rwa [abs_of_pos h1] at hj
  · rintro ⟨h1, hd, h3⟩
    refine ⟨h1, fun j => ?_, h3⟩
    have hj : dist (y j) (y₀ j) < ε := (dist_pi_lt_iff h1).mp hd j
    rw [Real.dist_eq] at hj
    rw [sq_lt_sq, abs_of_pos h1]
    exact hj

/-- **The chain computes the fibre-ball condition.** -/
theorem FB_W_eq_Sem (V : Set (Fin (FBa p n) → ℝ)) : FB_W p n V = FB_Sem p n V := by
  ext w
  rw [FB_W, Work.WilG0.projLastIter_eq, Set.mem_ofPred_eq]
  simp only [Work.WilG4c.snocIt_append]
  constructor
  · rintro ⟨y₀, hy₀⟩
    rw [FB_D3, WilkiesDesign.projLast, Set.mem_ofPred_eq] at hy₀
    obtain ⟨ε, hε⟩ := hy₀
    rw [FB_D2, Set.mem_inter_iff] at hε
    obtain ⟨hε1, hε2⟩ := hε
    rw [Set.mem_ofPred_eq] at hε1
    rw [Set.mem_compl_iff] at hε2
    rw [FB_D1, Work.WilG0.projLastIter_eq, Set.mem_ofPred_eq, not_exists] at hε2
    have hε1' : 0 < ε := by
      simpa only [fbE1_eq, Fin.snoc_last] using hε1
    refine ⟨y₀, ε, hε1', fun y hy => ?_⟩
    have hnot : fbBig p n w y₀ ε y ∉ FibreBallBad p n V := by
      have h := hε2 y
      rwa [Work.WilG4c.snocIt_append, ← fbBig] at h
    rw [fbBig_mem_Bad_iff] at hnot
    by_contra hVc
    exact hnot ⟨hε1', hy, hVc⟩
  · rintro ⟨y₀, ε, hε1, hball⟩
    refine ⟨y₀, ?_⟩
    rw [FB_D3, WilkiesDesign.projLast, Set.mem_ofPred_eq]
    refine ⟨ε, ?_⟩
    rw [FB_D2, Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_ofPred_eq, fbE1_eq, Fin.snoc_last]
      exact hε1
    · rw [Set.mem_compl_iff, FB_D1, Work.WilG0.projLastIter_eq, Set.mem_ofPred_eq, not_exists]
      intro y
      rw [Work.WilG4c.snocIt_append, ← fbBig, fbBig_mem_Bad_iff]
      rintro ⟨_, hd, hVc⟩
      exact hVc (hball y hd)

end Semantics

/-! ## 5  The main theorem -/

theorem FibreBallMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (V : Set (Fin (p + (n + 1)) → ℝ)),
      V ∈ S.Ω F D (p + (n + 1)) →
      {z : Fin (p + (n + 1) + 1) → ℝ |
        ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
          ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε →
            Work.WilkG4c.fibPt (Fin.init z) y ∈ V}
      ∈ S.Ω (F + A) (D + C) (p + (n + 1) + 1) := by
  refine ⟨FBA p n, FBC p n, fun F D V hV => ?_⟩
  have h := FB_prod_mem S p n F D V hV
  have hset : {z : Fin (FBa p n + 1) → ℝ | Fin.init z ∈ FB_W p n V}
      = {z : Fin (p + (n + 1) + 1) → ℝ |
          ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
            ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε →
              Work.WilkG4c.fibPt (Fin.init z) y ∈ V} := by
    rw [FB_W_eq_Sem]
    rfl
  rw [hset] at h
  exact h

end Work.WilkG4c

/-! ## 6  The module-path alias

The workspace convention "module `Submission.Work.X.Y` ↔ namespace `Work.X`" attaches the name
`Work.WilG4c.FibreBallMem` to this module (the verifier looks the theorem up under the name
derived from the file path).  The statement as requested lives in the namespace `Work.WilkG4c`
used by the rest of this area; we expose it under both names. -/

namespace Work.WilG4c

/-- Alias of `Work.WilkG4c.FibreBallMem` under the module-path namespace. -/
theorem FibreBallMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (V : Set (Fin (p + (n + 1)) → ℝ)),
      V ∈ S.Ω F D (p + (n + 1)) →
      {z : Fin (p + (n + 1) + 1) → ℝ |
        ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
          ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε →
            Work.WilkG4c.fibPt (Fin.init z) y ∈ V}
      ∈ S.Ω (F + A) (D + C) (p + (n + 1) + 1) :=
  Work.WilkG4c.FibreBallMem S p n

end Work.WilG4c
