/-
  WilG4c / clampRel_mem — the fixed "clamp" relation `t = clamp01 s` is `Ω`-definable.

  `clampRel N ⊆ ℝ^{N+2}` is the set `z_N = clamp01 (z_{N+1})`.  It is a *semialgebraic* set
  (a union of two pieces cut out by polynomial equations and the open condition
  `0 < z_{N+1}(1 - z_{N+1})`), hence lies in every `SOMin.Ω`.  Since the relation is a fixed
  degree-`O(1)` set, the format grows at most linearly in the ambient dimension `N`; here we
  obtain the very generous bounds `N + 6` and `14` and then pad.

  The construction:
  * `I₂ = {x ∈ ℝ² | x₁ ∈ (0,1)}` is realised as the projection along the last variable of the
    hypersurface `x₂² (x₁ - x₁²) - 1 = 0`; this gives `I₂ ∈ Ω 4 4 2`.
  * The two-dimensional clamp relation is `(P ∩ I₂) ∪ (R ∩ I₂ᶜ)` for the hyperplanes
    `P = {x₀ = x₁}`, `R = {x₀ = 1/2}`, hence lies in `Ω 6 10 2`.
  * Repeatedly prepending free coordinates (`SOMin.prod_left`) moves this relation to the last
    two coordinates of `ℝ^{N+2}`, at the cost of `N` in the format and nothing in the degree.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.ClampDefs
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## 1. The open unit interval in one coordinate of `ℝ²` -/

/-- `x₂² (x₁ - x₁²) - 1` in the variables `(x₀, x₁, x₂)`; eliminating `x₂` leaves
`0 < x₁ (1 - x₁)`, i.e. `x₁ ∈ (0,1)`. -/
def qClamp : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 2 * MvPolynomial.X 2 *
      (MvPolynomial.X 1 - MvPolynomial.X 1 * MvPolynomial.X 1) - 1

theorem qClamp_totalDegree_le : qClamp.totalDegree ≤ 4 := by
  have h1 : (MvPolynomial.X (1 : Fin 3) - MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (1 : Fin 3) :
      MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 := by
    calc _ ≤ max (MvPolynomial.X (1 : Fin 3)).totalDegree
                  (MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (1 : Fin 3)).totalDegree :=
            MvPolynomial.totalDegree_sub _ _
      _ ≤ max 1 (1 + 1) := by
            apply max_le_max
            · rw [MvPolynomial.totalDegree_X]
            · calc _ ≤ (MvPolynomial.X (1 : Fin 3)).totalDegree +
                        (MvPolynomial.X (1 : Fin 3)).totalDegree := MvPolynomial.totalDegree_mul _ _
                _ = 1 + 1 := by rw [MvPolynomial.totalDegree_X]
      _ = 2 := by norm_num
  have h2 : (MvPolynomial.X (2 : Fin 3) * MvPolynomial.X (2 : Fin 3) :
      MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 := by
    calc _ ≤ (MvPolynomial.X (2 : Fin 3)).totalDegree +
              (MvPolynomial.X (2 : Fin 3)).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 2 := by rw [MvPolynomial.totalDegree_X]
  unfold qClamp
  calc (MvPolynomial.X 2 * MvPolynomial.X 2 *
          (MvPolynomial.X 1 - MvPolynomial.X 1 * MvPolynomial.X 1) - 1 :
            MvPolynomial (Fin 3) ℝ).totalDegree
      ≤ max (MvPolynomial.X 2 * MvPolynomial.X 2 *
              (MvPolynomial.X 1 - MvPolynomial.X 1 * MvPolynomial.X 1) :
                MvPolynomial (Fin 3) ℝ).totalDegree
            (1 : MvPolynomial (Fin 3) ℝ).totalDegree := MvPolynomial.totalDegree_sub _ _
    _ ≤ max (2 + 2) 0 := by
          apply max_le_max
          · exact le_trans (MvPolynomial.totalDegree_mul _ _) (add_le_add h2 h1)
          · rw [show (1 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C 1 from rfl]
            rw [MvPolynomial.totalDegree_C]
    _ = 4 := by norm_num

/-- Evaluation of `qClamp` at `Fin.snoc x t`. -/
theorem eval_qClamp {x : Fin 2 → ℝ} (t : ℝ) :
    MvPolynomial.eval (Fin.snoc x t) qClamp = t ^ 2 * (x 1 * (1 - x 1)) - 1 := by
  have h1 : (Fin.snoc x t : Fin 3 → ℝ) 1 = x 1 := by
    have h : (1 : Fin 3) = Fin.castSucc (1 : Fin 2) := by decide
    rw [h, Fin.snoc_castSucc]
  have h2 : (Fin.snoc x t : Fin 3 → ℝ) 2 = t := by
    have h : (2 : Fin 3) = Fin.last 2 := by decide
    rw [h, Fin.snoc_last]
  unfold qClamp
  simp only [map_sub, map_mul, MvPolynomial.eval_X, map_one]
  rw [h1, h2]
  ring

/-- `0 < t (1 - t)` is exactly `t ∈ (0,1)`. -/
theorem mem_Ioo_iff_mul (t : ℝ) : t ∈ Set.Ioo (0 : ℝ) 1 ↔ 0 < t * (1 - t) := by
  rw [Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; nlinarith
  · intro h
    have ht1 : t < 1 := by
      by_contra hc
      push_neg at hc
      have : t * (1 - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    have ht0 : 0 < t := by
      by_contra hc
      push_neg at hc
      have : t * (1 - t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
      linarith
    exact ⟨ht0, ht1⟩

/-- The existential quantifier over the last variable of `qClamp = 0` cuts out `x₁ ∈ (0,1)`. -/
theorem exists_eval_qClamp_eq_zero (x : Fin 2 → ℝ) :
    (∃ t : ℝ, MvPolynomial.eval (Fin.snoc x t) qClamp = 0) ↔ 0 < x 1 * (1 - x 1) := by
  have hev : ∀ t : ℝ, MvPolynomial.eval (Fin.snoc x t) qClamp =
      t ^ 2 * (x 1 * (1 - x 1)) - 1 := fun t => eval_qClamp t
  simp only [hev]
  constructor
  · rintro ⟨t, ht⟩
    have ht' : t ^ 2 * (x 1 * (1 - x 1)) = 1 := by linarith
    by_contra hcon
    push_neg at hcon
    have : t ^ 2 * (x 1 * (1 - x 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hcon
    linarith
  · intro hc
    refine ⟨(Real.sqrt (x 1 * (1 - x 1)))⁻¹, ?_⟩
    have hc0 : x 1 * (1 - x 1) ≠ 0 := ne_of_gt hc
    have hs : (Real.sqrt (x 1 * (1 - x 1))) ^ 2 = x 1 * (1 - x 1) :=
      Real.sq_sqrt (le_of_lt hc)
    rw [inv_pow, hs, inv_mul_cancel₀ hc0]
    ring

/-- The set `x₁ ∈ (0,1)` of `ℝ²`. -/
def clampI : Set (Fin 2 → ℝ) := {x | x 1 ∈ Set.Ioo (0 : ℝ) 1}

theorem clampI_mem (S : SOMin) : clampI ∈ S.Ω 4 4 2 := by
  have h := S.proj (S.hyp 3 qClamp)
  have hset : projLast {y : Fin 3 → ℝ | MvPolynomial.eval y qClamp = 0} = clampI := by
    ext x
    simp only [projLast, Set.mem_setOf_eq, clampI]
    simp only [exists_eval_qClamp_eq_zero, mem_Ioo_iff_mul]
  rw [hset] at h
  exact Work.WilG1.Omega.mono h le_rfl qClamp_totalDegree_le

/-! ## 2. The two-dimensional clamp relation -/

/-- The two-dimensional clamp relation `x₀ = clamp01 x₁`. -/
def clampTwo : Set (Fin 2 → ℝ) := {x | x 0 = clamp01 (x 1)}

/-- The hyperplane `x₀ = x₁`. -/
def clampP : Set (Fin 2 → ℝ) := {x | x 0 = x 1}

/-- The hyperplane `x₀ = 1/2`. -/
def clampR : Set (Fin 2 → ℝ) := {x | x 0 = 1 / 2}

theorem clampP_mem (S : SOMin) : clampP ∈ S.Ω 2 1 2 := by
  simpa [clampP] using Work.WilG1.Omega.coordEq_mem (S := S) 1 (0 : Fin 2) (1 : Fin 2)

theorem clampR_mem (S : SOMin) : clampR ∈ S.Ω 2 1 2 := by
  have h := S.hyp 2 (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (1 / 2) : MvPolynomial (Fin 2) ℝ)
  have hset : {x : Fin 2 → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (1 / 2) : MvPolynomial (Fin 2) ℝ) = 0} =
      clampR := by
    ext x
    simp only [clampR, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  calc (MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (1 / 2) : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ max (MvPolynomial.X (0 : Fin 2)).totalDegree
            (MvPolynomial.C (1 / 2) : MvPolynomial (Fin 2) ℝ).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ = max 1 0 := by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    _ ≤ 1 := by norm_num

theorem clampTwo_eq : clampTwo = (clampP ∩ clampI) ∪ (clampR ∩ clampIᶜ) := by
  ext x
  simp only [clampTwo, clampP, clampR, clampI, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_union, Set.mem_compl_iff]
  by_cases h : x 1 ∈ Set.Ioo (0 : ℝ) 1
  · rw [clamp01_of_mem h]
    constructor
    · intro hx; exact Or.inl ⟨hx, h⟩
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact h1
      · exact absurd h h2
  · rw [clamp01_of_not_mem h]
    constructor
    · intro hx; exact Or.inr ⟨hx, h⟩
    · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · exact absurd h2 h
      · exact h1

theorem clampTwo_mem (S : SOMin) : clampTwo ∈ S.Ω 6 10 2 := by
  have hI : clampI ∈ S.Ω 4 4 2 := clampI_mem S
  have hP : clampP ∈ S.Ω 2 1 2 := clampP_mem S
  have hR : clampR ∈ S.Ω 2 1 2 := clampR_mem S
  have hIc : clampIᶜ ∈ S.Ω 5 4 2 := S.compl hI
  have hPI : clampP ∩ clampI ∈ S.Ω 5 5 2 := by
    have hP' : clampP ∈ S.Ω 4 1 2 := Work.WilG1.Omega.mono hP (by norm_num) le_rfl
    exact Work.WilG0.Omega_inter2 hP' hI
  have hRIc : clampR ∩ clampIᶜ ∈ S.Ω 6 5 2 := by
    have hR' : clampR ∈ S.Ω 5 1 2 := Work.WilG1.Omega.mono hR (by norm_num) le_rfl
    exact Work.WilG0.Omega_inter2 hR' hIc
  have hU : (clampP ∩ clampI) ∪ (clampR ∩ clampIᶜ) ∈ S.Ω 6 10 2 := by
    have hPI' : clampP ∩ clampI ∈ S.Ω 6 5 2 := Work.WilG1.Omega.mono hPI (by norm_num) le_rfl
    exact Work.WilG0.Omega_union2 hPI' hRIc
  rw [clampTwo_eq]
  exact hU

/-! ## 3. Lifting to `ℝ^{N+2}` by prepending free coordinates -/

/-- `clampLift k` is the copy of the clamp relation whose two constrained coordinates are the
last two of `ℝ^{k+2}`. -/
def clampLift (k : ℕ) : Set (Fin (k + 2) → ℝ) :=
  {z | z (Fin.castSucc (Fin.last k)) = clamp01 (z (Fin.last (k + 1)))}

theorem clampLift_zero : clampLift 0 = clampTwo := by
  ext z
  simp only [clampLift, clampTwo, Set.mem_setOf_eq]
  have h1 : (Fin.castSucc (Fin.last 0) : Fin (0 + 2)) = (0 : Fin (0 + 2)) := by decide
  have h2 : (Fin.last 1 : Fin (0 + 2)) = (1 : Fin (0 + 2)) := by decide
  rw [h1, h2]

/-- `Fin.tail` application, in a form usable as a rewrite rule. -/
theorem tail_apply {k : ℕ} (z : Fin (k + 3) → ℝ) (i : Fin (k + 2)) :
    Fin.tail z i = z i.succ := by
  have h : Fin.tail (fun j : Fin (k + 3) => z j) = fun j : Fin (k + 2) => z j.succ :=
    Fin.tail_def
  simpa using congrFun h i

theorem clampLift_succ (k : ℕ) :
    clampLift (k + 1) = {z : Fin (k + 3) → ℝ | Fin.tail z ∈ clampLift k} := by
  ext z
  simp only [clampLift, Set.mem_setOf_eq]
  rw [tail_apply z (Fin.castSucc (Fin.last k)), tail_apply z (Fin.last (k + 1))]
  simp only [Fin.succ_castSucc, Fin.succ_last]

theorem clampLift_mem (S : SOMin) : ∀ k : ℕ, clampLift k ∈ S.Ω (6 + k) 10 (k + 2) := by
  intro k
  induction k with
  | zero =>
      rw [clampLift_zero]
      exact clampTwo_mem S
  | succ k ih =>
      have h := S.prod_left ih
      rw [clampLift_succ k]
      exact h

theorem clampRel_mem (S : WilkiesDesign.SOMin) (N : ℕ) :
    Work.WilG4c.clampRel N ∈ S.Ω (N + 20) 30 (N + 2) := by
  exact Work.WilG1.Omega.mono (clampLift_mem S N) (by omega) (by omega)

end Work.WilG4c
