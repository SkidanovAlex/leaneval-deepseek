/-
  WilG1 / Thin / oneDim_pred

  The four one-sided oscillation predicates `RHi`, `RLo`, `LHi`, `LLo`, their description by
  the `OShape` formula `sShp`, and the resulting `Ω`-membership of `oscR g q` and `oscL g q`.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.bad_covered
import Submission.Work.WilG1.Thin.oneDim_shape

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture Work.WilG1 WilkiesDesign.CG

/-! ## The four predicates -/

/-- Right quotients exceed `q` frequently. -/
def RHi (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ q * (y - x) < g y - g x}

/-- Right quotients fall below `q` frequently. -/
def RLo (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ g y - g x < q * (y - x)}

/-- Left quotients exceed `q` frequently. -/
def LHi (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ g y - g x < q * (y - x)}

/-- Left quotients fall below `q` frequently. -/
def LLo (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ q * (y - x) < g y - g x}

theorem oscR_eq (g : ℝ → ℝ) (q : ℝ) : oscR g q = RHi g q ∩ RLo g q := by
  ext x
  simp only [oscR, RHi, RLo, Set.mem_ofPred_eq, Set.mem_inter_iff, dq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h1 δ hδ
        exact ⟨y, hy1, hy2, (lt_div_iff₀ (by linarith)).mp hy3⟩,
      fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h2 δ hδ
        exact ⟨y, hy1, hy2, (div_lt_iff₀ (by linarith)).mp hy3⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h1 δ hδ
        exact ⟨y, hy1, hy2, (lt_div_iff₀ (by linarith)).mpr hy3⟩,
      fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h2 δ hδ
        exact ⟨y, hy1, hy2, (div_lt_iff₀ (by linarith)).mpr hy3⟩⟩

theorem oscL_eq (g : ℝ → ℝ) (q : ℝ) : oscL g q = LHi g q ∩ LLo g q := by
  ext x
  simp only [oscL, LHi, LLo, Set.mem_ofPred_eq, Set.mem_inter_iff, dq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h1 δ hδ
        exact ⟨y, hy1, hy2, (lt_div_iff_of_neg (by linarith)).mp hy3⟩,
      fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h2 δ hδ
        exact ⟨y, hy1, hy2, (div_lt_iff_of_neg (by linarith)).mp hy3⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h1 δ hδ
        exact ⟨y, hy1, hy2, (lt_div_iff_of_neg (by linarith)).mpr hy3⟩,
      fun δ hδ => by
        obtain ⟨y, hy1, hy2, hy3⟩ := h2 δ hδ
        exact ⟨y, hy1, hy2, (div_lt_iff_of_neg (by linarith)).mpr hy3⟩⟩

/-! ## The four characteristic predicates -/

theorem sIn_RHi (g : ℝ → ℝ) (q : ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    sIn (graphOf (fun x : Fin 1 → ℝ => g (x 0))) PRp (PS1p q) w δ ↔
      ∃ y : ℝ, w 0 < y ∧ y < w 0 + δ ∧ q * (y - w 0) < g y - g (w 0) := by
  unfold sIn
  constructor
  · rintro ⟨r, hA, hB, h1, h2⟩
    rw [graphA_iff] at hA
    rw [graphB_iff] at hB
    rw [eval_PRp] at h1
    rw [eval_PS1p] at h2
    have hpos : 0 < (r 0 - w 0) * (δ - (r 0 - w 0)) := by
      nlinarith [sq_nonneg (r 3), h1]
    have hyx : 0 < r 0 - w 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hpos2 : 0 < (r 2 - r 1) - q * (r 0 - w 0) := by
      nlinarith [sq_nonneg (r 4), h2]
    have hlt : r 0 - w 0 < δ := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ⟨r 0, by linarith, by linarith, by linarith⟩
  · rintro ⟨y, hy1, hy2, hy3⟩
    have hA : 0 < y - w 0 := by linarith
    have hB : 0 < δ - (y - w 0) := by linarith
    have hC : 0 < (g y - g (w 0)) - q * (y - w 0) := by linarith
    refine ⟨mk5 y (g (w 0)) (g y) (Real.sqrt ((y - w 0) * (δ - (y - w 0))))⁻¹
      (Real.sqrt ((g y - g (w 0)) - q * (y - w 0)))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [graphA_iff]; simp [mk5_one]
    · rw [graphB_iff]; simp [mk5_zero, mk5_two]
    · rw [eval_PRp]
      simp only [mk5_zero, mk5_three]
      have hsq : Real.sqrt ((y - w 0) * (δ - (y - w 0))) ^ 2
          = (y - w 0) * (δ - (y - w 0)) := Real.sq_sqrt (le_of_lt (mul_pos hA hB))
      have hne : (y - w 0) * (δ - (y - w 0)) ≠ 0 := ne_of_gt (mul_pos hA hB)
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring
    · rw [eval_PS1p]
      simp only [mk5_zero, mk5_one, mk5_two, mk5_four]
      have hsq : Real.sqrt ((g y - g (w 0)) - q * (y - w 0)) ^ 2
          = (g y - g (w 0)) - q * (y - w 0) := Real.sq_sqrt (le_of_lt hC)
      have hne : (g y - g (w 0)) - q * (y - w 0) ≠ 0 := ne_of_gt hC
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring

theorem sIn_RLo (g : ℝ → ℝ) (q : ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    sIn (graphOf (fun x : Fin 1 → ℝ => g (x 0))) PRp (PS2p q) w δ ↔
      ∃ y : ℝ, w 0 < y ∧ y < w 0 + δ ∧ g y - g (w 0) < q * (y - w 0) := by
  unfold sIn
  constructor
  · rintro ⟨r, hA, hB, h1, h2⟩
    rw [graphA_iff] at hA
    rw [graphB_iff] at hB
    rw [eval_PRp] at h1
    rw [eval_PS2p] at h2
    have hpos : 0 < (r 0 - w 0) * (δ - (r 0 - w 0)) := by
      nlinarith [sq_nonneg (r 3), h1]
    have hyx : 0 < r 0 - w 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hpos2 : 0 < q * (r 0 - w 0) - (r 2 - r 1) := by
      nlinarith [sq_nonneg (r 4), h2]
    have hlt : r 0 - w 0 < δ := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ⟨r 0, by linarith, by linarith, by linarith⟩
  · rintro ⟨y, hy1, hy2, hy3⟩
    have hA : 0 < y - w 0 := by linarith
    have hB : 0 < δ - (y - w 0) := by linarith
    have hC : 0 < q * (y - w 0) - (g y - g (w 0)) := by linarith
    refine ⟨mk5 y (g (w 0)) (g y) (Real.sqrt ((y - w 0) * (δ - (y - w 0))))⁻¹
      (Real.sqrt (q * (y - w 0) - (g y - g (w 0))))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [graphA_iff]; simp [mk5_one]
    · rw [graphB_iff]; simp [mk5_zero, mk5_two]
    · rw [eval_PRp]
      simp only [mk5_zero, mk5_three]
      have hsq : Real.sqrt ((y - w 0) * (δ - (y - w 0))) ^ 2
          = (y - w 0) * (δ - (y - w 0)) := Real.sq_sqrt (le_of_lt (mul_pos hA hB))
      have hne : (y - w 0) * (δ - (y - w 0)) ≠ 0 := ne_of_gt (mul_pos hA hB)
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring
    · rw [eval_PS2p]
      simp only [mk5_zero, mk5_one, mk5_two, mk5_four]
      have hsq : Real.sqrt (q * (y - w 0) - (g y - g (w 0))) ^ 2
          = q * (y - w 0) - (g y - g (w 0)) := Real.sq_sqrt (le_of_lt hC)
      have hne : q * (y - w 0) - (g y - g (w 0)) ≠ 0 := ne_of_gt hC
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring

theorem sIn_LHi (g : ℝ → ℝ) (q : ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    sIn (graphOf (fun x : Fin 1 → ℝ => g (x 0))) PLp (PS2p q) w δ ↔
      ∃ y : ℝ, w 0 - δ < y ∧ y < w 0 ∧ g y - g (w 0) < q * (y - w 0) := by
  unfold sIn
  constructor
  · rintro ⟨r, hA, hB, h1, h2⟩
    rw [graphA_iff] at hA
    rw [graphB_iff] at hB
    rw [eval_PLp] at h1
    rw [eval_PS2p] at h2
    have hpos : 0 < (w 0 - r 0) * (δ - (w 0 - r 0)) := by
      nlinarith [sq_nonneg (r 3), h1]
    have hyx : 0 < w 0 - r 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hpos2 : 0 < q * (r 0 - w 0) - (r 2 - r 1) := by
      nlinarith [sq_nonneg (r 4), h2]
    have hlt : w 0 - r 0 < δ := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ⟨r 0, by linarith, by linarith, by linarith⟩
  · rintro ⟨y, hy1, hy2, hy3⟩
    have hA : 0 < w 0 - y := by linarith
    have hB : 0 < δ - (w 0 - y) := by linarith
    have hC : 0 < q * (y - w 0) - (g y - g (w 0)) := by linarith
    refine ⟨mk5 y (g (w 0)) (g y) (Real.sqrt ((w 0 - y) * (δ - (w 0 - y))))⁻¹
      (Real.sqrt (q * (y - w 0) - (g y - g (w 0))))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [graphA_iff]; simp [mk5_one]
    · rw [graphB_iff]; simp [mk5_zero, mk5_two]
    · rw [eval_PLp]
      simp only [mk5_zero, mk5_three]
      have hsq : Real.sqrt ((w 0 - y) * (δ - (w 0 - y))) ^ 2
          = (w 0 - y) * (δ - (w 0 - y)) := Real.sq_sqrt (le_of_lt (mul_pos hA hB))
      have hne : (w 0 - y) * (δ - (w 0 - y)) ≠ 0 := ne_of_gt (mul_pos hA hB)
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring
    · rw [eval_PS2p]
      simp only [mk5_zero, mk5_one, mk5_two, mk5_four]
      have hsq : Real.sqrt (q * (y - w 0) - (g y - g (w 0))) ^ 2
          = q * (y - w 0) - (g y - g (w 0)) := Real.sq_sqrt (le_of_lt hC)
      have hne : q * (y - w 0) - (g y - g (w 0)) ≠ 0 := ne_of_gt hC
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring

theorem sIn_LLo (g : ℝ → ℝ) (q : ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    sIn (graphOf (fun x : Fin 1 → ℝ => g (x 0))) PLp (PS1p q) w δ ↔
      ∃ y : ℝ, w 0 - δ < y ∧ y < w 0 ∧ q * (y - w 0) < g y - g (w 0) := by
  unfold sIn
  constructor
  · rintro ⟨r, hA, hB, h1, h2⟩
    rw [graphA_iff] at hA
    rw [graphB_iff] at hB
    rw [eval_PLp] at h1
    rw [eval_PS1p] at h2
    have hpos : 0 < (w 0 - r 0) * (δ - (w 0 - r 0)) := by
      nlinarith [sq_nonneg (r 3), h1]
    have hyx : 0 < w 0 - r 0 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hpos2 : 0 < (r 2 - r 1) - q * (r 0 - w 0) := by
      nlinarith [sq_nonneg (r 4), h2]
    have hlt : w 0 - r 0 < δ := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact ⟨r 0, by linarith, by linarith, by linarith⟩
  · rintro ⟨y, hy1, hy2, hy3⟩
    have hA : 0 < w 0 - y := by linarith
    have hB : 0 < δ - (w 0 - y) := by linarith
    have hC : 0 < (g y - g (w 0)) - q * (y - w 0) := by linarith
    refine ⟨mk5 y (g (w 0)) (g y) (Real.sqrt ((w 0 - y) * (δ - (w 0 - y))))⁻¹
      (Real.sqrt ((g y - g (w 0)) - q * (y - w 0)))⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [graphA_iff]; simp [mk5_one]
    · rw [graphB_iff]; simp [mk5_zero, mk5_two]
    · rw [eval_PLp]
      simp only [mk5_zero, mk5_three]
      have hsq : Real.sqrt ((w 0 - y) * (δ - (w 0 - y))) ^ 2
          = (w 0 - y) * (δ - (w 0 - y)) := Real.sq_sqrt (le_of_lt (mul_pos hA hB))
      have hne : (w 0 - y) * (δ - (w 0 - y)) ≠ 0 := ne_of_gt (mul_pos hA hB)
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring
    · rw [eval_PS1p]
      simp only [mk5_zero, mk5_one, mk5_two, mk5_four]
      have hsq : Real.sqrt ((g y - g (w 0)) - q * (y - w 0)) ^ 2
          = (g y - g (w 0)) - q * (y - w 0) := Real.sq_sqrt (le_of_lt hC)
      have hne : (g y - g (w 0)) - q * (y - w 0) ≠ 0 := ne_of_gt hC
      rw [inv_pow, hsq, inv_mul_cancel₀ hne]
      ring

/-! ## `Ω`-membership -/

/-- The degree of the shape, as a polynomial in `D`. -/
def bP (P1' P2' : MvPolynomial (Fin 7) ℝ) : Polynomial ℕ :=
  Polynomial.C (sPol.totalDegree + 4 + P1'.totalDegree + P2'.totalDegree) +
    Polynomial.C 2 * Polynomial.X

theorem bP_eval (X : Set (Fin 2 → ℝ)) (D : ℕ) (P1' P2' : MvPolynomial (Fin 7) ℝ) :
    (bP P1' P2').eval D = sShp.deg (sData X D P1' P2') := by
  simp only [bP, sData, sShp, sBody, sBlk, sPos, OShape.deg, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The `Good` condition of the shape, from the graph membership. -/
theorem sGood {S : WilkiesDesign.SOMin} {F D : ℕ} {g : ℝ → ℝ}
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2)
    (P1' P2' : MvPolynomial (Fin 7) ℝ) :
    sShp.Good S F (sData (graphOf (fun x : Fin 1 → ℝ => g (x 0))) D P1' P2') := by
  simp only [sShp, sData, sPos, sBody, sBlk, OShape.Good, true_and, and_true]
  exact ⟨hg, hg⟩

/-- `Ω`-membership of a predicate realised by the shape. -/
theorem pred_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ)
    (P1' P2' : MvPolynomial (Fin 7) ℝ) (P : Set ℝ)
    (hP : {w : Fin 1 → ℝ | ∀ δ : ℝ, 0 < δ → sIn (graphOf (fun x : Fin 1 → ℝ => g (x 0)))
      P1' P2' w δ} = liftR P) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR P ∈ S.Ω a (b.eval D) 1 := by
  refine ⟨Work.WilG0.oFmt F sShp, bP P1' P2', ?_⟩
  have hmem := Work.WilG0.realize_mem_Omega S sShp F
    (sData (graphOf (fun x : Fin 1 → ℝ => g (x 0))) D P1' P2') (sGood (S := S) hg P1' P2')
  rw [sShp_realize, hP, ← bP_eval] at hmem
  exact hmem

theorem RHi_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (RHi g q) ∈ S.Ω a (b.eval D) 1 := by
  refine pred_mem (S := S) (F := F) (D := D) g hg q PRp (PS1p q) (RHi g q) ?_
  ext w
  simp only [Set.mem_ofPred_eq, liftR, RHi]
  constructor
  · intro h δ hδ
    exact (sIn_RHi g q w δ hδ).mp (h δ hδ)
  · intro h δ hδ
    exact (sIn_RHi g q w δ hδ).mpr (h δ hδ)

theorem RLo_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (RLo g q) ∈ S.Ω a (b.eval D) 1 := by
  refine pred_mem (S := S) (F := F) (D := D) g hg q PRp (PS2p q) (RLo g q) ?_
  ext w
  simp only [Set.mem_ofPred_eq, liftR, RLo]
  constructor
  · intro h δ hδ
    exact (sIn_RLo g q w δ hδ).mp (h δ hδ)
  · intro h δ hδ
    exact (sIn_RLo g q w δ hδ).mpr (h δ hδ)

theorem LHi_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (LHi g q) ∈ S.Ω a (b.eval D) 1 := by
  refine pred_mem (S := S) (F := F) (D := D) g hg q PLp (PS2p q) (LHi g q) ?_
  ext w
  simp only [Set.mem_ofPred_eq, liftR, LHi]
  constructor
  · intro h δ hδ
    exact (sIn_LHi g q w δ hδ).mp (h δ hδ)
  · intro h δ hδ
    exact (sIn_LHi g q w δ hδ).mpr (h δ hδ)

theorem LLo_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (LLo g q) ∈ S.Ω a (b.eval D) 1 := by
  refine pred_mem (S := S) (F := F) (D := D) g hg q PLp (PS1p q) (LLo g q) ?_
  ext w
  simp only [Set.mem_ofPred_eq, liftR, LLo]
  constructor
  · intro h δ hδ
    exact (sIn_LLo g q w δ hδ).mp (h δ hδ)
  · intro h δ hδ
    exact (sIn_LLo g q w δ hδ).mpr (h δ hδ)

theorem oscR_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (oscR g q) ∈ S.Ω a (b.eval D) 1 := by
  obtain ⟨a₁, b₁, h1⟩ := RHi_mem (S := S) (F := F) (D := D) g hg q
  obtain ⟨a₂, b₂, h2⟩ := RLo_mem (S := S) (F := F) (D := D) g hg q
  refine ⟨max a₁ a₂ + 1, b₁ + b₂, ?_⟩
  have h := Omega.inter₂ (S := S) h1 h2
  rwa [← liftR_inter, ← oscR_eq] at h

theorem oscL_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), liftR (oscL g q) ∈ S.Ω a (b.eval D) 1 := by
  obtain ⟨a₁, b₁, h1⟩ := LHi_mem (S := S) (F := F) (D := D) g hg q
  obtain ⟨a₂, b₂, h2⟩ := LLo_mem (S := S) (F := F) (D := D) g hg q
  refine ⟨max a₁ a₂ + 1, b₁ + b₂, ?_⟩
  have h := Omega.inter₂ (S := S) h1 h2
  rwa [← liftR_inter, ← oscL_eq] at h

end Work.WilG1.Thin
