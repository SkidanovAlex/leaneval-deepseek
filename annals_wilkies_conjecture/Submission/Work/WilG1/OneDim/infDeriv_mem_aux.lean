/-
  WilG1 / OneDim — auxiliaries for `infDeriv_mem`.

  The polynomials, hyperplane evaluations, total-degree bounds and elementary real facts
  used by `Work.WilG1.OneDim.infDeriv_mem`.  The coordinate layout is fixed once and for
  all: in `ℝⁿ` the coordinates are

    `0 = x`, `1 = a` (`= g x`), `2 = M`, `3 = δ`, `4 = y`, `5 = b` (`= g y`),

  and the last coordinate is a fresh witness `t` realising a strict inequality `0 < A` as
  `t ^ 2 * A = 1`.
-/
import Mathlib
import Submission.Work.WilG0.Main
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Calc.le_mem
import Submission.Work.WilG1.Calc.supBall_mem

set_option autoImplicit false
noncomputable section

open Classical
open WilkiesDesign

namespace Work.WilG1.OneDim

/-! ## 1. The polynomials defining the strict-inequality atoms -/

/-- `t ^ 2 (M - 1) - 1`, in `ℝ⁴` with coordinates `(x, a, M, t)`. -/
def infP1 : MvPolynomial (Fin 4) ℝ :=
  (MvPolynomial.X (3 : Fin 4))^2 * (MvPolynomial.X (2 : Fin 4) - 1) - 1
/-- `t ^ 2 δ - 1`, in `ℝ⁵` with coordinates `(x, a, M, δ, t)`. -/
def infP2 : MvPolynomial (Fin 5) ℝ :=
  (MvPolynomial.X (4 : Fin 5))^2 * (MvPolynomial.X (3 : Fin 5)) - 1
/-- `t ^ 2 (y - x) ^ 2 - 1`, in `ℝ⁶` with coordinates `(x, a, M, δ, y, t)`. -/
def infP3 : MvPolynomial (Fin 6) ℝ :=
  (MvPolynomial.X (5 : Fin 6))^2 *
    (MvPolynomial.X (4 : Fin 6) - MvPolynomial.X (0 : Fin 6))^2 - 1
/-- `t ^ 2 (δ ^ 2 - (y - x) ^ 2) - 1`, in `ℝ⁶`. -/
def infP4 : MvPolynomial (Fin 6) ℝ :=
  (MvPolynomial.X (5 : Fin 6))^2 *
    ((MvPolynomial.X (3 : Fin 6))^2 -
      (MvPolynomial.X (4 : Fin 6) - MvPolynomial.X (0 : Fin 6))^2) - 1
/-- The bracket `s (b - a) (y - x)` in `ℝ⁷`. -/
private def infP5a (s : ℝ) : MvPolynomial (Fin 7) ℝ :=
  MvPolynomial.C s * (MvPolynomial.X (5 : Fin 7) - MvPolynomial.X (1 : Fin 7)) *
    (MvPolynomial.X (4 : Fin 7) - MvPolynomial.X (0 : Fin 7))
/-- The bracket `M (y - x) ^ 2` in `ℝ⁷`. -/
private def infP5b : MvPolynomial (Fin 7) ℝ :=
  MvPolynomial.X (2 : Fin 7) *
    (MvPolynomial.X (4 : Fin 7) - MvPolynomial.X (0 : Fin 7))^2
/-- `t ^ 2 (s (b - a)(y - x) - M (y - x)^2) - 1` in `ℝ⁷` with coordinates
`(x, a, M, δ, y, b, t)`. -/
def infP5 (s : ℝ) : MvPolynomial (Fin 7) ℝ :=
  (MvPolynomial.X (6 : Fin 7))^2 * (infP5a s - infP5b) - 1

/-- The pair of coordinate positions `(y, b) = (4, 5)` used by the graph atom in `ℝ⁶`. -/
def infιY : Fin 2 → Fin 6 := ![(4 : Fin 6), (5 : Fin 6)]

/-! ## 2. Evaluation of the atoms at a `snoc`-extension -/

private lemma ev1 (v : Fin 3 → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc v t) infP1 = t^2 * (v 2 - 1) - 1 := by
  have h3 : (Fin.snoc v t : Fin 4 → ℝ) (3 : Fin 4) = t := rfl
  have h2 : (Fin.snoc v t : Fin 4 → ℝ) (2 : Fin 4) = v 2 := rfl
  simp only [infP1, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, map_one]
  rw [h3, h2]

private lemma ev2 (v : Fin 4 → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc v t) infP2 = t^2 * v 3 - 1 := by
  have h4 : (Fin.snoc v t : Fin 5 → ℝ) (4 : Fin 5) = t := rfl
  have h3 : (Fin.snoc v t : Fin 5 → ℝ) (3 : Fin 5) = v 3 := rfl
  simp only [infP2, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, map_one]
  rw [h4, h3]

private lemma ev3 (v : Fin 5 → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc v t) infP3 = t^2 * (v 4 - v 0)^2 - 1 := by
  have h5 : (Fin.snoc v t : Fin 6 → ℝ) (5 : Fin 6) = t := rfl
  have h4 : (Fin.snoc v t : Fin 6 → ℝ) (4 : Fin 6) = v 4 := rfl
  have h0 : (Fin.snoc v t : Fin 6 → ℝ) (0 : Fin 6) = v 0 := rfl
  simp only [infP3, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, map_one]
  rw [h5, h4, h0]

private lemma ev4 (v : Fin 5 → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc v t) infP4 = t^2 * ((v 3)^2 - (v 4 - v 0)^2) - 1 := by
  have h5 : (Fin.snoc v t : Fin 6 → ℝ) (5 : Fin 6) = t := rfl
  have h4 : (Fin.snoc v t : Fin 6 → ℝ) (4 : Fin 6) = v 4 := rfl
  have h3 : (Fin.snoc v t : Fin 6 → ℝ) (3 : Fin 6) = v 3 := rfl
  have h0 : (Fin.snoc v t : Fin 6 → ℝ) (0 : Fin 6) = v 0 := rfl
  simp only [infP4, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, map_one]
  rw [h5, h4, h3, h0]

private lemma ev5 (s : ℝ) (v : Fin 6 → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc v t) (infP5 s) =
      t^2 * (s * (v 5 - v 1) * (v 4 - v 0) - v 2 * (v 4 - v 0)^2) - 1 := by
  have h6 : (Fin.snoc v t : Fin 7 → ℝ) (6 : Fin 7) = t := rfl
  have h5 : (Fin.snoc v t : Fin 7 → ℝ) (5 : Fin 7) = v 5 := rfl
  have h4 : (Fin.snoc v t : Fin 7 → ℝ) (4 : Fin 7) = v 4 := rfl
  have h2 : (Fin.snoc v t : Fin 7 → ℝ) (2 : Fin 7) = v 2 := rfl
  have h1 : (Fin.snoc v t : Fin 7 → ℝ) (1 : Fin 7) = v 1 := rfl
  have h0 : (Fin.snoc v t : Fin 7 → ℝ) (0 : Fin 7) = v 0 := rfl
  simp only [infP5, infP5a, infP5b, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, map_one]
  rw [h6, h5, h4, h2, h1, h0]

/-- `∃ t, t ^ 2 * A v = 1` iff `0 < A v`; hence the projection of the hypersurface
`t ^ 2 A - 1 = 0` is the positivity set `{v | 0 < A v}`. -/
private lemma pos_proj {n : ℕ} (P : MvPolynomial (Fin (n+1)) ℝ) (A : (Fin n → ℝ) → ℝ)
    (h : ∀ (v : Fin n → ℝ) (t : ℝ), MvPolynomial.eval (Fin.snoc v t) P = t^2 * A v - 1)
    (v : Fin n → ℝ) :
    v ∈ projLast {w : Fin (n+1) → ℝ | MvPolynomial.eval w P = 0} ↔ 0 < A v := by
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [h v t] at ht
    exact Work.WilG1.Calc.sq_mul_eq_one_iff_pos.mp ⟨t, by linarith⟩
  · intro hv
    refine ⟨Real.sqrt ((A v)⁻¹), ?_⟩
    rw [h v]
    rw [Real.sq_sqrt (by positivity), inv_mul_cancel₀ (ne_of_gt hv)]
    ring

/-! ## 3. The five positivity atoms -/

lemma inf_mem_slab1 (v : Fin 3 → ℝ) :
    v ∈ projLast {w : Fin 4 → ℝ | MvPolynomial.eval w infP1 = 0} ↔ 1 < v 2 := by
  rw [pos_proj infP1 (fun v => v 2 - 1) (fun v t => ev1 v t) v, sub_pos]

lemma inf_mem_slab2 (v : Fin 4 → ℝ) :
    v ∈ projLast {w : Fin 5 → ℝ | MvPolynomial.eval w infP2 = 0} ↔ 0 < v 3 :=
  pos_proj infP2 (fun v => v 3) (fun v t => ev2 v t) v

lemma inf_mem_slab3 (v : Fin 5 → ℝ) :
    v ∈ projLast {w : Fin 6 → ℝ | MvPolynomial.eval w infP3 = 0} ↔ 0 < (v 4 - v 0)^2 :=
  pos_proj infP3 (fun v => (v 4 - v 0)^2) (fun v t => ev3 v t) v

lemma inf_mem_slab4 (v : Fin 5 → ℝ) :
    v ∈ projLast {w : Fin 6 → ℝ | MvPolynomial.eval w infP4 = 0} ↔
      0 < (v 3)^2 - (v 4 - v 0)^2 :=
  pos_proj infP4 (fun v => (v 3)^2 - (v 4 - v 0)^2) (fun v t => ev4 v t) v

lemma inf_mem_slab5 (s : ℝ) (v : Fin 6 → ℝ) :
    v ∈ projLast {w : Fin 7 → ℝ | MvPolynomial.eval w (infP5 s) = 0} ↔
      0 < s * (v 5 - v 1) * (v 4 - v 0) - v 2 * (v 4 - v 0)^2 :=
  pos_proj (infP5 s)
    (fun v => s * (v 5 - v 1) * (v 4 - v 0) - v 2 * (v 4 - v 0)^2)
    (fun v t => ev5 s v t) v

/-! ## 4. Total-degree bounds for the atoms -/

private lemma td_mul2 {σ : Type*} (p q : MvPolynomial σ ℝ) :
    (p * q).totalDegree ≤ p.totalDegree + q.totalDegree := MvPolynomial.totalDegree_mul p q
private lemma td_sub2 {σ : Type*} (p q : MvPolynomial σ ℝ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := MvPolynomial.totalDegree_sub p q
private lemma td_sq2 {σ : Type*} (p : MvPolynomial σ ℝ) :
    (p^2).totalDegree ≤ 2 * p.totalDegree := MvPolynomial.totalDegree_pow p 2
private lemma td_X2 {σ : Type*} [Nontrivial ℝ] (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ ℝ).totalDegree ≤ 1 :=
  le_of_eq (MvPolynomial.totalDegree_X i)
private lemma td_diff2 {σ : Type*} (i j : σ) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial σ ℝ).totalDegree ≤ 1 :=
  le_trans (td_sub2 _ _) (max_le (td_X2 i) (td_X2 j))

lemma infP1_td : infP1.totalDegree ≤ 3 := by
  rw [infP1]
  have h1 : ((MvPolynomial.X (3:Fin 4))^2 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (3:Fin 4) : MvPolynomial (Fin 4) ℝ), td_X2 (3:Fin 4)]
  have h2 : (MvPolynomial.X (2:Fin 4) - 1 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := by
    refine le_trans (td_sub2 _ _) (max_le (td_X2 _) ?_)
    rw [MvPolynomial.totalDegree_one]; norm_num
  have h3 : (((MvPolynomial.X (3:Fin 4))^2 * (MvPolynomial.X (2:Fin 4) - 1) :
      MvPolynomial (Fin 4) ℝ).totalDegree) ≤ 3 := by
    linarith [td_mul2 ((MvPolynomial.X (3:Fin 4))^2 : MvPolynomial (Fin 4) ℝ)
      (MvPolynomial.X (2:Fin 4) - 1 : MvPolynomial (Fin 4) ℝ)]
  refine le_trans (td_sub2 _ _) (max_le h3 ?_)
  rw [MvPolynomial.totalDegree_one]; norm_num

lemma infP2_td : infP2.totalDegree ≤ 3 := by
  rw [infP2]
  have h1 : ((MvPolynomial.X (4:Fin 5))^2 : MvPolynomial (Fin 5) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (4:Fin 5) : MvPolynomial (Fin 5) ℝ), td_X2 (4:Fin 5)]
  have h3 : (((MvPolynomial.X (4:Fin 5))^2 * MvPolynomial.X (3:Fin 5) :
      MvPolynomial (Fin 5) ℝ).totalDegree) ≤ 3 := by
    linarith [td_mul2 ((MvPolynomial.X (4:Fin 5))^2 : MvPolynomial (Fin 5) ℝ)
      (MvPolynomial.X (3:Fin 5) : MvPolynomial (Fin 5) ℝ), td_X2 (3:Fin 5)]
  refine le_trans (td_sub2 _ _) (max_le h3 ?_)
  rw [MvPolynomial.totalDegree_one]; norm_num

lemma infP3_td : infP3.totalDegree ≤ 4 := by
  rw [infP3]
  have h2 : (((MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2) :
      MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6) :
      MvPolynomial (Fin 6) ℝ), td_diff2 (4:Fin 6) (0:Fin 6)]
  have h1 : ((MvPolynomial.X (5:Fin 6))^2 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (5:Fin 6) : MvPolynomial (Fin 6) ℝ), td_X2 (5:Fin 6)]
  have h3 : (((MvPolynomial.X (5:Fin 6))^2 *
      (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2 :
      MvPolynomial (Fin 6) ℝ).totalDegree) ≤ 4 := by
    linarith [td_mul2 ((MvPolynomial.X (5:Fin 6))^2 : MvPolynomial (Fin 6) ℝ)
      ((MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2 : MvPolynomial (Fin 6) ℝ)]
  refine le_trans (td_sub2 _ _) (max_le h3 ?_)
  rw [MvPolynomial.totalDegree_one]; norm_num

lemma infP4_td : infP4.totalDegree ≤ 4 := by
  rw [infP4]
  have h2 : (((MvPolynomial.X (3:Fin 6))^2 -
      (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2) :
      MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2 := by
    refine le_trans (td_sub2 _ _) (max_le ?_ ?_)
    · linarith [td_sq2 (MvPolynomial.X (3:Fin 6) : MvPolynomial (Fin 6) ℝ), td_X2 (3:Fin 6)]
    · linarith [td_sq2 (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6) :
        MvPolynomial (Fin 6) ℝ), td_diff2 (4:Fin 6) (0:Fin 6)]
  have h1 : ((MvPolynomial.X (5:Fin 6))^2 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (5:Fin 6) : MvPolynomial (Fin 6) ℝ), td_X2 (5:Fin 6)]
  have h3 : (((MvPolynomial.X (5:Fin 6))^2 * ((MvPolynomial.X (3:Fin 6))^2 -
      (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2) :
      MvPolynomial (Fin 6) ℝ).totalDegree) ≤ 4 := by
    linarith [td_mul2 ((MvPolynomial.X (5:Fin 6))^2 : MvPolynomial (Fin 6) ℝ)
      ((MvPolynomial.X (3:Fin 6))^2 - (MvPolynomial.X (4:Fin 6) - MvPolynomial.X (0:Fin 6))^2 :
        MvPolynomial (Fin 6) ℝ)]
  refine le_trans (td_sub2 _ _) (max_le h3 ?_)
  rw [MvPolynomial.totalDegree_one]; norm_num

private lemma infP5a_td (s : ℝ) : (infP5a s).totalDegree ≤ 2 := by
  rw [infP5a]
  have hc : (MvPolynomial.C s : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 0 :=
    le_of_eq (MvPolynomial.totalDegree_C s)
  have h51 : ((MvPolynomial.C s *
      (MvPolynomial.X (5:Fin 7) - MvPolynomial.X (1:Fin 7)) :
      MvPolynomial (Fin 7) ℝ)).totalDegree ≤ 1 := by
    linarith [td_mul2 (MvPolynomial.C s : MvPolynomial (Fin 7) ℝ)
      (MvPolynomial.X (5:Fin 7) - MvPolynomial.X (1:Fin 7) : MvPolynomial (Fin 7) ℝ),
      td_diff2 (5:Fin 7) (1:Fin 7)]
  linarith [td_mul2 (MvPolynomial.C s * (MvPolynomial.X (5:Fin 7) - MvPolynomial.X (1:Fin 7)) :
      MvPolynomial (Fin 7) ℝ)
      (MvPolynomial.X (4:Fin 7) - MvPolynomial.X (0:Fin 7) : MvPolynomial (Fin 7) ℝ),
    td_diff2 (4:Fin 7) (0:Fin 7)]

private lemma infP5b_td : infP5b.totalDegree ≤ 3 := by
  rw [infP5b]
  have hd2 : (((MvPolynomial.X (4:Fin 7) - MvPolynomial.X (0:Fin 7))^2) :
      MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (4:Fin 7) - MvPolynomial.X (0:Fin 7) :
      MvPolynomial (Fin 7) ℝ), td_diff2 (4:Fin 7) (0:Fin 7)]
  linarith [td_mul2 (MvPolynomial.X (2:Fin 7) : MvPolynomial (Fin 7) ℝ)
    ((MvPolynomial.X (4:Fin 7) - MvPolynomial.X (0:Fin 7))^2 : MvPolynomial (Fin 7) ℝ),
    td_X2 (2:Fin 7)]

lemma infP5_td (s : ℝ) : (infP5 s).totalDegree ≤ 5 := by
  rw [infP5]
  have h6 : ((MvPolynomial.X (6:Fin 7))^2 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
    linarith [td_sq2 (MvPolynomial.X (6:Fin 7) : MvPolynomial (Fin 7) ℝ), td_X2 (6:Fin 7)]
  have hbr : (infP5a s - infP5b).totalDegree ≤ 3 :=
    le_trans (td_sub2 _ _) (max_le (le_trans (infP5a_td s) (by norm_num)) (infP5b_td))
  have h3 : (((MvPolynomial.X (6:Fin 7))^2 * (infP5a s - infP5b) :
      MvPolynomial (Fin 7) ℝ).totalDegree) ≤ 5 := by
    linarith [td_mul2 ((MvPolynomial.X (6:Fin 7))^2 : MvPolynomial (Fin 7) ℝ)
      (infP5a s - infP5b)]
  refine le_trans (td_sub2 _ _) (max_le h3 ?_)
  rw [MvPolynomial.totalDegree_one]; norm_num

/-! ## 5. Two elementary real-analytic facts used to identify the realised set -/

/-- For `δ > 0`, the conjunction `0 < (y - z0)^2 ∧ 0 < δ^2 - (y - z0)^2` is exactly
`y ≠ z0 ∧ |y - z0| < δ`. -/
lemma inf_aux_hyp {z0 δ y : ℝ} (hδ : 0 < δ) :
    (0 < (y - z0)^2 ∧ 0 < δ^2 - (y - z0)^2) ↔ (y ≠ z0 ∧ |y - z0| < δ) := by
  have hδa : |δ| = δ := abs_of_pos hδ
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨sub_ne_zero.mp (sq_pos_iff.mp h1), ?_⟩
    rw [← hδa, ← sq_lt_sq]
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨sq_pos_iff.mpr (sub_ne_zero.mpr h1), ?_⟩
    rw [← hδa, ← sq_lt_sq] at h2
    linarith

/-- For `u ≠ 0`, `0 < s a u - M u ^ 2` is exactly `M < s (a / u)`:  multiplying by the
positive `u ^ 2` clears the denominator. -/
lemma inf_aux_ineq (M s a u : ℝ) (hu : u ≠ 0) :
    0 < s * a * u - M * u^2 ↔ M < s * (a / u) := by
  have hu2 : 0 < u^2 := by positivity
  have hkey : (s * (a/u)) * u^2 = s * a * u := by field_simp
  have hA : 0 < s * a * u - M * u^2 ↔ M * u^2 < s * a * u := by
    constructor <;> intro h <;> linarith
  rw [hA, ← hkey, mul_lt_mul_iff_of_pos_right hu2]

end Work.WilG1.OneDim
