import Mathlib
import Submission.Work.SG.Defs

/-! ## Shared vocabulary for the Selling-reduction node (`exists_conj_into_sellingStab`)

Definitions (plus elementary, fully proved lemmas about them) used by the lemmas of the Selling
route.  It imports only `Submission.Work.SG.Defs`.

Main objects:

* `bf Q u v = uᵀ Q v` and `qf Q v = vᵀ Q v` (integer bilinear / quadratic form);
* `linComb4 t v = ∑ m, t m * v m` (integer linear combination of four vectors);
* `sb W` — the four *superbase* vectors of a matrix `W`: `sb W 0 = -(v₁+v₂+v₃)` and
  `sb W i.succ` is the `i`-th column of `W`;
* `ObSbase Q W` — the superbase of `W` is *obtuse* for `Q` (all cross terms `≤ 0`);
* `suppGraph Q W` — the support graph of an obtuse superbase (ordered pairs `m < n` with
  negative cross term), as a list;
* `modEq`, `minVecs A` — congruence mod `2` and the vectors `≠ 0` minimal in their class mod
  `2ℤ³` for the integer form `A`;
* `coordVec`, `permMat σ`, `permE σ E` — relabelling data of a superbase permutation
  `σ : Equiv.Perm (Fin 4)`;
* `IsConnGraph E` — the graph `E` is connected.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- Integer 3-vectors. -/
abbrev IVec := Fin 3 → ℤ

/-- The bilinear form `uᵀ Q v` attached to a matrix `Q`. -/
def bf (Q : IMat) (u v : IVec) : ℤ := ∑ i, u i * ∑ j, Q i j * v j

/-- The quadratic form `vᵀ Q v`. -/
def qf (Q : IMat) (v : IVec) : ℤ := bf Q v v

/-- Integer linear combination of four vectors. -/
def linComb4 (t : Fin 4 → ℤ) (v : Fin 4 → IVec) : IVec := fun k => ∑ m, t m * v m k

theorem bf_add_right (Q : IMat) (u v v' : IVec) : bf Q u (v + v') = bf Q u v + bf Q u v' := by
  simp only [bf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem bf_neg_right (Q : IMat) (u v : IVec) : bf Q u (-v) = -bf Q u v := by
  simp only [bf, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem bf_neg_left (Q : IMat) (u v : IVec) : bf Q (-u) v = -bf Q u v := by
  simp only [bf, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem bf_smul_right (Q : IMat) (u v : IVec) (c : ℤ) : bf Q u (c • v) = c * bf Q u v := by
  simp only [bf, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem bf_smul_left (Q : IMat) (u v : IVec) (c : ℤ) : bf Q (c • u) v = c * bf Q u v := by
  simp only [bf, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- The bilinear form is linear in its second argument on four-term linear combinations. -/
theorem bf_linComb4 (Q : IMat) (u : IVec) (t : Fin 4 → ℤ) (v : Fin 4 → IVec) :
    bf Q u (linComb4 t v) = ∑ m, t m * bf Q u (v m) := by
  simp only [bf, linComb4, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

theorem bf_comm (Q : IMat) (hQ : Qᵀ = Q) (u v : IVec) : bf Q u v = bf Q v u := by
  have h01 : Q 0 1 = Q 1 0 := by
    have := congrFun (congrFun hQ 1) 0
    simpa [Matrix.transpose_apply] using this
  have h02 : Q 0 2 = Q 2 0 := by
    have := congrFun (congrFun hQ 2) 0
    simpa [Matrix.transpose_apply] using this
  have h12 : Q 1 2 = Q 2 1 := by
    have := congrFun (congrFun hQ 2) 1
    simpa [Matrix.transpose_apply] using this
  simp only [bf, Fin.sum_univ_three, h01, h02, h12]
  ring

theorem qf_zero (Q : IMat) : qf Q 0 = 0 := by simp [qf, bf]

theorem qf_neg (Q : IMat) (v : IVec) : qf Q (-v) = qf Q v := by
  simp only [qf, bf_neg_left, bf_neg_right, neg_neg]

/-- The quadratic form of a conjugate matrix. -/
theorem qf_conj (Q W : IMat) (y : IVec) : qf (Wᵀ * Q * W) y = qf Q (W.mulVec y) := by
  simp only [qf, bf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

/-- The `m`-th vector of the superbase attached to a matrix `W`.  Index `0` is
`-(v₁+v₂+v₃)`, indices `1,2,3` are the columns of `W` (so any three of the four form a basis
whenever `W` is unimodular). -/
def sb (W : IMat) : Fin 4 → IVec :=
  ![(fun k => -(W k 0 + W k 1 + W k 2)), (fun k => W k 0), (fun k => W k 1), (fun k => W k 2)]

@[simp] theorem sb_zero (W : IMat) : sb W 0 = fun k => -(W k 0 + W k 1 + W k 2) := rfl

@[simp] theorem sb_one (W : IMat) : sb W 1 = fun k => W k 0 := rfl

@[simp] theorem sb_two (W : IMat) : sb W 2 = fun k => W k 1 := rfl

@[simp] theorem sb_three (W : IMat) : sb W 3 = fun k => W k 2 := rfl

theorem sb_succ (W : IMat) (i : Fin 3) : sb W i.succ = fun k => W k i := by
  fin_cases i <;> rfl

/-- The superbase vectors sum to zero. -/
theorem sb_sum_zero (W : IMat) : ∑ m : Fin 4, sb W m = 0 := by
  funext k
  simp [Fin.sum_univ_four, sb]
  ring

/-- `(0,y)` as a `Fin 4 → ℤ` function. -/
def cons0 (y : IVec) : Fin 4 → ℤ := Fin.cases 0 y

@[simp] theorem cons0_zero (y : IVec) : cons0 y 0 = 0 := rfl

@[simp] theorem cons0_succ (y : IVec) (i : Fin 3) : cons0 y i.succ = y i := rfl

theorem cons0_eq_cons (y : IVec) : cons0 y = Fin.cons 0 y := by
  funext m
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩ <;> simp [cons0]

theorem sum_cons0_sb (W : IMat) (y : IVec) (k : Fin 3) :
    ∑ m : Fin 4, cons0 y m * sb W m k = ∑ i : Fin 3, y i * W k i := by
  rw [Fin.sum_univ_succ]
  simp only [cons0_zero, zero_mul, zero_add, cons0_succ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sb_succ W i]

/-- `W` applied to `y` is the linear combination of the superbase vectors with coefficients
`(0,y)`. -/
theorem mulVec_eq_linComb4 (W : IMat) (y : IVec) :
    W.mulVec y = linComb4 (cons0 y) (sb W) := by
  funext k
  simp only [linComb4, Matrix.mulVec, dotProduct]
  rw [sum_cons0_sb W y k]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `W` applied to `y`, indexed by the columns. -/
theorem mulVec_eq_sum_sb (W : IMat) (y : IVec) :
    W.mulVec y = fun k => y 0 * sb W 1 k + y 1 * sb W 2 k + y 2 * sb W 3 k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [sb_one, sb_two, sb_three]
  ring

/-- The superbase of `W` is obtuse for `Q`: all cross terms are `≤ 0`. -/
def ObSbase (Q W : IMat) : Prop := ∀ m n : Fin 4, m ≠ n → bf Q (sb W m) (sb W n) ≤ 0

/-- The support graph of an obtuse superbase: the list of pairs `m < n` whose cross term is
(strictly) negative. -/
def suppGraph (Q W : IMat) : List (Fin 4 × Fin 4) :=
  ((List.finRange 4) ×ˢ (List.finRange 4)).filterMap fun p =>
    if p.1 < p.2 ∧ bf Q (sb W p.1) (sb W p.2) < 0 then some p else none

theorem mem_suppGraph {Q W : IMat} {p : Fin 4 × Fin 4} :
    p ∈ suppGraph Q W ↔ p.1 < p.2 ∧ bf Q (sb W p.1) (sb W p.2) < 0 := by
  rw [suppGraph, List.mem_filterMap]
  constructor
  · rintro ⟨a, -, ha⟩
    by_cases h : a.1 < a.2 ∧ bf Q (sb W a.1) (sb W a.2) < 0
    · rw [if_pos h] at ha
      rw [← Option.some.inj ha]
      exact h
    · rw [if_neg h] at ha
      exact absurd ha (by simp)
  · intro h
    exact ⟨p, List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩,
      by rw [if_pos h]⟩

/-- Congruence of integer vectors modulo `2`. -/
def modEq (y y' : IVec) : Prop := ∀ i, (2 : ℤ) ∣ y' i - y i

theorem modEq_refl (y : IVec) : modEq y y := fun i => ⟨0, by ring⟩

theorem modEq_symm {y y' : IVec} (h : modEq y y') : modEq y' y := by
  intro i
  obtain ⟨c, hc⟩ := h i
  exact ⟨-c, by
    have h1 : y i - y' i = -(y' i - y i) := by ring
    rw [h1, hc]; ring⟩

theorem modEq_trans {y y' y'' : IVec} (h : modEq y y') (h' : modEq y' y'') : modEq y y'' := by
  intro i
  obtain ⟨c, hc⟩ := h i
  obtain ⟨d, hd⟩ := h' i
  exact ⟨c + d, by
    have h1 : y'' i - y i = (y'' i - y' i) + (y' i - y i) := by ring
    rw [h1, hd, hc]; ring⟩

theorem modEq_add {y y' z z' : IVec} (h : modEq y y') (h' : modEq z z') :
    modEq (y + z) (y' + z') := by
  intro i
  obtain ⟨c, hc⟩ := h i
  obtain ⟨d, hd⟩ := h' i
  exact ⟨c + d, by
    simp only [Pi.add_apply]
    have h1 : y' i + z' i - (y i + z i) = (y' i - y i) + (z' i - z i) := by ring
    rw [h1, hc, hd]; ring⟩

theorem modEq_smul {y y' : IVec} (c : ℤ) (h : modEq y y') : modEq (c • y) (c • y') := by
  intro i
  obtain ⟨d, hd⟩ := h i
  exact ⟨c * d, by
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 : c * y' i - c * y i = c * (y' i - y i) := by ring
    rw [h1, hd]; ring⟩

/-- The vectors `≠ 0` that minimise the integer quadratic form `qf A` in their class mod `2ℤ³`. -/
def minVecs (A : IMat) : Set IVec := {y | y ≠ 0 ∧ ∀ y', modEq y y' → qf A y ≤ qf A y'}

/-- Coordinate vector of the `m`-th superbase vector in the basis given by the columns: `-1` in
each coordinate for `m = 0`, and the standard basis vector for `m = i.succ`. -/
def coordVec : Fin 4 → IVec := Fin.cases (fun _ => -1) (fun i k => if k = i then 1 else 0)

@[simp] theorem coordVec_zero : coordVec 0 = fun _ => (-1 : ℤ) := rfl

@[simp] theorem coordVec_succ (i : Fin 3) : coordVec i.succ = fun k => if k = i then 1 else 0 := rfl

theorem coordVec_ne_zero (m : Fin 4) : coordVec m ≠ 0 := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · intro h
    have := congrFun h 0
    simp at this
  · rw [coordVec_succ]
    intro h
    have := congrFun h i
    simp at this

/-- `W` applied to the coordinate vector of `v_m` is `v_m` itself. -/
theorem mulVec_coordVec (W : IMat) (m : Fin 4) : W.mulVec (coordVec m) = sb W m := by
  rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨i, rfl⟩
  · funext k
    rw [coordVec_zero, sb_zero]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · rw [coordVec_succ i, sb_succ W i]
    funext k
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    fin_cases i <;> simp

/-- The matrix of the superbase relabelling induced by a permutation `σ : Perm (Fin 4)`: its
`j`-th column is the coordinate vector of `v_{σ(j.succ)}` in the column basis of `W`. -/
def permMat (σ : Equiv.Perm (Fin 4)) : IMat := fun i j => coordVec (σ j.succ) i

/-- The edge `{a,b}` in normal form (smaller index first). -/
def nrmEdge (a b : Fin 4) : Fin 4 × Fin 4 := if a < b then (a, b) else (b, a)

theorem nrmEdge_fst_lt (a b : Fin 4) (h : a ≠ b) : (nrmEdge a b).1 < (nrmEdge a b).2 := by
  unfold nrmEdge
  split
  · assumption
  · rename_i hlt
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)

theorem nrmEdge_eq (a b : Fin 4) : nrmEdge a b = (a, b) ∨ nrmEdge a b = (b, a) := by
  unfold nrmEdge; split <;> simp

theorem nrmEdge_comm (a b : Fin 4) : nrmEdge a b = nrmEdge b a := by
  unfold nrmEdge; split <;> split <;> simp_all <;> omega

/-- Relabelling of an edge list by `σ`, each edge put in normal form. -/
def permE (σ : Equiv.Perm (Fin 4)) (E : List (Fin 4 × Fin 4)) : List (Fin 4 × Fin 4) :=
  E.map fun p => nrmEdge (σ p.1) (σ p.2)

/-- The graph `E` (on the four superbase vertices) is connected. -/
def IsConnGraph (E : List (Fin 4 × Fin 4)) : Prop :=
  ∀ a b : Fin 4, Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E) a b

end Work.SG
