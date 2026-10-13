/-
  WilE4 — the frozen area `E4`: **effective semialgebraic fibrewise closure**.

  `E4_sa_fiber_closure` (`Submission/Work/Wilkies/E/Spec.lean`) asks that for each fixed `p, q`
  there is a polynomial bound `b` such that for every semialgebraic set `X ⊆ ℝ^{p+q}` in
  disjunctive normal form the fibrewise closure `fiberClosure X` is again semialgebraic, of degree at
  most `b.eval X.deg`.

  The construction is the one of the CAD chapter of this area (`Submission/Work/WilE4/CAD/`):

  * embed `X` into `ℝ^{p + q + (q+1)}` with coordinates `(x, y, ε, y')`, intersected with the two
    strict inequalities `ε > 0` and `Σⱼ (y'ⱼ - yⱼ)² < ε²` (`fiberSet`);
  * `Work.WilE4.CAD.exists_fiberClosure_step` produces, for such a set `Z` and a family containing
    its atoms, a semialgebraic set of the form `{x | ∀ ε > 0, ∃ y', (x, ε, y') ∈ Z}` with a degree
    bounded by a polynomial in the size of the family;
  * by `Work.WilE4.CAD.fiberClosure_eq_sq` that set is exactly `fiberClosure X`.

  The degree bound is the composition of the polynomial supplied by `exists_fiberClosure_step` with
  the (linear) bound `X.deg + 6` for the degree of the family of the embedded set.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE4.Basic
import Submission.Work.WilE4.CAD.Embed
import Submission.Work.WilE4.CAD.Level
import Submission.Work.WilE4.CAD.fiberClosure_eq_sq
import Submission.Work.WilE4.CAD.exists_fiberClosure_step

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4

open MvPolynomial WilkiesDesign WilkiesDesign.E

variable (p q : ℕ)

/-! ## The block coordinates of `Fin (p + q + (q + 1))` -/

/-- The position of `xᵢ`. -/
def eX (i : Fin p) : Fin (p + q + (q + 1)) := ⟨i, by omega⟩

/-- The position of `yⱼ`. -/
def eY (j : Fin q) : Fin (p + q + (q + 1)) := ⟨p + j, by omega⟩

/-- The position of `ε`. -/
def eEps : Fin (p + q + (q + 1)) := ⟨p + q, by omega⟩

/-- The position of `y'ⱼ`. -/
def eYp (j : Fin q) : Fin (p + q + (q + 1)) := ⟨p + q + 1 + j, by omega⟩

/-- The injection `(x, y') ↪ (x, y, ε, y')`. -/
def embedXY' : Fin (p + q) → Fin (p + q + (q + 1)) :=
  fun i => if h : (i : ℕ) < p then eX p q ⟨i, h⟩ else eYp p q ⟨(i : ℕ) - p, by omega⟩

/-- The atom `Σⱼ (y'ⱼ - yⱼ)² - ε²`. -/
def quadE : MvPolynomial (Fin (p + q + (q + 1))) ℝ :=
  ((Finset.univ : Finset (Fin q)).sum fun j =>
      (MvPolynomial.X (eYp p q j) - MvPolynomial.X (eY p q j)) ^ 2)
    - MvPolynomial.X (eEps p q) ^ 2

theorem eval_quadE (z : Fin (p + q + (q + 1)) → ℝ) :
    MvPolynomial.eval z (quadE p q) =
      ((Finset.univ : Finset (Fin q)).sum fun j =>
          (z (eYp p q j) - z (eY p q j)) ^ 2) - z (eEps p q) ^ 2 := by
  simp [quadE]

/-- A difference of two degree-`≤ 1` polynomials has degree `≤ 1`. -/
theorem totalDegree_sub_le_one {f g : MvPolynomial (Fin (p + q + (q + 1))) ℝ}
    (hf : f.totalDegree ≤ 1) (hg : g.totalDegree ≤ 1) : (f - g).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub f g).trans (max_le hf hg)

theorem atomDegD_quadE_le : atomDegD (quadE p q) ≤ 4 := by
  have hvar : ∀ i : Fin (p + q + (q + 1)),
      (MvPolynomial.X i : MvPolynomial (Fin (p + q + (q + 1))) ℝ).totalDegree ≤ 1 :=
    fun i => le_of_eq (MvPolynomial.totalDegree_X i)
  have hterm : ∀ j : Fin q,
      (((MvPolynomial.X (eYp p q j) - MvPolynomial.X (eY p q j)) ^ 2 :
        MvPolynomial (Fin (p + q + (q + 1))) ℝ)).totalDegree ≤ 2 := by
    intro j
    rw [pow_two]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have h := totalDegree_sub_le_one p q (hvar (eYp p q j)) (hvar (eY p q j)); omega)
  have hsum : ((Finset.univ.sum fun j : Fin q =>
      (MvPolynomial.X (eYp p q j) - MvPolynomial.X (eY p q j)) ^ 2 :
        MvPolynomial (Fin (p + q + (q + 1))) ℝ)).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    exact Finset.sup_le fun j _ => hterm j
  have hsq : (((MvPolynomial.X (eEps p q) ^ 2) :
      MvPolynomial (Fin (p + q + (q + 1))) ℝ)).totalDegree ≤ 2 := by
    rw [pow_two]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by have := hvar (eEps p q); omega)
  have hmax : max ((Finset.univ.sum fun j : Fin q =>
      (MvPolynomial.X (eYp p q j) - MvPolynomial.X (eY p q j)) ^ 2 :
        MvPolynomial (Fin (p + q + (q + 1))) ℝ).totalDegree)
      ((((MvPolynomial.X (eEps p q) ^ 2) :
        MvPolynomial (Fin (p + q + (q + 1))) ℝ)).totalDegree) ≤ 2 := max_le hsum hsq
  have hsub := MvPolynomial.totalDegree_sub
    ((Finset.univ.sum fun j : Fin q =>
      (MvPolynomial.X (eYp p q j) - MvPolynomial.X (eY p q j)) ^ 2) :
        MvPolynomial (Fin (p + q + (q + 1))) ℝ)
    ((MvPolynomial.X (eEps p q) ^ 2) : MvPolynomial (Fin (p + q + (q + 1))) ℝ)
  rw [quadE, atomDegD]
  have := hsub.trans hmax
  omega

/-! ## The embedded set -/

/-- `X`, embedded in `ℝ^{p + q + (q+1)}` as the set of `(x, y, ε, y')` with `(x, y') ∈ X` and
`ε > 0` and `Σⱼ (y'ⱼ - yⱼ)² < ε²`. -/
def fiberSet (X : SA (p + q)) : SAd (p + q + (q + 1)) :=
  ((SAd.ofSA X).renameAlong (embedXY' p q)).interBasic
    ⟨[], [MvPolynomial.X (eEps p q), -(quadE p q)]⟩

/-- A family containing all the atoms of `fiberSet X`: the renamed atoms of `X` together with the
two new atoms. -/
def fiberFam (X : SA (p + q)) : List (MvPolynomial (Fin (p + q + (q + 1))) ℝ) :=
  ((SAd.ofSA X).renameAlong (embedXY' p q)).atoms ++
    [MvPolynomial.X (eEps p q), -(quadE p q)]

theorem fiberSet_atoms_mem (X : SA (p + q)) :
    ∀ B ∈ (fiberSet p q X).basics, ∀ P ∈ B.eqs ++ B.pos, P ∈ fiberFam p q X := by
  intro B hB P hP
  simp only [fiberSet, SAd.interBasic, List.mem_map] at hB
  obtain ⟨B₀, hB₀, rfl⟩ := hB
  simp only [List.append_nil] at hP
  rw [List.mem_append] at hP
  rcases hP with hP | hP
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨B₀, hB₀, List.mem_append_left _ hP⟩)
  · rw [List.mem_append] at hP
    rcases hP with hP | hP
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨B₀, hB₀, List.mem_append_right _ hP⟩)
    · rw [List.mem_cons] at hP
      rcases hP with hP | hP
      · exact List.mem_append_right _ (by rw [hP]; exact List.mem_cons_self)
      · rw [List.mem_cons] at hP
        rcases hP with hP | hP
        · exact List.mem_append_right _
            (by rw [hP]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        · exact absurd hP (by simp)

/-! ## Coordinates of an appended point -/

theorem eX_eq_castAdd (i : Fin p) :
    eX p q i = Fin.castAdd (q + 1) (⟨i, by omega⟩ : Fin (p + q)) := Fin.ext rfl

theorem eY_eq_castAdd (j : Fin q) :
    eY p q j = Fin.castAdd (q + 1) (Fin.natAdd p j) := Fin.ext rfl

theorem eEps_eq_natAdd : eEps p q = Fin.natAdd (p + q) (0 : Fin (q + 1)) :=
  Fin.ext (by simp [eEps])

theorem eYp_eq_natAdd (j : Fin q) :
    eYp p q j = Fin.natAdd (p + q) (Fin.succ j) := by
  refine Fin.ext ?_
  simp only [eYp, Fin.val_natAdd, Fin.val_succ]
  omega

theorem append_eX (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) (i : Fin p) :
    Fin.append x (Fin.cons ε y') (eX p q i) = x ⟨i, by omega⟩ := by
  rw [eX_eq_castAdd p q i, Fin.append_left]

theorem append_eY (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) (j : Fin q) :
    Fin.append x (Fin.cons ε y') (eY p q j) = x (Fin.natAdd p j) := by
  rw [eY_eq_castAdd p q j, Fin.append_left]

theorem append_eEps (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) :
    Fin.append x (Fin.cons ε y') (eEps p q) = ε := by
  rw [eEps_eq_natAdd p q, Fin.append_right, Fin.cons_zero]

theorem append_eYp (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) (j : Fin q) :
    Fin.append x (Fin.cons ε y') (eYp p q j) = y' j := by
  rw [eYp_eq_natAdd p q j, Fin.append_right, Fin.cons_succ]

theorem appendXY'_eX (x : Fin (p + q) → ℝ) (y' : Fin q → ℝ) (i : Fin p) :
    Fin.append (projFirst p q x) y' (⟨i, by omega⟩ : Fin (p + q)) = x ⟨i, by omega⟩ := by
  rw [show (⟨i, by omega⟩ : Fin (p + q)) = Fin.castAdd q (⟨i, by omega⟩ : Fin p)
      from Fin.ext rfl, Fin.append_left]
  rfl

theorem appendXY'_eYp (x : Fin (p + q) → ℝ) (y' : Fin q → ℝ) (j : Fin q) :
    Fin.append (projFirst p q x) y' (Fin.natAdd p j) = y' j :=
  Fin.append_right _ _ _

theorem embedXY'_eq (x : Fin (p + q) → ℝ) (ρ : ℝ) (y' : Fin q → ℝ) :
    (fun i => Fin.append x (Fin.cons ρ y') (embedXY' p q i))
      = Fin.append (projFirst p q x) y' := by
  funext i
  rcases lt_or_ge (i : ℕ) p with hp | hp
  · rw [embedXY', dif_pos hp, append_eX]
    exact (appendXY'_eX p q x y' ⟨i, hp⟩).symm
  · rw [embedXY', dif_neg (not_lt.mpr hp), append_eYp]
    rw [← appendXY'_eYp p q x y' ⟨(i : ℕ) - p, by omega⟩]
    congr 1
    refine Fin.ext ?_
    simp only [Fin.val_natAdd]
    omega

/-! ## Membership in the embedded set -/

/-- The evaluation of `-(Σⱼ (y'ⱼ - yⱼ)² - ε²)` at an appended point. -/
theorem eval_negQuadE_append (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) :
    0 < MvPolynomial.eval (Fin.append x (Fin.cons ε y')) (-(quadE p q)) ↔
      ((Finset.univ : Finset (Fin q)).sum fun j => (y' j - projSnd p q x j) ^ 2) < ε ^ 2 := by
  have hsum : (Finset.univ.sum fun j : Fin q =>
      (Fin.append x (Fin.cons ε y') (eYp p q j)
        - Fin.append x (Fin.cons ε y') (eY p q j)) ^ 2)
      = (Finset.univ.sum fun j : Fin q => (y' j - projSnd p q x j) ^ 2) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [append_eYp, append_eY]
    rfl
  rw [map_neg, neg_pos, eval_quadE, append_eEps, hsum]
  constructor <;> intro h <;> linarith

theorem mem_fiberSet_iff (X : SA (p + q)) (x : Fin (p + q) → ℝ) (ε : ℝ) (y' : Fin q → ℝ) :
    Fin.append x (Fin.cons ε y') ∈ (fiberSet p q X).set ↔
      Fin.append (projFirst p q x) y' ∈ X.set ∧ 0 < ε ∧
        ((Finset.univ : Finset (Fin q)).sum fun j => (y' j - projSnd p q x j) ^ 2) < ε ^ 2 := by
  have hcoord := embedXY'_eq p q x ε y'
  have hbasic : (Fin.append x (Fin.cons ε y') ∈
      (⟨[], [MvPolynomial.X (eEps p q), -(quadE p q)]⟩ : BasicD (p + q + (q + 1))).set) ↔
      (0 < ε ∧ ((Finset.univ : Finset (Fin q)).sum fun j =>
        (y' j - projSnd p q x j) ^ 2) < ε ^ 2) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := h.2 (MvPolynomial.X (eEps p q)) List.mem_cons_self
        rwa [MvPolynomial.eval_X, append_eEps] at h1
      · exact (eval_negQuadE_append p q x ε y').mp
          (h.2 (-(quadE p q)) (List.mem_cons_of_mem _ List.mem_cons_self))
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => by simp at hf, fun g hg => ?_⟩
      rw [List.mem_cons] at hg
      rcases hg with hg | hg
      · rw [hg, MvPolynomial.eval_X, append_eEps]; exact h1
      · rw [List.mem_cons] at hg
        rcases hg with hg | hg
        · rw [hg]
          exact (eval_negQuadE_append p q x ε y').mpr h2
        · exact absurd hg (by simp)
  rw [fiberSet, SAd.interBasic_set, Set.mem_inter_iff, SAd.renameAlong_set, SAd.set_ofSA]
  simp only [Set.mem_ofPred_eq]
  rw [hbasic, hcoord]

/-! ## The main theorem -/

theorem famDeg_atoms {m : ℕ} (X : SAd m) : CAD.famDeg X.atoms = X.deg := by
  have h : ∀ l : List (BasicD m),
      CAD.famDeg (l.flatMap BasicD.atoms) = (l.map BasicD.deg).sum := by
    intro l
    induction l with
    | nil => simp [CAD.famDeg]
    | cons B t ih =>
      rw [List.flatMap_cons, CAD.famDeg_append, ih, List.map_cons, List.sum_cons]
      rfl
  exact h X.basics

theorem famDeg_fiberFam_le (X : SA (p + q)) :
    CAD.famDeg (fiberFam p q X) ≤ (Polynomial.X + Polynomial.C 6).eval X.deg := by
  have h1 : CAD.famDeg ((SAd.ofSA X).renameAlong (embedXY' p q)).atoms ≤ X.deg := by
    rw [famDeg_atoms]
    exact (SAd.renameAlong_deg_le (embedXY' p q) (SAd.ofSA X)).trans_eq (SAd.deg_ofSA X)
  have h2 : CAD.famDeg ([MvPolynomial.X (eEps p q)] :
      List (MvPolynomial (Fin (p + q + (q + 1))) ℝ)) = 2 := by
    simp [CAD.famDeg, atomDegD, MvPolynomial.totalDegree_X]
  have h3 : CAD.famDeg ([-(quadE p q)] :
      List (MvPolynomial (Fin (p + q + (q + 1))) ℝ)) ≤ 4 := by
    simp only [CAD.famDeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact (CAD.atomDegD_neg (quadE p q)).trans_le (atomDegD_quadE_le p q)
  have h23 : CAD.famDeg ([MvPolynomial.X (eEps p q), -(quadE p q)] :
      List (MvPolynomial (Fin (p + q + (q + 1))) ℝ)) ≤ 6 := by
    rw [show ([MvPolynomial.X (eEps p q), -(quadE p q)] :
        List (MvPolynomial (Fin (p + q + (q + 1))) ℝ))
        = [MvPolynomial.X (eEps p q)] ++ [-(quadE p q)] from rfl, CAD.famDeg_append, h2]
    omega
  rw [fiberFam, CAD.famDeg_append]
  have h4 : (Polynomial.X + Polynomial.C 6).eval X.deg = X.deg + 6 := by
    simp
  rw [h4]
  omega

theorem E4_sa_fiber_closure_proved :
    ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : SA (p + q),
      ∃ Y : SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set := by
  intro p q
  obtain ⟨B, hB⟩ := CAD.exists_fiberClosure_step (p + q) q
  refine ⟨B.comp (Polynomial.X + Polynomial.C 6), fun X => ?_⟩
  obtain ⟨Y, hYset, hYdeg⟩ := hB (fiberSet p q X) (fiberFam p q X) (fiberSet_atoms_mem p q X)
  refine ⟨SAd.toSA Y, ?_, ?_⟩
  · rw [SAd.deg_toSA]
    refine hYdeg.trans ?_
    rw [Polynomial.eval_comp]
    exact CAD.polynomial_eval_mono B (famDeg_fiberFam_le p q X)
  · rw [SAd.set_toSA, hYset, CAD.fiberClosure_eq_sq]
    ext x
    constructor
    · intro h ε hε
      obtain ⟨y', hy'⟩ := h ε hε
      obtain ⟨h1, -, h3⟩ := (mem_fiberSet_iff p q X x ε y').mp hy'
      exact ⟨y', h1, h3⟩
    · intro h ε hε
      obtain ⟨y', hy'X, hy'lt⟩ := h ε hε
      exact ⟨y', (mem_fiberSet_iff p q X x ε y').mpr ⟨hy'X, hε, hy'lt⟩⟩

end Work.WilE4
