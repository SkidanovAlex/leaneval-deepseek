/-
  WilE4 — area E4 (effective semialgebraic fibrewise closure).

  This file: transport between the frozen `EAPoly m 0`/`SA m`/`Basic m 0` vocabulary (which lives
  over `MvPolynomial (Fin m ⊕ Fin 0) ℝ`) and the polynomial-ring vocabulary `MvPolynomial (Fin m) ℝ`
  that the CAD development uses, together with the basic DNF API.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4
open WilkiesDesign WilkiesDesign.E
open MvPolynomial

/-! ## Transport of the frozen vocabulary -/

/-- The index equivalence `Fin m ⊕ Fin 0 ≃ Fin m`. -/
def sumFinZeroEquiv (m : ℕ) : Fin m ⊕ Fin 0 ≃ Fin m where
  toFun := Sum.elim id (fun j => j.elim0)
  invFun i := Sum.inl i
  left_inv := by
    rintro (i | i)
    · rfl
    · exact i.elim0
  right_inv i := rfl

@[simp] theorem sumFinZeroEquiv_inl (m : ℕ) (i : Fin m) :
    sumFinZeroEquiv m (Sum.inl i) = i := rfl

/-- Transport `EAPoly m 0` to `MvPolynomial (Fin m) ℝ`. -/
def eapEquiv (m : ℕ) : EAPoly m 0 ≃ₐ[ℝ] MvPolynomial (Fin m) ℝ :=
  MvPolynomial.renameEquiv ℝ (sumFinZeroEquiv m)

theorem eapEquiv_apply (m : ℕ) (Q : EAPoly m 0) :
    eapEquiv m Q = MvPolynomial.rename (sumFinZeroEquiv m) Q := rfl

/-- `eaEval` along the empty chain is evaluation of the transported polynomial. -/
theorem eaEval_eq_eval (m : ℕ) (Q : EAPoly m 0) (x : Fin m → ℝ) :
    eaEval (EAChain.nil m) Q x = MvPolynomial.eval x (eapEquiv m Q) := by
  have h : (Sum.elim x (fun j : Fin 0 => Real.exp ((EAChain.nil m).ell j x)))
      = (x ∘ sumFinZeroEquiv m) := by
    funext i
    rcases i with i | i
    · rfl
    · exact i.elim0
  rw [eaEval, eapEquiv_apply, MvPolynomial.eval_rename, h]

/-- `atomDeg` is preserved by the transport. -/
theorem atomDeg_eq (m : ℕ) (Q : EAPoly m 0) :
    atomDeg Q = (eapEquiv m Q).totalDegree + 1 := by
  simp only [eapEquiv, atomDeg, MvPolynomial.totalDegree_renameEquiv]

/-! ## The polynomial-ring vocabulary -/

/-- A basic semialgebraic set over `ℝ^m`, as equations `= 0` and strict inequalities `> 0`. -/
structure BasicD (m : ℕ) where
  eqs : List (MvPolynomial (Fin m) ℝ)
  pos : List (MvPolynomial (Fin m) ℝ)

/-- Degree of an atom, matching the frozen `atomDeg`. -/
def atomDegD {m : ℕ} (P : MvPolynomial (Fin m) ℝ) : ℕ := P.totalDegree + 1

namespace BasicD

variable {m : ℕ}

/-- Satisfaction of a basic set. -/
def Holds (B : BasicD m) (x : Fin m → ℝ) : Prop :=
  (∀ f ∈ B.eqs, MvPolynomial.eval x f = 0) ∧ (∀ g ∈ B.pos, 0 < MvPolynomial.eval x g)

/-- The set defined by a basic set. -/
def set (B : BasicD m) : Set (Fin m → ℝ) := {x | B.Holds x}

/-- Degree of a basic set. -/
def deg (B : BasicD m) : ℕ := ((B.eqs ++ B.pos).map atomDegD).sum

theorem deg_cons (l₁ l₂ : List (MvPolynomial (Fin m) ℝ)) :
    (⟨l₁, l₂⟩ : BasicD m).deg = (l₁.map atomDegD).sum + (l₂.map atomDegD).sum := by
  simp [deg, List.map_append, List.sum_append]

theorem deg_le_of_mem_atom {B : BasicD m} {P : MvPolynomial (Fin m) ℝ}
    (h : P ∈ B.eqs ∨ P ∈ B.pos) : atomDegD P ≤ B.deg := by
  rcases h with h | h
  · rw [deg_cons]
    exact Nat.le_add_right_of_le (List.le_sum_of_mem (List.mem_map_of_mem h))
  · rw [deg_cons]
    exact Nat.le_add_left_of_le (List.le_sum_of_mem (List.mem_map_of_mem h))

/-- Transport a `BasicD m` back to the frozen `Basic m 0`. -/
def toBasic (B : BasicD m) : Basic m 0 :=
  ⟨B.eqs.map (eapEquiv m).symm, B.pos.map (eapEquiv m).symm⟩

end BasicD

/-- A semialgebraic set over `ℝ^m` in disjunctive normal form. -/
structure SAd (m : ℕ) where
  basics : List (BasicD m)

namespace SAd

variable {m : ℕ}

/-- The set defined by an `SAd`. -/
def set (X : SAd m) : Set (Fin m → ℝ) := {x | ∃ B ∈ X.basics, B.Holds x}

/-- Degree of an `SAd`. -/
def deg (X : SAd m) : ℕ := (X.basics.map BasicD.deg).sum

theorem mem_set {X : SAd m} {x : Fin m → ℝ} :
    x ∈ X.set ↔ ∃ B ∈ X.basics, B.Holds x := Iff.rfl

theorem set_mono {X Y : SAd m} (h : ∀ B ∈ X.basics, B ∈ Y.basics) : X.set ⊆ Y.set :=
  fun x hx => by
    obtain ⟨B, hB, hBx⟩ := hx
    exact ⟨B, h B hB, hBx⟩

/-- The empty set. -/
def empty (m : ℕ) : SAd m := ⟨[]⟩

@[simp] theorem empty_set (m : ℕ) : (empty m).set = ∅ := by
  ext x; simp [empty, set]

@[simp] theorem empty_deg (m : ℕ) : (empty m).deg = 0 := by simp [empty, deg]

/-- Union (concatenation of the lists). -/
def union (X Y : SAd m) : SAd m := ⟨X.basics ++ Y.basics⟩

theorem union_set (X Y : SAd m) : (union X Y).set = X.set ∪ Y.set := by
  ext x
  simp only [union, set, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨B, hB | hB, h⟩
    · exact Or.inl ⟨B, hB, h⟩
    · exact Or.inr ⟨B, hB, h⟩
  · rintro (⟨B, hB, h⟩ | ⟨B, hB, h⟩)
    · exact ⟨B, Or.inl hB, h⟩
    · exact ⟨B, Or.inr hB, h⟩

theorem union_deg (X Y : SAd m) : (union X Y).deg = X.deg + Y.deg := by
  simp [union, deg, List.map_append, List.sum_append]

/-- Alias of `union_deg`. -/
theorem union_deg_le (X Y : SAd m) : (union X Y).deg = X.deg + Y.deg := union_deg X Y

/-- Intersection with a single basic set. -/
def interBasic (X : SAd m) (B : BasicD m) : SAd m :=
  ⟨X.basics.map fun B' => ⟨B'.eqs ++ B.eqs, B'.pos ++ B.pos⟩⟩

theorem interBasic_set (X : SAd m) (B : BasicD m) :
    (interBasic X B).set = X.set ∩ B.set := by
  ext x
  simp only [Set.mem_inter_iff, mem_set, interBasic, BasicD.set, List.mem_map,
    BasicD.Holds]
  constructor
  · rintro ⟨B', ⟨B₀, hB₀, rfl⟩, h1, h2⟩
    refine ⟨⟨B₀, hB₀, ?_, ?_⟩, ?_, ?_⟩
    · intro f hf; exact h1 f (List.mem_append_left _ hf)
    · intro g hg; exact h2 g (List.mem_append_left _ hg)
    · intro f hf; exact h1 f (List.mem_append_right _ hf)
    · intro g hg; exact h2 g (List.mem_append_right _ hg)
  · rintro ⟨⟨B₀, hB₀, h11, h12⟩, h21, h22⟩
    exact ⟨⟨B₀.eqs ++ B.eqs, B₀.pos ++ B.pos⟩,
      ⟨B₀, hB₀, rfl⟩, fun f hf => (List.mem_append.mp hf).elim (h11 f) (h21 f),
      fun g hg => (List.mem_append.mp hg).elim (h12 g) (h22 g)⟩

theorem interBasic_deg (X : SAd m) (B : BasicD m) :
    (interBasic X B).deg = X.deg + X.basics.length * B.deg := by
  have hkey : ∀ B' : BasicD m, (⟨B'.eqs ++ B.eqs, B'.pos ++ B.pos⟩ : BasicD m).deg
      = B'.deg + B.deg := by
    intro B'
    rw [BasicD.deg_cons, BasicD.deg_cons, BasicD.deg_cons, List.map_append, List.map_append,
      List.sum_append, List.sum_append]
    ring
  have hlist : ∀ l : List (BasicD m),
      (((l.map fun B' => (⟨B'.eqs ++ B.eqs, B'.pos ++ B.pos⟩ : BasicD m)).map
        BasicD.deg).sum) = (l.map BasicD.deg).sum + l.length * B.deg := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, hkey a, ih]
      ring
  simp only [interBasic, deg]
  rw [hlist X.basics]

/-- Intersect with the basic set of a single inequality `0 < Q`. -/
def interPos (X : SAd m) (Q : MvPolynomial (Fin m) ℝ) : SAd m :=
  interBasic X ⟨[], [Q]⟩

theorem interPos_deg (X : SAd m) (Q : MvPolynomial (Fin m) ℝ) :
    (interPos X Q).deg = X.deg + X.basics.length * atomDegD Q := by
  rw [interPos, interBasic_deg]
  simp [BasicD.deg, atomDegD]

end SAd

/-! ## Transport of `Basic`/`SA` to `BasicD`/`SAd` -/

namespace Basic

variable {m : ℕ}

/-- Transport a frozen `Basic m 0` to `BasicD m`. -/
def toD (B : Basic m 0) : BasicD m :=
  ⟨B.eqs.map (eapEquiv m), B.pos.map (eapEquiv m)⟩

theorem holds_toD (B : Basic m 0) (x : Fin m → ℝ) :
    (toD B).Holds x ↔ B.holds (EAChain.nil m) x := by
  constructor
  · intro h
    rw [toD] at h
    refine ⟨?_, ?_⟩
    · intro f hf
      rw [eaEval_eq_eval]
      exact h.1 (eapEquiv m f) (List.mem_map_of_mem hf)
    · intro g hg
      rw [eaEval_eq_eval]
      exact h.2 (eapEquiv m g) (List.mem_map_of_mem hg)
  · intro h
    rw [toD]
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
      rw [← eaEval_eq_eval]
      exact h.1 f hf
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
      rw [← eaEval_eq_eval]
      exact h.2 f hf

theorem deg_toD (B : Basic m 0) : (toD B).deg = B.deg := by
  have hlist : ∀ l : List (EAPoly m 0),
      (((l.map (eapEquiv m)).map atomDegD).sum) = (l.map atomDeg).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, atomDegD,
        ← atomDeg_eq m a]
  rw [toD, BasicD.deg_cons, Basic.deg, List.map_append, List.sum_append]
  rw [hlist B.eqs, hlist B.pos]

end Basic

namespace SAd

variable {m : ℕ}

/-- Transport an `SAd m` to the frozen `SA m`. -/
def toSA (X : SAd m) : SA m := ⟨X.basics.map BasicD.toBasic⟩

theorem set_toSA (X : SAd m) : (toSA X).set = X.set := by
  have key : ∀ B : BasicD m, ∀ x : Fin m → ℝ,
      ((BasicD.toBasic B).holds (EAChain.nil m) x ↔ B.Holds x) := by
    intro B x
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro Q hQ
        have h1 := h.1 ((eapEquiv m).symm Q) (List.mem_map_of_mem hQ)
        rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply] at h1
        exact h1
      · intro Q hQ
        have h2 := h.2 ((eapEquiv m).symm Q) (List.mem_map_of_mem hQ)
        rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply] at h2
        exact h2
    · intro h
      rw [BasicD.toBasic]
      refine ⟨?_, ?_⟩
      · intro g hg
        obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hg
        rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply]
        exact h.1 Q hQ
      · intro g hg
        obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hg
        rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply]
        exact h.2 Q hQ
  ext x
  simp only [toSA, SA.set, set, List.mem_map]
  constructor
  · rintro ⟨B, ⟨B₀, hB₀, rfl⟩, h⟩
    exact ⟨B₀, hB₀, (key B₀ x).mp h⟩
  · rintro ⟨B, hB, h⟩
    exact ⟨BasicD.toBasic B, ⟨B, hB, rfl⟩, (key B x).mpr h⟩

theorem deg_toSA (X : SAd m) : (toSA X).deg = X.deg := by
  have hlist : ∀ l : List (MvPolynomial (Fin m) ℝ),
      (((l.map (eapEquiv m).symm).map atomDeg).sum) = (l.map atomDegD).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, atomDegD,
        atomDeg_eq m ((eapEquiv m).symm a), AlgEquiv.apply_symm_apply]
  have key : ∀ B : BasicD m, ((BasicD.toBasic B).deg) = B.deg := by
    intro B
    rw [BasicD.toBasic, BasicD.deg_cons, Basic.deg, List.map_append, List.sum_append]
    rw [hlist B.eqs, hlist B.pos]
  rw [toSA, SA.deg, deg, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro B _
  exact key B

end SAd

end Work.WilE4
