/-
  Area `WilC4aTS`: Tarski--Seidenberg for one projection (hole `C4a_TS1` of area C4a).

  This file: the *vocabulary* of the area.

  We work with the frozen vocabulary `WilkiesDesign.E` (`EAPoly`, `Basic`, `SA`, `eaEval`)
  transported to the plain polynomial ring `MvPolynomial (Fin m) ℝ`.  Working in `Fin m` (rather
  than `Fin m ⊕ Fin 0`) is what lets us split off the last variable with
  `MvPolynomial.finSuccEquiv`, which is the shape the elimination needs.

  Contents:
  * the transport `EAPoly m 0 ≃ₐ[ℝ] Poly m` and its compatibility with `eaEval`/`Basic.holds`;
  * `BasicD m`, `SAd m`: the transported basic/SA vocabulary, with `set`, `toSA`, `set_toSA`;
  * the semialgebraic algebra on `SAd m`: `empty`, `univ`, `union`, `inter`, `compl` (so that
    `SAd` is closed under boolean operations, as needed to compose sub-formulas during
    elimination) and the corresponding `set` lemmas;
  * `projLast` lemmas.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC4aTS
open WilkiesDesign WilkiesDesign.E
open MvPolynomial

/-! ## 1. The polynomial-ring vocabulary -/

/-- Polynomials in `m` real variables. -/
abbrev Poly (m : ℕ) := MvPolynomial (Fin m) ℝ

/-- The index equivalence `Fin m ⊕ Fin 0 ≃ Fin m`. -/
def sumFinZeroEquiv (m : ℕ) : Fin m ⊕ Fin 0 ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_zero m))

/-- Transport the frozen `EAPoly m 0` to `Poly m`. -/
def eapEquiv (m : ℕ) : EAPoly m 0 ≃ₐ[ℝ] Poly m :=
  MvPolynomial.renameEquiv ℝ (sumFinZeroEquiv m)

theorem eapEquiv_apply (m : ℕ) (Q : EAPoly m 0) :
    eapEquiv m Q = MvPolynomial.rename (sumFinZeroEquiv m) Q := rfl

/-- `eaEval` along the empty chain is evaluation of the transported polynomial. -/
theorem eaEval_eq_eval (m : ℕ) (Q : EAPoly m 0) (x : Fin m → ℝ) :
    eaEval (EAChain.nil m) Q x = MvPolynomial.eval x (eapEquiv m Q) := by
  have hpt : ∀ i : Fin m ⊕ Fin 0,
      (Sum.elim x fun j : Fin 0 => Real.exp ((EAChain.nil m).ell j x)) i
        = x (sumFinZeroEquiv m i) := by
    intro i
    rcases i with i | i
    · show x i = x (sumFinZeroEquiv m (Sum.inl i))
      rw [show sumFinZeroEquiv m (Sum.inl i) = i from by
        simp [sumFinZeroEquiv, finSumFinEquiv]]
    · exact i.elim0
  unfold eaEval
  rw [eapEquiv_apply, MvPolynomial.eval_rename]
  exact congrArg (fun y => MvPolynomial.eval y Q) (funext hpt)

/-- `atomDeg` is preserved by the transport. -/
theorem atomDeg_eq (m : ℕ) (Q : EAPoly m 0) :
    atomDeg Q = (eapEquiv m Q).totalDegree + 1 := by
  simp only [atomDeg, eapEquiv, MvPolynomial.totalDegree_renameEquiv]

/-! ## 2. Basic and SA sets over `Poly m` -/

/-- A basic semialgebraic set: equations `= 0` and strict inequalities `> 0`. -/
structure BasicD (m : ℕ) where
  eqs : List (Poly m)
  pos : List (Poly m)

namespace BasicD

variable {m : ℕ}

/-- Satisfaction of a basic set. -/
def Holds (B : BasicD m) (x : Fin m → ℝ) : Prop :=
  (∀ f ∈ B.eqs, MvPolynomial.eval x f = 0) ∧ (∀ g ∈ B.pos, 0 < MvPolynomial.eval x g)

/-- The set defined by a basic set. -/
def set (B : BasicD m) : Set (Fin m → ℝ) := {x | B.Holds x}

/-- Degree of a basic set, matching the frozen `Basic.deg`. -/
def deg (B : BasicD m) : ℕ := ((B.eqs ++ B.pos).map fun P => P.totalDegree + 1).sum

/-- Intersection of two basic sets. -/
def inter (B₁ B₂ : BasicD m) : BasicD m :=
  ⟨B₁.eqs ++ B₂.eqs, B₁.pos ++ B₂.pos⟩

/-- `Holds` of an intersection, in terms of `Holds` of the two parts. -/
theorem holds_inter_iff (B₁ B₂ : BasicD m) (x : Fin m → ℝ) :
    (B₁.inter B₂).Holds x ↔ B₁.Holds x ∧ B₂.Holds x := by
  simp only [Holds, inter, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun f hf => h1 f (Or.inl hf), fun g hg => h2 g (Or.inl hg)⟩,
      ⟨fun f hf => h1 f (Or.inr hf), fun g hg => h2 g (Or.inr hg)⟩⟩
  · rintro ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩
    exact ⟨fun f hf => hf.elim (fun h => h1a f h) (fun h => h2a f h),
      fun g hg => hg.elim (fun h => h1b g h) (fun h => h2b g h)⟩

@[simp] theorem set_inter (B₁ B₂ : BasicD m) :
    (B₁.inter B₂).set = B₁.set ∩ B₂.set := by
  ext x
  change (B₁.inter B₂).Holds x ↔ B₁.Holds x ∧ B₂.Holds x
  exact holds_inter_iff B₁ B₂ x

/-- Transport a `BasicD m` back to the frozen `Basic m 0`. -/
def toBasic (B : BasicD m) : Basic m 0 :=
  ⟨B.eqs.map (eapEquiv m).symm, B.pos.map (eapEquiv m).symm⟩

theorem holds_toBasic (B : BasicD m) (x : Fin m → ℝ) :
    (toBasic B).holds (EAChain.nil m) x ↔ B.Holds x := by
  constructor
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · have h1 := h.1 ((eapEquiv m).symm f) (List.mem_map_of_mem (f := (eapEquiv m).symm) hf)
      rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply] at h1
      exact h1
    · have h1 := h.2 ((eapEquiv m).symm g) (List.mem_map_of_mem (f := (eapEquiv m).symm) hg)
      rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply] at h1
      exact h1
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply]
      exact h.1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [eaEval_eq_eval, AlgEquiv.apply_symm_apply]
      exact h.2 g₀ hg₀

end BasicD

/-- The basic set consisting of the single strict inequality `g > 0`. -/
def BPos {m : ℕ} (g : Poly m) : BasicD m := ⟨[], [g]⟩

/-- The basic set consisting of the single equation `f = 0`. -/
def BEq {m : ℕ} (f : Poly m) : BasicD m := ⟨[f], []⟩

/-- `Holds` of `BPos g`. -/
theorem BPos_holds {m : ℕ} (g : Poly m) (x : Fin m → ℝ) :
    (BPos g).Holds x ↔ 0 < MvPolynomial.eval x g := by
  refine ⟨fun h => h.2 g (by simp [BPos]), fun h => ⟨?_, fun g' hg' => ?_⟩⟩
  · intro f hf; simp only [BPos, List.not_mem_nil] at hf
  · simp only [BPos, List.mem_singleton] at hg'
    subst hg'; exact h

/-- `Holds` of `BEq f`. -/
theorem BEq_holds {m : ℕ} (f : Poly m) (x : Fin m → ℝ) :
    (BEq f).Holds x ↔ MvPolynomial.eval x f = 0 := by
  refine ⟨fun h => h.1 f (by simp [BEq]), fun h => ⟨fun f' hf' => ?_, ?_⟩⟩
  · simp only [BEq, List.mem_singleton] at hf'
    subst hf'; exact h
  · intro g hg; simp only [BEq, List.not_mem_nil] at hg

@[simp] theorem BPos_set {m : ℕ} (g : Poly m) :
    (BPos g).set = {x | 0 < MvPolynomial.eval x g} := by
  ext x; exact BPos_holds g x

@[simp] theorem BEq_set {m : ℕ} (f : Poly m) :
    (BEq f).set = {x | MvPolynomial.eval x f = 0} := by
  ext x; exact BEq_holds f x

/-- The list of basic sets whose union is the complement of `B`.

The complement of `{∧fᵢ = 0 ∧ ∧gⱼ > 0}` is `⋃ᵢ {fᵢ ≠ 0} ∪ ⋃ⱼ {gⱼ ≤ 0}`; each `f ≠ 0` is a
union of the two strict inequalities `f > 0`, `-f > 0`, and each `g ≤ 0` is a union of the strict
inequality `-g > 0` and the equation `g = 0`.  The list is `(l₁ ++ l₂) ++ (l₃ ++ l₄)`. -/
def BasicD.complList {m : ℕ} (B : BasicD m) : List (BasicD m) :=
  ((B.eqs.map fun f => BPos f) ++ (B.eqs.map fun f => BPos (-f))) ++
    ((B.pos.map fun g => BPos (-g)) ++ (B.pos.map fun g => BEq g))

namespace BasicD

variable {m : ℕ} {B : BasicD m} {f g : Poly m}

theorem BPos_mem_complList (hf : f ∈ B.eqs) : BPos f ∈ B.complList := by
  simp only [complList, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl ⟨f, hf, rfl⟩)

theorem BPos_neg_mem_complList (hf : f ∈ B.eqs) : BPos (-f) ∈ B.complList := by
  simp only [complList, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨f, hf, rfl⟩)

theorem BPos_neg_mem_complList' (hg : g ∈ B.pos) : BPos (-g) ∈ B.complList := by
  simp only [complList, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨g, hg, rfl⟩)

theorem BEq_mem_complList (hg : g ∈ B.pos) : BEq g ∈ B.complList := by
  simp only [complList, List.mem_append, List.mem_map]
  exact Or.inr (Or.inr ⟨g, hg, rfl⟩)

/-- Membership in `complList` is exactly the negation of `Holds`. -/
theorem mem_complList_iff (x : Fin m → ℝ) :
    (∃ B' ∈ B.complList, B'.Holds x) ↔ ¬ B.Holds x := by
  constructor
  · rintro ⟨B', hB', hB'holds⟩ hB
    rw [complList, List.mem_append, List.mem_append, List.mem_append, List.mem_map,
      List.mem_map, List.mem_map, List.mem_map] at hB'
    rcases hB' with (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) | (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact absurd (hB.1 f hf) (ne_of_gt ((BPos_holds f x).mp hB'holds))
    · have h2 := (BPos_holds (-f) x).mp hB'holds
      rw [MvPolynomial.eval_neg] at h2
      exact absurd (hB.1 f hf) (ne_of_lt (by linarith))
    · have h2 := (BPos_holds (-g) x).mp hB'holds
      rw [MvPolynomial.eval_neg] at h2
      exact absurd (hB.2 g hg) (not_lt.mpr (by linarith))
    · have h0 := (BEq_holds g x).mp hB'holds
      exact absurd (hB.2 g hg) (by rw [h0]; exact lt_irrefl 0)
  · intro h
    by_cases hA : ∃ f ∈ B.eqs, MvPolynomial.eval x f ≠ 0
    · obtain ⟨fw, hfw, hne⟩ := hA
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨BPos (-fw), BPos_neg_mem_complList hfw, (BPos_holds (-fw) x).mpr ?_⟩
        rw [MvPolynomial.eval_neg]; linarith
      · exact ⟨BPos fw, BPos_mem_complList hfw, (BPos_holds fw x).mpr hgt⟩
    · have hB0 : ∃ g ∈ B.pos, ¬ (0 < MvPolynomial.eval x g) := by
        by_contra hcon
        rw [not_exists] at hcon
        have hall : ∀ g ∈ B.pos, 0 < MvPolynomial.eval x g := by
          intro g hg
          by_contra hng
          exact hcon g ⟨hg, hng⟩
        have hA' : ∀ f ∈ B.eqs, MvPolynomial.eval x f = 0 := by
          intro f hf
          by_contra hne
          exact hA ⟨f, hf, hne⟩
        exact h ⟨hA', hall⟩
      obtain ⟨gw, hgw, hle⟩ := hB0
      rcases lt_or_eq_of_le (le_of_not_gt hle) with hlt | heq
      · refine ⟨BPos (-gw), BPos_neg_mem_complList' hgw, (BPos_holds (-gw) x).mpr ?_⟩
        rw [MvPolynomial.eval_neg]; linarith
      · exact ⟨BEq gw, BEq_mem_complList hgw, (BEq_holds gw x).mpr heq⟩

end BasicD

/-- A semialgebraic set over `ℝ^m` in disjunctive normal form. -/
structure SAd (m : ℕ) where
  basics : List (BasicD m)

namespace SAd

variable {m : ℕ}

/-- The set defined by an `SAd`. -/
def set (X : SAd m) : Set (Fin m → ℝ) := {x | ∃ B ∈ X.basics, B.Holds x}

/-- The empty set. -/
def empty (m : ℕ) : SAd m := ⟨[]⟩

/-- Full space: one basic set with no conditions. -/
def univ (m : ℕ) : SAd m := ⟨[⟨[], []⟩]⟩

/-- Union. -/
def union (X Y : SAd m) : SAd m := ⟨X.basics ++ Y.basics⟩

/-- Intersection with a single basic set (each disjunct conjoined with `B`). -/
def interBasic (X : SAd m) (B : BasicD m) : SAd m :=
  ⟨X.basics.map fun B' => B'.inter B⟩

/-- The intersection of two unions of basic sets, as a union of basic sets.

`interListsAux l L'` is the list of all intersections `B ∩ B'`, `B ∈ l`, `B' ∈ L'`. -/
def interListsAux (l L' : List (BasicD m)) : List (BasicD m) :=
  l.flatMap fun B => L'.map fun B' => B'.inter B

/-- The intersection of a list of unions of basic sets, again in DNF.

`interLists [l₁, …, lₙ]` is the list of all intersections `B₁ ∩ ⋯ ∩ Bₙ`, `Bᵢ ∈ lᵢ`. -/
def interLists : List (List (BasicD m)) → List (BasicD m)
  | [] => [⟨[], []⟩]
  | l :: L => interListsAux l (interLists L)

/-- Intersection (distribution over DNF). -/
def inter (X Y : SAd m) : SAd m := ⟨interLists [X.basics, Y.basics]⟩

/-- Complement, by CNF-to-DNF expansion: `¬⋃ᵢ Bᵢ = ⋂ᵢ ¬Bᵢ`. -/
def compl (X : SAd m) : SAd m := ⟨interLists (X.basics.map BasicD.complList)⟩

@[simp] theorem mem_set {X : SAd m} {x : Fin m → ℝ} :
    x ∈ X.set ↔ ∃ B ∈ X.basics, B.Holds x := Iff.rfl

@[simp] theorem empty_set (m : ℕ) : (empty m).set = ∅ := by
  ext x; simp [empty, set]

@[simp] theorem univ_set (m : ℕ) : (univ m).set = Set.univ := by
  ext x; simp [univ, set, BasicD.Holds]

@[simp] theorem union_set (X Y : SAd m) : (union X Y).set = X.set ∪ Y.set := by
  ext x
  simp only [union, set, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨B, hB | hB, h⟩
    · exact Or.inl ⟨B, hB, h⟩
    · exact Or.inr ⟨B, hB, h⟩
  · rintro (⟨B, hB, h⟩ | ⟨B, hB, h⟩)
    · exact ⟨B, Or.inl hB, h⟩
    · exact ⟨B, Or.inr hB, h⟩

@[simp] theorem interBasic_set (X : SAd m) (B : BasicD m) :
    (interBasic X B).set = X.set ∩ B.set := by
  ext x
  rw [Set.mem_inter_iff]
  change (∃ B' ∈ X.basics.map (fun B' => B'.inter B), B'.Holds x) ↔
    (∃ B' ∈ X.basics, B'.Holds x) ∧ B.Holds x
  constructor
  · rintro ⟨B', hB', h⟩
    obtain ⟨B'', hB'', rfl⟩ := List.mem_map.mp hB'
    have h' := (BasicD.holds_inter_iff B'' B x).mp h
    exact ⟨⟨B'', hB'', h'.1⟩, h'.2⟩
  · rintro ⟨⟨B'', hB'', h₁⟩, h₂⟩
    exact ⟨B''.inter B, List.mem_map.mpr ⟨B'', hB'', rfl⟩,
      (BasicD.holds_inter_iff B'' B x).mpr ⟨h₁, h₂⟩⟩

theorem mem_interListsAux (l L' : List (BasicD m)) (x : Fin m → ℝ) :
    x ∈ (⟨interListsAux l L'⟩ : SAd m).set ↔
      (∃ B ∈ l, B.Holds x) ∧ x ∈ (⟨L'⟩ : SAd m).set := by
  rw [interListsAux, SAd.mem_set, SAd.mem_set]
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨B₁, hB₁, hB⟩ := List.mem_flatMap.mp hB
    obtain ⟨B₂, hB₂, rfl⟩ := List.mem_map.mp hB
    have h' := (BasicD.holds_inter_iff B₂ B₁ x).mp hx
    exact ⟨⟨B₁, hB₁, h'.2⟩, ⟨B₂, hB₂, h'.1⟩⟩
  · rintro ⟨⟨B₁, hB₁, h₁⟩, ⟨B₂, hB₂, h₂⟩⟩
    refine ⟨B₂.inter B₁, ?_, (BasicD.holds_inter_iff B₂ B₁ x).mpr ⟨h₂, h₁⟩⟩
    rw [List.mem_flatMap]
    exact ⟨B₁, hB₁, List.mem_map.mpr ⟨B₂, hB₂, rfl⟩⟩

theorem mem_interLists (L : List (List (BasicD m))) (x : Fin m → ℝ) :
    x ∈ (⟨interLists L⟩ : SAd m).set ↔ ∀ l ∈ L, ∃ B ∈ l, B.Holds x := by
  induction L with
  | nil => simp [interLists, BasicD.Holds]
  | cons l L ih =>
      simp only [interLists]
      rw [mem_interListsAux, ih]
      simp only [List.mem_cons, forall_eq_or_imp]

@[simp] theorem compl_set (X : SAd m) : X.compl.set = X.setᶜ := by
  ext x
  rw [Set.mem_compl_iff, compl, mem_interLists, SAd.mem_set]
  constructor
  · rintro h ⟨B, hB, hx⟩
    have h' : ∃ B' ∈ B.complList, B'.Holds x :=
      h (BasicD.complList B) (List.mem_map_of_mem hB)
    exact (BasicD.mem_complList_iff (B := B) x).mp h' hx
  · intro hx l hl
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hl
    exact (BasicD.mem_complList_iff (B := B) x).mpr (fun hcon => hx ⟨B, hB, hcon⟩)

@[simp] theorem inter_set (X Y : SAd m) : (inter X Y).set = X.set ∩ Y.set := by
  ext x
  rw [inter, mem_interLists, Set.mem_inter_iff, SAd.mem_set, SAd.mem_set]
  constructor
  · intro h
    exact ⟨h X.basics (by simp), h Y.basics (by simp)⟩
  · rintro ⟨hX, hY⟩ l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hX
    · exact hY

end SAd

/-- Transport an `SAd m` to the frozen `SA m`. -/
def SAd.toSA {m : ℕ} (X : SAd m) : SA m := ⟨X.basics.map BasicD.toBasic⟩

theorem SAd.set_toSA {m : ℕ} (X : SAd m) : (X.toSA).set = X.set := by
  ext x
  rw [SAd.mem_set]
  change (∃ B ∈ X.basics.map BasicD.toBasic, B.holds (EAChain.nil m) x) ↔
    ∃ B ∈ X.basics, B.Holds x
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨B₀, hB₀, (BasicD.holds_toBasic B₀ x).mp hx⟩
  · rintro ⟨B, hB, hx⟩
    exact ⟨B.toBasic, List.mem_map.mpr ⟨B, hB, rfl⟩, (BasicD.holds_toBasic B x).mpr hx⟩


/-- Transport a frozen `Basic m 0` to `BasicD m`. -/
def BasicD.ofBasic {m : ℕ} (B : Basic m 0) : BasicD m :=
  ⟨B.eqs.map (eapEquiv m), B.pos.map (eapEquiv m)⟩

theorem BasicD.set_ofBasic {m : ℕ} (B : Basic m 0) :
    (BasicD.ofBasic B).set = {x | B.holds (EAChain.nil m) x} := by
  ext x
  rw [BasicD.set]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rw [eaEval_eq_eval]
      exact h1 (eapEquiv m f) (List.mem_map_of_mem hf)
    · rw [eaEval_eq_eval]
      exact h2 (eapEquiv m g) (List.mem_map_of_mem hg)
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
      rw [← eaEval_eq_eval]
      exact h1 f₀ hf₀
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      rw [← eaEval_eq_eval]
      exact h2 g₀ hg₀

/-- Transport a frozen `SA m` to `SAd m`. -/
def SAd.ofSA {m : ℕ} (X : SA m) : SAd m := ⟨X.basics.map BasicD.ofBasic⟩

theorem SAd.set_ofSA {m : ℕ} (X : SA m) : (SAd.ofSA X).set = X.set := by
  ext x
  rw [SAd.mem_set, SA.set]
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    have hx' : x ∈ (BasicD.ofBasic B₀).set := hx
    rw [BasicD.set_ofBasic B₀] at hx'
    exact ⟨B₀, hB₀, hx'⟩
  · rintro ⟨B₀, hB₀, hx⟩
    refine ⟨BasicD.ofBasic B₀, List.mem_map_of_mem hB₀, ?_⟩
    have hx' : x ∈ {x | Basic.holds (EAChain.nil m) B₀ x} := hx
    rw [← BasicD.set_ofBasic B₀] at hx'
    exact hx' 

/-- Projection drops unions. -/
theorem projLast_union {m : ℕ} (A B : Set (Fin (m + 1) → ℝ)) :
    projLast (A ∪ B) = projLast A ∪ projLast B := by
  ext x
  simp only [projLast, Set.mem_union]
  constructor
  · rintro ⟨t, ht | ht⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr ⟨t, ht⟩
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact ⟨t, Or.inl ht⟩
    · exact ⟨t, Or.inr ht⟩

/-- The projection of an SA set is the union of the projections of its basic sets. -/
theorem projLast_set_eq_iUnion {m : ℕ} (X : SAd (m + 1)) :
    projLast X.set = ⋃ B ∈ X.basics, projLast B.set := by
  ext x
  simp only [projLast, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, B, hB, ht⟩
    exact ⟨B, hB, t, ht⟩
  · rintro ⟨B, hB, t, ht⟩
    exact ⟨t, B, hB, ht⟩

end Work.WilC4aTS
