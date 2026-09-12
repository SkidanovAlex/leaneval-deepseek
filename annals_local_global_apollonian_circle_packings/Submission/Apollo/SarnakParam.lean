/-
The seed and first S-mate steps of the Sarnak parametrization of the tangent
partners of a circle.

Fix a Descartes quadruple w of the orbit and the circle a = w i at index i,
with cyclic order (a, b, c, d) = (w i, w(i+1), w(i+2), w(i+3)).  The form
attached at (w, i) is f(x,y) = qfEval w i x y = A x² + B x y + C y² with
A = a+b, B = a+b+c-d, C = a+c (QForms), discriminant B²-4AC = -4a²
(QForms.qf_discriminant).  Sarnak's observation: the curvatures of the
circles tangent to the circle of curvature a are exactly {f(x,y) - a :
gcd(x,y) = 1}.

This file proves the base of that parametrization and its first steps, all as
exact integer identities:

  * seed  : the three tangent partners of a inside its own Descartes
            quadruple are f(1,0)-a, f(0,1)-a, f(1,-1)-a  (`sarnak_seed_*`);
  * steps : replacing the partner b = w(i+1) (resp. c = w(i+2),
            d = w(i+3)) by its S-mate (S-move at that coordinate) gives the
            new value f(1,-2)-a (resp. f(2,-1)-a, f(1,1)-a)
            (`sarnak_step_one` etc.), with the other two partners unchanged
            (their seed parametrization persists).

Iterating these moves walks around the ring of Descartes quadruples
containing the circle; the remaining task of the full orbit parametrization
is to close the induction, i.e. to prove that the form attached at each
subsequent quadruple is a PSL(2,Z)-translate of the original form (equivalently
that the "new parameter" rule composes), after which every tangent partner of
the circle is congruent modulo a to a value of the single original form.
-/
import Submission.Apollo.QForms
import Submission.Apollo.OneStep
import Submission.Apollo.Occurrence
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- the cyclic successor b = w(i+1) is f(1,0) - a. -/
lemma sarnak_seed_one (w : Fin 4 → ℤ) (i : Fin 4) :
    qfEval w i 1 0 - w i = w (i + 1) := by
  dsimp [qfEval, qfA]
  ring

/-- the second cyclic partner c = w(i+2) is f(0,1) - a. -/
lemma sarnak_seed_two (w : Fin 4 → ℤ) (i : Fin 4) :
    qfEval w i 0 1 - w i = w (i + 2) := by
  dsimp [qfEval, qfC]
  ring

/-- the third cyclic partner d = w(i+3) is f(1,-1) - a. -/
lemma sarnak_seed_three (w : Fin 4 → ℤ) (i : Fin 4) :
    qfEval w i 1 (-1) - w i = w (i + 3) := by
  dsimp [qfEval, qfA, qfB, qfC]
  ring

/-- replacing the partner w(i+1) by its S-mate (S-move at index i+1) gives
the value f(1,-2) - a. -/
lemma sarnak_step_one (w : Fin 4 → ℤ) (i : Fin 4) :
    (gen (i + 1) • w) (i + 1) = qfEval w i 1 (-2) - w i := by
  rw [gen_smul_apply]
  simp
  have hs := sum_excl_three w i (i + 1) (i + 2) (i + 3)
    (fin_ne_succ : i ≠ i + 1) (fin_ne_succ2 : i ≠ i + 2) (fin_ne_succ3 : i ≠ i + 3)
    (fin_succ_ne : i + 1 ≠ i + 2) (fin_succ2_ne : i + 1 ≠ i + 3) (fin_succ3_ne : i + 2 ≠ i + 3)
  rw [hs]
  dsimp [qfEval, qfA, qfB, qfC]
  ring

/-- replacing the partner w(i+2) by its S-mate gives f(2,-1) - a. -/
lemma sarnak_step_two (w : Fin 4 → ℤ) (i : Fin 4) :
    (gen (i + 2) • w) (i + 2) = qfEval w i 2 (-1) - w i := by
  rw [gen_smul_apply]
  simp
  have hs := sum_excl_three w i (i + 2) (i + 1) (i + 3)
    (fin_ne_succ2 : i ≠ i + 2) (fin_ne_succ : i ≠ i + 1) (fin_ne_succ3 : i ≠ i + 3)
    (fin_succ_ne.symm : i + 2 ≠ i + 1) (fin_succ3_ne : i + 2 ≠ i + 3) (fin_succ2_ne : i + 1 ≠ i + 3)
  rw [hs]
  dsimp [qfEval, qfA, qfB, qfC]
  ring

/-- replacing the partner w(i+3) by its S-mate gives f(1,1) - a. -/
lemma sarnak_step_three (w : Fin 4 → ℤ) (i : Fin 4) :
    (gen (i + 3) • w) (i + 3) = qfEval w i 1 1 - w i := by
  rw [gen_smul_apply]
  simp
  have hs := sum_excl_three w i (i + 3) (i + 1) (i + 2)
    (fin_ne_succ3 : i ≠ i + 3) (fin_ne_succ : i ≠ i + 1) (fin_ne_succ2 : i ≠ i + 2)
    (fin_succ2_ne.symm : i + 3 ≠ i + 1) (fin_succ3_ne.symm : i + 3 ≠ i + 2) (fin_succ_ne : i + 1 ≠ i + 2)
  rw [hs]
  dsimp [qfEval, qfA, qfB, qfC]
  ring

/-- after the S-mate step at i+1, the two surviving partners still have their
seed parametrization with the original form. -/
lemma sarnak_step_one_survivors (w : Fin 4 → ℤ) (i : Fin 4) :
    (gen (i + 1) • w) (i + 2) = qfEval w i 0 1 - w i ∧
    (gen (i + 1) • w) (i + 3) = qfEval w i 1 (-1) - w i := by
  constructor
  · rw [other_coord_eq w (i + 1) (i + 2) (fin_succ_ne.symm)]
    exact (sarnak_seed_two w i).symm
  · rw [other_coord_eq w (i + 1) (i + 3) (fin_succ2_ne.symm)]
    exact (sarnak_seed_three w i).symm

/-- moving the partner at i+1 replaces the attached form by the linear
substitution (x,y) ↦ (x, -2x - y). -/
lemma form_update_one (w : Fin 4 → ℤ) (i : Fin 4) (x y : ℤ) :
    qfEval (gen (i + 1) • w) i x y = qfEval w i x (-2 * x - y) := by
  have h0 : (gen (i + 1) • w) i = w i := other_coord_eq w (i + 1) i fin_ne_succ
  have h1 := sarnak_step_one w i
  have h2 : (gen (i + 1) • w) (i + 2) = w (i + 2) := other_coord_eq w (i + 1) (i + 2) fin_succ_ne.symm
  have h3 : (gen (i + 1) • w) (i + 3) = w (i + 3) := other_coord_eq w (i + 1) (i + 3) fin_succ2_ne.symm
  simp only [qfEval, qfA, qfB, qfC]
  rw [h0, h1, h2, h3]
  simp only [qfEval, qfA, qfB, qfC]
  ring

/-- moving the partner at i+2 replaces the attached form by the linear
substitution (x,y) ↦ (x + 2y, -y). -/
lemma form_update_two (w : Fin 4 → ℤ) (i : Fin 4) (x y : ℤ) :
    qfEval (gen (i + 2) • w) i x y = qfEval w i (x + 2 * y) (-y) := by
  have h0 : (gen (i + 2) • w) i = w i := other_coord_eq w (i + 2) i fin_ne_succ2
  have h1 := sarnak_step_two w i
  have h2 : (gen (i + 2) • w) (i + 1) = w (i + 1) := other_coord_eq w (i + 2) (i + 1) fin_succ_ne
  have h3 : (gen (i + 2) • w) (i + 3) = w (i + 3) := other_coord_eq w (i + 2) (i + 3) fin_succ3_ne.symm
  simp only [qfEval, qfA, qfB, qfC]
  rw [h0, h1, h2, h3]
  simp only [qfEval, qfA, qfB, qfC]
  ring

/-- moving the partner at i+3 replaces the attached form by the linear
substitution (x,y) ↦ (x, -y). -/
lemma form_update_three (w : Fin 4 → ℤ) (i : Fin 4) (x y : ℤ) :
    qfEval (gen (i + 3) • w) i x y = qfEval w i x (-y) := by
  have h0 : (gen (i + 3) • w) i = w i := other_coord_eq w (i + 3) i fin_ne_succ3
  have h1 := sarnak_step_three w i
  have h2 : (gen (i + 3) • w) (i + 1) = w (i + 1) := other_coord_eq w (i + 3) (i + 1) fin_succ2_ne
  have h3 : (gen (i + 3) • w) (i + 2) = w (i + 2) := other_coord_eq w (i + 3) (i + 2) fin_succ3_ne
  simp only [qfEval, qfA, qfB, qfC]
  rw [h0, h1, h2, h3]
  simp only [qfEval, qfA, qfB, qfC]
  ring

/-- a Fin-4 index different from i is one of its three cyclic successors. -/
lemma fin_succ_cases (i j : Fin 4) (hji : j ≠ i) : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by
  fin_cases i <;> fin_cases j <;> simp at hji ⊢

/-- moving any coordinate different from i updates the attached form by a
linear substitution: every value of the new form is a value of the old form. -/
lemma form_update_any (w : Fin 4 → ℤ) (i j : Fin 4) (hji : j ≠ i) (x y : ℤ) :
    ∃ x' y' : ℤ, qfEval (gen j • w) i x y = qfEval w i x' y' := by
  rcases (fin_succ_cases i j hji) with rfl | rfl | rfl
  · exact ⟨x, -2 * x - y, form_update_one w i x y⟩
  · exact ⟨x + 2 * y, -y, form_update_two w i x y⟩
  · exact ⟨x, -y, form_update_three w i x y⟩



/-- generic step induction over a reflexive-transitive closure. -/
lemma of_rt {α : Type} {r : α → α → Prop} (Q : α → Prop)
    (hstep : ∀ (b c : α), r b c → Q b → Q c) :
    ∀ {a c : α}, Relation.ReflTransGen r a c → Q a → Q c := by
  intro a c h
  induction h with
  | refl => intro q; exact q
  | tail hprev hstep' ih => intro q; exact hstep _ _ hstep' (ih q)

lemma rt_symm {α : Type} {r : α → α → Prop} (hsym : ∀ {a b : α}, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl (hsym hstep)) ih

lemma reflTransGen_of_eqvGen {α : Type} {r : α → α → Prop} (hsym : ∀ {a b : α}, r a b → r b a)
    {a b : α} (h : Relation.EqvGen r a b) : Relation.ReflTransGen r a b := by
  induction h with
  | rel a b hrel => exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hrel
  | refl a => exact Relation.ReflTransGen.refl
  | symm a b h ih => exact rt_symm hsym ih
  | trans a b c h₁ h₂ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₁ ih₂

lemma eqvGen_of_reflTransGen {α : Type} {r : α → α → Prop}
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl a
  | tail hprev hstep ih =>
      apply Relation.EqvGen.trans
      · exact ih
      · exact Relation.EqvGen.rel _ _ hstep

/-- the generating step of `sameCircle` is symmetric (S-moves are
involutions). -/
lemma replaceStep_symm {o₁ o₂ : Occ} (h : replaceStep o₁ o₂) : replaceStep o₂ o₁ := by
  rcases h with ⟨w, i, j, hne, rfl, rfl⟩
  exact ⟨gen i • w, i, j, hne, rfl,
    (congrArg (fun t : Fin 4 → ℤ => (t, j)) (gen_smul_gen_smul w i)).symm⟩

/-- ring reachability: quadruples obtained from w by S-moves away from index
i (the circle at index i is never moved). -/
def ringReach (i : Fin 4) (w u : Fin 4 → ℤ) : Prop :=
  Relation.ReflTransGen (fun x y : Fin 4 → ℤ => ∃ j : Fin 4, j ≠ i ∧ y = gen j • x) w u

/-- the parametrization invariant along the ring: the circle value stays
w i and the attached form at each reachable quadruple takes only values of
the single form attached at (w,i). -/
def FormValues (w : Fin 4 → ℤ) (i : Fin 4) (u : Fin 4 → ℤ) : Prop :=
  u i = w i ∧ ∀ x y : ℤ, ∃ x' y' : ℤ, qfEval u i x y = qfEval w i x' y'

lemma formValues_step (w : Fin 4 → ℤ) (i : Fin 4) {b c : Fin 4 → ℤ}
    (h : ∃ j : Fin 4, j ≠ i ∧ c = gen j • b) (q : FormValues w i b) :
    FormValues w i c := by
  rcases h with ⟨j, hji, rfl⟩
  rcases q with ⟨hbi, hq⟩
  constructor
  · rw [other_coord_eq b j i (hji.symm : i ≠ j)]
    exact hbi
  · intro x y
    rcases form_update_any b i j hji x y with ⟨x₁, y₁, h₁⟩
    rcases hq x₁ y₁ with ⟨x₂, y₂, h₂⟩
    exact ⟨x₂, y₂, h₁.trans h₂⟩

/-- the form invariant holds along the whole ring walk around the circle. -/
theorem formValues_of_ringReach (w : Fin 4 → ℤ) (i : Fin 4) :
    ∀ u : Fin 4 → ℤ, ringReach i w u → FormValues w i u := by
  intro u h
  exact of_rt (FormValues w i) (fun b c h' q => formValues_step w i (b := b) (c := c) h' q)
    h ⟨rfl, fun x y => ⟨x, y, rfl⟩⟩

/-- a ring-reachable quadruple carries the same circle at index i. -/
theorem sameCircle_of_ringReach (w u : Fin 4 → ℤ) (i : Fin 4) :
    ringReach i w u → sameCircle (w, i) (u, i) := by
  intro h
  exact of_rt (fun x : Fin 4 → ℤ => sameCircle (w, i) (x, i))
    (fun b c (h' : ∃ j : Fin 4, j ≠ i ∧ c = gen j • b)
        (q : sameCircle (w, i) (b, i)) => by
      rcases h' with ⟨j, hji, rfl⟩
      exact Relation.EqvGen.trans (x := (w, i)) (y := (b, i)) (z := (gen j • b, i)) q
        (Relation.EqvGen.rel (b, i) (gen j • b, i)
          (⟨b, j, i, hji, rfl, rfl⟩ : replaceStep (b, i) (gen j • b, i))))
    h (Relation.EqvGen.refl (w, i))

/-- one step of a sameCircle chain, as a quadruple ring step. -/
lemma ringReach_of_occStep (w : Fin 4 → ℤ) (i : Fin 4) {bocc cocc : Occ}
    (hstep : replaceStep bocc cocc) (q : ringReach i w bocc.1 ∧ bocc.2 = i) :
    ringReach i w cocc.1 ∧ cocc.2 = i := by
  rcases hstep with ⟨v, k, l, hkl, hb, hc⟩
  have h1 : bocc.2 = l := by simpa using (congrArg (fun o : Occ => o.2) hb)
  have hl : l = i := by
    rw [q.2] at h1
    exact h1.symm
  have hk : k ≠ i := by
    intro hki
    apply hkl
    rw [hki, hl]
  constructor
  · refine Relation.ReflTransGen.tail q.1 ⟨k, hk, ?_⟩
    have hbf : bocc.1 = v := congrArg (fun o : Occ => o.1) hb
    have hcf : cocc.1 = gen k • v := congrArg (fun o : Occ => o.1) hc
    rw [hcf, hbf]
  · have h2 := congrArg (fun o : Occ => o.2) hc
    rw [hl] at h2
    exact h2

/-- any sameCircle occurrence chain around the circle is a ring walk. -/
theorem ringReach_of_sameCircle (w u : Fin 4 → ℤ) (i : Fin 4) :
    sameCircle (w, i) (u, i) → ringReach i w u := by
  intro h
  have hrt : Relation.ReflTransGen replaceStep (w, i) (u, i) :=
    reflTransGen_of_eqvGen (fun h' => replaceStep_symm h') h
  exact (of_rt (fun o : Occ => ringReach i w o.1 ∧ o.2 = i)
    (fun b c h' q => ringReach_of_occStep w i h' q) hrt
      ⟨Relation.ReflTransGen.refl, rfl⟩).1

/-- Sarnak parametrization (weak, exact): every tangent-partner value of the
circle at (w,i), over the whole ring of Descartes quadruples containing it at
index i, is a value of the single quadratic form attached at (w,i). -/
theorem sarnak_ring_partner (w : Fin 4 → ℤ) (i : Fin 4) :
    ∀ u : Fin 4 → ℤ, ringReach i w u → ∀ j : Fin 4, j ≠ i →
      ∃ x y : ℤ, u j = qfEval w i x y - w i := by
  intro u hu j hji
  have hF := formValues_of_ringReach w i u hu
  rcases hF with ⟨hui, hq⟩
  rcases (fin_succ_cases i j hji) with rfl | rfl | rfl
  · rcases hq 1 0 with ⟨x, y, hx⟩
    refine ⟨x, y, ?_⟩
    calc
      u (i + 1) = qfEval u i 1 0 - u i := (sarnak_seed_one u i).symm
      _ = qfEval w i x y - w i := by rw [hx, hui]
  · rcases hq 0 1 with ⟨x, y, hx⟩
    refine ⟨x, y, ?_⟩
    calc
      u (i + 2) = qfEval u i 0 1 - u i := (sarnak_seed_two u i).symm
      _ = qfEval w i x y - w i := by rw [hx, hui]
  · rcases hq 1 (-1) with ⟨x, y, hx⟩
    refine ⟨x, y, ?_⟩
    calc
      u (i + 3) = qfEval u i 1 (-1) - u i := (sarnak_seed_three u i).symm
      _ = qfEval w i x y - w i := by rw [hx, hui]

/-- Sarnak parametrization in occurrence form: if p is a tangent partner
occurrence of a same-circle occurrence o of (w,i), then the partner value is
a value of the single form attached at (w,i). -/
theorem sarnak_occ_partner (w : Fin 4 → ℤ) (i : Fin 4) :
    ∀ (o p : Occ), sameCircle (w, i) o → tangent o p → o.2 ≠ p.2 →
      ∃ x y : ℤ, ovalue p = qfEval w i x y - w i := by
  intro o p ho htan hne
  -- o.2 = i (replaceStep never moves the index):
  have ho2 : o.2 = i := by
    have hrt : Relation.ReflTransGen replaceStep (w, i) o :=
      reflTransGen_of_eqvGen (fun h' => replaceStep_symm h') ho
    exact (of_rt (fun oo : Occ => oo.2 = i)
      (fun b c h' q => by
        rcases h' with ⟨v, k, l, hkl, rfl, rfl⟩
        exact q) hrt rfl)
  -- o.1 is ring-reachable from w:
  have hoPair : o = (o.1, i) := Prod.ext rfl ho2
  have hring : ringReach i w o.1 := by
    rw [hoPair] at ho
    exact ringReach_of_sameCircle w o.1 i ho
  have hpi : p.2 ≠ i := by
    intro hpi
    rw [ho2] at hne
    exact hne hpi.symm
  have hp1 : o.1 = p.1 := htan.1
  have hmain := sarnak_ring_partner w i o.1 hring p.2 hpi
  rcases hmain with ⟨x, y, hxy⟩
  refine ⟨x, y, ?_⟩
  calc
    ovalue p = p.1 p.2 := rfl
    _ = o.1 p.2 := by rw [hp1]
    _ = qfEval w i x y - w i := hxy

end Apollo
