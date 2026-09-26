import Submission.Work.Nielsen

open FreeGroup
set_option autoImplicit false

/-!
# The termination measure of the two-phase Nielsen reduction

The classical reduction of a free basis (Lyndon–Schupp Prop. I.4.1 /
Magnus–Karrass–Solitar Thm. 3.1–3.2; see `NielsenReductionBlueprint.lean`)
has two phases:

  * *Phase 1* (unbalanced side): a slot move strictly decreases the total
    reduced length `N = Σᵢ |wᵢ|`;
  * *Phase 2* (balanced side): at constant length, a slot move strictly
    decreases a lexicographic *energy*.

This file makes the *termination* part of that scheme precise and proves it in
full generality:

    energy_terminates :
        WellFounded (fun x y => N x < N y ∨ (N x = N y ∧ e x < e y))

i.e. a binary relation in which every step either strictly decreases `N`, or
keeps `N` equal and strictly decreases an arbitrary ℕ-valued energy `e`, is
well-founded: the measure is the lexicographic pair `(N x, e x)` of natural
numbers.  No property of the energy beyond "ℕ-valued" is needed for
termination, so this part is independent of the still-open combinatorial
content of the balanced-side analysis (which will later supply the specific
energy and prove that the specific balanced move decreases it).

For concreteness the file also defines a *positional* word energy
(`wordEnergy`, the standard base-`B` lexicographic weight, most significant
letter first; cf. A. J. Bene, arXiv:1010.5275, §4) and its tuple-level sum
`tupleEnergy`.  The choice of base and letter ranking is left as a parameter.
-/

namespace Submission.Nielsen

noncomputable section

/-- Lexicographic order on pairs, built from a relation on each coordinate:
`(a, b) < (a', b')` iff `ra a a'`, or `a = a'` and `rb b b'`. -/
def LexLT {α β : Type*} (ra : α → α → Prop) (rb : β → β → Prop)
    (x y : α × β) : Prop :=
  ra x.1 y.1 ∨ (x.1 = y.1 ∧ rb x.2 y.2)

/-- The lexicographic combination of two well-founded relations is
well-founded. -/
theorem LexLT_wf {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}
    (hwa : WellFounded ra) (hwb : WellFounded rb) :
    WellFounded (LexLT ra rb) := by
  let C : α → Prop := fun a' : α => ∀ b' : β, Acc (LexLT ra rb) (a', b')
  have hstep : ∀ a' : α, (∀ a'' : α, ra a'' a' → C a'') → C a' := by
    intro a' hia b'
    refine WellFounded.induction hwb (C := fun b'' : β => Acc (LexLT ra rb) (a', b'')) (a := b') ?_
    intro b'' hib
    exact Acc.intro (a', b'') (by
      intro q hq
      rcases q with ⟨a0, b0⟩
      rcases hq with ha0 | hab0
      · exact hia a0 ha0 b0
      · rcases hab0 with ⟨heq, hb0⟩
        have ha0 : a0 = a' := by simpa using heq
        subst a0
        exact hib b0 hb0)
  have hAll : ∀ a : α, C a := fun a => WellFounded.induction hwa (C := C) (a := a) hstep
  exact ⟨fun p => by rcases p with ⟨a, b⟩; exact hAll a b⟩

/-- **Termination of the two-phase reduction.**  Any relation whose steps
either strictly decrease `N`, or keep `N` equal and strictly decrease the
ℕ-valued energy `e`, is well-founded (this is the formal content of the
`energy_terminates` item of `NielsenReductionBlueprint.lean`). -/
theorem energy_terminates {α : Type*} (N e : α → ℕ) :
    WellFounded (fun x y : α =>
      N x < N y ∨ (N x = N y ∧ e x < e y)) := by
  have hwf : WellFounded (LexLT (· < ·) (· < ·) : (ℕ × ℕ) → (ℕ × ℕ) → Prop) :=
    LexLT_wf wellFounded_lt wellFounded_lt
  have himg : WellFounded (InvImage (LexLT (· < ·) (· < ·) : (ℕ × ℕ) → (ℕ × ℕ) → Prop)
      (fun x : α => (N x, e x))) :=
    InvImage.wf (fun x : α => (N x, e x)) hwf
  change WellFounded (InvImage (LexLT (· < ·) (· < ·) : (ℕ × ℕ) → (ℕ × ℕ) → Prop)
      (fun x : α => (N x, e x)))
  exact himg

/-- Positional word energy with base `B` and digit function `rank`
(most significant letter first).  For a (reduced) word this is
`Σⱼ B^{ℓ-1-j} · rank(L[j])`. -/
def wordEnergy {α : Type*} (B : ℕ) (rank : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: t => B ^ t.length * rank a + wordEnergy B rank t

lemma wordEnergy_nil {α : Type*} (B : ℕ) (rank : α → ℕ) :
    wordEnergy B rank ([] : List α) = 0 := rfl

lemma wordEnergy_cons {α : Type*} (B : ℕ) (rank : α → ℕ) (a : α) (t : List α) :
    wordEnergy B rank (a :: t) = B ^ t.length * rank a + wordEnergy B rank t := rfl

/-- Total word energy of the basis-image tuple of an automorphism of `F_n`,
with letters ranked by `rank : Fin n × Bool → ℕ` and base `B`. -/
def tupleEnergy (n : ℕ) (B : ℕ) (rank : (Fin n × Bool) → ℕ)
    (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  ∑ i : Fin n, wordEnergy B rank (FreeGroup.toWord (α (FreeGroup.of i)))

/-- The two-phase termination measure specialised to automorphisms of `F_n`:
`N` is the total reduced length and the energy is the tuple word energy. -/
theorem energy_terminates_aut (n : ℕ) (B : ℕ) (rank : (Fin n × Bool) → ℕ) :
    WellFounded (fun α β : MulAut (FreeGroup (Fin n)) =>
      N α < N β ∨ (N α = N β ∧ tupleEnergy n B rank α < tupleEnergy n B rank β)) := by
  exact energy_terminates (N := fun α : MulAut (FreeGroup (Fin n)) => N α)
    (e := fun α => tupleEnergy n B rank α)

end

end Submission.Nielsen
