import Mathlib

/-!
# The pointwise stabilizer of `{4,5,6}` inside `A₇`

We count the even permutations of `Fin 7` that fix the three points `4, 5, 6` pointwise.

A permutation fixing `{4,5,6}` pointwise is exactly a permutation of the complement
`{0,1,2,3}`, extended by the identity; this is the content of
`Equiv.Perm.subtypeEquivSubtypePerm`.  Under that equivalence the sign is preserved
(`Equiv.Perm.sign_ofSubtype`), so the count equals the number of even permutations of a
four-element type, which is `4!/2 = 12`.

Concretely we reduce the question, by an explicit chain of equivalences of subtypes, to
`Fintype.card {f : Equiv.Perm (Fin 4) // f.sign = 1} = 12`, a finite computation.
-/

namespace Work.DSTR

open Equiv

/-- The predicate cutting out `{0,1,2,3}` inside `Fin 7`. -/
private abbrev P7 : Fin 7 → Prop := fun a => a ∈ ({0,1,2,3} : Finset (Fin 7))

/-- Permutations of `Fin 7` that fix the complement of `{0,1,2,3}` pointwise, i.e. that fix
`{4,5,6}` pointwise. -/
private abbrev B : Type := {g : Equiv.Perm (Fin 7) // ∀ a, ¬ P7 a → g a = a}

/-- Fixing `{4,5,6}` pointwise is the same as fixing the complement of `{0,1,2,3}` pointwise. -/
private lemma pf_iff (g : Equiv.Perm (Fin 7)) :
    (∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q) ↔ (∀ a, ¬ P7 a → g a = a) := by
  have hiff : ∀ a : Fin 7, (¬ P7 a) ↔ a ∈ ({4,5,6} : Finset (Fin 7)) := by decide
  exact ⟨fun h a ha => h a ((hiff a).mp ha), fun h q hq => h q ((hiff q).mpr hq)⟩

/-- Replacing the pointwise-fixing condition by the complement formulation. -/
private noncomputable def E1 :
    {g : Equiv.Perm (Fin 7) //
        Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q} ≃
      {g : Equiv.Perm (Fin 7) // Equiv.Perm.sign g = 1 ∧ (∀ a, ¬ P7 a → g a = a)} :=
  Equiv.subtypeEquivRight (fun g => and_congr_right (fun _ => pf_iff g))

/-- Swapping the two conjuncts. -/
private noncomputable def E2 :
    {g : Equiv.Perm (Fin 7) // Equiv.Perm.sign g = 1 ∧ (∀ a, ¬ P7 a → g a = a)} ≃
      {g : Equiv.Perm (Fin 7) // (∀ a, ¬ P7 a → g a = a) ∧ Equiv.Perm.sign g = 1} :=
  Equiv.subtypeEquivRight (fun _ => and_comm)

/-- Flattening the nested subtype. -/
private noncomputable def E3 :
    {g : Equiv.Perm (Fin 7) // (∀ a, ¬ P7 a → g a = a) ∧ Equiv.Perm.sign g = 1} ≃
      {g : B // Equiv.Perm.sign g.1 = 1} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter (fun g : Equiv.Perm (Fin 7) => ∀ a, ¬ P7 a → g a = a)
    (fun g => Equiv.Perm.sign g = 1)).symm

/-- The pointwise stabilizer of `{4,5,6}` is the set of permutations of the complement
`{0,1,2,3}`, and this correspondence preserves the sign. -/
private noncomputable def E4 :
    {g : B // Equiv.Perm.sign g.1 = 1} ≃
      {f : Equiv.Perm (Subtype P7) // Equiv.Perm.sign f = 1} :=
  ((Equiv.subtypeEquivRight (fun f : Equiv.Perm (Subtype P7) => by
      rw [Equiv.Perm.subtypeEquivSubtypePerm_apply_coe, Equiv.Perm.sign_ofSubtype])).trans
    (Equiv.subtypeEquivOfSubtype (p := fun b : B => Equiv.Perm.sign b.1 = 1)
      (Equiv.Perm.subtypeEquivSubtypePerm P7))).symm

/-- The complement `{0,1,2,3}` is a four-element type. -/
private noncomputable def S : Subtype P7 ≃ Fin 4 :=
  (Finset.equivFin ({0,1,2,3} : Finset (Fin 7))).trans (finCongr (by decide))

/-- Transporting permutations along `S` preserves the sign. -/
private noncomputable def E5 :
    {f : Equiv.Perm (Subtype P7) // Equiv.Perm.sign f = 1} ≃
      {f : Equiv.Perm (Fin 4) // Equiv.Perm.sign f = 1} :=
  Equiv.subtypeEquiv (Equiv.permCongr S)
    (fun f => by simp [Equiv.Perm.sign_permCongr])

/-- The full bijection: even permutations of `Fin 7` fixing `{4,5,6}` pointwise correspond to
even permutations of `Fin 4`. -/
private noncomputable def E :
    {g : Equiv.Perm (Fin 7) //
        Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q} ≃
      {f : Equiv.Perm (Fin 4) // Equiv.Perm.sign f = 1} :=
  E1.trans (E2.trans (E3.trans (E4.trans E5)))

theorem A7PtwiseStab456 :
    (Finset.univ.filter (fun g : Equiv.Perm (Fin 7) =>
      Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q)).card = 12 := by
  have hcard : (Finset.univ.filter (fun g : Equiv.Perm (Fin 7) =>
        Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q)).card =
      Fintype.card {g : Equiv.Perm (Fin 7) //
        Equiv.Perm.sign g = 1 ∧ ∀ q ∈ ({4,5,6} : Finset (Fin 7)), g q = q} :=
    (Fintype.card_subtype _).symm
  rw [hcard]
  exact (Fintype.card_congr E).trans (by decide)

end Work.DSTR
