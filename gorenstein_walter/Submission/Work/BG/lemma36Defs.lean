import Mathlib
import Submission.Work.BG.Core24
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.L33DDefs
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.kerLeOfMulAutInv

/-!
# `Work.BG.lemma36Defs` — vocabulary for BG Lemma 3.6 (`Work.BG.lemma36`)

This module contains **only definitions** (no `sorry`), so that the lemmas delegated for
`Work.BG.lemma36` can import it without inheriting the target's `sorry`.

The proof plan is in `Submission/Work/BG/NOTES_lemma36_plan.md`.  Recall the repair of the
printed proof: the formal conclusion only asks for *some* `a ∈ Irr(U)` with `K ⊄ ker a` and
`2 * D.n * a(1) < χ(1)`, so one takes `a` of **minimal degree** (`aMin`) among the
irreducibles of `U = ↥(Uin C)` not trivial on `K`.

Vocabulary:

* `irrDeg a` — the degree `a(1)` of an irreducible character, as a natural number;
* `nontrivialOn K a` — `a` is not trivial on `K` (as a character of `↥(Uin C)`);
* `aMin D C K hne` — an element of `nontrivialOn K` of minimal `irrDeg`
  (`aMin_spec` gives membership and minimality);
* `sOrbitU D C hDC a` — the `S`-orbit of `a ∈ Irr(U)` under the conjugation action
  `L33D.phiS` of `D.S` on `U`;
* `lamOrbitOfU C a` — the `Λ`-orbit of `a` in the sense of BG Remark 3.1, realised as the set
  of `ν ∈ Irr(H₀)` whose restriction to `U` contains `a`
  (Remark 3.1: `ν ∈ Λ(a) ⟺ a ∈ supp(ν|_U)`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {X : Type} [Group X] [Finite X]

/-! ## 1. The degree of an irreducible character as a natural number -/

/-- The degree `a(1)` of an irreducible character, as a natural number. -/
noncomputable def irrDeg (a : IrreducibleCharacter X) : ℕ :=
  Classical.choose (irreducibleCharacter_apply_one_eq_pos_natCast a)

/-- `irrDeg` computes `a(1)`. -/
theorem irrDeg_spec (a : IrreducibleCharacter X) :
    ((a : ClassFunction X ℂ) 1) = ((irrDeg a : ℕ) : ℂ) :=
  (Classical.choose_spec (irreducibleCharacter_apply_one_eq_pos_natCast a)).2

/-- The degree of an irreducible character is positive. -/
theorem irrDeg_pos (a : IrreducibleCharacter X) : 0 < irrDeg a :=
  (Classical.choose_spec (irreducibleCharacter_apply_one_eq_pos_natCast a)).1

/-! ## 2. `U`-characters nontrivial on `K`, and `a_min` -/

section Main

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- `a ∈ Irr(U)` is not trivial on `K` (`U` read inside `H₀`). -/
def nontrivialOn (C : Sec2Ctx G) (K : Subgroup G) (a : IrreducibleCharacter ↥(Uin C)) : Prop :=
  ∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K ∧
    (a : ClassFunction ↥(Uin C) ℂ) u ≠ (a : ClassFunction ↥(Uin C) ℂ) 1

/-- The irreducibles of `U = ↥(Uin C)` that are not trivial on `K`. -/
def nontrivialIrr (C : Sec2Ctx G) (K : Subgroup G) :
    Set (IrreducibleCharacter ↥(Uin C)) :=
  {a | nontrivialOn C K a}

/-- The irreducibles of `U` nontrivial on `K`, as a finset. -/
noncomputable def nontrivialIrrFinset (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))] :
    Finset (IrreducibleCharacter ↥(Uin C)) := by
  classical
  exact Finset.univ.filter (fun a => a ∈ nontrivialIrr C K)

theorem mem_nontrivialIrrFinset (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    {a : IrreducibleCharacter ↥(Uin C)} :
    a ∈ nontrivialIrrFinset C K ↔ a ∈ nontrivialIrr C K := by
  classical
  simp only [nontrivialIrrFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem nontrivialIrrFinset_nonempty (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (hne : (nontrivialIrr C K).Nonempty) : (nontrivialIrrFinset C K).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, (mem_nontrivialIrrFinset C K).mpr ha⟩

/-- **The minimal-degree irreducible of `U` nontrivial on `K`.**  This is the `a` of the
repaired route to BG Lemma 3.6: the formal conclusion only asks for some `a ∈ Irr(U)` with
`K ⊄ ker a` and `2 * D.n * a(1) < χ(1)`, so the minimal one is optimal. -/
noncomputable def aMin (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (hne : (nontrivialIrr C K).Nonempty) : IrreducibleCharacter ↥(Uin C) :=
  Classical.choose (Finset.exists_min_image (nontrivialIrrFinset C K) irrDeg
    (nontrivialIrrFinset_nonempty C K hne))

theorem aMin_mem (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (hne : (nontrivialIrr C K).Nonempty) : aMin C K hne ∈ nontrivialIrr C K :=
  (mem_nontrivialIrrFinset C K).mp (Classical.choose_spec (Finset.exists_min_image
    (nontrivialIrrFinset C K) irrDeg (nontrivialIrrFinset_nonempty C K hne))).1

theorem aMin_min (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (hne : (nontrivialIrr C K).Nonempty) {b : IrreducibleCharacter ↥(Uin C)}
    (hb : b ∈ nontrivialIrr C K) : irrDeg (aMin C K hne) ≤ irrDeg b :=
  (Classical.choose_spec (Finset.exists_min_image (nontrivialIrrFinset C K) irrDeg
    (nontrivialIrrFinset_nonempty C K hne))).2 b ((mem_nontrivialIrrFinset C K).mpr hb)

/-- `aMin` is nontrivial on `K`, i.e. it witnesses `K ⊄ ker a`. -/
theorem aMin_nontrivial (C : Sec2Ctx G) (K : Subgroup G) [Fintype ↥(Uin C)] [Fintype (IrreducibleCharacter ↥(Uin C))]
    (hne : (nontrivialIrr C K).Nonempty) :
    ∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K ∧
      (aMin C K hne : ClassFunction ↥(Uin C) ℂ) u ≠
        (aMin C K hne : ClassFunction ↥(Uin C) ℂ) 1 :=
  aMin_mem C K hne

end Main

/-! ## 3. The two orbits attached to `a ∈ Irr(U)` -/

section Orbits

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (D : BGData G) (C : Sec2Ctx G)

/-- The `S`-orbit of a class function of `U = ↥(Uin C)` under the conjugation action
`L33D.phiS` of the Sylow `2`-subgroup `D.S` on `U`. -/
noncomputable def sOrbitU (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) : Set (ClassFunction ↥(Uin C) ℂ) :=
  {b | ∃ s : ↥(D.S), b = ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom a}

/-- The `Λ`-orbit of `a ∈ Irr(U)` in the sense of BG Remark 3.1: the irreducibles of `H₀`
having `a` as a constituent of their restriction to `U`.  (Remark 3.1: there is a unique
`Λ`-orbit `Λ(a)` with `ν|_U = a₁ + … + aₙ` for all `ν ∈ Λ(a)`, so `ν ∈ Λ(a) ⟺ a` is a
constituent of `ν|_U`.) -/
def lamOrbitOfU (C : Sec2Ctx G) [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (a : ClassFunction ↥(Uin C) ℂ) : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {ν | IsIrreducibleCharacter ν ∧
    ClassFunction.inner (ClassFunction.restrict (Uin C) ν) a ≠ 0}

end Orbits

end Work.BG
