/-
  WilC5 — core definitions for the syntactic transfinite construction of a `κ`-saturated
  elementary extension.

  This file sets up the *level-indexed* version of the construction.  At level `x` the available
  constants are `C x = SatC L M κ x` (the seed constants for `M` plus the constants of birth level
  `< x`); the constants created *at* level `x` are the types `SatTyp2 L (C x)` over `C x`.

  We build, by well-founded recursion on the well-ordered type `SatIdx κ`:

  * `SatData3 x` — a structure in the language `L[[C x]]`;
  * `SatTh3 x` — its complete theory;
  * `SatSpec3 x T` — the specification at level `x`, given the theories of the lower levels;
  * `SatSpecG x` — the specification at level `x` for the theories of the construction.

  The main results of this file are the unfolding lemma `SatData3_eq`, the membership (peeling)
  lemmas for `SatSpec3`/`SatSpecG`, and the basic combinatorics of the inclusions `SatInc`.
-/
import Mathlib
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatIdxBdd2
import Submission.Work.WilC5.SatIdxNoMax

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- The index type `SatIdx κ` has no greatest element. -/
instance instNoMaxOrderSatIdx (κ : Cardinal.{0}) : NoMaxOrder (SatIdx κ) := SatIdxNoMax κ

omit instM in
/-- The inclusion maps `SatInc` do not depend on the proof of the inequality. -/
theorem SatInc_proof_irrel {x y : SatIdx κ} (h h' : x ≤ y) :
    SatInc L M κ h = SatInc L M κ h' :=
  congrArg (SatInc L M κ) (Subsingleton.elim h h')

omit instM in
/-- The inclusion of the constants of level `x` into those of level `succ x`. -/
noncomputable def SatIncSucc (x : SatIdx κ) : SatC L M κ x → SatC L M κ (Order.succ x) :=
  SatInc L M κ (le_of_lt (Order.lt_succ x))

/-- The constant created at level `x` for the type `q` over the constants of level `x`. -/
noncomputable def SatNewConst (x : SatIdx κ) (q : SatTyp2 L (SatC L M κ x)) :
    SatC L M κ (Order.succ x) :=
  Sum.inr ⟨⟨x, Order.lt_succ x⟩, (SatNew_eq L M κ x).symm ▸ q⟩

omit instM in
@[simp]
theorem SatIncSucc_inl (x : SatIdx κ) (m : M) :
    SatIncSucc L M κ x (Sum.inl m) = Sum.inl m := rfl

omit instM in
@[simp]
theorem SatIncSucc_inr (x : SatIdx κ) (u : SatIdx κ) (hu : u < x) (a : SatNew L M κ u) :
    SatIncSucc L M κ x (Sum.inr ⟨⟨u, hu⟩, a⟩) =
      Sum.inr ⟨⟨u, lt_of_lt_of_le hu (le_of_lt (Order.lt_succ x))⟩, a⟩ := rfl

@[simp]
theorem SatNewConst_eq (x : SatIdx κ) (q : SatTyp2 L (SatC L M κ x)) :
    SatNewConst L M κ x q =
      Sum.inr ⟨⟨x, Order.lt_succ x⟩, (SatNew_eq L M κ x).symm ▸ q⟩ := rfl

theorem SatNewConst_injective (x : SatIdx κ) : Function.Injective (SatNewConst L M κ x) := by
  intro q q' h
  have h2 : ((SatNew_eq L M κ x).symm ▸ q) = ((SatNew_eq L M κ x).symm ▸ q') := by
    have h3 := Sum.inr_injective h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h3).2
  exact (cast_inj (SatNew_eq L M κ x).symm).mp h2

/-- A newly created constant is not an old one. -/
theorem SatNewConst_not_mem_range (x : SatIdx κ) (q : SatTyp2 L (SatC L M κ x)) :
    ∀ c : SatC L M κ x, SatIncSucc L M κ x c ≠ SatNewConst L M κ x q := by
  intro c h
  cases c with
  | inl m => exact absurd h (by simp)
  | inr p =>
    obtain ⟨⟨u, hu⟩, a⟩ := p
    have h2 := Sum.inr_injective h
    have h3 : (⟨u, lt_of_lt_of_le hu (le_of_lt (Order.lt_succ x))⟩ :
        {y : SatIdx κ // y < Order.succ x}) = ⟨x, Order.lt_succ x⟩ :=
      (Sigma.mk.inj_iff.mp h2).1
    exact absurd (congrArg Subtype.val h3) (ne_of_lt hu)

/-- The witness axioms at level `x`: for every type `q` over the constants of level `x` that is
consistent with the theory `T` at level `x`, the sentences saying that the new constant `c_q`
satisfies `q`.  These sentences live in the language of level `succ x`. -/
noncomputable def SatWitLev (x : SatIdx κ) (T : (L[[SatC L M κ x]]).Theory) :
    (L[[SatC L M κ (Order.succ x)]]).Theory :=
  ⋃ (q : SatTyp2 L (SatC L M κ x)), ⋃ (_ : SatCons2 T q),
    SatWit2 (SatIncSucc L M κ x) (SatNewConst L M κ x) q

omit instM in
theorem mem_SatWitLev {x : SatIdx κ} {T : (L[[SatC L M κ x]]).Theory}
    {σ : (L[[SatC L M κ (Order.succ x)]]).Sentence} :
    σ ∈ SatWitLev L M κ x T ↔
      ∃ (q : SatTyp2 L (SatC L M κ x)) (_ : SatCons2 T q),
        σ ∈ SatWit2 (SatIncSucc L M κ x) (SatNewConst L M κ x) q := by
  simp only [SatWitLev, Set.mem_iUnion]

/-- The specification at level `x`, given the theories of all lower levels: the image of the
elementary diagram of `M`, the images of the lower theories, and the witness axioms for the types
over the constants of the lower levels consistent with the corresponding theory.

It is defined directly by its membership condition (`mem_SatSpec3` is `Iff.rfl`), which is the form
in which it is used. -/
noncomputable def SatSpec3 (x : SatIdx κ)
    (T : ∀ y : SatIdx κ, y < x → (L[[SatC L M κ y]]).Theory) :
    (L[[SatC L M κ x]]).Theory :=
  {σ | (∃ τ ∈ L.elementaryDiagram M,
        (SatLangMap (Sum.inl : M → SatC L M κ x)).onSentence τ = σ) ∨
      (∃ (y : SatIdx κ) (hy : y < x) (τ : (L[[SatC L M κ y]]).Sentence), τ ∈ T y hy ∧
        (SatLangMap (SatInc L M κ (le_of_lt hy))).onSentence τ = σ) ∨
      (∃ (p : SatIdx κ) (hp : p < x) (q : SatTyp2 L (SatC L M κ p)) (_ : SatCons2 (T p hp) q)
        (φ : (L[[SatC L M κ p]]).Formula (q.1 ⊕ Fin 1)), φ ∈ q.2 ∧
        (SatLangMap (SatInc L M κ (Order.succ_le_of_lt hp))).onSentence
          (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ) = σ)}

/-- The membership (peeling) lemma for the specification at level `x`. -/
theorem mem_SatSpec3 {x : SatIdx κ} {T : ∀ y : SatIdx κ, y < x → (L[[SatC L M κ y]]).Theory}
    {σ : (L[[SatC L M κ x]]).Sentence} :
    σ ∈ SatSpec3 L M κ x T ↔
      (∃ τ ∈ L.elementaryDiagram M, (SatLangMap (Sum.inl : M → SatC L M κ x)).onSentence τ = σ) ∨
      (∃ (y : SatIdx κ) (hy : y < x) (τ : (L[[SatC L M κ y]]).Sentence), τ ∈ T y hy ∧
        (SatLangMap (SatInc L M κ (le_of_lt hy))).onSentence τ = σ) ∨
      (∃ (p : SatIdx κ) (hp : p < x) (q : SatTyp2 L (SatC L M κ p)) (_ : SatCons2 (T p hp) q)
        (φ : (L[[SatC L M κ p]]).Formula (q.1 ⊕ Fin 1)), φ ∈ q.2 ∧
        (SatLangMap (SatInc L M κ (Order.succ_le_of_lt hp))).onSentence
          (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ) = σ) :=
  Iff.rfl

/-- The recursive construction of the structure at level `x`, together with its language. -/
noncomputable def SatData3 : ∀ x : SatIdx κ, Σ (N : Type), (L[[SatC L M κ x]]).Structure N :=
  (inferInstance : WellFounded (· < · : SatIdx κ → SatIdx κ → Prop)).fix fun x rec =>
    let T : ∀ y : SatIdx κ, y < x → (L[[SatC L M κ y]]).Theory := fun y hy =>
      letI := (rec y hy).2
      (L[[SatC L M κ y]]).completeTheory (rec y hy).1
    if h : (SatSpec3 L M κ x T).IsSatisfiable then
      ⟨h.some.Carrier, h.some.struc⟩
    else ⟨PUnit, Inhabited.trivialStructure (L[[SatC L M κ x]])⟩

/-- The carrier of the structure at level `x`. -/
noncomputable def SatMod3 (x : SatIdx κ) : Type := (SatData3 L M κ x).1

/-- The structure at level `x`. -/
@[instance_reducible]
noncomputable def SatStruc3 (x : SatIdx κ) :
    (L[[SatC L M κ x]]).Structure (SatMod3 L M κ x) := (SatData3 L M κ x).2


/-- The complete theory of the structure at level `x`. -/
noncomputable def SatTh3 (x : SatIdx κ) : (L[[SatC L M κ x]]).Theory :=
  letI := SatStruc3 L M κ x
  (L[[SatC L M κ x]]).completeTheory (SatMod3 L M κ x)

/-- The specification at level `x` for the theories of the construction. -/
noncomputable def SatSpecG (x : SatIdx κ) : (L[[SatC L M κ x]]).Theory :=
  SatSpec3 L M κ x (fun _ _ => SatTh3 L M κ _)

theorem mem_SatSpecG {x : SatIdx κ} {σ : (L[[SatC L M κ x]]).Sentence} :
    σ ∈ SatSpecG L M κ x ↔
      (∃ τ ∈ L.elementaryDiagram M, (SatLangMap (Sum.inl : M → SatC L M κ x)).onSentence τ = σ) ∨
      (∃ (y : SatIdx κ) (hy : y < x) (τ : (L[[SatC L M κ y]]).Sentence), τ ∈ SatTh3 L M κ y ∧
        (SatLangMap (SatInc L M κ (le_of_lt hy))).onSentence τ = σ) ∨
      (∃ (p : SatIdx κ) (hp : p < x) (q : SatTyp2 L (SatC L M κ p))
        (_ : SatCons2 (SatTh3 L M κ p) q)
        (φ : (L[[SatC L M κ p]]).Formula (q.1 ⊕ Fin 1)), φ ∈ q.2 ∧
        (SatLangMap (SatInc L M κ (Order.succ_le_of_lt hp))).onSentence
          (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ) = σ) :=
  mem_SatSpec3 L M κ (x := x) (T := fun _ _ => SatTh3 L M κ _)

/-- The unfolding lemma for the recursion. -/
theorem SatData3_eq (x : SatIdx κ) :
    SatData3 L M κ x =
      (if h : (SatSpecG L M κ x).IsSatisfiable then
        ⟨h.some.Carrier, h.some.struc⟩
      else ⟨PUnit, Inhabited.trivialStructure (L[[SatC L M κ x]])⟩) := by
  rw [SatData3, WellFounded.fix_eq]
  rfl

/-- The structure at level `x` always has a nonempty carrier. -/
theorem SatMod3_nonempty (x : SatIdx κ) : Nonempty (SatMod3 L M κ x) := by
  rw [SatMod3, SatData3_eq L M κ x]
  split_ifs with h
  · exact h.some.instNonempty
  · exact ⟨PUnit.unit⟩

end Work.WilC5
