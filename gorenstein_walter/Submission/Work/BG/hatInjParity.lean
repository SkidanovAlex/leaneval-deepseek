import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.oddCardFixedOfOddSum
import Submission.Work.BG.multiplicityDegreeNat

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory

/-!
# Column parity of the Glauberman correspondence

This file proves `Work.BG.hatInjParity`: for a finite group `U` of odd order with an involutive
automorphism `σ` and `β ∈ Irr(C_U(σ))`, an *odd* number of `σ`-invariant irreducible characters of
`U` has `β` appearing with odd multiplicity in the restriction to `C_U(σ)`.

The proof has three ingredients, all of which are isolated below.

* `twist`: the action `α ↦ α ∘ σ` on `Irr(U)`, an involution whose fixed points are exactly the
  `σ`-invariant irreducible characters.  Because `σ` fixes `C = C_U(σ)` pointwise, `α` and
  `α ∘ σ` have the *same* restriction to `C`.
* `Work.BG.multiplicityDegreeNat` (the analytic input): the degree-weighted multiplicity sum
  `Σ_{α ∈ Irr U} (α|_C, β)_C · α(1) = [U : C] · β(1)` (Fourier expansion of the induced character
  `β^U` at `1`).
* `Work.BG.oddCardFixedOfOddSum` (the combinatorial input): for an involution of a finite type
  with an invariant `ℕ`-weight, oddness of the total weight forces oddness of the number of fixed
  points of odd weight.

The main theorem `hatInjParity_aux` is stated for an abstract subgroup `C` pointwise fixed by `σ`;
`hatInjParity` is its specialisation to `C = Work.BG.fixedSubgroup σ`.
-/

section Twist

variable {U : Type} [Group U]

/-- Conjugation-twist of an irreducible character along an automorphism `σ`:
`α ↦ α ∘ σ`. -/
noncomputable def twist (σ : MulAut U) (α : IrreducibleCharacter U) : IrreducibleCharacter U :=
  ⟨ClassFunction.compHom (σ : U →* U) (α : ClassFunction U ℂ),
    α.isIrreducible.compHom_of_surjective σ.surjective⟩

@[simp] theorem twist_coe (σ : MulAut U) (α : IrreducibleCharacter U) :
    ((twist σ α : IrreducibleCharacter U) : ClassFunction U ℂ) =
      ClassFunction.compHom (σ : U →* U) (α : ClassFunction U ℂ) := rfl

theorem twist_apply (σ : MulAut U) (α : IrreducibleCharacter U) (u : U) :
    (twist σ α : ClassFunction U ℂ) u = (α : ClassFunction U ℂ) (σ u) :=
  ClassFunction.compHom_apply _ _ u

/-- `twist σ` is an involution when `σ` is. -/
theorem twist_involutive (σ : MulAut U) (hσ : σ * σ = 1) (α : IrreducibleCharacter U) :
    twist σ (twist σ α) = α := by
  have h : ∀ u : U, σ (σ u) = u := by
    intro u
    have := congrArg (fun e : MulAut U => e u) hσ
    simpa using this
  apply IrreducibleCharacter.ext
  apply ClassFunction.ext
  intro u
  rw [twist_apply, twist_apply, h]

/-- The fixed points of `twist σ` are exactly the `σ`-invariant irreducible characters. -/
theorem twist_eq_self_iff (σ : MulAut U) (α : IrreducibleCharacter U) :
    twist σ α = α ↔ ∀ u : U, (α : ClassFunction U ℂ) (σ u) = (α : ClassFunction U ℂ) u := by
  constructor
  · intro h u
    have := congrArg (fun β : IrreducibleCharacter U => (β : ClassFunction U ℂ) u) h
    simpa [twist_apply] using this
  · intro h
    apply IrreducibleCharacter.ext
    apply ClassFunction.ext
    intro u
    rw [twist_apply]
    exact h u

end Twist

/-- If `σ` fixes every element of `C` pointwise, then `α` and `twist σ α` have the same
restriction to `C`. -/
theorem restrict_twist_of_eq {U : Type} [Group U] (σ : MulAut U) (C : Subgroup U)
    (hfix : ∀ c : ↥C, σ (c : U) = (c : U)) (α : IrreducibleCharacter U) :
    ClassFunction.restrict C (twist σ α : ClassFunction U ℂ) =
      ClassFunction.restrict C (α : ClassFunction U ℂ) := by
  apply ClassFunction.ext
  intro c
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, twist_apply, hfix c]

/-- An odd integer is a natural number of the shape `2k+1` with `k : ℤ`: used to identify the
parity condition of `hatInjParity` with `Odd` of the multiplicity. -/
theorem exists_int_odd_iff (n : ℕ) :
    (∃ k : ℤ, (n : ℂ) = ((2 * k + 1 : ℤ) : ℂ)) ↔ Odd n := by
  constructor
  · rintro ⟨k, hk⟩
    have key : ((n : ℤ) : ℂ) = ((2 * k + 1 : ℤ) : ℂ) := by
      rw [Int.cast_natCast, hk]
    have hk'' : (n : ℤ) = 2 * k + 1 := Int.cast_inj.mp key
    have : Odd ((n : ℤ)) := ⟨k, hk''⟩
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩

/-- **Column parity of the Glauberman correspondence**, abstract form: `C` is a subgroup of `U`
fixed pointwise by the involution `σ`. -/
theorem hatInjParity_aux {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    (C : Subgroup U) (hfix : ∀ c : ↥C, σ (c : U) = (c : U))
    [Fintype ↥C] [Invertible (Nat.card ↥C : ℂ)]
    (β : IrreducibleCharacter ↥C) :
    Odd (Nat.card {α : SigmaInvIrr U σ // ∃ k : ℤ,
      ClassFunction.inner
        (ClassFunction.restrict C ((α : IrreducibleCharacter U) : ClassFunction U ℂ))
        (β : ClassFunction ↥C ℂ) = ((2 * k + 1 : ℤ) : ℂ)}) := by
  classical
  haveI : Fintype (IrreducibleCharacter U) := Fintype.ofFinite _
  -- The multiplicity of `β` in `α|_C`.
  let p : IrreducibleCharacter U → ℕ :=
    fun α => Classical.choose (IrreducibleCharacter.restrictionMultiplicity_natCast C α β)
  have hp : ∀ α : IrreducibleCharacter U,
      ClassFunction.restrictionMultiplicity C (α : ClassFunction U ℂ)
        (β : ClassFunction ↥C ℂ) = (p α : ℂ) :=
    fun α => Classical.choose_spec (IrreducibleCharacter.restrictionMultiplicity_natCast C α β)
  -- The degree of `α`.
  let d : IrreducibleCharacter U → ℕ :=
    fun α => Classical.choose α.isIrreducible.exists_natDegree_charValue_one_dvd_card
  have hd : ∀ α : IrreducibleCharacter U, (α : ClassFunction U ℂ) 1 = (d α : ℂ) :=
    fun α => (Classical.choose_spec α.isIrreducible.exists_natDegree_charValue_one_dvd_card).2.1
  have hd_odd : ∀ α : IrreducibleCharacter U, Odd (d α) :=
    fun α => hU.of_dvd_nat
      (Classical.choose_spec α.isIrreducible.exists_natDegree_charValue_one_dvd_card).2.2
  -- The degree of `β`.
  let dβ : ℕ := Classical.choose β.isIrreducible.exists_natDegree_charValue_one_dvd_card
  have hβ : (β : ClassFunction ↥C ℂ) 1 = (dβ : ℂ) :=
    (Classical.choose_spec β.isIrreducible.exists_natDegree_charValue_one_dvd_card).2.1
  have hC_odd : Odd (Nat.card ↥C) := hU.of_dvd_nat ⟨C.index, (Subgroup.card_mul_index C).symm⟩
  have hdβ_odd : Odd dβ := hC_odd.of_dvd_nat
    (Classical.choose_spec β.isIrreducible.exists_natDegree_charValue_one_dvd_card).2.2
  have hindex_odd : Odd C.index :=
    hU.of_dvd_nat ⟨Nat.card ↥C, (Subgroup.index_mul_card C).symm⟩
  -- The degree-weighted multiplicity sum.
  have hsum : (∑ α : IrreducibleCharacter U, p α * d α) = C.index * dβ :=
    multiplicityDegreeNat C β p hp d hd dβ hβ
  have hodd_prod : Odd (∑ α : IrreducibleCharacter U, p α * d α) :=
    hsum ▸ hindex_odd.mul hdβ_odd
  -- Oddness survives dropping the odd factors `d α`.
  have hodd_p : Odd (∑ α : IrreducibleCharacter U, p α) := by
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd_prod ⊢
    rw [← hodd_prod]
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show ((d α : ℕ) : ZMod 2) = 1 from (ZMod.natCast_eq_one_iff_odd).mpr (hd_odd α)]
    ring
  -- `p` is invariant under the twist.
  have hp_inv : ∀ α : IrreducibleCharacter U, p (twist σ α) = p α := by
    intro α
    have h2 : (p (twist σ α) : ℂ) = (p α : ℂ) := by
      rw [← hp (twist σ α), ← hp α, ClassFunction.restrictionMultiplicity_def,
        ClassFunction.restrictionMultiplicity_def, restrict_twist_of_eq σ C hfix α]
    exact Nat.cast_inj.mp h2
  have hodd_fixed : Odd (Nat.card {α : IrreducibleCharacter U // twist σ α = α ∧ Odd (p α)}) :=
    oddCardFixedOfOddSum (twist σ) (twist_involutive σ hσ) p hp_inv hodd_p
  -- The parity condition of the statement is exactly `Odd (p α)`.
  have key : ∀ α : IrreducibleCharacter U,
      Odd (p α) ↔ ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict C (α : ClassFunction U ℂ))
        (β : ClassFunction ↥C ℂ) = ((2 * k + 1 : ℤ) : ℂ) := by
    intro α
    have h1 : ClassFunction.inner (ClassFunction.restrict C (α : ClassFunction U ℂ))
        (β : ClassFunction ↥C ℂ) = (p α : ℂ) := by
      rw [← ClassFunction.restrictionMultiplicity_def]
      exact hp α
    rw [h1]
    exact (exists_int_odd_iff (p α)).symm
  -- Transport the count along the involution.
  have hcard : Nat.card {α : SigmaInvIrr U σ // ∃ k : ℤ,
        ClassFunction.inner (ClassFunction.restrict C ((α : IrreducibleCharacter U) : ClassFunction U ℂ))
          (β : ClassFunction ↥C ℂ) = ((2 * k + 1 : ℤ) : ℂ)}
      = Nat.card {α : IrreducibleCharacter U // twist σ α = α ∧ Odd (p α)} := by
    let toFun : {α : SigmaInvIrr U σ // ∃ k : ℤ,
        ClassFunction.inner (ClassFunction.restrict C ((α : IrreducibleCharacter U) : ClassFunction U ℂ))
          (β : ClassFunction ↥C ℂ) = ((2 * k + 1 : ℤ) : ℂ)}
        → {α : IrreducibleCharacter U // twist σ α = α ∧ Odd (p α)} :=
      fun a => ⟨a.1.1, (twist_eq_self_iff σ a.1.1).mpr a.1.2, (key a.1.1).mpr a.2⟩
    let invFun : {α : IrreducibleCharacter U // twist σ α = α ∧ Odd (p α)}
        → {α : SigmaInvIrr U σ // ∃ k : ℤ,
        ClassFunction.inner (ClassFunction.restrict C ((α : IrreducibleCharacter U) : ClassFunction U ℂ))
          (β : ClassFunction ↥C ℂ) = ((2 * k + 1 : ℤ) : ℂ)} :=
      fun b => ⟨⟨b.1, (twist_eq_self_iff σ b.1).mp b.2.1⟩, (key b.1).mp b.2.2⟩
    exact Nat.card_congr ⟨toFun, invFun, (by intro a; rfl), (by intro b; rfl)⟩
  rw [hcard]
  exact hodd_fixed

open OddOrder.RepresentationTheory in
/-- **Column parity of the Glauberman correspondence.** For a finite group `U` of odd order with an
involutive automorphism `σ` and `β ∈ Irr(C_U(σ))`, an *odd* number of `σ`-invariant irreducible
characters of `U` has `β` appearing with odd multiplicity in the restriction to `C_U(σ)`.

Route: `Σ_{α ∈ Irr U} (α|_{C}, β)·α(1) = β^U(1) = [U : C]·β(1)` (Fourier expansion of the induced
character `β^U` at `1`), every irreducible character of an odd-order group has odd degree, and the
non-`σ`-invariant `α` come in pairs `{α, α^σ}` with equal multiplicity `(α^σ|_{C}, β) = (α|_{C}, β)`
(since `σ` fixes `C` pointwise). -/
theorem hatInjParity {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(Work.BG.fixedSubgroup σ)] [Invertible (Nat.card ↥(Work.BG.fixedSubgroup σ) : ℂ)]
    (β : IrreducibleCharacter ↥(Work.BG.fixedSubgroup σ)) :
    Odd (Nat.card {α : Work.BG.SigmaInvIrr U σ // ∃ k : ℤ,
      ClassFunction.inner
        (ClassFunction.restrict (Work.BG.fixedSubgroup σ)
          ((α : IrreducibleCharacter U) : ClassFunction U ℂ))
        (β : ClassFunction ↥(Work.BG.fixedSubgroup σ) ℂ) = ((2 * k + 1 : ℤ) : ℂ)}) :=
  hatInjParity_aux hU σ hσ (Work.BG.fixedSubgroup σ) (fun c => c.2) β

end Work.BG
