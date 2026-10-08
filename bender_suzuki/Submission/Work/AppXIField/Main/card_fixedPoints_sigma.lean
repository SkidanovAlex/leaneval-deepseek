import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.AppXIField.Main

/-- **Counting the fixed points of `σ b` on `F`.**

Let `F` be a finite field, `A` a finite (commutative) group embedded in `Fˣ` through `ι`,
with `|F| = |A| + 1` (so that `ι` is a bijection onto `Fˣ`), and let `B` act on `A` by
group automorphisms `φ` and on `F` by ring automorphisms `σ`, compatibly:
`σ b (ι a) = ι (φ b a)`.  Then for every `b`, the number of fixed points of `σ b` on `F`
equals the number of fixed points of `φ b` on `A` plus one.

Indeed, `σ b` fixes `0` (which is not in the image of `ι`), and on `Fˣ` the fixed points of
`σ b` correspond — through the bijection `ι` — exactly to the fixed points of `φ b` on `A`. -/
theorem card_fixedPoints_sigma {F : Type} [Field F] [Fintype F] {A B : Type*} [CommGroup A]
    [Group B] (ι : A →* Fˣ) (φ : B →* MulAut A) (σ : B →* (F ≃+* F))
    (hι : Function.Injective ι) (hcard : Nat.card F = Nat.card A + 1)
    (hσ : ∀ (b : B) (a : A), σ b (ι a : F) = (ι (φ b a) : F)) :
    ∀ b : B, Nat.card (Function.fixedPoints (σ b)) = Nat.card ↥{a : A | φ b a = a} + 1 := by
  intro b
  classical
  -- `ι` is injective and `|A| = |Fˣ|`, hence `ι` is surjective onto `Fˣ`.
  have hunits : Nat.card A = Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    simp
  have hsurj : Function.Surjective ι :=
    (hι.bijective_of_nat_card_le (le_of_eq hunits.symm)).2
  haveI : Finite A := Finite.of_injective ι hι
  let P : Set A := {a : A | φ b a = a}
  -- The map sending `none` to `0` and `some a` to `ι a`.
  let g : Option ↥P → ↥(Function.fixedPoints (σ b)) := fun o =>
    match o with
    | none => ⟨(0 : F), by show σ b (0 : F) = 0; exact map_zero (σ b)⟩
    | some a => ⟨(ι a.1 : F), by
        show σ b (↑(ι a.1) : F) = (ι a.1 : F)
        rw [hσ b a.1]
        exact congrArg (fun x => (ι x : F)) a.2⟩
  have hg : Function.Bijective g := by
    constructor
    · intro o₁ o₂ h
      match o₁, o₂ with
      | none, none => rfl
      | none, some c =>
        exfalso
        have h2 : ((ι c.1 : F)) = 0 := by
          have h3 := congrArg Subtype.val h
          simpa [g] using h3.symm
        exact Units.ne_zero (ι c.1) h2
      | some a, none =>
        exfalso
        have h2 : ((ι a.1 : F)) = 0 := by
          have h3 := congrArg Subtype.val h
          simpa [g] using h3
        exact Units.ne_zero (ι a.1) h2
      | some a, some c =>
        have h2 : ((ι a.1 : F)) = (ι c.1 : F) := by
          have h3 := congrArg Subtype.val h
          simpa [g] using h3
        exact congrArg some (Subtype.ext (hι (Units.ext h2)))
    · rintro ⟨x, hx⟩
      have hx' : σ b x = x := hx
      by_cases hx0 : x = 0
      · -- the only fixed point outside the image of `ι` is `0`
        exact ⟨none, Subtype.ext hx0.symm⟩
      · -- a nonzero fixed point of `σ b` is `ι a` for a fixed point `a` of `φ b`
        obtain ⟨a, ha⟩ := hsurj (Units.mk0 x hx0)
        have haval : (ι a : F) = x := by rw [ha, Units.val_mk0]
        have hfix : φ b a = a := by
          apply hι
          apply Units.ext
          rw [← hσ b a, haval, hx']
        exact ⟨some ⟨a, hfix⟩, Subtype.ext haval⟩
  have key : Nat.card (Option ↥P) = Nat.card ↥(Function.fixedPoints (σ b)) :=
    Nat.card_congr (Equiv.ofBijective g hg)
  rw [Finite.card_option] at key
  exact key.symm

end Work.AppXIField.Main
