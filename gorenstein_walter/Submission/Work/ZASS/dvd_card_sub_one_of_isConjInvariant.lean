/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Z4/Z5 counting: orbits of a fixed-point-free conjugation action

This file proves `Work.ZASS.dvd_card_sub_one_of_isConjInvariant`, the counting step of the
area `ZASS` of the Gorenstein–Walter project.  The mathematical content is completely general
and is isolated here as three lemmas about a group acting on a type:

* `card_orbit_eq_card_of_fixedPointFree`: in a fixed-point-free action (`g • a = a → g = 1`)
  the orbit of every point has exactly `|G|` elements, the orbit map `g ↦ g • a` being a
  bijection;
* `dvd_card_of_fixedPointFree`: consequently `|G| ∣ |α|` for a finite fixed-point-free action
  (the orbit decomposition `α ≃ Σ ω, orbit ω` exhibits `|α|` as a sum of `|G|`'s);
* `dvd_card_sub_one_of_fixedPointFree`: if in addition there is one (necessarily unique)
  point `b` fixed by all of `G` and no other element is fixed by a nonidentity element, then
  `|G| ∣ |α| - 1` — remove `b` and apply the previous lemma.

The target theorem is then the special case of the last statement for the conjugation action
of `H ≤ N_G(U)` on an `H`-invariant `W ≤ U`, where the unique fixed point is `1 ∈ W`: this is
the counting step shared by `|Z(U)| ≡ 1`, the first-layer count and the irreducibility of `U`
as an `H`-module.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-! ## Counting the orbits of a fixed-point-free action -/

section Counting

variable {G α : Type*}

/-- **Orbit size of a fixed-point-free action.** If no nonidentity element of `G` fixes a
point of `α`, then the orbit of `a` has exactly `|G|` elements: the orbit map
`g ↦ g • a : G → orbit G a` is a bijection, injectivity being exactly the freeness. -/
theorem card_orbit_eq_card_of_fixedPointFree [Group G] [MulAction G α]
    (hfree : ∀ (g : G) (a : α), g • a = a → g = 1) (a : α) :
    Nat.card (MulAction.orbit G a) = Nat.card G := by
  have hinj : Function.Injective
      (fun g : G => (⟨g • a, MulAction.mem_orbit a g⟩ : MulAction.orbit G a)) := by
    intro g g' h
    have h1 : g • a = g' • a := Subtype.ext_iff.mp h
    have h2 : (g⁻¹ * g') • a = a := by rw [mul_smul, ← h1, inv_smul_smul]
    exact inv_mul_eq_one.mp (hfree (g⁻¹ * g') a h2)
  have hsurj : Function.Surjective
      (fun g : G => (⟨g • a, MulAction.mem_orbit a g⟩ : MulAction.orbit G a)) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

/-- **Divisibility for a fixed-point-free action.** A finite fixed-point-free action has all
orbits of size `|G|`, and `α` is the disjoint union of its orbits, so `|G|` divides `|α|`. -/
theorem dvd_card_of_fixedPointFree [Group G] [MulAction G α] [Finite G] [Finite α]
    (hfree : ∀ (g : G) (a : α), g • a = a → g = 1) : Nat.card G ∣ Nat.card α := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (MulAction.orbitRel.Quotient G α) := Fintype.ofFinite _
  have hterm : ∀ ω : MulAction.orbitRel.Quotient G α,
      Nat.card (MulAction.orbit G (Quotient.out ω)) = Nat.card G :=
    fun ω => card_orbit_eq_card_of_fixedPointFree hfree (Quotient.out ω)
  have h1 : Nat.card α = ∑ ω : MulAction.orbitRel.Quotient G α, Nat.card G := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G α), Nat.card_sigma]
    exact Finset.sum_congr rfl fun ω _ => hterm ω
  rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

/-- **`|G| ∣ |α| - 1` for an action with a single fixed point.** Let `G` act on `α`, let `b`
be fixed by all of `G`, and suppose that a nonidentity element of `G` fixes only `b`.  Then
the action restricts to the complement of `{b}` (which is `G`-invariant precisely because `b`
is fixed), where it is fixed-point-free, so `|G| ∣ |α| - 1`. -/
theorem dvd_card_sub_one_of_fixedPointFree [Group G] [MulAction G α] [Finite G] [Finite α]
    (b : α) (hb : ∀ g : G, g • b = b)
    (hfree : ∀ (g : G), g ≠ 1 → ∀ a : α, g • a = a → a = b) :
    Nat.card G ∣ Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype {a : α // a ≠ b} := Fintype.ofFinite _
  haveI : Fintype {a : α // a = b} := Fintype.ofFinite _
  -- the punctured type carries the restricted action: `b` is fixed, so it is `G`-invariant
  letI : MulAction G {a : α // a ≠ b} :=
    { smul := fun g a => ⟨g • a.1, by
        intro hgb
        exact a.2 (by rw [← inv_smul_smul g a.1, hgb, hb])⟩
      one_smul := fun a => Subtype.ext (one_smul G a.1)
      mul_smul := fun g g' a => Subtype.ext (mul_smul g g' a.1) }
  have hcard : Nat.card {a : α // a ≠ b} = Nat.card α - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : α => x = b), Fintype.card_subtype_eq]
  have hfree' : ∀ (g : G) (a : {a : α // a ≠ b}), g • a = a → g = 1 := by
    intro g a ha
    have ha' : g • a.1 = a.1 := Subtype.ext_iff.mp ha
    by_contra hg
    exact a.2 (hfree g hg a.1 ha')
  have hdvd := dvd_card_of_fixedPointFree (G := G) (α := {a : α // a ≠ b}) hfree'
  rwa [hcard] at hdvd

end Counting

/-! ## The conjugation action of `H` on an invariant `W` -/

/-- **Z4/Z5 counting (blueprint §ZASS).** Let `H ≤ N(U)` act fixed-point-freely on `U` by
conjugation and let `W ≤ U` be a nontrivial `H`-invariant subgroup.  Then `|H| = (p^k-1)/2`
divides `|W| - 1`: the orbits of `H` on `W^#` all have `|H|` elements, by
`Work.ZASS.conjBy_injective`, so they partition `W^#`.  This is the counting step shared by
`|Z(U)| ≡ 1`, the first-layer count and the irreducibility of `U` as an `H`-module. -/
theorem dvd_card_sub_one_of_isConjInvariant {G : Type} [Group G] [Finite G] {p k : ℕ}
    {U H W : Subgroup G} (hWU : W ≤ U) (hHle : H ≤ Subgroup.normalizer (U : Set G))
    (hfix : Work.ZASS.FixedPointFreeConj U H) (hcardH : Nat.card H = (p ^ k - 1) / 2)
    (hWne : W ≠ ⊥) (hWinv : Work.ZASS.IsConjInvariant H W) :
    (p ^ k - 1) / 2 ∣ Nat.card W - 1 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  haveI : Fintype ↥W := Fintype.ofFinite _
  -- conjugation makes `W` an `H`-set (this is `IsConjInvariant H W`)
  letI : MulAction ↥H ↥W :=
    { smul := fun h w => ⟨conjBy (h : G) (w : G), hWinv h h.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show conjBy ((1 : ↥H) : G) (w : G) = (w : G)
        simp [conjBy])
      mul_smul := fun h h' w => Subtype.ext (by
        show conjBy ((h * h' : ↥H) : G) (w : G)
          = conjBy (h : G) (conjBy (h' : G) (w : G))
        simp only [conjBy, Subgroup.coe_mul]
        group) }
  -- `1 ∈ W` is the unique fixed point
  have hb : ∀ g : ↥H, g • (1 : ↥W) = 1 := by
    intro g
    exact Subtype.ext (by
      show conjBy (g : G) ((1 : ↥W) : G) = ((1 : ↥W) : G)
      simp [conjBy])
  have hfree : ∀ (g : ↥H), g ≠ 1 → ∀ a : ↥W, g • a = a → a = 1 := by
    intro g hg a ha
    have ha' : conjBy (g : G) (a : G) = (a : G) := Subtype.ext_iff.mp ha
    have hg' : (g : G) ≠ 1 := fun h => hg (Subtype.ext h)
    exact Subtype.ext (hfix (g : G) g.2 hg' (a : G) (hWU a.2) ha')
  have key := dvd_card_sub_one_of_fixedPointFree (G := ↥H) (α := ↥W) 1 hb hfree
  rw [← hcardH]
  exact key

end Work.ZASS
