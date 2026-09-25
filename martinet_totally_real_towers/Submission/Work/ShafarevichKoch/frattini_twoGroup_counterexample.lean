import Mathlib

/-!
# A normal `2`-subgroup `R` with `R ≤ ⁅R, G⁆ · R²`

This is the counterexample advertised in `Work.ShafarevichKoch.frattini_not_determine_normalClosure`
(see the chapter `README.md`, §9.2) and needed by the Shafarevich--Koch development: the
"Frattini/Nakayama" first-order description of a normal closure,

```
H · ⁅R, G⁆ · R²  =  R   ⟹   H = R,
```

is **false** when phrased for an abstract group `G` rather than for a pro-`2` group `G`, *even when
the quotient `R/H` is itself a `2`-group*.  The failure is not caused by odd torsion in `R/H`; it is
caused by the ambient group: the action of `G` on `R/H` need not be pro-`2`.

The witness here is the classical one: inside the alternating group `A₄` (which we realise inside
`S₄ = Equiv.Perm (Fin 4)` as the Klein four subgroup)

* `R = V₄ = {1, (01)(23), (02)(13), (03)(12)}` is a normal subgroup of `S₄`, hence of `A₄`; it is a
  `2`-group (`x² = 1` for every `x ∈ V₄`) and nontrivial;
* `R² = ⊥`, so the assertion `R ≤ ⁅R, ⊤⁆ ⊔ closure (R²)` says exactly `V₄ ≤ ⁅V₄, S₄⁆`;
* and indeed `⁅V₄, S₄⁆ = V₄`: conjugating a double transposition by a `3`-cycle permutes the three
  double transpositions cyclically, so `⁅x, (012)⁆` runs through all three nontrivial elements of
  `V₄` as `x` does.  Concretely (with `a = (01)(23)`, `b = (02)(13)`, `c = a·b = (03)(12)`,
  `g = (012)`):

  `⁅a, g⁆ = b`, `⁅b, g⁆ = c`, `⁅c, g⁆ = a`.

So `V₄ ≤ ⁅V₄, ⊤⁆ · V₄²` while `V₄ ≠ ⊥`: the first-order data does not determine the subgroup.
(Compare `A₄ ⊵ V₄` with `R/H = V₄`, a `2`-group, versus the abelian witness `6ℤ ≤ 2ℤ` of
`frattini_not_determine_normalClosure`, where `R/H ≅ ℤ/3` is odd.  What *is* true — and what the
pro-`2` interface `ClosedRelationData` of the chapter encodes — is the corresponding statement for
a pro-`2` ambient group, where Nakayama applies to the `2`-complete situation.)

Everything is finite and decided by computation in `S₄`.
-/

open scoped commutatorElement

namespace Work.ShafarevichKoch

namespace KleinFourCounterexample

open Equiv

/-- The double transposition `(0 1)(2 3)`. -/
def pA : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The double transposition `(0 2)(1 3)`. -/
def pB : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The third double transposition `(0 3)(1 2) = pA * pB`. -/
def pC : Equiv.Perm (Fin 4) := pA * pB

/-- The `3`-cycle `(0 1 2)` (as a permutation, `0 ↦ 1 ↦ 2 ↦ 0`). -/
def pG : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- **The Klein four subgroup `V₄ ≤ S₄`**, given by its four elements
`{1, (01)(23), (02)(13), (03)(12)}`. -/
def V4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {1, pA, pB, pC}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

/-- `V₄` is normal in `S₄`: conjugation permutes the three double transpositions. -/
theorem V4_normal : V4.Normal := by
  constructor
  intro n hn g
  have h : ∀ y ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4))), ∀ g : Equiv.Perm (Fin 4),
      g * y * g⁻¹ ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4))) := by decide
  exact h n hn g

/-- `V₄` is nontrivial: `(01)(23) ≠ 1`. -/
theorem V4_ne_bot : V4 ≠ ⊥ := by
  intro h
  have ha : pA ∈ V4 := by
    show pA ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4)))
    decide
  have : pA ∈ (⊥ : Subgroup (Equiv.Perm (Fin 4))) := h ▸ ha
  exact (by decide : pA ≠ 1) (Subgroup.mem_bot.mp this)

/-- `V₄` is a `2`-group: every element is an involution. -/
theorem V4_isPGroup : IsPGroup 2 ↥V4 := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, ?_⟩
  have h : ∀ y ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4))), y ^ 2 = 1 := by decide
  exact Subtype.ext (h x x.2)

/-- **`V₄ ≤ ⁅V₄, S₄⁆ ⊔ V₄²`.**  Since `V₄² = ⊥` it suffices to exhibit the three double
transpositions as commutators with the `3`-cycle `(0 1 2)`:
`⁅pA, pG⁆ = pB`, `⁅pB, pG⁆ = pC`, `⁅pC, pG⁆ = pA`. -/
theorem V4_le_commutator_sup_sq :
    V4 ≤ ⁅V4, (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ ⊔
      Subgroup.closure ((fun x : Equiv.Perm (Fin 4) => x ^ 2) '' (V4 : Set _)) := by
  have hA : pA ∈ V4 := by
    show pA ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4)))
    decide
  have hB : pB ∈ V4 := by
    show pB ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4)))
    decide
  have hC : pC ∈ V4 := by
    show pC ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4)))
    decide
  have hA' : pA ∈ ⁅V4, (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ := by
    have h : ⁅pC, pG⁆ = pA := by decide
    rw [← h]
    exact Subgroup.commutator_mem_commutator hC (Subgroup.mem_top pG)
  have hB' : pB ∈ ⁅V4, (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ := by
    have h : ⁅pA, pG⁆ = pB := by decide
    rw [← h]
    exact Subgroup.commutator_mem_commutator hA (Subgroup.mem_top pG)
  have hC' : pC ∈ ⁅V4, (⊤ : Subgroup (Equiv.Perm (Fin 4)))⁆ := by
    have h : ⁅pB, pG⁆ = pC := by decide
    rw [← h]
    exact Subgroup.commutator_mem_commutator hB (Subgroup.mem_top pG)
  intro n hn
  have hn' : n ∈ ({1, pA, pB, pC} : Set (Equiv.Perm (Fin 4))) := hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn'
  rcases hn' with h | h | h | h
  · subst h; exact Subgroup.mem_sup_left (Subgroup.one_mem _)
  · subst h; exact Subgroup.mem_sup_left hA'
  · subst h; exact Subgroup.mem_sup_left hB'
  · subst h; exact Subgroup.mem_sup_left hC'

end KleinFourCounterexample

/-- **A normal `2`-subgroup `R ≤ ⁅R, ⊤⁆ ⊔ closure (R²)` which is nontrivial.**  The witness is
`R = V₄` inside `G = S₄`: `V₄` is normal, nontrivial, of exponent `2`, and `⁅V₄, S₄⁆ = V₄` (the
three double transpositions are conjugates of one another by a `3`-cycle), so `R ≤ ⁅R, ⊤⁆ · R²`
even though `R ≠ 1`.  This is the `A₄ ⊵ V₄` counterexample of the Shafarevich--Koch chapter: the
"Frattini/Nakayama" characterisation of a normal closure fails in an abstract ambient group even
when `R` is a `2`-group. -/
theorem frattini_twoGroup_counterexample :
    ∃ (G : Type) (_ : Group G) (R : Subgroup G), R.Normal ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧
      R ≤ ⁅R, ⊤⁆ ⊔ Subgroup.closure ((fun x : G => x ^ 2) '' (R : Set G)) := by
  refine ⟨Equiv.Perm (Fin 4), inferInstance, KleinFourCounterexample.V4,
    KleinFourCounterexample.V4_normal, KleinFourCounterexample.V4_ne_bot,
    KleinFourCounterexample.V4_isPGroup, ?_⟩
  exact KleinFourCounterexample.V4_le_commutator_sup_sq

end Work.ShafarevichKoch
