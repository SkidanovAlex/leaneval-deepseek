import Mathlib

open MeasureTheory

/-!
# Atoms and the measurability of saturated sets (the *selector* trick)

Let `A` be a σ-algebra on a space `X`, coarser than the Borel σ-algebra, together with a
**selector** `s : X → X`: a Borel function that is `A`-measurable, idempotent, and sends every
point into its own `A`-atom:

  `Measurable s`,  `Measurable[A] s`,  `s (s x) = s x`,  `s x ∈ [x]_A`.

Then every Borel `A`-saturated set is `A`-measurable (`measurableSet_of_atomSaturated_of_selector`).

This is the tool that turns the "a.e." plaque statements of Pisa 7.31/7.37 into the frozen
`IsPlaqueAlgebra` requirements `MeasurableSet[m] Z` and `[x]_m ⊆ Z` for `x ∈ Z`: the set of
*good* points is Borel and saturated, but a priori only coanalytic, so it need not be measurable
in `A`; the selector identifies it with the preimage of a Borel set under `s`.

Proof: `G = s ⁻¹' (G ∩ {x | s x = x})` (saturation plus `s x ∈ [x]_A`), and the set of fixed
points of `s` is Borel — either by hypothesis, or from the fact that it is the preimage of the
(closed, hence Borel) diagonal under the measurable map `x ↦ (x, s x)`
(`measurableSet_fixed_of_measurable`, stated separately because a local `MeasurableSpace` binder
makes the instance search for the product σ-algebra ambiguous).  Hence
`G ∈ comap s ‹_› ≤ A`.
-/

namespace Work.EKLC6Core

/-- The atom `[x]_m` of a σ-algebra `m` at a point `x`: the intersection of all `m`-measurable
sets containing `x`. -/
def atomOf {X : Type*} (m : MeasurableSpace X) (x : X) : Set X := ⋂₀ {s | MeasurableSet[m] s ∧ x ∈ s}

theorem atomOf_subset_of_mem {X : Type*} [MeasurableSpace X] {m : MeasurableSpace X} {B : Set X}
    (hB : MeasurableSet[m] B) {y : X} (hy : y ∈ B) : atomOf m y ⊆ B :=
  Set.sInter_subset_of_mem ⟨hB, hy⟩

theorem atomOf_subset_atomOf_of_mem {X : Type*} [MeasurableSpace X] {m : MeasurableSpace X}
    {x y : X} (hy : y ∈ atomOf m x) : atomOf m y ⊆ atomOf m x :=
  Set.sInter_mono (fun s hs => ⟨hs.1, atomOf_subset_of_mem hs.1 hs.2 hy⟩)

theorem mem_atomOf_comm {X : Type*} [MeasurableSpace X] {m : MeasurableSpace X} {x y : X} :
    y ∈ atomOf m x ↔ x ∈ atomOf m y := by
  have key : ∀ {a b : X}, b ∈ atomOf m a → a ∈ atomOf m b := by
    intro a b hab
    by_contra hba
    have h : ∃ S : Set X, MeasurableSet[m] S ∧ b ∈ S ∧ a ∉ S := by
      by_contra hc
      push Not at hc
      exact hba (by rw [atomOf]; exact Set.mem_sInter.mpr (fun t ht => hc t ht.1 ht.2))
    obtain ⟨S, hSmeas, hbS, haS⟩ := h
    have hbSc : b ∈ Sᶜ := (atomOf_subset_of_mem hSmeas.compl haS) hab
    exact hbSc hbS
  exact ⟨key, key⟩

theorem atomOf_eq_of_mem {X : Type*} [MeasurableSpace X] {m : MeasurableSpace X} {x y : X}
    (hy : y ∈ atomOf m x) : atomOf m y = atomOf m x :=
  le_antisymm (atomOf_subset_atomOf_of_mem hy)
    (atomOf_subset_atomOf_of_mem (mem_atomOf_comm.mp hy))

/-- **The set of fixed points of a measurable idempotent is Borel.**  (Stated in a context with
no other `MeasurableSpace X` hypothesis, so that the instance search for the product σ-algebra is
unambiguous.) -/
theorem measurableSet_fixed_of_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [T2Space X] [BorelSpace X] [SecondCountableTopology X] (s : X → X) (hs : Measurable s) :
    MeasurableSet {x : X | s x = x} := by
  have hd : MeasurableSet {p : X × X | p.1 = p.2} := isClosed_diagonal.measurableSet
  have hmap : Measurable (fun x : X => (x, s x)) := measurable_id.prodMk hs
  simpa [eq_comm] using hd.preimage hmap

/-- **The selector lemma.**  If a σ-algebra `A` admits an idempotent `A`-measurable selector `s`
into its atoms, then every `mX`-saturated set whose selector's fixed points form an `mX`-measurable
set is `A`-measurable.  The ambient σ-algebra `mX` is passed as a *named* instance so that the
instance search is not captured by the local `A`. -/
theorem measurableSet_of_atomSaturated_of_selector {X : Type*} [TopologicalSpace X]
    [mX : MeasurableSpace X] [T2Space X] [BorelSpace X] [SecondCountableTopology X]
    {A : MeasurableSpace X}
    (s : X → X) (hsA : Measurable[A, mX] s) (hidem : ∀ x, s (s x) = s x)
    (hmem : ∀ x, s x ∈ atomOf A x) (hfix : MeasurableSet[mX] {x : X | s x = x})
    {G : Set X} (hG : MeasurableSet[mX] G) (hsat : ∀ x ∈ G, atomOf A x ⊆ G) :
    MeasurableSet[A] G := by
  have hGeq : G = s ⁻¹' (G ∩ {x : X | s x = x}) := by
    ext x
    constructor
    · intro hx
      exact ⟨hsat x hx (hmem x), hidem x⟩
    · rintro ⟨hsxG, -⟩
      exact hsat (s x) hsxG (mem_atomOf_comm.mp (hmem x))
  rw [hGeq]
  exact hsA (hG.inter hfix)


end Work.EKLC6Core
