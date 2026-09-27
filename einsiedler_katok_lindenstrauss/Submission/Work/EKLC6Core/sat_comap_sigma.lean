import Mathlib
import Submission.Work.EKLC6Core.saturated_measurable

/-!
# `Work.EKLC6Core.sat_comap_sigma` — saturating a σ-algebra by a saturated set

Let `A` be a σ-algebra on `X`, `φ : X → X` a map whose pullback preserves `A`
(`comap φ A ≤ A`), and `Z` an `A`-saturated set: `[x]_A ⊆ Z` for every `x ∈ Z`.

Then the σ-algebra `A' = A ⊔ σ({φ⁻¹ⁿ Z})` has (a) `Z` among its measurable sets, (b)
`comap φ A' ≤ A'` whenever `comap φ A ≤ A`, and (c) **the same atoms as `A`**: `[x]_{A'} = [x]_A`
— so a plaque algebra for `A` is still a plaque algebra for `A'`.

This is the measurability fix for the frozen `IsPlaqueAlgebra`: the good set produced by the
thin-boundary/Borel–Cantelli argument is Borel and `A`-saturated but a priori only *coanalytic*,
so it need not be `A`-measurable; enlarging `A` by the orbit of `Z` makes `Z` measurable without
changing the atoms.

The proof of (c): let `T = [x]_A`.  The family `𝓑 = {S | T ⊆ S or S ∩ T = ∅}` is a σ-algebra; it
contains `A` (an `A`-measurable `S ∋ x` contains `T`) and contains each generator `φ⁻¹ⁿ Z`,
because saturation propagates along the orbit: `y ∈ T` implies `φⁿ y ∈ [φⁿ x]_A`, so that
`φⁿ y ∈ Z ⟺ φⁿ x ∈ Z` (both implications use saturation, at `φⁿ y` resp. `φⁿ x`).  Hence
`A' ≤ 𝓑`, and every `A'`-measurable set containing `x` contains all of `T`.
-/

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.EKLC6Core

/-- **The atoms of `A ⊔ σ(orbit of Z)` are the atoms of `A`**, for `Z` an `A`-saturated set. -/
theorem atomOf_sup_comap_eq {X : Type*} [MeasurableSpace X] {A : MeasurableSpace X} {φ : X → X}
    (hdec : MeasurableSpace.comap φ A ≤ A) {Z : Set X} (hsat : ∀ x ∈ Z, atomOf A x ⊆ Z) (x : X) :
    atomOf (A ⊔ MeasurableSpace.generateFrom (Set.range (fun n : ℕ => (φ^[n]) ⁻¹' Z))) x
      = atomOf A x := by
  -- the atom relation is preserved by `φ`
  have hpres : ∀ u : X, ∀ y ∈ atomOf A u, φ y ∈ atomOf A (φ u) := by
    intro u y hy
    rw [atomOf, Set.mem_sInter] at hy ⊢
    intro S hS
    obtain ⟨hSmeas, huS⟩ := hS
    exact hy (φ ⁻¹' S) ⟨MeasurableSpace.le_def.mp hdec _ (by
        exact MeasurableSpace.measurableSet_comap.mpr ⟨S, hSmeas, rfl⟩),
      Set.mem_preimage.mpr huS⟩
  have hpresN : ∀ n : ℕ, ∀ u : X, ∀ y ∈ atomOf A u,
      (φ^[n]) y ∈ atomOf A ((φ^[n]) u) := by
    intro n
    induction n with
    | zero => intro u y hy; exact hy
    | succ k ih =>
      intro u y hy
      have h1 : φ y ∈ atomOf A (φ u) := hpres u y hy
      have h2 : (φ^[k]) (φ y) ∈ atomOf A ((φ^[k]) (φ u)) := ih (φ u) (φ y) h1
      simpa using h2
  -- the σ-algebra of sets which contain the atom of `x` or are disjoint from it
  let B : MeasurableSpace X :=
    { MeasurableSet' := fun S => atomOf A x ⊆ S ∨ S ∩ atomOf A x = ∅
      measurableSet_empty := Or.inr (by simp)
      measurableSet_compl := by
        intro S hS
        rcases hS with hS | hS
        · refine Or.inr ?_
          rw [← Set.not_nonempty_iff_eq_empty]
          rintro ⟨a, haSc, haT⟩
          exact haSc (hS haT)
        · refine Or.inl ?_
          intro a haT
          rw [Set.mem_compl_iff]
          intro haS
          have hmem : a ∈ S ∩ atomOf A x := ⟨haS, haT⟩
          rw [hS] at hmem
          exact hmem
      measurableSet_iUnion := by
        intro f hf
        by_cases hex : ∃ i, atomOf A x ⊆ f i
        · obtain ⟨i, hi⟩ := hex
          exact Or.inl (Set.Subset.trans hi (Set.subset_iUnion f i))
        · push Not at hex
          refine Or.inr ?_
          rw [← Set.not_nonempty_iff_eq_empty]
          rintro ⟨a, haU, haT⟩
          obtain ⟨i, hai⟩ := Set.mem_iUnion.mp haU
          have hdisj : f i ∩ atomOf A x = ∅ := (hf i).resolve_left (hex i)
          have hmem : a ∈ f i ∩ atomOf A x := ⟨hai, haT⟩
          rw [hdisj] at hmem
          exact hmem }
  -- `B` contains `A`
  have hAB : A ≤ B := by
    intro S hS
    by_cases hxS : x ∈ S
    · exact Or.inl (atomOf_subset_of_mem hS hxS)
    · refine Or.inr ?_
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨a, haS, haT⟩
      exact hxS (atomOf_subset_of_mem hS haS (mem_atomOf_comm.mp haT))
  -- `B` contains the generators
  have hGB : MeasurableSpace.generateFrom (Set.range (fun n : ℕ => (φ^[n]) ⁻¹' Z)) ≤ B := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨n, rfl⟩
    by_cases hxS : (φ^[n]) x ∈ Z
    · refine Or.inl ?_
      intro y hy
      exact hsat _ hxS (hpresN n x y hy)
    · refine Or.inr ?_
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨a, haS, haT⟩
      exact hxS (hsat _ haS (mem_atomOf_comm.mp (hpresN n x a haT)))
  -- the self-membership `x ∈ [x]_A`
  have hself : x ∈ atomOf A x := by
    rw [atomOf, Set.mem_sInter]
    exact fun S hS => hS.2
  have hmono : atomOf (A ⊔ MeasurableSpace.generateFrom
        (Set.range (fun n : ℕ => (φ^[n]) ⁻¹' Z))) x ⊆ atomOf A x := by
    intro y hy
    rw [atomOf, Set.mem_sInter] at hy ⊢
    intro S hS
    exact hy S ⟨MeasurableSpace.le_def.mp le_sup_left S hS.1, hS.2⟩
  refine le_antisymm hmono ?_
  intro y hy
  rw [atomOf, Set.mem_sInter]
  intro S hS
  have hSB : MeasurableSet[B] S :=
    MeasurableSpace.le_def.mp (sup_le hAB hGB) S hS.1
  have hSB' : atomOf A x ⊆ S ∨ S ∩ atomOf A x = ∅ := hSB
  rcases hSB' with hsub | hdisj
  · exact hsub hy
  · have hmem : x ∈ S ∩ atomOf A x := ⟨hS.2, hself⟩
    rw [hdisj] at hmem
    exact absurd hmem (by simp)

end Work.EKLC6Core
