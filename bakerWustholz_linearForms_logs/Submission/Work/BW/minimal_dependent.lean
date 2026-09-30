import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Extraction of a *minimal* linearly dependent subfamily: if a finite family
`ℓ : Fin n → ℂ` is linearly dependent over `ℚ`, then it contains a subfamily,
indexed by `Fin m` with `m ≥ 1` through an injective `e`, which is dependent while
every subfamily obtained by deleting a single element is independent.

This is the standard "minimal counterexample / minimal support" step used to
reduce a linear dependence of logarithms to one in which every proper subfamily
is independent. -/
theorem minimal_dependent {n : ℕ} (ℓ : Fin n → ℂ)
    (hdep : ¬ LinearIndependent ℚ ℓ) :
    ∃ (m : ℕ) (hm : 1 ≤ m) (e : Fin m → Fin n), Function.Injective e ∧
      (¬ LinearIndependent ℚ (fun j => ℓ (e j))) ∧
      (∀ j : Fin m, LinearIndependent ℚ (fun i : {i : Fin m // i ≠ j} => ℓ (e i))) := by
  classical
  -- A linear dependence gives a finite subset `s₀` which is already dependent.
  obtain ⟨s₀, g, hsum, i₀, hi₀, hgi₀⟩ := not_linearIndependent_iff.mp hdep
  -- Among the nonempty dependent finite subsets choose one of least cardinality.
  have hex : ∃ k : ℕ, ∃ s : Finset (Fin n), s.card = k ∧ s.Nonempty ∧
      ¬ LinearIndepOn ℚ ℓ (s : Set (Fin n)) :=
    ⟨s₀.card, s₀, rfl, ⟨i₀, hi₀⟩,
      (not_linearIndepOn_finset_iff).mpr ⟨g, hsum, i₀, hi₀, hgi₀⟩⟩
  obtain ⟨s, hscard, hsne, hsdep⟩ := Nat.find_spec hex
  -- The empty set is independent, so a strictly smaller dependent set would be nonempty.
  have hempty : LinearIndepOn ℚ ℓ ((∅ : Finset (Fin n)) : Set (Fin n)) := by
    by_contra hcon
    obtain ⟨f, -, i, hi, -⟩ := (not_linearIndepOn_finset_iff).mp hcon
    exact absurd hi (Finset.notMem_empty i)
  -- Minimality: every finite subset of smaller cardinality is independent.
  have hsmin : ∀ t : Finset (Fin n), t.card < s.card →
      LinearIndepOn ℚ ℓ (t : Set (Fin n)) := by
    intro t ht
    rcases Finset.eq_empty_or_nonempty t with ht0 | htne
    · rw [ht0]; exact hempty
    · by_contra hcon
      exact Nat.find_min hex (by rw [← hscard]; exact ht) ⟨t, rfl, htne, hcon⟩
  have hm : 1 ≤ s.card := Finset.card_pos.mpr hsne
  -- Enumerate `s` by `Fin s.card`.
  let E : s ≃ Fin s.card := Finset.equivFinOfCardEq rfl
  let e : Fin s.card → Fin n := fun j => ((E.symm j : s) : Fin n)
  have hinj : Function.Injective e := by
    intro x y hxy
    have h1 : E.symm x = E.symm y := Subtype.ext hxy
    exact E.symm.injective h1
  have hrange : Set.range e = (s : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact (E.symm j).2
    · intro hy
      exact ⟨E ⟨y, hy⟩, by simp [e]⟩
  refine ⟨s.card, hm, e, hinj, ?_, ?_⟩
  -- The whole family is dependent.
  · intro hcon
    exact hsdep (by rw [← hrange]; exact (linearIndepOn_range_iff hinj ℓ).mpr hcon)
  -- Deleting any element leaves an independent family.
  · intro j
    have hlt : (s.erase (e j)).card < s.card := Finset.card_erase_lt_of_mem (E.symm j).2
    have hli := hsmin (s.erase (e j)) hlt
    have hinj' : Function.Injective (fun i : {i : Fin s.card // i ≠ j} => e i) := by
      intro x y hxy
      exact Subtype.ext (hinj hxy)
    have hrange' : Set.range (fun i : {i : Fin s.card // i ≠ j} => e i) =
        (s.erase (e j) : Set (Fin n)) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨fun h => i.2 (hinj h), (E.symm i.1).2⟩
      · intro hy
        rw [Finset.mem_coe, Finset.mem_erase] at hy
        obtain ⟨hne, hmem⟩ := hy
        refine ⟨⟨E ⟨y, hmem⟩, ?_⟩, ?_⟩
        · intro hj; exact hne (by rw [← hj]; simp [e])
        · simp [e]
    exact (linearIndepOn_range_iff hinj' ℓ).mp (by rw [hrange']; exact hli)

end Work.BW
