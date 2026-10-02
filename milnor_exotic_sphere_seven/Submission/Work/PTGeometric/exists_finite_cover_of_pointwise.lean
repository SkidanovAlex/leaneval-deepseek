import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A finite cover with prescribed data, from pointwise data on a compact set

Elementary topological bookkeeping: if a compact set `K` admits, at each of its points `x`, an open
neighbourhood `U x` (with `x ∈ U x`, with `closure (U x) ⊆ T` for a fixed open `T`, with a property
`Q` holding on `closure (U x)` and a property `P` holding on `U x` for a prescribed `ℓ x`), then
finitely many of these neighbourhoods still cover `K`, and one gets a `Fin m`-indexed family of the
same data.

This is the compactness step of the chart fields of
`Work.PTGeometric.nonempty_rawAmbientData_of_sourceRegion`.
-/

namespace Work.PTGeometric

/-- **Finitely many of a pointwise family of open neighbourhoods cover a compact set, keeping the
prescribed data.**  The data are a linear map `ℓ`, a property `Q` of `(ℓ, set)` that holds on the
*closure* of the chosen neighbourhood, and a property `P` of `(ℓ, set)` that is monotone in the set
and holds on the neighbourhood itself. -/
theorem exists_finite_cover_of_pointwise {X L : Type*} [TopologicalSpace X] {K T : Set X}
    (hK : IsCompact K) (P : L → Set X → Prop) (Q : L → Set X → Prop)
    (hpoint : ∀ x ∈ K, ∃ (ℓ : L) (U : Set X),
      IsOpen U ∧ x ∈ U ∧ closure U ⊆ T ∧ Q ℓ (closure U) ∧ P ℓ U)
    (hPmono : ∀ (ℓ : L) (U U' : Set X), P ℓ U → U' ⊆ U → P ℓ U') :
    ∃ (m : ℕ) (ℓ : Fin m → L) (U : Fin m → Set X),
      (∀ j, IsOpen (U j)) ∧ (∀ j, closure (U j) ⊆ T) ∧
      (∀ j, Q (ℓ j) (closure (U j))) ∧ (∀ j, P (ℓ j) (U j)) ∧
      (∀ x ∈ K, ∃ j, x ∈ U j) := by
  classical
  choose ℓfun Ufun hUopen hxU hclU hQ hP using fun x : K => hpoint x.1 x.2
  have hcover : K ⊆ ⋃ x : K, Ufun x := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ufun (fun x => hUopen x) hcover
  refine ⟨Fintype.card {x : K // x ∈ t},
    fun j => ℓfun ((Fintype.equivFin {x : K // x ∈ t}).symm j).1,
    fun j => Ufun ((Fintype.equivFin {x : K // x ∈ t}).symm j).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; exact hUopen _
  · intro j; exact hclU _
  · intro j; exact hQ _
  · intro j; exact hP _
  · intro x hx
    have hx' : x ∈ ⋃ i ∈ t, Ufun i := ht hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx'
    obtain ⟨i, hit, hxi⟩ := hx'
    refine ⟨Fintype.equivFin {x : K // x ∈ t} ⟨i, hit⟩, ?_⟩
    show x ∈ Ufun ((Fintype.equivFin {x : K // x ∈ t}).symm
      (Fintype.equivFin {x : K // x ∈ t} ⟨i, hit⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hxi

end Work.PTGeometric
