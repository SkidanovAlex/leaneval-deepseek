import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

/-!
# A spanning finite family contains an independent subfamily of size `finrank`

If a finite family `v : ι → V` of vectors of a finite dimensional vector space
spans the whole space, then one can extract from it a linearly independent
subfamily indexed by `Fin (finrank F V)`.
-/

open Submodule

noncomputable section

namespace Commons.LinearAlgebra.Module

theorem exists_independent_subfamily_of_span_top {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {ι : Type*} [Fintype ι]
    (v : ι → V) (hspan : Submodule.span F (Set.range v) = ⊤) :
    ∃ t : Fin (Module.finrank F V) → ι,
      LinearIndependent F (fun j : Fin (Module.finrank F V) => v (t j)) := by
  classical
  -- A maximal linearly independent subset of `Set.range v` (obtained by extending ∅).
  let hs0 : LinearIndepOn F id (∅ : Set V) := by
    simp [LinearIndepOn]
  let hst : (∅ : Set V) ⊆ Set.range v := Set.empty_subset (Set.range v)
  let B : Set V := hs0.extend hst
  -- It still spans `V`, because extending ∅ inside `range v` does not change the span.
  have hBspan : span F B = ⊤ := by
    dsimp [B]
    rw [LinearIndepOn.span_extend_eq_span (K := F) (V := V) hs0 hst, hspan]
  have hBli : LinearIndepOn F id B := by
    dsimp [B]
    exact LinearIndepOn.linearIndepOn_extend (K := F) (ι := V) (v := id)
      (s := (∅ : Set V)) (t := Set.range v) hs0 hst
  have hBsub : B ⊆ Set.range v := by
    dsimp [B]
    exact LinearIndepOn.extend_subset (K := F) (ι := V) (v := id)
      (s := (∅ : Set V)) (t := Set.range v) hs0 hst
  -- `B` is finite, as a subset of the finite set `range v`.
  have hBfin : B.Finite := (Set.finite_range v).subset hBsub
  letI : Fintype ↥B := hBfin.fintype
  -- A linearly independent spanning set has cardinality equal to the finrank.
  have hcardB : Fintype.card ↥B = Module.finrank F V := by
    have h₁ := finrank_span_set_eq_card (R := F) (M := V) (s := B) hBli
    rw [hBspan] at h₁
    simpa using h₁.symm
  -- Parametrize `B` by `Fin (finrank F V)`.
  let e : Fin (Module.finrank F V) ≃ ↥B := (Fintype.equivFinOfCardEq hcardB).symm
  -- Each element of `B` lies in `range v`, so it has an index.
  have hmem : ∀ x : ↥B, (x : V) ∈ Set.range v := by
    intro x
    exact hBsub x.2
  let g : ↥B → ι := fun x => Classical.choose (hmem x)
  have hg : ∀ x : ↥B, v (g x) = (x : V) := fun x => Classical.choose_spec (hmem x)
  refine ⟨fun j => g (e j), ?_⟩
  -- The chosen subfamily is exactly the basis `B`, hence linearly independent.
  have h₁ : LinearIndependent F (fun x : ↥B => (x : V)) := by
    simpa [LinearIndepOn] using hBli
  have h₂ : LinearIndependent F (fun j : Fin (Module.finrank F V) => ((e j : ↥B) : V)) :=
    (linearIndependent_equiv (e := e) (f := fun x : ↥B => (x : V))).2 h₁
  simpa [hg] using h₂

end Commons.LinearAlgebra.Module