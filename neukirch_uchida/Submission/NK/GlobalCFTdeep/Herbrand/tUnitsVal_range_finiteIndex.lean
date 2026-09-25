/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank

/-!
# The valuation map on `T`-units is onto `N • (everything)`

Let `L` be a number field, `T` a finite set of places of `L`, and `SSet T` the finite places of `L`
lying in `T`.  The `T`-units `TUnits T ⊆ Lˣ` are the units which are local units away from `T`, and

  `tUnitsVal T : Additive (TUnits T) →ₗ[ℤ] (SSet T → ℤ)`

(`NK.GlobalCFTdeep.tUnitsVal`, from `Herbrand/TUnitsRank.lean`) records the `q`-adic valuations of
a `T`-unit at the finite places `q ∈ SSet T`.

The main theorem of this file says that the image of `tUnitsVal T` contains `N • c` for **every**
`c : SSet T → ℤ`, as soon as the `T`-units contain a family `a q` (`q ∈ SSet T`) with

* `expUnit q (a q) = N`, and
* `expUnit q' (a q) = 0` for `q' ≠ q`,

i.e. a family whose valuation vectors are the `N`-multiples of the coordinate functions.  In other
words, once such a "unimodular up to `N`" family of `T`-units exists, the cokernel of `tUnitsVal T`
is annihilated by `N` — the range of `tUnitsVal T` has finite index at most `N`, in the strongest
possible sense that it contains the whole submodule `N • (SSet T → ℤ)`.

This is the linear-algebra half of the `S`-unit / Dirichlet-unit computation: the arithmetic input
is exactly the existence of the family `a`, and the present file converts it into the surjectivity
statement about `N`-multiples used downstream (Milne, *Class Field Theory*, Theorem 4.3, via
`NK.GlobalCFTdeep.Herbrand`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped BigOperators

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT NK.GlobalCFTdeep

/-- The finite places lying in a finite set of places form a finite type. -/
theorem finite_SSet {L : Type} [Field L] [NumberField L] (T : Set (Place L)) [Finite T] :
    Finite (SSet T) :=
  Finite.of_injective (fun q : SSet T => (⟨Place.ofFinite q.1, q.2⟩ : T)) (by
    intro p q h
    exact Subtype.ext (Place.ofFinite_inj.mp (congrArg Subtype.val h)))

/-- A function on a finite type is the sum of its values against the coordinate functions. -/
theorem sum_smul_pi_single_eq {α : Type} [Fintype α] [DecidableEq α] (c : α → ℤ) :
    (∑ q, c q • Pi.single q (1 : ℤ)) = c := by
  ext q'
  rw [Finset.sum_apply, Finset.sum_eq_single q']
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro h; exact absurd (Finset.mem_univ q') h

/-- **The valuation map on the `T`-units is onto `N • (everything)`.**

If the `T`-units contain, for every finite place `q ∈ SSet T`, an element `a q` satisfying
`expUnit q (a q) = N` and `expUnit q' (a q) = 0` for `q' ≠ q`, then every function
`c : SSet T → ℤ` is an `N`-multiple of a valuation vector of a `T`-unit. -/
theorem tUnitsVal_range_finiteIndex {L : Type} [Field L] [NumberField L]
    (T : Set (NK.GlobalCFT.Place L)) [Finite T] {N : ℕ} (hN : 0 < N)
    (a : NK.GlobalCFTdeep.SSet T → NK.GlobalCFTdeep.TUnits T)
    (haN : ∀ q : NK.GlobalCFTdeep.SSet T,
      NK.GlobalCFTdeep.expUnit q.1 ((a q : NK.GlobalCFTdeep.TUnits T) : Lˣ) = (N : ℤ))
    (ha0 : ∀ q q' : NK.GlobalCFTdeep.SSet T, q' ≠ q →
      NK.GlobalCFTdeep.expUnit q'.1 ((a q : NK.GlobalCFTdeep.TUnits T) : Lˣ) = 0) :
    ∀ c : NK.GlobalCFTdeep.SSet T → ℤ, ∃ x : Additive (NK.GlobalCFTdeep.TUnits T),
      (N : ℤ) • c = NK.GlobalCFTdeep.tUnitsVal T x := by
  haveI : Finite (SSet T) := finite_SSet T
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  haveI : DecidableEq (SSet T) := Classical.decEq _
  -- The valuation vector of `a q` is `N` times the coordinate function at `q`.
  have hsingle : ∀ q : SSet T,
      tUnitsVal T (Additive.ofMul (a q)) = (N : ℤ) • Pi.single q (1 : ℤ) := by
    intro q
    ext q'
    rw [tUnitsVal_apply, Pi.smul_apply, Pi.single_apply]
    by_cases h : q' = q
    · subst h
      simp [haN]
    · simp [h, ha0 q q' h]
  intro c
  -- The `T`-unit `x = ∑ q, c q • a q` has valuation vector `N • c`.
  refine ⟨∑ q : SSet T, c q • Additive.ofMul (a q), ?_⟩
  rw [map_sum]
  rw [show (∑ q : SSet T, tUnitsVal T (c q • Additive.ofMul (a q)))
      = ∑ q : SSet T, (N : ℤ) • (c q • Pi.single q (1 : ℤ)) from
    Finset.sum_congr rfl fun q _ => by rw [map_smul, hsingle q, smul_comm]]
  rw [← Finset.smul_sum, sum_smul_pi_single_eq c]

end NK.GlobalCFTdeep.Herbrand
