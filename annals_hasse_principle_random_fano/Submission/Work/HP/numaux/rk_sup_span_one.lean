import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs

/-!
# Adding a vector outside the saturation raises the rank by one

Let `Λ ⊆ ℤ^ι` be an integral lattice (with `ι` finite) and let `u` be an integer vector whose
class is not in the saturation `satLat Λ`.  Then adjoining `u` to `Λ` increases the rank by one:

`rk (Λ ⊔ span ℤ {u}) = rk Λ + 1`.

The point is that the sum is direct: if `x ∈ Λ ∩ span ℤ {u}` then `x = c • u` for some `c`,
and `x ∈ Λ` with `c ≠ 0` would force `u ∈ satLat Λ` by definition of the saturation.  Hence
the intersection is trivial and ranks add.  The primitivity of `Λ` is not needed for this; it is
kept in the statement because that is how the lemma is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Finset

namespace Work.HP.numaux

/-- Adjoining to an integral lattice a vector outside its saturation raises the rank by one. -/
theorem rk_sup_span_one {ι : Type} [Fintype ι] [DecidableEq ι] {Λ : Submodule ℤ (ι → ℤ)}
    (hΛ : IsPrimLat Λ) {u : ι → ℤ} (hu : u ∉ satLat Λ) :
    rk (Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ))) = rk Λ + 1 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (Submodule.zero_mem _)
  -- The two summands meet trivially.
  have hinf : Λ ⊓ Submodule.span ℤ ({u} : Set (ι → ℤ)) = ⊥ := by
    rw [← disjoint_iff]
    refine Submodule.disjoint_span_singleton''.mpr fun r hr => ?_
    by_cases hr0 : r = 0
    · simp [hr0]
    · exact absurd ⟨r, hr0, hr⟩ hu
  -- The span of a nonzero vector has rank one.
  have hS : Module.finrank ℤ (Submodule.span ℤ ({u} : Set (ι → ℤ))) = 1 := by
    have hle : (ℤ ∙ u) = Submodule.span ℤ ({u} : Set (ι → ℤ)) := rfl
    rw [← hle]
    simpa using (LinearEquiv.toSpanNonzeroSingleton ℤ (ι → ℤ) u hu0).finrank_eq.symm
  -- Ranks add over a direct sum (cardinal-level rank formula).
  have hrank :=
    Submodule.rank_sup_add_rank_inf_eq (R := ℤ) Λ (Submodule.span ℤ ({u} : Set (ι → ℤ)))
  rw [hinf, rank_bot, add_zero] at hrank
  have hfin : Module.finrank ℤ ↥(Λ ⊔ Submodule.span ℤ ({u} : Set (ι → ℤ)))
      = Module.finrank ℤ Λ + Module.finrank ℤ (Submodule.span ℤ ({u} : Set (ι → ℤ))) := by
    rw [← Nat.cast_inj (R := Cardinal)]
    rw [Nat.cast_add, Submodule.finrank_eq_rank, Submodule.finrank_eq_rank,
        Submodule.finrank_eq_rank, hrank]
  simp only [Work.HP.rk]
  rw [hfin, hS]

end Work.HP.numaux
