import Mathlib
import Submission.Work.CurveBasics.Order.PthPowers

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

namespace Work.CurveBasics.Order

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- The intermediate field of elements of `F` whose `p`-th power lies in `L`; equivalently the
preimage of `L` under the Frobenius map `x ↦ x ^ p`.  It is the "inverse Frobenius" of `L`
and, restricted to a purely inseparable extension, records exactly the elements killed by the
`p`-power map modulo `L`. -/
noncomputable def pthRoots (p : ℕ) [ExpChar F p] (L : IntermediateField k F) :
    IntermediateField k F :=
  Subfield.toIntermediateField (L.toSubfield.comap (frobenius F p))
    (fun c => by
      show (frobenius F p) (algebraMap k F c) ∈ L.toSubfield
      rw [frobenius_def]
      exact pow_mem (L.algebraMap_mem c) p)

/-- Characterisation of the elements of `pthRoots p L`. -/
theorem mem_pthRoots {p : ℕ} [ExpChar F p] {L : IntermediateField k F} {x : F} :
    x ∈ pthRoots p L ↔ x ^ p ∈ L := by
  change x ∈ Subfield.comap (frobenius F p) L.toSubfield ↔ x ^ p ∈ L
  rw [Subfield.mem_comap, frobenius_def, IntermediateField.mem_toSubfield]

theorem pthPowers_sup_adjoin_le {k F : Type u} [Field k] [PerfectField k] [Field F] [Algebra k F]
    {p : ℕ} [ExpChar k p] [ExpChar F p] {L : IntermediateField k F} {b : F}
    (hbp : b ^ p ∈ L) :
    Work.CurveBasics.Order.pthPowers p (L ⊔ IntermediateField.adjoin k ({b} : Set F)) ≤ L := by
  -- It suffices to show that the generators `L` and `b` of the compositum lie in `pthRoots p L`.
  have hle : L ⊔ IntermediateField.adjoin k ({b} : Set F) ≤ pthRoots p L := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [mem_pthRoots]
      exact pow_mem hx p
    · rw [IntermediateField.adjoin_le_iff]
      exact Set.singleton_subset_iff.mpr (mem_pthRoots.mpr hbp)
  intro x hx
  obtain ⟨y, hy, hyx⟩ := mem_pthPowers.mp hx
  rw [← hyx]
  exact mem_pthRoots.mp (hle hy)

end Work.CurveBasics.Order
