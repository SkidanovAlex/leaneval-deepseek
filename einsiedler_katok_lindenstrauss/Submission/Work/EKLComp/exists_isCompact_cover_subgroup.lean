import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.X3Background

/-!
# A closed subgroup of `SL₃(ℝ)` meets an open set in a countable union of compacta

For a closed subgroup `U ≤ SL₃(ℝ)` and an open set `O ⊆ SL₃(ℝ)`, the set `O ∩ U` is a countable
union of compact subsets of `SL₃(ℝ)`.

The argument is the standard one: `SL₃(ℝ)` is locally compact and second countable, hence so is
every closed subspace, hence the open subset `O ∩ U` of `U` is locally compact and second
countable, hence σ-compact.  Unwinding the two subtype coercions turns the resulting countable
cover of `↥(O ∩ U)` into compact subsets of `SL₃(ℝ)`.
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

theorem exists_isCompact_cover_subgroup (U : Subgroup Work.EKLContract.SL3)
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) (O : Set Work.EKLContract.SL3)
    (hO : IsOpen O) :
    ∃ C : ℕ → Set Work.EKLContract.SL3,
      (∀ n, IsCompact (C n)) ∧ ⋃ n, C n = O ∩ (U : Set Work.EKLContract.SL3) := by
  -- `SL₃(ℝ)` is locally compact and second countable
  haveI : LocallyCompactSpace Work.EKLContract.SL3 := locallyCompactSpace_SL3
  haveI : SecondCountableTopology Work.EKLContract.SL3 :=
    Work.EKLContract.Lemmas.SL3Topology.2
  -- `↥U` is a closed subspace of a locally compact second countable space
  haveI : LocallyCompactSpace ↥(U : Set Work.EKLContract.SL3) := hU.locallyCompactSpace
  haveI : SecondCountableTopology ↥(U : Set Work.EKLContract.SL3) := inferInstance
  -- the trace of `O` on `↥U` is open
  have hWopen : IsOpen (Subtype.val ⁻¹' O : Set ↥(U : Set Work.EKLContract.SL3)) :=
    hO.preimage continuous_subtype_val
  -- ... hence locally compact and second countable, hence σ-compact
  have hWsc : IsSigmaCompact (Subtype.val ⁻¹' O : Set ↥(U : Set Work.EKLContract.SL3)) := by
    haveI : LocallyCompactSpace ↥(Subtype.val ⁻¹' O : Set ↥(U : Set Work.EKLContract.SL3)) :=
      hWopen.locallyCompactSpace
    haveI : SecondCountableTopology
        ↥(Subtype.val ⁻¹' O : Set ↥(U : Set Work.EKLContract.SL3)) := inferInstance
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  -- coercion back to `SL₃(ℝ)` recovers exactly `O ∩ U`
  have himg : (Subtype.val '' (Subtype.val ⁻¹' O :
      Set ↥(U : Set Work.EKLContract.SL3)) : Set Work.EKLContract.SL3)
      = O ∩ (U : Set Work.EKLContract.SL3) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.2⟩
    · rintro ⟨hxO, hxU⟩
      exact ⟨⟨x, hxU⟩, hxO, rfl⟩
  obtain ⟨C, hC, hcov⟩ := hWsc.image continuous_subtype_val
  exact ⟨C, hC, by rw [hcov, himg]⟩

end Work.EKLComp
