import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.archPairData_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed level `L_c` of `flags_2305`

`G1⁺`'s archimedean pairing is defined at *one* level `L_c` with `res_{L_c} c ≠ 1`, chosen
independently of the coefficient cocycle `b` (`_lead_design/flags_2305/flags_2305.md`).  This file
supplies it: for every involution `c ≠ 1` of `G_k` there is a finite Galois level `L ≥ K` at which
`c` still acts non-trivially.

Route: Krull separation of the point `c` from `1` gives a finite level `E` with
`c ∉ E.fixingSubgroup`; the fixed field of the open normal subgroup
`K.fixingSubgroup ⊓ E.fixingSubgroup` is then a finite Galois `L ≥ K` whose fixing subgroup is
contained in `E.fixingSubgroup`, so `c` is not fixed by `L` either.  (This is step (a) of
`PT.archPairData_exists`'s proof, extracted so that it does not depend on `b`.)
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 2000000

section LevelRes

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The fixed level `L_c`**: a finite Galois level `L ≥ K` with `res_L c ≠ 1`.  (The argument is
independent of the coefficient module.) -/
theorem exists_level_res_ne_one (c : Ω ≃ₐ[k] Ω) (hc1 : c ≠ 1) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      K ≤ L ∧ SSGRoute.res k L c ≠ 1 := by
  classical
  -- Krull separation: a finite level `E` at which `c` is not the identity
  obtain ⟨E, hEfin, hcE⟩ :
      ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ c ∉ E.fixingSubgroup := by
    have h1c : (1 : Ω ≃ₐ[k] Ω) ≠ c := fun h => hc1 h.symm
    have hnhds : ({c}ᶜ : Set (Ω ≃ₐ[k] Ω)) ∈ nhds (1 : Ω ≃ₐ[k] Ω) :=
      isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff] using h1c)
    obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff k Ω ({c}ᶜ)).mp hnhds
    exact ⟨E, hEfin, fun hc => hEsub hc (by simp)⟩
  -- the open normal subgroup whose fixed field we take
  set U : Subgroup (Ω ≃ₐ[k] Ω) := K.fixingSubgroup ⊓ E.fixingSubgroup with hUdef
  have hUopen : IsOpen (U : Set (Ω ≃ₐ[k] Ω)) :=
    (IntermediateField.fixingSubgroup_isOpen K).inter
      (IntermediateField.fixingSubgroup_isOpen E)
  obtain ⟨L, hLfin, hLnorm, hKL, hfixL⟩ :=
    Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K U hUopen
  have hLgal : IsGalois k ↥L := by
    haveI : FiniteDimensional k ↥L := hLfin
    haveI : Normal k ↥L := hLnorm
    infer_instance
  refine ⟨L, hLfin, hLgal, hKL, fun hzero => ?_⟩
  have hcL : c ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker (E := L)]
    exact MonoidHom.mem_ker.mpr hzero
  exact hcE (hfixL hcL).2

end LevelRes

end Work.SSGRoute.PT
