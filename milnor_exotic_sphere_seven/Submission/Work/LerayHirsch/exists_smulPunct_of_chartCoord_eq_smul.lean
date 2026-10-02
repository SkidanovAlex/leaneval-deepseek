import Mathlib
import Submission.Work.LerayHirsch.Punctum

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace Work.LerayHirsch

/-- **Chart coordinates determine proportionality.**  If two points of the punctured total space of
a complex gluing-data bundle `Z` lie over the same base point `b ∈ Z.baseSet i` and their `i`-th
chart coordinates are proportional (by a complex number `c`), then they differ by the `ℂˣ`-action,
i.e. `p = d • q` for a unit `d`.  The scalar is automatically a unit because `chartCoord` is nonzero
on the punctured part (`chartCoord_ne_zero_of_mem_baseSet`). -/
theorem exists_smulPunct_of_chartCoord_eq_smul {m : ℕ} {B : Type}
    [TopologicalSpace B] {ι : Type}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    {p q : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z))}
    (hp : p.1.proj ∈ Z.baseSet i) (hq : q.1.proj ∈ Z.baseSet i) (hb : p.1.proj = q.1.proj)
    {c : ℂ} (h : Work.LerayHirsch.chartCoord Z i p = c • Work.LerayHirsch.chartCoord Z i q) :
    ∃ d : ℂˣ, p = Work.LerayHirsch.smulPunct Z d q := by
  -- The scalar is automatically nonzero, since `chartCoord` is nonzero on the punctured part.
  have hcq : c ≠ 0 := by
    intro hc
    have hp0 := Work.LerayHirsch.chartCoord_ne_zero_of_mem_baseSet Z i p hp
    rw [h, hc, zero_smul] at hp0
    exact hp0 rfl
  refine ⟨Units.mk0 c hcq, ?_⟩
  -- The transition `coordChange i (indexAt ·) ·` inverts the chart coordinates.
  have hkey : ∀ v : EuclideanSpace ℂ (Fin m),
      (Z.coordChange i (Z.indexAt q.1.proj) q.1.proj)
        ((Z.coordChange (Z.indexAt q.1.proj) i q.1.proj) v) = v := by
    intro v
    have hc' := Z.coordChange_comp (Z.indexAt q.1.proj) i (Z.indexAt q.1.proj) q.1.proj
      ⟨⟨Z.mem_baseSet_at q.1.proj, hq⟩, Z.mem_baseSet_at q.1.proj⟩ v
    rw [Z.coordChange_self (Z.indexAt q.1.proj) q.1.proj (Z.mem_baseSet_at q.1.proj) v] at hc'
    exact hc'
  -- Unfold the chart coordinates and use that the two points lie over the same base point.
  have hT : (Z.coordChange (Z.indexAt q.1.proj) i q.1.proj) (show EuclideanSpace ℂ (Fin m) from p.1.snd)
      = c • (Z.coordChange (Z.indexAt q.1.proj) i q.1.proj) (show EuclideanSpace ℂ (Fin m) from q.1.snd) := by
    have h1 := h
    rw [Work.LerayHirsch.chartCoord_def, Work.LerayHirsch.chartCoord_def, hb] at h1
    exact h1
  -- Apply the inverse transition to both sides.
  have hv : (show EuclideanSpace ℂ (Fin m) from p.1.snd)
      = c • (show EuclideanSpace ℂ (Fin m) from q.1.snd) := by
    have h2 := congrArg (Z.coordChange i (Z.indexAt q.1.proj) q.1.proj) hT
    rw [map_smul, hkey, hkey] at h2
    exact h2
  -- Assemble: the base points agree and the fibres agree by `hv`.
  refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
  · simpa using hb
  · exact heq_of_eq hv

end Work.LerayHirsch
