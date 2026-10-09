/-
Copyright (c) 2025. All rights reserved.

# Inflation followed by restriction is zero

The composite `H¹(G ⧸ N, A^N) --inf--> H¹(G, A) --res--> H¹(N, A)` vanishes; this is the
`⊆` half of the inflation–restriction exactness in degree `1`
(`Work.GroupCohomology.range_infH1_eq_ker_resH1`).

## Main result

* `Work.GroupCohomology.resH1_infH1_eq_zero`
-/
import Submission.Work.GroupCohomology.range_infH1_eq_ker_resH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- **Inflation followed by restriction is zero** in degree `1`. -/
theorem resH1_infH1_eq_zero :
    (resH1 (A := A) G N).comp (infH1 (A := A) N) = 0 := by
  refine AddMonoidHom.ext ?_
  intro x
  have hx : infH1 (A := A) N x ∈ (resH1 (A := A) G N).ker := by
    rw [← range_infH1_eq_ker_resH1 (A := A) N]
    exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [AddMonoidHom.comp_apply]
  exact hx

end Work.GroupCohomology
