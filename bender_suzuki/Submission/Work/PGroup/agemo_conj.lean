import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise
open Subgroup

namespace Work.PGroup

/-- Membership in a conjugate of a subgroup: `x ∈ gHg⁻¹ ↔ g⁻¹ x g ∈ H`. -/
theorem mem_conjBy_iff {G : Type*} [Group G] {g x : G} {H : Subgroup G} :
    x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  rw [conjBy, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]

/-- The agemo subgroup `℧ⁱ(P)` is characteristic in `P`: it is invariant under conjugation by
every element of the normalizer of `P` (FT §2). -/
theorem agemo_conj {G : Type*} [Group G] (p i : ℕ) (P : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    Work.PGroup.conjBy g (Work.PGroup.agemo p i P) = Work.PGroup.agemo p i P := by
  apply le_antisymm
  · -- `g · ℧ⁱ(P) · g⁻¹ ≤ ℧ⁱ(P)`: the conjugate of a `p ^ i`-th power is a `p ^ i`-th power.
    rw [Work.PGroup.conjBy, Work.PGroup.agemo, Subgroup.smul_closure, Subgroup.closure_le]
    rintro y hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨y0, hy0, hy_eq⟩ := hy
    obtain ⟨x, hx, rfl⟩ := hy0
    rw [MulAut.smul_def] at hy_eq
    rw [← hy_eq]
    rw [map_pow]
    exact pow_mem_agemo ((Subgroup.mem_normalizer_iff.mp hg x).mp hx)
  · -- `℧ⁱ(P) ≤ g · ℧ⁱ(P) · g⁻¹`: every `p ^ i`-th power is the conjugate of a `p ^ i`-th power.
    rw [Work.PGroup.agemo, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    change x ^ p ^ i ∈ Work.PGroup.conjBy g (Subgroup.closure {y : G | ∃ x ∈ P, x ^ p ^ i = y})
    rw [mem_conjBy_iff]
    have hx' : g⁻¹ * x * g ∈ P := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    rw [← MulAut.conj_inv_apply g (x ^ p ^ i), map_pow ((MulAut.conj g)⁻¹) x (p ^ i),
      MulAut.conj_inv_apply g x]
    exact pow_mem_agemo hx'

end Work.PGroup
