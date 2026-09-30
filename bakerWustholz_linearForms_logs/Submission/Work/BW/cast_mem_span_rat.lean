import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The integral span of the rows of `M` maps into the `ℚ`-span of the cast rows (an integral
combination is a rational combination). Proof: `Submodule.span_induction` on the membership, each
generator being `Submodule.subset_span (Set.mem_range_self j)`, the `smul` step using
`((c • a) i : ℚ) = (c : ℚ) • (a i : ℚ)`. -/
theorem cast_mem_span_rat {ρ r : ℕ} (M : Fin ρ → Fin r → ℤ) {x : Fin r → ℤ}
    (hx : x ∈ Submodule.span ℤ (Set.range M)) :
    (fun i => (x i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span (Set.mem_range_self j)
  | zero => exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
    simp only [Pi.add_apply, Int.cast_add]
    exact Submodule.add_mem _ iha ihb
  | smul c a _ iha =>
    have h : (fun i => ((c • a) i : ℚ)) = (c : ℚ) • (fun i => (a i : ℚ)) := by
      funext i; simp
    rw [h]
    exact Submodule.smul_mem _ _ iha

end Work.BW
