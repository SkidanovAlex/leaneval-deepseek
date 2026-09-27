import Mathlib
import Submission.Work.Sard.wp.Defs
import Submission.Work.Sard.holder_two_fderiv_eq_zero
import Submission.Work.Sard.holder_three_snd_fderiv_eq_zero
import Submission.Work.Sard.dimH_levelSet_le
import Submission.Work.Drive.sard_weak_empty_interior

/-!
# The weak form of Sard's theorem, level `1` (`ℝ² → ℝ`), global version

`Work.Sard.wp.WeakSardGlobal 1` states: for a `C^∞` map `ρ : E → F` between finite-dimensional real
normed spaces with `finrank ℝ F = 1` and `finrank ℝ E = 2` (i.e. `finrank ℝ E = finrank ℝ F + 1`),
the set of critical values `ρ '' {z | ¬ Surjective (fderiv ℝ ρ z)}` has empty interior.

For a target of dimension one the critical set is exactly `{z | fderiv ℝ ρ z = 0}` (a linear map into
a one-dimensional space is surjective iff it is nonzero), so the whole content is the `m = 1` case of
the flat stratum, proved in `Work.Drive.flat_case_one` (Hausdorff dimension `2/3 < 1`).  The passage
from the compact statement to the global one is Baire category applied to the σ-compact exhaustion of
`E` by the closed balls around the origin, the critical set being closed.
-/

open scoped ContDiff Topology
open Set Filter

namespace Work.Sard

/-- A continuous linear map into a one-dimensional space is surjective iff it is nonzero. -/
private lemma surjective_iff_ne_zero_of_finrank_eq_one {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ F = 1) (L : E →L[ℝ] F) :
    Function.Surjective L ↔ L ≠ 0 := by
  constructor
  · intro hL h0
    have hsub : Subsingleton F := ⟨fun a b => by
      obtain ⟨x, hx⟩ := hL a
      obtain ⟨y, hy⟩ := hL b
      rw [h0] at hx hy
      have hxa : a = 0 := by simpa using hx.symm
      have hyb : b = 0 := by simpa using hy.symm
      rw [hxa, hyb]⟩
    have h0' : Module.finrank ℝ F = 0 := Module.finrank_zero_iff.mpr hsub
    omega
  · intro hL
    have h2 : Module.finrank ℝ (LinearMap.range (L : E →ₗ[ℝ] F)) = Module.finrank ℝ F := by
      obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
        by_contra h
        push Not at h
        exact hL (ContinuousLinearMap.ext h)
      have hmem : L v ∈ LinearMap.range (L : E →ₗ[ℝ] F) := LinearMap.mem_range_self _ _
      have hspan : Submodule.span ℝ {L v} ≤ LinearMap.range (L : E →ₗ[ℝ] F) :=
        Submodule.span_le.mpr (by simp [hmem])
      have h1 : Module.finrank ℝ (Submodule.span ℝ {L v}) = 1 := finrank_span_singleton hv
      have h3 : Module.finrank ℝ (LinearMap.range (L : E →ₗ[ℝ] F)) ≤ 1 := by
        calc Module.finrank ℝ (LinearMap.range (L : E →ₗ[ℝ] F)) ≤ Module.finrank ℝ F :=
              Submodule.finrank_le _
          _ = 1 := hF
      have hle := Submodule.finrank_mono hspan
      omega
    have htop : LinearMap.range (L : E →ₗ[ℝ] F) = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact LinearMap.range_eq_top.mp htop

theorem weakSardGlobalOne : Work.Sard.wp.WeakSardGlobal 1 := by
  intro E _ _ _ F _ _ _ hF hE ρ hρ
  have hE2 : Module.finrank ℝ E = 2 := by omega
  -- for a one-dimensional target, critical means vanishing derivative
  have hcrit : {z : E | ¬ Function.Surjective (fderiv ℝ ρ z)} = {z : E | fderiv ℝ ρ z = 0} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, surjective_iff_ne_zero_of_finrank_eq_one hF,
      not_not]
  rw [hcrit]
  have hclosed : IsClosed {z : E | fderiv ℝ ρ z = 0} :=
    isClosed_eq (hρ.continuous_fderiv (by norm_num)) continuous_const
  -- σ-compact exhaustion of the plane
  have hcover : {z : E | fderiv ℝ ρ z = 0} =
      ⋃ m : ℕ, ({z : E | fderiv ℝ ρ z = 0} ∩ Metric.closedBall (0 : E) m) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⌈‖x‖⌉₊, hx, mem_closedBall_zero_iff.mpr (Nat.le_ceil _)⟩
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
      exact hm.1
  rw [hcover, Set.image_iUnion]
  refine Work.Sard.wp.interior_eq_empty_iUnion_isClosed (fun m => ?_) (fun m => ?_)
  · exact (((isCompact_closedBall (0 : E) m).inter_left hclosed).image hρ.continuous).isClosed
  · exact Work.Drive.flat_case_one hE2 hF ρ hρ (Metric.closedBall (0 : E) m) (isCompact_closedBall _ _)

end Work.Sard
