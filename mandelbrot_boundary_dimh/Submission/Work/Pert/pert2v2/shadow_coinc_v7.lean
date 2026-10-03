import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.AsmDefs

/-! Guidance from the project lead (the requester):

LEAD DESIGN (pert2_v2 S12 hcross, the coincidence step). Elementary.
1. F^[m] ς ∈ Qp': hQp' plus Set.mem_iUnion₂ with x := w, and Metric.mem_ball/dist_eq_norm from hshadow.
2. τ (F^[m] ς) = f^[m] (τ ς), by induction on the walk: hτF at F^[j] ς ∈ Qp Ξ α for j < m (hwalk) and Function.iterate_succ_apply'.
3. invOn τ Qp' (τ (F^[m] ς)) = F^[m] ς by Work.Pert.invOn_eq (AsmDefs.lean) with hinjτ and step 1.
Used in pert2_v2 with crux_limit_v7 (Qp' is exposed there as exactly this union) and Work.Pert.pert2v2.Rlow_eq_retOf_crux_walk (its hcoinc). hshadow comes from Work.Pert.pert2v2.ShadowBand.shadow_of_walks.
-/

namespace Work.Pert.pert2v2

open MandelDim Set Metric Filter Topology

theorem shadow_coinc_v7 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {f F τ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {K Qp' : Set ℂ} {m : ℕ} {w ς : ℂ}
    (hQp' : Qp' = ⋃ x ∈ K, Metric.ball (MandelDim.tau0 (f₀^[m] (d.φ x))) 4)
    (hinjτ : Set.InjOn τ Qp') (hwK : w ∈ K)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Work.Pert.Qp Ξ α)
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ α, τ (F z) = f (τ z))
    (hshadow : ‖F^[m] ς - MandelDim.tau0 (f₀^[m] (d.φ w))‖ < 4) :
    F^[m] ς ∈ Qp' ∧ Work.Pert.invOn τ Qp' (f^[m] (τ ς)) = F^[m] ς := by
  -- Step 1: the `m`-th iterate of `ς` lands in `Qp'`, via the shadow estimate.
  have hmem : F^[m] ς ∈ Qp' := by
    rw [hQp']
    refine Set.mem_iUnion₂.mpr ⟨w, hwK, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact hshadow
  -- Step 2: `τ` intertwines the two walks, so `τ (F^[m] ς) = f^[m] (τ ς)`.
  have hiter : ∀ j : ℕ, j ≤ m → τ (F^[j] ς) = f^[j] (τ ς) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      rw [Function.iterate_succ_apply']
      rw [hτF (F^[k] ς) (hwalk k hk'), ih hk']
      rw [Function.iterate_succ_apply']
  refine ⟨hmem, ?_⟩
  -- Step 3: `τ` is injective on `Qp'`, so the preimage of `f^[m] (τ ς)` is `F^[m] ς`.
  have hval : τ (F^[m] ς) = f^[m] (τ ς) := hiter m le_rfl
  exact Work.Pert.invOn_eq hinjτ ⟨F^[m] ς, hmem, hval⟩ hmem hval

end Work.Pert.pert2v2
