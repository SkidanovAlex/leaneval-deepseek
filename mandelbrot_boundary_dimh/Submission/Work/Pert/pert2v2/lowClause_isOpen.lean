import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.DphiP_open
import Submission.Work.Pert.pert2v2.RBlockCharts
import Submission.Work.Pert.pert2v2.continuousAt_iterate_phi_of_continuousOn

/-! Guidance from the project lead (the requester):

LEAD (pert2_v2 skeleton item S2). The set where the crux's low clause holds is open. Route, one conjunct of Work.Pert.pert2v2.LowClause at a time (RBlockDefs.lean):
  (1) {w ∈ U | ∀ j ≤ m, f^[j] (φ w) ∈ Df}: induction on m; f is continuous on the open Df and φ is continuous on the open U, so each step is the preimage of an open set under a map continuous on an open set.
  (2) f^[m] (φ w) ∈ τ '' Qp′: τ '' Qp′ is OPEN. τ is holomorphic with nonzero derivative on the open Qp′, hence an open map there (Work.Pert.Ksub2.exists_ball_local_inverse, or Mathlib's local homeomorphism / open mapping for analytic maps). Then intersect with (1).
  (3) F (invOn τ Qp′ (f^[m] (φ w))) ∈ Qp′: invOn τ Qp′ is continuous on τ '' Qp′ (Work.Pert.pert2v2.invOn_continuousAt in RBlockCharts.lean, using injectivity and τ′ ≠ 0). F is continuous on Qp′ and Qp′ is open, so this is a preimage of an open set on the open set from (2).
Reuse; do not re-prove: invOn_continuousAt, exists_ball_local_inverse, DphiP_open's iterate argument.
-/

namespace Work.Pert.pert2v2

open MandelDim
open Filter Set
open scoped Topology

theorem lowClause_isOpen {f F τ φ : ℂ → ℂ} {Df Qp' U : Set ℂ} {m : ℕ}
    (hU : IsOpen U) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    (hQp' : IsOpen Qp') (hτ : DifferentiableOn ℂ τ Qp') (hτne : ∀ z ∈ Qp', deriv τ z ≠ 0)
    (hinj : Set.InjOn τ Qp') (hF : ContinuousOn F Qp') (hφ : ContinuousOn φ U) :
    IsOpen {w : ℂ | w ∈ U ∧ Work.Pert.pert2v2.LowClause f Df F τ φ Qp' m w} := by
  -- openness is proved pointwise, one neighbourhood at a time
  rw [isOpen_iff_mem_nhds]
  rintro w₀ ⟨hwU, hclause⟩
  rw [LowClause] at hclause
  obtain ⟨hwalk, hland, hret⟩ := hclause
  -- ### (1) the walk-map `w ↦ f^[m] (φ w)` is continuous at `w₀`
  have hiter : ContinuousAt (fun w : ℂ => f^[m] (φ w)) w₀ :=
    continuousAt_iterate_phi_of_continuousOn hU hφ hDf hf hwU hwalk
  -- ### (3) the chosen preimage map `w ↦ invOn τ Qp' (f^[m] (φ w))` is continuous at `w₀`:
  -- its value is `τ ς` for a gate point `ς`, and `invOn τ Qp'` is the local inverse of `τ`
  -- at `ς` (`pert2v2.invOn_continuousAt`), so it is continuous there.
  have hpre : Work.Pert.invOn τ Qp' (f^[m] (φ w₀)) ∈ Qp' := Work.Pert.invOn_mem hland
  have hinv : ContinuousAt (fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) w₀ := by
    obtain ⟨ς, hςQ, hςτ⟩ := hland
    have h1 : ContinuousAt (fun v : ℂ => Work.Pert.invOn τ Qp' v) (τ ς) :=
      invOn_continuousAt hQp' hτ hinj hςQ (hτne ς hςQ)
    rw [hςτ] at h1
    exact h1.comp (g := fun v : ℂ => Work.Pert.invOn τ Qp' v)
      (f := fun w : ℂ => f^[m] (φ w)) hiter
  -- ### (2) the landing value lies in the *open* set `τ '' Qp'`
  have hτopen : IsOpen (τ '' Qp') := Work.Pert.isOpen_image_of_deriv_ne_zero hQp' hτ hτne
  have hτQp' : τ '' Qp' ∈ 𝓝 (f^[m] (φ w₀)) := hτopen.mem_nhds hland
  -- ### each conjunct holds eventually
  have hwalk_ev : ∀ᶠ w in 𝓝 w₀, ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df := by
    have hfin : ∀ᶠ w in 𝓝 w₀, ∀ i : Fin (m + 1), f^[i.val] (φ w) ∈ Df := by
      rw [Filter.eventually_all]
      intro i
      exact (continuousAt_iterate_phi_of_continuousOn (m := i.val) hU hφ hDf hf hwU
        (fun j hj => hwalk j (le_trans hj (Nat.le_of_lt_succ i.isLt)))).tendsto.eventually
        (hDf.mem_nhds (hwalk i.val (Nat.le_of_lt_succ i.isLt)))
    exact hfin.mono fun w hw j hj => hw ⟨j, Nat.lt_succ_of_le hj⟩
  have hland_ev : ∀ᶠ w in 𝓝 w₀, f^[m] (φ w) ∈ τ '' Qp' :=
    hiter.tendsto.eventually hτQp'
  have hret_ev : ∀ᶠ w in 𝓝 w₀, F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp' :=
    ((hF.continuousAt (hQp'.mem_nhds hpre)).comp
        (g := F) (f := fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) hinv).tendsto.eventually
      (hQp'.mem_nhds hret)
  have hclause_ev : ∀ᶠ w in 𝓝 w₀, LowClause f Df F τ φ Qp' m w := by
    show ∀ᶠ w in 𝓝 w₀, ((∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp' ∧
      F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp')
    exact hwalk_ev.and (hland_ev.and hret_ev)
  -- ### assemble: `U` is open, the clause holds on a neighbourhood
  exact Filter.mem_of_superset (Filter.inter_mem (hU.mem_nhds hwU) hclause_ev) (fun w hw => hw)

end Work.Pert.pert2v2
