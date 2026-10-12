import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fderiv_update_p2_eq` — the `p.2`-slot invariance of the `p.1`-directional
derivative

If `G` is invariant under overwriting the `p.2`-th slot (`G (Function.update x p.2 t) = G x` for
every `x` and `t`), then `G` is the composition `G ∘ reset` of `G` with the projection `reset`
that sets the `p.2`-slot to `0`.  The chain rule then gives

    fderiv ℝ G x = (fderiv ℝ G (reset x)) ∘SL reset   for every `x` (⋆)

because `fderiv ℝ reset x = reset` (`reset` is a continuous linear map).  The direction vector
`slotDirVec p.1 j` lives in the `p.1`-slot and `p.1 ≠ p.2`, so it is fixed by `reset`; applying (⋆)
at `x = Function.update Y p.2 t` and at `x = Y` and using `reset (Function.update Y p.2 t) = reset Y`
gives the claim.

This is the identity that makes the density `imgFibreDG ℓ p G u = ∫_{x'}∫_{s∈boxL}
Σ_j (∂_{p.1,j}G)(insertCoord2 p u s x')²` of `imgFibreEnergyDefs` depend on `u` only.

`sorry`-free.
-/

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The continuous linear map resetting slot `k` to `0`: `x ↦ Function.update x k 0`. -/
noncomputable def resetSlot {n : ℕ} (k : Fin n) : (Fin n → E3) →L[ℝ] (Fin n → E3) :=
  ContinuousLinearMap.pi (fun i => if i = k then 0 else ContinuousLinearMap.proj i)

/-- Coordinates of `resetSlot k`. -/
lemma resetSlot_apply {n : ℕ} (k : Fin n) (x : Fin n → E3) (i : Fin n) :
    resetSlot k x i = if i = k then 0 else x i := by
  rw [resetSlot, ContinuousLinearMap.pi_apply]
  by_cases h : i = k
  · simp [h]
  · simp [h, ContinuousLinearMap.proj_apply]

/-- `resetSlot k` is `Function.update · k 0`. -/
lemma resetSlot_eq_update {n : ℕ} (k : Fin n) (x : Fin n → E3) :
    resetSlot k x = Function.update x k 0 := by
  funext i
  rw [resetSlot_apply, Function.update_apply]

/-- `resetSlot k` is insensitive to the overwriting of slot `k`. -/
lemma resetSlot_update {n : ℕ} (k : Fin n) (x : Fin n → E3) (s : E3) :
    resetSlot k (Function.update x k s) = resetSlot k x := by
  rw [resetSlot_eq_update, resetSlot_eq_update, Function.update_idem]

/-- `resetSlot p.2` fixes the `p.1`-slot direction vector when `p.1 ≠ p.2`. -/
lemma resetSlot_slotDirVec {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (j : Fin 3) :
    resetSlot p.2 (slotDirVec p.1 j) = slotDirVec p.1 j := by
  rw [resetSlot_eq_update]
  have h2 : slotDirVec p.1 j p.2 = 0 := by
    rw [slotDirVec, Function.update_apply]
    exact if_neg (fun h => hp h.symm)
  rw [← h2]
  exact Function.update_eq_self p.2 (slotDirVec p.1 j)

theorem fderiv_update_p2_eq {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {G : Submission.BoseGases.X n → ℝ} (hG : Differentiable ℝ G)
    (hGind : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      G (Function.update x p.2 t) = G x)
    (Y : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    fderiv ℝ G (Function.update Y p.2 t) (Work.BoseBoxFock.slotDirVec p.1 j)
      = fderiv ℝ G Y (Work.BoseBoxFock.slotDirVec p.1 j) := by
  have key : ∀ x : Submission.BoseGases.X n,
      fderiv ℝ G x = (fderiv ℝ G (resetSlot p.2 x)) ∘SL resetSlot p.2 := by
    intro x
    have hcomp : G = G ∘ (⇑(resetSlot (n := n) p.2)) := by
      funext y
      simp only [Function.comp_apply]
      rw [resetSlot_eq_update p.2 y, hGind y 0]
    calc fderiv ℝ G x
        = fderiv ℝ (G ∘ (⇑(resetSlot p.2))) x :=
          congrArg (fun (H : Submission.BoseGases.X n → ℝ) => fderiv ℝ H x) hcomp
      _ = (fderiv ℝ G (resetSlot p.2 x)) ∘SL (fderiv ℝ (⇑(resetSlot p.2)) x) :=
          fderiv_comp x (hG.differentiableAt) (ContinuousLinearMap.differentiableAt _)
      _ = (fderiv ℝ G (resetSlot p.2 x)) ∘SL resetSlot p.2 := by
          rw [ContinuousLinearMap.fderiv]
  have h1 := key (Function.update Y p.2 t)
  have h2 := key Y
  rw [h1, ContinuousLinearMap.comp_apply, resetSlot_update, resetSlot_slotDirVec hp j]
  rw [h2, ContinuousLinearMap.comp_apply, resetSlot_slotDirVec hp j]

end Work.BoseBoxFock
