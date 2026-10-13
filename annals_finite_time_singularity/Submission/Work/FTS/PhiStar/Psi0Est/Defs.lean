/-
# `Work.FTS.PhiStar.Psi0Est.Defs` — the model functions of the endpoint analysis of `ψ`

The model function `ψ = psiSol α` (`Psi0Ode.lean`) is
`ψ(θ) = sin(2θ)·(Kc α + w₀(θ))` with `w₀ = wZer α = ∫_0^θ P/sin²`, and
`ψ'' = 2P − 4ψ − Γ̄` on `(0,π/2)` (`psiSol_sndDeriv`).  The purpose of this module is to
record the two auxiliary functions

* `qfun α θ = Pfun α θ / sin²θ`   (`= w₀'(θ)`), and
* `M1 α θ = 2cos(2θ)(Kc α + wZer α θ) + sin(2θ)·qfun α θ`   (`= ψ'(θ)`),

which make the `deriv`-junk behaviour of `ψ''` at the endpoints `θ = 0, π/2` manageable,
together with the elementary bookkeeping lemmas for `z`-independent functions that the
`𝒲^{l,∞}`-reduction needs.

Nothing here is proved by `sorry`; the deep facts about `qfun` (its continuity at the
endpoints) and about `M1` (that it agrees with `deriv ψ` and is flat at the endpoints) are
stated in the sibling modules `qfun_tendsto_endpoints`, `deriv_psiSol_eventuallyEq_M1` and
`hasDerivAt_M1_endpoints`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Psi0Ident
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-! ## The model functions -/

/-- `q = P/sin²θ = w₀'`, extended to all of `ℝ` by totalisation: `qfun α 0 = 0` and
`qfun α (π/2) = Pfun α (π/2)/1 = 0`. -/
def qfun (α : ℝ) (θ : ℝ) : ℝ := Pfun α θ / Real.sin θ ^ 2

/-- The explicit model for the first derivative of `psiSol α`:
`M1 α θ = 2cos(2θ)(Kc + w₀) + sin(2θ)·q`. -/
def M1 (α : ℝ) (θ : ℝ) : ℝ :=
  2 * Real.cos (2 * θ) * (Kc α + wZer α θ) + Real.sin (2 * θ) * qfun α θ

@[simp] lemma qfun_apply (α θ : ℝ) : qfun α θ = Pfun α θ / Real.sin θ ^ 2 := rfl

@[simp] lemma M1_apply (α θ : ℝ) :
    M1 α θ = 2 * Real.cos (2 * θ) * (Kc α + wZer α θ) + Real.sin (2 * θ) * qfun α θ :=
  rfl

/-! ## Separation of variables for `z`-independent functions -/

/-- `∂_z^{k}` of a function of `θ` alone vanishes for `k ≥ 1`. -/
theorem pzIter_theta_only_succ (g : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter (k + 1) (fun _ θ => g θ) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero =>
      funext z θ
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      simp
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      rw [Work.Spaces.pz]
      simp

/-- `D_θ^j` of a function of `θ` alone is the `dthU`-iterate of that function. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ θ => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.pth, ← Work.Spaces.dthU_apply,
        Function.iterate_succ_apply']

/-- The supremum of the zero function is zero. -/
theorem supAbs_zero_eq : Work.Spaces.supAbs (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  refine le_antisymm (Work.Spaces.supAbs_le (fun z hz θ hθ => by simp)) ?_
  have h := Work.Spaces.le_supAbs (g := fun _ _ : ℝ => (0 : ℝ))
    (z := 0) (θ := 0) (C := 0) Work.Spaces.zero_mem_Iz Work.Spaces.zero_mem_Iθ
    (fun z hz θ hθ => by simp)
  simpa using h

/-! ## Vanishing of the `dthU`-iterates at the angular boundary -/

lemma dthU_apply_zero (f : ℝ → ℝ) : Work.Spaces.dthU f 0 = 0 := by
  simp [Work.Spaces.dthU_apply]

lemma dthU_apply_pi_half (f : ℝ → ℝ) : Work.Spaces.dthU f (Real.pi / 2) = 0 := by
  rw [Work.Spaces.dthU_apply, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
    zero_mul]

lemma dthU_iter_apply_zero (f : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] f 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k = k + 1 from by omega, Function.iterate_succ_apply']
  exact dthU_apply_zero _

lemma dthU_iter_apply_pi_half (f : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Work.Spaces.dthU^[j] f (Real.pi / 2) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + k = k + 1 from by omega, Function.iterate_succ_apply']
  exact dthU_apply_pi_half _

end Work.FTS.PhiStar.Psi0Est
