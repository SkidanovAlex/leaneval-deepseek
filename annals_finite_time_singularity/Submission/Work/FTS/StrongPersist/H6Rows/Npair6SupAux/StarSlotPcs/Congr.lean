/-
# Congruence of the `ℋ^k`-integrand on the closed domain `Iz × Iθ`

Companion of `Work.FTS.StrongPersist.H6Pair6Aux.HkIntegrand_congr_Qd` (which is stated for the
*open* quadrant `Qd`): the `ℋ^k`-integrand and the `ℋ^k`-membership/norm only depend on the
values of the function on `Iz × Iθ`.  On the open quadrant this is locality of `Deriv`; at
`z = 0` and at `θ = 0, π/2` every weight of the integrand vanishes.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.Spaces.pz_aux
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `ℋ^k`-integrand only depends on the values of the function on the *closed* domain
`Iz × Iθ`. -/
theorem hkIntegrand_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k f' z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst α k f,
      Work.FTS.LocData.HkIntegrand_zero_fst α k f']
  · by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
    · refine Work.FTS.StrongPersist.H6Pair6Aux.HkIntegrand_congr_Qd (f := f) (f' := f')
        (fun z' θ' hzθ' => ?_) z θ ⟨hzpos, hθi⟩
      have hz' : (0 : ℝ) < z' := hzθ'.1
      have hθ' : θ' ∈ Work.Spaces.Iθ := ⟨le_of_lt hzθ'.2.1, le_of_lt hzθ'.2.2⟩
      exact h z' (show z' ∈ Work.Spaces.Iz from le_of_lt hz') θ' hθ'
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f z θ hs,
        Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k f' z θ hs]

/-- Honesty in `ℋ^k` transports along an equality on `Iz × Iθ`. -/
theorem hkMem_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ)
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k f' := by
  have hgoal := hkIntegrand_congr_Izθ (α := α) (k := k) (f := f) (f' := f') h
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro z hz
    exact (h1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hgoal z hz θ hθ))
  · refine h2.congr (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_))
    exact setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hgoal z hz θ hθ)

/-- The squared `ℋ^k`-norm transports along an equality on `Iz × Iθ`. -/
theorem hkSq_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k f' := by
  have hgoal := hkIntegrand_congr_Izθ (α := α) (k := k) (f := f) (f' := f') h
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici (fun z hz =>
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hgoal z hz θ hθ))

/-- The `ℋ^k`-norm transports along an equality on `Iz × Iθ`. -/
theorem hkNorm_congr_Izθ {α : ℝ} {k : ℕ} {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = f' z θ) :
    Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k f' := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hkSq_congr_Izθ h]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
