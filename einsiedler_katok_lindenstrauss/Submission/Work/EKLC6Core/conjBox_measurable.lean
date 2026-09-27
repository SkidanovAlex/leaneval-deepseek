import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.conjBox_measurable`

The conjugated box `conjBox U t = aDiag t · Box1 U · (aDiag t)⁻¹` is Borel measurable.  This is
what makes the pointwise information `growthFun U ν t x = -log ν x (conjBox U t)` (Pisa 7.6/7.18,
the Birkhoff summand of the entropy contribution `D_μ(a,U)`) an honest integral against the
leaf-wise measures `ν x`.

`B₁^U` is the intersection of the closed group `U` with the closed sup-norm ball of radius `1`
around the identity, hence closed; and `conjBox U t` is the preimage of `B₁^U` under the
measurable conjugation map `g ↦ aDiag (-t) · g · aDiag (-t)⁻¹` (equivalently, its image under the
homeomorphism `g ↦ aDiag t · g · aDiag t⁻¹`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `B₁^U = Box1 U` is a Borel subset of `SL₃(ℝ)`: it is the intersection of the closed subgroup
`U` with the closed sup-norm ball `{g | ∀ i j, |g i j - 1 i j| ≤ 1}` around the identity. -/
theorem measurableSet_box1 {U : Subgroup SL3} (hU : IsHoro U) : MeasurableSet (Box1 U) := by
  have hUc : IsClosed (U : Set SL3) := hU.1
  have hK : IsClosed {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} := by
    rw [show {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}
        = ⋂ i : Fin 3, ⋂ j : Fin 3,
            {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} by
      ext g; simp]
    refine isClosed_iInter (fun i => isClosed_iInter (fun j => ?_))
    have hcont : Continuous (fun g : SL3 => g i j) := by fun_prop
    have hset : {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}
        = (fun g : SL3 => g i j) ⁻¹'
            (Set.Icc ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 1)
                     ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)) := by
      ext g
      rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
      constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
    rw [hset]
    exact isClosed_Icc.preimage hcont
  rw [show Box1 U = (U : Set SL3) ∩
      {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1} by
    ext g; simp [Box1]]
  exact (hUc.inter hK).measurableSet

theorem conjBox_measurable {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (t : Fin 3 → ℝ) : MeasurableSet (Work.EKLC6Core.conjBox U t) := by
  rw [Work.EKLC6Core.conjBox, ← Work.EKLC6Core.preimage_conj_neg t (Work.EKLContract.Box1 U)]
  exact (Work.EKLC6Core.measurableSet_box1 hU).preimage (Work.EKLC6Core.measurable_conj (-t))

end Work.EKLC6Core
