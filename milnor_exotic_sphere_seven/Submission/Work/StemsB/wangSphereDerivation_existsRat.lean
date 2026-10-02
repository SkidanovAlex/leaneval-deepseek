import Mathlib
import Submission.Work.StemsB.WangDerivationR
import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.StemsB.collarThomRat
import Submission.Work.StemsB.wangSphereDerivation_exists
import Submission.Work.StemsB.WangCohRat
import Submission.Work.StemsB.Rat.WangThetaTwDerivation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB

theorem wangSphereDerivation_existsRat (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : ContinuousMap E (Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    ∃ (γ : ∀ k : ℕ,
        Work.Cohomology.singularCohomology ℚ k (TopCat.of (p ⁻¹' Work.StemsB.sphLoopOuter b)) ≅
        Work.Cohomology.singularCohomology ℚ k (Work.StemsB.wangCohFsp b p))
      (τS : ∀ n : ℕ,
        (Work.Cohomology.relComplex ℚ (TopCat.of E)
            (p ⁻¹' Work.StemsB.sphLoopOuter b)).homology (n + b + 1) ≅
        Work.Cohomology.singularCohomology ℚ (n + 1) (Work.StemsB.wangCohFsp b p)),
      Work.StemsB.WangCohShiftDerivationR ℚ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
        (Work.StemsB.wangCohFsp b p) b γ τS := by
  refine ⟨Work.StemsB.Rat.wangGammaExplicit b p hT_O,
    fun n => Work.StemsB.Rat.wangTauSTw b hb E p hT_O d_G hT_G n, ?_⟩
  unfold Work.StemsB.WangCohShiftDerivationR
  intro n n' a b'
  rw [Work.StemsB.Rat.wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G (n + n' + b),
      Work.StemsB.Rat.wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G n,
      Work.StemsB.Rat.wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G n']
  exact Work.StemsB.Rat.wangThetaTw_derivation b hb E p d_G hT_G hT_O n n' a b'

end Work.StemsB
