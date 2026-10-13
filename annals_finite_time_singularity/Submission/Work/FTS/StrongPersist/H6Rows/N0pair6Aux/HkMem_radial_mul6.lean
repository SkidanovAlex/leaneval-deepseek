import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMaj6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMemOfContMajorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

theorem HkMem_radial_mul6 :
    ∀ (α B : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ), 0 < α → 0 ≤ B →
      ContDiffOn ℝ 6 X (Set.Ioi 0) →
      (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j X z| ≤ B) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 6 (fun z θ => X z * f z θ) := by
  intro α B X f _hα hB hX hbnd hf hmem
  obtain ⟨K, hKpos, hmaj⟩ := radialMaj6 α B X f hB hX hf hbnd
  exact HkMemOfContMajorant α 6 hKpos.le (radialMul6Cont α X f hX hf) hmem hmaj

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
