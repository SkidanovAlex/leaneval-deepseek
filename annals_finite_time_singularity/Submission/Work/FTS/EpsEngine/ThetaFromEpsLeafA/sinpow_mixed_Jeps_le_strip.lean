import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.StripDefs
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.Core
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.EpsMem_strip
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.stripLo_stripHi_eq_of_logrel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sinpow_mixed_Jeps_le_strip` — sub-leaf (A) of the θ-uniformity of `J_ε`

The pointwise bound (with the `sin^{γ-1}` gain kept) of the routed slot of the log-coordinate
mollifier against the **strip** energy of the truncations `stripLo`/`stripHi`:

  `sin(2θ)^{1-γ} · (D_z^b D_θ^a (J_ε g) z θ)² ≤ C · EpsSq α (stripLo (thShift θ (-ε)) g)`

(and the symmetric statement at the `π/2`-end).  The whole analytic content is in
`ThetaFromEpsLeafA/Core.core_bound`: the routed identity, the (unweighted) Cauchy–Schwarz, the
log-coordinate substitution `subst_kernel_iter`, and the pointwise density comparison on the
kernel window.  Here the two truncations are only *instantiated*:

* `EpsMem_strip` gives the honesty of the truncated profiles;
* `stripLo_stripHi_eq_of_logrel` says that on the window (`|p₂| ≤ ε` and
  `p₂ = log tan θ − log tan θ'`) each truncation agrees with `g`.
-/

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

theorem sinpow_mixed_Jeps_le_strip {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.FTS.StrongEps.EpsMem α g →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α
              (Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) ∧
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α
              (Work.FTS.EpsEngine.ThetaFromEps.stripHi
                (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) := by
  obtain ⟨C, hC0, hcore⟩ := core_bound (ρ := ρ) hρ hα hε hε1 a b
  refine ⟨C, hC0, ?_⟩
  intro g hsm hg z θ hz hθ0 hθπ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθπ⟩
  have hLo : Work.FTS.StrongEps.EpsMem α
      (Work.FTS.EpsEngine.ThetaFromEps.stripLo (Work.FTS.StrongEps.thShift θ (-ε)) g) :=
    (EpsMem_strip hg (Work.FTS.StrongEps.thShift θ (-ε))).1
  have hHi : Work.FTS.StrongEps.EpsMem α
      (Work.FTS.EpsEngine.ThetaFromEps.stripHi
        (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε) g) :=
    (EpsMem_strip hg (Real.pi / 2 - Work.FTS.StrongEps.thShift θ ε)).2
  constructor
  · exact hcore g hsm z θ hz hθI _ hLo
      (fun z' θ' p₂ _ hθ' hp₂ hrel =>
        (stripLo_stripHi_eq_of_logrel hθI hε hθ' hp₂ hrel).1)
  · exact hcore g hsm z θ hz hθI _ hHi
      (fun z' θ' p₂ _ hθ' hp₂ hrel =>
        (stripLo_stripHi_eq_of_logrel hθI hε hθ' hp₂ hrel).2)

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
