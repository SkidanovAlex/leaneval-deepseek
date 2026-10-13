import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroCore
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf1dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.l12ContDiffOnOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

theorem T5bZeroTerm : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  refine ⟨8 * CL, by positivity, ?_⟩
  intro α hα f a b ρ hsm hm6 hm7 hvt haxis hl12 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hCL' : ∀ k ≤ 4, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ CL * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hCL α f hα0 hα1 hsm hm6 hl12 k hk z hz
  have hψsm : ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
    l12ContDiffOnOpen α hα f hsm hm7
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (hσcont := Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta)
      (hσnn := fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.sin_two_nonneg_Iθ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
      (hσcap := by
        intro θ hθ
        by_cases ha0 : a = 0
        · rw [if_pos ha0]
        · rw [if_neg ha0]
          exact Work.FTS.H2.rpow_eta_le_gam hα0 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafEta] using hcore
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun _ => (1:ℝ)) (hσcont := continuousOn_const)
      (hσnn := fun θ _ => zero_le_one)
      (hσcap := by
        intro θ hθ
        refine Work.FTS.TransportS.one_le_rpow_neg ?_ hθ
        by_cases ha0 : a = 0
        · rw [if_pos ha0]; norm_num [Work.Spaces.eta]
        · rw [if_neg ha0, Work.Spaces.gam]; linarith)
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafOne, mul_one] using hcore
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (hσcont := Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0
        (Work.Spaces.gam α))
      (hσnn := fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.sin_two_nonneg_Iθ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
      (hσcap := by
        intro θ hθ
        rw [if_neg (by omega : ¬ a = 0)])
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafGam] using hcore

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
