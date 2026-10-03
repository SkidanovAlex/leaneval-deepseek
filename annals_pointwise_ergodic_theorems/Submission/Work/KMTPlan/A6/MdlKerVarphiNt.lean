import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs
import Submission.Work.KMTAreas.A7.varphiNt_IW_facts

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators

/-- A summable majorant for the convolution kernel of `Tle ρ l` applied to the modulated bump
`φ_{N,t} = varphiNt N k t`, uniform in `t ∈ [1/2,1]`, together with the measurability in `t` of
that kernel. -/
theorem MdlKerVarphiNt (ρ : ℝ) (l N k : ℕ) :
    ∃ a : ℤ → ℝ, Summable a ∧
      (∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ,
        ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphiNt N k t) i‖ ≤ a i) ∧
      (∀ i : ℤ, Measurable
        (fun t : ℝ => Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphiNt N k t) i)) := by
  classical
  -- Uniform-in-`t` bounds for the modulated bump `φ_{N,t}` on `t ∈ [1/2,1]`.
  obtain ⟨R, S, hSnn, hS⟩ := Work.KMTAreas.A7.varphiNt_bounds N k
  set C : ℝ := 4 * (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * S) + 1 with hC
  refine ⟨fun i => C * (1 / (1 + |(i : ℝ)|) ^ 2), ?_, ?_, ?_⟩
  · -- summability: the majorant is a constant times the `j^{-2}` comparison weight
    have h := Work.KMTAreas.A7.summable_kmtKernWeight
    have h' : Summable (fun i : ℤ => C * ‖Work.KMTAreas.A7.kmtKernWeight i‖) :=
      h.mul_left C
    refine h'.congr fun i => ?_
    rw [Work.KMTAreas.A7.norm_kmtKernWeight]
  · -- uniformity: quadratic decay of the kernel of a `C²` compactly supported bump
    intro t ht i
    obtain ⟨-, hcd, hcs, h1, h2⟩ := hS t ht
    have hdec := Work.KMTAreas.A7.iwKernel_decay_of_bump
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) hcd hcs hSnn h1 h2 i
    have hker : ‖Work.KMTPlan.A6.mdlIWKer ρ l (Work.KMTAreas.A7.varphiNt N k t) i‖
        = ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t))) i‖ :=
      rfl
    rw [hker, hC]
    refine le_trans hdec ?_
    rw [Work.KMTAreas.A7.norm_kmtKernWeight]
  · -- measurability in `t`
    intro i
    exact Work.KMTAreas.A7.measurable_iwKernel_varphiNt ρ l N k i

end Work.KMTPlan.A6
