import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.bCommutator_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseC3QAll

theorem bCommutatorDag_swap_s {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (s k : Mode)
    (h1 : F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k))
    (h2 : F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k))
    (hχ : ∀ s : Mode, E.hatChi (-s) = E.hatChi s)
    (hα : ∀ k : Mode, E.alpha (-k) = E.alpha k) (y : F.H) :
    F.bOp E.alpha (-k) (F.bOpDag E.alpha (s - k) y)
      = F.bOpDag E.alpha (s - k) (F.bOp E.alpha (-k) y)
        + ((1 - E.alpha k * E.alpha (s - k)) * (E.hatChiSq s - E.hatChi k * E.hatChi (s - k))) • y := by
  -- The two commutator kernels, in the `χ̂`, `χ̂²` language of the statement.
  have hker1 : F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := h1
  have hker2 : F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := h2
  -- The four elementary commutators, pointwise.
  have hA : ∀ f : F.H, F.a (-k) (F.aDag (s - k) f)
      = F.aDag (s - k) (F.a (-k) f) + (F.ccrK (-k) (s - k)) • f := by
    intro f
    have hh := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr (-k) (s - k))
    simpa using hh
  have hB : ∀ f : F.H, F.a (-k) (F.a (k - s) f) = F.a (k - s) (F.a (-k) f) := by
    intro f
    have hh := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ann_comm (-k) (k - s))
    simpa using hh
  have hC : ∀ f : F.H, F.aDag k (F.aDag (s - k) f) = F.aDag (s - k) (F.aDag k f) := by
    intro f
    have hh := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.cre_comm k (s - k))
    simpa using hh
  have hD : ∀ f : F.H, F.aDag k (F.a (k - s) f)
      = F.a (k - s) (F.aDag k f) - (F.ccrK (k - s) k) • f := by
    intro f
    have hh := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr (k - s) k)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at hh
    rw [hh]
    module
  -- Expand both sides and cancel.
  simp only [Work.BoseB7.FockData.bOp, Work.BoseB7.FockData.bOpDag, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul, neg_neg, neg_sub]
  rw [hA y, hB y, hC y, hD y, hker1, hker2, hα k]
  module

end Work.BoseC3QAll
