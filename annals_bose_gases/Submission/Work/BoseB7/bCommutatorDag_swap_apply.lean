import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.bCommutator_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

/-- The transposed form of the squeezed commutator `bCommutator_eq`: applied to a
vector, `[b_{-k}, b_{s-k}†] = (1-α_kα_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k))`.

This is the identity FS `lem:EstimatesOnQ3-js` uses when they move `b_{-k}`
through `b_{s-k}†` in the `h.c.` half of `Q₃` (the scalar is a real multiple of
the identity, so it is unchanged by transposition, cf. `bCommutator_eq`).

The computation is the mirror image of `bCommutator_eq`'s: with `p = s-k`,
`q = -k`, expanding `b_q b_p† - b_p† b_q = [a_q,a_p†] + α_p[a_q,a_{-p}]
+ α_q[a_{-q}†,a_p†] + α_qα_p[a_{-q}†,a_{-p}]` kills the middle two terms by
`ann_comm`/`cre_comm` and leaves `ccrK (-k) (s-k) - α_{-k}α_{s-k}ccrK (k-s) k`,
which the kernel hypothesis `hasKernel` together with evenness of `α, χ̂, χ̂²`
rewrites into the asserted scalar. -/
theorem bCommutatorDag_swap_apply {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.EstHyp F E)
    (s k : Mode) (y : F.H) :
    F.bOp E.alpha (-k) (F.bOpDag E.alpha (s - k) y)
      = F.bOpDag E.alpha (s - k) (F.bOp E.alpha (-k) y)
        + ((1 - E.alpha k * E.alpha (s - k)) * (E.hatChiSq s - E.hatChi k * E.hatChi (s - k))) • y := by
  -- the two commutator kernels, in the `χ̂`, `χ̂²` language of the statement
  have hker1 : F.ccrK (-k) (s - k) = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
    rw [h.hasKernel (-k) (s - k), show -k - (s - k) = -s by abel, h.hatChiSqEven s,
      h.hatChiEven k]
  have hker2 : F.ccrK (k - s) k = E.hatChiSq s - E.hatChi k * E.hatChi (s - k) := by
    rw [h.hasKernel (k - s) k, show (k - s) - k = -s by abel, h.hatChiSqEven s,
      show k - s = -(s - k) by abel, h.hatChiEven (s - k)]
    ring
  -- the four elementary commutators, pointwise
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
  -- expand both sides and cancel
  simp only [FockData.bOp, FockData.bOpDag, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, neg_neg, neg_sub]
  rw [hA y, hB y, hC y, hD y, hker1, hker2, h.alphaEven k]
  module

end Work.BoseB7
