import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

/-! ## The squeezed commutator `[b_{s-k}, b_{-k}†]` (FS `lem:EstimatesOnQ3-js`, piece 4)

Writing `p = s - k`, `q = -k`, so `-p = k - s`, `-q = k` and
`b_p = a_p + α_p a_{-p}†`, `b_q† = a_q† + α_q a_{-q}`, the bilinearity of the
composition and the four elementary commutators

* `[a_p, a_q†] = ccrK p q`,
* `[a_p, a_{-q}] = 0`, `[a_{-p}†, a_q†] = 0`,
* `[a_{-p}†, a_{-q}] = -[a_{-q}, a_{-p}†] = -ccrK (-q) (-p) = -ccrK k (k-s)`

give `[b_p, b_q†] = ccrK (s-k) (-k) - α_{s-k}α_{-k} ccrK k (k-s)`. -/
theorem bCommutator_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (s k : Mode) :
    F.bCommutator E s k =
      (F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s)) •
        (1 : F.H →ₗ[ℝ] F.H) := by
  -- the four elementary commutators, pointwise
  have hA : ∀ f : F.H, F.a (s - k) (F.aDag (-k) f)
      = F.aDag (-k) (F.a (s - k) f) + (F.ccrK (s - k) (-k)) • f := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr (s - k) (-k))
    simpa using h
  have hB : ∀ f : F.H, F.a (s - k) (F.a k f) = F.a k (F.a (s - k) f) := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ann_comm (s - k) k)
    simpa using h
  have hC : ∀ f : F.H,
      F.aDag (k - s) (F.aDag (-k) f) = F.aDag (-k) (F.aDag (k - s) f) := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.cre_comm (k - s) (-k))
    simpa using h
  have hD : ∀ f : F.H, F.aDag (k - s) (F.a k f)
      = F.a k (F.aDag (k - s) f) - (F.ccrK k (k - s)) • f := by
    intro f
    have h := congrArg (fun g : F.H →ₗ[ℝ] F.H => g f) (F.ccr k (k - s))
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [h]
    module
  -- expand both products and cancel the two vanishing commutators
  ext f
  simp only [Work.BoseB7.FockData.bCommutator, Work.BoseB7.FockData.bOp,
    Work.BoseB7.FockData.bOpDag, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, neg_neg, neg_sub]
  rw [hA f, hB f, hC f, hD f]
  simp only [Module.End.one_apply]
  module

end Work.BoseB7
