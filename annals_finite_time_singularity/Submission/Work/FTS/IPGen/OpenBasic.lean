/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/OpenBasic.lean` — the open-quadrant descent lemmas of the `IP`-chapter

The `add` clause of every `IP`-level package splits `IP (f₁ + f₂) g` at the three recursion
slots, so it needs

* the descent of the level-`(n+1)` honesty `HkMem α (n+1) f` to `HkMem α n (D_θf)`,
  `HkMem α n (D_zf)` and `HkMem α n f`; and
* the block continuity `BlocksCont k f` and the block additivity `BlocksAdd k f₁ f₂` of the
  arguments.

All five are *true* for `SmoothOpen` (interior `C^∞` on the open quadrant) data — this is the
open-quadrant counterpart of `CoercivityFix`'s `RegQ`-based descent (`HkMem_mono_quad`,
`RegQ_dz.mixed_Dz_shift`, `Comm2w.BlocksCont.of_smoothQuad`).  The two pointwise
dominations of the `ℋ`-integrands at consecutive levels are already in the tree
(`CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge`, with the sharp range `-(1/10) ≤ α`;
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ`), and the membership versions follow from them by
`LocData.HkMem_of_majorant`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Block continuity and block additivity from `SmoothOpen` -/

/-- **Block continuity from interior smoothness**: `SmoothOpen f` gives `C^∞` of every mixed
derivative `D_z^bD_θ^a f` on the *whole* open quadrant `Qd` (which is literally `Q0`, the
smoothness domain of `SmoothOpen`), hence `BlocksCont k f` for every `k`.  This is the
weakening of `Comm2w.BlocksCont.of_smoothQuad` needed for the `HQo` class. -/
theorem BlocksCont_of_smoothOpen {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont k f := by
  intro a b _
  exact (hf.mixed b a).continuousOn

/-- **Block additivity from interior smoothness**: for `SmoothOpen f₁`, `SmoothOpen f₂` every
mixed derivative of `f₁ + f₂` splits on the open quadrant (`SmoothOpen.mixed_add`). -/
theorem BlocksAdd_of_smoothOpen {k : ℕ} {f₁ f₂ : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂) :
    Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂ := by
  intro a b _ z θ hzθ
  exact h₁.mixed_add h₂ b a z θ hzθ.1 hzθ.2.1 hzθ.2.2

/-! ## Descent of `HkMem` along the recursion slots -/

/-- **`HkMem` descends one level along `D_θ`** (for `α` in the sharp range `-(1/10) ≤ α`
where `η ≤ γ`, which is precisely the range in which the pure `D_z`-slots of `D_θf` are
dominated by the mixed `(1,·)`-slots of `f`).

The pointwise domination with constant `1` is
`CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge`; `HkMem_of_majorant` turns it into membership,
the continuity input being `SmoothOpen.continuousOn_HkIntegrand` of `SmoothOpen.Dth`. -/
theorem HkMem_Dth_le {α : ℝ} {k : ℕ} {f : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α k (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (k + 1) f z θ)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf).continuousOn_HkIntegrand α k)
    hm.1 hm.2
    (fun z hz θ hθ => Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα k f z θ hz hθ)

/-- **`HkMem` descends one level along `D_z`** (no restriction on `α`).  This is the
`SmoothOpen`-hypothesis version of `EllipticEst.remov.EllWeakPos.HkMem_Dz_shift` (which spends
the intermediate level `k`), via the pointwise domination
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ`. -/
theorem HkMem_Dz_le {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α (k + 1) f) : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α k hf hm

/-- **`HkMem` descends any number of levels** in the open class: this is
`OpenPkg.HkMem_mono_open`, restated in this chapter's namespace for convenience. -/
theorem HkMem_mono_le {α : ℝ} {k : ℕ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ l : ℕ, l ≤ k → Work.Spaces.HkMem α k f → Work.Spaces.HkMem α l f :=
  Work.FTS.OpenPkg.HkMem_mono_open hf

/-- The descent triple consumed by the `HkIPStep`-lift of the `add` clause: from the
level-`(k+1)` honesty of `f` (and its interior smoothness) one gets the level-`k` honesty of
`f`, `D_θf` and `D_zf`. -/
theorem HkMem_descent {α : ℝ} {k : ℕ} {f : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkMem α k (Work.Spaces.Dth f)
      ∧ Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
  ⟨Work.FTS.OpenPkg.HkMem_mono_open hf k (Nat.le_succ k) hm,
    HkMem_Dth_le hα hf hm, HkMem_Dz_le hf hm⟩

end Work.FTS.IPGen
