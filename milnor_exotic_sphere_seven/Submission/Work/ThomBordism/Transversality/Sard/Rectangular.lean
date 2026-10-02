import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Assembly
import Submission.Work.ThomBordism.Transversality.Sard.strataDifference_null
import Submission.Work.ThomBordism.Transversality.Sard.localFlat
import Submission.Work.ThomBordism.Transversality.Sard.notFlat_null

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Rectangular Sard's theorem

The three steps of the classical proof of Sard's theorem are packaged in `SardSteps`
(`Sard/Assembly.lean`), and `sardEuclidOn_of_steps` runs the double induction.  All three steps are
now **proved** in this directory:

* `strataDifference_null` — the hypersurface step (from `levelSet_null`, `scalarPartial`);
* `localFlat` — the flat step (Taylor estimate);
* `notFlat_null` — the non-flat step (flow box + Fubini; `Sard/notFlat_null.lean`).

Hence

* `sardEuclid` — Sard's theorem for `C^∞` maps `ℝⁿ → ℝᵐ`, for **all** `n`, `m`;
* `sardRectangular` — the chapter's input `Work.ThomBordism.Transversality.SardRectangular`
  (Sard for `C^∞` maps `ℝ^a → ℝ^b`, `b ≤ a`), **unconditional**.

The statement `NotFlatStep` isolates the non-flat step; it is kept (with `sardSteps_of`,
`sardEuclid_of`, `sardRectangular_of`) because it is the exact form in which the classical proof
produces the remaining piece, and `notFlatStep_holds` records that it is now a theorem.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInf CInfOn Zk IsCriticalPoint SardEuclid SardEuclidOn
  SardRectangular)

/-- **The non-flat step** of the classical proof of Sard's theorem: the image of the critical set
with non-vanishing derivative is null (this is the straightening + Fubini piece).
`notFlatStep_holds` proves it (`Sard/notFlat_null.lean`). -/
def NotFlatStep : Prop :=
  ∀ (n m : ℕ), SardEuclidOn n m →
    ∀ (f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1)))
      (U : Set (EuclideanSpace ℝ (Fin (n+1)))),
      IsOpen U → CInfOn f U →
        volume (f '' (({x | IsCriticalPoint f x} \ Zk f 1) ∩ U)) = 0

/-- The non-flat step is a theorem: `Sard.notFlat_null` (`Sard/notFlat_null.lean`). -/
theorem notFlatStep_holds : NotFlatStep :=
  fun _ _ hIH _ _ hU hf => notFlat_null hIH hU hf

/-- The three steps, with the two proved ones filled in from `strataDifference_null` and
`localFlat`. -/
theorem sardSteps_of (h : NotFlatStep) : SardSteps where
  notFlat := h
  strata := fun _ _ k hk hIH _ _ hU hf => strataDifference_null hk hIH hU hf
  flat := fun _ _ K hK hKm _ _ hU hf => localFlat hK hKm hU hf

/-- The three steps, unconditionally. -/
theorem sardSteps : SardSteps := sardSteps_of notFlatStep_holds

/-- **Rectangular Sard's theorem** for `C^∞` maps `ℝⁿ → ℝᵐ` (all `n`, `m`). -/
theorem sardEuclid_of (h : NotFlatStep) (n m : ℕ) : SardEuclid n m :=
  sardEuclid_of_steps (sardSteps_of h) n m

/-- **Sard's theorem for `C^∞` maps `ℝⁿ → ℝᵐ`**, for all `n`, `m`. -/
theorem sardEuclid (n m : ℕ) : SardEuclid n m :=
  sardEuclid_of notFlatStep_holds n m

/-- **The chapter's input `SardRectangular`**, from the non-flat step: Sard's theorem for `C^∞` maps
`ℝ^a → ℝ^b` with `b ≤ a`. -/
theorem sardRectangular_of (h : NotFlatStep) : SardRectangular := by
  intro a b _ f hf
  exact sardEuclid_of h a b f hf

/-- **Sard's theorem, rectangular case** (item 1 of the chapter): for a `C^∞` map `ℝ^a → ℝ^b` with
`b ≤ a` the set of critical values has measure zero.  Unconditional. -/
theorem sardRectangular : SardRectangular := sardRectangular_of notFlatStep_holds

end Work.ThomBordism.Transversality.Sard
