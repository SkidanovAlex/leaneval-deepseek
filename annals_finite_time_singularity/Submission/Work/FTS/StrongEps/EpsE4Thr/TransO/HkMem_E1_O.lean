/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/HkMem_E1_O` — `ℋⁿ`-membership of the `D_θ`-transfer defect, open class

The transfer of the coercivity fix (`CoercivityFix/Transfer/Profiles.lean`) is driven by the two
radial profiles `radA α f`, `radS α f` and their two defects

  `E1 α f = (D_θΓ)·radA α f`,     `E2 α f = Ê₂f + Γ·radS α f`.

This file proves the `ℋⁿ`-membership (`n ≤ 3`) of the first defect on the *open* coercivity class
`CoerAdmO α f` of the route (`EpsE4Thr/OpenClass.lean`), the `SmoothOpen`-twin of
`CoercivityFix/Transfer/E1_pkg` (whose class `CoerAdm` is the strip class `SmoothQuad`, which the
projected mollified slices of the route do not satisfy).

`E1 α f = B(θ)·R(z)` is a *separated* product: the angular factor `B = D_θΓ` is `C³` on `(0,π/2)`
(`Transfer.sinGam_contDiffOn_Ioo`) and the radial factor `R = radA α f` is `C⁴` on `(0,∞)` from
`SmoothOpen f` and `HkMem α 5 f` (`GalFields.Norm.radA_Corr_contDiffOn_four`).  The three
ingredients of the frozen proof are therefore available in the open class:

* **blocks continuity** `BlocksCont n (E1 α f)` — `BlocksCont_mul_factor` applied to the two
  factors (`E1_blocks_open_O` below);
* **the angular majorant** — `E1Parts.AngGam`, class-free;
* **the radial majorant** `∑_{j<4} (D_z^j (radA α f))²w²` — integrable by
  `EpsE4Thr.radA_slotSum_le` (the open-class radial slot bound of `E1_norm_O`), which gives the
  *sum* over `j ≤ 3`, not the individual slots: `integrableOn_slot_of_sum` below extracts the
  individual slots from the sum, the missing measurability being the continuity of the slot on
  `(0,∞)` (from the `C⁴`-regularity of `radA` and the continuity of the weight `w` there).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1_pkg
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1_norm_O
import Submission.Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two inputs of the frozen assembly, in the open class -/

/-- **Block continuity of `E1 α f` on the open class.**  `E1 α f = B(θ)·R(z)` is a separated
product with `B = sin 2θ·Γ'(θ)` of class `C³` on `(0,π/2)` and `R = radA α f` of class `C⁴`
(hence `C³`) on `(0,∞)`; `BlocksCont_mul_factor` gives the blocks of order `≤ 3`, and
`blocksCont_mono` the order `≤ n ≤ 3`. -/
theorem E1_blocks_open_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    ((Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hsm hmem5).1).of_le
      (by norm_num)
  have hb : ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo α
  have h3 : Work.FTS.CoercivityFix.Assembly.BlocksCont 3
      (fun z θ : ℝ => (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
        * Work.FTS.CoercivityFix.Transfer.radA α f z) :=
    Work.FTS.CoercivityFix.Transfer.BlocksCont_mul_factor _ _ hb hR
  exact Work.FTS.CoercivityFix.Transfer.blocksCont_mono hn h3

/-- **The level-three radial slot sum of `radA α f` is integrable** on `Iz` for the open class:
`EpsE4Thr.radA_slotSum_le` at `n = 3`. -/
private theorem radA_slot_sum_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) :
    IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range 4,
      (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
  (Work.FTS.StrongEps.EpsE4Thr.radA_slotSum_le.choose_spec.2 α hα hα1 f hf 3 (by norm_num)).1

/-- **A single radial slot is integrable, given the integrability of the slot sum.**  The
summand `(D_z^j A)²w²` is nonnegative and bounded by the (integrable) sum; its a.e. strong
measurability on `Iz` comes from its continuity on `(0,∞)`, i.e. from the continuity of the
`Zop`-iterate `Zop^[j] A = D_z^j A` (`DzdIter_eq_Zop_iter`) and of the weight `w`, the endpoint
`z = 0` being a null set. -/
private theorem integrableOn_slot_of_sum {A : ℝ → ℝ}
    (hA : ContDiffOn ℝ 4 A (Set.Ioi (0 : ℝ)))
    (hsum : IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range 4,
      (Work.Elliptic.DzdIter c A z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    {j : ℕ} (hj : j ≤ 3) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.DzdIter j A z) ^ 2
      * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hsum ?_ ?_
  · -- continuity on `(0,∞)`, hence a.e. strong measurability on `Iz = [0,∞)`
    have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
      have hEq : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
      rw [hEq]
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    have hZ : ContinuousOn (Work.Spaces.Zop^[j] A) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
        (b := j) (n := 0) (by
          have h4 : ((j : ℕ) : WithTop ℕ∞) ≤ 4 := by
            exact_mod_cast (show j ≤ 4 by omega)
          simpa using hA.of_le h4)
    have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter j A z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => (Work.Spaces.Zop^[j] A z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      funext z
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    rw [hfun, Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact ((hZ.pow 2).mul (hw.pow 2)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    have hnn : 0 ≤ (Work.Elliptic.DzdIter j A z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact Finset.single_le_sum
      (f := fun c => (Work.Elliptic.DzdIter c A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun c _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_range.mpr (by omega))

/-! ## The target -/

/-- **`E1 α f ∈ ℋⁿ` for `f` in the open coercivity class.**  This is the `SmoothOpen`-twin of
`E1Parts.HkMem_E1_of`: the angular majorant `Γ²sin(2θ)^{-η} + Γ²sin(2θ)^{-γ}` (`AngGam`) is
integrable and the radial majorant is the level-three slot sum of `radA α f`, whose
integrability is `radA_slotSum_le` (open class); the individual slots are extracted from that
sum by `integrableOn_slot_of_sum`. -/
theorem HkMem_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.1.2.1
  have hrad4 : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f)
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four hα hα1 hsm hmem5).1
  have hblocks := E1_blocks_open_O α hα hα1 n hn hf
  have hsum := radA_slot_sum_integrable hα hα1 hf
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.HkMem_E1_of α hα hα1 n hn hblocks
    (fun j hj => integrableOn_slot_of_sum hrad4 hsum hj)

end Work.FTS.StrongEps.EpsE4Thr.TransO
