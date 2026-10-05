import Mathlib
import Submission.Work.RPCore.Flow.isCompact_fundamentalDomain
import Submission.Work.RPCore.Flow.fderiv_eq_of_periodic
import Submission.Work.RPCore.Flow.periodic_Tk_int
import Submission.Work.RPCore.Flow.bounded_of_periodic_of_eq_on_slab

/-!
# The derivative of a `2π`-periodic `C¹` function supported in a slab is bounded

If `f : PS → ℝ` is `C¹`, `2π`-periodic in the angle `q₂` (`f ∘ Tk 1 = f`) and vanishes outside the
slab `{|q₁| + |p₁| + |p₂| ≤ R}`, then `‖fderiv ℝ f‖` is globally bounded.

The point is that the derivative inherits all three properties of `f` (continuity from `C¹`,
periodicity from `fderiv_eq_of_periodic`, and vanishing *off the open slab* since `f` is locally `0`
there), so the compactness statement `bounded_of_periodic_of_eq_on_slab` applies to `fderiv ℝ f`
itself (viewed as a function of `(t, x)` which is constant in `t`).
-/

open scoped Topology

namespace Work.RPCore.Flow

/-- The additive form of the angle shift: `x + angleShift = Tk 1 x`. -/
private noncomputable def angleShift : Work.RPV.PS := ((0, 2 * Real.pi), (0, 0))

private theorem add_angleShift_eq_Tk_one (x : Work.RPV.PS) :
    x + angleShift = Work.RPV.Tk 1 x := by
  ext <;> simp [angleShift, Work.RPV.Tk]

theorem fderiv_bounded_of_periodic_on_slab (f : Work.RPV.PS → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : ∀ x, f (Work.RPV.Tk 1 x) = f x) (R : ℝ)
    (hsupp : ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → f x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  -- The additive periodicity of `f` along the angle shift.
  have hshift : ∀ y : Work.RPV.PS, f (y + angleShift) = f y := fun y => by
    rw [add_angleShift_eq_Tk_one]; exact hper y
  -- `fderiv ℝ f` is periodic in the angle.
  have hper' : ∀ z : ℝ × Work.RPV.PS, fderiv ℝ f (Work.RPV.Tk 1 z.2) = fderiv ℝ f z.2 := by
    intro z
    have h := fderiv_eq_of_periodic f hfdiff hshift z.2
    rwa [add_angleShift_eq_Tk_one] at h
  -- `fderiv ℝ f` vanishes off the *open* slab, where `f` is locally zero.
  have hsupp' : ∀ z : ℝ × Work.RPV.PS,
      R < |z.2.1.1| + |z.2.2.1| + |z.2.2.2| → fderiv ℝ f z.2 = 0 := by
    intro z hz
    have hcont : Continuous fun y : Work.RPV.PS => |y.1.1| + |y.2.1| + |y.2.2| := by fun_prop
    have hopen : {y : Work.RPV.PS | R < |y.1.1| + |y.2.1| + |y.2.2|} ∈ 𝓝 z.2 :=
      (isOpen_lt continuous_const hcont).mem_nhds hz
    have hev : f =ᶠ[𝓝 z.2] 0 := by
      filter_upwards [hopen] with y hy
      exact hsupp y hy.le
    rw [hev.fderiv_eq]
    simp
  -- Compactness of the slab in the remaining coordinates kills the angle direction.
  obtain ⟨M, hM0, hM⟩ := bounded_of_periodic_of_eq_on_slab
    (fun z : ℝ × Work.RPV.PS => fderiv ℝ f z.2)
    (hfcont.comp continuous_snd) hper' hsupp' 0
  exact ⟨M, hM0, fun x => hM (0, x) (by simp)⟩

end Work.RPCore.Flow
