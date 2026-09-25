import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

open Set
open scoped Topology

namespace Commons.Analysis.Real

/-- The function `x ↦ log (log x)` is concave on `(1, +∞)`.

This follows by composing the concave, increasing function `log` (which is
strictly concave on `(0, +∞)`) with the concave function `log` on `(1, +∞)`:
for concave `g` which is monotone on the image of a concave `f`, the
composition `g ∘ f` is concave. -/
lemma concaveOn_log_log_Ioi :
    ConcaveOn ℝ (Set.Ioi (1 : ℝ)) (fun x => Real.log (Real.log x)) := by
  have hlog : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  -- inner function: `log` is concave on `(1, ∞) ⊆ (0, ∞)`
  have hf : ConcaveOn ℝ (Set.Ioi (1 : ℝ)) Real.log :=
    hlog.subset (by intro x hx; change 1 < x at hx; exact lt_trans zero_lt_one hx)
      (convex_Ioi (1 : ℝ))
  -- outer function: `log` is concave on the image `log '' (1, ∞) = (0, ∞)`
  have hg : ConcaveOn ℝ (Real.log '' Set.Ioi (1 : ℝ)) Real.log := by
    rw [Real.image_log_Ioi (a := (1 : ℝ)) zero_lt_one]
    simpa using hlog
  -- `log` is increasing on its image
  have hg' : MonotoneOn Real.log (Real.log '' Set.Ioi (1 : ℝ)) := by
    rw [Real.image_log_Ioi (a := (1 : ℝ)) zero_lt_one]
    intro x hx y hy hxy
    have hx0 : 0 < x := by simpa using hx
    exact Real.log_le_log hx0 hxy
  simpa only [Function.comp_def] using (ConcaveOn.comp hg hf hg')

/-- The graph of `x ↦ log (log x)` lies above its chord on any interval
`[a, b]` with `1 < a`: concavity of `log ∘ log` on `(1, ∞)`. -/
theorem log_log_chord {a b x : ℝ} (ha : 1 < a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.log (Real.log x) ≥
      ((b - x) / (b - a)) * Real.log (Real.log a) +
        ((x - a) / (b - a)) * Real.log (Real.log b) := by
  let f : ℝ → ℝ := fun y => Real.log (Real.log y)
  have hcc : ConcaveOn ℝ (Set.Icc a b) f := by
    refine (concaveOn_log_log_Ioi.subset ?hst (convex_Icc a b))
    intro y hy
    exact lt_of_lt_of_le ha hy.1
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hba : b - a ≠ 0 := by linarith
  have hwa : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hxb) (sub_pos.mpr hab).le
  have hwb : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hax) (sub_pos.mpr hab).le
  have hwsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [hba]
    ring
  have hxeq : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp [hba]
    ring
  have hineq := hcc.2 ha_mem hb_mem hwa hwb hwsum
  -- concavity:  w_a • f a + w_b • f b ≤ f (w_a • a + w_b • b)
  simp only [smul_eq_mul] at hineq
  rw [hxeq] at hineq
  simpa [f] using hineq

end Commons.Analysis.Real