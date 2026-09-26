import Mathlib
import Submission.Work.Drive.EpsForm.Defs
import Submission.Work.BoxShrink.Core.Counting.Sphere

/-!
# The sphere count as an `encard` bound

The sweep of `Work.BoxSweep.sweep` counts the *parameters* `t ∈ [0, 2π)` at which the knot meets
the boundary sphere `∂PBox s c σ`.  The count is consumed downstream as a bound on the number of
*points* of `range K.curve ∩ sphereSet c σ s`, which is what `Pardon`'s Lemma 4.2 speaks about.

The two differ only by the parametrization: the curve `K.curve` is `2π`-periodic, so its range is
the image of the fundamental interval `[0, 2π)`, and the cardinality of an image is at most the
cardinality of the source.  This file records that elementary passage, together with the
arithmetic `10(1+ε)/ε · d ≤ countConst · d` which turns Pardon's hypothesis `countConst · d <
min p q` into the strict bound on the count.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.EpsForm

/-- A `2π`-periodic curve attains every one of its values in the fundamental interval `[0, 2π)`:
the range of a knot is the image of that interval. -/
lemma range_knot_eq_image_Ico (K : Knot) :
    Set.range K.curve = K.curve '' Set.Ico 0 (2 * Real.pi) := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro y ⟨t, rfl⟩
  obtain ⟨k, hk, -⟩ :=
    existsUnique_sub_zsmul_mem_Ico (a := 2 * Real.pi) (by positivity) t 0
  refine ⟨t - k • (2 * Real.pi), by simpa using hk, ?_⟩
  conv_rhs => rw [← sub_add_cancel t (k • (2 * Real.pi))]
  exact (Function.Periodic.zsmul K.periodic k (t - k • (2 * Real.pi))).symm

/-- The number of points of `range K.curve` lying on the sphere `∂PBox s c σ` is at most the
number of parameters `t ∈ [0, 2π)` at which the curve meets the sphere. -/
lemma encard_range_inter_sphereSet_le_encard_param (K : Knot) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} := by
  have hS : Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s =
      K.curve '' (Set.Ico 0 (2 * Real.pi) ∩ K.curve ⁻¹'
        (Work.BoxShrink.Core.sphereSet c σ s)) := by
    rw [range_knot_eq_image_Ico K]
    ext y
    constructor
    · rintro ⟨⟨t, ht, hy⟩, hyT⟩
      exact ⟨t, ⟨ht, by simpa [hy] using hyT⟩, hy⟩
    · rintro ⟨t, ⟨ht, hyT⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hyT⟩
  have hT : (Set.Ico 0 (2 * Real.pi) ∩ K.curve ⁻¹'
        (Work.BoxShrink.Core.sphereSet c σ s)) =
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} := by
    ext t
    simp [Work.BoxShrink.Core.mem_sphereSet]
  rw [hS, hT]
  exact Set.encard_image_le K.curve _

theorem encard_inter_sphereSet_lt_min
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) <
      (Nat.min p q : ℕ∞) := by
  refine lt_of_le_of_lt (encard_range_inter_sphereSet_le_encard_param K c σ s) ?_
  exact Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q)
    (ne_of_gt (lt_min hp hq)) hcount
    (Work.BoxShrink.Core.ten_coeff_mul_lt_min hp hq hd hsmall)

end Work.Drive.EpsForm
