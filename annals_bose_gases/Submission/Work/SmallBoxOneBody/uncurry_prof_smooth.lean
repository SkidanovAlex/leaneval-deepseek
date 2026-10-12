import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Work.SmallBoxOneBody.ProfDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxOneBody

open Filter
open scoped Topology ContDiff

theorem uncurry_prof_smooth :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) =>
        Work.SmallBoxOneBody.Prof ((‖y‖ - 1) / (R - 1))))
      (Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  rw [IsOpen.contDiffOn_iff (isOpen_Ioi.prod isOpen_univ)]
  intro p hp
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true] at hp
  have hf : Function.uncurry (fun (R : ℝ) (y : EuclideanSpace ℝ (Fin 3)) =>
        Work.SmallBoxOneBody.Prof ((‖y‖ - 1) / (R - 1)))
      = fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxOneBody.Prof ((‖q.2‖ - 1) / (q.1 - 1)) := rfl
  rw [hf]
  rcases lt_or_ge (‖p.2‖) 1 with hn | hn
  · -- Near a point with `‖y‖ < 1` the argument of `Prof` is strictly negative,
    -- so `Prof` is locally constant equal to `1` and the composition is smooth.
    have h1 : ∀ᶠ q in 𝓝 p, ‖q.2‖ < 1 :=
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds hn
    have h2 : ∀ᶠ q in 𝓝 p, 1 < q.1 :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hp
    have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxOneBody.Prof ((‖q.2‖ - 1) / (q.1 - 1))) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
      filter_upwards [h1, h2] with q hq1 hq2
      exact Work.SmallBoxOneBody.Prof_of_nonpos
        (le_of_lt (div_neg_of_neg_of_pos (by linarith) (by linarith)))
    exact (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq heq
  · -- Away from the origin the norm is smooth, and the denominator `R - 1` does not
    -- vanish, so the whole expression is smooth and `Prof` is globally smooth.
    have h2 : p.2 ≠ 0 := norm_pos_iff.mp (by linarith)
    have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => ‖q.2‖ - 1) p :=
      (ContDiffAt.norm ℝ (ContDiffAt.snd contDiffAt_id) h2).sub contDiffAt_const
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => q.1 - 1) p :=
      (ContDiffAt.fst contDiffAt_id).sub contDiffAt_const
    have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => (‖q.2‖ - 1) / (q.1 - 1)) p :=
      hnum.div hden (sub_ne_zero.mpr (ne_of_gt hp))
    exact (Work.SmallBoxOneBody.Prof_smooth.contDiffAt).comp p hq

end Work.SmallBoxOneBody
