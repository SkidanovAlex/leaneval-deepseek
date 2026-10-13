/-
# `Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound`

Near `z = 0` the mode-`m` radial Euler Green function
`Work.FTS.PhiStar.Radial.radGreen α m c` and its `z`-derivative obey a *pointwise* power bound
with the same exponent `d = min pc (2m/α) > 3/2` (where `|c t| ≤ Kc t^{pc}` near `0` is the
hypothesis on the source `c`).

`radGreen α m c z = rgK (z^{-q} rgA z + z^{p} rgB z)` with `q = (2m+5)/α`, `p = 2m/α`, so the two
indicial branches are `rgG1 = z^{-q} rgA` and `rgG2 = z^{p} rgB`.  The three ingredients are

* `rgG1_near_bound` : `|rgG1 z| ≤ Kc z^{pc}/(pc+q)`,
* `rgG2_near_bound` : `|rgG2 z| ≤ (∫_0^∞ ‖rgF2‖) z^{p}` (using `h0'`/`hinf` to make the tail
  integral finite),
* `radGreen_deriv1_form` : `z ∂_z radGreen = rgK (p·rgG2 − q·rgG1)`,

which together with `min pc p > 3/2` give the stated bound for `B = max (rgK (c1 + Cf))
(rgK (p Cf + q c1))` (`c1 = Kc/(pc+q)`, `Cf = ∫_0^∞ ‖rgF2‖`).  This is the pointwise form of the
estimate proved (as a limit statement) in `Submission/Work/FTS/ClassC/radGreen_near_limits.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.ClassC.rgG1_near_bound
import Submission.Work.FTS.ClassC.rgG2_near_bound
import Submission.Work.FTS.ClassC.radGreen_deriv1_form
import Submission.Work.FTS.ClassC.radGreen_near_limits
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.EllExist
open Work.FTS.ClassC

namespace Work.FTS.ClassC.HonestCut

theorem radGreen_near_pointwise_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∃ B d : ℝ, 0 ≤ B ∧ 3 / 2 < d ∧ ∀ z : ℝ, 0 < z → z ≤ 1 →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ B * z ^ d
      ∧ |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z| ≤ B * z ^ d := by
  obtain ⟨Kc, pc, hKc, hpc32, hvy⟩ := hvy
  have hpc : 0 < pc := by linarith
  have hqpos : 0 < rgQ α m := rgQ_pos hα m
  have hKpos : 0 < rgK α m := rgK_pos hα m
  have hppos : 0 < rgP α m := rgP_pos hα hm
  have hpnn : 0 ≤ rgP α m := hppos.le
  -- integrability of the tail kernel on all of `(0,∞)`, from `(0,1)` and `(1,∞)`
  have h2 : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) := by
    have hnear : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioo 0 1) := h0'
    have hfar : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 1) := hinf
    have hsing : MeasureTheory.IntegrableOn (rgF2 α m c) ({1} : Set ℝ) :=
      MeasureTheory.integrableOn_singleton (f := rgF2 α m c) (x := 1)
        (by finiteness) (by rw [measure_singleton]; exact ENNReal.zero_lt_top)
    have hIoc : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1) := by
      rw [← Set.Ioo_union_right (show (0 : ℝ) < 1 by norm_num)]
      exact hnear.union hsing
    have h := hIoc.union hfar
    rwa [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 from by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · linarith
      · intro hx
        by_cases h : x ≤ 1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (lt_of_not_ge h)] at h
  -- the three constants of the estimate
  set Cf : ℝ := ∫ t in Set.Ioi 0, ‖rgF2 α m c t‖ with hCfdef
  set c1 : ℝ := Kc / (pc + rgQ α m) with hc1def
  set d : ℝ := min pc (rgP α m) with hddef
  set A : ℝ := rgK α m * (rgP α m * Cf + rgQ α m * c1) with hAdef
  set B0 : ℝ := rgK α m * (c1 + Cf) with hB0def
  have hc1nn : 0 ≤ c1 := by
    rw [hc1def]
    exact div_nonneg hKc.le (add_nonneg hpc.le hqpos.le)
  have hCfnn : 0 ≤ Cf := by
    rw [hCfdef]
    exact integral_nonneg fun t => norm_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hKpos.le (add_nonneg (mul_nonneg hpnn hCfnn) (mul_nonneg hqpos.le hc1nn))
  have hB0nn : 0 ≤ B0 := by
    rw [hB0def]
    exact mul_nonneg hKpos.le (add_nonneg hc1nn hCfnn)
  have hd32 : (3 : ℝ) / 2 < d := by
    rw [hddef]
    exact lt_min hpc32 (by linarith [rgP_ge hα hα4 hm])
  have hdpc : d ≤ pc := by rw [hddef]; exact min_le_left _ _
  have hdp : d ≤ rgP α m := by rw [hddef]; exact min_le_right _ _
  -- the two branch bounds
  have hbd1 : ∀ z : ℝ, 0 < z → z ≤ 1 →
      |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) :=
    rgG1_near_bound hα hKc hpc hvy
  have hbd2 : ∀ z : ℝ, 0 < z →
      |rgG2 α m c z| ≤ (∫ t in Set.Ioi 0, ‖rgF2 α m c t‖) * z ^ (rgP α m) :=
    rgG2_near_bound h2
  have hG1 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG1 α m c z| ≤ c1 * z ^ d := by
    intro z hz0 hz1
    have hpcδ : z ^ pc ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdpc
    calc |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) := hbd1 z hz0 hz1
      _ = c1 * z ^ pc := by rw [hc1def]; ring_nf
      _ ≤ c1 * z ^ d := mul_le_mul_of_nonneg_left hpcδ hc1nn
  have hG2 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG2 α m c z| ≤ Cf * z ^ d := by
    intro z hz0 hz1
    have hpδ : z ^ (rgP α m) ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdp
    have h1 : |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := by
      have hp := hbd2 z hz0
      rwa [← hCfdef] at hp
    calc |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := h1
      _ ≤ Cf * z ^ d := mul_le_mul_of_nonneg_left hpδ hCfnn
  -- `radGreen` is `rgK (g₁ + g₂)` and hence `O(z^d)`
  have hgeq : ∀ z : ℝ, radGreen α m c z = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
    intro z
    rw [radGreen_eq]
    simp only [rgG1, rgG2]
  have hG : ∀ z : ℝ, 0 < z → z ≤ 1 → ‖radGreen α m c z‖ ≤ B0 * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    rw [Real.norm_eq_abs, hgeq z, abs_mul, abs_of_pos hKpos]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
      _ ≤ rgK α m * (c1 * z ^ d + Cf * z ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2') hKpos.le
      _ = B0 * z ^ d := by rw [hB0def]; ring
  -- and the combination `rgK (p g₂ - q g₁)` occurring in the derivative is `O(z^d)` too
  have hT : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)‖ ≤ A * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    have h2n : ‖rgG2 α m c z‖ ≤ Cf * z ^ d := by rw [Real.norm_eq_abs]; exact h2'
    have h1n : ‖rgG1 α m c z‖ ≤ c1 * z ^ d := by rw [Real.norm_eq_abs]; exact h1
    rw [norm_mul, Real.norm_of_nonneg hKpos.le]
    calc rgK α m * ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
        ≤ rgK α m * (rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d)) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          calc ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
              = ‖rgP α m * rgG2 α m c z + -(rgQ α m * rgG1 α m c z)‖ := by
                rw [sub_eq_add_neg]
            _ ≤ ‖rgP α m * rgG2 α m c z‖ + ‖-(rgQ α m * rgG1 α m c z)‖ := norm_add_le _ _
            _ = rgP α m * ‖rgG2 α m c z‖ + rgQ α m * ‖rgG1 α m c z‖ := by
                simp only [norm_neg, norm_mul, Real.norm_of_nonneg hpnn,
                  Real.norm_of_nonneg hqpos.le]
            _ ≤ rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d) :=
                add_le_add (mul_le_mul_of_nonneg_left h2n hpnn)
                  (mul_le_mul_of_nonneg_left h1n hqpos.le)
      _ = A * z ^ d := by rw [hAdef]; ring
  refine ⟨max B0 A, d, le_trans hB0nn (le_max_left B0 A), hd32, ?_⟩
  intro z hz0 hz1
  have hzpd : (0 : ℝ) ≤ z ^ d := Real.rpow_nonneg hz0.le d
  constructor
  · have h := hG z hz0 hz1
    rw [Real.norm_eq_abs] at h
    calc |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ B0 * z ^ d := h
      _ ≤ max B0 A * z ^ d := mul_le_mul_of_nonneg_right (le_max_left B0 A) hzpd
  · have h := hT z hz0 hz1
    rw [Real.norm_eq_abs] at h
    have hd1 := radGreen_deriv1_form hα m hcont h0 hinf z hz0
    calc |z * deriv (fun z' => Work.FTS.PhiStar.Radial.radGreen α m c z') z|
        = |z * deriv (radGreen α m c) z| := by rfl
      _ = |rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)| := by rw [hd1]
      _ ≤ A * z ^ d := h
      _ ≤ max B0 A * z ^ d := mul_le_mul_of_nonneg_right (le_max_right B0 A) hzpd

end Work.FTS.ClassC.HonestCut
