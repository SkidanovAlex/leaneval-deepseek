/-
# `Work.FTS.ClassC.radGreen_near_limits`

The local behaviour of the mode-`m` radial Euler Green function
`Work.FTS.PhiStar.Radial.radGreen α m c` near `z = 0`:

  `radGreen α m c z ^ 2 / z ^ 3 → 0`  and  `∂_z radGreen α m c z · radGreen α m c z / z ^ 2 → 0`
  as `z → 0⁺`.

The Green function is the sum of the two indicial branches
`rgG1 = z^{-q} ∫_0^z c t^{q-1}` and `rgG2 = z^{p} ∫_z^∞ c t^{-p-1}` (`q = (2m+5)/α`, `p = 2m/α`).
The hypothesis `hvy` (a power bound `|c t| ≤ K t^{pc}`, `pc > 3/2`, near `0`) bounds the decaying
branch by `O(z^{pc})`, and the integrability hypotheses `h0'`, `hinf` bound the *tail* integral
uniformly, giving `rgG2 = O(z^{p})` with `p = 2m/α ≥ 8`.  Since `min pc p > 3/2`, the Green
function itself is `O(z^{δ})` for some `δ > 3/2`, which gives both limits at once; the derivative
enters through the explicit first-derivative identity `z ∂_z radGreen = rgK (p·rgG2 − q·rgG1)`.

The three ingredients are proved in the sibling modules
`Submission/Work/FTS/ClassC/{rgG1_near_bound, rgG2_near_bound, radGreen_deriv1_form}.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.ClassC.rgG1_near_bound
import Submission.Work.FTS.ClassC.rgG2_near_bound
import Submission.Work.FTS.ClassC.radGreen_deriv1_form

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.EllExist

/-! ### helpers -/

/-- A function bounded by `C · z ^ d` (`d > 0`) on `(0,1)` tends to `0` at `0` within `(0,∞)`. -/
private lemma tendsto_zero_of_bound {F : ℝ → ℝ} {C d : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z ∈ Set.Ioo (0 : ℝ) 1, ‖F z‖ ≤ C * z ^ d) :
    Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Filter.Tendsto (fun z : ℝ => C * z ^ d) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht := (Real.continuousAt_rpow_const 0 d (Or.inr hd.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hd)] at ht
    have ht2 := ht.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    have h3 := ht2.const_mul C
    simpa using h3
  refine squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg (F z)) ?_ hmaj
  have hmemb : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
    rw [show Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 ∩ Set.Iio 1 from by
      ext z
      simp only [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, Set.mem_inter_iff]]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds one_pos)
  exact Filter.mem_of_superset hmemb fun z hz => hb z hz

/-- The tail kernel `rgF2 α m c t = c t · t^{-p-1}` is integrable on all of `(0,∞)` as soon as it
is integrable on `(0,1)` and on `(1,∞)`. -/
private lemma rgF2_integrableOn_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) := by
  have hnear : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioo 0 1) := by
    rw [show rgF2 α m c = fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1) from rfl]
    exact h0'
  have hfar : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 1) := by
    rw [show rgF2 α m c = fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1) from rfl]
    exact hinf
  have hsing : MeasureTheory.IntegrableOn (rgF2 α m c) ({1} : Set ℝ) :=
    MeasureTheory.integrableOn_singleton (f := rgF2 α m c) (x := 1)
      (by finiteness) (by rw [measure_singleton]; exact ENNReal.zero_lt_top)
  have hIoc : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1) := by
    rw [← Set.Ioo_union_right (show (0 : ℝ) < 1 by norm_num)]
    exact hnear.union hsing
  have h' : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1 ∪ Set.Ioi 1) :=
    hIoc.union hfar
  rwa [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 from by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
    · intro hx
      by_cases h' : x ≤ 1
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr (lt_of_not_ge h')] at h'

/-- `(z^d)^2 / z^3 = z^{2d-3}` for `z > 0`. -/
private lemma rpow_sq_div_cube {z d : ℝ} (hz : 0 < z) : (z ^ d) ^ 2 / z ^ 3 = z ^ (2 * d - 3) := by
  rw [← Real.rpow_mul_natCast hz.le d 2, ← Real.rpow_natCast z 3, ← Real.rpow_sub hz]
  congr 1
  push_cast
  ring

/-- `z^d · z^d / z^3 = z^{2d-3}` for `z > 0`. -/
private lemma rpow_mul_self_div_cube {z d : ℝ} (hz : 0 < z) :
    z ^ d * z ^ d / z ^ 3 = z ^ (2 * d - 3) := by
  rw [← Real.rpow_add hz, ← Real.rpow_natCast z 3, ← Real.rpow_sub hz]
  congr 1
  push_cast
  ring

/-! ### the theorem -/

theorem radGreen_near_limits {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z) :
    Filter.Tendsto (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨Kc, pc, hKc, hpc32, hvy⟩ := hvy
  have hqpos : 0 < rgQ α m := rgQ_pos hα m
  have hKpos : 0 < rgK α m := rgK_pos hα m
  have hppos : 0 < rgP α m := rgP_pos hα hm
  have hpnn : 0 ≤ rgP α m := hppos.le
  -- the three constants of the estimate
  set Cf : ℝ := ∫ t in Set.Ioi 0, ‖rgF2 α m c t‖ with hCfdef
  set c1 : ℝ := Kc / (pc + rgQ α m) with hc1def
  set d : ℝ := min pc (rgP α m) with hddef
  set A : ℝ := rgK α m * (rgP α m * Cf + rgQ α m * c1) with hAdef
  set B : ℝ := rgK α m * (c1 + Cf) with hBdef
  have hpc : 0 < pc := by linarith
  have hc1nn : 0 ≤ c1 := by
    rw [hc1def]
    exact div_nonneg hKc.le (add_nonneg hpc.le hqpos.le)
  have hCfnn : 0 ≤ Cf := by
    rw [hCfdef]
    exact integral_nonneg fun t => norm_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hKpos.le (add_nonneg (mul_nonneg hpnn hCfnn) (mul_nonneg hqpos.le hc1nn))
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hKpos.le (add_nonneg hc1nn hCfnn)
  have hdpos : 0 < d := by rw [hddef]; exact lt_min hpc hppos
  have hd32 : (3 : ℝ) / 2 < d := by
    rw [hddef]
    exact lt_min hpc32 (by linarith [rgP_ge hα hα4 hm])
  have hdpc : d ≤ pc := by rw [hddef]; exact min_le_left _ _
  have hdp : d ≤ rgP α m := by rw [hddef]; exact min_le_right _ _
  -- integrability of the tail kernel on all of `(0,∞)`
  have h2 : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) :=
    rgF2_integrableOn_Ioi h0' hinf
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
  have hgeq : ∀ z : ℝ, Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
    intro z
    rw [radGreen_eq]
    simp only [rgG1, rgG2]
  have hG : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ≤ B * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    rw [Real.norm_eq_abs, hgeq z, abs_mul, abs_of_pos hKpos]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
      _ ≤ rgK α m * (c1 * z ^ d + Cf * z ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2') hKpos.le
      _ = B * z ^ d := by rw [hBdef]; ring
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
  -- the explicit first derivative rewrites the second limit into a polynomial expression
  have hder : ∀ z : ℝ, 0 < z →
      deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2
        = (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z))
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 3 := by
    intro z hz0
    have hz0ne : z ≠ 0 := ne_of_gt hz0
    have hmain : z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) :=
      radGreen_deriv1_form hα m hcont h0 hinf z hz0
    have hd : deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) / z := by
      rw [eq_div_iff hz0ne, mul_comm]
      exact hmain
    rw [hd, div_mul_eq_mul_div, div_div, show z * z ^ 2 = z ^ 3 from by ring]
  have hQ : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
        ≤ B ^ 2 * z ^ (2 * d - 3) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hz3 : (0 : ℝ) < z ^ 3 := pow_pos hz0 3
    have hb := hG z hz0 hz1
    have hsq : (z ^ d) ^ 2 / z ^ 3 = z ^ (2 * d - 3) := rpow_sq_div_cube hz0
    calc ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
        = ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ^ 2 / z ^ 3 := by
          rw [norm_div, norm_pow, Real.norm_of_nonneg hz3.le]
      _ ≤ (B * z ^ d) ^ 2 / z ^ 3 := by
          apply div_le_div_of_nonneg_right _ hz3.le
          exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = B ^ 2 * z ^ (2 * d - 3) := by
          rw [mul_pow, mul_div_assoc, hsq]
  have hQ2 : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2‖ ≤ A * B * z ^ (2 * d - 3) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hz3 : (0 : ℝ) < z ^ 3 := pow_pos hz0 3
    have hb := hG z hz0 hz1
    have hTb := hT z hz0 hz1
    rw [hder z hz0]
    calc ‖(rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z))
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 3‖
        = ‖rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)‖
            * ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ / z ^ 3 := by
          rw [norm_div, norm_mul, Real.norm_of_nonneg hz3.le]
      _ ≤ (A * z ^ d) * (B * z ^ d) / z ^ 3 := by
          apply div_le_div_of_nonneg_right _ hz3.le
          exact mul_le_mul hTb hb (norm_nonneg _)
            (mul_nonneg hAnn (Real.rpow_nonneg hz0.le d))
      _ = A * B * z ^ (2 * d - 3) := by
          have h1 : (A * z ^ d) * (B * z ^ d) = A * B * (z ^ d * z ^ d) := by ring
          rw [h1, mul_div_assoc, rpow_mul_self_div_cube hz0]
  exact ⟨tendsto_zero_of_bound (F := fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
      (C := B ^ 2) (d := 2 * d - 3) (by linarith) (sq_nonneg B) hQ,
    tendsto_zero_of_bound (F := fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
      (C := A * B) (d := 2 * d - 3) (by linarith) (mul_nonneg hAnn hBnn) hQ2⟩

end Work.FTS.ClassC
