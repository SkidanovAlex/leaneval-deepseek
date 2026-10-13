import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_interval_le_tail
import Submission.Work.FTS.PhiStar.Honesty.rgA_integral_add_adjacent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

/-! ### Auxiliary lemmas -/
private lemma setIntegral_Ioc_eq_interval {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Set.Ioc a b, f t = g t) :
    (∫ t in Set.Ioc a b, f t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h

/-- `(x + y)² ≤ 2x² + 2y²`. -/
private lemma sq_add_le_two {x y : ℝ} : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- `(t^{a/2})² = t^a` for `t > 0`. -/
private lemma rpow_half_sq {t : ℝ} (ht : 0 < t) {a : ℝ} :
    (t ^ (a / 2)) ^ 2 = t ^ a := by
  rw [sq, ← Real.rpow_add ht]
  congr 1
  ring


/-- **Pointwise bound for the decaying Green branch in the far field.**

With `q = rgQ α m ≥ 28`, `rgG1 α m c z = z^{-q} ∫_0^z c t t^{q-1} dt` and
`rgA α m c z = ∫_0^z c t t^{q-1} dt = ∫_0^1 rgF1 + ∫_1^z rgF1`, Cauchy–Schwarz on `(1,z]`
gives `(∫_1^z rgF1)² ≤ (∫_1^z (c t)² t^{q-1})(∫_1^z t^{q-1}) ≤ z^q ∫_1^z (c t)² t^{q-1}`,
and `(x + y)² ≤ 2x² + 2y²` then yields the pointwise bound. -/
theorem rgG1_pt_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t) ^ 2
              * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))
          + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
  obtain ⟨_, hF1_1z, -⟩ := rgHonest_aemeas hα hα4 hm hc hnear hfar
  have hq28 : 28 ≤ Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  have hq1 : (1 : ℝ) < Work.FTS.EllExist.rgQ α m := by linarith
  have hqm1 : 0 < Work.FTS.EllExist.rgQ α m - 1 := by linarith
  have hqm1le : 0 ≤ Work.FTS.EllExist.rgQ α m - 1 := le_of_lt hqm1
  have h2qm1 : 0 < 2 * Work.FTS.EllExist.rgQ α m - 1 := by linarith
  -- abbreviations
  set A0 : ℝ := ∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t with hA0
  set J : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t with hJ
  set KK : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1) with hKK
  -- ### the splitting of the forward primitive
  have hsplit : ∀ z : ℝ, 1 ≤ z → Work.FTS.EllExist.rgA α m c z = A0 + J z := by
    intro z hz
    have h := rgA_integral_add_adjacent hα hα4 hm hc hnear hfar z hz
    simpa [hA0, hJ] using h
  -- ### integrability of `t^(q-1)` and of `(c t)^2 t^(q-1)` on `(1,z]`
  have hLint_Ioc : ∀ z : ℝ, 1 ≤ z →
      IntegrableOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioc (1 : ℝ) z) := by
    intro z hz
    have hcont : ContinuousOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Icc (1 : ℝ) z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hkIoc : ∀ z : ℝ, 1 ≤ z →
      IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioc (1 : ℝ) z) := by
    intro z hz
    have h1 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc (1 : ℝ) z) :=
      hfar.mono_set (fun t ht => ht.1)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) z)),
        ‖t ^ (Work.FTS.EllExist.rgQ α m - 1)‖ ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      exact Real.rpow_le_rpow ht0.le ht.2 hqm1le
    have haesm : AEStronglyMeasurable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1))
        (volume.restrict (Set.Ioc (1 : ℝ) z)) :=
      (measurable_id.pow_const (Work.FTS.EllExist.rgQ α m - 1)).aestronglyMeasurable
    have hb1 : Integrable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1) * (c t) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) :=
      Integrable.bdd_mul h1 haesm hbdd
    exact hb1.congr (ae_of_all _ (fun t => mul_comm (t ^ (Work.FTS.EllExist.rgQ α m - 1)) ((c t) ^ 2)))
  -- ### nonnegativity of `KK`
  have hKKnn : ∀ z : ℝ, 1 ≤ z → 0 ≤ KK z := by
    intro z hz
    simp only [hKK]
    exact intervalIntegral.integral_nonneg hz
      (fun t ht => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one ht.1) _))
  -- ### Cauchy-Schwarz for `J`
  have hCS : ∀ z : ℝ, 1 ≤ z → (J z) ^ 2 ≤ KK z * (∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hf2 : Integrable (fun t : ℝ => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hkIoc z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [mul_pow, rpow_half_sq ht0]
    have hg2 : Integrable (fun t : ℝ => (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hLint_Ioc z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [rpow_half_sq ht0]
    have hfg : Integrable (fun t : ℝ => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2))
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hF1_1z z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      simp only [Work.FTS.EllExist.rgF1]
      rw [mul_assoc, ← Real.rpow_add ht0,
        show (Work.FTS.EllExist.rgQ α m - 1) / 2 + (Work.FTS.EllExist.rgQ α m - 1) / 2 = Work.FTS.EllExist.rgQ α m - 1 from by ring]
    have hcs := CSTools.sq_integral_mul_le (μ := volume.restrict (Set.Ioc (1 : ℝ) z)) hf2 hg2 hfg
    have e1 : (∫ t, (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)
          ∂(volume.restrict (Set.Ioc (1 : ℝ) z))) = J z := by
      rw [setIntegral_Ioc_eq_interval hz
        (f := fun t => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2))
        (g := Work.FTS.EllExist.rgF1 α m c) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          simp only [Work.FTS.EllExist.rgF1]
          rw [mul_assoc, ← Real.rpow_add ht0,
            show (Work.FTS.EllExist.rgQ α m - 1) / 2 + (Work.FTS.EllExist.rgQ α m - 1) / 2 = Work.FTS.EllExist.rgQ α m - 1 from by ring])]
    have e2 : (∫ t, (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2
          ∂(volume.restrict (Set.Ioc (1 : ℝ) z))) = KK z := by
      rw [setIntegral_Ioc_eq_interval hz (f := fun t => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (g := fun t => (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          rw [mul_pow, rpow_half_sq ht0])]
    have e3 : (∫ t, (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2 ∂(volume.restrict (Set.Ioc (1 : ℝ) z)))
        = ∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      rw [setIntegral_Ioc_eq_interval hz (f := fun t => (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (g := fun t => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          rw [rpow_half_sq ht0])]
    rw [e1, e2, e3] at hcs
    exact hcs
  -- ### the bound `∫_1^z t^{q-1} ≤ z^q`
  have hLz : ∀ z : ℝ, 1 ≤ z → (∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1)) ≤ z ^ Work.FTS.EllExist.rgQ α m := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hcont : ContinuousOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Icc (1 : ℝ) z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
    have hi1 : IntervalIntegrable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume (1 : ℝ) z :=
      hcont.intervalIntegrable_of_Icc hz
    have hi2 : IntervalIntegrable (fun _ : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1)) volume (1 : ℝ) z :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hz hi1 hi2
      (fun t ht => Real.rpow_le_rpow (le_trans zero_le_one ht.1) ht.2 hqm1le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hzq : (z - 1) * z ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z ^ Work.FTS.EllExist.rgQ α m := by
      have h1 : (z - 1) * z ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hz0.le _)
      have h2 : z * z ^ (Work.FTS.EllExist.rgQ α m - 1) = z ^ Work.FTS.EllExist.rgQ α m := by
        calc z * z ^ (Work.FTS.EllExist.rgQ α m - 1) = z ^ (1 : ℝ) * z ^ (Work.FTS.EllExist.rgQ α m - 1) := by rw [Real.rpow_one]
          _ = z ^ ((1 : ℝ) + (Work.FTS.EllExist.rgQ α m - 1)) := (Real.rpow_add hz0 1 (Work.FTS.EllExist.rgQ α m - 1)).symm
          _ = z ^ Work.FTS.EllExist.rgQ α m := by
                rw [show (1 : ℝ) + (Work.FTS.EllExist.rgQ α m - 1) = Work.FTS.EllExist.rgQ α m from by ring]
      linarith [h1, h2.le]
    linarith [hmono, hzq]
  -- ### the pointwise bound
  have hpt : ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hz1 : 1 ≤ z := le_of_lt hz
    have hG : (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (Work.FTS.EllExist.rgA α m c z) ^ 2 := by
      simp only [Work.FTS.EllExist.rgG1, mul_pow]
      rw [show (z ^ (-(Work.FTS.EllExist.rgQ α m))) ^ 2 = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) from by
            rw [sq, ← Real.rpow_add hz0]
            congr 1
            ring]
    have h1 : (Work.FTS.EllExist.rgA α m c z) ^ 2 ≤ 2 * A0 ^ 2 + 2 * (J z) ^ 2 := by
      rw [hsplit z hz1]
      exact sq_add_le_two
    have hExp : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * z ^ Work.FTS.EllExist.rgQ α m = z ^ (-(Work.FTS.EllExist.rgQ α m)) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have h3 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2 ≤ z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
      have h4 : (J z) ^ 2 ≤ KK z * z ^ Work.FTS.EllExist.rgQ α m :=
        le_trans (hCS z hz1) (mul_le_mul_of_nonneg_left (hLz z hz1) (hKKnn z hz1))
      have h5 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2 ≤ z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (KK z * z ^ Work.FTS.EllExist.rgQ α m) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hz0.le _)
      have h6 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (KK z * z ^ Work.FTS.EllExist.rgQ α m) = z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
        rw [mul_comm (KK z) (z ^ Work.FTS.EllExist.rgQ α m), ← mul_assoc, hExp]
      linarith [h5, h6.le]
    calc (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (Work.FTS.EllExist.rgA α m c z) ^ 2 := hG
      _ ≤ z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (2 * A0 ^ 2 + 2 * (J z) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hz0.le _)
      _ = 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * (z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2) := by ring
      _ ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z) := by linarith [h3]
      _ = 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by ring
  simpa [hA0, hJ, hKK] using hpt

end Work.FTS.PhiStar.Honesty
