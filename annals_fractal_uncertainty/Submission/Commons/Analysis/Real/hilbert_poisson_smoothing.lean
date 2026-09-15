import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.MeasureTheory.Integral.integral_poisson_kernel
import Submission.Commons.Analysis.Real.integral_poisson_hilbert_kernel

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

namespace Commons.Analysis.Real


theorem integral_abs_sub_div_le_of_lipschitz {g : ℝ → ℝ} {L : NNReal}
    (hL : LipschitzWith L g) (hg : Integrable g) (y : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), |g (y + t) - g (y - t)| / t ≤ 2 * (L : ℝ) + 2 * ∫ x, |g x| := by
  set f : ℝ → ℝ := fun t => |g (y + t) - g (y - t)| / t with hfdef
  have h2L : (0:ℝ) ≤ 2 * (L:ℝ) := by positivity
  have hgm : Measurable g := hL.continuous.measurable
  have hf_meas : Measurable f := by
    rw [hfdef]
    have h1 : Measurable (fun t : ℝ => g (y + t)) :=
      hgm.comp (measurable_const.add measurable_id)
    have h2 : Measurable (fun t : ℝ => g (y - t)) :=
      hgm.comp (measurable_const.sub measurable_id)
    exact (h1.sub h2).abs.div measurable_id
  have hle1 : ∀ t ∈ Set.Ioc (0:ℝ) 1, f t ≤ 2 * (L:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    rw [hfdef]
    have h := hL.dist_le_mul (y + t) (y - t)
    rw [Real.dist_eq, Real.dist_eq] at h
    have hsub : (y + t) - (y - t) = 2 * t := by ring
    rw [hsub] at h
    rw [abs_of_pos (by linarith : (0:ℝ) < 2 * t)] at h
    rw [div_le_iff₀ ht0]
    calc |g (y + t) - g (y - t)| ≤ (L : ℝ) * (2 * t) := h
      _ = 2 * (L:ℝ) * t := by ring
  have hInt1 : IntegrableOn f (Set.Ioc (0:ℝ) 1) volume := by
    refine IntegrableOn.of_bound (by rw [Real.volume_Ioc]; norm_num) hf_meas.aestronglyMeasurable.restrict (2 * (L:ℝ)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hle1 t ht
    · rw [hfdef]; exact div_nonneg (abs_nonneg _) (le_of_lt ht.1)
  have hA_int : Integrable (fun t : ℝ => |g (y + t)| + |g (y - t)|) volume :=
    (hg.abs.comp_add_left y).add (hg.abs.comp_sub_left y)
  have hInt2 : IntegrableOn f (Set.Ioi (1:ℝ)) volume := by
    refine Integrable.mono' hA_int.restrict hf_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht1
    rw [hfdef, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (le_of_lt ht0))]
    rw [div_le_iff₀ ht0]
    refine le_trans (abs_sub _ _) ?_
    exact le_mul_of_one_le_right (by positivity) (le_of_lt ht1)
  have hsplit : (∫ t in Set.Ioi (0:ℝ), f t)
      = (∫ t in Set.Ioc (0:ℝ) 1, f t) + (∫ t in Set.Ioi (1:ℝ), f t) := by
    have hU : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
      ext t; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h,_⟩ | h) <;> linarith
      · intro h
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
    have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
      rw [Set.disjoint_left]; intro t ht1 ht2; exact absurd ht1.2 (not_le.mpr ht2)
    rw [← hU]
    exact setIntegral_union hdisj measurableSet_Ioi hInt1 hInt2
  have hbound1 : (∫ t in Set.Ioc (0:ℝ) 1, f t) ≤ 2 * (L:ℝ) := by
    have hg0 : IntegrableOn (fun _ : ℝ => 2 * (L:ℝ)) (Set.Ioc (0:ℝ) 1) volume :=
      IntegrableOn.of_bound (by rw [Real.volume_Ioc]; norm_num) aestronglyMeasurable_const (2 * (L:ℝ))
        (ae_of_all _ (fun _ => by rw [Real.norm_of_nonneg h2L]))
    have h := setIntegral_mono_on hInt1 hg0 measurableSet_Ioc hle1
    have hc : (∫ t in Set.Ioc (0:ℝ) 1, (2 * (L:ℝ))) = 2 * (L:ℝ) := by
      rw [setIntegral_const]; simp
    rw [hc] at h
    exact h
  have hbound2 : (∫ t in Set.Ioi (1:ℝ), f t) ≤ 2 * ∫ x, |g x| := by
    have h1 : (∫ t in Set.Ioi (1:ℝ), f t)
        ≤ ∫ t in Set.Ioi (1:ℝ), (|g (y + t)| + |g (y - t)|) := by
      refine setIntegral_mono_on hInt2 hA_int.restrict measurableSet_Ioi ?_
      intro t ht
      have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht1
      rw [hfdef, div_le_iff₀ ht0]
      refine le_trans (abs_sub _ _) ?_
      exact le_mul_of_one_le_right (by positivity) (le_of_lt ht1)
    have h2 : (∫ t in Set.Ioi (1:ℝ), (|g (y + t)| + |g (y - t)|))
        ≤ ∫ t : ℝ, (|g (y + t)| + |g (y - t)|) := by
      have key : (∫ t in Set.Ioi (1:ℝ), (|g (y + t)| + |g (y - t)|))
          ≤ ∫ t in Set.univ, (|g (y + t)| + |g (y - t)|) :=
        setIntegral_mono_set hA_int.integrableOn
          (ae_of_all _ (fun t => by positivity))
          (ae_of_all _ (fun _ _ => trivial))
      simpa only [setIntegral_univ] using key
    have e1 : (∫ a : ℝ, |g (y + a)|) = ∫ x : ℝ, |g x| :=
      integral_add_left_eq_self (fun x : ℝ => |g x|) y
    have e2 : (∫ a : ℝ, |g (y - a)|) = ∫ x : ℝ, |g x| :=
      integral_sub_left_eq_self (fun x : ℝ => |g x|) volume y
    have h3 : ∫ t : ℝ, (|g (y + t)| + |g (y - t)|) = 2 * ∫ x, |g x| := by
      rw [integral_add (hg.abs.comp_add_left y) (hg.abs.comp_sub_left y), e1, e2]
      ring
    linarith [h1, h2, h3.le]
  calc (∫ t in Set.Ioi (0:ℝ), f t)
      = (∫ t in Set.Ioc (0:ℝ) 1, f t) + (∫ t in Set.Ioi (1:ℝ), f t) := hsplit
    _ ≤ 2 * (L:ℝ) + 2 * ∫ x, |g x| := add_le_add hbound1 hbound2

theorem poissonKernel_lipschitz {s : ℝ} (hs : 0 < s) :
    ∀ a b : ℝ, |s / (Real.pi * (s ^ 2 + a ^ 2)) - s / (Real.pi * (s ^ 2 + b ^ 2))|
      ≤ (1 / (Real.pi * s ^ 2)) * |a - b| := by
  intro a b
  have hDa : (0:ℝ) < s^2 + a^2 := by positivity
  have hDb : (0:ℝ) < s^2 + b^2 := by positivity
  have hD : (0:ℝ) < (s^2+a^2)*(s^2+b^2) := mul_pos hDa hDb
  have hkey : s^3 * |a + b| ≤ (s^2+a^2)*(s^2+b^2) := by
    have h1 := abs_add_le a b
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ s^3)
    have ha := sq_abs a
    have hb := sq_abs b
    nlinarith [h3, ha, hb, sq_nonneg (|a| - s/2), sq_nonneg (|b| - s/2),
      sq_nonneg (|a| * |b|), sq_nonneg a, sq_nonneg b, sq_nonneg s]
  have hdiff : s / (Real.pi * (s ^ 2 + a ^ 2)) - s / (Real.pi * (s ^ 2 + b ^ 2))
      = (s / Real.pi) * ((b - a) * (b + a) / ((s^2+a^2)*(s^2+b^2))) := by
    field_simp
    ring
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < s / Real.pi),
      abs_div, abs_of_pos hD, abs_mul, abs_sub_comm b a, add_comm b a]
  have hbnd : |a + b| ≤ (s^2+a^2)*(s^2+b^2) / s^3 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < s^3)]
    calc |a+b| * s^3 = s^3 * |a+b| := by ring
      _ ≤ (s^2+a^2)*(s^2+b^2) := hkey
  have hstep : (s/Real.pi) * (|a-b| * |a+b| / ((s^2+a^2)*(s^2+b^2)))
      ≤ (s/Real.pi) * (|a-b| * (((s^2+a^2)*(s^2+b^2))/s^3) / ((s^2+a^2)*(s^2+b^2))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (le_of_lt hD)
    exact mul_le_mul_of_nonneg_left hbnd (abs_nonneg _)
  refine le_trans hstep ?_
  rw [show (s/Real.pi) * (|a-b| * (((s^2+a^2)*(s^2+b^2))/s^3) / ((s^2+a^2)*(s^2+b^2)))
        = (1/(Real.pi*s^2)) * |a-b| from by field_simp]

theorem integral_abs_poisson_diff_div_le {s u : ℝ} (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ),
        |s / (Real.pi * (s ^ 2 + (u - t) ^ 2)) - s / (Real.pi * (s ^ 2 + (u + t) ^ 2))| / t
      ≤ 2 / (Real.pi * s ^ 2) + 2 := by
  set Q : ℝ → ℝ := fun v => s / (Real.pi * (s^2 + v^2)) with hQdef
  have hQlip := poissonKernel_lipschitz hs
  have hQnn : ∀ v, 0 ≤ Q v := by intro v; rw [hQdef]; positivity
  have hbase : Integrable (fun x : ℝ => (1 + (x * s⁻¹) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero (ne_of_gt hs))
  have hbound : Integrable (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹) := by
    have heq : (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹)
        = fun x : ℝ => (s ^ 2)⁻¹ * (1 + (x * s⁻¹) ^ 2)⁻¹ := by
      funext x
      have h1 : s ^ 2 + x ^ 2 ≠ 0 := by positivity
      have h2 : 1 + (x * s⁻¹) ^ 2 ≠ 0 := by positivity
      field_simp
    rw [heq]; exact hbase.const_mul _
  have hQint : Integrable Q := by
    have hc : Integrable (fun x : ℝ => (s/Real.pi) * (s^2+x^2)⁻¹) := hbound.const_mul _
    refine hc.congr ?_
    filter_upwards with x
    rw [hQdef]; field_simp
  have hQint1 : ∫ v : ℝ, Q v = 1 := by
    have h := Commons.MeasureTheory.Integral.integral_poisson_kernel (y := s) hs
    simpa [hQdef] using h
  set f : ℝ → ℝ := fun t => |Q (u - t) - Q (u + t)| / t with hfdef
  have hQcont : Continuous Q := by
    rw [hQdef]
    exact continuous_const.div (by continuity) (fun v => by positivity)
  have hf_meas : Measurable f := by
    rw [hfdef]
    exact ((hQcont.comp (continuous_const.sub continuous_id)).sub
      (hQcont.comp (continuous_const.add continuous_id))).abs.measurable.div measurable_id
  have hMnn : (0:ℝ) ≤ 2 / (Real.pi * s^2) := by positivity
  have hle1 : ∀ t ∈ Set.Ioc (0:ℝ) 1, f t ≤ 2 / (Real.pi * s^2) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    rw [hfdef]
    have h := hQlip (u - t) (u + t)
    have hsub : (u - t) - (u + t) = -(2*t) := by ring
    rw [hsub, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2*t)] at h
    rw [div_le_iff₀ ht0]
    have : (2 / (Real.pi * s^2)) * t = (1 / (Real.pi * s^2)) * (2*t) := by ring
    rw [this]
    exact h
  have hInt1 : IntegrableOn f (Set.Ioc (0:ℝ) 1) volume := by
    refine IntegrableOn.of_bound (by rw [Real.volume_Ioc]; norm_num) hf_meas.aestronglyMeasurable.restrict (2 / (Real.pi * s^2)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hle1 t ht
    · rw [hfdef]; exact div_nonneg (abs_nonneg _) (le_of_lt ht.1)
  have hA_int : Integrable (fun t : ℝ => Q (u - t) + Q (u + t)) volume :=
    (hQint.comp_sub_left u).add (hQint.comp_add_left u)
  have htri : ∀ t, |Q (u - t) - Q (u + t)| ≤ Q (u - t) + Q (u + t) := by
    intro t
    have h := abs_sub (Q (u - t)) (Q (u + t))
    rwa [abs_of_nonneg (hQnn _), abs_of_nonneg (hQnn _)] at h
  have hInt2 : IntegrableOn f (Set.Ioi (1:ℝ)) volume := by
    refine Integrable.mono' hA_int.restrict hf_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht1
    rw [hfdef, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (le_of_lt ht0)),
        div_le_iff₀ ht0]
    refine le_trans (htri t) ?_
    exact le_mul_of_one_le_right (by positivity) (le_of_lt ht1)
  have hsplit : (∫ t in Set.Ioi (0:ℝ), f t)
      = (∫ t in Set.Ioc (0:ℝ) 1, f t) + (∫ t in Set.Ioi (1:ℝ), f t) := by
    have hU : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
      ext t; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h,_⟩ | h) <;> linarith
      · intro h
        by_cases h1 : t ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
    have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
      rw [Set.disjoint_left]; intro t ht1 ht2; exact absurd ht1.2 (not_le.mpr ht2)
    rw [← hU]
    exact setIntegral_union hdisj measurableSet_Ioi hInt1 hInt2
  have hbound1 : (∫ t in Set.Ioc (0:ℝ) 1, f t) ≤ 2 / (Real.pi * s^2) := by
    have hg0 : IntegrableOn (fun _ : ℝ => 2 / (Real.pi * s^2)) (Set.Ioc (0:ℝ) 1) volume :=
      IntegrableOn.of_bound (by rw [Real.volume_Ioc]; norm_num) aestronglyMeasurable_const (2 / (Real.pi * s^2))
        (ae_of_all _ (fun _ => by rw [Real.norm_of_nonneg hMnn]))
    have h := setIntegral_mono_on hInt1 hg0 measurableSet_Ioc hle1
    have hc : (∫ t in Set.Ioc (0:ℝ) 1, (2 / (Real.pi * s^2))) = 2 / (Real.pi * s^2) := by
      rw [setIntegral_const]; simp
    rw [hc] at h; exact h
  have hbound2 : (∫ t in Set.Ioi (1:ℝ), f t) ≤ 2 := by
    have h1 : (∫ t in Set.Ioi (1:ℝ), f t)
        ≤ ∫ t in Set.Ioi (1:ℝ), (Q (u - t) + Q (u + t)) := by
      refine setIntegral_mono_on hInt2 hA_int.restrict measurableSet_Ioi ?_
      intro t ht
      have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht1
      rw [hfdef, div_le_iff₀ ht0]
      refine le_trans (htri t) ?_
      exact le_mul_of_one_le_right (by positivity) (le_of_lt ht1)
    have h2 : (∫ t in Set.Ioi (1:ℝ), (Q (u - t) + Q (u + t))) ≤ ∫ t : ℝ, (Q (u - t) + Q (u + t)) := by
      have key : (∫ t in Set.Ioi (1:ℝ), (Q (u - t) + Q (u + t)))
          ≤ ∫ t in Set.univ, (Q (u - t) + Q (u + t)) :=
        setIntegral_mono_set hA_int.integrableOn
          (ae_of_all _ (fun t => by positivity))
          (ae_of_all _ (fun _ _ => trivial))
      simpa only [setIntegral_univ] using key
    have e1 : (∫ a : ℝ, Q (u - a)) = ∫ x : ℝ, Q x := integral_sub_left_eq_self Q volume u
    have e2 : (∫ a : ℝ, Q (u + a)) = ∫ x : ℝ, Q x := integral_add_left_eq_self Q u
    have h3 : ∫ t : ℝ, (Q (u - t) + Q (u + t)) = 2 := by
      rw [integral_add (hQint.comp_sub_left u) (hQint.comp_add_left u), e1, e2, hQint1]
      ring
    linarith [h1, h2, h3.le]
  calc (∫ t in Set.Ioi (0:ℝ), f t)
      = (∫ t in Set.Ioc (0:ℝ) 1, f t) + (∫ t in Set.Ioi (1:ℝ), f t) := hsplit
    _ ≤ 2 / (Real.pi * s^2) + 2 := add_le_add hbound1 hbound2

theorem lipschitz_of_contDiff_one {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ∃ L : NNReal, LipschitzWith L g := by
  have hder : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdercs : HasCompactSupport (deriv g) := hc.deriv
  obtain ⟨C0, hC0⟩ := hder.bounded_above_of_compact_support hdercs
  let L : NNReal := ⟨max C0 0, le_max_right _ _⟩
  have hLcoe : (L : ℝ) = max C0 0 := NNReal.coe_mk (max C0 0) (le_max_right _ _)
  refine ⟨L, LipschitzWith.of_dist_le_mul ?_⟩
  intro a b
  have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (C := (L:ℝ))
    (fun x _ => (hg.differentiable one_ne_zero).differentiableAt)
    (fun x _ => by rw [hLcoe]; exact le_trans (hC0 x) (le_max_left _ _))
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  rw [Real.dist_eq, Real.dist_eq]
  simpa only [Real.norm_eq_abs] using hMVT

theorem integrable_poisson_mul_diff_quotient {g : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    Integrable (Function.uncurry (fun y t : ℝ =>
        (s / (Real.pi * (s ^ 2 + y ^ 2))) * ((g (y + t) - g (y - t)) / t)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  set Q : ℝ → ℝ := fun y => s / (Real.pi * (s^2 + y^2)) with hQdef
  set F : ℝ → ℝ → ℝ := fun y t => Q y * ((g (y + t) - g (y - t)) / t) with hFdef
  have hgm : Measurable g := hg.continuous.measurable
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  obtain ⟨L, hLip⟩ := lipschitz_of_contDiff_one hg hc
  have hB1 := fun y => integral_abs_sub_div_le_of_lipschitz hLip hgint y
  have hQcont : Continuous Q := by
    rw [hQdef]; exact continuous_const.div (by continuity) (fun y => by positivity)
  have hQnn : ∀ y, 0 ≤ Q y := by intro y; rw [hQdef]; positivity
  obtain ⟨R, hRpos, hR⟩ := hc.exists_pos_le_norm
  -- measurability of the uncurried integrand
  have hAESM : AEStronglyMeasurable (Function.uncurry F)
      (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    rw [hFdef]
    refine (hQcont.measurable.comp measurable_fst).mul ?_
    exact ((hgm.comp (measurable_fst.add measurable_snd)).sub
      (hgm.comp (measurable_fst.sub measurable_snd))).div measurable_snd
  -- inner integrability for each y
  have hint_inner : ∀ᵐ y ∂(volume : Measure ℝ),
      Integrable (fun t => F y t) (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply ae_of_all
    intro y
    set M : ℝ := R + |y| with hMdef
    have h2Lnn : (0:ℝ) ≤ 2 * (L:ℝ) := by positivity
    have hmaj_on : IntegrableOn (fun _ : ℝ => 2 * (L:ℝ)) (Set.Ioc (0:ℝ) M) volume :=
      IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        aestronglyMeasurable_const (2 * (L:ℝ)) (ae_of_all _ (fun _ => by rw [Real.norm_of_nonneg h2Lnn]))
    have hmaj : Integrable ((Set.Ioc (0:ℝ) M).indicator (fun _ => 2 * (L:ℝ))) volume :=
      (integrable_indicator_iff measurableSet_Ioc).mpr hmaj_on
    have hFmeas : Measurable (fun t => F y t) := by
      rw [hFdef]
      exact measurable_const.mul
        (((hgm.comp (measurable_const.add measurable_id)).sub
          (hgm.comp (measurable_const.sub measurable_id))).div measurable_id)
    -- pointwise bound
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ‖F y t‖ ≤ Q y * (Set.Ioc (0:ℝ) M).indicator (fun _ => 2 * (L:ℝ)) t := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      have hquot_le : |(g (y + t) - g (y - t)) / t| ≤ 2 * (L:ℝ) := by
        rw [abs_div, abs_of_pos ht0]
        have h := hLip.dist_le_mul (y + t) (y - t)
        rw [Real.dist_eq, Real.dist_eq] at h
        have hsub : (y + t) - (y - t) = 2 * t := by ring
        rw [hsub, abs_of_pos (by linarith : (0:ℝ) < 2*t)] at h
        rw [div_le_iff₀ ht0]
        calc |g (y + t) - g (y - t)| ≤ (L:ℝ) * (2*t) := h
          _ = 2 * (L:ℝ) * t := by ring
      rw [hFdef]
      simp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn y)]
      apply mul_le_mul_of_nonneg_left _ (hQnn y)
      by_cases htM : t ≤ M
      · rw [abs_div, abs_of_pos ht0, Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) M from ⟨ht0, htM⟩)]
        rw [div_le_iff₀ ht0]
        have h := hLip.dist_le_mul (y + t) (y - t)
        rw [Real.dist_eq, Real.dist_eq] at h
        have hsub : (y + t) - (y - t) = 2 * t := by ring
        rw [hsub, abs_of_pos (by linarith : (0:ℝ) < 2*t)] at h
        calc |g (y + t) - g (y - t)| ≤ (L:ℝ) * (2*t) := h
          _ = 2 * (L:ℝ) * t := by ring
      · rw [Set.indicator_of_notMem (by rintro ⟨_, h⟩; exact htM h)]
        have htM' : M < t := lt_of_not_ge htM
        have hzero : g (y + t) - g (y - t) = 0 := by
          have hy1 : R ≤ ‖y + t‖ := by
            rw [Real.norm_eq_abs]
            have h : |t| ≤ |y + t| + |y| := by
              have := abs_add_le (y + t) (-y)
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
            rw [abs_of_pos ht0] at h; linarith
          have hy2 : R ≤ ‖y - t‖ := by
            rw [Real.norm_eq_abs, abs_sub_comm]
            have h : |t| ≤ |t - y| + |y| := by
              have := abs_add_le (t - y) y
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
            rw [abs_of_pos ht0] at h; linarith
          rw [hR (y + t) hy1, hR (y - t) hy2]; ring
        rw [hzero, zero_div, abs_zero]
    exact Integrable.mono' (hmaj.restrict.const_mul (Q y))
      (hFmeas.aestronglyMeasurable) hbound
  -- outer integrability
  have hint_outer : Integrable (fun y => ∫ t, ‖F y t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))) volume := by
    have hAESMouter : AEStronglyMeasurable
        (fun y => ∫ t, ‖F y t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))) volume :=
      AEStronglyMeasurable.integral_prod_right' (μ := volume)
        (ν := volume.restrict (Set.Ioi (0:ℝ))) hAESM.norm
    have hbound : ∀ y, ‖∫ t, ‖F y t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))‖
        ≤ (2 * (L:ℝ) + 2 * ∫ x, |g x|) * Q y := by
      intro y
      have hnn : 0 ≤ ∫ t, ‖F y t‖ ∂(volume.restrict (Set.Ioi (0:ℝ))) :=
        integral_nonneg (fun t => norm_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      have hcongr : (∫ t, ‖F y t‖ ∂(volume.restrict (Set.Ioi (0:ℝ))))
          = Q y * ∫ t, |(g (y + t) - g (y - t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        rw [hFdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn y)]
      rw [hcongr]
      have hEq : (∫ t, |(g (y + t) - g (y - t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))))
          = ∫ t, |g (y + t) - g (y - t)| / t ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) < t := ht
        rw [abs_div, abs_of_pos ht0]
      rw [hEq]
      have hB := hB1 y
      calc Q y * (∫ t, |g (y + t) - g (y - t)| / t ∂(volume.restrict (Set.Ioi (0:ℝ))))
          ≤ Q y * (2 * (L:ℝ) + 2 * ∫ x, |g x|) := mul_le_mul_of_nonneg_left hB (hQnn y)
        _ = (2 * (L:ℝ) + 2 * ∫ x, |g x|) * Q y := by ring
    have hQint : Integrable Q volume := by
      have hbase : Integrable (fun x : ℝ => (1 + (x * s⁻¹) ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero (ne_of_gt hs))
      have hbnd : Integrable (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹) := by
        have heq : (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹)
            = fun x : ℝ => (s ^ 2)⁻¹ * (1 + (x * s⁻¹) ^ 2)⁻¹ := by
          funext x
          have h1 : s ^ 2 + x ^ 2 ≠ 0 := by positivity
          have h2 : 1 + (x * s⁻¹) ^ 2 ≠ 0 := by positivity
          field_simp
        rw [heq]; exact hbase.const_mul _
      have hc2 : Integrable (fun x : ℝ => (s/Real.pi) * (s^2+x^2)⁻¹) := hbnd.const_mul _
      refine hc2.congr ?_
      filter_upwards with x
      rw [hQdef]; field_simp
    exact Integrable.mono' (hQint.const_mul (2 * (L:ℝ) + 2 * ∫ x, |g x|)) hAESMouter
      (ae_of_all _ hbound)
  exact (integrable_prod_iff hAESM).mpr ⟨hint_inner, hint_outer⟩


theorem integrable_poissonKernel {s : ℝ} (hs : 0 < s) :
    Integrable (fun v : ℝ => s / (Real.pi * (s^2 + v^2))) volume := by
  have hbase : Integrable (fun x : ℝ => (1 + (x * s⁻¹) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero (ne_of_gt hs))
  have hbnd : Integrable (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹) := by
    have heq : (fun x : ℝ => (s ^ 2 + x ^ 2)⁻¹)
        = fun x : ℝ => (s ^ 2)⁻¹ * (1 + (x * s⁻¹) ^ 2)⁻¹ := by
      funext x
      have h1 : s ^ 2 + x ^ 2 ≠ 0 := by positivity
      have h2 : 1 + (x * s⁻¹) ^ 2 ≠ 0 := by positivity
      field_simp
    rw [heq]; exact hbase.const_mul _
  have hc2 : Integrable (fun x : ℝ => (s/Real.pi) * (s^2+x^2)⁻¹) := hbnd.const_mul _
  refine hc2.congr ?_
  filter_upwards with x
  field_simp

theorem integrable_g_mul_poisson_diff_quotient {g : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    Integrable (Function.uncurry (fun u t : ℝ =>
        g u * ((s / (Real.pi * (s ^ 2 + (u - t) ^ 2)) - s / (Real.pi * (s ^ 2 + (u + t) ^ 2))) / t)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  set Q : ℝ → ℝ := fun v => s / (Real.pi * (s^2 + v^2)) with hQdef
  set G : ℝ → ℝ → ℝ := fun u t => g u * ((Q (u - t) - Q (u + t)) / t) with hGdef
  have hgm : Measurable g := hg.continuous.measurable
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hQlip := poissonKernel_lipschitz hs
  have hQnn : ∀ v, 0 ≤ Q v := by intro v; rw [hQdef]; positivity
  have hQint : Integrable Q := by
    have h := integrable_poissonKernel (s := s) hs
    refine h.congr ?_
    filter_upwards with x
    rw [hQdef]
  have hQcont : Continuous Q := by
    rw [hQdef]; exact continuous_const.div (by continuity) (fun v => by positivity)
  have hAESM : AEStronglyMeasurable (Function.uncurry G)
      (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    rw [hGdef]
    refine (hgm.comp measurable_fst).mul ?_
    refine ((hQcont.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (hQcont.measurable.comp (measurable_fst.add measurable_snd))).div measurable_snd
  have hMnn : (0:ℝ) ≤ 2 / (Real.pi * s^2) := by positivity
  have hint_inner : ∀ᵐ u ∂(volume : Measure ℝ),
      Integrable (fun t => G u t) (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply ae_of_all
    intro u
    -- majorant for |quot t|
    have hpart1 : Integrable ((Set.Ioc (0:ℝ) 1).indicator (fun _ => 2 / (Real.pi * s^2))) volume := by
      refine (integrable_indicator_iff measurableSet_Ioc).mpr ?_
      exact IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        aestronglyMeasurable_const (2 / (Real.pi * s^2)) (ae_of_all _ (fun _ => by rw [Real.norm_of_nonneg hMnn]))
    have hpart2 : Integrable (fun t : ℝ => Q (u - t) + Q (u + t)) volume :=
      (hQint.comp_sub_left u).add (hQint.comp_add_left u)
    have hmaj : Integrable (fun t : ℝ =>
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => 2 / (Real.pi * s^2)) t + (Q (u - t) + Q (u + t))) volume :=
      hpart1.add hpart2
    have hGmeas : Measurable (fun t => G u t) := by
      rw [hGdef]
      exact measurable_const.mul
        (((hQcont.measurable.comp (measurable_const.sub measurable_id)).sub
          (hQcont.measurable.comp (measurable_const.add measurable_id))).div measurable_id)
    have htri : ∀ t, |Q (u - t) - Q (u + t)| ≤ Q (u - t) + Q (u + t) := by
      intro t
      have h := abs_sub (Q (u - t)) (Q (u + t))
      rwa [abs_of_nonneg (hQnn _), abs_of_nonneg (hQnn _)] at h
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
        ‖G u t‖ ≤ |g u| * ((Set.Ioc (0:ℝ) 1).indicator (fun _ => 2 / (Real.pi * s^2)) t + (Q (u - t) + Q (u + t))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      rw [hGdef, Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases ht1 : t ≤ 1
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) 1 from ⟨ht0, ht1⟩)]
        have h := hQlip (u - t) (u + t)
        have hsub : (u - t) - (u + t) = -(2*t) := by ring
        rw [hsub, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2*t)] at h
        rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
        have hle2 : (1/(Real.pi*s^2)) * (2*t) = (2/(Real.pi*s^2)) * t := by ring
        rw [hle2] at h
        calc |Q (u - t) - Q (u + t)| ≤ (2 / (Real.pi * s^2)) * t := h
          _ ≤ ((2 / (Real.pi * s^2)) + (Q (u - t) + Q (u + t))) * t := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt ht0)
              exact le_add_of_nonneg_right (by positivity)
      · rw [Set.indicator_of_notMem (by rintro ⟨_, h⟩; exact ht1 h)]
        have ht1' : (1:ℝ) < t := lt_of_not_ge ht1
        rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
        calc |Q (u - t) - Q (u + t)| ≤ Q (u - t) + Q (u + t) := htri t
          _ ≤ (0 + (Q (u - t) + Q (u + t))) * t := by
              rw [zero_add]
              exact le_mul_of_one_le_right (by positivity) (le_of_lt ht1')
    exact Integrable.mono' (hmaj.restrict.const_mul (|g u|)) hGmeas.aestronglyMeasurable hbound
  have hint_outer : Integrable (fun u => ∫ t, ‖G u t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))) volume := by
    have hAESMouter : AEStronglyMeasurable
        (fun u => ∫ t, ‖G u t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))) volume :=
      AEStronglyMeasurable.integral_prod_right' (μ := volume)
        (ν := volume.restrict (Set.Ioi (0:ℝ))) hAESM.norm
    have hbound : ∀ u, ‖∫ t, ‖G u t‖ ∂(volume.restrict (Set.Ioi (0:ℝ)))‖
        ≤ (2 / (Real.pi * s^2) + 2) * |g u| := by
      intro u
      have hnn : 0 ≤ ∫ t, ‖G u t‖ ∂(volume.restrict (Set.Ioi (0:ℝ))) :=
        integral_nonneg (fun t => norm_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      have hcongr : (∫ t, ‖G u t‖ ∂(volume.restrict (Set.Ioi (0:ℝ))))
          = |g u| * ∫ t, |(Q (u - t) - Q (u + t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
        rw [← integral_const_mul (|g u|)]
        apply integral_congr_ae
        filter_upwards with t
        rw [hGdef, Real.norm_eq_abs, abs_mul]
      rw [hcongr]
      have hle : (∫ t, |(Q (u - t) - Q (u + t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))))
          ≤ 2 / (Real.pi * s^2) + 2 := by
        have hcongr2 : (∫ t, |(Q (u - t) - Q (u + t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))))
            = ∫ t in Set.Ioi (0:ℝ),
                |s / (Real.pi * (s^2 + (u-t)^2)) - s / (Real.pi * (s^2 + (u+t)^2))| / t := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          have ht0 : (0:ℝ) < t := ht
          rw [hQdef, abs_div, abs_of_pos ht0]
        rw [hcongr2]
        exact integral_abs_poisson_diff_div_le (s := s) (u := u) hs
      calc |g u| * (∫ t, |(Q (u - t) - Q (u + t)) / t| ∂(volume.restrict (Set.Ioi (0:ℝ))))
          ≤ |g u| * (2 / (Real.pi * s^2) + 2) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = (2 / (Real.pi * s^2) + 2) * |g u| := by ring
    exact Integrable.mono' (hgint.abs.const_mul (2 / (Real.pi * s^2) + 2)) hAESMouter
      (ae_of_all _ hbound)
  exact (integrable_prod_iff hAESM).mpr ⟨hint_inner, hint_outer⟩
/-- **Hilbert–Poisson smoothing.**  The conjugate Poisson integral `(1/π) ∫ g(t) t/(t²+s²) dt`
equals the Poisson integral of the Hilbert transform of `g`. -/
theorem hilbert_poisson_smoothing {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {s : ℝ} (hs : 0 < s) :
    (1 / Real.pi) * ∫ v : ℝ, g v * (v / (v ^ 2 + s ^ 2))
      = ∫ y : ℝ, ((1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), (g (y + t) - g (y - t)) / t)
          * (s / (Real.pi * (s ^ 2 + y ^ 2))) := by
  set Q : ℝ → ℝ := fun y => s / (Real.pi * (s ^ 2 + y ^ 2)) with hQdef
  set F : ℝ → ℝ → ℝ := fun y t => Q y * ((g (y + t) - g (y - t)) / t) with hFdef
  set G : ℝ → ℝ → ℝ := fun u t =>
      g u * ((Q (u - t) - Q (u + t)) / t) with hGdef
  have hQcont : Continuous Q := by
    rw [hQdef]; exact continuous_const.div (by continuity) (fun y => by positivity)
  have hQnn : ∀ y, 0 ≤ Q y := by intro y; rw [hQdef]; positivity
  have hQint : Integrable Q volume := by
    have h := integrable_poissonKernel (s := s) hs
    refine h.congr ?_
    filter_upwards with x
    rw [hQdef]
  obtain ⟨Cg, hCg⟩ := hg.continuous.bounded_above_of_compact_support hc
  have hFint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    simpa only [hFdef, hQdef] using integrable_poisson_mul_diff_quotient (s := s) hs hg hc
  have hGint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    simpa only [hGdef, hQdef] using integrable_g_mul_poisson_diff_quotient (s := s) hs hg hc
  have hcore : (∫ y, (∫ t in Set.Ioi (0:ℝ), (g (y + t) - g (y - t)) / t) * Q y)
      = ∫ v : ℝ, g v * (v / (v ^ 2 + s ^ 2)) := by
    have hstep1 : (∫ y, (∫ t in Set.Ioi (0:ℝ), (g (y + t) - g (y - t)) / t) * Q y)
        = ∫ y, ∫ t in Set.Ioi (0:ℝ), F y t := by
      apply integral_congr_ae; filter_upwards with y
      rw [hFdef]
      rw [← integral_mul_const]
      apply integral_congr_ae; filter_upwards with t; ring
    rw [hstep1, integral_integral_swap hFint]
    have hinner : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
        (∫ y, F y t ∂volume) = ∫ u, G u t ∂volume := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      have hgcont : Continuous g := hg.continuous
      have h1 : Integrable (fun y => Q y * g (y + t)) volume := by
        refine Integrable.mono' (hQint.const_mul Cg) ?_ ?_
        · exact (hQcont.mul (hgcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn y)]
          calc Q y * |g (y + t)| ≤ Q y * Cg := mul_le_mul_of_nonneg_left (hCg (y+t)) (hQnn y)
            _ = Cg * Q y := by ring
      have h2 : Integrable (fun y => Q y * g (y - t)) volume := by
        refine Integrable.mono' (hQint.const_mul Cg) ?_ ?_
        · exact (hQcont.mul (hgcont.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn y)]
          calc Q y * |g (y - t)| ≤ Q y * Cg := mul_le_mul_of_nonneg_left (hCg (y-t)) (hQnn y)
            _ = Cg * Q y := by ring
      have e1 : (∫ y, Q y * g (y + t)) = ∫ u, g u * Q (u - t) := by
        have h := integral_add_right_eq_self (μ := volume) (fun u : ℝ => g u * Q (u - t)) t
        simpa [mul_comm] using h
      have e2 : (∫ y, Q y * g (y - t)) = ∫ u, g u * Q (u + t) := by
        have h := integral_add_right_eq_self (μ := volume) (fun u : ℝ => g u * Q (u + t)) (-t)
        simp only [sub_eq_add_neg] at h ⊢
        simpa [mul_comm, add_assoc, add_left_comm, add_comm] using h
      have h1' : Integrable (fun u => g u * Q (u - t)) volume := by
        refine Integrable.mono' ((hQint.comp_sub_right (μ := volume) t).const_mul Cg) ?_ ?_
        · exact (hgcont.mul (hQcont.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
        · filter_upwards with u
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn (u - t))]
          calc |g u| * Q (u - t) ≤ Cg * Q (u - t) :=
                mul_le_mul_of_nonneg_right (hCg u) (hQnn _)
            _ = Cg * Q (u - t) := rfl
      have h2' : Integrable (fun u => g u * Q (u + t)) volume := by
        refine Integrable.mono' ((hQint.comp_add_right t).const_mul Cg) ?_ ?_
        · exact (hgcont.mul (hQcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable
        · filter_upwards with u
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQnn (u + t))]
          calc |g u| * Q (u + t) ≤ Cg * Q (u + t) :=
                mul_le_mul_of_nonneg_right (hCg u) (hQnn _)
            _ = Cg * Q (u + t) := rfl
      calc (∫ y, F y t)
          = ∫ y, Q y * ((g (y + t) - g (y - t)) / t) := by rw [hFdef]
        _ = ∫ y, (Q y * g (y + t) - Q y * g (y - t)) / t := by
              apply integral_congr_ae; filter_upwards with y; ring
        _ = (∫ y, (Q y * g (y + t) - Q y * g (y - t))) / t := integral_div t _
        _ = ((∫ y, Q y * g (y + t)) - (∫ y, Q y * g (y - t))) / t := by rw [integral_sub h1 h2]
        _ = ((∫ u, g u * Q (u - t)) - (∫ u, g u * Q (u + t))) / t := by rw [e1, e2]
        _ = (∫ u, (g u * Q (u - t) - g u * Q (u + t))) / t := by rw [integral_sub h1' h2']
        _ = ∫ u, (g u * Q (u - t) - g u * Q (u + t)) / t := (integral_div t _).symm
        _ = ∫ u, G u t := by
              rw [hGdef]
              apply integral_congr_ae; filter_upwards with u; ring
    rw [integral_congr_ae hinner]
    rw [← integral_integral_swap hGint]
    apply integral_congr_ae; filter_upwards with u
    rw [hGdef, integral_const_mul]
    congr 1
    have hk := integral_poisson_hilbert_kernel (s := s) (y := u) hs
    rw [show (∫ t in Set.Ioi (0:ℝ), (Q (u - t) - Q (u + t)) / t)
        = ∫ t in Set.Ioi (0:ℝ),
            ((1 / Real.pi) * (s / (s ^ 2 + (u - t) ^ 2))
              - (1 / Real.pi) * (s / (s ^ 2 + (u + t) ^ 2))) / t from by
      rw [hQdef]
      apply integral_congr_ae; filter_upwards with t
      have h1 : s ^ 2 + (u - t) ^ 2 ≠ 0 := by positivity
      have h2 : s ^ 2 + (u + t) ^ 2 ≠ 0 := by positivity
      field_simp]
    rw [hk]
  have hR : (∫ y : ℝ, ((1 / Real.pi) * ∫ t in Set.Ioi (0:ℝ), (g (y + t) - g (y - t)) / t)
        * (s / (Real.pi * (s^2 + y^2))))
      = (1 / Real.pi) * ∫ y, (∫ t in Set.Ioi (0:ℝ), (g (y + t) - g (y - t)) / t) * Q y := by
    rw [hQdef, ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with y; ring
  rw [hR, hcore]

end Commons.Analysis.Real