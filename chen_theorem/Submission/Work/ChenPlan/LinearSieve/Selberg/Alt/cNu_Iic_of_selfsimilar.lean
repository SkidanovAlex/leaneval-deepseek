import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.uniform_of_exp

/-!
# The CDF of the reference law `cNu` at arguments `θ ≤ 1`

`cNu` is the law of the reference sum `cY = Σ_{k≥1} e^{-S_k}` (`S_k` the partial sums of
iid standard exponentials).  Its distribution function satisfies

  `cNu (Iic θ) = θ · ∫ (1+t)⁻¹ ∂cNu`   for `0 < θ ≤ 1`,

the "base case" of the linear-sieve `σ`-function.  The proof here starts from the
self-similarity `cNu = law of U·(1+Y)` (`U` uniform on `(0,1)`, `Y ~ cNu`) and the
observation that `cY > 0` pointwise, so that `cNu` charges no mass to `(-∞, 0]`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- `cSum` is measurable in the sample point. -/
lemma measurable_cSum (k : ℕ) : Measurable (fun x : ℕ → ℝ => cSum x k) := by
  unfold cSum
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- The reference sum is measurable. -/
lemma measurable_cY : Measurable cY := by
  unfold cY
  exact Measurable.tsum fun k => Real.measurable_exp.comp (measurable_cSum (k+1)).neg

instance instCnuIsProbabilityMeasure : IsProbabilityMeasure cNu := by
  rw [cNu]
  exact (Measure.isProbabilityMeasure_map_iff measurable_cY.aemeasurable).mpr inferInstance

/-- Lebesgue measure of the restricted unit interval on a left interval `(-∞, t]`. -/
lemma vol_restrict_Ioo_Iic (t : ℝ) (_ht0 : 0 < t) (ht1 : t < 1) :
    (volume.restrict (Set.Ioo (0:ℝ) 1)) (Set.Iic t) = ENNReal.ofReal t := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Ioo (0:ℝ) 1 = Set.Ioc 0 t := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, lt_of_le_of_lt h2 ht1⟩
  rw [hset, Real.volume_Ioc, sub_zero]

/-- The `cUnif`-measure of the section `{u | u * (1+z) ≤ θ}`, for `θ - 1 < z`. -/
lemma cUnif_section_eq (hcUnif : cUnif = volume.restrict (Set.Ioo (0:ℝ) 1))
    {z θ : ℝ} (hθ0 : 0 < θ) (hz : θ - 1 < z) :
    cUnif {u : ℝ | u * (1 + z) ≤ θ} = ENNReal.ofReal (θ * (1 + z)⁻¹) := by
  have hpos : 0 < 1 + z := by linarith
  rw [hcUnif]
  have hset : {u : ℝ | u * (1 + z) ≤ θ} = Set.Iic (θ / (1 + z)) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    exact (le_div_iff₀ hpos).symm
  rw [hset, vol_restrict_Ioo_Iic (θ / (1 + z)) (div_pos hθ0 hpos)
        ((div_lt_one hpos).mpr (by linarith)), div_eq_mul_inv]

/-- A section of the map `(u,z) ↦ u * (1+z)` is empty once `z > x - 1`, for `x ≤ 0`. -/
lemma section_empty_of {y z u : ℝ} (hy : y ≤ 0) (hz : y - 1 < z)
    (hu0 : 0 < u) (hu1 : u < 1) (hle : u * (1 + z) ≤ y) : False := by
  have hle0 : (1 + z) ≤ 0 := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_pos hu0 h]
  rcases lt_or_eq_of_le hle0 with hneg | hzero
  · have hprod : 0 < (u - 1) * (1 + z) := mul_pos_of_neg_of_neg (by linarith) hneg
    nlinarith [hprod]
  · have hy0 : y = 0 := le_antisymm hy (by nlinarith [hle, hzero])
    linarith

/-- The distribution function of `cNu` as the integral of the `cUnif`-measures of the
sections of the multiplication map, deduced from the self-similarity. -/
lemma cNu_Iic_eq_lintegral
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2))) (x : ℝ) :
    cNu (Set.Iic x) = ∫⁻ z : ℝ, cUnif {u : ℝ | u * (1 + z) ≤ x} ∂cNu := by
  have hφ : Measurable (fun p : ℝ × ℝ => p.1 * (1 + p.2)) := by fun_prop
  have hS : MeasurableSet ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' (Set.Iic x)) :=
    hφ measurableSet_Iic
  conv_lhs => rw [hself]
  rw [Measure.map_apply hφ measurableSet_Iic,
      Measure.prod_apply_symm
        (s := (fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' (Set.Iic x)) hS]
  refine lintegral_congr fun z => ?_
  have hset : (fun u : ℝ => (u, z)) ⁻¹'
        ((fun p : ℝ × ℝ => p.1 * (1 + p.2)) ⁻¹' Set.Iic x)
      = {u : ℝ | u * (1 + z) ≤ x} := by
    ext u; simp [Set.mem_preimage]
  rw [hset]

/-- `cNu` charges no mass to `(-∞, 0]`: this is where the self-similarity is used. -/
lemma cNu_Iic_nonpos
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = volume.restrict (Set.Ioo (0:ℝ) 1))
    {x : ℝ} (hx : x ≤ 0) : cNu (Set.Iic x) = 0 := by
  have hmeasS : ∀ z : ℝ, MeasurableSet {u : ℝ | u * (1 + z) ≤ x} := fun z =>
    measurableSet_Iic.preimage (by fun_prop : Measurable (fun u : ℝ => u * (1 + z)))
  have hstep : ∀ y : ℝ, y ≤ 0 → cNu (Set.Iic y) ≤ cNu (Set.Iic (y - 1)) := by
    intro y hy
    have hle : ∫⁻ z : ℝ, cUnif {u : ℝ | u * (1 + z) ≤ y} ∂cNu
        ≤ ∫⁻ z : ℝ, (Set.Iic (y - 1)).indicator (fun _ => (1:ℝ≥0∞)) z ∂cNu :=
      lintegral_mono fun z => by
        by_cases hz : z ∈ Set.Iic (y - 1)
        · rw [Set.indicator_of_mem hz]
          rw [hcUnif, Measure.restrict_apply (t := {u : ℝ | u * (1 + z) ≤ y})
                (measurableSet_Iic.preimage
                  (by fun_prop : Measurable (fun u : ℝ => u * (1 + z))))]
          calc volume ({u : ℝ | u * (1 + z) ≤ y} ∩ Set.Ioo (0:ℝ) 1)
              ≤ volume (Set.Ioo (0:ℝ) 1) := measure_mono Set.inter_subset_right
            _ = 1 := by rw [Real.volume_Ioo]; norm_num
        · rw [Set.indicator_of_notMem hz]
          rw [hcUnif, Measure.restrict_apply (t := {u : ℝ | u * (1 + z) ≤ y})
                (measurableSet_Iic.preimage
                  (by fun_prop : Measurable (fun u : ℝ => u * (1 + z))))]
          have hz' : y - 1 < z := by
            rw [Set.mem_Iic] at hz
            exact not_le.mp hz
          have hempty : {u : ℝ | u * (1 + z) ≤ y} ∩ Set.Ioo (0:ℝ) 1 = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro u hu
            exact section_empty_of hy hz' hu.2.1 hu.2.2 hu.1
          rw [hempty, measure_empty]
    rw [cNu_Iic_eq_lintegral hself y,
        ← lintegral_indicator_one (μ := cNu) measurableSet_Iic]
    exact hle
  have hchain : cNu (Set.Iic x) ≤ ⨅ n : ℕ, cNu (Set.Iic (-(n:ℝ))) := by
    refine le_iInf fun n => ?_
    rcases le_or_gt x (-(n:ℝ)) with h | h
    · exact measure_mono (Set.Iic_subset_Iic.mpr h)
    · have hiter : ∀ m : ℕ, cNu (Set.Iic x) ≤ cNu (Set.Iic (x - m)) := by
        intro m
        induction m with
        | zero => simp
        | succ k ih =>
            have hk : cNu (Set.Iic (x - (k:ℝ))) ≤ cNu (Set.Iic (x - (k:ℝ) - 1)) :=
              hstep (x - (k:ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k])
            have heq : Set.Iic (x - (k:ℝ) - 1) = Set.Iic (x - ↑(k + 1 : ℕ)) := by
              push_cast
              congr 1
              ring
            rw [← heq]
            exact le_trans ih hk
      obtain ⟨m, hm⟩ := exists_nat_ge (x + n)
      refine le_trans (hiter m) (measure_mono (Set.Iic_subset_Iic.mpr ?_))
      linarith
  have hzero : (⨅ n : ℕ, cNu (Set.Iic (-(n:ℝ)))) = 0 := by
    have hanti : Antitone (fun n : ℕ => Set.Iic (-(n:ℝ))) := by
      intro i j hij
      rw [Set.Iic_subset_Iic]
      linarith [Nat.cast_le (α := ℝ) |>.mpr hij]
    have hInter : (⋂ n : ℕ, Set.Iic (-(n:ℝ))) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro t ht
      rw [Set.mem_iInter] at ht
      obtain ⟨m, hm⟩ := exists_nat_gt (-t)
      exact (not_le.mpr (by linarith : -(m:ℝ) < t)) (ht m)
    calc (⨅ n : ℕ, cNu (Set.Iic (-(n:ℝ))))
        = cNu (⋂ n : ℕ, Set.Iic (-(n:ℝ))) :=
          (hanti.measure_iInter (fun _ => measurableSet_Iic.nullMeasurableSet)
            ⟨0, measure_ne_top _ _⟩).symm
      _ = cNu ∅ := by rw [hInter]
      _ = 0 := measure_empty
  exact le_antisymm (le_trans hchain (le_of_eq hzero)) bot_le

theorem cNu_Iic_of_selfsimilar
    (hself : cNu = (cUnif.prod cNu).map (fun p : ℝ × ℝ => p.1 * (1 + p.2)))
    (hcUnif : cUnif = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    cNu (Set.Iic θ) = ENNReal.ofReal (θ * ∫ z : ℝ, (1+z)⁻¹ ∂cNu) := by
  have hnull : cNu (Set.Iic (θ - 1)) = 0 := cNu_Iic_nonpos hself hcUnif (by linarith)
  have hcongr : (fun z : ℝ => cUnif {u : ℝ | u * (1 + z) ≤ θ})
      =ᵐ[cNu] (fun z : ℝ => ENNReal.ofReal (θ * (1 + z)⁻¹)) := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ hnull
    intro z hz
    rw [Set.mem_Iic]
    by_contra hmem
    rw [not_le] at hmem
    exact hz (cUnif_section_eq hcUnif hθ0 hmem)
  have hIntf : Integrable (fun z : ℝ => (1 + z)⁻¹) cNu := by
    have hmeas : AEStronglyMeasurable (fun z : ℝ => (1 + z)⁻¹) cNu :=
      (by fun_prop : Measurable (fun z : ℝ => (1 + z)⁻¹)).aestronglyMeasurable
    refine Integrable.of_bound hmeas 1 ?_
    rw [ae_iff]
    apply measure_mono_null _ (cNu_Iic_nonpos hself hcUnif (le_refl 0))
    intro z hz
    rw [Set.mem_Iic]
    by_contra hmem
    rw [not_le] at hmem
    refine hz ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hIntθ : Integrable (fun z : ℝ => θ * (1 + z)⁻¹) cNu := hIntf.const_mul θ
  have hnonneg : ∀ᵐ z ∂cNu, (0:ℝ) ≤ θ * (1 + z)⁻¹ := by
    rw [ae_iff]
    apply measure_mono_null _ hnull
    intro z hz
    rw [Set.mem_Iic]
    by_contra hmem
    rw [not_le] at hmem
    exact hz (mul_nonneg (le_of_lt hθ0) (inv_nonneg.mpr (by linarith)))
  rw [cNu_Iic_eq_lintegral hself θ, lintegral_congr_ae hcongr,
      ← ofReal_integral_eq_lintegral_ofReal hIntθ hnonneg, integral_const_mul]

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
