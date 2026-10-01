import Mathlib
import Submission.Work.ZeroDensity.Ingham.hasSum_cos_fract
import Submission.Work.ZeroDensity.Zeta.Balanced.sawtIbp
import Submission.Work.ZeroDensity.Zeta.Balanced.sineCpowIoiIbp
import Submission.Work.ZeroDensity.Zeta.Balanced.integrableOn_fract_mul_cpow

/-!
# The sawtooth Fourier expansion, integrated termwise (sorry-free)
-/

namespace Work.ZeroDensity.Ingham.AfeProof

open MeasureTheory Set
open scoped BigOperators

noncomputable section

lemma cpowIdx_ne_zero (k : ℕ) : ((k : ℂ) + 1) ≠ 0 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have h' : ((k : ℝ) + 1 : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  simpa using h'

/-- The `k`-th Fourier coefficient `1/(2π²(k+1)²)`, as a real number. -/
def bernC (k : ℕ) : ℝ := 1 / (2 * Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2)

lemma bernC_nonneg (k : ℕ) : 0 ≤ bernC k := by rw [bernC]; positivity

lemma bernC_eq (k : ℕ) : bernC k = (1 / (2 * Real.pi ^ 2)) * (1 / ((k : ℝ) + 1) ^ 2) := by
  rw [bernC]; field_simp

/-- The reindexed series `Σ_{k≥0} 1/(2π²(k+1)²) = 1/12` of Bernoulli coefficients. -/
lemma hasSum_bernC : HasSum (fun k : ℕ => (bernC k : ℂ)) (1 / 12) := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have h1 : HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hz
    simpa using h
  have h2 : HasSum (fun k : ℕ => ((1 : ℝ) / ((k : ℝ) + 1) ^ 2 : ℂ))
      (((Real.pi : ℂ) ^ 2) / 6) := by
    have h := Complex.hasSum_ofReal.mpr h1
    simpa using h
  have h3 := h2.mul_left ((1 / (2 * (Real.pi : ℂ) ^ 2)))
  have hval : (1 / (2 * (Real.pi : ℂ) ^ 2)) * (((Real.pi : ℂ) ^ 2) / 6) = 1 / 12 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  rw [hval] at h3
  refine h3.congr_fun (fun k => ?_)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm : ((k : ℂ) + 1) ≠ 0 := cpowIdx_ne_zero k
  rw [bernC]
  push_cast
  field_simp

lemma summable_bernC : Summable bernC := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have h1 : HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hz
    simpa using h
  have h2 : Summable (fun k : ℕ => (1 / (2 * Real.pi ^ 2)) * (1 / ((k : ℝ) + 1) ^ 2)) :=
    h1.summable.mul_left _
  exact h2.congr (fun k => (bernC_eq k).symm)

/-- The integrand of the `k`-th Fourier term, `c_k·cos(2π(k+1)u)·u^{-s-2}`. -/
def bernF (s : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  (bernC k : ℂ) *
    (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))

lemma bernF_apply (s : ℂ) (k : ℕ) (u : ℝ) :
    bernF s k u = (bernC k : ℂ) *
      (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) := rfl

/-- **Termwise integration of the second-Bernoulli cosine series.** -/
theorem bernF_hasSum {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    HasSum (fun k : ℕ => (bernC k : ℂ) *
        ∫ u in Set.Ioi (N : ℝ),
          ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      ((∫ u in Set.Ioi (N : ℝ),
          ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
        + (1 / 12) * ((N : ℂ) ^ (-s - 1) / (s + 1))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hre : -(s.re) - 2 < -1 := by linarith [hs]
  have hcpow_re : (-s - 2).re = -(s.re) - 2 := by simp
  -- (1) the pointwise Fourier identity
  have hpt : ∀ u : ℝ, HasSum (fun k : ℕ => bernF s k u)
      ((((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) + (1 / 12)) * (u : ℂ) ^ (-s - 2)) := by
    intro u
    have hz1 : HasSum
        (fun k : ℕ => (1 / ((k : ℝ) + 1) ^ 2) * Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u))
        (Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6)) := by
      have h := (hasSum_nat_add_iff' 1).mpr (hasSum_cos_fract u)
      rw [Finset.sum_range_one] at h
      have h0 : (1 / (((0 : ℕ) : ℝ)) ^ 2) * Real.cos (2 * Real.pi * (((0 : ℕ) : ℝ)) * u) = 0 := by
        norm_num
      rw [h0, sub_zero] at h
      simpa using h
    have hz2 : HasSum
        (fun k : ℕ => bernC k * Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u))
        ((1 / (2 * Real.pi ^ 2)) *
          (Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6))) := by
      have h := hz1.mul_left (1 / (2 * Real.pi ^ 2))
      refine h.congr_fun (fun k => ?_)
      rw [bernC_eq]; ring
    have hz3 : HasSum
        (fun k : ℕ => ((bernC k * Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ))
        ((((1 / (2 * Real.pi ^ 2)) *
          (Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6)) : ℝ) : ℂ)) :=
      Complex.hasSum_ofReal.mpr hz2
    have hz4 := hz3.mul_right ((u : ℂ) ^ (-s - 2))
    have hval : ((((1 / (2 * Real.pi ^ 2)) *
          (Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6)) : ℝ) : ℂ))
        = (((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) + (1 / 12)) := by
      have hp : Real.pi ≠ 0 := Real.pi_ne_zero
      push_cast
      field_simp
      ring
    rw [hval] at hz4
    refine hz4.congr_fun (fun k => ?_)
    rw [bernF, Complex.ofReal_mul]
    ring
  -- (2) integrability of each term
  have hF_int : ∀ k : ℕ, IntegrableOn (bernF s k) (Set.Ioi (N : ℝ)) := by
    intro k
    have hg : IntegrableOn (fun u : ℝ => bernC k * u ^ (-(s.re) - 2)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hre hNpos).const_mul (bernC k)
    refine Integrable.mono' hg ?_ ?_
    · refine (ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)).aestronglyMeasurable
        measurableSet_Ioi
      · exact (Complex.continuous_ofReal.comp
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn
      · refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
        intro a ha
        exact Or.inl (by rw [Complex.ofReal_re]; exact lt_of_lt_of_le hNpos (le_of_lt ha))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hNpos (le_of_lt hu)
      have hbc : ‖(bernC k : ℂ)‖ = bernC k := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bernC_nonneg k)]
      have hcos : ‖(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have hcw : ‖(u : ℂ) ^ (-s - 2)‖ = u ^ (-(s.re) - 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hcpow_re]
      have hgn : ‖bernC k * u ^ (-(s.re) - 2)‖ = bernC k * u ^ (-(s.re) - 2) := by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (bernC_nonneg k) (Real.rpow_nonneg (le_of_lt hu0) _))]
      rw [bernF, norm_mul, norm_mul, hbc, hcw]
      have h1 : ‖(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ))‖ * u ^ (-(s.re) - 2)
          ≤ u ^ (-(s.re) - 2) := by
        simpa using mul_le_of_le_one_left (Real.rpow_nonneg (le_of_lt hu0) (-(s.re) - 2)) hcos
      simpa using mul_le_mul_of_nonneg_left h1 (bernC_nonneg k)
  -- (3) summability of the integrals of the norms
  have hF_sum : Summable (fun k : ℕ =>
      ∫ u in Set.Ioi (N : ℝ), ‖bernF s k u‖) := by
    have huint : ∀ k : ℕ,
        (∫ u in Set.Ioi (N : ℝ), ‖bernF s k u‖)
          ≤ bernC k * (∫ u in Set.Ioi (N : ℝ), u ^ (-(s.re) - 2)) := by
      intro k
      have hg : IntegrableOn (fun u : ℝ => bernC k * u ^ (-(s.re) - 2)) (Set.Ioi (N : ℝ)) :=
        (integrableOn_Ioi_rpow_of_lt hre hNpos).const_mul (bernC k)
      have hb : ∀ᵐ u ∂(volume.restrict (Set.Ioi (N : ℝ))),
          ‖bernF s k u‖ ≤ bernC k * u ^ (-(s.re) - 2) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hNpos (le_of_lt hu)
        have hbc : ‖(bernC k : ℂ)‖ = bernC k := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bernC_nonneg k)]
        have hcos : ‖(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ))‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact Real.abs_cos_le_one _
        have hcw : ‖(u : ℂ) ^ (-s - 2)‖ = u ^ (-(s.re) - 2) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hcpow_re]
        rw [bernF, norm_mul, norm_mul, hbc, hcw]
        have h1 : ‖(((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ))‖ * u ^ (-(s.re) - 2)
            ≤ u ^ (-(s.re) - 2) := by
          simpa using mul_le_of_le_one_left (Real.rpow_nonneg (le_of_lt hu0) (-(s.re) - 2)) hcos
        simpa using mul_le_mul_of_nonneg_left h1 (bernC_nonneg k)
      calc (∫ u in Set.Ioi (N : ℝ), ‖bernF s k u‖)
          = ∫ u, ‖bernF s k u‖ ∂(volume.restrict (Set.Ioi (N : ℝ))) := rfl
        _ ≤ ∫ u, bernC k * u ^ (-(s.re) - 2) ∂(volume.restrict (Set.Ioi (N : ℝ))) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _)) hg hb
        _ = bernC k * ∫ u, u ^ (-(s.re) - 2) ∂(volume.restrict (Set.Ioi (N : ℝ))) :=
            integral_const_mul _ _
        _ = bernC k * (∫ u in Set.Ioi (N : ℝ), u ^ (-(s.re) - 2)) := rfl
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun u => norm_nonneg _))
      huint ?_
    exact summable_bernC.mul_right _
  -- (4) the interchange
  have key := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi (N : ℝ))) hF_int hF_sum
  have hL : (fun k : ℕ => ∫ u, bernF s k u ∂(volume.restrict (Set.Ioi (N : ℝ))))
      = (fun k : ℕ => (bernC k : ℂ) *
          ∫ u in Set.Ioi (N : ℝ),
            ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) := by
    funext k
    rw [show (∫ u, bernF s k u ∂(volume.restrict (Set.Ioi (N : ℝ))))
        = ∫ u, (bernC k : ℂ) *
            (((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
          ∂(volume.restrict (Set.Ioi (N : ℝ))) from
        integral_congr_ae (Filter.Eventually.of_forall (fun u => bernF_apply s k u))]
    exact integral_const_mul _ _
  have hInt2 : (∫ u in Set.Ioi (N : ℝ), (u : ℂ) ^ (-s - 2)) = (N : ℂ) ^ (-s - 1) / (s + 1) := by
    rw [integral_Ioi_cpow_of_lt (by rw [hcpow_re]; exact hre) hNpos]
    have e1 : (-s - 2 + 1 : ℂ) = -s - 1 := by ring
    have e2 : (-s - 1 : ℂ) = -(s + 1) := by ring
    rw [e1, e2, neg_div_neg_eq, Complex.ofReal_natCast]
  have hR : (∫ u, (∑' k : ℕ, bernF s k u) ∂(volume.restrict (Set.Ioi (N : ℝ))))
      = (∫ u in Set.Ioi (N : ℝ),
          ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
        + (1 / 12) * ((N : ℂ) ^ (-s - 1) / (s + 1)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun u => (hpt u).tsum_eq))]
    have hsplit : (fun u : ℝ => (((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) + (1 / 12))
          * (u : ℂ) ^ (-s - 2))
        = (fun u : ℝ => ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)
            + (1 / 12) * (u : ℂ) ^ (-s - 2)) := by
      funext u; ring
    rw [hsplit]
    have h1 : IntegrableOn (fun u : ℝ =>
        ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
        (Set.Ioi (N : ℝ)) :=
      Work.ZeroDensity.Zeta.Balanced.integrableOn_fract_mul_cpow hs hNpos
    have h2 : IntegrableOn (fun u : ℝ => (1 / 12) * (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt (by rw [hcpow_re]; exact hre) hNpos).const_mul _
    rw [integral_add h1 h2, integral_const_mul, hInt2]
  rw [hL, hR] at key
  exact key

/-- **The sawtooth Fourier expansion, integrated termwise.** -/
theorem afeSawtoothFourier {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in Set.Ioi (N : ℝ), (((Int.fract u : ℝ) : ℂ) - 1 / 2) * (u : ℂ) ^ (-s - 1)
      = -(∑' k : ℕ, (1 / (Real.pi * ((k : ℝ) + 1))) *
          ∫ u in Set.Ioi (N : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
  have hs1' : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hpoint : ∀ k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1))) *
          ∫ u in Set.Ioi (N : ℝ),
            ((Real.sin (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
        = (N : ℂ) ^ (-s - 1) * (bernC k : ℂ)
          - (s + 1) * ((bernC k : ℂ) *
              ∫ u in Set.Ioi (N : ℝ),
                ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) := by
    intro k
    rw [Work.ZeroDensity.Zeta.Balanced.sineCpowIoiIbp (s := s) hs0 N hN k]
    have hcos : ((Real.cos (2 * Real.pi * ((k : ℝ) + 1) * (N : ℝ)) : ℝ) : ℂ) = 1 := by
      have harg : 2 * Real.pi * ((k : ℝ) + 1) * (N : ℝ)
          = (((k + 1) * N : ℕ) : ℝ) * (2 * Real.pi) := by push_cast; ring
      rw [harg, Real.cos_nat_mul_two_pi]
      norm_num
    rw [hcos]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hm : ((k : ℂ) + 1) ≠ 0 := cpowIdx_ne_zero k
    rw [bernC]
    push_cast
    field_simp
  have hZ := hasSum_bernC.mul_left ((N : ℂ) ^ (-s - 1))
  have hB := bernF_hasSum (s := s) hs0 N hN
  have hBm := hB.mul_left (s + 1)
  have hsub := hZ.sub hBm
  have hmain := hsub.congr_fun hpoint
  have halg : (s + 1) * (∫ u in Set.Ioi (N : ℝ),
        ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      = -((N : ℂ) ^ (-s - 1) * (1 / 12)
        - (s + 1) * ((∫ u in Set.Ioi (N : ℝ),
              ((((Int.fract u) ^ 2 - Int.fract u) / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
            + (1 / 12) * ((N : ℂ) ^ (-s - 1) / (s + 1)))) := by
    field_simp
    ring
  rw [Work.ZeroDensity.Zeta.Balanced.sawtIbp (s := s) hs0 N hN, hmain.tsum_eq]
  exact halg

end

end Work.ZeroDensity.Ingham.AfeProof
