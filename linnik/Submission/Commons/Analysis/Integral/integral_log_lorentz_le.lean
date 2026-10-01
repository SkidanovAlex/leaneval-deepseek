import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Integral.norm_intervalIntegral_mul_le

open MeasureTheory Real Set

namespace Commons.Analysis.Integral

private lemma log_two_add_le_two_add_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.log (2 + x) ≤ 2 + Real.sqrt x := by
  have key : ∀ t : ℝ, 0 ≤ t → Real.log (2 + t^2) ≤ 2 + t := by
    intro t ht
    have hmono : MonotoneOn (fun t : ℝ => 2 + t - Real.log (2 + t^2)) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · apply ContinuousOn.sub
        · fun_prop
        · apply ContinuousOn.log
          · fun_prop
          · intro y hy; positivity
      · intro y hy
        have : DifferentiableAt ℝ (fun t : ℝ => 2 + t - Real.log (2 + t^2)) y := by
          apply DifferentiableAt.sub
          · fun_prop
          · exact (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => 2 + t^2) y).log (by positivity)
        exact this.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hd : deriv (fun t : ℝ => 2 + t - Real.log (2 + t^2)) y = 1 - 2 * y / (2 + y^2) := by
          have h1 : HasDerivAt (fun t : ℝ => 2 + t) 1 y := by
            simpa using (hasDerivAt_id y).const_add (2:ℝ)
          have h2 : HasDerivAt (fun t : ℝ => 2 + t^2) (2*y) y := by
            simpa using ((hasDerivAt_id y).pow 2).const_add (2:ℝ)
          have h3 : HasDerivAt (fun t : ℝ => Real.log (2 + t^2)) (2 * y / (2 + y^2)) y := h2.log (by positivity)
          exact (h1.sub h3).deriv
        rw [hd]
        rw [sub_nonneg, div_le_one (by positivity)]
        nlinarith [sq_nonneg (y-1)]
    have h0 : (2 + (0:ℝ) - Real.log (2 + (0:ℝ)^2)) ≤ (2 + t - Real.log (2 + t^2)) :=
      hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hpos : (0:ℝ) < 2 + (0:ℝ) - Real.log (2 + (0:ℝ)^2) := by
      have hlog2 : Real.log 2 < 2 := by linarith [Real.log_two_lt_d9]
      have hh : (2:ℝ) + 0 - Real.log (2 + (0:ℝ)^2) = 2 - Real.log 2 := by norm_num
      rw [hh]; linarith
    linarith
  have hthis := key (Real.sqrt x) (Real.sqrt_nonneg x)
  rw [sq_sqrt hx] at hthis
  exact hthis

private lemma log_two_add_abs_le (t b : ℝ) :
    Real.log (2 + |t|) ≤ Real.log (2 + |b|) + Real.log (2 + |t - b|) := by
  have ht : (0:ℝ) < 2 + |t| := by positivity
  have hb : (0:ℝ) < 2 + |b| := by positivity
  have htb : (0:ℝ) < 2 + |t - b| := by positivity
  rw [← Real.log_mul hb.ne' htb.ne']
  apply Real.log_le_log ht
  have h1 : |t| ≤ |t - b| + |b| := by
    have := abs_add_le (t - b) b
    rwa [sub_add_cancel] at this
  nlinarith [abs_nonneg (t-b), abs_nonneg b, abs_nonneg t,
    mul_nonneg (abs_nonneg b) (abs_nonneg (t-b))]

private lemma phi_le_majorant (a x : ℝ) (_ha : 0 < a) (hx : 1 < x) :
    (3 + Real.sqrt x)/(a^2+x^2) ≤ 3 * x^(-2:ℝ) + x^(-(3:ℝ)/2) := by
  have hx0 : 0 < x := by linarith
  have hnum : 0 ≤ 3 + Real.sqrt x := by positivity
  have hden : x^2 ≤ a^2 + x^2 := by nlinarith [sq_nonneg a]
  have hstep : (3 + Real.sqrt x)/(a^2+x^2) ≤ (3 + Real.sqrt x)/x^2 :=
    div_le_div_of_nonneg_left hnum (by positivity) hden
  have hexp : (3 + Real.sqrt x)/x^2 = 3 * x^(-2:ℝ) + x^(-(3:ℝ)/2) := by
    rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_two]
    rw [show (-(3:ℝ)/2) = (1/2:ℝ) + (-2:ℝ) by norm_num, Real.rpow_add hx0, ← Real.sqrt_eq_rpow]
    rw [show (-2:ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_two]
    field_simp
  linarith [hstep, hexp.le, hexp.ge]

private lemma integrableOn_phi (a : ℝ) (ha : 3/2 < a) :
    IntegrableOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Ioi 0) := by
  have ha0 : 0 < a := by linarith
  have hnum : Continuous (fun x : ℝ => 3 + Real.sqrt x) := by fun_prop
  have hden : Continuous (fun x : ℝ => a^2 + x^2) := by fun_prop
  have hne : ∀ x : ℝ, a^2 + x^2 ≠ 0 := by intro x; positivity
  have hcont : ContinuousOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Icc 0 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx; positivity
  have h1 : IntegrableOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Ioc 0 1) :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hA : IntegrableOn (fun x : ℝ => x ^ (-2:ℝ)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).2 (by norm_num)
  have hB : IntegrableOn (fun x : ℝ => x ^ (-(3:ℝ)/2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).2 (by norm_num)
  have hg : IntegrableOn (fun x : ℝ => 3 * x ^ (-2:ℝ) + x ^ (-(3:ℝ)/2)) (Set.Ioi 1) :=
    (hA.const_mul 3).add hB
  have h2 : IntegrableOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Ioi 1) := by
    apply Integrable.mono' hg
    · exact (hnum.div hden hne).stronglyMeasurable.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact phi_le_majorant a x ha0 hx
  have hset : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, h2⟩ | h)
      · exact h1
      · linarith
  rw [hset]
  exact h1.union h2

private lemma integral_phi_le (a : ℝ) (ha : 3/2 < a) :
    (∫ x in Set.Ioi 0, (3 + Real.sqrt x) / (a^2 + x^2)) ≤ 61/9 := by
  have ha0 : 0 < a := by linarith
  have hφint := integrableOn_phi a ha
  have h1 : IntegrableOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Ioc 0 1) :=
    hφint.mono_set (fun x hx => Set.mem_Ioi.mpr (Set.mem_Ioc.mp hx).1)
  have h2 : IntegrableOn (fun x : ℝ => (3 + Real.sqrt x) / (a^2 + x^2)) (Set.Ioi 1) :=
    hφint.mono_set (fun x hx => Set.mem_Ioi.mpr (by have := Set.mem_Ioi.mp hx; linarith))
  have b1 : (∫ x in Set.Ioc 0 1, (3 + Real.sqrt x) / (a^2 + x^2)) ≤ 16/9 := by
    have hcle : IntegrableOn (fun _ : ℝ => (4:ℝ)/a^2) (Set.Ioc 0 1) := by
      apply integrableOn_const
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      · exact ENNReal.coe_ne_top
    have hle : ∀ x ∈ Set.Ioc 0 1, (3 + Real.sqrt x) / (a^2 + x^2) ≤ (4:ℝ)/a^2 := by
      intro x hx
      have hx1 : x ≤ 1 := hx.2
      have hsx : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
      have hd : (0:ℝ) < a^2 + x^2 := by positivity
      have hden : a^2 ≤ a^2 + x^2 := by nlinarith [sq_nonneg x]
      calc (3 + Real.sqrt x)/(a^2+x^2)
          ≤ 4/(a^2+x^2) := div_le_div_of_nonneg_right (by linarith) hd.le
        _ ≤ 4/a^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    have hmono := setIntegral_mono_on h1 hcle measurableSet_Ioc hle
    rw [setIntegral_const] at hmono
    have hvol : (volume : Measure ℝ).real (Set.Ioc 0 1) = 1 := by
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num
    rw [hvol, one_smul] at hmono
    have ha2' : (9:ℝ)/4 < a^2 := by nlinarith
    have hc : (4:ℝ)/a^2 ≤ 16/9 := by
      have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 4 by norm_num) (show (0:ℝ) < 9/4 by norm_num) ha2'.le
      have h' : (4:ℝ)/(9/4) = 16/9 := by norm_num
      linarith [h]
    linarith
  have hA : IntegrableOn (fun x : ℝ => x ^ (-2:ℝ)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).2 (by norm_num)
  have hB : IntegrableOn (fun x : ℝ => x ^ (-(3:ℝ)/2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).2 (by norm_num)
  have hg : IntegrableOn (fun x : ℝ => 3 * x ^ (-2:ℝ) + x ^ (-(3:ℝ)/2)) (Set.Ioi 1) :=
    (hA.const_mul 3).add hB
  have b2 : (∫ x in Set.Ioi 1, (3 + Real.sqrt x) / (a^2 + x^2)) ≤ 5 := by
    have hle : ∀ x ∈ Set.Ioi 1, (3 + Real.sqrt x) / (a^2 + x^2) ≤ 3 * x ^ (-2:ℝ) + x ^ (-(3:ℝ)/2) :=
      fun x hx => phi_le_majorant a x ha0 hx
    have hmono := setIntegral_mono_on h2 hg measurableSet_Ioi hle
    have hgval : (∫ x : ℝ in Set.Ioi 1, (3 * x ^ (-2:ℝ) + x ^ (-(3:ℝ)/2))) = 5 := by
      rw [integral_add (hA.const_mul 3) hB, integral_const_mul]
      have e1 : (∫ x : ℝ in Set.Ioi 1, x ^ (-2:ℝ)) = 1 := by
        rw [integral_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) (show (0:ℝ) < 1 by norm_num)]
        have h : (1:ℝ) ^ ((-2:ℝ) + 1) = 1 := by
          rw [show (-2:ℝ)+1 = (-1:ℝ) by norm_num, Real.one_rpow]
        rw [h]; norm_num
      have e2 : (∫ x : ℝ in Set.Ioi 1, x ^ (-(3:ℝ)/2)) = 2 := by
        rw [integral_Ioi_rpow_of_lt (show (-(3:ℝ)/2) < -1 by norm_num) (show (0:ℝ) < 1 by norm_num)]
        have h : (1:ℝ) ^ (-(3:ℝ)/2 + 1) = 1 := by
          rw [show (-(3:ℝ)/2 + 1) = (-1/2:ℝ) by norm_num, Real.one_rpow]
        rw [h]; norm_num
      rw [e1, e2]; norm_num
    linarith [hmono, hgval]
  have hset : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨h1, h2⟩ | h)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 => by
      have h1 := (Set.mem_Ioc.mp hx1).2
      have h2 := Set.mem_Ioi.mp hx2
      linarith)
  rw [hset, setIntegral_union hdisj measurableSet_Ioi h1 h2]
  linarith [b1, b2]

private lemma integral_psi_le (a : ℝ) (ha : 3/2 < a) :
    (∫ x in Set.Ioi 0, (1 + Real.log (2 + x)) / (a^2 + x^2))
      ≤ (∫ x in Set.Ioi 0, (3 + Real.sqrt x) / (a^2 + x^2)) := by
  have ha0 : 0 < a := by linarith
  have hφ := integrableOn_phi a ha
  have hmeas : Measurable (fun x : ℝ => (1 + Real.log (2 + x)) / (a^2 + x^2)) := by
    apply Measurable.div
    · exact measurable_const.add (Measurable.log (measurable_const.add measurable_id))
    · fun_prop
  have hle : ∀ x ∈ Set.Ioi 0, (1 + Real.log (2 + x)) / (a^2 + x^2)
      ≤ (3 + Real.sqrt x) / (a^2 + x^2) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [log_two_add_le_two_add_sqrt x hx0]
  have hψ : IntegrableOn (fun x : ℝ => (1 + Real.log (2 + x)) / (a^2 + x^2)) (Set.Ioi 0) := by
    apply Integrable.mono' hφ
    · exact hmeas.stronglyMeasurable.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      have hx0 : 0 ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
      have hnn : 0 ≤ (1 + Real.log (2 + x)) / (a^2 + x^2) := by
        apply div_nonneg
        · have : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith); linarith
        · positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hle x hx
  exact setIntegral_mono_on hψ hφ measurableSet_Ioi hle

private lemma integrable_phi_abs (a : ℝ) (ha : 3/2 < a) :
    Integrable (fun s : ℝ => (3 + Real.sqrt |s|) / (a^2 + s^2)) := by
  have hφ := integrableOn_phi a ha
  have hIoi : IntegrableOn (fun s : ℝ => (3 + Real.sqrt |s|) / (a^2 + s^2)) (Set.Ioi 0) := by
    refine hφ.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (Set.mem_Ioi.mp hx)]
  have hIic : IntegrableOn (fun s : ℝ => (3 + Real.sqrt |s|) / (a^2 + s^2)) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero, neg_sq]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have hunion : IntegrableOn (fun s : ℝ => (3 + Real.sqrt |s|) / (a^2 + s^2)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    hIoi.union hIic
  rw [Set.Ioi_union_Iic] at hunion
  exact integrableOn_univ.mp hunion

private lemma integral_log_div_sq_le (a : ℝ) (ha : 3/2 < a) :
    (∫ s : ℝ, (1 + Real.log (2 + |s|)) / (a^2 + s^2)) ≤ 20 := by
  have heq : (∫ s : ℝ, (1 + Real.log (2 + |s|)) / (a^2 + s^2))
      = ∫ s : ℝ, (fun x : ℝ => (1 + Real.log (2 + x)) / (a^2 + x^2)) |s| := by
    apply integral_congr_ae
    filter_upwards with s
    simp [sq_abs]
  rw [heq, integral_comp_abs (f := fun x : ℝ => (1 + Real.log (2 + x)) / (a^2 + x^2))]
  have h1 := integral_psi_le a ha
  have h2 := integral_phi_le a ha
  linarith

theorem integral_log_lorentz_le (a b : ℝ) (ha : 3 / 2 < a) :
    (∫ t : ℝ, (Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) ≤
      20 * (Real.log (2 + |b|) + 1) := by
  have ha0 : 0 < a := by linarith
  set K : ℝ := Real.log (2 + |b|) + 1 with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have : 0 ≤ Real.log (2 + |b|) := Real.log_nonneg (by have := abs_nonneg b; linarith)
    linarith
  set M : ℝ → ℝ := fun s => (3 + Real.sqrt |s|) / (a^2 + s^2) with hMdef
  have hMint : Integrable M := integrable_phi_abs a ha
  have hgint : Integrable (fun t : ℝ => K * M (t - b)) := (hMint.comp_sub_right b).const_mul K
  have hle : (fun t : ℝ => (Real.log (2 + |t|) + 1) / (a^2 + (t - b)^2)) ≤ (fun t => K * M (t - b)) := by
    intro t
    have hlog := log_two_add_abs_le t b
    have hlogtb := log_two_add_le_two_add_sqrt |t - b| (abs_nonneg _)
    have hs : 0 ≤ Real.sqrt |t - b| := Real.sqrt_nonneg _
    have hprod : 0 ≤ (K - 1) * (2 + Real.sqrt |t - b|) :=
      mul_nonneg (by linarith) (by linarith)
    have hnum : Real.log (2 + |t|) + 1 ≤ K * (3 + Real.sqrt |t - b|) := by
      nlinarith [hlog, hlogtb, hprod]
    have hden : (0:ℝ) < a^2 + (t-b)^2 := by positivity
    have hgoal : (Real.log (2 + |t|) + 1) / (a^2 + (t - b)^2)
        ≤ K * ((3 + Real.sqrt |t - b|) / (a^2 + (t - b)^2)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hnum hden.le
    simpa [hMdef] using hgoal
  have hfnn : 0 ≤ᵐ[volume] (fun t : ℝ => (Real.log (2 + |t|) + 1) / (a^2 + (t - b)^2)) :=
    Filter.Eventually.of_forall (fun t => div_nonneg (by
      have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by have := abs_nonneg t; linarith); linarith) (by positivity))
  refine le_trans (integral_mono_of_nonneg hfnn hgint (Filter.Eventually.of_forall hle)) ?_
  have hmeq : (∫ s : ℝ, M s) = 2 * ∫ x in Set.Ioi 0, (3 + Real.sqrt x)/(a^2+x^2) := by
    rw [hMdef]
    have hthis : (fun s : ℝ => (3 + Real.sqrt |s|)/(a^2+s^2)) = (fun s => (fun x : ℝ => (3 + Real.sqrt x)/(a^2+x^2)) |s|) := by
      funext s; simp only [sq_abs]
    rw [hthis, integral_comp_abs (f := fun x : ℝ => (3 + Real.sqrt x)/(a^2+x^2))]
  have htr : (∫ t : ℝ, M (t - b)) = ∫ s : ℝ, M s := by
    rw [show (fun t : ℝ => M (t - b)) = (fun t => M (t + (-b))) by funext t; rw [sub_eq_add_neg]]
    exact integral_add_right_eq_self M (-b)
  have hφle := integral_phi_le a ha
  calc (∫ t : ℝ, K * M (t - b))
      = K * ∫ t : ℝ, M (t - b) := integral_const_mul K _
    _ = K * ∫ s : ℝ, M s := by rw [htr]
    _ = K * (2 * ∫ x in Set.Ioi 0, (3 + Real.sqrt x)/(a^2+x^2)) := by rw [hmeq]
    _ ≤ K * (2 * (61/9)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [hφle]
    _ ≤ 20 * K := by
        have hK0 : (0:ℝ) ≤ K := by linarith
        have := mul_le_mul_of_nonneg_left (show (2 * (61/9):ℝ) ≤ 20 by norm_num) hK0
        linarith


end Commons.Analysis.Integral