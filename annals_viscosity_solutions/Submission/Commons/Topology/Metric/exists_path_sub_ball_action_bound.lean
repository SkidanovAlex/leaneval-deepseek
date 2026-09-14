import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Commons.MeasureTheory.Integral.intervalIntegral_rpow_abs_sub_inv_le_six
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat

open Set MeasureTheory intervalIntegral
open scoped BigOperators Topology ENNReal

set_option maxHeartbeats 8000000

namespace Commons.Topology.Metric

private lemma sqrt_add_le_sqrt_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.sqrt a + Real.sqrt b)]
  apply Real.sqrt_le_sqrt
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

private lemma sqrt_abs_sub_le (x y : ℝ) :
    Real.sqrt |x| ≤ Real.sqrt |y| + Real.sqrt |x - y| := by
  have hxy : |x| ≤ |y| + |x - y| := by
    calc |x| = |y + (x - y)| := by ring_nf
      _ ≤ |y| + |x - y| := abs_add_le _ _
  calc Real.sqrt |x| ≤ Real.sqrt (|y| + |x - y|) := Real.sqrt_le_sqrt hxy
    _ ≤ Real.sqrt |y| + Real.sqrt |x - y| :=
        sqrt_add_le_sqrt_add_sqrt |y| |x-y| (abs_nonneg _) (abs_nonneg _)

private noncomputable def hh (A : Finset ℝ) (hA : A.Nonempty) : ℝ → ℝ :=
  fun u => A.inf' hA (fun a => Real.sqrt |u - a|)

private lemma hh_holder (A : Finset ℝ) (hA : A.Nonempty) (u v : ℝ) :
    |hh A hA u - hh A hA v| ≤ Real.sqrt |u - v| := by
  obtain ⟨a₀, ha₀, hmin₀⟩ := Finset.exists_mem_eq_inf' hA (fun a => Real.sqrt |u - a|)
  obtain ⟨a₁, ha₁, hmin₁⟩ := Finset.exists_mem_eq_inf' hA (fun a => Real.sqrt |v - a|)
  have hu : hh A hA u = Real.sqrt |u - a₀| := hmin₀
  have hv : hh A hA v = Real.sqrt |v - a₁| := hmin₁
  rw [hu, hv, abs_sub_le_iff]
  have hle₁ : Real.sqrt |v - a₁| ≤ Real.sqrt |v - a₀| := by
    rw [← hv]; exact Finset.inf'_le _ ha₀
  have hle₂ : Real.sqrt |u - a₀| ≤ Real.sqrt |u - a₁| := by
    rw [← hu]; exact Finset.inf'_le _ ha₁
  have key1 : Real.sqrt |v - a₀| ≤ Real.sqrt |u - a₀| + Real.sqrt |v - u| := by
    have h := sqrt_abs_sub_le (v - a₀) (u - a₀)
    have hd : (v - a₀) - (u - a₀) = v - u := by ring
    rwa [hd] at h
  have key2 : Real.sqrt |u - a₁| ≤ Real.sqrt |v - a₁| + Real.sqrt |u - v| := by
    have h := sqrt_abs_sub_le (u - a₁) (v - a₁)
    have hd : (u - a₁) - (v - a₁) = u - v := by ring
    rwa [hd] at h
  constructor
  · linarith
  · have hcomm : |v - u| = |u - v| := abs_sub_comm v u
    rw [hcomm] at key1; linarith

private lemma hh_cont (A : Finset ℝ) (hA : A.Nonempty) : Continuous (hh A hA) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε^2, by positivity, fun v hv => ?_⟩
  have key := hh_holder A hA u v
  rw [Real.dist_eq, abs_sub_comm]
  have hu : |u - v| = dist v u := by rw [Real.dist_eq, abs_sub_comm]
  calc |hh A hA u - hh A hA v| ≤ Real.sqrt |u - v| := key
    _ < Real.sqrt (ε^2) := Real.sqrt_lt_sqrt (abs_nonneg _) (by rw [hu]; exact hv)
    _ = ε := Real.sqrt_sq hε.le

private lemma hh_nonneg (A : Finset ℝ) (hA : A.Nonempty) (u : ℝ) : 0 ≤ hh A hA u :=
  Finset.le_inf' hA (fun a => Real.sqrt |u - a|) (fun b _ => Real.sqrt_nonneg _)

private lemma hh_le (A : Finset ℝ) (hA : A.Nonempty) (u a : ℝ) (ha : a ∈ A) :
    hh A hA u ≤ Real.sqrt |u - a| :=
  Finset.inf'_le (fun a => Real.sqrt |u - a|) ha

private lemma hh_pos_of_notMem (A : Finset ℝ) (hA : A.Nonempty) (u : ℝ) (hu : u ∉ A) :
    0 < hh A hA u := by
  obtain ⟨a₀, ha₀, hmin₀⟩ := Finset.exists_mem_eq_inf' hA (fun a => Real.sqrt |u - a|)
  have h : hh A hA u = Real.sqrt |u - a₀| := hmin₀
  rw [h]
  apply Real.sqrt_pos.mpr
  rw [abs_pos]
  intro hc
  exact hu (by rw [show u = a₀ by linarith]; exact ha₀)

private lemma hh_eq_zero_of_mem (A : Finset ℝ) (hA : A.Nonempty) (u : ℝ) (hu : u ∈ A) :
    hh A hA u = 0 := by
  have h1 := hh_le A hA u u hu
  rw [sub_self, abs_zero, Real.sqrt_zero] at h1
  exact le_antisymm h1 (hh_nonneg A hA u)

private lemma hh_deriv_thm (A : Finset ℝ) (hA : A.Nonempty) (y : ℝ) :
    HasDerivAt (fun y => ∫ u in (0:ℝ)..y, hh A hA u) (hh A hA y) y := by
  refine intervalIntegral.integral_hasDerivAt_right ((hh_cont A hA).intervalIntegrable 0 y) ?_ ?_
  · exact (hh_cont A hA).stronglyMeasurableAtFilter volume (𝓝 y)
  · exact (hh_cont A hA).continuousAt

private lemma hh_ge_of_le (A : Finset ℝ) (hA : A.Nonempty) (hamax : A.max' hA ≤ 1/2)
    {u : ℝ} (hu : 1/2 ≤ u) :
    Real.sqrt (u - 1/2) ≤ hh A hA u := by
  refine Finset.le_inf' hA (fun a => Real.sqrt |u - a|) (fun b hb => ?_)
  apply Real.sqrt_le_sqrt
  have hb' : b ≤ 1/2 := le_trans (Finset.le_max' A b hb) hamax
  rw [abs_of_nonneg (by linarith)]
  linarith

private lemma abs_rpow_neg_half_le (t : ℝ) :
    |t| ^ (-(1/2):ℝ) ≤ |t| ^ (-(2/3):ℝ) + 1 := by
  by_cases ht : t = 0
  · subst ht; simp
  · have h : 0 < |t| := abs_pos.mpr ht
    have hs1 : (0:ℝ) < |t| ^ (1/2:ℝ) := Real.rpow_pos_of_pos h _
    have key : |t| ^ (-(1/2):ℝ) * |t| ^ (1/2:ℝ)
        ≤ (|t| ^ (-(2/3):ℝ) + 1) * |t| ^ (1/2:ℝ) := by
      rw [← Real.rpow_add h, show (-(1/2):ℝ) + 1/2 = 0 by norm_num, Real.rpow_zero]
      have hL : (|t| ^ (-(2/3):ℝ) + 1) * |t| ^ (1/2:ℝ)
          = |t| ^ (-(2/3) + 1/2:ℝ) + |t| ^ (1/2:ℝ) := by
        rw [add_mul, one_mul, ← Real.rpow_add h]
      rw [hL, show (-(2/3):ℝ) + 1/2 = -(1/6) by norm_num]
      rcases le_total 1 |t| with h2 | h2
      · have h3 : (1:ℝ) ≤ |t| ^ (1/2:ℝ) := Real.one_le_rpow h2 (by norm_num)
        have h4 : (0:ℝ) ≤ |t| ^ (-(1/6):ℝ) := Real.rpow_nonneg (abs_nonneg _) _
        linarith
      · have h3 : (1:ℝ) ≤ (|t|⁻¹) ^ (1/6:ℝ) :=
          Real.one_le_rpow ((one_le_inv₀ h).mpr h2) (by norm_num)
        rw [Real.inv_rpow h.le, ← Real.rpow_neg (abs_nonneg t) (1/6)] at h3
        have h4 : (0:ℝ) ≤ |t| ^ (1/2:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
        linarith
    exact le_of_mul_le_mul_right key hs1

private lemma rpow_three_halves_half : ((1/2:ℝ)) ^ (3/2:ℝ) = (Real.sqrt 2) / 4 := by
  rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 1/2),
      Real.rpow_one, show (1/2:ℝ) = 2⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow]
  have h : (2:ℝ) ^ (1/2:ℝ) * 2 ^ (1/2:ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  have hpos : (0:ℝ) < 2 ^ (1/2:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  field_simp
  linarith [h]

set_option maxHeartbeats 1000000 in
theorem exists_holder_parametrisation_finset (A : Finset ℝ) (hA : A.Nonempty)
    (ha : ∀ a ∈ A, |a| ≤ 1 / 2) :
    ∃ F : ℝ → ℝ, F 0 = 0 ∧ F 1 = 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, F t ∈ Set.Icc (0 : ℝ) 1) ∧
      AbsolutelyContinuousOnInterval F 0 1 ∧
      IntervalIntegrable (fun t : ℝ => (deriv F t) ^ 2) volume (0 : ℝ) 1 ∧
      (∀ a ∈ A, ∃ b : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 : ℝ) * |t - b| ^ (2 / 3 : ℝ) ≤ |F t - a|) ∧
      ∫ t in (0 : ℝ)..1, (deriv F t) ^ 2 ≤ 100 * (A.card : ℝ) := by
  have hamax : A.max' hA ≤ 1 / 2 := (abs_le.mp (ha _ (Finset.max'_mem A hA))).2
  have hamin : -(1 / 2 : ℝ) ≤ A.max' hA := (abs_le.mp (ha _ (Finset.max'_mem A hA))).1
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∫ u in (0 : ℝ)..1, hh A hA u := ⟨_, rfl⟩
  have hSpos : 0 < S := by
    rw [hSdef]
    refine intervalIntegral.integral_pos (by norm_num) (hh_cont A hA).continuousOn
      (fun x _ => hh_nonneg A hA x) ?_
    obtain ⟨c, hc, hcA⟩ := (Set.Icc_infinite (show (0:ℝ) < 1 by norm_num)).exists_notMem_finset A
    exact ⟨c, hc, hh_pos_of_notMem A hA c hcA⟩
  have hSupper : S ≤ Real.sqrt (3 / 2) := by
    rw [hSdef]
    have hb : ∀ u ∈ Set.Icc (0:ℝ) 1, hh A hA u ≤ Real.sqrt (3 / 2) := by
      intro u hu
      refine le_trans (hh_le A hA u (A.max' hA) (Finset.max'_mem A hA)) (Real.sqrt_le_sqrt ?_)
      rw [abs_le]
      exact ⟨by linarith [hamax, hu.1], by linarith [hamin, hu.2]⟩
    calc ∫ u in (0:ℝ)..1, hh A hA u ≤ ∫ u in (0:ℝ)..1, Real.sqrt (3/2) :=
          intervalIntegral.integral_mono_on (by norm_num) ((hh_cont A hA).intervalIntegrable 0 1)
            intervalIntegrable_const hb
      _ = Real.sqrt (3/2) := by rw [intervalIntegral.integral_const]; simp
  have hSlower : (2/3:ℝ) * ((1/2:ℝ)^(3/2:ℝ)) ≤ S := by
    rw [hSdef]
    have hcont' : Continuous (fun u : ℝ => Real.sqrt (u - 1/2)) :=
      Real.continuous_sqrt.comp (continuous_id.sub continuous_const)
    have h4 : ∫ u in (1/2:ℝ)..1, Real.sqrt (u - 1/2) = (2/3:ℝ) * ((1/2:ℝ)^(3/2:ℝ)) := by
      rw [intervalIntegral.integral_comp_sub_right (fun v => Real.sqrt v) (1/2)]
      rw [show (1/2:ℝ) - 1/2 = 0 by norm_num, show (1:ℝ) - 1/2 = 1/2 by norm_num]
      rw [show (fun v : ℝ => Real.sqrt v) = (fun v => v ^ (1/2:ℝ)) by
            funext v; exact Real.sqrt_eq_rpow v]
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < 1/2))]
      rw [show (1/2:ℝ) + 1 = 3/2 by norm_num, Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)]
      ring
    rw [← h4]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hh_cont A hA).intervalIntegrable 0 (1/2)) ((hh_cont A hA).intervalIntegrable (1/2) 1)]
    have h2 : 0 ≤ ∫ u in (0:ℝ)..(1/2), hh A hA u :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => hh_nonneg A hA u)
    have h3 : ∫ u in (1/2:ℝ)..1, Real.sqrt (u - 1/2) ≤ ∫ u in (1/2:ℝ)..1, hh A hA u :=
      intervalIntegral.integral_mono_on (by norm_num) (hcont'.intervalIntegrable (1/2) 1)
        ((hh_cont A hA).intervalIntegrable (1/2) 1)
        (fun u hu => hh_ge_of_le A hA hamax hu.1)
    linarith
  have hSle : S ≤ 3 / 2 := (le_trans hSupper (by rw [Real.sqrt_le_iff]; norm_num))
  -- H
  let H : ℝ → ℝ := fun y => (∫ u in (0:ℝ)..y, hh A hA u) / S
  have hH0 : H 0 = 0 := by
    show (∫ u in (0:ℝ)..0, hh A hA u) / S = 0
    simp
  have hH1 : H 1 = 1 := by
    show (∫ u in (0:ℝ)..1, hh A hA u) / S = 1
    rw [← hSdef]
    exact div_self (ne_of_gt hSpos)
  have hHcont : Continuous H := by
    have h1 : Continuous (fun y : ℝ => ∫ u in (0:ℝ)..y, hh A hA u) :=
      intervalIntegral.continuous_primitive (fun a b => (hh_cont A hA).intervalIntegrable a b) 0
    exact h1.div_const S
  have hHderiv : ∀ y : ℝ, HasDerivAt H (hh A hA y / S) y := by
    intro y
    have h1 := hh_deriv_thm A hA y
    exact h1.div_const S
  have hHmono : StrictMono H := by
    intro y z hyz
    have hpos : 0 < ∫ u in y..z, hh A hA u := by
      refine intervalIntegral.integral_pos hyz (hh_cont A hA).continuousOn
        (fun x _ => hh_nonneg A hA x) ?_
      obtain ⟨c, hc, hcA⟩ := (Set.Icc_infinite hyz).exists_notMem_finset A
      exact ⟨c, hc, hh_pos_of_notMem A hA c hcA⟩
    have hkey : H z - H y = (∫ u in y..z, hh A hA u) / S := by
      show (∫ u in (0:ℝ)..z, hh A hA u) / S - (∫ u in (0:ℝ)..y, hh A hA u) / S = _
      rw [div_sub_div_same, intervalIntegral.integral_interval_sub_left
        ((hh_cont A hA).intervalIntegrable 0 z) ((hh_cont A hA).intervalIntegrable 0 y)]
    rw [← sub_pos, hkey]
    exact div_pos hpos hSpos
  have hHinj : Function.Injective H := hHmono.injective
  -- F
  let F : ℝ → ℝ := Function.invFun H
  have hHrange : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∈ Set.range H := by
    intro t ht
    have hsub := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hHcont.continuousOn
    rw [hH0, hH1] at hsub
    obtain ⟨x, -, hx⟩ := hsub ht
    exact ⟨x, hx⟩
  have hHF : ∀ t ∈ Set.Icc (0:ℝ) 1, H (F t) = t := by
    intro t ht
    obtain ⟨x, hx⟩ := hHrange t ht
    exact Function.invFun_eq ⟨x, hx⟩
  have hF0 : F 0 = 0 := by
    refine hHinj ?_
    rw [hHF 0 (by norm_num), hH0]
  have hF1 : F 1 = 1 := by
    refine hHinj ?_
    rw [hHF 1 (by norm_num), hH1]
  have hFmem : ∀ t ∈ Set.Icc (0:ℝ) 1, F t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    have h := hHF t ht
    refine ⟨?_, ?_⟩
    · by_contra hlt
      push_neg at hlt
      have hc := hHmono hlt
      rw [hHF t ht, hH0] at hc
      exact absurd hc (not_lt.mpr ht.1)
    · by_contra hlt
      push_neg at hlt
      have hc := hHmono hlt
      rw [hH1, hHF t ht] at hc
      exact absurd hc (not_lt.mpr ht.2)
  have hHmem : ∀ t ∈ Set.Icc (0:ℝ) 1, H t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · by_contra hc
      push_neg at hc
      rw [← hH0] at hc
      exact absurd ((hHmono.lt_iff_lt).mp hc) (not_lt.mpr ht.1)
    · by_contra hc
      push_neg at hc
      rw [← hH1] at hc
      exact absurd ((hHmono.lt_iff_lt).mp hc) (not_lt.mpr ht.2)
  have hFmono : MonotoneOn F (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    by_contra hcon
    push_neg at hcon
    have h2 : H (F t) < H (F s) := hHmono hcon
    rw [hHF s hs, hHF t ht] at h2
    exact absurd h2 (not_lt.mpr hst)
  have hHholder : ∀ a ∈ A, ∀ y : ℝ, |H y - H a| ≤ (2/(3*S)) * |y - a| ^ (3/2:ℝ) := by
    intro a haA y
    have hsub : H y - H a = (∫ u in a..y, hh A hA u)/S := by
      show (∫ u in (0:ℝ)..y, hh A hA u)/S - (∫ u in (0:ℝ)..a, hh A hA u)/S = _
      rw [div_sub_div_same, intervalIntegral.integral_interval_sub_left
        ((hh_cont A hA).intervalIntegrable 0 y) ((hh_cont A hA).intervalIntegrable 0 a)]
    have hkey : ∀ d : ℝ, a ≤ d → ∫ u in a..d, hh A hA u ≤ (2/3:ℝ) * (d - a)^(3/2:ℝ) := by
      intro d had
      have h1 : ∫ u in a..d, hh A hA u ≤ ∫ u in a..d, Real.sqrt (u - a) :=
        intervalIntegral.integral_mono_on had ((hh_cont A hA).intervalIntegrable a d)
          ((Real.continuous_sqrt.comp (continuous_id.sub continuous_const)).intervalIntegrable a d)
          (fun u hu => by
            simpa [abs_of_nonneg (by linarith [hu.1] : (0:ℝ) ≤ u - a)] using hh_le A hA u a haA)
      have h2 : ∫ u in a..d, Real.sqrt (u - a) = (2/3:ℝ) * (d - a)^(3/2:ℝ) := by
        rw [intervalIntegral.integral_comp_sub_right (fun v => Real.sqrt v) a]
        rw [show a - a = 0 by ring]
        rw [show (fun v : ℝ => Real.sqrt v) = (fun v => v ^ (1/2:ℝ)) by
              funext v; exact Real.sqrt_eq_rpow v]
        rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < 1/2))]
        rw [show (1/2:ℝ) + 1 = 3/2 by norm_num, Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)]
        ring
      linarith
    have hkey' : ∀ d : ℝ, d ≤ a → ∫ u in d..a, hh A hA u ≤ (2/3:ℝ) * (a - d)^(3/2:ℝ) := by
      intro d hda
      have h1 : ∫ u in d..a, hh A hA u ≤ ∫ u in d..a, Real.sqrt (a - u) :=
        intervalIntegral.integral_mono_on hda ((hh_cont A hA).intervalIntegrable d a)
          ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).intervalIntegrable d a)
          (fun u hu => by
            simpa [abs_of_nonpos (by linarith [hu.2] : (u:ℝ) - a ≤ 0)] using hh_le A hA u a haA)
      have h2 : ∫ u in d..a, Real.sqrt (a - u) = (2/3:ℝ) * (a - d)^(3/2:ℝ) := by
        rw [intervalIntegral.integral_comp_sub_left (fun v => Real.sqrt v) a]
        rw [show a - a = 0 by ring]
        rw [show (fun v : ℝ => Real.sqrt v) = (fun v => v ^ (1/2:ℝ)) by
              funext v; exact Real.sqrt_eq_rpow v]
        rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < 1/2))]
        rw [show (1/2:ℝ) + 1 = 3/2 by norm_num, Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0)]
        ring
      linarith
    have hbd : |∫ u in a..y, hh A hA u| ≤ (2/3:ℝ) * |y - a|^(3/2:ℝ) := by
      rcases le_total a y with h | h
      · rw [abs_of_nonneg (intervalIntegral.integral_nonneg h (fun u _ => hh_nonneg A hA u)),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ y - a)]
        exact hkey y h
      · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg h (fun u _ => hh_nonneg A hA u)),
            abs_of_nonpos (by linarith : y - a ≤ 0), neg_sub]
        exact hkey' y h
    rw [hsub, abs_div, abs_of_pos hSpos, div_le_iff₀ hSpos]
    rw [show (2 / (3 * S)) * |y - a| ^ (3/2:ℝ) * S = (2/3) * |y - a| ^ (3/2:ℝ) by
          field_simp]
    exact hbd
  have hHolderH : ∀ a ∈ A, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (1/2:ℝ) * |t - H a|^(2/3:ℝ) ≤ |F t - a| := by
    intro a haA t ht
    have h1 := hHholder a haA (F t)
    rw [hHF t ht] at h1
    have hS2 : (1/2:ℝ) ≤ (3*S/2)^(2/3:ℝ) := by
      have h3 : (1/2:ℝ)^(3/2:ℝ) ≤ 3*S/2 := by linarith [hSlower]
      have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h3 (by norm_num : (0:ℝ) ≤ 2/3)
      rwa [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2),
           show (3/2:ℝ) * (2/3) = 1 by norm_num, Real.rpow_one] at h4
    have h5 : (3*S/2) * |t - H a| ≤ |F t - a|^(3/2:ℝ) := by
      have h6 : (3*S/2) * |t - H a| ≤ (3*S/2) * ((2/(3*S)) * |F t - a|^(3/2:ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith [hSpos])
      have h7 : (3*S/2) * ((2/(3*S)) * |F t - a|^(3/2:ℝ)) = |F t - a|^(3/2:ℝ) := by
        field_simp
      linarith [h6]
    calc (1/2:ℝ) * |t - H a|^(2/3:ℝ)
        ≤ (3*S/2)^(2/3:ℝ) * |t - H a|^(2/3:ℝ) :=
          mul_le_mul_of_nonneg_right hS2 (Real.rpow_nonneg (abs_nonneg _) _)
      _ = ((3*S/2) * |t - H a|)^(2/3:ℝ) := by
          rw [Real.mul_rpow (by linarith [hSpos] : (0:ℝ) ≤ 3*S/2) (abs_nonneg _)]
      _ ≤ (|F t - a|^(3/2:ℝ))^(2/3:ℝ) :=
          Real.rpow_le_rpow (by positivity) h5 (by norm_num)
      _ = |F t - a| := by
          rw [← Real.rpow_mul (abs_nonneg _), show (3/2:ℝ)*(2/3) = 1 by norm_num, Real.rpow_one]
  have hHolder : ∀ a ∈ A, ∃ b : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (1/2:ℝ) * |t - b|^(2/3:ℝ) ≤ |F t - a| :=
    fun a ha => ⟨H a, hHolderH a ha⟩
  -- Measurability of F via a monotone extension
  let Fc : ℝ → ℝ := fun u => F (min 1 (max 0 u))
  have hFc_mono : Monotone Fc := by
    intro u v huv
    have h1 : min 1 (max 0 u) ≤ min 1 (max 0 v) :=
      min_le_min le_rfl (max_le_max le_rfl huv)
    exact hFmono ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
      ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩ h1
  have hFc_eq : ∀ u ∈ Set.Icc (0:ℝ) 1, Fc u = F u := by
    intro u hu
    show F (min 1 (max 0 u)) = F u
    rw [max_eq_right hu.1, min_eq_right hu.2]
  let ψ : ℝ → ℝ := fun u => S / hh A hA (Fc u)
  have hψm : Measurable ψ :=
    Measurable.div measurable_const ((hh_cont A hA).measurable.comp hFc_mono.measurable)
  have hψ_nonneg : ∀ u, 0 ≤ ψ u :=
    fun u => div_nonneg hSpos.le (hh_nonneg A hA _)
  have hψeq : ∀ x ∈ Set.Icc (0:ℝ) 1, ψ (H x) = S / hh A hA x := by
    intro x hx
    have hFH : F (H x) = x := hHinj (Function.invFun_eq ⟨x, rfl⟩)
    show S / hh A hA (Fc (H x)) = S / hh A hA x
    rw [hFc_eq (H x) (hHmem x hx), hFH]
  have hsub : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∫ x in (0:ℝ)..F t, ψ (H x) * (hh A hA x / S)) = ∫ u in (0:ℝ)..t, ψ u := by
    intro t ht
    have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := H) (f' := fun x => hh A hA x / S) (g := ψ) (a := 0) (b := F t)
      hHcont.continuousOn
      (fun x _ => hHderiv x)
      (fun x _ => div_nonneg (hh_nonneg A hA x) hSpos.le)
    rw [hH0, hHF t ht] at key
    exact key
  have hFprim : ∀ t ∈ Set.Icc (0:ℝ) 1, F t = ∫ u in (0:ℝ)..t, ψ u := by
    intro t ht
    have hFt0 : 0 ≤ F t := (hFmem t ht).1
    have hFt1 : F t ≤ 1 := (hFmem t ht).2
    have hAae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ (A : Set ℝ) := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ∉ (A : Set ℝ)} = (A : Set ℝ) := by ext a; simp
      rw [this]
      exact A.finite_toSet.measure_zero volume
    have hcongr : ∫ x in (0:ℝ)..F t, ψ (H x) * (hh A hA x / S) = ∫ x in (0:ℝ)..F t, (1:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hAae] with x hxA hx
      rw [Set.uIoc_of_le hFt0] at hx
      have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, le_trans hx.2 hFt1⟩
      rw [hψeq x hxI]
      have hnev : hh A hA x ≠ 0 := ne_of_gt (hh_pos_of_notMem A hA x hxA)
      field_simp
    have hsub' := hsub t ht
    rw [hcongr, intervalIntegral.integral_const] at hsub'
    simpa using hsub'
  -- ψ is interval integrable
  have hψint : IntervalIntegrable ψ volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff]
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have h1 : ∫ a, ψ a ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) = 1 := by
      have hF1' := hFprim 1 (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)
      rw [hF1] at hF1'
      have h4 : ∫ a in Set.Ioc (0:ℝ) 1, ψ a = ∫ u in (0:ℝ)..1, ψ u :=
        (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm
      rw [h4, ← hF1']
    refine ⟨hψm.aestronglyMeasurable.restrict, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h2 : ∫⁻ a, ‖ψ a‖ₑ ∂(volume.restrict (Set.Ioc (0:ℝ) 1))
        = ∫⁻ a, ENNReal.ofReal (ψ a) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      lintegral_congr fun a => Real.enorm_eq_ofReal (hψ_nonneg a)
    rw [h2, lt_top_iff_ne_top]
    intro hcon
    have h3 := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (Filter.Eventually.of_forall hψ_nonneg) hψm.aestronglyMeasurable
    rw [hcon] at h3
    simp only [ENNReal.toReal_top] at h3
    linarith [h1, h3]
  -- F is absolutely continuous on [0,1]
  have hFAC : AbsolutelyContinuousOnInterval F 0 1 := by
    have hprim : AbsolutelyContinuousOnInterval (fun t => ∫ u in (0:ℝ)..t, ψ u) 0 1 :=
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral hψint
        (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_rfl, by norm_num⟩)
    rw [absolutelyContinuousOnInterval_iff] at hprim ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := hprim ε hε
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have hsum : ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2)
        = ∑ i ∈ Finset.range E.1,
            dist ((fun t => ∫ u in (0:ℝ)..t, ψ u) (E.2 i).1)
                 ((fun t => ∫ u in (0:ℝ)..t, ψ u) (E.2 i).2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h1 : (E.2 i).1 ∈ Set.Icc (0:ℝ) 1 := by
        have := (hE.1 i hi).1
        rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
      have h2 : (E.2 i).2 ∈ Set.Icc (0:ℝ) 1 := by
        have := (hE.1 i hi).2
        rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
      rw [hFprim _ h1, hFprim _ h2]
    rw [hsum]
    exact hδp E hE hlen
  -- derivative of F is ψ a.e.
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioo (0:ℝ) 1 → deriv F x = ψ x := by
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hψint] with x hx hxI
    have hxIccU : x ∈ Set.uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨hxI.1.le, hxI.2.le⟩
    have hd : HasDerivAt (fun t => ∫ u in (0:ℝ)..t, ψ u) (ψ x) x :=
      hx hxIccU 0 (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_rfl, by norm_num⟩)
    have heq : F =ᶠ[𝓝 x] (fun t => ∫ u in (0:ℝ)..t, ψ u) := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with t ht
      exact hFprim t ⟨ht.1.le, ht.2.le⟩
    exact (hd.congr_of_eventuallyEq heq).deriv
  have hMAJle : ∀ x ∈ Set.Icc (0:ℝ) 1, 1 / hh A hA x
      ≤ ∑ a ∈ A, (|x - a| ^ (-(2/3):ℝ) + 1) := by
    intro x hx
    obtain ⟨a₀, ha₀, hmin₀⟩ := Finset.exists_mem_eq_inf' hA (fun a => Real.sqrt |x - a|)
    have h1 : hh A hA x = Real.sqrt |x - a₀| := hmin₀
    rw [h1, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (abs_nonneg (x - a₀)) (1/2)]
    calc |x - a₀| ^ (-(1/2):ℝ) ≤ ∑ a ∈ A, |x - a| ^ (-(1/2):ℝ) :=
          Finset.single_le_sum (fun a _ => Real.rpow_nonneg (abs_nonneg _) _) ha₀
      _ ≤ ∑ a ∈ A, (|x - a| ^ (-(2/3):ℝ) + 1) :=
          Finset.sum_le_sum (fun a _ => by
            have := abs_rpow_neg_half_le (x - a)
            linarith)
  have hbase_int : ∀ a : ℝ, IntervalIntegrable
      (fun x => |x - a| ^ (-(2/3):ℝ)) volume (0:ℝ) 1 := by
    intro a
    have h2 : IntervalIntegrable (fun x : ℝ => |x| ^ (-(2/3):ℝ)) volume (-a) (1 - a) :=
      Commons.MeasureTheory.Integral.intervalIntegrable_abs_rpow (-(2/3)) (by norm_num) _ _
    have h3 := h2.comp_sub_right a
    rw [show -a + a = 0 by ring, show 1 - a + a = 1 by ring] at h3
    exact h3
  have hterm_int : ∀ a : ℝ, IntervalIntegrable
      (fun x => |x - a| ^ (-(2/3):ℝ) + 1) volume (0:ℝ) 1 :=
    fun a => (hbase_int a).add intervalIntegrable_const
  have hMAJint : IntervalIntegrable
      (fun x => ∑ a ∈ A, (|x - a| ^ (-(2/3):ℝ) + 1)) volume (0:ℝ) 1 := by
    have this : IntervalIntegrable (∑ a ∈ A, fun x => |x - a| ^ (-(2/3):ℝ) + 1) volume (0:ℝ) 1 :=
      IntervalIntegrable.sum A (fun a _ => hterm_int a)
    rw [show (∑ a ∈ A, fun x => |x - a| ^ (-(2/3):ℝ) + 1)
        = fun x => ∑ a ∈ A, (|x - a| ^ (-(2/3):ℝ) + 1) from
        funext fun x => Finset.sum_apply x A (fun a x => |x - a| ^ (-(2/3):ℝ) + 1)] at this
    exact this
  have hMAJbd : ∫ x in (0:ℝ)..1, (∑ a ∈ A, (|x - a| ^ (-(2/3):ℝ) + 1)) ≤ 7 * (A.card:ℝ) := by
    rw [intervalIntegral.integral_finsetSum (s := A) (f := fun a x => |x - a| ^ (-(2/3):ℝ) + 1)
      (fun a _ => hterm_int a)]
    have h2 : ∀ a ∈ A, ∫ x in (0:ℝ)..1, (|x - a| ^ (-(2/3):ℝ) + 1) ≤ 7 := by
      intro a ha
      have hsplit : ∫ x in (0:ℝ)..1, (|x - a| ^ (-(2/3):ℝ) + 1)
          = (∫ x in (0:ℝ)..1, |x - a| ^ (-(2/3):ℝ)) + 1 := by
        rw [intervalIntegral.integral_add (hbase_int a) intervalIntegrable_const,
            intervalIntegral.integral_const]
        norm_num
      rw [hsplit]
      have h3 : ∫ x in (0:ℝ)..1, |x - a| ^ (-(2/3):ℝ) ≤ 6 := by
        have h4 := Commons.MeasureTheory.Integral.intervalIntegral_rpow_abs_sub_inv_le_six a
        rw [show (∫ x in (0:ℝ)..1, |x - a| ^ (-(2/3):ℝ))
            = ∫ x in (0:ℝ)..1, ((|x - a| ^ (2/3:ℝ)))⁻¹ from
              intervalIntegral.integral_congr (fun t _ => Real.rpow_neg (abs_nonneg _) (2/3))]
        exact h4
      linarith
    calc ∑ a ∈ A, ∫ x in (0:ℝ)..1, (|x - a| ^ (-(2/3):ℝ) + 1)
        ≤ ∑ a ∈ A, 7 := Finset.sum_le_sum h2
      _ = 7 * (A.card:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h2int : IntervalIntegrable (fun x => 1 / hh A hA x) volume (0:ℝ) 1 := by
    refine IntervalIntegrable.mono_fun' hMAJint ?_ ?_
    · have : (fun x => 1 / hh A hA x) = (hh A hA)⁻¹ := funext fun x => one_div _
      rw [this]
      exact (hh_cont A hA).measurable.inv.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
      have hnn : (0:ℝ) ≤ 1 / hh A hA x := div_nonneg zero_le_one (hh_nonneg A hA x)
      rw [Real.norm_of_nonneg hnn]
      exact hMAJle x hxI
  have hsubst : ∫ t in (0:ℝ)..1, (ψ t)^2 = S * ∫ x in (0:ℝ)..1, (1 / hh A hA x) := by
    have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := H) (f' := fun x => hh A hA x / S) (g := fun u => (ψ u)^2) (a := 0) (b := F 1)
      hHcont.continuousOn (fun x _ => hHderiv x)
      (fun x _ => div_nonneg (hh_nonneg A hA x) hSpos.le)
    rw [hF1, hH0, hH1] at key
    simp only [Function.comp_apply] at key
    rw [← key]
    have hAae2 : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ (A : Set ℝ) := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ∉ (A : Set ℝ)} = (A : Set ℝ) := by ext a; simp
      rw [this]
      exact A.finite_toSet.measure_zero volume
    have hcongr : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0:ℝ) 1 →
        ψ (H x) ^ 2 * (hh A hA x / S) = S * (1 / hh A hA x) := by
      filter_upwards [hAae2] with x hxA hx2
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx2
      have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx2.1.le, hx2.2⟩
      rw [hψeq x hxI]
      have hnev : hh A hA x ≠ 0 := ne_of_gt (hh_pos_of_notMem A hA x hxA)
      field_simp
    rw [intervalIntegral.integral_congr_ae hcongr, intervalIntegral.integral_const_mul]
  have henergy : ∫ t in (0:ℝ)..1, (deriv F t)^2 ≤ 100 * (A.card:ℝ) := by
    have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ≠ 1} = {1} := by ext a; simp
      rw [this]
      exact measure_singleton 1
    have heq : ∫ t in (0:ℝ)..1, (deriv F t)^2 = ∫ t in (0:ℝ)..1, (ψ t)^2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv, hne1] with x hx hx1 hxI
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hxI
      rw [hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩]
    rw [heq, hsubst]
    have hb : ∫ x in (0:ℝ)..1, (1 / hh A hA x) ≤ 7 * (A.card:ℝ) :=
      le_trans (intervalIntegral.integral_mono_on (by norm_num) h2int hMAJint hMAJle) hMAJbd
    have hq : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, (1 / hh A hA x) :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun x _ => div_nonneg zero_le_one (hh_nonneg A hA x))
    have h1 : S * ∫ x in (0:ℝ)..1, (1 / hh A hA x) ≤ (3/2) * (7 * (A.card:ℝ)) :=
      mul_le_mul hSle hb hq (by norm_num)
    linarith
  have hpsibd : ∀ u ∈ Set.Icc (0:ℝ) 1,
      (ψ u)^2 ≤ 2 * S^2 * ∑ a ∈ A, (|u - H a|^(2/3:ℝ))⁻¹ := by
    intro u hu
    obtain ⟨a₀, ha₀, hmin₀⟩ := Finset.exists_mem_eq_inf' hA (fun a => Real.sqrt |F u - a|)
    have hcusp : (1/2:ℝ) * |u - H a₀|^(2/3:ℝ) ≤ |F u - a₀| := hHolderH a₀ ha₀ u hu
    have hmin₀' : hh A hA (F u) = Real.sqrt |F u - a₀| := hmin₀
    rcases eq_or_lt_of_le (Real.rpow_nonneg (abs_nonneg _) (2/3:ℝ)) with hz | hpos
    · have hza : |u - H a₀| = 0 := by
        by_contra hne
        have hne' : u - H a₀ ≠ 0 := by
          intro hc; exact hne (by rw [hc, abs_zero])
        have hpos' : 0 < |u - H a₀| := abs_pos.mpr hne'
        have h3 : 0 < |u - H a₀| ^ (2/3:ℝ) := Real.rpow_pos_of_pos hpos' (2/3:ℝ)
        rw [← hz] at h3
        exact lt_irrefl (0:ℝ) h3
      have huH : u = H a₀ := by
        have h4 := abs_eq_zero.mp hza; linarith
      have hFH : F (H a₀) = a₀ := hHinj (Function.invFun_eq ⟨a₀, rfl⟩)
      have hzero : ψ u = 0 := by
        show S / hh A hA (Fc u) = 0
        rw [hFc_eq u hu, huH, hFH, hh_eq_zero_of_mem A hA a₀ ha₀, div_zero]
      rw [hzero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Real.rpow_nonneg (abs_nonneg _) _)))
    · have heq : 2 * S^2 * (|u - H a₀|^(2/3:ℝ))⁻¹ = S^2 / ((1/2) * |u - H a₀|^(2/3:ℝ)) := by
        field_simp [hpos.ne']
      have hψu : ψ u = S / Real.sqrt |F u - a₀| := by
        show S / hh A hA (Fc u) = S / Real.sqrt |F u - a₀|
        rw [hFc_eq u hu]
        exact congrArg (fun z => S / z) hmin₀'
      have hsum_le : (|u - H a₀|^(2/3:ℝ))⁻¹ ≤ ∑ a ∈ A, (|u - H a|^(2/3:ℝ))⁻¹ :=
        Finset.single_le_sum (f := fun a => (|u - H a|^(2/3:ℝ))⁻¹)
          (fun a _ => inv_nonneg.mpr (Real.rpow_nonneg (abs_nonneg _) _)) ha₀
      have h2 : (ψ u)^2 ≤ 2 * S^2 * (|u - H a₀|^(2/3:ℝ))⁻¹ := by
        rw [hψu, div_pow, Real.sq_sqrt (abs_nonneg _), heq]
        exact div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hpos) hcusp
      exact le_trans h2 (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hψ2int : IntervalIntegrable (fun u => (ψ u)^2) volume (0:ℝ) 1 := by
    have hmaj : IntervalIntegrable
        (fun u => 2 * S^2 * ∑ a ∈ A, (|u - H a|^(2/3:ℝ))⁻¹) volume (0:ℝ) 1 := by
      have hkey : ∀ a ∈ A,
          IntervalIntegrable (fun u => (|u - H a|^(2/3:ℝ))⁻¹) volume (0:ℝ) 1 := by
        intro a _
        have h0 : IntervalIntegrable (fun u : ℝ => |u - H a| ^ (-(2/3):ℝ)) volume (0:ℝ) 1 :=
          hbase_int (H a)
        rwa [show (fun u : ℝ => |u - H a| ^ (-(2/3):ℝ)) = (fun u => (|u - H a|^(2/3:ℝ))⁻¹)
          from by funext u; exact Real.rpow_neg (abs_nonneg _) (2/3)] at h0
      have hthis := IntervalIntegrable.sum A (f := fun a u => (|u - H a|^(2/3:ℝ))⁻¹) hkey
      rw [show (∑ a ∈ A, fun u => (|u - H a|^(2/3:ℝ))⁻¹)
          = (fun u => ∑ a ∈ A, (|u - H a|^(2/3:ℝ))⁻¹) from
          funext fun u => Finset.sum_apply u A (fun a u => (|u - H a|^(2/3:ℝ))⁻¹)] at hthis
      exact hthis.const_mul (2 * S^2)
    refine IntervalIntegrable.mono_fun' hmaj ?_ ?_
    · exact (hψm.pow_const 2).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with u hu
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpsibd u ⟨hu.1.le, hu.2⟩
  have hderiv_sq_int : IntervalIntegrable (fun t => (deriv F t)^2) volume (0:ℝ) 1 := by
    refine hψ2int.congr_ae ?_
    rw [show Set.uIoc (0:ℝ) 1 = Set.Ioc (0:ℝ) 1 from Set.uIoc_of_le (by norm_num)]
    change (fun t : ℝ => (ψ t)^2) =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)]
      (fun t : ℝ => (deriv F t)^2)
    have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ≠ 1} = {1} := by ext a; simp
      rw [this]
      exact measure_singleton 1
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderiv, hne1] with x hx hx1 hxI
    rw [hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩]
  exact ⟨F, hF0, hF1, hFmem, hFAC, hderiv_sq_int, hHolder, henergy⟩

private lemma norm_add_smul_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (c : ℝ) : ‖v‖ * |c + inner ℝ u v / ‖v‖ ^ 2| ≤ ‖u + c • v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hv2pos : 0 < ‖v‖ ^ 2 := by positivity
  have hR : 0 ≤ ‖u + c • v‖ := norm_nonneg _
  have hL : 0 ≤ ‖v‖ * |c + inner ℝ u v / ‖v‖ ^ 2| := by positivity
  have hkey : ‖u + c • v‖ ^ 2 = ‖u‖ ^ 2 + 2 * c * inner ℝ u v + c ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsq : (‖v‖ * |c + inner ℝ u v / ‖v‖ ^ 2|) ^ 2 ≤ ‖u + c • v‖ ^ 2 := by
    rw [hkey, mul_pow, sq_abs]
    have hexp : (‖v‖ ^ 2 * (c + inner ℝ u v / ‖v‖ ^ 2) ^ 2)
        = ‖v‖ ^ 2 * c ^ 2 + 2 * c * inner ℝ u v + (inner ℝ u v) ^ 2 / ‖v‖ ^ 2 := by
      field_simp
      ring
    rw [hexp]
    have hcs : (inner ℝ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      have h := real_inner_mul_inner_self_le u v
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
      nlinarith [h]
    have := (div_le_iff₀ hv2pos).mpr hcs
    linarith
  have h1 := sq_le_sq.mp hsq
  rw [abs_of_nonneg hL, abs_of_nonneg hR] at h1
  exact h1

private theorem ac_congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) (heq : ∀ x ∈ Set.uIcc a b, f x = g x) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hprop⟩ := h ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  rw [AbsolutelyContinuousOnInterval.disjWithin] at hE
  have hsum : ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)
      = ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq _ (hE.1 i hi).1, heq _ (hE.1 i hi).2]
  rw [← hsum]
  exact hprop E hE hlen

private theorem intervalIntegrable_of_comp_sub_left {g : ℝ → ℝ} {a b c : ℝ}
    (h : IntervalIntegrable (fun x => g (c - x)) volume (c - b) (c - a)) :
    IntervalIntegrable g volume a b := by
  rw [← IntervalIntegrable.comp_sub_left_iff (f := g) (a := a) (b := b) c]
  exact h.symm

private theorem ae_comp_sub_left' {P : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), P x) (c : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), P (c - x) :=
  (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℝ) c).ae h

private lemma ac_const {X : Type*} [PseudoMetricSpace X] (c : X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  ((LipschitzWith.const c).lipschitzOnWith).absolutelyContinuousOnInterval

theorem exists_path_sub_ball_action_bound :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
        {N : ℕ} (m : Fin N → ℝ) (hm : ∀ i, 0 < m i) (s : Finset (Fin N))
        (x y : EuclideanSpace E (Fin N)) (r₀ : E) {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ)
        (hx : ∀ i ∈ s, dist (x i) r₀ ≤ R) (hy : ∀ i ∈ s, dist (y i) r₀ ≤ R)
        (hout : ∀ i ∉ s, y i = x i),
        ∃ γ : ℝ → EuclideanSpace E (Fin N),
          γ 0 = x ∧ γ τ = y ∧
          (∀ t, ∀ i, i ∉ s → γ t i = x i) ∧
          (∀ t, ∀ i, i ∈ s → dist (γ t i) r₀ ≤ 7 * (N : ℝ) * R) ∧
          AbsolutelyContinuousOnInterval γ 0 τ ∧
          (∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
              t ∈ Set.Ioc 0 τ → ∀ i ∈ s, ∀ j ∈ s, i ≠ j → γ t i ≠ γ t j) ∧
          MeasureTheory.IntegrableOn
            (fun t => (1 / 2) * (∑ i ∈ s, m i * ‖deriv γ t i‖ ^ 2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                    m i * m j * (dist (γ t i) (γ t j))⁻¹))
            (Set.Ioc 0 τ) ∧
          (∫ t in (0 : ℝ)..τ, ((1 / 2) * (∑ i ∈ s, m i * ‖deriv γ t i‖ ^ 2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                    m i * m j * (dist (γ t i) (γ t j))⁻¹)))
            ≤ c₁ * (∑ i ∈ s, m i) * (N : ℝ) ^ 4 * R ^ 2 / τ
                + c₂ * (∑ i ∈ s, m i) ^ 2 * (N : ℝ) ^ 4 * τ / R := by
  refine ⟨100000, 10, by norm_num, by norm_num, ?_⟩
  intro E _ _ _ N m hm s x y r₀ R τ hR hτ hx hy hout
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hs0 : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i => Fin.elim0 i)
    refine ⟨fun _ => x, rfl, Subsingleton.elim x y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t i hi
      rfl
    · intro t i hi
      rw [hs0] at hi
      exact absurd hi (Finset.notMem_empty i)
    · exact ac_const x 0 τ
    · simp [hs0]
    · have hzero : (fun t : ℝ => (1 / 2) * (∑ i ∈ s, m i * ‖(deriv (fun _ : ℝ => x) t) i‖ ^ 2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (((fun _ : ℝ => x) t) i) (((fun _ : ℝ => x) t) j))⁻¹))
          = (fun _ : ℝ => 0) := by
        funext t; rw [hs0]; simp
      rw [hzero]
      exact integrableOn_zero
    · have hzero : (fun t : ℝ => (1 / 2) * (∑ i ∈ s, m i * ‖(deriv (fun _ : ℝ => x) t) i‖ ^ 2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (((fun _ : ℝ => x) t) i) (((fun _ : ℝ => x) t) j))⁻¹))
          = (fun _ : ℝ => 0) := by
        funext t; rw [hs0]; simp
      rw [hzero, intervalIntegral.integral_zero]
      rw [hs0]
      simp

  · have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : E, w₀ ≠ 0 := exists_ne 0
    have hw₀pos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
    let w : E := ‖w₀‖⁻¹ • w₀
    have hwnorm : ‖w‖ = 1 := by
      show ‖‖w₀‖⁻¹ • w₀‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw₀pos.le),
        inv_mul_cancel₀ (ne_of_gt hw₀pos)]
    let vv : E := (6 * R) • w
    have hvnorm : ‖vv‖ = 6 * R := by
      show ‖(6 * R) • w‖ = 6 * R
      rw [norm_smul, Real.norm_of_nonneg (by positivity), hwnorm, mul_one]
    let qq : EuclideanSpace E (Fin N) :=
      WithLp.toLp 2 (fun i => if i ∈ s then r₀ + ((i : ℕ) : ℝ) • vv else x i)
    have hqq_s : ∀ i ∈ s, qq i = r₀ + ((i:ℕ):ℝ) • vv := by
      intro i hi
      show (WithLp.toLp 2 (fun i => if i ∈ s then r₀ + ((i : ℕ) : ℝ) • vv else x i)) i = _
      rw [WithLp.ofLp_toLp]
      simp [hi]
    have hqq_not : ∀ i ∉ s, qq i = x i := by
      intro i hi
      show (WithLp.toLp 2 (fun i => if i ∈ s then r₀ + ((i : ℕ) : ℝ) • vv else x i)) i = _
      rw [WithLp.ofLp_toLp]
      simp [hi]
    let dirX : Fin N → Fin N → E := fun i j => (qq i - x i) - (qq j - x j)
    let dirY : Fin N → Fin N → E := fun i j => (qq i - y i) - (qq j - y j)
    let tX : Fin N → Fin N → ℝ := fun i j => -(inner ℝ (x i - x j) (dirX i j)) / ‖dirX i j‖^2
    let tY : Fin N → Fin N → ℝ := fun i j => -(inner ℝ (y i - y j) (dirY i j)) / ‖dirY i j‖^2
    let fv : Fin N × Fin N × Bool → ℝ := fun p =>
      if p.1 ∈ s ∧ p.2.1 ∈ s ∧ p.1 ≠ p.2.1 then
        (if p.2.2 then tY p.1 p.2.1 else tX p.1 p.2.1) else 0
    let A : Finset ℝ := insert 0 ((Finset.univ : Finset (Fin N × Fin N × Bool)).image fv)
    have hAne : A.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    have hAcard : (A.card : ℝ) ≤ 2 * (N:ℝ)^2 + 1 := by
      have h3 : (Finset.univ : Finset (Fin N × Fin N × Bool)).card = 2 * N * N := by
        simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm, mul_assoc]
      have h1 : A.card ≤ 2 * N * N + 1 := by
        have h2 : A.card ≤ ((Finset.univ : Finset (Fin N × Fin N × Bool)).image fv).card + 1 :=
          Finset.card_insert_le _ _
        have h4 : ((Finset.univ : Finset (Fin N × Fin N × Bool)).image fv).card
            ≤ 2 * N * N := by rw [← h3]; exact Finset.card_image_le
        omega
      calc (A.card : ℝ) ≤ ((2*N*N + 1 : ℕ) : ℝ) := by exact_mod_cast h1
        _ = 2*(N:ℝ)^2 + 1 := by push_cast; ring
    -- geometry
    have hqq_dist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 6 * R ≤ ‖qq i - qq j‖ := by
      intro i hi j hj hij
      have h1 : qq i - qq j = (((i:ℕ):ℝ) - ((j:ℕ):ℝ)) • vv := by
        rw [hqq_s i hi, hqq_s j hj]; module
      rw [h1, norm_smul, Real.norm_eq_abs, hvnorm]
      have h2 : (1:ℝ) ≤ |((i:ℕ):ℝ) - ((j:ℕ):ℝ)| := by
        rcases lt_trichotomy (i:ℕ) (j:ℕ) with hlt | heq | hgt
        · have h5 : ((j:ℕ):ℝ) ≥ ((i:ℕ):ℝ) + 1 := by
            exact_mod_cast (by omega : (j:ℕ) ≥ (i:ℕ) + 1)
          rw [abs_sub_comm]
          linarith [abs_of_nonneg (by linarith : (0:ℝ) ≤ ((j:ℕ):ℝ) - ((i:ℕ):ℝ))]
        · exact absurd (Fin.ext heq) hij
        · have h5 : ((i:ℕ):ℝ) ≥ ((j:ℕ):ℝ) + 1 := by
            exact_mod_cast (by omega : (i:ℕ) ≥ (j:ℕ) + 1)
          linarith [abs_of_nonneg (by linarith : (0:ℝ) ≤ ((i:ℕ):ℝ) - ((j:ℕ):ℝ))]
      nlinarith [h2, hR]
    have hxdist : ∀ i ∈ s, ∀ j ∈ s, ‖x i - x j‖ ≤ 2 * R := by
      intro i hi j hj
      show ‖x i - x j‖ ≤ 2 * R
      rw [← dist_eq_norm]
      have h1 : dist (x i) r₀ ≤ R := hx i hi
      have h2 : dist r₀ (x j) ≤ R := by rw [dist_comm]; exact hx j hj
      have h3 : dist (x i) r₀ + dist r₀ (x j) ≤ 2 * R := by linarith
      exact (dist_triangle (x i) r₀ (x j)).trans h3
    have hydist : ∀ i ∈ s, ∀ j ∈ s, ‖y i - y j‖ ≤ 2 * R := by
      intro i hi j hj
      show ‖y i - y j‖ ≤ 2 * R
      rw [← dist_eq_norm]
      have h1 : dist (y i) r₀ ≤ R := hy i hi
      have h2 : dist r₀ (y j) ≤ R := by rw [dist_comm]; exact hy j hj
      have h3 : dist (y i) r₀ + dist r₀ (y j) ≤ 2 * R := by linarith
      exact (dist_triangle (y i) r₀ (y j)).trans h3
    have hdirXn : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 4 * R ≤ ‖dirX i j‖ := by
      intro i hi j hj hij
      have h1 : dirX i j = (qq i - qq j) - (x i - x j) := by
        show (qq i - x i) - (qq j - x j) = _; abel
      have h5 : ‖qq i - qq j‖ - ‖x i - x j‖ ≤ ‖dirX i j‖ := by
        have h6 : ‖qq i - qq j‖ - ‖x i - x j‖ ≤ ‖(qq i - qq j) - (x i - x j)‖ :=
          (abs_le.mp (abs_norm_sub_norm_le (qq i - qq j) (x i - x j))).2
        rwa [h1]
      have h3 := hqq_dist i hi j hj hij
      have h4 := hxdist i hi j hj
      linarith
    have htXb : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → |tX i j| ≤ 1/2 := by
      intro i hi j hj hij
      have hdir : dirX i j ≠ 0 := by
        intro hc
        have hcz : ‖dirX i j‖ = 0 := by rw [hc]; simp
        have := hdirXn i hi j hj hij
        linarith [hR]
      have hpos : 0 < ‖dirX i j‖^2 := by positivity
      show |-(inner ℝ (x i - x j) (dirX i j)) / ‖dirX i j‖^2| ≤ 1/2
      rw [abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
      have hcs : |inner ℝ (x i - x j) (dirX i j)| ≤ ‖x i - x j‖ * ‖dirX i j‖ :=
        abs_real_inner_le_norm _ _
      have h4 := hxdist i hi j hj
      have h3 := hdirXn i hi j hj hij
      have hnn : (0:ℝ) ≤ ‖dirX i j‖ := norm_nonneg _
      have : ‖x i - x j‖ ≤ (1/2) * ‖dirX i j‖ := by linarith
      nlinarith [hcs, h4, h3, hnn, mul_le_mul_of_nonneg_right this hnn, sq_nonneg (R)]
    have htYb : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → |tY i j| ≤ 1/2 := by
      intro i hi j hj hij
      have hdir : dirY i j ≠ 0 := by
        intro hc
        have hcz : ‖dirY i j‖ = 0 := by rw [hc]; simp
        have h1 : dirY i j = (qq i - qq j) - (y i - y j) := by
          show (qq i - y i) - (qq j - y j) = _; abel
        rw [h1] at hcz
        have h3 := hqq_dist i hi j hj hij
        have h4 := hydist i hi j hj
        have := abs_norm_sub_norm_le (qq i - qq j) (y i - y j)
        linarith [(abs_le.mp this).2, hR]
      have hpos : 0 < ‖dirY i j‖^2 := by positivity
      show |-(inner ℝ (y i - y j) (dirY i j)) / ‖dirY i j‖^2| ≤ 1/2
      rw [abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
      have hcs : |inner ℝ (y i - y j) (dirY i j)| ≤ ‖y i - y j‖ * ‖dirY i j‖ :=
        abs_real_inner_le_norm _ _
      have h4 := hydist i hi j hj
      have h2 : dirY i j = (qq i - qq j) - (y i - y j) := by
        show (qq i - y i) - (qq j - y j) = _; abel
      have h3 : 4 * R ≤ ‖dirY i j‖ := by
        rw [h2]
        have := abs_norm_sub_norm_le (qq i - qq j) (y i - y j)
        have h5 := hqq_dist i hi j hj hij
        linarith [(abs_le.mp this).2]
      have hnn : (0:ℝ) ≤ ‖dirY i j‖ := norm_nonneg _
      have : ‖y i - y j‖ ≤ (1/2) * ‖dirY i j‖ := by linarith
      nlinarith [hcs, h4, h3, hnn, mul_le_mul_of_nonneg_right this hnn, sq_nonneg (R)]
    have hAnorm : ∀ a ∈ A, |a| ≤ 1/2 := by
      intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · rw [h]; norm_num
      · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp h
        show |fv p| ≤ 1/2
        by_cases hp : p.1 ∈ s ∧ p.2.1 ∈ s ∧ p.1 ≠ p.2.1
        · rw [show fv p = (if p.2.2 then tY p.1 p.2.1 else tX p.1 p.2.1) from by
                simp only [fv]; rw [if_pos hp]]
          by_cases hb : p.2.2
          · rw [if_pos hb]; exact htYb p.1 hp.1 p.2.1 hp.2.1 hp.2.2
          · rw [if_neg hb]; exact htXb p.1 hp.1 p.2.1 hp.2.1 hp.2.2
        · rw [show fv p = 0 from by simp only [fv]; rw [if_neg hp]]
          norm_num
    -- reparametrisation
    obtain ⟨F, hF0, hF1, hFmem, hFAC, hFint, hFholder, hFenergy⟩ :=
      exists_holder_parametrisation_finset A hAne hAnorm
    let G : EuclideanSpace E (Fin N) → ℝ → EuclideanSpace E (Fin N) := fun a u => a + F u • (qq - a)
    let γ2 : ℝ → EuclideanSpace E (Fin N) := fun t => if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)
    let γ : ℝ → EuclideanSpace E (Fin N) := fun t => if t ≤ 0 then x else if t ≤ τ then γ2 t else y
    have hτ2 : 0 < τ/2 := by linarith
    have hG_app : ∀ a u, G a u = a + F u • (qq - a) := fun a u => rfl
    -- parameter ranges
    have hph1 : ∀ t, 0 ≤ t → t ≤ τ/2 → (2*t/τ) ∈ Set.Icc (0:ℝ) 1 := by
      intro t ht0 ht1
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hτ]; linarith
    have hph2 : ∀ t, τ/2 ≤ t → t ≤ τ → (2 - 2*t/τ) ∈ Set.Icc (0:ℝ) 1 := by
      intro t ht0 ht1
      constructor
      · rw [sub_nonneg, div_le_iff₀ hτ]; linarith
      · have h : (1:ℝ) ≤ 2*t/τ := by rw [one_le_div hτ]; linarith
        linarith
    -- γ agrees with γ2 on [0,τ]
    have hγeq : ∀ t ∈ Set.Icc (0:ℝ) τ, γ t = γ2 t := by
      intro t ht
      show (if t ≤ 0 then x else if t ≤ τ then γ2 t else y) = γ2 t
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        rw [if_pos le_rfl]
        show x = γ2 0
        rw [show γ2 0 = G x 0 from by
              show (if (0:ℝ) ≤ τ/2 then G x (2*0/τ) else G y (2 - 2*0/τ)) = G x 0
              rw [if_pos (by linarith), mul_zero, zero_div]]
        show x = x + F 0 • (qq - x)
        rw [hF0, zero_smul, add_zero]
      · rw [if_neg (not_le.mpr h), if_pos ht.2]
    -- basic properties of γ2
    have hγ2_0 : γ2 0 = x := by
      show (if (0:ℝ) ≤ τ/2 then G x (2*0/τ) else G y (2 - 2*0/τ)) = x
      rw [if_pos (by linarith), mul_zero, zero_div]
      show x + F 0 • (qq - x) = x
      rw [hF0, zero_smul, add_zero]
    have hγ2_τ : γ2 τ = y := by
      show (if τ ≤ τ/2 then G x (2*τ/τ) else G y (2 - 2*τ/τ)) = y
      rw [if_neg (by linarith), show 2 - 2*τ/τ = 0 by rw [mul_div_assoc, div_self (ne_of_gt hτ), mul_one, sub_self]]
      show y + F 0 • (qq - y) = y
      rw [hF0, zero_smul, add_zero]
    have hγ0 : γ 0 = x := by
      show (if (0:ℝ) ≤ 0 then x else if (0:ℝ) ≤ τ then γ2 0 else y) = x
      rw [if_pos le_rfl]
    have hγτ : γ τ = y := by
      show (if τ ≤ 0 then x else if τ ≤ τ then γ2 τ else y) = y
      rw [if_neg (not_le.mpr hτ), if_pos le_rfl, hγ2_τ]
    have hγout : ∀ t, ∀ i, i ∉ s → γ t i = x i := by
      intro t i hi
      by_cases ht : t ≤ 0
      · rw [show γ t = x from by
              show (if t ≤ 0 then x else if t ≤ τ then γ2 t else y) = x
              rw [if_pos ht]]
      · by_cases ht2 : t ≤ τ
        · rw [hγeq t ⟨by linarith, ht2⟩]
          by_cases ht3 : t ≤ τ/2
          · rw [show γ2 t = G x (2*t/τ) from by
                  show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G x (2*t/τ)
                  rw [if_pos ht3]]
            show (x + F (2*t/τ) • (qq - x)) i = x i
            simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hqq_not i hi, sub_self,
              smul_zero, add_zero]
          · rw [show γ2 t = G y (2 - 2*t/τ) from by
                  show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G y (2 - 2*t/τ)
                  rw [if_neg ht3]]
            show (y + F (2 - 2*t/τ) • (qq - y)) i = x i
            simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hqq_not i hi, hout i hi,
              sub_self, smul_zero, add_zero]
        · rw [show γ t = y from by
                show (if t ≤ 0 then x else if t ≤ τ then γ2 t else y) = y
                rw [if_neg ht, if_neg ht2]]
          exact hout i hi
    have hqqnn : ∀ i ∈ s, ‖qq i - r₀‖ ≤ 6 * (N:ℝ) * R := by
      intro i hi
      rw [hqq_s i hi, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hvnorm]
      have hnn : (0:ℝ) ≤ ((i:ℕ):ℝ) := by positivity
      rw [abs_of_nonneg hnn]
      have hle : ((i:ℕ):ℝ) ≤ (N:ℝ) := by
        have := i.isLt
        exact_mod_cast (le_of_lt this)
      nlinarith [hR, hle]
    have hGxnorm : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ i ∈ s, ‖G x u i - r₀‖ ≤ 7 * (N:ℝ) * R := by
      intro u hu i hi
      have hFu := hFmem u hu
      have hkey : G x u i - r₀ = (1 - F u) • (x i - r₀) + F u • (qq i - r₀) := by
        simp only [hG_app, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
        module
      rw [hkey]
      have h1 : ‖(1 - F u) • (x i - r₀)‖ ≤ R := by
        rw [norm_smul, Real.norm_of_nonneg (by linarith [hFu.2])]
        have hb : ‖x i - r₀‖ ≤ R := by rw [← dist_eq_norm]; exact hx i hi
        calc (1 - F u) * ‖x i - r₀‖ ≤ 1 * R :=
              mul_le_mul (by linarith [hFu.1]) hb (norm_nonneg _) (by norm_num)
          _ = R := one_mul _
      have h2 : ‖F u • (qq i - r₀)‖ ≤ 6 * (N:ℝ) * R := by
        rw [norm_smul, Real.norm_of_nonneg hFu.1]
        have hb : ‖qq i - r₀‖ ≤ 6 * (N:ℝ) * R := hqqnn i hi
        calc F u * ‖qq i - r₀‖ ≤ 1 * (6 * (N:ℝ) * R) :=
              mul_le_mul hFu.2 hb (norm_nonneg _) (by linarith)
          _ = 6 * (N:ℝ) * R := one_mul _
      have h3 : ‖(1 - F u) • (x i - r₀) + F u • (qq i - r₀)‖ ≤ R + 6 * (N:ℝ) * R :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
      have h4 : R + 6 * (N:ℝ) * R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
      linarith [h3, h4]
    have hγ2ball : ∀ t ∈ Set.Icc (0:ℝ) τ, ∀ i ∈ s, dist (γ2 t i) r₀ ≤ 7 * (N:ℝ) * R := by
      intro t ht i hi
      rw [dist_eq_norm]
      by_cases ht3 : t ≤ τ/2
      · rw [show γ2 t = G x (2*t/τ) from by
              show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G x (2*t/τ)
              rw [if_pos ht3]]
        exact hGxnorm (2*t/τ) (hph1 t ht.1 ht3) i hi
      · rw [show γ2 t = G y (2 - 2*t/τ) from by
              show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G y (2 - 2*t/τ)
              rw [if_neg ht3]]
        have hu := hph2 t ((not_le.mp ht3).le) ht.2
        have hFu := hFmem (2 - 2*t/τ) hu
        have hyb : ‖y i - r₀‖ ≤ R := by rw [← dist_eq_norm]; exact hy i hi
        have hkey : G y (2 - 2*t/τ) i - r₀
            = (1 - F (2 - 2*t/τ)) • (y i - r₀) + F (2 - 2*t/τ) • (qq i - r₀) := by
          simp only [hG_app, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply]
          module
        rw [hkey]
        have h1 : ‖(1 - F (2 - 2*t/τ)) • (y i - r₀)‖ ≤ R := by
          rw [norm_smul, Real.norm_of_nonneg (by linarith [hFu.2])]
          calc (1 - F (2 - 2*t/τ)) * ‖y i - r₀‖ ≤ 1 * R :=
                mul_le_mul (by linarith [hFu.1]) hyb (norm_nonneg _) (by norm_num)
            _ = R := one_mul _
        have h2 : ‖F (2 - 2*t/τ) • (qq i - r₀)‖ ≤ 6 * (N:ℝ) * R := by
          rw [norm_smul, Real.norm_of_nonneg hFu.1]
          have hb : ‖qq i - r₀‖ ≤ 6 * (N:ℝ) * R := hqqnn i hi
          calc F (2 - 2*t/τ) * ‖qq i - r₀‖ ≤ 1 * (6 * (N:ℝ) * R) :=
                mul_le_mul hFu.2 hb (norm_nonneg _) (by linarith)
            _ = 6 * (N:ℝ) * R := one_mul _
        have h3 : ‖(1 - F (2 - 2*t/τ)) • (y i - r₀) + F (2 - 2*t/τ) • (qq i - r₀)‖
            ≤ R + 6 * (N:ℝ) * R := (norm_add_le _ _).trans (add_le_add h1 h2)
        have h4 : R + 6 * (N:ℝ) * R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
        linarith [h3, h4]
    have hγball : ∀ t, ∀ i, i ∈ s → dist (γ t i) r₀ ≤ 7 * (N:ℝ) * R := by
      intro t i hi
      by_cases ht : t ≤ 0
      · rw [show γ t = x from by
              show (if t ≤ 0 then x else if t ≤ τ then γ2 t else y) = x
              rw [if_pos ht]]
        have hb : dist (x i) r₀ ≤ R := hx i hi
        have h4 : R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
        linarith
      · by_cases ht2 : t ≤ τ
        · rw [hγeq t ⟨by linarith, ht2⟩]
          exact hγ2ball t ⟨by linarith, ht2⟩ i hi
        · rw [show γ t = y from by
                show (if t ≤ 0 then x else if t ≤ τ then γ2 t else y) = y
                rw [if_neg ht, if_neg ht2]]
          have hb : dist (y i) r₀ ≤ R := hy i hi
          have h4 : R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
          linarith
    -- Absolute continuity of the path
    have hACfirst : AbsolutelyContinuousOnInterval (fun t : ℝ => G x (2*t/τ)) (0:ℝ) (τ/2) := by
      have hFaff : AbsolutelyContinuousOnInterval (fun t : ℝ => F ((2/τ) * t + 0))
          ((0-0)/(2/τ)) ((1-0)/(2/τ)) :=
        Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
          (f := F) (a := 0) (b := 1) (c := 2/τ) (d := 0) (by positivity) hFAC
      rw [show ((0:ℝ) - 0)/(2/τ) = 0 by simp,
          show ((1:ℝ) - 0)/(2/τ) = τ/2 by rw [sub_zero, one_div_div]] at hFaff
      have h1 : AbsolutelyContinuousOnInterval (fun t : ℝ => F (2*t/τ)) 0 (τ/2) :=
        ac_congr hFaff (fun t _ => by rw [show (2/τ) * t + 0 = 2*t/τ by ring])
      have hconst : AbsolutelyContinuousOnInterval
          (fun _ : ℝ => (qq - x : EuclideanSpace E (Fin N))) 0 (τ/2) :=
        (LipschitzWith.const (qq - x)).lipschitzOnWith.absolutelyContinuousOnInterval
      have hconst2 : AbsolutelyContinuousOnInterval
          (fun _ : ℝ => (x : EuclideanSpace E (Fin N))) 0 (τ/2) :=
        (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval
      refine ac_congr ((h1.smul hconst).add hconst2) ?_
      intro u _
      show F (2*u/τ) • (qq - x) + x = G x (2*u/τ)
      rw [hG_app]
      abel
    have hACsecond : AbsolutelyContinuousOnInterval (fun t : ℝ => G y (2 - 2*t/τ)) (τ/2) τ := by
      have hFaff : AbsolutelyContinuousOnInterval (fun t : ℝ => F ((-(2/τ)) * t + 2))
          ((0-2)/(-(2/τ))) ((1-2)/(-(2/τ))) :=
        Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
          (f := F) (a := 0) (b := 1) (c := -(2/τ)) (d := 2)
          (neg_ne_zero.mpr (by positivity : (2/τ : ℝ) ≠ 0)) hFAC
      rw [show ((0:ℝ) - 2)/(-(2/τ)) = τ by
            rw [show ((0:ℝ) - 2) = -(2:ℝ) by norm_num, neg_div_neg_eq, div_div_eq_mul_div]
            ring_nf,
          show ((1:ℝ) - 2)/(-(2/τ)) = τ/2 by
            rw [show ((1:ℝ) - 2) = -(1:ℝ) by norm_num, neg_div_neg_eq, div_div_eq_mul_div]
            ring_nf] at hFaff
      have hFaff' : AbsolutelyContinuousOnInterval (fun t : ℝ => F ((-(2/τ)) * t + 2)) (τ/2) τ :=
        hFaff.symm
      have h1 : AbsolutelyContinuousOnInterval (fun t : ℝ => F (2 - 2*t/τ)) (τ/2) τ :=
        ac_congr hFaff' (fun t _ => by rw [show (-(2/τ)) * t + 2 = 2 - 2*t/τ by ring])
      have hconst : AbsolutelyContinuousOnInterval
          (fun _ : ℝ => (qq - y : EuclideanSpace E (Fin N))) (τ/2) τ :=
        (LipschitzWith.const (qq - y)).lipschitzOnWith.absolutelyContinuousOnInterval
      have hconst2 : AbsolutelyContinuousOnInterval
          (fun _ : ℝ => (y : EuclideanSpace E (Fin N))) (τ/2) τ :=
        (LipschitzWith.const y).lipschitzOnWith.absolutelyContinuousOnInterval
      refine ac_congr ((h1.smul hconst).add hconst2) ?_
      intro u _
      show F (2 - 2*u/τ) • (qq - y) + y = G y (2 - 2*u/τ)
      rw [hG_app]
      abel
    have hmid : (fun t : ℝ => G x (2*t/τ)) (τ/2) = (fun t : ℝ => G y (2 - 2*t/τ)) (τ/2) := by
      show G x (2*(τ/2)/τ) = G y (2 - 2*(τ/2)/τ)
      have h2t : 2*(τ/2)/τ = 1 := by field_simp
      rw [h2t]
      norm_num
      rw [hG_app, hG_app, hF1]
      simp only [one_smul]
      abel
    have hACcat := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
      (by linarith : (0:ℝ) ≤ τ/2) (by linarith : (τ/2) ≤ τ) hmid hACfirst hACsecond
    have hACγ2 : AbsolutelyContinuousOnInterval γ2 0 τ := by
      refine ac_congr hACcat (fun u _ => ?_)
      show (if u ≤ τ/2 then G x (2*u/τ) else G y (2 - 2*u/τ)) = γ2 u
      rfl
    have hACγ : AbsolutelyContinuousOnInterval γ 0 τ :=
      ac_congr hACγ2 (fun u hu =>
        (hγeq u (by rwa [uIcc_of_le (by linarith : (0:ℝ) ≤ τ)] at hu)).symm)
    -- a.e. differentiability of F and its pullback
    have hFdiff : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioo (0:ℝ) 1 → DifferentiableAt ℝ F u := by
      filter_upwards [hFAC.ae_differentiableAt] with u hu huIoo
      exact hu (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨huIoo.1.le, huIoo.2.le⟩)
    have hFdiff_aff : ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.Ioo (0:ℝ) (τ/2) → DifferentiableAt ℝ F (2*t/τ) := by
      have hq := (MeasureTheory.Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
        (by positivity : (2/τ : ℝ) ≠ 0)).ae hFdiff
      filter_upwards [hq] with t ht htIoo
      have h2 : (2*t/τ : ℝ) = (2/τ) * t := by ring
      have hmem : (2/τ) * t ∈ Set.Ioo (0:ℝ) 1 := by
        constructor
        · exact mul_pos (by positivity) htIoo.1
        · have h3 : (2/τ) * t = 2*t/τ := by ring
          rw [h3, div_lt_one hτ]
          linarith [htIoo.2]
      rw [h2]
      exact ht hmem
    -- derivative of the half-curves
    have hHderiv : ∀ a : EuclideanSpace E (Fin N), ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.Ioo (0:ℝ) (τ/2) →
        deriv (fun s : ℝ => G a (2*s/τ)) s = (2/τ) • ((deriv F (2*s/τ)) • (qq - a)) := by
      intro a
      filter_upwards [hFdiff_aff] with s hFd hsIoo
      have hL : HasDerivAt (fun s : ℝ => 2*s/τ) (2/τ) s := by
        have h1 : HasDerivAt (fun s : ℝ => (2/τ) * s) (2/τ) s := by
          simpa using (hasDerivAt_id s).const_mul (2/τ)
        refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
        ring
      have hG' : HasDerivAt (G a) ((deriv F (2*s/τ)) • (qq - a)) (2*s/τ) :=
        ((hFd hsIoo).hasDerivAt.smul_const (qq - a)).const_add a
      exact (hG'.scomp s hL).deriv
    -- γ2 agrees with the half-curves
    have hγ2first : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (0:ℝ) (τ/2) →
        γ2 =ᶠ[𝓝 t] (fun s : ℝ => G x (2*s/τ)) := by
      filter_upwards with t ht
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      show (if s ≤ τ/2 then G x (2*s/τ) else G y (2 - 2*s/τ)) = G x (2*s/τ)
      rw [if_pos hs.2.le]
    have hγ2sec : ∀ σ ∈ Set.Ioo (0:ℝ) (τ/2), γ2 (τ - σ) = G y (2*σ/τ) := by
      intro σ hs
      show (if τ - σ ≤ τ/2 then G x (2*(τ-σ)/τ) else G y (2 - 2*(τ-σ)/τ)) = G y (2*σ/τ)
      rw [if_neg (by linarith [hs.2]),
        show 2 - 2*(τ-σ)/τ = 2*σ/τ by rw [mul_div_assoc]; field_simp; ring]
    -- kinetic bound
    let Kx : ℝ := ∑ i ∈ s, m i * ‖qq i - x i‖^2
    let Ky : ℝ := ∑ i ∈ s, m i * ‖qq i - y i‖^2
    have hqqx : ∀ i ∈ s, ‖qq i - x i‖ ≤ 7 * (N:ℝ) * R := by
      intro i hi
      have h1 : qq i - x i = (qq i - r₀) - (x i - r₀) := by abel
      rw [h1]
      have h2 := hqqnn i hi
      have h3 : ‖x i - r₀‖ ≤ R := by rw [← dist_eq_norm]; exact hx i hi
      have : ‖(qq i - r₀) - (x i - r₀)‖ ≤ 6 * (N:ℝ) * R + R := (norm_sub_le _ _).trans (add_le_add h2 h3)
      have h4 : 6 * (N:ℝ) * R + R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
      linarith [this, h4]
    have hqqy : ∀ i ∈ s, ‖qq i - y i‖ ≤ 7 * (N:ℝ) * R := by
      intro i hi
      have h1 : qq i - y i = (qq i - r₀) - (y i - r₀) := by abel
      rw [h1]
      have h2 := hqqnn i hi
      have h3 : ‖y i - r₀‖ ≤ R := by rw [← dist_eq_norm]; exact hy i hi
      have : ‖(qq i - r₀) - (y i - r₀)‖ ≤ 6 * (N:ℝ) * R + R := (norm_sub_le _ _).trans (add_le_add h2 h3)
      have h4 : 6 * (N:ℝ) * R + R ≤ 7 * (N:ℝ) * R := by nlinarith [hR, hN1]
      linarith [this, h4]
    have hKx : Kx ≤ (∑ i ∈ s, m i) * (7 * (N:ℝ) * R)^2 := by
      have : Kx = ∑ i ∈ s, m i * ‖qq i - x i‖^2 := rfl
      rw [this]
      calc ∑ i ∈ s, m i * ‖qq i - x i‖^2
          ≤ ∑ i ∈ s, m i * (7 * (N:ℝ) * R)^2 :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (hqqx i hi) 2) (hm i).le)
        _ = (∑ i ∈ s, m i) * (7 * (N:ℝ) * R)^2 := (Finset.sum_mul _ _ _).symm
    have hKy : Ky ≤ (∑ i ∈ s, m i) * (7 * (N:ℝ) * R)^2 := by
      have : Ky = ∑ i ∈ s, m i * ‖qq i - y i‖^2 := rfl
      rw [this]
      calc ∑ i ∈ s, m i * ‖qq i - y i‖^2
          ≤ ∑ i ∈ s, m i * (7 * (N:ℝ) * R)^2 :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (hqqy i hi) 2) (hm i).le)
        _ = (∑ i ∈ s, m i) * (7 * (N:ℝ) * R)^2 := (Finset.sum_mul _ _ _).symm
    have hmass0 : (0:ℝ) ≤ ∑ i ∈ s, m i := Finset.sum_nonneg (fun i _ => (hm i).le)
    have hKx0 : 0 ≤ Kx := by
      have : Kx = ∑ i ∈ s, m i * ‖qq i - x i‖^2 := rfl
      rw [this]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hm i).le (sq_nonneg _))
    have hKy0 : 0 ≤ Ky := by
      have : Ky = ∑ i ∈ s, m i * ‖qq i - y i‖^2 := rfl
      rw [this]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hm i).le (sq_nonneg _))
    -- the derivative identity for the first half
    have hcomp1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (0:ℝ) (τ/2) →
        deriv γ2 t = (2/τ) • ((deriv F (2*t/τ)) • (qq - x)) := by
      filter_upwards [hγ2first, hHderiv x] with t h1 h2 ht
      rw [(h1 ht).deriv_eq, h2 ht]
    have hcvx : ∫ t in (0:ℝ)..(τ/2), (deriv F (2*t/τ))^2
        = (τ/2) * ∫ u in (0:ℝ)..1, (deriv F u)^2 := by
      have h1 := intervalIntegral.integral_comp_mul_left
        (f := fun u : ℝ => (deriv F u)^2) (a := (0:ℝ)) (b := τ/2) (c := 2/τ) (by positivity)
      rw [show (2/τ) * 0 = 0 by ring, show (2/τ)*(τ/2) = 1 by field_simp] at h1
      rw [show (fun t : ℝ => (deriv F ((2/τ) * t))^2) = (fun t => (deriv F (2*t/τ))^2) from by
            funext t; rw [show (2/τ)*t = 2*t/τ by ring]] at h1
      rw [h1, smul_eq_mul, inv_eq_one_div, show (1:ℝ)/(2/τ) = τ/2 by field_simp]
    have hne2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ τ/2 := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ≠ τ/2} = {τ/2} := by ext a; simp
      rw [this]; exact measure_singleton _
    have hkin1 : ∫ t in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
        ≤ (Kx / τ) * (100 * (A.card:ℝ)) := by
      have hcongr : ∫ t in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
          = ∫ t in (0:ℝ)..(τ/2), (2/τ^2) * Kx * (deriv F (2*t/τ))^2 := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hcomp1, hne2] with t hc hne' ht
        rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at ht
        have htIoo : t ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨ht.1, lt_of_le_of_ne ht.2 hne'⟩
        rw [hc htIoo]
        have hs : ∀ i, ((2/τ) • ((deriv F (2*t/τ)) • (qq - x))) i
            = ((2/τ) * (deriv F (2*t/τ))) • (qq i - x i) := by
          intro i
          rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_smul]
        simp only [hs]
        have hsum : (∑ i ∈ s, m i * ‖((2/τ) * (deriv F (2*t/τ))) • (qq i - x i)‖^2)
            = ((2/τ) * (deriv F (2*t/τ)))^2 * Kx := by
          have hKx' : Kx = ∑ i ∈ s, m i * ‖qq i - x i‖^2 := rfl
          rw [hKx', Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
        rw [hsum]
        ring
      rw [hcongr, intervalIntegral.integral_const_mul, hcvx]
      have hcc : (2/τ^2) * Kx * ((τ/2) * ∫ u in (0:ℝ)..1, (deriv F u)^2)
          = (Kx/τ) * ∫ u in (0:ℝ)..1, (deriv F u)^2 := by
        field_simp
      rw [hcc]
      have hb : (Kx/τ) * ∫ u in (0:ℝ)..1, (deriv F u)^2 ≤ (Kx/τ) * (100 * (A.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hFenergy (by positivity)
      exact hb
    -- chosen crossing parameters
    have hxAx : ∀ i j, i ∈ s → j ∈ s → i ≠ j → tX i j ∈ A := by
      intro i j hi hj hij
      have hfve : fv (i, j, false) = tX i j := by
        simp only [fv]
        rw [if_pos ⟨hi, hj, hij⟩, if_neg (by simp : ¬ ((false : Bool) = true))]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(i, j, false), Finset.mem_univ _, hfve⟩)
    let bx : Fin N → Fin N → ℝ := fun i j =>
      if h : i ∈ s ∧ j ∈ s ∧ i ≠ j then
        Classical.choose (hFholder (tX i j) (hxAx i j h.1 h.2.1 h.2.2)) else 0
    have hbx' : ∀ i j, i ∈ s → j ∈ s → i ≠ j → ∀ t ∈ Set.Icc (0:ℝ) 1,
        (1/2:ℝ) * |t - bx i j|^(2/3:ℝ) ≤ |F t - tX i j| := by
      intro i j hi hj hij t ht
      have h1 : bx i j = Classical.choose (hFholder (tX i j) (hxAx i j hi hj hij)) := by
        simp only [bx]
        rw [dif_pos ⟨hi, hj, hij⟩]
      rw [h1]
      exact Classical.choose_spec (hFholder (tX i j) (hxAx i j hi hj hij)) t ht
    -- the bad time set is finite
    have hbad : ∀ᵐ t ∂(volume : Measure ℝ), ∀ p : Fin N × Fin N, 2*t/τ ≠ bx p.1 p.2 := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ ∀ p : Fin N × Fin N, 2*a/τ ≠ bx p.1 p.2}
          = {a : ℝ | ∃ p : Fin N × Fin N, 2*a/τ = bx p.1 p.2} := by
        ext a; simp only [not_forall, not_ne_iff]
      rw [hset]
      refine MeasureTheory.measure_mono_null ?_
        ((Finset.finite_toSet (Finset.image (fun p : Fin N × Fin N => τ * bx p.1 p.2 / 2)
          Finset.univ)).measure_zero volume)
      rintro t ⟨p, hp⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨p, Finset.mem_univ _, ?_⟩
      have h4 : 2 * t = bx p.1 p.2 * τ := (div_eq_iff (ne_of_gt hτ)).mp hp
      rw [div_eq_iff (by norm_num : (2:ℝ) ≠ 0)]
      linarith
    -- geometric lower bound for the distance at time t in the first half
    have hdistlo : ∀ t ∈ Set.Ioc (0:ℝ) (τ/2), ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        (2*R) * |2*t/τ - bx i j|^(2/3:ℝ) ≤ dist (γ2 t i) (γ2 t j) := by
      intro t ht i hi j hj hij
      have hγ2t : γ2 t = G x (2*t/τ) := by
        show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G x (2*t/τ)
        rw [if_pos ht.2]
      have harg : (G x (2*t/τ)) i - (G x (2*t/τ)) j
          = (x i - x j) + F (2*t/τ) • dirX i j := by
        have hGi : (G x (2*t/τ)) i = x i + F (2*t/τ) • (qq i - x i) := by simp [hG_app]
        have hGj : (G x (2*t/τ)) j = x j + F (2*t/τ) • (qq j - x j) := by simp [hG_app]
        rw [hGi, hGj, show dirX i j = (qq i - x i) - (qq j - x j) from rfl]
        module
      rw [hγ2t, dist_eq_norm, harg]
      have hun := norm_add_smul_ge (x i - x j) (dirX i j) (F (2*t/τ))
      have heq : F (2*t/τ) + inner ℝ (x i - x j) (dirX i j) / ‖dirX i j‖^2
          = F (2*t/τ) - tX i j := by
        rw [show tX i j = -(inner ℝ (x i - x j) (dirX i j)) / ‖dirX i j‖^2 from rfl]
        ring
      rw [heq] at hun
      have h2 : (1/2) * |2*t/τ - bx i j|^(2/3:ℝ) ≤ |F (2*t/τ) - tX i j| :=
        hbx' i j hi hj hij (2*t/τ) (hph1 t ht.1.le ht.2)
      have h4 := hdirXn i hi j hj hij
      have hnn : (0:ℝ) ≤ |F (2*t/τ) - tX i j| := abs_nonneg _
      calc (2*R) * |2*t/τ - bx i j|^(2/3:ℝ)
          ≤ (2*R) * (2 * |F (2*t/τ) - tX i j|) := by
            have hnn2 : (0:ℝ) ≤ |2*t/τ - bx i j|^(2/3:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
            nlinarith [h2, hR]
        _ = (4*R) * |F (2*t/τ) - tX i j| := by ring
        _ ≤ ‖dirX i j‖ * |F (2*t/τ) - tX i j| := by nlinarith [h4]
        _ ≤ ‖(x i - x j) + F (2*t/τ) • dirX i j‖ := hun
    -- per-term potential bound
    have hpot_ae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) (τ/2) →
        (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
        ≤ ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)) := by
      filter_upwards [hbad] with t hb ht
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hi1, hij⟩ := hi
      have hlo := hdistlo t ht i hi1 j hj (ne_of_lt hij)
      have hne : 2*t/τ - bx i j ≠ 0 := sub_ne_zero.mpr (hb (i,j))
      have hpos : 0 < (2*R) * |2*t/τ - bx i j|^(2/3:ℝ) :=
        mul_pos (by linarith) (Real.rpow_pos_of_pos (abs_pos.mpr hne) _)
      have hinv := inv_anti₀ hpos hlo
      have h2 : ((2*R) * |2*t/τ - bx i j|^(2/3:ℝ))⁻¹
          = (1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹) := by
        rw [mul_inv, inv_eq_one_div]
      rw [h2] at hinv
      exact mul_le_mul_of_nonneg_left hinv (mul_nonneg (hm i).le (hm j).le)
    -- integrals of the per-pair kernels
    have hterm_int : ∀ c : ℝ, IntervalIntegrable
        (fun t : ℝ => (|2*t/τ - c|^(2/3:ℝ))⁻¹) volume (0:ℝ) (τ/2) := by
      intro c
      have h1 : IntervalIntegrable (fun u : ℝ => (|u - c|^(2/3:ℝ))⁻¹) volume (0:ℝ) 1 := by
        have h0 : IntervalIntegrable (fun u : ℝ => |u - c| ^ (-(2/3):ℝ)) volume (0:ℝ) 1 := by
          have h00 : IntervalIntegrable (fun u : ℝ => |u| ^ (-(2/3):ℝ)) volume (0-c) (1-c) :=
            Commons.MeasureTheory.Integral.intervalIntegrable_abs_rpow (-(2/3)) (by norm_num) _ _
          have h01 := h00.comp_sub_right c
          rwa [show 0 - c + c = 0 by ring, show 1 - c + c = 1 by ring] at h01
        rwa [show (fun u : ℝ => |u - c| ^ (-(2/3):ℝ)) = (fun u => (|u - c|^(2/3:ℝ))⁻¹) from by
              funext u; exact Real.rpow_neg (abs_nonneg _) (2/3)] at h0
      have h2 := h1.comp_mul_left (c := 2/τ)
      rw [show (0:ℝ)/(2/τ) = 0 by simp, show (1:ℝ)/(2/τ) = τ/2 by rw [one_div_div]] at h2
      rw [show (fun x : ℝ => (|(2/τ) * x - c|^(2/3:ℝ))⁻¹)
            = (fun t => (|2*t/τ - c|^(2/3:ℝ))⁻¹) from by
            funext x; rw [show (2/τ)*x = 2*x/τ by ring]] at h2
      exact h2
    have hterm_val : ∀ c : ℝ, ∫ t in (0:ℝ)..(τ/2), (|2*t/τ - c|^(2/3:ℝ))⁻¹ ≤ 3 * τ := by
      intro c
      have h1 := intervalIntegral.integral_comp_mul_left
        (f := fun u : ℝ => (|u - c|^(2/3:ℝ))⁻¹) (a := (0:ℝ)) (b := τ/2) (c := 2/τ) (by positivity)
      rw [show (2/τ) * 0 = 0 by ring, show (2/τ)*(τ/2) = 1 by field_simp] at h1
      rw [show (fun t : ℝ => (|(2/τ)*t - c|^(2/3:ℝ))⁻¹)
            = (fun t => (|2*t/τ - c|^(2/3:ℝ))⁻¹) from by
            funext t; rw [show (2/τ)*t = 2*t/τ by ring]] at h1
      rw [h1, smul_eq_mul, inv_eq_one_div, show (1:ℝ)/(2/τ) = τ/2 by field_simp]
      have h2 := Commons.MeasureTheory.Integral.intervalIntegral_rpow_abs_sub_inv_le_six c
      nlinarith [h2, hτ]
    have hpairs : ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j ≤ (∑ i ∈ s, m i)^2 := by
      have h1 : ∀ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j
          ≤ ∑ i ∈ s, m i * m j :=
        fun j hj => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (hm i).le (hm j).le)
      calc ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j
          ≤ ∑ j ∈ s, ∑ i ∈ s, m i * m j := Finset.sum_le_sum h1
        _ = ∑ j ∈ s, (∑ i ∈ s, m i) * m j := by
            apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
        _ = (∑ i ∈ s, m i) * (∑ j ∈ s, m j) := by rw [Finset.mul_sum]
        _ = (∑ i ∈ s, m i)^2 := by ring
    have hdisteq : ∀ i j : Fin N, ContinuousOn
        (fun t : ℝ => ‖(x i - x j) + F (2*t/τ) • dirX i j‖) (Set.Ioc (0:ℝ) (τ/2)) := by
      intro i j
      have hFcont : ContinuousOn F (Set.Icc (0:ℝ) 1) := hFAC.continuousOn.mono Set.Icc_subset_uIcc
      have hFt : ContinuousOn (fun t : ℝ => F (2*t/τ)) (Set.Ioc (0:ℝ) (τ/2)) :=
        hFcont.comp (by fun_prop : ContinuousOn (fun t : ℝ => 2*t/τ) (Set.Ioc (0:ℝ) (τ/2)))
          (fun t ht => hph1 t ht.1.le ht.2)
      exact (continuousOn_const.add (hFt.smul continuousOn_const)).norm
    have hdistval : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) (τ/2))), ∀ i j : Fin N,
        dist ((γ2 t) i) ((γ2 t) j) = ‖(x i - x j) + F (2*t/τ) • dirX i j‖ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      intro i j
      have hγ2t : γ2 t = G x (2*t/τ) := by
        show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G x (2*t/τ)
        rw [if_pos ht.2]
      have harg : (G x (2*t/τ)) i - (G x (2*t/τ)) j
          = (x i - x j) + F (2*t/τ) • dirX i j := by
        have hGi : (G x (2*t/τ)) i = x i + F (2*t/τ) • (qq i - x i) := by simp [hG_app]
        have hGj : (G x (2*t/τ)) j = x j + F (2*t/τ) • (qq j - x j) := by simp [hG_app]
        rw [hGi, hGj, show dirX i j = (qq i - x i) - (qq j - x j) from rfl]
        module
      rw [hγ2t, dist_eq_norm, harg]
    have hdist_m : ∀ i j : Fin N, AEMeasurable (fun t : ℝ => dist ((γ2 t) i) ((γ2 t) j))
        (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
      intro i j
      refine AEMeasurable.congr (f := fun t : ℝ => ‖(x i - x j) + F (2*t/τ) • dirX i j‖) ?_ ?_
      · exact ((hdisteq i j).aemeasurable measurableSet_Ioc)
      · filter_upwards [hdistval] with t ht
        exact (ht i j).symm
    have hpot_m : AEStronglyMeasurable (fun t : ℝ =>
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
        (volume.restrict (Set.uIoc (0:ℝ) (τ/2))) := by
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)]
      have h1 : AEStronglyMeasurable (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹)
          (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
        refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
        have h2 : AEStronglyMeasurable (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹)
            (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
          refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
          have h3 : AEMeasurable (fun t : ℝ => m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹)
              (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
            (AEMeasurable.inv (hdist_m i j)).const_mul (m i * m j)
          exact h3.aestronglyMeasurable
        have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹)
            = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹) := by
          funext t; rw [Finset.sum_apply]
        rw [h4]; exact h2
      have h5 : (fun t : ℝ => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹)
          = (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((γ2 t) i) ((γ2 t) j))⁻¹) := by
        funext t; rw [Finset.sum_apply]
      rw [h5]; exact h1
    have hmaj_int_eq : IntervalIntegrable (fun t => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))) volume (0:ℝ) (τ/2) := by
      have h0 : ∀ j ∈ s, IntervalIntegrable (fun t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) volume (0:ℝ) (τ/2) := by
        intro j hj
        have h2 := IntervalIntegrable.sum (s.filter (fun i => i < j))
          (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          (fun i _ => ((hterm_int (bx i j)).const_mul (1/(2*R))).const_mul (m i * m j))
        have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
            = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
          funext t; rw [Finset.sum_apply]
        rw [h4]; exact h2
      have h3 := IntervalIntegrable.sum s (f := fun j t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) h0
      have h5 : (fun t : ℝ => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          = (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
        funext t; rw [Finset.sum_apply]
      rw [h5]; exact h3
    have hpot_int_eq : IntervalIntegrable (fun t =>
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
        volume (0:ℝ) (τ/2) := by
      have hle : (fun x : ℝ => ‖(∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 x i) (γ2 x j))⁻¹)‖)
          ≤ᵐ[volume.restrict (Set.uIoc (0:ℝ) (τ/2))]
          (fun t => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
        change ∀ᵐ x ∂(volume.restrict (Set.uIoc (0:ℝ) (τ/2))),
          ‖(∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 x i) (γ2 x j))⁻¹)‖
          ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*x/τ - bx i j|^(2/3:ℝ))⁻¹)))
        rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hpot_ae] with t hb ht
        rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at ht
        have hnn : (0:ℝ) ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹) :=
          Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg
            (mul_nonneg (hm i).le (hm j).le) (inv_nonneg.mpr dist_nonneg)))
        rw [Real.norm_of_nonneg hnn]
        exact hb ht
      exact hmaj_int_eq.mono_fun' hpot_m hle
    have hmaj1 : ∫ t in (0:ℝ)..(τ/2),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
        ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := by
      have hinner : ∀ j ∈ s, ∫ t in (0:ℝ)..(τ/2),
            (∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          ≤ ∑ i ∈ s.filter (fun i => i < j), m i * m j * ((1/(2*R)) * (3*τ)) := by
        intro j hj
        rw [intervalIntegral.integral_finsetSum (s := s.filter (fun i => i < j))
          (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          (fun i _ => by
            have h2 := ((hterm_int (bx i j)).const_mul (1/(2*R))).const_mul (m i * m j)
            simpa only [Finset.sum_apply] using h2)]
        apply Finset.sum_le_sum
        intro i hi
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hterm_val (bx i j))
            (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ 2*R)))
          (mul_nonneg (hm i).le (hm j).le)
      have h1 : ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          = ∑ j ∈ s, ∫ t in (0:ℝ)..(τ/2), (∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
        rw [intervalIntegral.integral_finsetSum (s := s)
          (f := fun j t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          (fun j _ => by
            have h2 := IntervalIntegrable.sum (s.filter (fun i => i < j))
              (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
              (fun i _ => ((hterm_int (bx i j)).const_mul (1/(2*R))).const_mul (m i * m j))
            have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
                = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
                  m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
              funext t; rw [Finset.sum_apply]
            rw [h4]; exact h2)]
      rw [h1]
      calc ∑ j ∈ s, ∫ t in (0:ℝ)..(τ/2), (∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
          ≤ ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * ((1/(2*R)) * (3*τ)) :=
            Finset.sum_le_sum hinner
        _ = (3*τ/(2*R)) * ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 :=
            mul_le_mul_of_nonneg_left hpairs (by positivity)
    have hpot1 : ∫ t in (0:ℝ)..(τ/2),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
        ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := by
      have hfi : Integrable (fun t => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ τ/2)).mp hpot_int_eq
      have hgi : Integrable (fun t => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))))
          (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ τ/2)).mp hmaj_int_eq
      have hmono : ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
          ≤ ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹))) := by
        rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ τ/2),
            intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ τ/2)]
        refine MeasureTheory.integral_mono_ae hfi hgi ?_
        change ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) (τ/2))),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
          ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - bx i j|^(2/3:ℝ))⁻¹)))
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hpot_ae] with t hb ht
        exact hb ht
      exact hmono.trans hmaj1
    -- the second half, via the substitution t |-> tau - t
    have hγsym : ∀ σ ∈ Set.Ioo (0:ℝ) (τ/2), γ2 (τ - σ) = G y (2*σ/τ) := hγ2sec
    have hyAy : ∀ i j, i ∈ s → j ∈ s → i ≠ j → tY i j ∈ A := by
      intro i j hi hj hij
      have hfve : fv (i, j, true) = tY i j := by
        simp only [fv]
        rw [if_pos ⟨hi, hj, hij⟩]
        simp
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(i, j, true), Finset.mem_univ _, hfve⟩)
    let byv : Fin N → Fin N → ℝ := fun i j =>
      if h : i ∈ s ∧ j ∈ s ∧ i ≠ j then
        Classical.choose (hFholder (tY i j) (hyAy i j h.1 h.2.1 h.2.2)) else 0
    have hbyv' : ∀ i j, i ∈ s → j ∈ s → i ≠ j → ∀ t ∈ Set.Icc (0:ℝ) 1,
        (1/2:ℝ) * |t - byv i j|^(2/3:ℝ) ≤ |F t - tY i j| := by
      intro i j hi hj hij t ht
      have h1 : byv i j = Classical.choose (hFholder (tY i j) (hyAy i j hi hj hij)) := by
        simp only [byv]
        rw [dif_pos ⟨hi, hj, hij⟩]
      rw [h1]
      exact Classical.choose_spec (hFholder (tY i j) (hyAy i j hi hj hij)) t ht
    have hbadY : ∀ᵐ t ∂(volume : Measure ℝ), ∀ p : Fin N × Fin N, 2*t/τ ≠ byv p.1 p.2 := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : ℝ | ¬ ∀ p : Fin N × Fin N, 2*a/τ ≠ byv p.1 p.2}
          = {a : ℝ | ∃ p : Fin N × Fin N, 2*a/τ = byv p.1 p.2} := by
        ext a; simp only [not_forall, not_ne_iff]
      rw [hset]
      refine MeasureTheory.measure_mono_null ?_
        ((Finset.finite_toSet (Finset.image (fun p : Fin N × Fin N => τ * byv p.1 p.2 / 2)
          Finset.univ)).measure_zero volume)
      rintro t ⟨p, hp⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨p, Finset.mem_univ _, ?_⟩
      have h4 : 2 * t = byv p.1 p.2 * τ := (div_eq_iff (ne_of_gt hτ)).mp hp
      rw [div_eq_iff (by norm_num : (2:ℝ) ≠ 0)]
      linarith
    have hdistloY : ∀ t ∈ Set.Ioc (0:ℝ) (τ/2), ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        (2*R) * |2*t/τ - byv i j|^(2/3:ℝ) ≤ dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j) := by
      intro t ht i hi j hj hij
      have harg : (G y (2*t/τ)) i - (G y (2*t/τ)) j
          = (y i - y j) + F (2*t/τ) • dirY i j := by
        have hGi : (G y (2*t/τ)) i = y i + F (2*t/τ) • (qq i - y i) := by simp [hG_app]
        have hGj : (G y (2*t/τ)) j = y j + F (2*t/τ) • (qq j - y j) := by simp [hG_app]
        rw [hGi, hGj, show dirY i j = (qq i - y i) - (qq j - y j) from rfl]
        module
      rw [dist_eq_norm, harg]
      have hun := norm_add_smul_ge (y i - y j) (dirY i j) (F (2*t/τ))
      have heq : F (2*t/τ) + inner ℝ (y i - y j) (dirY i j) / ‖dirY i j‖^2
          = F (2*t/τ) - tY i j := by
        rw [show tY i j = -(inner ℝ (y i - y j) (dirY i j)) / ‖dirY i j‖^2 from rfl]
        ring
      rw [heq] at hun
      have h2 : (1/2) * |2*t/τ - byv i j|^(2/3:ℝ) ≤ |F (2*t/τ) - tY i j| :=
        hbyv' i j hi hj hij (2*t/τ) (hph1 t ht.1.le ht.2)
      have hdir : dirY i j = (qq i - qq j) - (y i - y j) := by
        show (qq i - y i) - (qq j - y j) = _; abel
      have h4 : 4 * R ≤ ‖dirY i j‖ := by
        rw [hdir]
        have hb := abs_norm_sub_norm_le (qq i - qq j) (y i - y j)
        have h5 := hqq_dist i hi j hj hij
        have h6 := hydist i hi j hj
        linarith [(abs_le.mp hb).2]
      have hnn : (0:ℝ) ≤ |F (2*t/τ) - tY i j| := abs_nonneg _
      calc (2*R) * |2*t/τ - byv i j|^(2/3:ℝ)
          ≤ (2*R) * (2 * |F (2*t/τ) - tY i j|) := by
            have hnn2 : (0:ℝ) ≤ |2*t/τ - byv i j|^(2/3:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
            nlinarith [h2, hR]
        _ = (4*R) * |F (2*t/τ) - tY i j| := by ring
        _ ≤ ‖dirY i j‖ * |F (2*t/τ) - tY i j| := by nlinarith [h4]
        _ ≤ ‖(y i - y j) + F (2*t/τ) • dirY i j‖ := hun
    have hpot_aeY : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) (τ/2) →
        (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹)
        ≤ ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹)) := by
      filter_upwards [hbadY] with t hb ht
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hi1, hij⟩ := hi
      have hlo := hdistloY t ht i hi1 j hj (ne_of_lt hij)
      have hne : 2*t/τ - byv i j ≠ 0 := sub_ne_zero.mpr (hb (i,j))
      have hpos : 0 < (2*R) * |2*t/τ - byv i j|^(2/3:ℝ) :=
        mul_pos (by linarith) (Real.rpow_pos_of_pos (abs_pos.mpr hne) _)
      have hinv := inv_anti₀ hpos hlo
      have h2 : ((2*R) * |2*t/τ - byv i j|^(2/3:ℝ))⁻¹
          = (1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹) := by
        rw [mul_inv, inv_eq_one_div]
      rw [h2] at hinv
      exact mul_le_mul_of_nonneg_left hinv (mul_nonneg (hm i).le (hm j).le)
    -- ===== second half: potential energy =====
    have hdist_m_gen : ∀ (a : EuclideanSpace E (Fin N)) (i j : Fin N), AEMeasurable
        (fun σ : ℝ => dist ((G a (2*σ/τ)) i) ((G a (2*σ/τ)) j))
        (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
      intro a i j
      have hcont : ContinuousOn (fun σ : ℝ =>
          ‖(a i - a j) + F (2*σ/τ) • ((qq i - a i) - (qq j - a j))‖) (Set.Ioc (0:ℝ) (τ/2)) := by
        have hFcont : ContinuousOn F (Set.Icc (0:ℝ) 1) := hFAC.continuousOn.mono Set.Icc_subset_uIcc
        have hFt : ContinuousOn (fun t : ℝ => F (2*t/τ)) (Set.Ioc (0:ℝ) (τ/2)) :=
          hFcont.comp (by fun_prop : ContinuousOn (fun t : ℝ => 2*t/τ) (Set.Ioc (0:ℝ) (τ/2)))
            (fun t ht => hph1 t ht.1.le ht.2)
        exact (continuousOn_const.add (hFt.smul continuousOn_const)).norm
      have hval : ∀ σ : ℝ, ∀ i j : Fin N,
          dist ((G a (2*σ/τ)) i) ((G a (2*σ/τ)) j)
            = ‖(a i - a j) + F (2*σ/τ) • ((qq i - a i) - (qq j - a j))‖ := by
        intro σ i' j'
        have harg : (G a (2*σ/τ)) i' - (G a (2*σ/τ)) j'
            = (a i' - a j') + F (2*σ/τ) • ((qq i' - a i') - (qq j' - a j')) := by
          have hGi : (G a (2*σ/τ)) i' = a i' + F (2*σ/τ) • (qq i' - a i') := by simp [hG_app]
          have hGj : (G a (2*σ/τ)) j' = a j' + F (2*σ/τ) • (qq j' - a j') := by simp [hG_app]
          rw [hGi, hGj]
          module
        rw [dist_eq_norm, harg]
      refine AEMeasurable.congr (f := fun σ : ℝ =>
        ‖(a i - a j) + F (2*σ/τ) • ((qq i - a i) - (qq j - a j))‖) ?_ ?_
      · exact hcont.aemeasurable measurableSet_Ioc
      · filter_upwards [Filter.Eventually.of_forall hval] with σ h
        exact (h i j).symm
    have hpot_m_gen : ∀ a : EuclideanSpace E (Fin N), AEStronglyMeasurable (fun t : ℝ =>
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹))
        (volume.restrict (Set.uIoc (0:ℝ) (τ/2))) := by
      intro a
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)]
      have h1 : AEStronglyMeasurable (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹)
          (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
        refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
        have h2 : AEStronglyMeasurable (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹)
            (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) := by
          refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
          have h3 : AEMeasurable (fun t : ℝ =>
                m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹)
              (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
            (AEMeasurable.inv (hdist_m_gen a i j)).const_mul (m i * m j)
          exact h3.aestronglyMeasurable
        have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹)
            = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹) := by
          funext t; rw [Finset.sum_apply]
        rw [h4]; exact h2
      have h5 : (fun t : ℝ => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹)
          = (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G a (2*t/τ)) i) ((G a (2*t/τ)) j))⁻¹) := by
        funext t; rw [Finset.sum_apply]
      rw [h5]; exact h1
    have hmaj_int_gen : ∀ b : Fin N → Fin N → ℝ, IntervalIntegrable (fun t =>
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))) volume (0:ℝ) (τ/2) := by
      intro b
      have h0 : ∀ j ∈ s, IntervalIntegrable (fun t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) volume (0:ℝ) (τ/2) := by
        intro j hj
        have h2 := IntervalIntegrable.sum (s.filter (fun i => i < j))
          (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          (fun i _ => ((hterm_int (b i j)).const_mul (1/(2*R))).const_mul (m i * m j))
        have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
            = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
              m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) := by
          funext t; rw [Finset.sum_apply]
        rw [h4]; exact h2
      have h3 := IntervalIntegrable.sum s (f := fun j t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) h0
      have h5 : (fun t : ℝ => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          = (∑ j ∈ s, fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) := by
        funext t; rw [Finset.sum_apply]
      rw [h5]; exact h3
    have hmaj_val_gen : ∀ b : Fin N → Fin N → ℝ, ∫ t in (0:ℝ)..(τ/2),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
        ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := by
      intro b
      have hinner : ∀ j ∈ s, ∫ t in (0:ℝ)..(τ/2),
            (∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          ≤ ∑ i ∈ s.filter (fun i => i < j), m i * m j * ((1/(2*R)) * (3*τ)) := by
        intro j hj
        rw [intervalIntegral.integral_finsetSum (s := s.filter (fun i => i < j))
          (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          (fun i _ => by
            have h2 := ((hterm_int (b i j)).const_mul (1/(2*R))).const_mul (m i * m j)
            simpa only [Finset.sum_apply] using h2)]
        apply Finset.sum_le_sum
        intro i hi
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hterm_val (b i j))
            (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ 2*R)))
          (mul_nonneg (hm i).le (hm j).le)
      have h1 : ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          = ∑ j ∈ s, ∫ t in (0:ℝ)..(τ/2), (∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) := by
        rw [intervalIntegral.integral_finsetSum (s := s)
          (f := fun j t => ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          (fun j _ => by
            have h2 := IntervalIntegrable.sum (s.filter (fun i => i < j))
              (f := fun i t => m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
              (fun i _ => ((hterm_int (b i j)).const_mul (1/(2*R))).const_mul (m i * m j))
            have h4 : (fun t : ℝ => ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
                = (∑ i ∈ s.filter (fun i => i < j), fun t : ℝ =>
                  m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹))) := by
              funext t; rw [Finset.sum_apply]
            rw [h4]; exact h2)]
      rw [h1]
      calc ∑ j ∈ s, ∫ t in (0:ℝ)..(τ/2), (∑ i ∈ s.filter (fun i => i < j),
              m i * m j * ((1/(2*R)) * ((|2*t/τ - b i j|^(2/3:ℝ))⁻¹)))
          ≤ ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j * ((1/(2*R)) * (3*τ)) :=
            Finset.sum_le_sum hinner
        _ = (3*τ/(2*R)) * ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j), m i * m j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 :=
            mul_le_mul_of_nonneg_left hpairs (by positivity)
    have hpotY_eq : IntervalIntegrable (fun t =>
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹))
        volume (0:ℝ) (τ/2) := by
      have hle : (fun x : ℝ => ‖(∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*x/τ)) i) ((G y (2*x/τ)) j))⁻¹)‖)
          ≤ᵐ[volume.restrict (Set.uIoc (0:ℝ) (τ/2))]
          (fun t => ∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹))) := by
        change ∀ᵐ x ∂(volume.restrict (Set.uIoc (0:ℝ) (τ/2))),
          ‖(∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*x/τ)) i) ((G y (2*x/τ)) j))⁻¹)‖
          ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*x/τ - byv i j|^(2/3:ℝ))⁻¹)))
        rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hpot_aeY] with t hb ht
        rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at ht
        have hnn : (0:ℝ) ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹) :=
          Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg
            (mul_nonneg (hm i).le (hm j).le) (inv_nonneg.mpr dist_nonneg)))
        rw [Real.norm_of_nonneg hnn]
        exact hb ht
      exact (hmaj_int_gen byv).mono_fun' (hpot_m_gen y) hle
    have hpotY : ∫ t in (0:ℝ)..(τ/2),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹)
        ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := by
      have hfi : Integrable (fun t => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹))
          (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ τ/2)).mp hpotY_eq
      have hgi : Integrable (fun t => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹))))
          (volume.restrict (Set.Ioc (0:ℝ) (τ/2))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ τ/2)).mp
          (hmaj_int_gen byv)
      have hmono : ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹)
          ≤ ∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹))) := by
        rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ τ/2),
            intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ τ/2)]
        refine MeasureTheory.integral_mono_ae hfi hgi ?_
        change ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) (τ/2))),
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*t/τ)) i) ((G y (2*t/τ)) j))⁻¹)
          ≤ (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * ((1/(2*R)) * ((|2*t/τ - byv i j|^(2/3:ℝ))⁻¹)))
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hpot_aeY] with t hb ht
        exact hb ht
      exact hmono.trans (hmaj_val_gen byv)
    have hpot2 : ∫ t in (τ/2)..τ, (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
        ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := by
      have hcomp : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Set.uIoc (0:ℝ) (τ/2) →
          (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 (τ - σ) i) (γ2 (τ - σ) j))⁻¹)
          = (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*σ/τ)) i) ((G y (2*σ/τ)) j))⁻¹) := by
        filter_upwards [hne2] with σ hne hσ
        rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at hσ
        have hIoo : σ ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨hσ.1, lt_of_le_of_ne hσ.2 hne⟩
        show (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 (τ - σ) i) (γ2 (τ - σ) j))⁻¹)
          = (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist ((G y (2*σ/τ)) i) ((G y (2*σ/τ)) j))⁻¹)
        rw [hγ2sec σ hIoo]
      have hstep := intervalIntegral.integral_comp_sub_left
        (f := fun u : ℝ => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
            m i * m j * (dist (γ2 u i) (γ2 u j))⁻¹)) (a := (0:ℝ)) (b := τ/2) (d := τ)
      rw [show τ - τ/2 = τ/2 by ring, show τ - (0:ℝ) = τ by ring] at hstep
      calc ∫ t in (τ/2)..τ, (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)
          = ∫ σ in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 (τ - σ) i) (γ2 (τ - σ) j))⁻¹) := hstep.symm
        _ = ∫ σ in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist ((G y (2*σ/τ)) i) ((G y (2*σ/τ)) j))⁻¹) :=
            intervalIntegral.integral_congr_ae hcomp
        _ ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 := hpotY
    -- ===== second half: kinetic energy =====
    have hk2deriv : ∀ a : EuclideanSpace E (Fin N), ∀ᵐ σ ∂(volume : Measure ℝ),
        σ ∈ Set.Ioo (0:ℝ) (τ/2) →
        deriv (fun u : ℝ => G a (2 - 2*u/τ)) (τ - σ)
          = (-(2/τ)) • ((deriv F (2*σ/τ)) • (qq - a)) := by
      intro a
      filter_upwards [hFdiff_aff] with σ hFd hσIoo
      have hpt : 2 - 2*(τ - σ)/τ = 2*σ/τ := by
        field_simp
        ring
      have hd : DifferentiableAt ℝ F (2 - 2*(τ - σ)/τ) := by
        rw [hpt]; exact hFd hσIoo
      have hG' : HasDerivAt (G a) ((deriv F (2 - 2*(τ - σ)/τ)) • (qq - a))
          (2 - 2*(τ - σ)/τ) :=
        (hd.hasDerivAt.smul_const (qq - a)).const_add a
      have hL : HasDerivAt (fun u : ℝ => 2 - 2*u/τ) (-(2/τ)) (τ - σ) := by
        have h1 : HasDerivAt (fun u : ℝ => (-(2/τ)) * u + 2) (-(2/τ)) (τ - σ) := by
          simpa using ((hasDerivAt_id (τ - σ)).const_mul (-(2/τ))).const_add 2
        refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
        ring
      have hcomp := hG'.scomp (τ - σ) hL
      have hd1 : (fun u : ℝ => G a (2 - 2*u/τ)) = (G a ∘ fun u : ℝ => 2 - 2*u/τ) := rfl
      rw [hd1, hcomp.deriv, hpt]
    have hγ2sec_deriv : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Set.Ioo (0:ℝ) (τ/2) →
        deriv γ2 (τ - σ) = (-(2/τ)) • ((deriv F (2*σ/τ)) • (qq - y)) := by
      filter_upwards [hk2deriv y] with σ hσ hσIoo
      have hEq : γ2 =ᶠ[𝓝 (τ - σ)] (fun u : ℝ => G y (2 - 2*u/τ)) := by
        filter_upwards [Ioo_mem_nhds (by linarith [hσIoo.2] : (τ/2:ℝ) < τ - σ)
          (by linarith [hσIoo.1] : (τ - σ : ℝ) < τ)] with u hu
        show (if u ≤ τ/2 then G x (2*u/τ) else G y (2 - 2*u/τ)) = G y (2 - 2*u/τ)
        rw [if_neg (not_le.mpr hu.1)]
      rw [hEq.deriv_eq, hσ hσIoo]
    have hsub2kin : ∫ t in (τ/2)..τ, (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
        = ∫ σ in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 (τ - σ) i‖^2) := by
      have hstep := intervalIntegral.integral_comp_sub_left
        (f := fun u : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 u i‖^2)) (a := (0:ℝ)) (b := τ/2) (d := τ)
      rw [show τ - τ/2 = τ/2 by ring, show τ - (0:ℝ) = τ by ring] at hstep
      exact hstep.symm
    have hkey2 : ∫ σ in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 (τ - σ) i‖^2)
        = ∫ σ in (0:ℝ)..(τ/2), (2/τ^2) * Ky * (deriv F (2*σ/τ))^2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hγ2sec_deriv, hne2] with σ hid σne hσ
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at hσ
      have hσIoo : σ ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨hσ.1, lt_of_le_of_ne hσ.2 σne⟩
      rw [hid hσIoo]
      have hs : ∀ i, ((-(2/τ)) • ((deriv F (2*σ/τ)) • (qq - y))) i
          = ((-(2/τ)) * (deriv F (2*σ/τ))) • (qq i - y i) := by
        intro i
        rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_smul]
      simp only [hs]
      have hsum : (∑ i ∈ s, m i * ‖((-(2/τ)) * (deriv F (2*σ/τ))) • (qq i - y i)‖^2)
          = ((-(2/τ)) * (deriv F (2*σ/τ)))^2 * Ky := by
        have hKy' : Ky = ∑ i ∈ s, m i * ‖qq i - y i‖^2 := rfl
        rw [hKy', Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      rw [hsum]
      ring
    have hkin2 : ∫ t in (τ/2)..τ, (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
        ≤ (Ky / τ) * (100 * (A.card:ℝ)) := by
      rw [hsub2kin, hkey2]
      rw [intervalIntegral.integral_const_mul]
      rw [show (2/τ^2) * Ky * ∫ σ in (0:ℝ)..(τ/2), (deriv F (2*σ/τ))^2
          = (2/τ^2) * Ky * ((τ/2) * ∫ u in (0:ℝ)..1, (deriv F u)^2) by rw [hcvx]]
      have hcc : (2/τ^2) * Ky * ((τ/2) * ∫ u in (0:ℝ)..1, (deriv F u)^2)
          = (Ky/τ) * ∫ u in (0:ℝ)..1, (deriv F u)^2 := by
        field_simp
      rw [hcc]
      exact mul_le_mul_of_nonneg_left hFenergy (by positivity)
    -- ===== a.e. collision-freeness of γ =====
    have hneT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ τ := by
      rw [MeasureTheory.ae_iff]
      have : {a : ℝ | ¬ a ≠ τ} = {τ} := by ext a; simp
      rw [this]; exact measure_singleton τ
    have hderivγ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo (0:ℝ) τ →
        deriv γ t = deriv γ2 t := by
      filter_upwards with t ht
      have hEq : γ =ᶠ[𝓝 t] γ2 := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
        exact hγeq u ⟨hu.1.le, hu.2.le⟩
      exact hEq.deriv_eq
    have hγnc : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        t ∈ Set.Ioc 0 τ → ∀ i ∈ s, ∀ j ∈ s, i ≠ j → γ t i ≠ γ t j := by
      have hbadY' : ∀ᵐ t ∂(volume : Measure ℝ), ∀ p : Fin N × Fin N, 2*(τ - t)/τ ≠ byv p.1 p.2 :=
        ae_comp_sub_left' hbadY τ
      filter_upwards [hbad, hbadY, hbadY', hne2, hneT] with t hb hby hby' hne2' hneT' ht
      intro i hi j hj hij
      rw [hγeq t ⟨ht.1.le, ht.2⟩]
      have hltτ : t < τ := lt_of_le_of_ne ht.2 hneT'
      have hpos : 0 < dist (γ2 t i) (γ2 t j) := by
        rcases le_or_gt t (τ/2) with hle | hlt
        · have h1 := hdistlo t ⟨ht.1, hle⟩ i hi j hj hij
          have hne' : 2*t/τ - bx i j ≠ 0 := sub_ne_zero.mpr (hb (i, j))
          have h2 : 0 < (2*R) * |2*t/τ - bx i j|^(2/3:ℝ) :=
            mul_pos (by linarith) (Real.rpow_pos_of_pos (abs_pos.mpr hne') (2/3:ℝ))
          linarith
        · have ht' : τ - t ∈ Set.Ioc (0:ℝ) (τ/2) := ⟨by linarith, by linarith⟩
          have h1 := hdistloY (τ - t) ht' i hi j hj hij
          have hid : 2*(τ - t)/τ = 2 - 2*t/τ := by field_simp
          have hγ2t : γ2 t = G y (2*(τ - t)/τ) := by
            show (if t ≤ τ/2 then G x (2*t/τ) else G y (2 - 2*t/τ)) = G y (2*(τ - t)/τ)
            rw [if_neg (not_le.mpr hlt), hid]
          rw [hγ2t]
          have hne' : 2*(τ - t)/τ - byv i j ≠ 0 := sub_ne_zero.mpr (hby' (i, j))
          have h2 : 0 < (2*R) * |2*(τ - t)/τ - byv i j|^(2/3:ℝ) :=
            mul_pos (by linarith) (Real.rpow_pos_of_pos (abs_pos.mpr hne') (2/3:ℝ))
          linarith
      exact dist_pos.mp hpos
    -- ===== integrability of the kinetic part =====
    have hKbase : ∀ a : EuclideanSpace E (Fin N), IntervalIntegrable
        (fun σ : ℝ => (2/τ^2) * (∑ i ∈ s, m i * ‖qq i - a i‖^2) * (deriv F (2*σ/τ))^2)
        volume (0:ℝ) (τ/2) := by
      intro a
      have h1 := hFint.comp_mul_left (c := 2/τ)
      rw [show (0:ℝ)/(2/τ) = 0 by simp, show (1:ℝ)/(2/τ) = τ/2 by rw [one_div_div]] at h1
      have h2 : (fun x : ℝ => (deriv F ((2/τ) * x))^2) = (fun x : ℝ => (deriv F (2*x/τ))^2) := by
        funext x; rw [show (2/τ)*x = 2*x/τ by ring]
      rw [h2] at h1
      exact h1.const_mul ((2/τ^2) * (∑ i ∈ s, m i * ‖qq i - a i‖^2))
    have hKae1 : (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
        =ᵐ[volume.restrict (Set.uIoc (0:ℝ) (τ/2))]
        (fun t : ℝ => (2/τ^2) * (∑ i ∈ s, m i * ‖qq i - x i‖^2) * (deriv F (2*t/τ))^2) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hcomp1, hne2] with t hc hne' ht
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at ht
      have htIoo : t ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨ht.1, lt_of_le_of_ne ht.2 hne'⟩
      rw [hc htIoo]
      have hs : ∀ i, ((2/τ) • ((deriv F (2*t/τ)) • (qq - x))) i
          = ((2/τ) * (deriv F (2*t/τ))) • (qq i - x i) := by
        intro i
        rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_smul]
      simp only [hs]
      have hsum : (∑ i ∈ s, m i * ‖((2/τ) * (deriv F (2*t/τ))) • (qq i - x i)‖^2)
          = ((2/τ) * (deriv F (2*t/τ)))^2 * (∑ i ∈ s, m i * ‖qq i - x i‖^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      rw [hsum]
      ring
    have hKint1 : IntervalIntegrable (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
        volume (0:ℝ) (τ/2) := (hKbase x).congr_ae hKae1.symm
    have hKae2 : (fun σ : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 (τ - σ) i‖^2))
        =ᵐ[volume.restrict (Set.uIoc (0:ℝ) (τ/2))]
        (fun σ : ℝ => (2/τ^2) * (∑ i ∈ s, m i * ‖qq i - y i‖^2) * (deriv F (2*σ/τ))^2) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ2sec_deriv, hne2] with σ hid hne' hσ
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at hσ
      have hσIoo : σ ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨hσ.1, lt_of_le_of_ne hσ.2 hne'⟩
      rw [hid hσIoo]
      have hs : ∀ i, ((-(2/τ)) • ((deriv F (2*σ/τ)) • (qq - y))) i
          = ((-(2/τ)) * (deriv F (2*σ/τ))) • (qq i - y i) := by
        intro i
        rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_smul]
      simp only [hs]
      have hsum : (∑ i ∈ s, m i * ‖((-(2/τ)) * (deriv F (2*σ/τ))) • (qq i - y i)‖^2)
          = ((-(2/τ)) * (deriv F (2*σ/τ)))^2 * (∑ i ∈ s, m i * ‖qq i - y i‖^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      rw [hsum]
      ring
    have hKsb : IntervalIntegrable (fun σ : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 (τ - σ) i‖^2))
        volume (0:ℝ) (τ/2) := (hKbase y).congr_ae hKae2.symm
    have hKint2 : IntervalIntegrable (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
        volume (τ/2) τ := by
      apply intervalIntegrable_of_comp_sub_left (c := τ) (a := τ/2) (b := τ)
      rw [show τ - τ = (0:ℝ) by ring, show τ - τ/2 = τ/2 by ring]
      exact hKsb
    -- ===== integrability of the potential part =====
    have hPsb : IntervalIntegrable (fun σ : ℝ => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
          m i * m j * (dist (γ2 (τ - σ) i) (γ2 (τ - σ) j))⁻¹)) volume (0:ℝ) (τ/2) := by
      refine hpotY_eq.congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hne2] with σ hne' hσ
      rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ τ/2)] at hσ
      have hσIoo : σ ∈ Set.Ioo (0:ℝ) (τ/2) := ⟨hσ.1, lt_of_le_of_ne hσ.2 hne'⟩
      show (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
          m i * m j * (dist ((G y (2*σ/τ)) i) ((G y (2*σ/τ)) j))⁻¹)
        = (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
          m i * m j * (dist (γ2 (τ - σ) i) (γ2 (τ - σ) j))⁻¹)
      rw [hγ2sec σ hσIoo]
    have hPint2 : IntervalIntegrable (fun t : ℝ => (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
          m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) volume (τ/2) τ := by
      apply intervalIntegrable_of_comp_sub_left (c := τ) (a := τ/2) (b := τ)
      rw [show τ - τ = (0:ℝ) by ring, show τ - τ/2 = τ/2 by ring]
      exact hPsb
    -- ===== the final integrability =====
    have hInt2 : IntervalIntegrable (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
          + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) volume (0:ℝ) τ :=
      (hKint1.trans hKint2).add (hpot_int_eq.trans hPint2)
    have hγInt : MeasureTheory.IntegrableOn
        (fun t => (1 / 2) * (∑ i ∈ s, m i * ‖deriv γ t i‖ ^ 2)
          + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ t i) (γ t j))⁻¹))
        (Set.Ioc 0 τ) := by
      have hcongr : (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
          =ᵐ[volume.restrict (Set.uIoc (0:ℝ) τ)]
          (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ t i) (γ t j))⁻¹)) := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hneT, hderivγ] with t hne hd ht
        rw [Set.uIoc_of_le hτ.le] at ht
        have htIoo : t ∈ Set.Ioo (0:ℝ) τ := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
        rw [hd htIoo, hγeq t ⟨ht.1.le, ht.2⟩]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mp (hInt2.congr_ae hcongr)
    -- ===== the integral bound =====
    have hKx' : Kx ≤ 49 * (∑ i ∈ s, m i) * (N:ℝ)^2 * R^2 := by
      refine hKx.trans (le_of_eq ?_)
      ring
    have hKy' : Ky ≤ 49 * (∑ i ∈ s, m i) * (N:ℝ)^2 * R^2 := by
      refine hKy.trans (le_of_eq ?_)
      ring
    have hsumxy : Kx + Ky ≤ 98 * (∑ i ∈ s, m i) * (N:ℝ)^2 * R^2 := by linarith
    have hA300 : (100 * (A.card:ℝ)) ≤ 300 * (N:ℝ)^2 := by
      have hN1s : (1:ℝ) ≤ (N:ℝ)^2 := by nlinarith [hN1]
      linarith [hAcard]
    have hnum : (Kx + Ky) * (100 * (A.card:ℝ)) ≤ 100000 * (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2 := by
      have hX : (0:ℝ) ≤ (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2 := by positivity
      calc (Kx + Ky) * (100 * (A.card:ℝ))
          ≤ (98 * (∑ i ∈ s, m i) * (N:ℝ)^2 * R^2) * (300 * (N:ℝ)^2) :=
            mul_le_mul hsumxy hA300 (by positivity) (by positivity)
        _ = 29400 * ((∑ i ∈ s, m i) * (N:ℝ)^4 * R^2) := by ring
        _ ≤ 100000 * ((∑ i ∈ s, m i) * (N:ℝ)^4 * R^2) :=
            mul_le_mul_of_nonneg_right (by norm_num : (29400:ℝ) ≤ 100000) hX
        _ = 100000 * (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2 := by ring
    have hKb : (∫ t in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
          + (∫ t in (τ/2)..τ, (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
        ≤ 100000 * (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2 / τ := by
      calc (∫ t in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
            + (∫ t in (τ/2)..τ, (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
          ≤ (Kx/τ) * (100*(A.card:ℝ)) + (Ky/τ) * (100*(A.card:ℝ)) := add_le_add hkin1 hkin2
        _ = ((Kx + Ky) * (100*(A.card:ℝ)))/τ := by
            rw [← add_mul, ← add_div, div_mul_eq_mul_div]
        _ ≤ (100000 * (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2)/τ :=
            div_le_div_of_nonneg_right hnum hτ.le
        _ = 100000 * (∑ i ∈ s, m i) * (N:ℝ)^4 * R^2 / τ := rfl
    have hN4 : (3:ℝ) ≤ 10 * (N:ℝ)^4 := by
      have h1 : (1:ℝ) ≤ (N:ℝ)^4 := one_le_pow₀ hN1
      linarith
    have hPb : (∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
          + (∫ t in (τ/2)..τ, (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
        ≤ 10 * (∑ i ∈ s, m i)^2 * (N:ℝ)^4 * τ / R := by
      have hstep : (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 + (3*τ/(2*R)) * (∑ i ∈ s, m i)^2
          = 3*τ*(∑ i ∈ s, m i)^2/R := by
        field_simp
        ring
      calc (∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
            + (∫ t in (τ/2)..τ, (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
              m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))
          ≤ (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 + (3*τ/(2*R)) * (∑ i ∈ s, m i)^2 :=
            add_le_add hpot1 hpot2
        _ = 3*τ*(∑ i ∈ s, m i)^2/R := hstep
        _ ≤ 10 * (∑ i ∈ s, m i)^2 * (N:ℝ)^4 * τ / R := by
            rw [div_le_div_iff₀ hR hR]
            have h3 : (3:ℝ) * ((∑ i ∈ s, m i)^2 * τ * R)
                ≤ (10 * (N:ℝ)^4) * ((∑ i ∈ s, m i)^2 * τ * R) :=
              mul_le_mul_of_nonneg_right hN4 (by positivity)
            nlinarith [h3]
    have hγbound : (∫ t in (0 : ℝ)..τ, ((1 / 2) * (∑ i ∈ s, m i * ‖deriv γ t i‖ ^ 2)
          + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ t i) (γ t j))⁻¹)))
        ≤ 100000 * (∑ i ∈ s, m i) * (N : ℝ) ^ 4 * R ^ 2 / τ
            + 10 * (∑ i ∈ s, m i) ^ 2 * (N : ℝ) ^ 4 * τ / R := by
      have heqγ : (∫ t in (0:ℝ)..τ, ((1/2) * (∑ i ∈ s, m i * ‖deriv γ t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ t i) (γ t j))⁻¹)))
          = ∫ t in (0:ℝ)..τ, ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hneT, hderivγ] with t hne hd ht
        rw [Set.uIoc_of_le hτ.le] at ht
        have htIoo : t ∈ Set.Ioo (0:ℝ) τ := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
        rw [hd htIoo, hγeq t ⟨ht.1.le, ht.2⟩]
      rw [heqγ]
      have hI12 : IntervalIntegrable (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) volume (0:ℝ) (τ/2) :=
        hKint1.add hpot_int_eq
      have hI23 : IntervalIntegrable (fun t : ℝ => (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) volume (τ/2) τ :=
        hKint2.add hPint2
      have hA : (∫ t in (0:ℝ)..τ, ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)))
          = (∫ t in (0:ℝ)..(τ/2), ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)))
            + (∫ t in (τ/2)..τ, ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹))) :=
        (intervalIntegral.integral_add_adjacent_intervals hI12 hI23).symm
      have hB : (∫ t in (0:ℝ)..(τ/2), ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)))
          = (∫ t in (0:ℝ)..(τ/2), (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
            + (∫ t in (0:ℝ)..(τ/2), (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) :=
        intervalIntegral.integral_add hKint1 hpot_int_eq
      have hC : (∫ t in (τ/2)..τ, ((1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2)
              + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                  m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)))
          = (∫ t in (τ/2)..τ, (1/2) * (∑ i ∈ s, m i * ‖deriv γ2 t i‖^2))
            + (∫ t in (τ/2)..τ, (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m i * m j * (dist (γ2 t i) (γ2 t j))⁻¹)) :=
        intervalIntegral.integral_add hKint2 hPint2
      rw [hA, hB, hC]
      linarith [hKb, hPb]
    exact ⟨γ, hγ0, hγτ, hγout, hγball, hACγ, hγnc, hγInt, hγbound⟩

end Commons.Topology.Metric