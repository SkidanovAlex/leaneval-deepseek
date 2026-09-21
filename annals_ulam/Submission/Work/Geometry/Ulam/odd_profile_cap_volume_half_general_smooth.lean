import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_pi
import Submission.Work.Geometry.Ulam.odd_cap_volume_hasDerivAt_smooth_general
import Submission.Commons.Geometry.Ulam.concaveOn_Icc_bounded
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval
import Submission.Commons.Geometry.Ulam.moment_h_bounds
import Submission.Work.Geometry.Ulam.profile_measurable_smooth_general_inf
import Submission.Work.Geometry.Ulam.active_nonneg_outside_of_roots_inside_general
import Submission.Work.Geometry.Ulam.active_nonneg_outside_of_roots_inside_general

namespace Commons.Geometry.Ulam

open MeasureTheory
open Set Filter
open scoped ContDiff Pointwise RealInnerProductSpace BigOperators Topology Interval

set_option autoImplicit false

private lemma odd_weight_eq_zero_of_not_active {n : ℕ} {f L : ℝ}
    (hf_nonneg : 0 ≤ f)
    (hnot : ¬ (-f < L ∧ L < f)) :
    (f ^ 2 - L ^ 2) ^ (n - 1) * Real.sqrt (f ^ 2 - L ^ 2) = 0 := by
  have hbase_nonpos : f ^ 2 - L ^ 2 ≤ 0 := by
    by_cases hL_le : L ≤ -f
    · have hf_le_negL : f ≤ -L := by linarith
      have hL_nonneg_neg : 0 ≤ -L := by linarith
      have hsq : f ^ 2 ≤ L ^ 2 := by
        rw [← neg_sq L]
        exact (sq_le_sq₀ hf_nonneg hL_nonneg_neg).2 hf_le_negL
      nlinarith
    · have hnegf_lt_L : -f < L := lt_of_not_ge hL_le
      have hf_le_L : f ≤ L := le_of_not_gt (by
        intro hLf
        exact hnot ⟨hnegf_lt_L, hLf⟩)
      have hL_nonneg : 0 ≤ L := le_trans hf_nonneg hf_le_L
      have hsq : f ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hf_nonneg hL_nonneg).2 hf_le_L
      nlinarith
  rw [Real.sqrt_eq_zero_of_nonpos hbase_nonpos, mul_zero]

private lemma odd_cap_integral_zero_eq_half_total {n : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    let W : ℝ → ℝ → ℝ := fun t z =>
      (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
    (∫ t in a..b, ∫ z in (-f t)..0, W t z) =
      (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) / 2 := by
  intro W
  have hinner : ∀ t ∈ Set.Icc a b,
      (∫ z in (-f t)..(f t), W t z) = 2 * ∫ z in (-f t)..0, W t z := by
    intro t ht
    have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
    have hg_cont : Continuous (fun z => W t z) := by
      dsimp [W]; fun_prop
    have hg_even : ∀ z, W t (-z) = W t z := by
      intro z
      dsimp [W]
      have harg : f t ^ 2 - (-z) ^ 2 = f t ^ 2 - z ^ 2 := by ring
      rw [harg]
    exact (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
  have htotal_eq : (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) =
      2 * (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
    calc
      (∫ t in a..b, ∫ z in (-f t)..(f t), W t z)
        = ∫ t in a..b, 2 * (∫ z in (-f t)..0, W t z) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc a b := by
              simpa [Set.uIcc_of_le (hab.le)] using ht
            exact hinner t htIcc
      _ = 2 * (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
            rw [intervalIntegral.integral_const_mul]
  nlinarith

private lemma odd_cap_volume_deriv_integral_eq_zero {n : ℕ} {a b : ℝ} (hab : a < b)
    {h x y f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc a b) f)
    (hf_left : f a = 0) (hf_right : f b = 0)
    (hf_pos : ∀ t ∈ Set.Ioo a b, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo a b ∧ y s ∈ Set.Ioo a b)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in a..b,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
            (t + deriv h s)
        else 0) = 0 := by
  intro s hs
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  rcases hxy_inside s hs with ⟨hp_mem, hq_mem⟩
  let p : ℝ := -x s
  let q : ℝ := y s
  have hp_neg : p < 0 := by dsimp [p]; linarith
  have hq_pos : 0 < q := by dsimp [q]; exact hypos
  have hfp_sq : f p ^ 2 = (s * p + h s) ^ 2 := by simpa [p] using hfx_sq
  have hfq_sq : f q ^ 2 = (s * q + h s) ^ 2 := by simpa [q] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t :=
    profile_nonneg_Icc_general (a := a) (b := b) hab.le hf_conc hf_left hf_right
  have hactive := active_nonneg_outside_of_roots_inside_general (s := s) (h := h s)
    (u := p) (v := q) (α := a) (β := b) hs hp_mem hq_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (L t) ^ 2)
  let C : ℝ := deriv h s
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then W t * (t + C) else 0
  let G : ℝ → ℝ := fun t => if p ≤ t ∧ t ≤ q then W t * (t + C) else 0
  have hW_p : W p = 0 := by
    dsimp [W, L]
    have hbase : f p ^ 2 - (s * p + h s) ^ 2 = 0 := by rw [hfp_sq]; ring
    rw [hbase]
    simp [Real.sqrt_zero]
  have hW_q : W q = 0 := by
    dsimp [W, L]
    have hbase : f q ^ 2 - (s * q + h s) ^ 2 = 0 := by rw [hfq_sq]; ring
    rw [hbase]
    simp [Real.sqrt_zero]
  have hFG : Set.EqOn F G (Set.Icc a b) := by
    intro t ht
    by_cases htab : p ≤ t ∧ t ≤ q
    · have hnonneg := hactive.2 t htab
      have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
      have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
      have hW_zero_of_not : ¬ (-f t < L t ∧ L t < f t) → W t = 0 := by
        intro hnot
        have hg_pos_or : ¬ 0 < f t - L t ∨ ¬ 0 < f t + L t := by
          by_contra hboth
          have hboth' : 0 < f t - L t ∧ 0 < f t + L t := by
            simpa [not_or, not_lt] using hboth
          apply hnot
          constructor <;> dsimp [L] at * <;> linarith
        rcases hg_pos_or with hg_not | hq_not
        · have hg0 : f t - L t = 0 := le_antisymm (le_of_not_gt hg_not) hg_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hg0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [Real.sqrt_zero]
        · have hq0 : f t + L t = 0 := le_antisymm (le_of_not_gt hq_not) hq_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hq0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [Real.sqrt_zero]
      dsimp [F, G]
      rw [if_pos htab]
      by_cases hact : -f t < L t ∧ L t < f t
      · rw [if_pos hact]
      · rw [if_neg hact, hW_zero_of_not hact]
        simp
    · have hact_false : ¬ (-f t < L t ∧ L t < f t) := by
        intro hact
        exact htab (hactive.1 t ht hact)
      dsimp [F, G]
      rw [if_neg htab, if_neg hact_false]
  have hF_eq_G : (∫ t in a..b, F t) = ∫ t in a..b, G t := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le (hab.le)] using hFG
  have hsuppG_abG : Function.support G ⊆ Set.Ioc a b := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : p ≤ t ∧ t ≤ q
    · have ht_gt : a < t := lt_of_lt_of_le hp_mem.1 htab.1
      have ht_le : t ≤ b := le_trans htab.2 (le_of_lt hq_mem.2)
      exact ⟨ht_gt, ht_le⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hsuppG_ab : Function.support G ⊆ Set.Ioc p q := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : p ≤ t ∧ t ≤ q
    · have hta_ne : t ≠ p := by
        intro hta
        have hG0 : G t = 0 := by
          subst t
          simp [G, hW_p]
        exact (ht hG0).elim
      have hta_lt : p < t := lt_of_le_of_ne htab.1 (Ne.symm hta_ne)
      exact ⟨hta_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_abG
  have hIab := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := p) (b := q) hsuppG_ab
  have hpq : p < q := lt_trans hp_neg hq_pos
  have hG_ab_eq : (∫ t in p..q, G t) = ∫ t in p..q, W t * (t + C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : p ≤ t ∧ t ≤ q := by
      rw [Set.uIcc_of_le hpq.le] at ht
      exact ht
    dsimp [G]
    rw [if_pos htab]
  have hJ' : (∫ t in p..q, W t * (t + C)) = 0 := by
    have hJ0 := hJ s hs
    simpa [p, q, W, L, C] using hJ0
  have hmain : (∫ t in a..b, F t) = 0 := by
    calc
      (∫ t in a..b, F t) = ∫ t in a..b, G t := hF_eq_G
      _ = ∫ t, G t := hI1
      _ = ∫ t in p..q, G t := hIab.symm
      _ = ∫ t in p..q, W t * (t + C) := hG_ab_eq
      _ = 0 := hJ'
  simpa [F, L, W, C] using hmain

private lemma body_of_revolution_cap_volume_pi_euclidean {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x last ≤ s * x 0 + h}
    let W : ℝ → ℝ → ℝ := fun t z =>
      (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
    volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z := by
  intro last K H W c
  let e : (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have he_mp : MeasurePreserving (⇑e) volume volume := PiLp.volume_preserving_toLp (ι := Fin d)
  let Kf : Set (Fin d → ℝ) :=
    {x | x 0 ∈ Set.Icc a b ∧ ∑ i > (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
  let Hf : Set (Fin d → ℝ) := {x | x last ≤ s * x 0 + h}
  have hpre_e : e ⁻¹' (K ∩ H) = Kf ∩ Hf := by
    ext x
    simp [K, H, Kf, Hf, e, PiLp.toLp_apply]
  have hvol_trans : volume.real (K ∩ H) = volume.real (Kf ∩ Hf) := by
    rw [← hpre_e]
    exact (MeasurePreserving.measureReal_preimage_emb he_mp (K ∩ H)).symm
  have hfun := body_of_revolution_cap_integrals_pi (d := d) (n := n) (a := a) (b := b)
    (s := s) (h := h) (f := f) hdn hn hab hf_nonneg hf_meas
  rw [hvol_trans]
  simpa [Kf, Hf, W, c] using hfun.1

lemma odd_profile_cap_volume_half_general_smooth {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {a b : ℝ} (hab : a < b) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc a b)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo a b))
    (hf_conc : ConcaveOn ℝ (Set.Icc a b) f)
    (hf_left : f a = 0) (hf_right : f b = 0)
    (hf_pos : ∀ t ∈ Set.Ioo a b, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo a b ∧ y s ∈ Set.Ioo a b)
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s →
      MeasureTheory.volume.real (K ∩ {x | x ⟨d-1, by omega⟩ ≤ s * x 0 + h s}) =
        MeasureTheory.volume.real K / 2 := by
  classical
  intro K s hs
  let last : Fin d := ⟨d - 1, by omega⟩
  have hdpos : 2 ≤ d := by omega
  have hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t :=
    profile_nonneg_Icc_general (a := a) (b := b) hab.le hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    profile_measurable_smooth_general_inf (a := a) (b := b) hab.le hf_support hf_cont hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc a b) :=
    concaveOn_Icc_bounded hab.le hf_conc
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc a b, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let W : ℝ → ℝ → ℝ := fun t z =>
    (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let capIntegral : ℝ → ℝ := fun r =>
    ∫ t in a..b, ∫ z in (-f t)..(min (f t) (r * t + h r)), W t z
  have hderiv_int := odd_cap_volume_deriv_integral_eq_zero (n := n) (a := a) (b := b) hab hf_conc hf_left hf_right
    hf_pos hxy hxy_inside h_center
  have hderiv_cap : ∀ r > 0, HasDerivAt capIntegral 0 r := by
    intro r hr
    have hd := odd_cap_volume_hasDerivAt_smooth_general (n := n) (f := f) (h := h) (a := a) (b := b)
      hn hab.le hf_nonneg hf_meas hf_bdd hh_cont r
    have hd' : HasDerivAt capIntegral
        (∫ t in a..b,
          (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
            (t + deriv h r)) r := by
      simpa [capIntegral, W] using hd
    have hplain_eq_if :
        (∫ t in a..b,
          (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
            (t + deriv h r)) =
        ∫ t in a..b,
          if -f t < r * t + h r ∧ r * t + h r < f t then
            (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
              (t + deriv h r)
          else 0 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab.le] using ht
      by_cases hact : -f t < r * t + h r ∧ r * t + h r < f t
      · simp [hact]
      · have hW0 := odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := r * t + h r)
          (hf_nonneg t htIcc) hact
        simp [hact, hW0]
    have hderiv_zero :
        (∫ t in a..b,
          (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (r * t + h r) ^ 2) *
            (t + deriv h r)) = 0 := by
      rw [hplain_eq_if]
      simpa [W] using (hderiv_int r hr)
    exact hd'.congr_deriv hderiv_zero
  have hcont_cap : ContinuousOn capIntegral (Set.Ici 0) := by
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      have hd := odd_cap_volume_hasDerivAt_smooth_general (n := n) (f := f) (h := h) (a := a) (b := b)
        hn hab.le hf_nonneg hf_meas hf_bdd hh_cont (0 : ℝ)
      exact hd.continuousAt.continuousWithinAt
    · have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hd := odd_cap_volume_hasDerivAt_smooth_general (n := n) (f := f) (h := h) (a := a) (b := b)
        hn hab.le hf_nonneg hf_meas hf_bdd hh_cont r
      exact hd.continuousAt.continuousWithinAt
  have hcap_const : ∀ r > 0, capIntegral r = capIntegral 0 :=
    const_on_Ioi_of_deriv_zero hderiv_cap hcont_cap
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hvol_cap : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s}) =
      c * capIntegral s := by
    have hbody := body_of_revolution_cap_volume_pi_euclidean (d := d) (n := n) (a := a) (b := b)
      (s := s) (h := h s) hdn hn hab.le hf_nonneg hf_meas
    simpa [capIntegral, W, c, K, last] using hbody
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hK_subset : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R} := by
    simpa [K, last, R] using
      (K_subset_H_large_general (d := d) (a := a) (b := b) (f := f) (M := M) (R := R)
        hab.le hdpos hR_gt hf_nonneg hf_le_M)
  have hvol_total : volume.real K = c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by
    have hbody := body_of_revolution_cap_integrals_pi (d := d) (n := n) (a := a) (b := b)
      (s := 0) (h := R) hdn hn hab.le hf_nonneg hf_meas
    have hmin_eq : ∀ t ∈ Set.Icc a b, min (f t) R = f t := by
      intro t ht
      have hf_le : f t ≤ R := le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt)
      exact min_eq_left hf_le
    have hvol_inter : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) =
        c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by
      have hbody1 : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) =
          c * (∫ t in a..b, ∫ z in (-f t)..(min (f t) R), W t z) := by
        have hbody' := body_of_revolution_cap_volume_pi_euclidean (d := d) (n := n) (a := a) (b := b)
          (s := 0) (h := R) hdn hn hab.le hf_nonneg hf_meas
        simpa [W, c, K, last] using hbody'
      have hinner_eq :
          (∫ t in a..b, ∫ z in (-f t)..(min (f t) R), W t z) =
            ∫ t in a..b, ∫ z in (-f t)..(f t), W t z := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc a b := by
          simpa [Set.uIcc_of_le hab.le] using ht
        change (∫ z in (-f t)..(min (f t) R), W t z) = ∫ z in (-f t)..(f t), W t z
        rw [hmin_eq t htIcc]
      calc
        volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R})
            = c * (∫ t in a..b, ∫ z in (-f t)..(min (f t) R), W t z) := hbody1
        _ = c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by rw [hinner_eq]
    have hvolK : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) = volume.real K := by
      rw [Set.inter_eq_left.mpr hK_subset]
    rw [hvolK] at hvol_inter
    simpa [W] using hvol_inter
  have hcap0 : capIntegral 0 = (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
    dsimp [capIntegral]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab.le] using ht
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t htIcc
    have hmin : min (f t) (0 * t + h 0) = 0 := by
      rw [h0]
      simp [hf_nonneg_t]
    change (∫ z in (-f t)..(min (f t) (0 * t + h 0)), W t z) =
      ∫ z in (-f t)..0, W t z
    rw [hmin]
  have hcap0_half : capIntegral 0 = (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) / 2 := by
    rw [hcap0]
    simpa [W] using (odd_cap_integral_zero_eq_half_total (n := n) (a := a) (b := b) hab (f := f) hf_nonneg)
  have hs_eq : capIntegral s = capIntegral 0 := hcap_const s hs
  calc
    MeasureTheory.volume.real (K ∩ {x | x ⟨d-1, by omega⟩ ≤ s * x 0 + h s})
        = c * capIntegral s := by simpa [last] using hvol_cap
    _ = c * capIntegral 0 := by rw [hs_eq]
    _ = c * ((∫ t in a..b, ∫ z in (-f t)..(f t), W t z) / 2) := by rw [hcap0_half]
    _ = (c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z)) / 2 := by ring
    _ = MeasureTheory.volume.real K / 2 := by rw [← hvol_total]

end Commons.Geometry.Ulam
