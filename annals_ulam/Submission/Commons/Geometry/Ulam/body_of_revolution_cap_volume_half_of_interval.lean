import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.cap_volume_continuousOn_Ici_zero_general
import Submission.Commons.Geometry.Ulam.cap_volume_hasDerivAt_smooth_general
import Submission.Commons.Geometry.Ulam.concaveOn_Icc_bounded
import Submission.Commons.Geometry.Ulam.cap_volume_deriv_integral_eq_zero_smooth_general

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped ContDiff Pointwise RealInnerProductSpace BigOperators Topology Interval

set_option autoImplicit false

/-! Helper lemmas for the general-interval cap volume half theorem. -/

lemma profile_nonneg_Icc_general {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf_conc : ConcaveOn ℝ (Set.Icc a b) f)
    (hf_left : f a = 0) (hf_right : f b = 0) :
    ∀ t ∈ Set.Icc a b, 0 ≤ f t := by
  intro t ht
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hmin := hf_conc.min_le_of_mem_Icc ha_mem hb_mem ht
  rw [hf_left, hf_right] at hmin
  simpa using hmin

lemma profile_measurable_smooth_general {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf_support : Function.support f ⊆ Set.Icc a b)
    (hf_cont : ContDiffOn ℝ ⊤ f (Set.Ioo a b))
    (hf_left : f a = 0) (hf_right : f b = 0) :
    Measurable f := by
  classical
  let s : Set ℝ := Set.Ioo a b
  let g : ℝ → ℝ := s.piecewise f (fun _ => 0)
  have hcont_f : ContinuousOn f s := hf_cont.continuousOn
  have hcont_zero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) sᶜ := continuous_const.continuousOn
  have hg_meas : Measurable g := by
    dsimp [g, s]
    exact ContinuousOn.measurable_piecewise hcont_f hcont_zero measurableSet_Ioo
  have hfg : f = g := by
    ext t
    by_cases ht : t ∈ s
    · simp [g, s, ht]
    · have hzero : f t = 0 := by
        by_cases htc : t ∈ Set.Icc a b
        · have ht1 : a ≤ t := htc.1
          have ht2 : t ≤ b := htc.2
          have hnot : ¬ (a < t ∧ t < b) := by simpa [s] using ht
          have hle_or : t = a ∨ t = b := by
            by_cases hlt : a < t
            · right
              have hnotlt : ¬ t < b := by
                intro h; exact hnot ⟨hlt, h⟩
              exact le_antisymm ht2 (le_of_not_gt hnotlt)
            · left
              exact le_antisymm (le_of_not_gt hlt) ht1
          rcases hle_or with rfl | rfl <;> simp [hf_left, hf_right]
        · by_contra hz
          have hmem : t ∈ Function.support f := by
            simpa [Function.mem_support] using hz
          exact htc (hf_support hmem)
      simp [g, ht, hzero]
  rw [hfg]
  exact hg_meas

lemma const_on_Ioi_of_deriv_zero {f : ℝ → ℝ}
    (hderiv : ∀ s > 0, HasDerivAt f 0 s)
    (hcont : ContinuousOn f (Set.Ici 0)) :
    ∀ s > 0, f s = f 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioi 0) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv f) 0 (Set.Ioi 0) := by
    intro x hx
    exact (hderiv x hx).deriv
  have hconst : ∃ a, ∀ x ∈ Set.Ioi 0, f x = a :=
    isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv_eq
  rcases hconst with ⟨a, ha⟩
  have hcont0 : ContinuousWithinAt f (Set.Ici 0) 0 := hcont.continuousWithinAt (by simp)
  have htend : Filter.Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := by
    refine tendsto_nhdsWithin_mono_left ?_ hcont0
    intro x hx
    have hx' : 0 < x := by simpa using hx
    exact le_of_lt hx'
  have htend_const : Filter.Tendsto f (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (ha x hx).symm
  have h0a : f 0 = a := tendsto_nhds_unique htend htend_const
  intro s hs
  have hs_eq : f s = a := ha s hs
  rw [hs_eq, h0a]

lemma intervalIntegral_half_even {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (hg_even : ∀ z, g (-z) = g z) :
    (∫ z in (-a)..0, g z) = ∫ z in 0..a, g z ∧
    (∫ z in (-a)..a, g z) = 2 * ∫ z in (-a)..0, g z := by
  have hsymm : (∫ z in (-a)..0, g z) = ∫ z in 0..a, g z := by
    have hcomp := intervalIntegral.integral_comp_neg (f := g) (a := 0) (b := a)
    calc
      (∫ z in (-a)..0, g z) = ∫ z in 0..a, g (-z) := by simpa using hcomp.symm
      _ = ∫ z in 0..a, g z := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact hg_even z
  have hint01 : IntervalIntegrable g volume 0 a := hg_cont.intervalIntegrable 0 a
  have hint_neg0 : IntervalIntegrable g volume (-a) 0 := hg_cont.intervalIntegrable (-a) 0
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := g)
    (a := -a) (b := 0) (c := a) hint_neg0 hint01
  constructor
  · exact hsymm
  · calc
      (∫ z in (-a)..a, g z) = (∫ z in (-a)..0, g z) + ∫ z in 0..a, g z := hsum.symm
      _ = (∫ z in (-a)..0, g z) + ∫ z in (-a)..0, g z := by rw [hsymm]
      _ = 2 * ∫ z in (-a)..0, g z := by ring

lemma cap_integral_zero_eq_half_total_general {n : ℕ} (hn : 2 ≤ n) {a b : ℝ}
    (hab : a ≤ b) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
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
      intro z; dsimp [W]; ring
    exact (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
  have htotal_eq : (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) =
      2 * (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
    calc
      (∫ t in a..b, ∫ z in (-f t)..(f t), W t z)
        = ∫ t in a..b, 2 * (∫ z in (-f t)..0, W t z) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc a b := by
              simpa [Set.uIcc_of_le hab] using ht
            exact hinner t htIcc
      _ = 2 * (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
            rw [intervalIntegral.integral_const_mul]
  nlinarith

lemma max_min_eq_of_nonneg_le {f M : ℝ}
    (hf_nonneg : 0 ≤ f) (hf_le : f ≤ M) :
    max (-f) (min f M) = f := by
  have hmin : min f M = f := min_eq_left hf_le
  have hmax : max (-f) f = f := max_eq_right (by linarith)
  rw [hmin, hmax]

lemma inner_total_eq_general {n : ℕ} {a b : ℝ} {f : ℝ → ℝ} {M : ℝ}
    (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M) :
    let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
    (∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) M)), W t z) =
      ∫ t in a..b, ∫ z in (-f t)..(f t), W t z := by
  intro W
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using ht
  have hup : max (-f t) (min (f t) M) = f t :=
    max_min_eq_of_nonneg_le (hf_nonneg t htIcc) (hf_le_M t htIcc)
  simp [hup]

lemma K_subset_H_large_general {d : ℕ} [NeZero d] {a b : ℝ} {f : ℝ → ℝ} {M R : ℝ}
    (hab : a ≤ b) (hd : 2 ≤ d) (hR : M < R)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    K ⊆ {x | x last ≤ R} := by
  intro last K x hx
  have hlast_pos : (0 : Fin d) < last := by
    dsimp [last]
    rw [Fin.lt_def]
    simp
    omega
  have hsq_nonneg : ∀ i ∈ Finset.Ioi (0 : Fin d), 0 ≤ (x i)^2 := by
    intro i hi; exact sq_nonneg _
  have hmem : last ∈ Finset.Ioi (0 : Fin d) := by simpa using hlast_pos
  have hsingle := Finset.single_le_sum (s := Finset.Ioi (0 : Fin d))
    (f := fun i : Fin d => (x i)^2) hsq_nonneg hmem
  have hx0mem : x 0 ∈ Set.Icc a b := hx.1
  have hsum_le : ∑ i > 0, (x i)^2 ≤ f (x 0)^2 := hx.2
  have hlast_sq_le_fsq : (x last)^2 ≤ f (x 0)^2 := le_trans hsingle hsum_le
  have hf0_nonneg : 0 ≤ f (x 0) := hf_nonneg (x 0) hx0mem
  have hf0_le_M : f (x 0) ≤ M := hf_le_M (x 0) hx0mem
  have hfsq_le_Msq : f (x 0)^2 ≤ M^2 := pow_le_pow_left₀ hf0_nonneg hf0_le_M 2
  have hlast_sq_le_Msq : (x last)^2 ≤ M^2 := le_trans hlast_sq_le_fsq hfsq_le_Msq
  have hM_nonneg : 0 ≤ M := le_trans hf0_nonneg hf0_le_M
  have hlast_abs_le_M : |x last| ≤ M := by
    have hsq_abs : |x last| ^ 2 ≤ M ^ 2 := by simpa [sq_abs] using hlast_sq_le_Msq
    have h1 := (sq_le_sq (a := |x last|) (b := M)).1 hsq_abs
    simpa [abs_of_nonneg hM_nonneg, abs_abs] using h1
  have hlast_le_M : x last ≤ M := le_trans (le_abs_self _) hlast_abs_le_M
  simpa using (le_of_lt (lt_of_le_of_lt hlast_le_M hR) : x last ≤ R)

lemma body_of_revolution_cap_volume_half_of_interval
    {d : ℕ} [NeZero d] {a b : ℝ} {f h x y : ℝ → ℝ}
    (n : ℕ) (hn : 2 ≤ n) (hdn : d = 2 * n) (hab : a ≤ b)
    (hf_support : Function.support f ⊆ Set.Icc a b)
    (hf_smooth : ContDiffOn ℝ ⊤ f (Set.Ioo a b))
    (hf_conc : ConcaveOn ℝ (Set.Icc a b) f)
    (hf_left : f a = 0) (hf_right : f b = 0)
    (hf_pos : ∀ t ∈ Set.Ioo a b, 0 < f t)
    (hh_smooth : ContDiffOn ℝ ⊤ h Set.univ)
    (hh0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo a b ∧ y s ∈ Set.Ioo a b)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s →
      MeasureTheory.volume.real (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}) =
        MeasureTheory.volume.real K / 2 := by
  intro K s hs
  classical
  have hdpos : 2 ≤ d := by omega
  have hab_lt : a < b := by
    have hs1 : 0 < (1 : ℝ) := by norm_num
    have hx1 := (hxy 1 hs1).1
    have hy1 := (hxy 1 hs1).2.1
    have hinside1 := hxy_inside 1 hs1
    have ha_lt : a < -x 1 := hinside1.1.1
    have hnegx_neg : -x 1 < 0 := by linarith
    have hb_gt : y 1 < b := hinside1.2.2
    have hb_pos : 0 < b := lt_trans hy1 hb_gt
    have ha_neg : a < 0 := lt_trans ha_lt hnegx_neg
    exact lt_trans ha_neg hb_pos
  have hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t :=
    profile_nonneg_Icc_general hab hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    profile_measurable_smooth_general hab hf_support hf_smooth hf_left hf_right
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc a b) :=
    concaveOn_Icc_bounded hab hf_conc
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  let capIntegral : ℝ → ℝ := fun r =>
    ∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (r * t + h r))), W t z
  have hderiv_int := cap_volume_deriv_integral_eq_zero_smooth_general hn hab hf_support hf_conc
    hf_left hf_right hf_pos hxy hxy_inside hJ
  have hderiv_cap : ∀ r > 0, HasDerivAt capIntegral 0 r := by
    intro r hr
    have hd := cap_volume_hasDerivAt_smooth_general (n := n) (f := f) (h := h) (a := a) (b := b)
      hn hab hf_nonneg hf_meas hf_bdd hh_smooth r
    have hd' : HasDerivAt capIntegral
        (∫ t in a..b,
          if -f t < r * t + h r ∧ r * t + h r < f t then
            (f t ^ 2 - (r * t + h r) ^ 2) ^ (n - 1) * (t + deriv h r)
          else 0) r := by
      simpa [capIntegral, W] using hd
    exact hd'.congr_deriv (by simpa [capIntegral, W] using (hderiv_int r hr))
  have hcont_cap : ContinuousOn capIntegral (Set.Ici 0) := by
    have hh_cont_Ici : ContinuousOn h (Set.Ici 0) :=
      hh_smooth.continuousOn.mono (by intro x hx; simp)
    have hcont := cap_volume_continuousOn_Ici_zero_general (n := n) (f := f) (h := h) (a := a) (b := b)
      (by omega) hab hf_nonneg hf_meas hf_bdd hh_cont_Ici
    simpa [capIntegral, W] using hcont
  have hcap_const : ∀ r > 0, capIntegral r = capIntegral 0 :=
    const_on_Ioi_of_deriv_zero hderiv_cap hcont_cap
  let last : Fin d := ⟨d - 1, by omega⟩
  have hlast_eq : last = lastFin d := by
    ext; simp [last, lastFin]
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hvol_cap : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s}) =
      c * capIntegral s := by
    have hbody := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := a) (b := b)
      (s := s) (h := h s) hdn hn hab hf_nonneg hf_meas
    simpa [capIntegral, W, c, K, last, hlast_eq] using hbody.1
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc a b, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc a b, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hK_subset : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R} := by
    have hsub := K_subset_H_large_general (d := d) (a := a) (b := b) (f := f) (M := M) (R := R)
      hab hdpos hR_gt hf_nonneg hf_le_M
    simpa [K, last, R] using hsub
  have hvol_total : volume.real K = c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by
    have hinner := inner_total_eq_general (n := n) (a := a) (b := b) (f := f) (M := R) hab hf_nonneg
      (by intro t ht; exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt))
    have hvol_inter : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) =
        c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by
      have hbody1 : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) =
          c * (∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) := by
        have hb := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := a) (b := b)
          (s := 0) (h := R) hdn hn hab hf_nonneg hf_meas
        simpa [W, c, K, last, hlast_eq] using hb.1
      have hinner_eq :
          (∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) =
            ∫ t in a..b, ∫ z in (-f t)..(f t), W t z := by
        simpa [W] using hinner
      calc
        volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R})
            = c * (∫ t in a..b, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), W t z) := hbody1
        _ = c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) := by rw [hinner_eq]
    have hvolK : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ R}) = volume.real K := by
      rw [Set.inter_eq_left.mpr hK_subset]
    rw [hvolK] at hvol_inter
    simpa [W] using hvol_inter
  have hcap0 : capIntegral 0 = (∫ t in a..b, ∫ z in (-f t)..0, W t z) := by
    have h0line : ∀ t ∈ Set.Icc a b,
        max (-f t) (min (f t) (0 * t + h 0)) = 0 := by
      intro t ht
      have hf_nonneg_t : 0 ≤ f t := hf_nonneg t ht
      have hmin : min (f t) (0 * t + h 0) = 0 := by
        rw [hh0]
        simp [hf_nonneg_t]
      have hmax : max (-f t) 0 = 0 := by
        rw [max_eq_right]
        linarith
      rw [hmin, hmax]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    have hup := h0line t htIcc
    change (∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + h 0))), W t z) =
      ∫ z in (-f t)..0, W t z
    rw [hup]
  have hcap0_half : capIntegral 0 = (∫ t in a..b, ∫ z in (-f t)..(f t), W t z) / 2 := by
    rw [hcap0]
    simpa [W] using cap_integral_zero_eq_half_total_general (n := n) hn hab hf_nonneg
  have hs_eq : capIntegral s = capIntegral 0 := hcap_const s hs
  calc
    MeasureTheory.volume.real (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s})
        = c * capIntegral s := by simpa [last] using hvol_cap
    _ = c * capIntegral 0 := by rw [hs_eq]
    _ = c * ((∫ t in a..b, ∫ z in (-f t)..(f t), W t z) / 2) := by rw [hcap0_half]
    _ = (c * (∫ t in a..b, ∫ z in (-f t)..(f t), W t z)) / 2 := by ring
    _ = MeasureTheory.volume.real K / 2 := by rw [← hvol_total]

end Commons.Geometry.Ulam
