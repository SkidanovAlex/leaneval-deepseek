import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds_smooth

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace Topology Interval

set_option autoImplicit false

private lemma even_concave_antitoneOn_Icc_zero_one {f : ℝ → ℝ}
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_even : ∀ t : ℝ, f (-t) = f t) :
    AntitoneOn f (Set.Icc 0 1) := by
  intro u hu v hv huv
  by_cases hlt : u < v
  · have hu0 : 0 ≤ u := hu.1
    have hvpos' : 0 < v := by linarith
    have hnegv_mem : -v ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hv.2, hvpos']
    have hv_mem_neg : v ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hvpos', hv.2]
    let lam : ℝ := (u + v) / (2 * v)
    have hden : 2 * v ≠ 0 := by positivity
    have hlam_nonneg : 0 ≤ lam := by
      dsimp [lam]
      positivity
    have hlam_le_one : lam ≤ 1 := by
      dsimp [lam]
      rw [div_le_one]
      · linarith
      · positivity
    have h1lam_nonneg : 0 ≤ 1 - lam := by linarith
    have hsum : (1 - lam) + lam = 1 := by ring
    have hcombo : (1 - lam) * (-v) + lam * v = u := by
      dsimp [lam]
      field_simp [hden]
      ring
    have hconc := hf_conc.2 hnegv_mem hv_mem_neg h1lam_nonneg hlam_nonneg hsum
    have hle : (1 - lam) * f (-v) + lam * f v ≤ f u := by
      have hpoint : (1 - lam) • (-v) + lam • v = u := by
        rw [smul_eq_mul, smul_eq_mul]
        exact hcombo
      rw [← hpoint]
      exact hconc
    rw [hf_even v] at hle
    have hle' : f v ≤ f u := by
      nlinarith [hle, hsum]
    exact hle'
  · have h_eq : u = v := le_antisymm huv (le_of_not_gt hlt)
    subst v
    rfl

private lemma sub_linear_strictAntiOn_Icc_zero_one {f : ℝ → ℝ} {s : ℝ}
    (hs : 0 < s) (hf_anti : AntitoneOn f (Set.Icc 0 1)) :
    StrictAntiOn (fun t : ℝ => f t - s * t) (Set.Icc 0 1) := by
  intro u hu v hv huv
  have hf_le : f v ≤ f u := hf_anti hu hv (le_of_lt huv)
  have hsu_lt : s * u < s * v := mul_lt_mul_of_pos_left huv hs
  dsimp
  linarith

private lemma even_profile_roots_order_of_h_pos
    {s x y h : ℝ} {f : ℝ → ℝ}
    (hs : 0 < s) (hxpos : 0 < x) (hypos : 0 < y)
    (hx_mem : x ∈ Set.Icc 0 1) (hy_mem : y ∈ Set.Icc 0 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_even : ∀ t : ℝ, f (-t) = f t)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hfy_sq : f y ^ 2 = (s * y + h) ^ 2)
    (hfx_sq : f (-x) ^ 2 = (s * (-x) + h) ^ 2)
    (hh : 0 < h) : y < x := by
  have hf_anti : AntitoneOn f (Set.Icc 0 1) :=
    even_concave_antitoneOn_Icc_zero_one hf_conc hf_even
  have hF_anti : StrictAntiOn (fun t : ℝ => f t - s * t) (Set.Icc 0 1) :=
    sub_linear_strictAntiOn_Icc_zero_one hs hf_anti
  have hx_Icc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hx_mem.1], by linarith [hx_mem.2]⟩
  have hy_Icc : y ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hy_mem.1], by linarith [hy_mem.2]⟩
  have hfy_lin_nonneg : 0 ≤ s * y + h := by positivity
  have hfy_eq : f y = s * y + h :=
    eq_of_sq_eq_sq_of_nonneg_of_nonneg hfy_sq (hf_nonneg y hy_Icc) hfy_lin_nonneg
  have hFy : f y - s * y = h := by linarith
  have hfx_sq' : f x ^ 2 = (h - s * x) ^ 2 := by
    have hraw := hfx_sq
    rw [hf_even x] at hraw
    convert hraw using 2
    ring
  have hfx_abs : f x = |h - s * x| := by
    have hsq := (sq_eq_sq_iff_abs_eq_abs (f x) (h - s * x)).mp hfx_sq'
    have hfx_nonneg : 0 ≤ f x := hf_nonneg x hx_Icc
    simpa [abs_of_nonneg hfx_nonneg] using hsq
  have hFx_lt : f x - s * x < h := by
    rw [hfx_abs]
    by_cases hle : s * x ≤ h
    · have hnonneg : 0 ≤ h - s * x := sub_nonneg.mpr hle
      rw [abs_of_nonneg hnonneg]
      have hsx_pos : 0 < s * x := mul_pos hs hxpos
      linarith
    · have hlt : h - s * x < 0 := sub_neg.mpr (lt_of_not_ge hle)
      rw [abs_of_neg hlt]
      have hsx_pos : 0 < s * x := mul_pos hs hxpos
      linarith
  have hnot : ¬ x ≤ y := by
    intro hxy_le
    by_cases heq : x = y
    · subst y
      linarith
    · have hxy_lt : x < y := lt_of_le_of_ne hxy_le heq
      have hFlt : f y - s * y < f x - s * x := hF_anti hx_mem hy_mem hxy_lt
      linarith
  exact lt_of_not_ge hnot

private lemma even_profile_roots_order_of_h_neg
    {s x y h : ℝ} {f : ℝ → ℝ}
    (hs : 0 < s) (hxpos : 0 < x) (hypos : 0 < y)
    (hx_mem : x ∈ Set.Icc 0 1) (hy_mem : y ∈ Set.Icc 0 1)
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_even : ∀ t : ℝ, f (-t) = f t)
    (hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t)
    (hfy_sq : f y ^ 2 = (s * y + h) ^ 2)
    (hfx_sq : f (-x) ^ 2 = (s * (-x) + h) ^ 2)
    (hh : h < 0) : x < y := by
  have hf_anti : AntitoneOn f (Set.Icc 0 1) :=
    even_concave_antitoneOn_Icc_zero_one hf_conc hf_even
  have hF_anti : StrictAntiOn (fun t : ℝ => f t - s * t) (Set.Icc 0 1) :=
    sub_linear_strictAntiOn_Icc_zero_one hs hf_anti
  have hx_Icc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hx_mem.1], by linarith [hx_mem.2]⟩
  have hy_Icc : y ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hy_mem.1], by linarith [hy_mem.2]⟩
  have hfx_sq' : f x ^ 2 = (h - s * x) ^ 2 := by
    have hraw := hfx_sq
    rw [hf_even x] at hraw
    convert hraw using 2
    ring
  have hfx_abs : f x = |h - s * x| := by
    have hsq := (sq_eq_sq_iff_abs_eq_abs (f x) (h - s * x)).mp hfx_sq'
    have hfx_nonneg : 0 ≤ f x := hf_nonneg x hx_Icc
    simpa [abs_of_nonneg hfx_nonneg] using hsq
  have hdiff_x_neg : h - s * x < 0 := by
    have hsx_pos : 0 < s * x := mul_pos hs hxpos
    linarith
  have hFx : f x - s * x = -h := by
    rw [hfx_abs, abs_of_neg hdiff_x_neg]
    ring
  have hfy_abs : f y = |s * y + h| := by
    have hsq := (sq_eq_sq_iff_abs_eq_abs (f y) (s * y + h)).mp hfy_sq
    have hfy_nonneg : 0 ≤ f y := hf_nonneg y hy_Icc
    simpa [abs_of_nonneg hfy_nonneg] using hsq
  have hFy_lt : f y - s * y < -h := by
    rw [hfy_abs]
    by_cases hle : 0 ≤ s * y + h
    · rw [abs_of_nonneg hle]
      linarith
    · have hlt : s * y + h < 0 := lt_of_not_ge hle
      rw [abs_of_neg hlt]
      have hsy_pos : 0 < s * y := mul_pos hs hypos
      linarith
  have hnot : ¬ y ≤ x := by
    intro hyx_le
    by_cases heq : y = x
    · subst x
      linarith
    · have hyx_lt : y < x := lt_of_le_of_ne hyx_le heq
      have hFlt : f x - s * x < f y - s * y := hF_anti hy_mem hx_mem hyx_lt
      linarith
  exact lt_of_not_ge hnot

-- TODO add moment weight data helper and target proof

private lemma exists_pos_lt_of_continuousAt_pos {W : ℝ → ℝ} {y : ℝ}
    (hy : 0 < y) (hcont : ContinuousAt W 0) (h0 : 0 < W 0) :
    ∃ c : ℝ, 0 < c ∧ c < y ∧ 0 < W c := by
  have hhalf : 0 < W 0 / 2 := half_pos h0
  have htend : Filter.Tendsto W (𝓝[>] (0:ℝ)) (𝓝 (W 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : ∀ᶠ t in 𝓝[>] (0:ℝ), W 0 / 2 < W t :=
    (tendsto_order.1 htend).1 (W 0 / 2) (by linarith)
  have hlt_y : ∀ᶠ t in 𝓝[>] (0:ℝ), t < y :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (a := (0:ℝ)) (b := y) hy)
  have hpos_mem : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioi (0:ℝ) := self_mem_nhdsWithin
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := by
    filter_upwards [hpos_mem] with t ht
    exact ht
  have hall : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t < y ∧ W 0 / 2 < W t := by
    filter_upwards [hpos, hlt_y, hlow] with t ht hty hw
    exact ⟨ht, hty, hw⟩
  rcases hall.exists with ⟨c, hc⟩
  refine ⟨c, hc.1, hc.2.1, ?_⟩
  linarith [hc.2.2, hhalf]

private lemma intervalIntegral_symm_eq_integral_add_neg_of_continuousOn {f : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hf : ContinuousOn f (Set.Icc (-a) a)) :
    (∫ t in (-a)..a, f t) = ∫ t in 0..a, (f t + f (-t)) := by
  have hneg_cont : ContinuousOn (fun t : ℝ => -t) (Set.Icc 0 a) := by fun_prop
  have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc 0 a) (Set.Icc (-a) a) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, ha]
  have hfneg_cont : ContinuousOn (fun t : ℝ => f (-t)) (Set.Icc 0 a) :=
    hf.comp hneg_cont hmaps
  have hf_int_left : IntervalIntegrable f MeasureTheory.volume (-a) 0 := by
    have hmono : Set.Icc (-a) 0 ⊆ Set.Icc (-a) a := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, ha]
    exact (hf.mono hmono).intervalIntegrable_of_Icc (by linarith [ha])
  have hf_int_right : IntervalIntegrable f MeasureTheory.volume 0 a := by
    have hmono : Set.Icc 0 a ⊆ Set.Icc (-a) a := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, ha]
    exact (hf.mono hmono).intervalIntegrable_of_Icc ha
  have hfneg_int : IntervalIntegrable (fun t : ℝ => f (-t)) MeasureTheory.volume 0 a :=
    hfneg_cont.intervalIntegrable_of_Icc ha
  have hneg : (∫ t in (-a)..0, f t) = ∫ t in 0..a, f (-t) := by
    have h := intervalIntegral.integral_comp_neg (f := fun t : ℝ => f (-t)) (a := -a) (b := 0)
    simpa using h
  calc
    (∫ t in (-a)..a, f t) = (∫ t in (-a)..0, f t) + (∫ t in 0..a, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hf_int_left hf_int_right).symm
    _ = (∫ t in 0..a, f (-t)) + (∫ t in 0..a, f t) := by rw [hneg]
    _ = ∫ t in 0..a, (f t + f (-t)) := by
      rw [add_comm]
      exact (intervalIntegral.integral_add hf_int_right hfneg_int).symm

private lemma moment_first_moment_neg_of_h_pos
    {n : ℕ} {s x y h : ℝ} {f : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hs : 0 < s) (hxpos : 0 < x) (hypos : 0 < y)
    (hxy_lt : y < x)
    (hf_even : ∀ t : ℝ, f (-t) = f t)
    (hh : 0 < h)
    (hbase_nonneg : ∀ t ∈ Set.Icc (-x) y, 0 ≤ f t ^ 2 - (s * t + h) ^ 2)
    (hW_nonneg : ∀ t ∈ Set.Icc (-x) y, 0 ≤ (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1))
    (hW_cont : ContinuousOn (fun t : ℝ => (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1)) (Set.Icc (-x) y))
    (hW0_pos : 0 < (f 0 ^ 2 - h ^ 2) ^ (n - 1)) :
    (∫ t in (-x)..y, (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) * t) < 0 := by
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1)
  have hW_cont' : ContinuousOn W (Set.Icc (-x) y) := by simpa [W] using hW_cont
  have hW_nonneg' : ∀ t ∈ Set.Icc (-x) y, 0 ≤ W t := by simpa [W] using hW_nonneg
  have hbase_nonneg' : ∀ t ∈ Set.Icc (-x) y, 0 ≤ f t ^ 2 - (s * t + h) ^ 2 := hbase_nonneg
  have hW0_pos' : 0 < W 0 := by simpa [W] using hW0_pos
  have hm : n - 1 ≠ 0 := by omega
  have hneg_y_pos : 0 < y := hypos
  have hx_neg_y_le : -x ≤ -y := by linarith [hxy_lt]
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-x) y := by
    constructor <;> linarith [hxy_lt, hypos]
  have hF_cont : ContinuousOn (fun t : ℝ => W t * t) (Set.Icc (-x) y) :=
    hW_cont'.mul continuousOn_id
  have hF_int_tail : IntervalIntegrable (fun t : ℝ => W t * t) MeasureTheory.volume (-x) (-y) := by
    have hmono : Set.Icc (-x) (-y) ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · exact ht.1
      · linarith [ht.2, hypos]
    exact (hF_cont.mono hmono).intervalIntegrable_of_Icc hx_neg_y_le
  have hF_int_symm : IntervalIntegrable (fun t : ℝ => W t * t) MeasureTheory.volume (-y) y := by
    have hmono : Set.Icc (-y) y ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · linarith [hx_neg_y_le, ht.1]
      · exact ht.2
    exact (hF_cont.mono hmono).intervalIntegrable_of_Icc (by linarith [hypos])
  have hI1_split : (∫ t in (-x)..y, W t * t) =
      (∫ t in (-x)..(-y), W t * t) + (∫ t in (-y)..y, W t * t) :=
    (intervalIntegral.integral_add_adjacent_intervals hF_int_tail hF_int_symm).symm
  have htail_nonpos : (∫ t in (-x)..(-y), W t * t) ≤ 0 := by
    have hneg_nonneg : 0 ≤ ∫ t in (-x)..(-y), -(W t * t) := by
      apply intervalIntegral.integral_nonneg hx_neg_y_le
      intro t ht
      have ht_ab : t ∈ Set.Icc (-x) y := by
        constructor
        · exact ht.1
        · linarith [ht.2, hypos]
      have hWt : 0 ≤ W t := hW_nonneg' t ht_ab
      have ht_neg : t < 0 := lt_of_le_of_lt ht.2 (by linarith [hypos])
      have hmul : W t * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWt (le_of_lt ht_neg)
      linarith
    have hneg_eq : (∫ t in (-x)..(-y), -(W t * t)) = - (∫ t in (-x)..(-y), W t * t) := by
      simpa using (intervalIntegral.integral_neg (f := fun t : ℝ => W t * t) (a := -x) (b := -y))
    linarith
  have hF_symm_cont : ContinuousOn (fun t : ℝ => W t * t) (Set.Icc (-y) y) := by
    have hmono : Set.Icc (-y) y ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · linarith [hx_neg_y_le, ht.1]
      · exact ht.2
    exact hF_cont.mono hmono
  have hsymm_eq : (∫ t in (-y)..y, W t * t) = ∫ t in 0..y, (W t * t + W (-t) * (-t)) :=
    intervalIntegral_symm_eq_integral_add_neg_of_continuousOn (by linarith [hypos]) hF_symm_cont
  have hsymm_eq' : (∫ t in (-y)..y, W t * t) = ∫ t in 0..y, (t * (W t - W (-t))) := by
    rw [hsymm_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hW_le_symm : ∀ t ∈ Set.Icc 0 y, W t ≤ W (-t) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hty : t ≤ y := ht.2
    have ht_ab : t ∈ Set.Icc (-x) y := by
      constructor
      · linarith
      · exact hty
    have hbase_t : 0 ≤ f t ^ 2 - (s * t + h) ^ 2 := hbase_nonneg' t ht_ab
    have hdiff_sq : (h - s * t) ^ 2 ≤ (s * t + h) ^ 2 := by
      have hdiff : (s * t + h) ^ 2 - (h - s * t) ^ 2 = 4 * s * t * h := by ring
      have hdiff_nonneg : 0 ≤ 4 * s * t * h := by positivity
      nlinarith
    have hbase_le : f t ^ 2 - (s * t + h) ^ 2 ≤ f t ^ 2 - (h - s * t) ^ 2 := by
      nlinarith
    have hWneg : W (-t) = (f t ^ 2 - (h - s * t) ^ 2) ^ (n - 1) := by
      dsimp [W]
      rw [hf_even t]
      congr 1
      ring
    have hWt : W t = (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) := rfl
    rw [hWt, hWneg]
    exact pow_le_pow_left₀ hbase_t hbase_le (n - 1)
  have hIcc_nhds : Set.Icc (-x) y ∈ 𝓝 0 := by
    rw [mem_nhds_iff_exists_Ioo_subset]
    refine ⟨-x, y, ?_, ?_⟩
    · constructor <;> linarith [hxy_lt, hypos]
    · intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hW_contAt0 : ContinuousAt W 0 := hW_cont'.continuousAt hIcc_nhds
  rcases exists_pos_lt_of_continuousAt_pos hypos hW_contAt0 hW0_pos' with ⟨c, hc_pos, hc_lt, hcW_pos⟩
  have hc_mem : c ∈ Set.Icc 0 y := ⟨le_of_lt hc_pos, le_of_lt hc_lt⟩
  have hc_ab : c ∈ Set.Icc (-x) y := by
    constructor
    · linarith
    · exact le_of_lt hc_lt
  have hbase_c : 0 ≤ f c ^ 2 - (s * c + h) ^ 2 := hbase_nonneg' c hc_ab
  have hcW_lt : W c < W (-c) := by
    have hdiff_sq : (h - s * c) ^ 2 < (s * c + h) ^ 2 := by
      have hdiff : (s * c + h) ^ 2 - (h - s * c) ^ 2 = 4 * s * c * h := by ring
      have hdiff_pos : 0 < 4 * s * c * h := by positivity
      nlinarith
    have hbase_lt : f c ^ 2 - (s * c + h) ^ 2 < f c ^ 2 - (h - s * c) ^ 2 := by
      nlinarith
    have hWnegc : W (-c) = (f c ^ 2 - (h - s * c) ^ 2) ^ (n - 1) := by
      dsimp [W]
      rw [hf_even c]
      congr 1
      ring
    have hWc : W c = (f c ^ 2 - (s * c + h) ^ 2) ^ (n - 1) := rfl
    rw [hWc, hWnegc]
    exact pow_lt_pow_left₀ hbase_lt hbase_c hm
  have hdiff_lt_exists : ∃ c ∈ Set.Icc 0 y, c * (W c - W (-c)) < 0 := by
    refine ⟨c, hc_mem, ?_⟩
    have hdiff_neg : W c - W (-c) < 0 := sub_neg.mpr hcW_lt
    have := mul_neg_of_pos_of_neg hc_pos hdiff_neg
    simpa using this
  have hdiff_cont : ContinuousOn (fun t : ℝ => t * (W t - W (-t))) (Set.Icc 0 y) := by
    have hW_0y : ContinuousOn W (Set.Icc 0 y) := by
      have hmono : Set.Icc 0 y ⊆ Set.Icc (-x) y := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      exact hW_cont'.mono hmono
    have hneg_cont : ContinuousOn (fun t : ℝ => -t) (Set.Icc 0 y) := by fun_prop
    have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc 0 y) (Set.Icc (-x) y) := by
      intro t ht
      constructor <;> linarith [hxy_lt, ht.1, ht.2, hypos]
    have hWneg_cont : ContinuousOn (fun t : ℝ => W (-t)) (Set.Icc 0 y) :=
      hW_cont'.comp hneg_cont hmaps
    exact continuousOn_id.mul (hW_0y.sub hWneg_cont)
  have hsymm_neg : (∫ t in 0..y, t * (W t - W (-t))) < 0 := by
    have hlt : (∫ t in 0..y, t * (W t - W (-t))) < (∫ t in 0..y, (0 : ℝ)) := by
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (f := fun t : ℝ => t * (W t - W (-t))) (g := fun _ : ℝ => (0 : ℝ))
        hypos hdiff_cont continuousOn_const ?_ ?_
      · intro t ht
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have hty : t ≤ y := ht.2
        have ht_mem : t ∈ Set.Icc 0 y := ⟨ht0, hty⟩
        have hWle : W t ≤ W (-t) := hW_le_symm t ht_mem
        have hdiff_le : W t - W (-t) ≤ 0 := sub_nonpos.mpr hWle
        exact mul_nonpos_of_nonneg_of_nonpos ht0 hdiff_le
      · exact hdiff_lt_exists
    simpa using hlt
  have hsymm_nonpos : (∫ t in (-y)..y, W t * t) < 0 := by
    rw [hsymm_eq']
    exact hsymm_neg
  have hI1 : (∫ t in (-x)..y, W t * t) < 0 := by
    rw [hI1_split]
    linarith
  simpa [W, mul_comm] using hI1

private lemma moment_first_moment_pos_of_h_neg
    {n : ℕ} {s x y h : ℝ} {f : ℝ → ℝ}
    (hn : 2 ≤ n)
    (hs : 0 < s) (hxpos : 0 < x) (hypos : 0 < y)
    (hxy_lt : x < y)
    (hf_even : ∀ t : ℝ, f (-t) = f t)
    (hh : h < 0)
    (hbase_nonneg : ∀ t ∈ Set.Icc (-x) y, 0 ≤ f t ^ 2 - (s * t + h) ^ 2)
    (hW_nonneg : ∀ t ∈ Set.Icc (-x) y, 0 ≤ (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1))
    (hW_cont : ContinuousOn (fun t : ℝ => (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1)) (Set.Icc (-x) y))
    (hW0_pos : 0 < (f 0 ^ 2 - h ^ 2) ^ (n - 1)) :
    (∫ t in (-x)..y, (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) * t) > 0 := by
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1)
  have hW_cont' : ContinuousOn W (Set.Icc (-x) y) := by simpa [W] using hW_cont
  have hW_nonneg' : ∀ t ∈ Set.Icc (-x) y, 0 ≤ W t := by simpa [W] using hW_nonneg
  have hbase_nonneg' : ∀ t ∈ Set.Icc (-x) y, 0 ≤ f t ^ 2 - (s * t + h) ^ 2 := hbase_nonneg
  have hW0_pos' : 0 < W 0 := by simpa [W] using hW0_pos
  have hm : n - 1 ≠ 0 := by omega
  have hx_pos : 0 < x := hxpos
  have hx_le_y : x ≤ y := le_of_lt hxy_lt
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-x) y := by
    constructor <;> linarith [hxpos, hypos]
  have hF_cont : ContinuousOn (fun t : ℝ => W t * t) (Set.Icc (-x) y) :=
    hW_cont'.mul continuousOn_id
  have hF_int_symm : IntervalIntegrable (fun t : ℝ => W t * t) MeasureTheory.volume (-x) x := by
    have hmono : Set.Icc (-x) x ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · exact ht.1
      · linarith [ht.2, hx_le_y]
    exact (hF_cont.mono hmono).intervalIntegrable_of_Icc (by linarith [hxpos])
  have hF_int_tail : IntervalIntegrable (fun t : ℝ => W t * t) MeasureTheory.volume x y := by
    have hmono : Set.Icc x y ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · linarith [hxpos, ht.1]
      · exact ht.2
    exact (hF_cont.mono hmono).intervalIntegrable_of_Icc hx_le_y
  have hI1_split : (∫ t in (-x)..y, W t * t) =
      (∫ t in (-x)..x, W t * t) + (∫ t in x..y, W t * t) :=
    (intervalIntegral.integral_add_adjacent_intervals hF_int_symm hF_int_tail).symm
  have htail_nonneg : 0 ≤ (∫ t in x..y, W t * t) := by
    apply intervalIntegral.integral_nonneg hx_le_y
    intro t ht
    have ht_ab : t ∈ Set.Icc (-x) y := by
      constructor
      · linarith [hxpos, ht.1]
      · exact ht.2
    have hWt : 0 ≤ W t := hW_nonneg' t ht_ab
    have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hxpos) ht.1
    exact mul_nonneg hWt ht_nonneg
  have hF_symm_cont : ContinuousOn (fun t : ℝ => W t * t) (Set.Icc (-x) x) := by
    have hmono : Set.Icc (-x) x ⊆ Set.Icc (-x) y := by
      intro t ht
      constructor
      · exact ht.1
      · linarith [ht.2, hx_le_y]
    exact hF_cont.mono hmono
  have hsymm_eq : (∫ t in (-x)..x, W t * t) = ∫ t in 0..x, (W t * t + W (-t) * (-t)) :=
    intervalIntegral_symm_eq_integral_add_neg_of_continuousOn (by linarith [hxpos]) hF_symm_cont
  have hsymm_eq' : (∫ t in (-x)..x, W t * t) = ∫ t in 0..x, (t * (W t - W (-t))) := by
    rw [hsymm_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hWneg_le_symm : ∀ t ∈ Set.Icc 0 x, W (-t) ≤ W t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htx : t ≤ x := ht.2
    have ht_neg_ab : -t ∈ Set.Icc (-x) y := by
      constructor
      · linarith
      · linarith [hx_pos, hxy_lt]
    have hbase_neg_t : 0 ≤ f t ^ 2 - (h - s * t) ^ 2 := by
      have hbase_neg := hbase_nonneg' (-t) ht_neg_ab
      rw [hf_even t] at hbase_neg
      convert hbase_neg using 1
      ring
    have hdiff_sq : (s * t + h) ^ 2 ≤ (h - s * t) ^ 2 := by
      have hdiff : (h - s * t) ^ 2 - (s * t + h) ^ 2 = - (4 * s * t * h) := by ring
      have hprod_nonpos : 4 * s * t * h ≤ 0 := by
        have h1 : 0 ≤ 4 * s * t := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos h1 (le_of_lt hh)
      nlinarith
    have hbase_le : f t ^ 2 - (h - s * t) ^ 2 ≤ f t ^ 2 - (s * t + h) ^ 2 := by
      nlinarith
    have hWneg : W (-t) = (f t ^ 2 - (h - s * t) ^ 2) ^ (n - 1) := by
      dsimp [W]
      rw [hf_even t]
      congr 1
      ring
    have hWt : W t = (f t ^ 2 - (s * t + h) ^ 2) ^ (n - 1) := rfl
    rw [hWneg, hWt]
    exact pow_le_pow_left₀ hbase_neg_t hbase_le (n - 1)
  have hIcc_nhds : Set.Icc (-x) y ∈ 𝓝 0 := by
    rw [mem_nhds_iff_exists_Ioo_subset]
    refine ⟨-x, y, ?_, ?_⟩
    · constructor <;> linarith [hxpos, hypos]
    · intro t ht
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hW_contAt0 : ContinuousAt W 0 := hW_cont'.continuousAt hIcc_nhds
  rcases exists_pos_lt_of_continuousAt_pos hxpos hW_contAt0 hW0_pos' with ⟨c, hc_pos, hc_lt, hcW_pos⟩
  have hc_mem : c ∈ Set.Icc 0 x := ⟨le_of_lt hc_pos, le_of_lt hc_lt⟩
  have hc_neg_ab : -c ∈ Set.Icc (-x) y := by
    constructor
    · linarith [hc_lt]
    · linarith [hx_pos, hxy_lt]
  have hbase_neg_c : 0 ≤ f c ^ 2 - (h - s * c) ^ 2 := by
    have hbase_neg := hbase_nonneg' (-c) hc_neg_ab
    rw [hf_even c] at hbase_neg
    convert hbase_neg using 1
    ring
  have hcW_lt : W (-c) < W c := by
    have hdiff_sq : (s * c + h) ^ 2 < (h - s * c) ^ 2 := by
      have hdiff : (h - s * c) ^ 2 - (s * c + h) ^ 2 = - (4 * s * c * h) := by ring
      have hprod_neg : 4 * s * c * h < 0 := by
        have h1 : 0 < 4 * s * c := by positivity
        exact mul_neg_of_pos_of_neg h1 hh
      nlinarith
    have hbase_lt : f c ^ 2 - (h - s * c) ^ 2 < f c ^ 2 - (s * c + h) ^ 2 := by
      nlinarith
    have hWnegc : W (-c) = (f c ^ 2 - (h - s * c) ^ 2) ^ (n - 1) := by
      dsimp [W]
      rw [hf_even c]
      congr 1
      ring
    have hWc : W c = (f c ^ 2 - (s * c + h) ^ 2) ^ (n - 1) := rfl
    rw [hWnegc, hWc]
    exact pow_lt_pow_left₀ hbase_lt hbase_neg_c hm
  have hdiff_gt_exists : ∃ c ∈ Set.Icc 0 x, 0 < c * (W c - W (-c)) := by
    refine ⟨c, hc_mem, ?_⟩
    have hdiff_pos : 0 < W c - W (-c) := sub_pos.mpr hcW_lt
    have := mul_pos hc_pos hdiff_pos
    simpa using this
  have hdiff_cont : ContinuousOn (fun t : ℝ => t * (W t - W (-t))) (Set.Icc 0 x) := by
    have hW_0x : ContinuousOn W (Set.Icc 0 x) := by
      have hmono : Set.Icc 0 x ⊆ Set.Icc (-x) y := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2, hx_le_y]
      exact hW_cont'.mono hmono
    have hneg_cont : ContinuousOn (fun t : ℝ => -t) (Set.Icc 0 x) := by fun_prop
    have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc 0 x) (Set.Icc (-x) y) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2, hx_pos, hxy_lt]
    have hWneg_cont : ContinuousOn (fun t : ℝ => W (-t)) (Set.Icc 0 x) :=
      hW_cont'.comp hneg_cont hmaps
    exact continuousOn_id.mul (hW_0x.sub hWneg_cont)
  have hsymm_pos : 0 < (∫ t in 0..x, t * (W t - W (-t))) := by
    refine intervalIntegral.integral_pos hxpos hdiff_cont ?_ ?_
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have htx : t ≤ x := ht.2
      have ht_mem : t ∈ Set.Icc 0 x := ⟨ht0, htx⟩
      have hWle : W (-t) ≤ W t := hWneg_le_symm t ht_mem
      have hdiff_nonneg : 0 ≤ W t - W (-t) := sub_nonneg.mpr hWle
      exact mul_nonneg ht0 hdiff_nonneg
    · exact hdiff_gt_exists
  have hsymm_nonneg : 0 < (∫ t in (-x)..x, W t * t) := by
    rw [hsymm_eq']
    exact hsymm_pos
  have hI1 : 0 < (∫ t in (-x)..y, W t * t) := by
    rw [hI1_split]
    linarith
  simpa [W, mul_comm] using hI1

private lemma moment_weight_data_smooth
    {n : ℕ} {h x y f : ℝ → ℝ} {s : ℝ}
    (hn : 2 ≤ n)
    (hs : 0 < s) (hneg : -s < h s) (hpos : h s < s)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hxy : ∀ r : ℝ, 0 < r → 0 < x r ∧ 0 < y r ∧
      (f (y r)) ^ 2 = (r * y r + h r) ^ 2 ∧
      (f (-x r)) ^ 2 = (r * (-x r) + h r) ^ 2)
    (hinside : -x s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y s ∈ Set.Ioo (-1 : ℝ) 1) :
    let a := -x s; let b := y s; let L := fun t : ℝ => s * t + h s; let W := fun t : ℝ => (f t ^ 2 - (L t) ^ 2) ^ (n - 1);
    (∀ t ∈ Set.Icc a b, 0 ≤ f t ^ 2 - (L t) ^ 2) ∧
      (∀ t ∈ Set.Icc a b, 0 ≤ W t) ∧ 0 < W 0 ∧ ContinuousOn W (Set.Icc a b) := by
  dsimp
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  let a : ℝ := -x s
  let b : ℝ := y s
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  have ha_neg : a < 0 := by dsimp [a]; linarith
  have hb_pos : 0 < b := by dsimp [b]; exact hypos
  have hab : a < b := lt_trans ha_neg hb_pos
  have ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [a] using hinside.1
  have hb_mem : b ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [b] using hinside.2
  have hfa_sq : f a ^ 2 = (s * a + h s) ^ 2 := by simpa [a] using hfx_sq
  have hfb_sq : f b ^ 2 = (s * b + h s) ^ 2 := by simpa [b] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have hactive := active_nonneg_outside_of_roots_inside (s := s) (h := h s) (a := a) (b := b)
    hs ha_mem hb_mem ha_neg hb_pos hf_conc hf_nonneg hf_pos hfa_sq hfb_sq
  have hbase_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t ^ 2 - (L t) ^ 2 := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
    have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
    nlinarith
  have hW_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ W t := by
    intro t ht
    have hA_nonneg : 0 ≤ f t ^ 2 - (L t) ^ 2 := hbase_nonneg t ht
    dsimp [W]
    positivity
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ha_mem.1, ha_mem.2, hb_mem.1, hb_mem.2, ht.1, ht.2]
  have hf_cont_Icc : ContinuousOn f (Set.Icc a b) :=
    hf_cont.continuousOn.mono hIcc_sub
  have hL_cont_Icc : ContinuousOn L (Set.Icc a b) := by
    dsimp [L]
    fun_prop
  have hA_cont : ContinuousOn (fun t => f t ^ 2 - (L t) ^ 2) (Set.Icc a b) :=
    (hf_cont_Icc.pow 2).sub (hL_cont_Icc.pow 2)
  have hW_cont : ContinuousOn W (Set.Icc a b) := by
    dsimp [W]
    exact hA_cont.pow (n - 1)
  have hphi_conc : ConcaveOn ℝ (Set.Icc a b) (fun t => f t - |L t|) := by
    have hf_sub : ConcaveOn ℝ (Set.Icc a b) f :=
      hf_conc.subset (by
        intro t ht
        exact ⟨le_trans (Set.Ioo_subset_Icc_self ha_mem).1 ht.1,
          le_trans ht.2 (Set.Ioo_subset_Icc_self hb_mem).2⟩)
        (convex_Icc a b)
    have hL_abs_conc : ConcaveOn ℝ (Set.Icc a b) (fun t => - |L t|) := by
      have hL_abs_conv : ConvexOn ℝ Set.univ (fun t : ℝ => |L t|) := by
        refine ⟨convex_univ, ?_⟩
        intro u hu v hv p q hp hq hpq
        simp only [smul_eq_mul]
        have hL_combo : L (p * u + q * v) = p * L u + q * L v := by
          dsimp [L]
          ring_nf
          nlinarith [hpq]
        rw [hL_combo]
        calc
          |p * L u + q * L v| ≤ |p * L u| + |q * L v| := abs_add_le _ _
          _ = p * |L u| + q * |L v| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
      have hL_abs_conc' : ConcaveOn ℝ Set.univ (fun t : ℝ => - |L t|) := by
        exact neg_concaveOn_iff.mpr hL_abs_conv
      exact hL_abs_conc'.subset (by intro t ht; trivial) (convex_Icc a b)
    exact hf_sub.add hL_abs_conc
  have hphi_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t - |L t| := by
    intro t ht
    have hnonneg := hactive.2 t ht
    have hg_nonneg : 0 ≤ f t - L t := by simpa [L] using hnonneg.1
    have hq_nonneg : 0 ≤ f t + L t := by simpa [L] using hnonneg.2
    have : |L t| ≤ f t := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hphi_a : f a - |L a| = 0 := by
    have hfa_nonneg : 0 ≤ f a := hf_nonneg a (Set.Ioo_subset_Icc_self ha_mem)
    rcases le_total (L a) 0 with hLa_nonpos | hLa_nonneg
    · have hfa_eq : f a = - L a :=
        eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hfa_sq hfa_nonneg hLa_nonpos
      rw [abs_of_nonpos hLa_nonpos]
      linarith
    · have hfa_eq : f a = L a :=
        eq_of_sq_eq_sq_of_nonneg_of_nonneg hfa_sq hfa_nonneg hLa_nonneg
      rw [abs_of_nonneg hLa_nonneg]
      linarith
  have hphi_b : f b - |L b| = 0 := by
    have hfb_nonneg : 0 ≤ f b := hf_nonneg b (Set.Ioo_subset_Icc_self hb_mem)
    rcases le_total (L b) 0 with hLb_nonpos | hLb_nonneg
    · have hfb_eq : f b = - L b :=
        eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hfb_sq hfb_nonneg hLb_nonpos
      rw [abs_of_nonpos hLb_nonpos]
      linarith
    · have hfb_eq : f b = L b :=
        eq_of_sq_eq_sq_of_nonneg_of_nonneg hfb_sq hfb_nonneg hLb_nonneg
      rw [abs_of_nonneg hLb_nonneg]
      linarith
  have hphi0_pos : 0 < f 0 - |L 0| := by
    have h0_mem : (0 : ℝ) ∈ Set.Icc a b := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
    by_contra hnot
    have hphi0 : f 0 - |L 0| = 0 := by
      exact le_antisymm (le_of_not_gt hnot) (hphi_nonneg 0 h0_mem)
    have hphi_zero_all := concave_nonneg_eq_zero_of_interior_zero (a := a) (b := b) (c := 0)
      ha_neg hb_pos hphi_conc hphi_a hphi_b hphi0 hphi_nonneg
    have hf_abs_all : ∀ t ∈ Set.Icc a b, f t = |L t| := by
      intro t ht
      have hz := hphi_zero_all t ht
      linarith [hphi_nonneg t ht]
    exact not_eq_abs_affine_of_concave_and_abs_h_lt_s hs hneg hpos ha_mem hb_mem ha_neg hb_pos
      hf_conc hf_left hf_right hf_abs_all
  have hW0_pos : 0 < W 0 := by
    have h0_mem : (0 : ℝ) ∈ Set.Icc a b := ⟨le_of_lt ha_neg, le_of_lt hb_pos⟩
    have hf0_pos : 0 < f 0 := hf_pos 0 (by norm_num)
    have hL0 : L 0 = h s := by simp [L]
    have hf0_gt : |L 0| < f 0 := by
      have : 0 < f 0 - |L 0| := hphi0_pos
      linarith
    have hA0_pos : 0 < f 0 ^ 2 - (L 0) ^ 2 := by
      have hf0_nonneg : 0 ≤ f 0 := le_of_lt hf0_pos
      have hL0_abs_nonneg : 0 ≤ |L 0| := abs_nonneg _
      have hsq_lt : (L 0) ^ 2 < (f 0) ^ 2 := by
        apply sq_lt_sq.mpr
        simpa [abs_of_pos hf0_pos] using hf0_gt
      linarith
    dsimp [W]
    exact pow_pos hA0_pos (n - 1)
  exact ⟨hbase_nonneg, hW_nonneg, hW0_pos, hW_cont⟩


lemma even_profile_deriv_sign
    (n : ℕ) (hn : 2 ≤ n) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1 : ℝ) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1 : ℝ) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hf_even : ∀ t : ℝ, f (-t) = f t)
    (hxy : ∀ s : ℝ, 0 < s →
      0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s → (0 < h s → 0 < deriv h s) ∧ (h s < 0 → deriv h s < 0) := by
  intro s hs
  have hb := moment_h_bounds_smooth (n := n) hn (h := h) (x := x) (y := y) (f := f)
    hf_support hf_cont hf_conc hf_left hf_right hf_pos hh_cont h0 hxy hJ s hs
  rcases hb with ⟨hneg_s, hpos_s⟩
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  have hinside := roots_inside_of_abs_h_lt_s hf_support hf_left hf_right hxy hs hneg_s hpos_s
  have hw := moment_weight_data_smooth (n := n) hn (h := h) (x := x) (y := y) (f := f)
    hs hneg_s hpos_s hf_cont hf_conc hf_left hf_right hf_pos hxy hinside
  rcases hw with ⟨hbase_nonneg_let, hW_nonneg_let, hW0_pos_let, hW_cont_let⟩
  let a : ℝ := -x s
  let b : ℝ := y s
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let C : ℝ := deriv h s
  have hbase_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t ^ 2 - (s * t + h s) ^ 2 := by
    simpa [a, b] using hbase_nonneg_let
  have hW_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ W t := by
    simpa [W, L, a, b] using hW_nonneg_let
  have hW0_pos : 0 < W 0 := by
    simpa [W, L] using hW0_pos_let
  have hW_cont : ContinuousOn W (Set.Icc a b) := by
    simpa [W, L, a, b] using hW_cont_let
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t :=
    even_profile_nonneg_Icc hf_conc hf_left hf_right
  have ha_neg : a < 0 := by dsimp [a]; linarith
  have hb_pos : 0 < b := by dsimp [b]; exact hypos
  have hab : a < b := lt_trans ha_neg hb_pos
  have hab_le : a ≤ b := le_of_lt hab
  have hI0_pos : 0 < ∫ t in a..b, W t := by
    refine intervalIntegral.integral_pos hab hW_cont ?_ ?_
    · intro t ht
      exact hW_nonneg t (Set.Ioc_subset_Icc_self ht)
    · refine ⟨0, ?_, hW0_pos⟩
      constructor <;> linarith [ha_neg, hb_pos]
  have hJ_ab : (∫ t in a..b, W t * (t + C)) = 0 := by
    dsimp [W, L, C, a, b]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hJ s hs
  have hWmul_cont : ContinuousOn (fun t : ℝ => W t * (t + C)) (Set.Icc a b) := by
    dsimp [W, L, C]
    fun_prop
  have hWt_cont : ContinuousOn (fun t : ℝ => W t * t) (Set.Icc a b) := by
    dsimp [W, L]
    fun_prop
  have hWC_cont : ContinuousOn (fun t : ℝ => W t * C) (Set.Icc a b) := by
    dsimp [W, L, C]
    fun_prop
  have hW_int : IntervalIntegrable W MeasureTheory.volume a b :=
    hW_cont.intervalIntegrable_of_Icc hab_le
  have hWt_int : IntervalIntegrable (fun t : ℝ => W t * t) MeasureTheory.volume a b :=
    hWt_cont.intervalIntegrable_of_Icc hab_le
  have hWC_int : IntervalIntegrable (fun t : ℝ => W t * C) MeasureTheory.volume a b :=
    hWC_cont.intervalIntegrable_of_Icc hab_le
  have hsum_int : IntervalIntegrable (fun t : ℝ => W t * t + W t * C) MeasureTheory.volume a b :=
    hWt_int.add hWC_int
  have h_congr : (∫ t in a..b, W t * (t + C)) = ∫ t in a..b, (W t * t + W t * C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have h_add : (∫ t in a..b, (W t * t + W t * C)) =
      (∫ t in a..b, W t * t) + (∫ t in a..b, W t * C) :=
    intervalIntegral.integral_add hWt_int hWC_int
  have h_mulC : (∫ t in a..b, W t * C) = (∫ t in a..b, W t) * C :=
    intervalIntegral.integral_mul_const C W
  have hJ_sum : (∫ t in a..b, W t * t) + (∫ t in a..b, W t) * C = 0 := by
    rw [← h_mulC, ← h_add, ← h_congr]
    exact hJ_ab
  have hI0_ne : (∫ t in a..b, W t) ≠ 0 := ne_of_gt hI0_pos
  have hC_eq : C = - (∫ t in a..b, W t * t) / (∫ t in a..b, W t) := by
    rw [eq_div_iff hI0_ne]
    linarith
  constructor
  · intro hh_pos
    have hx_mem : x s ∈ Set.Icc 0 1 := ⟨le_of_lt hxpos, by linarith [hinside.1.1]⟩
    have hy_mem : y s ∈ Set.Icc 0 1 := ⟨le_of_lt hypos, by linarith [hinside.2.2]⟩
    have hxy_lt : y s < x s := even_profile_roots_order_of_h_pos hs hxpos hypos hx_mem hy_mem
      hf_conc hf_even hf_nonneg hfy_sq hfx_sq hh_pos
    have hI1_neg := moment_first_moment_neg_of_h_pos (n := n) hn (s := s) (x := x s) (y := y s) (h := h s) (f := f)
      hs hxpos hypos hxy_lt hf_even hh_pos hbase_nonneg hW_nonneg hW_cont (by simpa [W, L] using hW0_pos)
    have hI1_neg' : (∫ t in a..b, W t * t) < 0 := by
      simpa [W, L, a, b, mul_comm] using hI1_neg
    have hC_pos : 0 < C := by
      rw [hC_eq]
      have hnum_pos : 0 < - (∫ t in a..b, W t * t) := by linarith
      exact div_pos hnum_pos hI0_pos
    simpa [C] using hC_pos
  · intro hh_neg
    have hx_mem : x s ∈ Set.Icc 0 1 := ⟨le_of_lt hxpos, by linarith [hinside.1.1]⟩
    have hy_mem : y s ∈ Set.Icc 0 1 := ⟨le_of_lt hypos, by linarith [hinside.2.2]⟩
    have hxy_lt : x s < y s := even_profile_roots_order_of_h_neg hs hxpos hypos hx_mem hy_mem
      hf_conc hf_even hf_nonneg hfy_sq hfx_sq hh_neg
    have hI1_pos := moment_first_moment_pos_of_h_neg (n := n) hn (s := s) (x := x s) (y := y s) (h := h s) (f := f)
      hs hxpos hypos hxy_lt hf_even hh_neg hbase_nonneg hW_nonneg hW_cont (by simpa [W, L] using hW0_pos)
    have hI1_pos' : 0 < (∫ t in a..b, W t * t) := by
      simpa [W, L, a, b, mul_comm] using hI1_pos
    have hC_neg : C < 0 := by
      rw [hC_eq]
      have hnum_neg : - (∫ t in a..b, W t * t) < 0 := by linarith
      exact div_neg_of_neg_of_pos hnum_neg hI0_pos
    simpa [C] using hC_neg

end Commons.Geometry.Ulam
