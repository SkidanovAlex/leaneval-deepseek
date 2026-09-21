import Mathlib
import Submission.Commons.Geometry.Ulam.moment_h_bounds

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace Interval

set_option autoImplicit false
set_option maxHeartbeats 800000

private lemma concave_nonneg_Icc_general {α β : ℝ} {f : ℝ → ℝ}
    (hαβ : α ≤ β)
    (hf_conc : ConcaveOn ℝ (Set.Icc α β) f)
    (hf_left : f α = 0) (hf_right : f β = 0) :
    ∀ t ∈ Set.Icc α β, 0 ≤ f t := by
  intro t ht
  have hmin := hf_conc.min_le_of_mem_Icc (x := α) (y := β) (z := t)
    (by exact ⟨le_rfl, hαβ⟩) (by exact ⟨hαβ, le_rfl⟩) ht
  rw [hf_left, hf_right] at hmin
  simpa using hmin

private lemma active_nonneg_outside_of_roots_inside_general
    {f : ℝ → ℝ} {s h u v α β : ℝ} (hs : 0 < s)
    (hu_mem : u ∈ Set.Ioo α β) (hv_mem : v ∈ Set.Ioo α β)
    (hu_neg : u < 0) (hv_pos : 0 < v)
    (hf_conc : ConcaveOn ℝ (Set.Icc α β) f)
    (hf_nonneg : ∀ t ∈ Set.Icc α β, 0 ≤ f t)
    (hf_pos : ∀ t ∈ Set.Ioo α β, 0 < f t)
    (hfu_sq : f u ^ 2 = (s * u + h) ^ 2)
    (hfv_sq : f v ^ 2 = (s * v + h) ^ 2) :
    (∀ t ∈ Set.Icc α β, (-f t < s * t + h ∧ s * t + h < f t) → u ≤ t ∧ t ≤ v) ∧
    (∀ t ∈ Set.Icc u v, 0 ≤ f t - (s * t + h) ∧ 0 ≤ f t + (s * t + h)) := by
  let L : ℝ → ℝ := fun t => s * t + h
  have hLmono : Monotone L := by
    intro p q hpq
    dsimp [L]
    have hle : s * p ≤ s * q := mul_le_mul_of_nonneg_left hpq (le_of_lt hs)
    linarith
  have hg_conc : ConcaveOn ℝ (Set.Icc α β) (fun t => f t - L t) := by
    dsimp [L]
    exact concaveOn_sub_affine f s h α β hf_conc
  have hq_conc : ConcaveOn ℝ (Set.Icc α β) (fun t => f t + L t) := by
    dsimp [L]
    exact concaveOn_add_affine f s h α β hf_conc
  have hu_Icc : u ∈ Set.Icc α β := Set.Ioo_subset_Icc_self hu_mem
  have hv_Icc : v ∈ Set.Icc α β := Set.Ioo_subset_Icc_self hv_mem
  have hfu_nonneg : 0 ≤ f u := hf_nonneg u hu_Icc
  have hfv_nonneg : 0 ≤ f v := hf_nonneg v hv_Icc
  have hfu_pos : 0 < f u := hf_pos u hu_mem
  have hfv_pos : 0 < f v := hf_pos v hv_mem
  have hLu : L u = s * u + h := rfl
  have hLv : L v = s * v + h := rfl
  have huv : u < v := lt_trans hu_neg hv_pos
  have hsq_u : f u ^ 2 = (L u) ^ 2 := by simpa [L] using hfu_sq
  have hsq_v : f v ^ 2 = (L v) ^ 2 := by simpa [L] using hfv_sq
  by_cases hLu_nonpos : L u ≤ 0
  · by_cases hLv_nonpos : L v ≤ 0
    · have hLu_neg : L u < 0 := lt_of_le_of_ne hLu_nonpos (by
        intro hLu0
        have hfu0 : f u = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg hLu_nonpos
          linarith
        linarith)
      have hLv_neg : L v < 0 := lt_of_le_of_ne hLv_nonpos (by
        intro hLv0
        have hfv0 : f v = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_v hfv_nonneg hLv_nonpos
          linarith
        linarith)
      have hqu : (fun t => f t + L t) u = 0 := by
        dsimp
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hqv : (fun t => f t + L t) v = 0 := by
        dsimp
        have hfv := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_v hfv_nonneg (le_of_lt hLv_neg)
        linarith
      have hq := concave_nonneg_between_of_zero (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hq_conc hqu hqv
      constructor
      · intro t ht hact
        by_cases htu : u ≤ t
        · by_cases htv : t ≤ v
          · exact ⟨htu, htv⟩
          · have hgt : v < t := lt_of_not_ge htv
            have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.2 t ⟨le_of_lt hgt, ht.2⟩
            have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
            linarith
        · have hlt : t < u := lt_of_not_ge htu
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2.1 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        have hLt_nonpos : L t ≤ 0 := le_trans (hLmono ht.2) hLv_nonpos
        have ht_Icc : t ∈ Set.Icc α β := ⟨le_trans hu_Icc.1 ht.1, le_trans ht.2 hv_Icc.2⟩
        have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
        have hg_nonneg : 0 ≤ f t - L t := by linarith
        exact ⟨by simpa [L] using hg_nonneg, hq.1 t ht⟩
    · have hLu_neg : L u < 0 := lt_of_le_of_ne hLu_nonpos (by
        intro hLu0
        have hfu0 : f u = 0 := by
          have h := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg hLu_nonpos
          linarith
        linarith)
      have hLv_pos : 0 < L v := lt_of_not_ge hLv_nonpos
      have hqu : (fun t => f t + L t) u = 0 := by
        dsimp
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hgv : (fun t => f t - L t) v = 0 := by
        dsimp
        have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
        linarith
      have hq_v_pos : 0 < (fun t => f t + L t) v := by
        dsimp [L]
        have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
        linarith
      have hg_u_pos : 0 < (fun t => f t - L t) u := by
        dsimp [L]
        have hfu := eq_neg_of_sq_eq_sq_of_nonneg_of_nonpos hsq_u hfu_nonneg (le_of_lt hLu_neg)
        linarith
      have hq := concave_nonneg_between_of_zero_left (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hq_conc hqu hq_v_pos
      have hg := concave_nonneg_between_of_zero_right (α := α) (β := β) (u := u) (v := v)
        (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hg_conc hg_u_pos hgv
      constructor
      · intro t ht hact
        by_cases htu : u ≤ t
        · by_cases htv : t ≤ v
          · exact ⟨htu, htv⟩
          · have hgt : v < t := lt_of_not_ge htv
            have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2 t ⟨le_of_lt hgt, ht.2⟩
            have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
            linarith
        · have hlt : t < u := lt_of_not_ge htu
          have hq_le : (fun t => f t + L t) t ≤ 0 := hq.2 t ⟨ht.1, le_of_lt hlt⟩
          have hq_pos : 0 < (fun t => f t + L t) t := by dsimp; linarith [hact.1]
          linarith
      · intro t ht
        exact ⟨hg.1 t ht, hq.1 t ht⟩
  · have hLu_pos : 0 < L u := lt_of_not_ge hLu_nonpos
    have hLv_pos : 0 < L v := lt_of_lt_of_le hLu_pos (hLmono (le_of_lt huv))
    have hgu : (fun t => f t - L t) u = 0 := by
      dsimp
      have hfu := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_u hfu_nonneg (le_of_lt hLu_pos)
      linarith
    have hgv : (fun t => f t - L t) v = 0 := by
      dsimp
      have hfv := eq_of_sq_eq_sq_of_nonneg_of_nonneg hsq_v hfv_nonneg (le_of_lt hLv_pos)
      linarith
    have hg := concave_nonneg_between_of_zero (α := α) (β := β) (u := u) (v := v)
      (hαu := hu_Icc.1) (huv := huv) (hvβ := hv_Icc.2) hg_conc hgu hgv
    constructor
    · intro t ht hact
      by_cases htu : u ≤ t
      · by_cases htv : t ≤ v
        · exact ⟨htu, htv⟩
        · have hgt : v < t := lt_of_not_ge htv
          have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.2 t ⟨le_of_lt hgt, ht.2⟩
          have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
          linarith
      · have hlt : t < u := lt_of_not_ge htu
        have hg_le : (fun t => f t - L t) t ≤ 0 := hg.2.1 t ⟨ht.1, le_of_lt hlt⟩
        have hg_pos : 0 < (fun t => f t - L t) t := by dsimp; linarith [hact.2]
        linarith
    · intro t ht
      have hLt_nonneg : 0 ≤ L t := le_trans hLu_pos.le (hLmono ht.1)
      have ht_Icc : t ∈ Set.Icc α β := ⟨le_trans hu_Icc.1 ht.1, le_trans ht.2 hv_Icc.2⟩
      have hft_nonneg : 0 ≤ f t := hf_nonneg t ht_Icc
      have hq_nonneg : 0 ≤ f t + L t := by linarith
      exact ⟨hg.1 t ht, by simpa [L] using hq_nonneg⟩

lemma cap_volume_deriv_integral_eq_zero_smooth_general {n : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} {h x y f : ℝ → ℝ}
    (hab : a ≤ b)
    (hf_support : Function.support f ⊆ Set.Icc a b)
    (hf_conc : ConcaveOn ℝ (Set.Icc a b) f)
    (hf_left : f a = 0) (hf_right : f b = 0)
    (hf_pos : ∀ t ∈ Set.Ioo a b, 0 < f t)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo a b ∧ y s ∈ Set.Ioo a b)
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s : ℝ, 0 < s →
      (∫ t in a..b,
        if -f t < s * t + h s ∧ s * t + h s < f t then
          (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)
        else 0) = 0 := by
  intro s hs
  rcases hxy s hs with ⟨hxpos, hypos, hfy_sq, hfx_sq⟩
  rcases hxy_inside s hs with ⟨ha_mem, hb_mem⟩
  let p : ℝ := -x s
  let q : ℝ := y s
  have hp_neg : p < 0 := by dsimp [p]; linarith
  have hq_pos : 0 < q := by dsimp [q]; exact hypos
  have hfp_sq : f p ^ 2 = (s * p + h s) ^ 2 := by simpa [p] using hfx_sq
  have hfq_sq : f q ^ 2 = (s * q + h s) ^ 2 := by simpa [q] using hfy_sq
  have hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t :=
    concave_nonneg_Icc_general hab hf_conc hf_left hf_right
  have hactive := active_nonneg_outside_of_roots_inside_general (s := s) (h := h s)
    (u := p) (v := q) (α := a) (β := b)
    hs ha_mem hb_mem hp_neg hq_pos hf_conc hf_nonneg hf_pos hfp_sq hfq_sq
  let L : ℝ → ℝ := fun t => s * t + h s
  let W : ℝ → ℝ := fun t => (f t ^ 2 - (L t) ^ 2) ^ (n - 1)
  let C : ℝ := deriv h s
  let F : ℝ → ℝ := fun t => if -f t < L t ∧ L t < f t then W t * (t + C) else 0
  let G : ℝ → ℝ := fun t => if p ≤ t ∧ t ≤ q then W t * (t + C) else 0
  have hn1 : 0 < n - 1 := by omega
  have hW_p : W p = 0 := by
    dsimp [W, L]
    have hbase : f p ^ 2 - (s * p + h s) ^ 2 = 0 := by rw [hfp_sq]; ring
    rw [hbase]
    simp [hn1.ne']
  have hW_q : W q = 0 := by
    dsimp [W, L]
    have hbase : f q ^ 2 - (s * q + h s) ^ 2 = 0 := by rw [hfq_sq]; ring
    rw [hbase]
    simp [hn1.ne']
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
          simp [hn1.ne']
        · have hq0 : f t + L t = 0 := le_antisymm (le_of_not_gt hq_not) hq_nonneg
          have hbase : f t ^ 2 - (L t) ^ 2 = 0 := by
            have hprod : (f t - L t) * (f t + L t) = 0 := by rw [hq0]; ring
            nlinarith [hprod]
          dsimp [W]
          rw [hbase]
          simp [hn1.ne']
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
    simpa [Set.uIcc_of_le hab] using hFG
  have hsuppG_ab : Function.support G ⊆ Set.Ioc a b := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : p ≤ t ∧ t ≤ q
    · have ht_gt : a < t := lt_of_lt_of_le ha_mem.1 htab.1
      have ht_le : t ≤ b := le_trans htab.2 (le_of_lt hb_mem.2)
      exact ⟨ht_gt, ht_le⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hsuppG_pq : Function.support G ⊆ Set.Ioc p q := by
    rw [Function.support_subset_iff]
    intro t ht
    by_cases htab : p ≤ t ∧ t ≤ q
    · have htp_ne : t ≠ p := by
        intro htp
        have hG0 : G t = 0 := by
          subst t
          simp [G, hW_p]
        exact (ht hG0).elim
      have htp_lt : p < t := lt_of_le_of_ne htab.1 (Ne.symm htp_ne)
      exact ⟨htp_lt, htab.2⟩
    · have hG0 : G t = 0 := by simp [G, htab]
      exact (ht hG0).elim
  have hI1 := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := a) (b := b) hsuppG_ab
  have hIpq := intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := G) (a := p) (b := q) hsuppG_pq
  have hpq : p < q := lt_trans hp_neg hq_pos
  have hG_pq_eq : (∫ t in p..q, G t) = ∫ t in p..q, W t * (t + C) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htab : p ≤ t ∧ t ≤ q := by
      rw [Set.uIcc_of_le hpq.le] at ht
      exact ht
    dsimp [G]
    rw [if_pos htab]
  have hJ' : (∫ t in p..q, W t * (t + C)) = 0 := by
    have hJ0 := hJ s hs
    simpa [p,q,W,L,C] using hJ0
  have hmain : (∫ t in a..b, F t) = 0 := by
    calc
      (∫ t in a..b, F t) = ∫ t in a..b, G t := hF_eq_G
      _ = ∫ t, G t := hI1
      _ = ∫ t in p..q, G t := hIpq.symm
      _ = ∫ t in p..q, W t * (t + C) := hG_pq_eq
      _ = 0 := hJ'
  simpa [F, L] using hmain

end Commons.Geometry.Ulam
