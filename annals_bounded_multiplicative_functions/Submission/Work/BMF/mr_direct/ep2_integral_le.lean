import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_sq_dvd_le
import Submission.Work.BMF.mr_direct.mv_natIcc_mean_value
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.dirPolyM_eq_mainA_add_ep2
import Submission.Work.BMF.mr_direct.ep2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-! ## Membership facts for `pSetE` -/

lemma mem_pSetE_fst {P Q X : ℝ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) :
    x.1 ∈ Work.BMF.mrDirect.primeSet P Q :=
  (Finset.mem_sigma.mp hx).1

lemma mem_pSetE_snd {P Q X : ℝ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) :
    x.2 ∈ Work.BMF.natIcc (X / x.1) (2 * X / x.1) :=
  (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1

lemma mem_pSetE_dvd {P Q X : ℝ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) : x.1 ∣ x.2 :=
  (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2

lemma pSetE_subset_buchSigma (P Q X : ℝ) :
    Work.BMF.mrDirect.pSetE P Q X ⊆ Work.BMF.mr_direct.buchSigma P Q X := by
  intro x hx
  rw [Work.BMF.mr_direct.buchSigma, Finset.mem_sigma]
  exact ⟨mem_pSetE_fst hx, mem_pSetE_snd hx⟩

lemma primeSet_bounds {P Q : ℝ} {p : ℕ} (hp : p ∈ Work.BMF.mrDirect.primeSet P Q) :
    p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
  rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
  have hQ0 : (0 : ℝ) ≤ Q := by
    have hne : ⌊Q⌋₊ ≠ 0 := by
      have : 1 ≤ p := hpr.one_le
      omega
    have hnot : ¬ (Q < 1) := fun h => hne ((Nat.floor_eq_zero (a := Q)).mpr h)
    linarith [not_lt.mp hnot]
  exact ⟨hpr, le_trans (Nat.le_ceil P) (by exact_mod_cast h1),
    le_trans (by exact_mod_cast h2) (Nat.floor_le hQ0)⟩

lemma one_le_snd {P Q X : ℝ} (hX : 1 ≤ X) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) : 1 ≤ x.2 := by
  obtain ⟨hpr, -, -⟩ := primeSet_bounds (mem_pSetE_fst hx)
  have hx1pos : (0 : ℝ) < (x.1 : ℝ) := by
    have : (2 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast hpr.two_le
    linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hmem := mem_pSetE_snd hx
  have hb := (Work.BMF.mrDirect.mem_natIcc
    (show (0 : ℝ) ≤ 2 * X / x.1 by positivity)).mp hmem
  have hpos : (0 : ℝ) < X / x.1 := by positivity
  have h2pos : (0 : ℝ) < (x.2 : ℝ) := lt_of_lt_of_le hpos hb.1
  have h2ne : x.2 ≠ 0 := by
    intro h; rw [h] at h2pos; simp at h2pos
  omega

lemma one_le_omegaCount_snd {P Q X : ℝ} (hX : 1 ≤ X) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) :
    1 ≤ Work.BMF.mrDirect.omegaCount P Q x.2 := by
  obtain ⟨hpr, hPx, hxQ⟩ := primeSet_bounds (mem_pSetE_fst hx)
  have hdvd : x.1 ∣ x.2 := mem_pSetE_dvd hx
  have h2 : 1 ≤ x.2 := one_le_snd hX hx
  have hmem : x.1 ∈ (Finset.Icc 1 x.2).filter
      (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ x.2) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpr.one_le, Nat.le_of_dvd (by omega) hdvd⟩, hpr, hPx, hxQ, hdvd⟩
  have hpos : 0 < ((Finset.Icc 1 x.2).filter
      (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ x.2)).card :=
    Finset.card_pos.mpr ⟨x.1, hmem⟩
  rw [Work.BMF.mrDirect.omegaCount]
  omega

lemma omegaCount_freq_eq {P Q X : ℝ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) :
    Work.BMF.mrDirect.omegaCount P Q (freq x) = Work.BMF.mrDirect.omegaCount P Q x.2 := by
  obtain ⟨hpr, hPx, hxQ⟩ := primeSet_bounds (mem_pSetE_fst hx)
  have hdvd : x.1 ∣ x.2 := mem_pSetE_dvd hx
  have h := Work.BMF.mr_direct.omegaCount_mul_prime (P := P) (Q := Q) (m := x.2) (p := x.1)
    hpr hPx hxQ
  simp only [freq]
  rw [h]
  simp [hdvd]

/-- Elementary numeric bound. -/
lemma inv_add_inv_succ_le (r : ℕ) (hr : 1 ≤ r) :
    ((r : ℝ))⁻¹ + (((r + 1 : ℕ)) : ℝ)⁻¹ ≤ 2 / (r : ℝ) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hs : (((r + 1 : ℕ)) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have hle : (((r + 1 : ℕ)) : ℝ)⁻¹ ≤ ((r : ℝ))⁻¹ := by
    rw [hs]
    exact (inv_le_inv₀ (by positivity) hrpos).mpr (by linarith)
  have h2 : (2 : ℝ) / (r : ℝ) = ((r : ℝ))⁻¹ + ((r : ℝ))⁻¹ := by
    rw [div_eq_mul_inv]; ring
  rw [h2]
  linarith

/-! ## The rewriting of `ep2` -/

lemma ep2_eq_sum_coef (a b c : ℕ → ℂ) (P Q X t : ℝ) :
    Work.BMF.mrDirect.ep2 a b c P Q X t
      = ∑ x ∈ Work.BMF.mrDirect.pSetE P Q X,
          coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [Work.BMF.mr_direct.ep2_sigma]
  rw [show (Work.BMF.mr_direct.buchSigma P Q X).filter (fun x => x.1 ∣ x.2)
        = Work.BMF.mrDirect.pSetE P Q X by
    rw [Work.BMF.mr_direct.buchSigma, Work.BMF.mrDirect.pSetE, Finset.filter_sigma']]
  apply Finset.sum_congr rfl
  intro x hx
  rw [coef, freq, Work.BMF.mr_direct.buchE]

/-! ## Coefficient bound -/

lemma coef_bound {P Q X : ℝ} (hX : 1 ≤ X) (a b c : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ Work.BMF.mrDirect.pSetE P Q X) :
    ‖coef a b c P Q x‖ ≤ 2 / (Work.BMF.mrDirect.omegaCount P Q (freq x) : ℝ) := by
  have hr1 : 1 ≤ Work.BMF.mrDirect.omegaCount P Q x.2 := one_le_omegaCount_snd hX hx
  have hfreq := omegaCount_freq_eq hx
  have hnorm1 : ‖(((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹‖
      = (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hnorm2 : ‖(((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖
      = (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have hmain : ‖coef a b c P Q x‖ ≤
      (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
        (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
    rw [coef]
    calc ‖a (x.2 * x.1) * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹ -
            b x.2 * c x.1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖
        ≤ ‖a (x.2 * x.1) * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ) : ℂ))⁻¹‖ +
            ‖b x.2 * c x.1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ) : ℂ))⁻¹‖ :=
          norm_sub_le _ _
      _ ≤ 1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
            1 * 1 * (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by
          apply add_le_add
          · rw [norm_mul, hnorm1]
            exact mul_le_mul_of_nonneg_right (ha _) (by positivity)
          · rw [norm_mul, norm_mul, hnorm2]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul (hb _) (hc _) (by positivity) (by norm_num)
      _ = (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
            (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := by ring
  calc ‖coef a b c P Q x‖
      ≤ (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ)⁻¹ +
          (((Work.BMF.mrDirect.omegaCount P Q x.2 + 1 : ℕ)) : ℝ)⁻¹ := hmain
    _ ≤ 2 / (((Work.BMF.mrDirect.omegaCount P Q x.2 : ℕ)) : ℝ) :=
        inv_add_inv_succ_le _ hr1
    _ = 2 / (Work.BMF.mrDirect.omegaCount P Q (freq x) : ℝ) := by rw [hfreq]

/-! ## Fibre cardinality bound -/

lemma ep2_fiber_card_le (P Q X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    ((Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n)).card
      ≤ Work.BMF.mrDirect.omegaCount P Q n := by
  by_cases hne : ((Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ Work.BMF.mrDirect.pSetE P Q X := (Finset.mem_filter.mp hx0).1
    have hf0 : freq x0 = n := (Finset.mem_filter.mp hx0).2
    have hn1 : 1 ≤ n := by
      have h2 : 1 ≤ x0.2 := one_le_snd hX hx0'
      have h1 : 1 ≤ x0.1 := (primeSet_bounds (mem_pSetE_fst hx0')).1.one_le
      have : 0 < x0.2 * x0.1 := Nat.mul_pos (by omega) (by omega)
      rw [← hf0, freq]
      omega
    have hmap : ∀ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n),
        x.1 ∈ (Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n) := by
      intro x hx
      rw [Finset.mem_filter]
      refine ⟨mem_pSetE_fst (Finset.mem_filter.mp hx).1, ?_⟩
      have hdvd : x.1 ∣ x.2 := mem_pSetE_dvd (Finset.mem_filter.mp hx).1
      have hfx : freq x = n := (Finset.mem_filter.mp hx).2
      have : x.1 ∣ x.2 * x.1 := dvd_mul_of_dvd_left hdvd x.1
      rwa [← hfx, freq]
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => x.1)
        ↑((Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n)) := by
      intro x hx y hy hxy
      change x.1 = y.1 at hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hy1 : 0 < y.1 := (primeSet_bounds (mem_pSetE_fst hy'.1)).1.pos
      have hfreq : x.2 * x.1 = y.2 * y.1 := by
        have : freq x = freq y := by rw [hx'.2, hy'.2]
        simpa only [freq] using this
      have hthis : x.2 = y.2 := by
        rw [hxy] at hfreq
        exact Nat.mul_right_cancel hy1 hfreq
      exact Sigma.ext hxy (heq_of_eq hthis)
    have hcard := Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ => x.1) hmap hinj
    rw [Work.BMF.mr_direct.card_primeSet_filter_dvd hn1] at hcard
    exact hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

/-! ## The merged sum -/

lemma ep2_eq_dd_sum (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 1 ≤ X) (t : ℝ) :
    Work.BMF.mrDirect.ep2 a b c P Q X t
      = ∑ n ∈ Work.BMF.natIcc X (2 * X),
          dd a b c P Q X n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [ep2_eq_sum_coef]
  have hfib : (∑ n ∈ (Work.BMF.mrDirect.pSetE P Q X).image freq,
        dd a b c P Q X n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ x ∈ Work.BMF.mrDirect.pSetE P Q X,
          coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Work.BMF.mrDirect.pSetE P Q X)
      (t := (Work.BMF.mrDirect.pSetE P Q X).image freq)
      (g := freq) (fun x hx => Finset.mem_image_of_mem freq hx)
      (fun x => coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [dd, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [← hfib]
  have himg_sub : (Work.BMF.mrDirect.pSetE P Q X).image freq ⊆ Work.BMF.natIcc X (2 * X) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have hmem : x.2 * x.1 ∈ Work.BMF.natIcc X (2 * X) :=
      Work.BMF.mr_direct.phi_mem (by linarith : 0 < X) (pSetE_subset_buchSigma P Q X hx)
    simpa [freq] using hmem
  apply Finset.sum_subset himg_sub
  intro n hn hnimg
  have hz : dd a b c P Q X n = 0 := by
    rw [dd]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exact absurd (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩) hnimg
  rw [hz, zero_mul]

/-! ## Bound on the merged coefficient -/

lemma dd_bound {P Q X : ℝ} (hX : 1 ≤ X) (a b c : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖dd a b c P Q X n‖ ≤ 2 := by
  by_cases hne : ((Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n)).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ Work.BMF.mrDirect.pSetE P Q X := (Finset.mem_filter.mp hx0).1
    have hf0 : freq x0 = n := (Finset.mem_filter.mp hx0).2
    have hr1 : 1 ≤ Work.BMF.mrDirect.omegaCount P Q n := by
      rw [← hf0, omegaCount_freq_eq hx0']
      exact one_le_omegaCount_snd hX hx0'
    have hterm : ∀ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n),
        ‖coef a b c P Q x‖ ≤ 2 / (Work.BMF.mrDirect.omegaCount P Q n : ℝ) := by
      intro x hx
      have hx' : x ∈ Work.BMF.mrDirect.pSetE P Q X := (Finset.mem_filter.mp hx).1
      have hfx : freq x = n := (Finset.mem_filter.mp hx).2
      have h := coef_bound hX a b c ha hb hc hx'
      rwa [hfx] at h
    calc ‖dd a b c P Q X n‖
        = ‖∑ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n),
            coef a b c P Q x‖ := rfl
      _ ≤ ∑ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n),
            ‖coef a b c P Q x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ (Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n),
            2 / (Work.BMF.mrDirect.omegaCount P Q n : ℝ) := Finset.sum_le_sum hterm
      _ = (((Work.BMF.mrDirect.pSetE P Q X).filter (fun x => freq x = n)).card : ℝ) *
            (2 / (Work.BMF.mrDirect.omegaCount P Q n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Work.BMF.mrDirect.omegaCount P Q n : ℝ) *
            (2 / (Work.BMF.mrDirect.omegaCount P Q n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast ep2_fiber_card_le P Q X hX n
      _ = 2 := by
          have h0 : (Work.BMF.mrDirect.omegaCount P Q n : ℝ) ≠ 0 := by
            have : (0:ℕ) < Work.BMF.mrDirect.omegaCount P Q n := by omega
            exact_mod_cast (ne_of_gt this)
          field_simp
  · rw [dd, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]
    norm_num

/-! ## Support count -/

lemma ep2_support_card_le (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 1 ≤ X) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) :
    ((Work.BMF.natIcc X (2 * X)).filter
        (fun n => dd a b c P Q X n ≠ 0)).card ≤ 4 * X / P := by
  have hsub : ((Work.BMF.natIcc X (2 * X)).filter (fun n => dd a b c P Q X n ≠ 0))
      ⊆ (Work.BMF.natIcc X (2 * X)).filter
          (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p * p ∣ n) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnB, hdne⟩ := hn
    refine ⟨hnB, ?_⟩
    by_contra hcon
    exact hdne (by
      rw [dd]
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxE, hxn⟩ := hx
      have hdvd : x.1 ∣ x.2 := mem_pSetE_dvd hxE
      have hp : x.1 ∈ Work.BMF.mrDirect.primeSet P Q := mem_pSetE_fst hxE
      have hsq : x.1 * x.1 ∣ n := by
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k, ?_⟩
        rw [← hxn, freq, hk]; ring
      exact (hcon ⟨x.1, hp, hsq⟩).elim)
  have h1 : (((Work.BMF.natIcc X (2 * X)).filter
        (fun n => dd a b c P Q X n ≠ 0)).card : ℝ)
      ≤ (((Work.BMF.natIcc X (2 * X)).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p * p ∣ n)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans h1 (Work.BMF.mr_direct.card_sq_dvd_le X P Q hX hP hPQ)

/-! ## The final sum bound -/

lemma dd_sum_bound (a b c : ℕ → ℂ) (P Q X : ℝ) (hX : 1 ≤ X) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) :
    (∑ n ∈ Work.BMF.natIcc X (2 * X),
        ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2) ≤ 16 / (P * X) := by
  have hXpos : 0 < X := by linarith
  set A := (Work.BMF.natIcc X (2 * X)).filter (fun n => dd a b c P Q X n ≠ 0) with hA
  have hA_sub : A ⊆ Work.BMF.natIcc X (2 * X) := Finset.filter_subset _ _
  have hsum_eq : (∑ n ∈ Work.BMF.natIcc X (2 * X), ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2)
      = ∑ n ∈ A, ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2 := by
    symm
    apply Finset.sum_subset hA_sub
    intro n hn hnA
    have hz : dd a b c P Q X n = 0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn, h⟩)
    rw [hz]
    simp
  rw [hsum_eq]
  have hterm : ∀ n ∈ A, ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 4 / X ^ 2 := by
    intro n hn
    have hn' : n ∈ Work.BMF.natIcc X (2 * X) := (Finset.mem_filter.mp hn).1
    have hbnd := Work.BMF.mr_direct.natIcc_bounds_gen (by linarith : (0:ℝ) < 2 * X) hn'
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hXpos hbnd.1
    have hd : ‖dd a b c P Q X n‖ ^ 2 ≤ 4 := by
      have h1 := dd_bound (P := P) (Q := Q) hX a b c ha hb hc n
      nlinarith [norm_nonneg (dd a b c P Q X n)]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2) (by positivity : (0:ℝ) < X^2)]
    have hn2 : X ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [hXpos, hbnd.1]
    nlinarith [hd, hn2, hXpos, norm_nonneg (dd a b c P Q X n)]
  calc (∑ n ∈ A, ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ ∑ n ∈ A, 4 / X ^ 2 := Finset.sum_le_sum hterm
    _ = (A.card : ℝ) * (4 / X ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * X / P) * (4 / X ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h := ep2_support_card_le a b c P Q X hX hP hPQ
        rwa [← hA] at h
    _ = 16 / (P * X) := by
        have hP0 : P ≠ 0 := by linarith
        have hX0 : X ≠ 0 := by linarith
        field_simp
        ring

/-! ## The main theorem -/

-- Mean-square bound for the `p²`-correction term `ep2`.
theorem ep2_integral_le (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2)
    (a b c : ℕ → ℂ) (P Q X S : ℝ) (hX : 1 ≤ X) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖Work.BMF.mrDirect.ep2 a b c P Q X t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (2 * X)) * (16 / (P * X)) := by
  have hXpos : 0 < X := by linarith
  have hX2X : X ≤ 2 * X := by linarith
  have hC0 : 0 ≤ C₀ := Work.BMF.mr_direct.c0_nonneg_of_mv C₀ hC₀
  have hpoint : ∀ t : ℝ, ‖Work.BMF.mrDirect.ep2 a b c P Q X t‖ ^ 2
      = ‖∑ n ∈ Work.BMF.natIcc X (2 * X),
          dd a b c P Q X n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 :=
    fun t => by rw [ep2_eq_dd_sum a b c P Q X hX t]
  have hint : (∫ t in (-S)..S, ‖Work.BMF.mrDirect.ep2 a b c P Q X t‖ ^ 2)
      = ∫ t in (-S)..S, ‖∑ n ∈ Work.BMF.natIcc X (2 * X),
          dd a b c P Q X n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  have hmv := Work.BMF.mr_direct.mv_natIcc_mean_value C₀ hC₀ (dd a b c P Q X) X (2 * X) S
    hXpos hX2X hS
  have hsum := dd_sum_bound a b c P Q X hX hP hPQ ha hb hc
  rw [hint]
  calc (∫ t in (-S)..S, ‖∑ n ∈ Work.BMF.natIcc X (2 * X),
          dd a b c P Q X n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (2 * X)) * ∑ n ∈ Work.BMF.natIcc X (2 * X),
          ‖dd a b c P Q X n‖ ^ 2 / (n : ℝ) ^ 2 := hmv
    _ ≤ (2 * S + 3 * C₀ * (2 * X)) * (16 / (P * X)) := by
        apply mul_le_mul_of_nonneg_left hsum
        have hmul : (0 : ℝ) ≤ C₀ * X := mul_nonneg hC0 hXpos.le
        nlinarith [hS, hmul]

end

end Work.BMF.mr_direct
