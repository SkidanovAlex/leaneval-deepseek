import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.ep2_defs
import Submission.Work.BMF.mr_direct.ep2_integral_le
import Submission.Work.BMF.mr_direct.card_sq_dvd_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the range mean-square bound on the `p²`-correction term `ep2R`

`Work.BMF.mrDirect.ep2R a b c P Q A B` is the double sum over pairs `⟨p, m⟩` with
`p` a prime in `[P,Q]`, `m ∈ [A/p, B/p]` and `p ∣ m`.  This file records the range analogue
of `Work.BMF.mrDirect.pSetE` / `dd` (`Submission/Work/BMF/mr_direct/ep2_defs.lean`):
`pSetER P Q A B` is the pair index set and `ddR` is the merged coefficient over the fibre of
the frequency `freq ⟨p,m⟩ = m·p`.

The main outputs used by `ep2R_integral_le` are `ep2R_eq_ddR_sum` (identifying `ep2R` with a
Dirichlet polynomial over `natIcc A B`) and the analytic bounds on `ddR`
(`ep2R_sum_bound`, in `Submission/Work/BMF/mr_direct/ep2R_sum_bound.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

noncomputable section

/-- Index set of the range `p²`-correction term `ep2R`, as a `sigma`-type of pairs `(p,m)`. -/
def pSetER (P Q A B : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Work.BMF.mrDirect.primeSet P Q).sigma
    (fun p => (Work.BMF.natIcc (A / p) (B / p)).filter (fun m : ℕ => p ∣ m))

/-- The merged coefficient of `ep2R` over the fibre of `freq`: the total coefficient of
`n^{-(1+it)}` in `ep2R`. -/
def ddR (a b c : ℕ → ℂ) (P Q A B : ℝ) (n : ℕ) : ℂ :=
  ∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), coef a b c P Q x

/-! ### Membership facts -/

lemma mem_pSetER_fst {P Q A B : ℝ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ pSetER P Q A B) :
    x.1 ∈ Work.BMF.mrDirect.primeSet P Q :=
  (Finset.mem_sigma.mp hx).1

lemma mem_pSetER_snd {P Q A B : ℝ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ pSetER P Q A B) :
    x.2 ∈ Work.BMF.natIcc (A / x.1) (B / x.1) :=
  (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1

lemma mem_pSetER_dvd {P Q A B : ℝ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ pSetER P Q A B) :
    x.1 ∣ x.2 :=
  (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2

lemma one_le_sndR {P Q A B : ℝ} (hA : 1 ≤ A) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ pSetER P Q A B) : 1 ≤ x.2 := by
  obtain ⟨hpr, -, -⟩ := Work.BMF.mr_direct.primeSet_bounds (mem_pSetER_fst hx)
  have hx1pos : (0 : ℝ) < (x.1 : ℝ) := by
    have : (2 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast hpr.two_le
    linarith
  have hmem : x.2 ∈ Work.BMF.natIcc (A / x.1) (B / x.1) := mem_pSetER_snd hx
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hmem
  have hceil : A / x.1 ≤ (x.2 : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmem.1)
  have hpos : (0 : ℝ) < A / x.1 := div_pos (by linarith) hx1pos
  have h2 : (0 : ℝ) < (x.2 : ℝ) := lt_of_lt_of_le hpos hceil
  have h2' : 0 < x.2 := by exact_mod_cast h2
  omega

lemma one_le_omegaCount_sndR {P Q A B : ℝ} (hA : 1 ≤ A) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ pSetER P Q A B) : 1 ≤ Work.BMF.mrDirect.omegaCount P Q x.2 := by
  obtain ⟨hpr, hPx, hxQ⟩ := Work.BMF.mr_direct.primeSet_bounds (mem_pSetER_fst hx)
  have hdvd : x.1 ∣ x.2 := mem_pSetER_dvd hx
  have h2 : 1 ≤ x.2 := one_le_sndR hA hx
  have hmem : x.1 ∈ (Finset.Icc 1 x.2).filter
      (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ x.2) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpr.one_le, Nat.le_of_dvd (by omega) hdvd⟩, hpr, hPx, hxQ, hdvd⟩
  have hpos : 0 < ((Finset.Icc 1 x.2).filter
      (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ x.2)).card :=
    Finset.card_pos.mpr ⟨x.1, hmem⟩
  rw [Work.BMF.mrDirect.omegaCount]
  omega

/-- `ω(m·p;P,Q) = ω(m;P,Q)` when `p` is a prime of `[P,Q]` dividing `m`. -/
lemma omegaCount_freq_eqR {P Q A B : ℝ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ pSetER P Q A B) :
    Work.BMF.mrDirect.omegaCount P Q (freq x) = Work.BMF.mrDirect.omegaCount P Q x.2 := by
  obtain ⟨hpr, hPx, hxQ⟩ := Work.BMF.mr_direct.primeSet_bounds (mem_pSetER_fst hx)
  have hdvd : x.1 ∣ x.2 := mem_pSetER_dvd hx
  have h := Work.BMF.mr_direct.omegaCount_mul_prime (P := P) (Q := Q) (m := x.2) (p := x.1)
    hpr hPx hxQ
  simp only [freq]
  rw [h]
  simp [hdvd]

/-- The frequency map sends `pSetER P Q A B` into `[A,B]`. -/
lemma phi_memR {P Q A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ pSetER P Q A B) : (x.2 * x.1 : ℕ) ∈ Work.BMF.natIcc A B := by
  obtain ⟨hpr, -, -⟩ := Work.BMF.mr_direct.primeSet_bounds (mem_pSetER_fst hx)
  have hp2 : (2 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast hpr.two_le
  have hp0 : (0 : ℝ) < (x.1 : ℝ) := by linarith
  rw [Work.BMF.mrDirect.mem_natIcc (by linarith : (0 : ℝ) ≤ B)]
  obtain ⟨hm1, hm2⟩ := (Work.BMF.mrDirect.mem_natIcc
    (show (0 : ℝ) ≤ B / x.1 from le_of_lt (div_pos (by linarith) hp0))).mp (mem_pSetER_snd hx)
  constructor
  · have h : (x.1 : ℝ) * (A / x.1) ≤ (x.1 : ℝ) * (x.2 : ℝ) :=
      mul_le_mul_of_nonneg_left hm1 hp0.le
    rw [show (x.1 : ℝ) * (A / x.1) = A by field_simp] at h
    calc A ≤ (x.1 : ℝ) * (x.2 : ℝ) := h
      _ = ((x.2 * x.1 : ℕ) : ℝ) := by push_cast; ring
  · have h : (x.2 : ℝ) * (x.1 : ℝ) ≤ (B / x.1) * (x.1 : ℝ) :=
      mul_le_mul_of_nonneg_right hm2 hp0.le
    rw [show (B / x.1) * (x.1 : ℝ) = B by field_simp] at h
    calc ((x.2 * x.1 : ℕ) : ℝ) = (x.2 : ℝ) * (x.1 : ℝ) := by push_cast; ring
      _ ≤ B := h

/-! ### The rewriting of `ep2R` -/

lemma ep2R_eq_sum_coef (a b c : ℕ → ℂ) (P Q A B t : ℝ) :
    Work.BMF.mrDirect.ep2R a b c P Q A B t
      = ∑ x ∈ pSetER P Q A B,
          coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [Work.BMF.mrDirect.ep2R, pSetER, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [coef, freq]

/-! ### The merged polynomial -/

lemma ep2R_eq_ddR_sum (a b c : ℕ → ℂ) (P Q A B : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (t : ℝ) :
    Work.BMF.mrDirect.ep2R a b c P Q A B t
      = ∑ n ∈ Work.BMF.natIcc A B,
          ddR a b c P Q A B n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  rw [ep2R_eq_sum_coef]
  have hfib : (∑ n ∈ (pSetER P Q A B).image freq,
        ddR a b c P Q A B n * ((n : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ x ∈ pSetER P Q A B,
          coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := pSetER P Q A B)
      (t := (pSetER P Q A B).image freq)
      (g := freq) (fun x hx => Finset.mem_image_of_mem freq hx)
      (fun x => coef a b c P Q x * ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ddR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [← hfib]
  have himg_sub : (pSetER P Q A B).image freq ⊆ Work.BMF.natIcc A B := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    simpa only [freq] using phi_memR (by linarith : (0:ℝ) < A) hAB hx
  apply Finset.sum_subset himg_sub
  intro n hn hnimg
  have hz : ddR a b c P Q A B n = 0 := by
    rw [ddR]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exact absurd (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩) hnimg
  rw [hz, zero_mul]

end

end Work.BMF.mr_direct
