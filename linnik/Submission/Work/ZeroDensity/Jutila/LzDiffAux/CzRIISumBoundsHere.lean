import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ExpSumNegSqrtSqBoundHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzSigDecayFinal
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzSigSqSumFinal
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzSigSumLeFinal

/-!
# The Region-II sum bounds of the two-sided `S₃` boundary term

This file proves `Work.ZeroDensity.Jutila.LzDiffAux.CzRIISumBoundsHere`: the four elementary
sum bounds consumed by `czRII_bound`.  The analytic content is split as follows.

* `czHarmDecay_aux` — the harmonic sum against the de la Vallée Poussin envelope is bounded;
  proved by a dyadic reduction to `czHarmDecay_sample`, which is in turn reduced to
  `ExpSumNegSqrtSqBound`.
* `CzSigDecayFinal`, `CzSigSqSumFinal`, `CzSigSumLeFinal` — the `σ_{-1/2}`-weighted bounds,
  proved in companion files.
* `czRII_assembly` — the elementary assembly of the four claims from these inputs.
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

lemma Dc_eq_czEps (c : ℝ) (n : ℕ) : Dc c n = czEps c (n:ℝ) := rfl
lemma czEps_pos' (c x : ℝ) : 0 < czEps c x := Real.exp_pos _
lemma czEps_nonneg' (c x : ℝ) : 0 ≤ czEps c x := (Real.exp_pos _).le

lemma czEps_eq_one_of_mem {c x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : czEps c x = 1 := by
  have hlog : Real.log x ≤ 0 := by
    by_cases hx0 : 0 ≤ x
    · exact Real.log_nonpos hx0 h2
    · push Not at hx0
      have hneg : Real.log x = Real.log (-x) := by simpa using Real.log_neg_eq_log (-x)
      rw [hneg]
      exact Real.log_nonpos (by linarith) (by linarith)
  unfold czEps
  rw [Real.sqrt_eq_zero_of_nonpos hlog]
  simp

lemma czEps_mono' {c x z : ℝ} (hc : 0 ≤ c) (hxz : x ≤ z) (hx : -1 ≤ x) :
    czEps c z ≤ czEps c x := by
  by_cases hx1 : x ≤ 1
  · rw [czEps_eq_one_of_mem hx hx1]; exact czEps_le_one hc
  · push Not at hx1
    exact czEps_antitone (c:=c) (x:=x) (z:=z) hc (by linarith) hxz

lemma czEps_half_shift {c z : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) :
    czEps c (z - 1) ≤ czEps c (z / 2) := by
  by_cases h : 2 ≤ z
  · exact czEps_mono' hc (by linarith) (by linarith)
  · push Not at h
    rw [czEps_eq_one_of_mem (c:=c) (x:=z-1) (by linarith) (by linarith),
        czEps_eq_one_of_mem (c:=c) (x:=z/2) (by linarith) (by linarith)]

lemma cz_r_lt_y' {w y : ℝ} (hw : 0 < w) (hy : 0 < y) {N q r : ℕ}
    (hNwy : (N:ℝ) < w*y) (hrR : r ≤ czR w N q) (hr1 : 1 ≤ r) : (r:ℝ) < y := by
  have hq : 1 ≤ q := by
    by_contra h
    push Not at h
    have hq0 : q = 0 := by omega
    subst hq0
    simp [czR] at hrR
    omega
  exact cz_r_lt_y hw hy hNwy hq hrR

lemma sqrt_sub_sqrt_le {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    Real.sqrt u - Real.sqrt v ≤ Real.sqrt (u - v) := by
  have h1 : Real.sqrt v ≤ Real.sqrt u := Real.sqrt_le_sqrt hvu
  have h2 : 0 ≤ Real.sqrt u - Real.sqrt v := sub_nonneg.mpr h1
  have h3 : (Real.sqrt u - Real.sqrt v)^2 ≤ u - v := by
    have hu := Real.sq_sqrt (le_trans hv hvu); have hvv := Real.sq_sqrt hv
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]
  calc Real.sqrt u - Real.sqrt v = Real.sqrt ((Real.sqrt u - Real.sqrt v)^2) := (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt (u - v) := Real.sqrt_le_sqrt h3

lemma czEps_quarter_shift {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T) :
    czEps c ((T-1)/4) ≤ Real.exp (2*c) * czEps c T := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt5 : Real.sqrt (Real.log 5) ≤ 2 := by
    rw [← hsqrt4]; apply Real.sqrt_le_sqrt
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 5) (by norm_num : (5:ℝ) ≠ 1)
    linarith
  have hcz5 : czEps c 5 = Real.exp (-(c * Real.sqrt (Real.log 5))) := rfl
  have hexp : Real.exp (-(2*c)) ≤ czEps c 5 := by
    rw [hcz5]; apply Real.exp_le_exp.mpr; nlinarith [hsqrt5, hc]
  by_cases h5 : T ≤ 5
  · have h1 : czEps c ((T-1)/4) = 1 := czEps_eq_one_of_mem (by linarith) (by linarith)
    have hle5 : czEps c 5 ≤ czEps c T := czEps_mono' hc (by linarith) (by linarith)
    rw [h1]
    have hone : (1:ℝ) = Real.exp (2*c) * Real.exp (-(2*c)) := by
      rw [← Real.exp_add, show 2*c + -(2*c) = 0 by ring, Real.exp_zero]
    rw [hone]
    exact mul_le_mul_of_nonneg_left (le_trans hexp hle5) (Real.exp_nonneg _)
  · push Not at h5
    have hpos : (0:ℝ) < (T-1)/4 := by linarith
    have hge1 : 1 ≤ (T-1)/4 := by linarith
    have hleT : (T-1)/4 ≤ T := by linarith
    have hlogT : Real.log ((T-1)/4) ≤ Real.log T := Real.log_le_log hpos hleT
    have hsub : Real.sqrt (Real.log T) - Real.sqrt (Real.log ((T-1)/4))
        ≤ Real.sqrt (Real.log T - Real.log ((T-1)/4)) :=
      sqrt_sub_sqrt_le (Real.log_nonneg hge1) hlogT
    have hdiff : Real.log T - Real.log ((T-1)/4) = Real.log (4*T/(T-1)) := by
      rw [← Real.log_div (by linarith : T ≠ 0) (by linarith : (T-1)/4 ≠ 0)]
      congr 1
      field_simp
    have hle5b : 4*T/(T-1) ≤ 5 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < T-1)]; linarith
    have hlog5 : Real.log (4*T/(T-1)) ≤ Real.log 5 :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) hle5b
    have h2 : Real.sqrt (Real.log T) - Real.sqrt (Real.log ((T-1)/4)) ≤ 2 := by
      refine le_trans hsub ?_
      rw [hdiff]
      exact le_trans (Real.sqrt_le_sqrt hlog5) hsqrt5
    have hkey : czEps c ((T-1)/4)
        = Real.exp (c * (Real.sqrt (Real.log T) - Real.sqrt (Real.log ((T-1)/4)))) * czEps c T := by
      unfold czEps
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hkey]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [hc, h2]

lemma czEps_wR_le {c w y : ℝ} (hc : 0 ≤ c) (hw : 0 < w) (hy : 0 < y) (hwy : w ≤ y)
    {N q : ℕ} (hNwy : (N:ℝ) < w*y) (hq : 1 ≤ q) :
    czEps c (w * (czR w N q : ℝ) / (4*y)) ≤ Real.exp (2*c) * Dc c (czT y N q) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hRgt : (N:ℝ)/((q:ℝ)*w) - 1 < (czR w N q : ℝ) := by
    have h := Nat.lt_floor_add_one ((N:ℝ)/((q:ℝ)*w))
    simp only [czR]
    linarith [h]
  have hTle : ((czT y N q : ℕ):ℝ) ≤ (N:ℝ)/((q:ℝ)*y) := by
    simp only [czT]; exact Nat.floor_le (by positivity)
  have hwr : w/y * ((N:ℝ)/((q:ℝ)*w)) = (N:ℝ)/((q:ℝ)*y) := by
    field_simp
  have hwyle1 : w/y ≤ 1 := by rw [div_le_one hy]; linarith
  have hmain1 : ((czT y N q : ℕ):ℝ) - 1 ≤ (N:ℝ)/((q:ℝ)*y) - w/y := by linarith [hTle, hwyle1]
  have hmain2 : (N:ℝ)/((q:ℝ)*y) - w/y < w*(czR w N q : ℝ)/y := by
    have hm := mul_lt_mul_of_pos_left hRgt (by positivity : 0 < w/y)
    rw [mul_sub, hwr, mul_one, div_mul_eq_mul_div] at hm
    linarith [hm]
  have hT1 : ((czT y N q : ℕ):ℝ) - 1 < w*(czR w N q : ℝ)/y := lt_of_le_of_lt hmain1 hmain2
  have hTnn : (0:ℝ) ≤ ((czT y N q : ℕ):ℝ) := by positivity
  have hdiv : (((czT y N q : ℕ):ℝ) - 1)/4 ≤ w*(czR w N q : ℝ)/(4*y) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*y)]
    have h := (lt_div_iff₀ hy).mp hT1
    nlinarith [h]
  have hstep : czEps c (w * (czR w N q : ℝ) / (4*y))
      ≤ czEps c ((((czT y N q : ℕ):ℝ) - 1)/4) :=
    czEps_mono' hc hdiv (by linarith : -1 ≤ (((czT y N q : ℕ):ℝ) - 1)/4)
  have hfin := czEps_quarter_shift (c:=c) (T:=((czT y N q : ℕ):ℝ)) hc hTnn
  have hDc : Dc c (czT y N q) = czEps c ((czT y N q : ℕ):ℝ) := rfl
  rw [hDc]
  linarith [hstep, hfin]

lemma czTmax_le_czT (w y : ℝ) (N q r : ℕ) :
    czTmax w y N q r ≤ czT y N q := min_le_left _ _

lemma czTmax_le_mul {w y : ℝ} (hw : 0 < w) (hy : 0 < y) {N q r : ℕ} (hr : 1 ≤ r) :
    ((czTmax w y N q r : ℕ) : ℝ) ≤ w * (r:ℝ) / y := by
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  unfold czTmax
  have h1 : ((min (czT y N q) ⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℕ) : ℝ)
      ≤ (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℝ) := by
    exact_mod_cast min_le_right _ _
  have ha1 : y / (r:ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hred : y ≤ (r:ℝ) * (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) := by
    have := (div_lt_iff₀ hrR).mp ha1; linarith
  have hmain : w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) ≤ w * (r:ℝ) / y := by
    rw [le_div_iff₀ hy, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)]
    nlinarith [hw, hred]
  exact le_trans h1 (le_trans (Nat.floor_le (by positivity)) hmain)

lemma czTmax_ge_floor {w y : ℝ} (hw : 0 < w) (hy : 0 < y) {r : ℕ} (hr : 1 ≤ r)
    (hry : (r:ℝ) ≤ y) :
    w * (r:ℝ) / (2*y) - 1 ≤ (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℝ) := by
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  set a : ℕ := ⌊y / (r:ℝ)⌋₊ with ha
  have haR : (a:ℝ) ≤ y / (r:ℝ) := Nat.floor_le (by positivity)
  have hrle2 : (r:ℝ) * ((a:ℝ) + 1) ≤ 2 * y := by
    have h1 : (a:ℝ) + 1 ≤ y / (r:ℝ) + 1 := by linarith
    have h2 : y / (r:ℝ) + 1 ≤ 2 * y / (r:ℝ) := by
      have h3 : y / (r:ℝ) + 1 = (y + (r:ℝ)) / (r:ℝ) := by field_simp
      rw [h3]
      exact div_le_div_of_nonneg_right (by linarith) hrR.le
    have hh : (a:ℝ) + 1 ≤ 2 * y / (r:ℝ) := le_trans h1 h2
    have := (le_div_iff₀ hrR).mp hh
    nlinarith [this]
  have hkey : w * (r:ℝ) / (2*y) ≤ w / ((a:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (a:ℝ)+1), div_mul_eq_mul_div,
        div_le_iff₀ (by positivity : (0:ℝ) < 2*y)]
    nlinarith [hw, hrle2]
  have hfl : w / ((a:ℝ) + 1) - 1 ≤ (⌊w / ((a:ℝ) + 1)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (w / ((a:ℝ) + 1)); linarith
  have heq : ((⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℕ) : ℝ)
      = (⌊w / ((a:ℝ) + 1)⌋₊ : ℝ) := by rw [ha]
  rw [heq]
  linarith

lemma czTmax_mono {w y : ℝ} (hw : 0 < w) (hy : 0 < y) {N q r s : ℕ} (hr : 1 ≤ r)
    (hrs : r ≤ s) : czTmax w y N q r ≤ czTmax w y N q s := by
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hle : y / (s:ℝ) ≤ y / (r:ℝ) := div_le_div_of_nonneg_left hy.le hrR (by exact_mod_cast hrs)
  have hfl : (⌊y / (s:ℝ)⌋₊ : ℝ) ≤ (⌊y / (r:ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.floor_mono hle
  unfold czTmax
  apply min_le_min_left
  apply Nat.floor_mono
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((⌊y / (s:ℝ)⌋₊ : ℕ) : ℝ) + 1), div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0:ℝ) < ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) + 1)]
  nlinarith [hw, hfl]

lemma czEps_czTmax_le {c w y : ℝ} (hc : 0 ≤ c) (hw : 0 < w) (hy : 0 < y)
    {N q r : ℕ} (hr : 1 ≤ r) (hry : (r:ℝ) ≤ y) :
    czEps c (czTmax w y N q r : ℝ)
      ≤ czEps c (czT y N q : ℝ) + czEps c (w * (r:ℝ) / (2*y) - 1) := by
  set x : ℝ := w * (r:ℝ) / (2*y) - 1 with hx
  have hx1 : -1 ≤ x := by
    rw [hx]
    have h : 0 ≤ w * (r:ℝ) / (2*y) := by positivity
    linarith
  have hb : x ≤ (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℝ) := by
    rw [hx]; exact czTmax_ge_floor hw hy hr hry
  rcases min_cases (czT y N q) (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊) with ⟨hm, _⟩ | ⟨hm, _⟩
  · have hcz : czTmax w y N q r = czT y N q := by unfold czTmax; rw [hm]
    rw [hcz]
    linarith [czEps_nonneg' c (czT y N q : ℝ), czEps_nonneg' c x]
  · have hcz : (czTmax w y N q r : ℝ)
        = (⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ : ℝ) := by unfold czTmax; rw [hm]
    rw [hcz]
    have h := czEps_mono' hc hb hx1
    linarith [czEps_nonneg' c (czT y N q : ℝ), czEps_nonneg' c x]



/-! ## The harmonic decay of the de la Vallée Poussin envelope -/

/-- Dyadic reduction: the harmonic sum against the envelope is dominated by the dyadic samples. -/
lemma czHarmDecay_dyadic {c A : ℝ} (hc : 0 ≤ c) (hA : 0 < A) (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * czEps c (A/(q:ℝ)))
      ≤ ∑ k ∈ Finset.range (Nat.log 2 Q + 1), czEps c (A/(2:ℝ)^(k+1)) := by
  have hmap : ∀ q ∈ Finset.Icc 1 Q, Nat.log 2 q ∈ Finset.range (Nat.log 2 Q + 1) := by
    intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Icc.mp hq).2)
  have hfib := Finset.sum_fiberwise_of_maps_to hmap
    (f := fun q : ℕ => (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
  rw [← hfib]
  apply Finset.sum_le_sum
  intro k hk
  set Ek := czEps c (A / (2:ℝ)^(k+1)) with hEk
  have hterm : ∀ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k),
      (1 / (q : ℝ)) * czEps c (A / (q : ℝ)) ≤ (1 / (2:ℝ)^k) * Ek := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqI, hqk⟩ := hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
    have hqne : q ≠ 0 := by omega
    have hq2k : 2 ^ k ≤ q := by rw [← hqk]; exact Nat.pow_log_le_self 2 hqne
    have hqlt : q < 2 ^ (k+1) := by
      rw [← hqk]; exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) q
    have h2kpos : (0:ℝ) < (2:ℝ)^k := by positivity
    have hqp : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hinv : 1 / (q:ℝ) ≤ 1 / (2:ℝ)^k := by
      apply one_div_le_one_div_of_le h2kpos
      exact_mod_cast hq2k
    have hle : A / (2:ℝ)^(k+1) ≤ A / (q:ℝ) := by
      apply div_le_div_of_nonneg_left hA.le hqp
      exact_mod_cast le_of_lt hqlt
    have hf : czEps c (A / (q : ℝ)) ≤ czEps c (A / (2:ℝ)^(k+1)) :=
      czEps_antitone hc (by positivity) hle
    exact mul_le_mul hinv hf (czEps_nonneg' c _) (by positivity)
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k),
          (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k), (1 / (2:ℝ)^k) * Ek :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k)).card : ℝ) * ((1 / (2:ℝ)^k) * Ek) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2:ℝ)^k) * ((1 / (2:ℝ)^k) * Ek) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (by rw [hEk]; exact czEps_nonneg' c _))
        have hsub : (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k)
            ⊆ Finset.Icc (2^k) (2^(k+1)-1) := by
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨hqI, hqk⟩ := hq
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
          have hqne : q ≠ 0 := by omega
          refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
          · rw [← hqk]; exact Nat.pow_log_le_self 2 hqne
          · have hqlt : q < 2^(k+1) := by
              rw [← hqk]; exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) q
            have hpos : 1 ≤ 2^(k+1) := Nat.one_le_two_pow
            omega
        have hcard : ((Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = k)).card ≤ 2^k := by
          have hc' := Finset.card_le_card hsub
          rw [Nat.card_Icc] at hc'
          have h1 : 1 ≤ 2 ^ (k+1) := Nat.one_le_two_pow
          rw [Nat.sub_add_cancel h1] at hc'
          have h2 : 2 ^ (k+1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
          omega
        exact_mod_cast hcard
    _ = Ek := by
        have hne : (2:ℝ)^k ≠ 0 := by positivity
        rw [← mul_assoc, mul_one_div, div_self hne, one_mul]

/-- The dyadic samples are bounded uniformly in `A ≥ 1` and `Q ≤ 2A`. -/
lemma czHarmDecay_sample {c A : ℝ} (hc : 0 < c) (hA : 1 ≤ A) (Q : ℕ)
    (hQ : (Q:ℝ) ≤ 2*A) :
    (∑ k ∈ Finset.range (Nat.log 2 Q + 1), czEps c (A/(2:ℝ)^(k+1)))
      ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) := by
  set K := Nat.log 2 Q with hK
  have hKle : (2:ℝ)^(K+1) ≤ 4*A := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ1
    · subst hQ0
      rw [show K = 0 by rw [hK]; simp, pow_one]
      linarith
    · have h2K : 2^K ≤ Q := Nat.pow_log_le_self 2 (by omega)
      have h1 : ((2:ℝ)^(K+1)) = 2*(2:ℝ)^K := by rw [pow_succ]; ring
      rw [h1]
      have h2 : ((2:ℝ)^K) ≤ (Q:ℝ) := by exact_mod_cast h2K
      nlinarith [h2, hQ]
  have hmin : (1:ℝ)/4 ≤ A/(2:ℝ)^(K+1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hKle]
  have hstep : ∀ k ∈ Finset.range (K+1),
      czEps c (A/(2:ℝ)^(k+1)) ≤ Real.exp (2*c) * czEps c ((2:ℝ)^(K-k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkK : k ≤ K := by omega
    have harg : (1:ℝ)/4 * (2:ℝ)^(K-k) ≤ A/(2:ℝ)^(k+1) := by
      have h : A/(2:ℝ)^(K+1) * (2:ℝ)^(K-k) = A/(2:ℝ)^(k+1) := by
        rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
        have hp : (2:ℝ)^(K-k) * (2:ℝ)^(k+1) = (2:ℝ)^(K+1) := by
          rw [← pow_add]; congr 1; omega
        rw [show A * (2:ℝ)^(K-k) * (2:ℝ)^(k+1) = A * ((2:ℝ)^(K-k) * (2:ℝ)^(k+1)) by ring, hp]
      rw [← h]
      exact mul_le_mul_of_nonneg_right hmin (by positivity)
    have hnn : (0:ℝ) ≤ (1:ℝ)/4 * (2:ℝ)^(K-k) := by positivity
    have h1 : czEps c (A/(2:ℝ)^(k+1)) ≤ czEps c ((1:ℝ)/4 * (2:ℝ)^(K-k)) :=
      czEps_mono' hc.le harg (by linarith)
    have h2 : czEps c ((1:ℝ)/4 * (2:ℝ)^(K-k)) ≤ Real.exp (2*c) * czEps c ((2:ℝ)^(K-k)) := by
      have hx : (1:ℝ) ≤ (2:ℝ)^(K-k) := one_le_pow₀ (by norm_num)
      have e1 : ((2:ℝ)^(K-k) - 1)/4 ≤ (1:ℝ)/4 * (2:ℝ)^(K-k) := by nlinarith [hx]
      have e2 : czEps c ((1:ℝ)/4 * (2:ℝ)^(K-k)) ≤ czEps c (((2:ℝ)^(K-k)-1)/4) :=
        czEps_mono' hc.le e1 (by nlinarith [hx])
      have e3 : czEps c (((2:ℝ)^(K-k)-1)/4) ≤ Real.exp (2*c) * czEps c ((2:ℝ)^(K-k)) :=
        czEps_quarter_shift hc.le (by positivity)
      linarith [e2, e3]
    linarith [h1, h2]
  calc (∑ k ∈ Finset.range (K+1), czEps c (A/(2:ℝ)^(k+1)))
      ≤ ∑ k ∈ Finset.range (K+1), Real.exp (2*c) * czEps c ((2:ℝ)^(K-k)) :=
        Finset.sum_le_sum hstep
    _ = Real.exp (2*c) * ∑ k ∈ Finset.range (K+1), czEps c ((2:ℝ)^(K-k)) := by rw [Finset.mul_sum]
    _ = Real.exp (2*c) * ∑ k ∈ Finset.range (K+1), czEps c ((2:ℝ)^k) := by
        congr 1
        conv_rhs => rw [← Finset.sum_range_reflect (fun k => czEps c ((2:ℝ)^k)) (K+1)]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [show (K+1)-1-k = K-k by omega]
    _ ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have ha : 0 < c*Real.sqrt (Real.log 2) := mul_pos hc (Real.sqrt_pos.mpr hlog2)
        have hconv : ∀ k : ℕ, czEps c ((2:ℝ)^k)
            = Real.exp (-((c*Real.sqrt (Real.log 2)) * Real.sqrt (k:ℝ))) := by
          intro k
          unfold czEps
          rw [Real.log_pow, Real.sqrt_mul (Nat.cast_nonneg k) (Real.log 2)]
          ring
        simp only [hconv]
        have h := ExpSumNegSqrtSqBound ha K
        have he : (c*Real.sqrt (Real.log 2))^2 = c^2*Real.log 2 := by
          rw [mul_pow, Real.sq_sqrt (Real.log_nonneg (by norm_num))]
        rw [he] at h
        exact h

/-- **Harmonic decay**: `Σ_{q ≤ Q} q^{-1}·e^{−c√(log(A/q))} ≤ C` for `A > 0`, `Q ≤ 2A`. -/
lemma czHarmDecay_aux (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q:ℝ) ≤ 2*A →
      (∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * czEps c (A/(q:ℝ))) ≤ C := by
  refine ⟨Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) + 1, by positivity, ?_⟩
  intro A Q hA hQ
  by_cases hA1 : 1 ≤ A
  · calc (∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * czEps c (A/(q:ℝ)))
        ≤ ∑ k ∈ Finset.range (Nat.log 2 Q + 1), czEps c (A/(2:ℝ)^(k+1)) :=
          czHarmDecay_dyadic hc.le hA Q
      _ ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) := czHarmDecay_sample hc hA1 Q hQ
      _ ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) + 1 := by
          have : (0:ℝ) ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) := by positivity
          linarith
  · push Not at hA1
    have hQ2 : Q ≤ 1 := by
      have h2 : (Q:ℝ) < 2 := by linarith
      have : Q < 2 := by exact_mod_cast h2
      omega
    calc (∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * czEps c (A/(q:ℝ)))
        ≤ ∑ q ∈ Finset.Icc 1 Q, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Icc] at hq
          have hq1 : 1 ≤ q := hq.1
          have hqp : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
          have hinv : 1/(q:ℝ) ≤ 1 := by rw [div_le_one hqp]; exact_mod_cast hq1
          have hexp : czEps c (A/(q:ℝ)) ≤ 1 := czEps_le_one hc.le
          calc (1/(q:ℝ)) * czEps c (A/(q:ℝ)) ≤ 1 * 1 :=
                mul_le_mul hinv hexp (czEps_nonneg' c _) (by norm_num)
            _ = 1 := by ring
      _ = (Q:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 1
          rw [Nat.card_Icc]; omega
      _ ≤ 1 := by exact_mod_cast hQ2
      _ ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) + 1 := by
          have : (0:ℝ) ≤ Real.exp (2*c) * (10 + 10/(c^2*Real.log 2)) := by positivity
          linarith



/-- The four Region-II sum bounds, assembled from the analytic inputs. -/

lemma czRII_assembly {c : ℝ} (hc : 0 < c)
    (CH : ℝ) (hCH : 0 < CH)
    (hHarm : ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q:ℝ) ≤ 2*A →
        (∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * czEps c (A/(q:ℝ))) ≤ CH)
    (CS : ℝ) (hCS : 0 < CS)
    (hSig : ∀ (b : ℝ) (R : ℕ), 0 < b → 1 ≤ R →
        (∑ r ∈ Finset.Icc 1 R, czSig r * czEps c (b*(r:ℝ)))
          ≤ CS * (1/b + (R:ℝ) * czEps c (b*(R:ℝ))))
    (hSigSq : ∀ M : ℕ, (∑ r ∈ Finset.Icc 1 M, czSig r * (r:ℝ)^2) ≤ 3*(M:ℝ)^3)
    (hSigSum : ∀ M : ℕ, (∑ r ∈ Finset.Icc 1 M, czSig r) ≤ 3*(M:ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
        (∑ q ∈ Finset.Icc 1 (czQ y N), (1:ℝ)/q * Dc c (czR w N q)) ≤ C)
      ∧ (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
        (∑ q ∈ Finset.Icc 1 (czQ y N), (1:ℝ)/q * Dc c (czT y N q)) ≤ C)
      ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
        (∑ r ∈ Finset.Icc 1 (czR w N q), (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
          * Dc c (czTmax w y N q r))
          ≤ C * (y/w + (czR w N q : ℝ) * Dc c (czT y N q)))
      ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
        (∑ r ∈ Finset.Icc 1 (czR w N q), (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
          * (((czTmax w y N q r : ℝ)/w)^2))
          ≤ C * ((czR w N q : ℝ)^3/y^2)) := by
  refine ⟨CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1, by positivity, ?_, ?_, ?_, ?_⟩
  · intro w y N hw hwy hyN hNwy
    have hw0 : 0 < w := by linarith
    have hy0 : 0 < y := by linarith
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hQA : ((czQ y N : ℕ):ℝ) ≤ (N:ℝ)/w := by
      calc ((czQ y N : ℕ):ℝ) ≤ (N:ℝ)/y := czQ_cast_le (N:=N) hy0
        _ ≤ (N:ℝ)/w := div_le_div_of_nonneg_left hNnn hw0 hwy
    have hQA2 : ((czQ y N : ℕ):ℝ) ≤ 2 * ((N:ℝ)/w/2) := by
      rw [show (2:ℝ)*((N:ℝ)/w/2) = (N:ℝ)/w by ring]; exact hQA
    calc (∑ q ∈ Finset.Icc 1 (czQ y N), (1:ℝ)/q * Dc c (czR w N q))
        ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), (1/(q:ℝ)) * czEps c (((N:ℝ)/w/2)/(q:ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Icc] at hq
          have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
          have hqA : (q:ℝ) ≤ (N:ℝ)/w := le_trans (by exact_mod_cast hq.2) hQA
          have hAQ : 1 ≤ ((N:ℝ)/w)/(q:ℝ) := by rw [le_div_iff₀ hqR]; linarith
          have hfloor : ((czR w N q : ℕ):ℝ) = (⌊((N:ℝ)/w)/(q:ℝ)⌋₊ : ℝ) := by
            simp only [czR]; congr 1; ring
          rw [Dc_eq_czEps, hfloor]
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/(q:ℝ))
          apply czEps_mono' hc.le _ _
          · have heq : ((N:ℝ)/w/2)/(q:ℝ) = (((N:ℝ)/w)/(q:ℝ))/2 := by ring
            rw [heq]; exact floor_ge_half hAQ
          · have : 0 ≤ ((N:ℝ)/w/2)/(q:ℝ) := by positivity
            linarith
      _ ≤ CH := hHarm ((N:ℝ)/w/2) (czQ y N) (by positivity) hQA2
      _ ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by
          have : 0 ≤ 3 + 4*CS + CS*Real.exp (2*c) + 1 := by positivity
          linarith
  · intro w y N hw hwy hyN hNwy
    have hw0 : 0 < w := by linarith
    have hy0 : 0 < y := by linarith
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hQB : ((czQ y N : ℕ):ℝ) ≤ (N:ℝ)/y := czQ_cast_le (N:=N) hy0
    have hQB2 : ((czQ y N : ℕ):ℝ) ≤ 2 * ((N:ℝ)/y/2) := by
      rw [show (2:ℝ)*((N:ℝ)/y/2) = (N:ℝ)/y by ring]; exact hQB
    calc (∑ q ∈ Finset.Icc 1 (czQ y N), (1:ℝ)/q * Dc c (czT y N q))
        ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), (1/(q:ℝ)) * czEps c (((N:ℝ)/y/2)/(q:ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Icc] at hq
          have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
          have hqB : (q:ℝ) ≤ (N:ℝ)/y := le_trans (by exact_mod_cast hq.2) hQB
          have hBQ : 1 ≤ ((N:ℝ)/y)/(q:ℝ) := by rw [le_div_iff₀ hqR]; linarith
          have hfloor : ((czT y N q : ℕ):ℝ) = (⌊((N:ℝ)/y)/(q:ℝ)⌋₊ : ℝ) := by
            simp only [czT]; congr 1; ring
          rw [Dc_eq_czEps, hfloor]
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/(q:ℝ))
          apply czEps_mono' hc.le _ _
          · have heq : ((N:ℝ)/y/2)/(q:ℝ) = (((N:ℝ)/y)/(q:ℝ))/2 := by ring
            rw [heq]; exact floor_ge_half hBQ
          · have : 0 ≤ ((N:ℝ)/y/2)/(q:ℝ) := by positivity
            linarith
      _ ≤ CH := hHarm ((N:ℝ)/y/2) (czQ y N) (by positivity) hQB2
      _ ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by
          have : 0 ≤ 3 + 4*CS + CS*Real.exp (2*c) + 1 := by positivity
          linarith
  · intro w y N q hw hwy hNwy
    rcases Nat.eq_zero_or_pos (czR w N q) with hR0 | hR1
    · have hw0 : 0 < w := by linarith
      rw [hR0, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_iff.mpr (by omega),
        Finset.sum_empty]
      have hRHS : (0:ℝ) ≤ y/w + (0:ℕ) * Dc c (czT y N q) := by
        rw [show (0:ℕ) * Dc c (czT y N q) = 0 by simp, add_zero]
        exact div_nonneg (by linarith) hw0.le
      have hCC : (0:ℝ) ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by positivity
      have hres := mul_nonneg hCC hRHS
      simpa using hres
    · have hw0 : 0 < w := by linarith
      have hy0 : 0 < y := by linarith
      have hq1 : 1 ≤ q := by
        by_contra h
        push Not at h
        have hq0 : q = 0 := by omega
        subst hq0
        simp [czR] at hR1
      have hstep : (∑ r ∈ Finset.Icc 1 (czR w N q), (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
            * Dc c (czTmax w y N q r))
          ≤ czEps c (czT y N q : ℝ) * (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r)
            + ∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * czEps c (w*(r:ℝ)/(4*y)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_Icc] at hr
        have hr1 : 1 ≤ r := hr.1
        have hrR : r ≤ czR w N q := hr.2
        have hry : (r:ℝ) ≤ y := le_of_lt (cz_r_lt_y' hw0 hy0 hNwy hrR hr1)
        have hz : 0 ≤ w*(r:ℝ)/(2*y) := by positivity
        have hA := czEps_czTmax_le (c:=c) (N:=N) (q:=q) (r:=r) hc.le hw0 hy0 hr1 hry
        rw [Dc_eq_czEps]
        have hB : czEps c (w*(r:ℝ)/(2*y) - 1) ≤ czEps c (w*(r:ℝ)/(4*y)) := by
          have h1 := czEps_half_shift (c:=c) (z:=w*(r:ℝ)/(2*y)) hc.le hz
          have h2 : w*(r:ℝ)/(2*y)/2 = w*(r:ℝ)/(4*y) := by ring
          rwa [h2] at h1
        have hsig : (0:ℝ) ≤ czSig r := czSig_nonneg r
        have h1 := mul_le_mul_of_nonneg_left hA hsig
        have h2 := mul_le_mul_of_nonneg_left hB hsig
        simp only [czSig] at h1 h2 ⊢
        nlinarith [h1, h2]
      have hbound : czEps c (czT y N q : ℝ) * (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r)
            + ∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * czEps c (w*(r:ℝ)/(4*y))
          ≤ (CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1)
            * (y/w + (czR w N q : ℝ) * Dc c (czT y N q)) := by
        have hDc : czEps c (czT y N q : ℝ) = Dc c (czT y N q) := (Dc_eq_czEps c (czT y N q)).symm
        have hsum1 : czEps c (czT y N q : ℝ) * (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r)
            ≤ 3 * (((czR w N q : ℕ):ℝ) * Dc c (czT y N q)) := by
          have hh := mul_le_mul_of_nonneg_left (hSigSum (czR w N q)) (czEps_nonneg' c (czT y N q : ℝ))
          rw [hDc] at hh ⊢
          nlinarith [hh]
        have hsum2 : (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * czEps c (w*(r:ℝ)/(4*y)))
            ≤ CS * (4*(y/w) + Real.exp (2*c) * (((czR w N q : ℕ):ℝ) * Dc c (czT y N q))) := by
          have h0 := hSig (w/(4*y)) (czR w N q) (by positivity) hR1
          have heq : (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * czEps c (w*(r:ℝ)/(4*y)))
              = (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * czEps c (w/(4*y)*(r:ℝ))) := by
            apply Finset.sum_congr rfl; intro r _; congr 1; ring
          rw [heq]
          refine le_trans h0 ?_
          apply mul_le_mul_of_nonneg_left _ hCS.le
          have h1 : 1/(w/(4*y)) = 4*y/w := by field_simp
          have h2 : czEps c (w/(4*y)*((czR w N q : ℕ):ℝ))
              ≤ Real.exp (2*c) * Dc c (czT y N q) := by
            have h3 := czEps_wR_le (c:=c) (w:=w) (y:=y) (N:=N) (q:=q) hc.le hw0 hy0 hwy hNwy hq1
            have he : w/(4*y)*((czR w N q : ℕ):ℝ) = w*((czR w N q : ℕ):ℝ)/(4*y) := by ring
            rwa [he]
          rw [h1]
          rw [show (4:ℝ)*y/w = 4*(y/w) by ring]
          have hRnn2 : (0:ℝ) ≤ ((czR w N q : ℕ):ℝ) := by positivity
          have hh := mul_le_mul_of_nonneg_left h2 hRnn2
          nlinarith [hh]
        have hCC1 : 4*CS ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by
          have : 0 ≤ CH + 3 + CS*Real.exp (2*c) + 1 := by positivity
          linarith
        have hCC2 : CS*Real.exp (2*c) ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by
          have : 0 ≤ CH + 3 + 4*CS + 1 := by positivity
          linarith
        have hynn : (0:ℝ) ≤ y/w := by positivity
        have hRD : (0:ℝ) ≤ ((czR w N q : ℕ):ℝ) * Dc c (czT y N q) :=
          mul_nonneg (by positivity) (by rw [Dc_eq_czEps]; exact czEps_nonneg' c _)
        have hB1 : 4*CS*(y/w) ≤ (CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1)*(y/w) :=
          mul_le_mul_of_nonneg_right hCC1 hynn
        have hB2 : CS*Real.exp (2*c)*(((czR w N q : ℕ):ℝ) * Dc c (czT y N q))
            ≤ (CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1)*(((czR w N q : ℕ):ℝ) * Dc c (czT y N q)) :=
          mul_le_mul_of_nonneg_right hCC2 hRD
        nlinarith [hsum1, hsum2, hB1, hB2]
      linarith [hstep, hbound]
  · intro w y N q hw hwy hNwy
    have hw0 : 0 < w := by linarith
    have hy0 : 0 < y := by linarith
    have hper : ∀ r ∈ Finset.Icc 1 (czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ)) * ((czTmax w y N q r : ℝ)/w)^2
          ≤ czSig r * ((r:ℝ)/y)^2 := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hle : (czTmax w y N q r : ℝ)/w ≤ (r:ℝ)/y := by
        have h := czTmax_le_mul (w:=w) (y:=y) (N:=N) (q:=q) (r:=r) hw0 hy0 hr.1
        have h2 := div_le_div_of_nonneg_right h hw0.le
        rwa [show w*(r:ℝ)/y/w = (r:ℝ)/y by field_simp] at h2
      have hsq : ((czTmax w y N q r : ℝ)/w)^2 ≤ ((r:ℝ)/y)^2 :=
        pow_le_pow_left₀ (by positivity) hle 2
      simp only [czSig]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    calc (∑ r ∈ Finset.Icc 1 (czR w N q), (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
            * (((czTmax w y N q r : ℝ)/w)^2))
        ≤ ∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * ((r:ℝ)/y)^2 := Finset.sum_le_sum hper
      _ = (∑ r ∈ Finset.Icc 1 (czR w N q), czSig r * (r:ℝ)^2) / y^2 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl; intro r _; ring_nf
      _ ≤ (3*((czR w N q : ℝ))^3)/y^2 :=
            div_le_div_of_nonneg_right (hSigSq (czR w N q)) (by positivity)
      _ = 3*(((czR w N q : ℝ))^3/y^2) := by ring
      _ ≤ (CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1) * (((czR w N q : ℝ))^3/y^2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have h3 : (3:ℝ) ≤ CH + (3 + 4*CS + CS*Real.exp (2*c)) + 1 := by
              have : 0 ≤ CH + 4*CS + CS*Real.exp (2*c) := by positivity
              linarith
            exact h3



theorem CzRIISumBoundsHere (c : ℝ) (hc : 0 < c) :
  ∃ C : ℝ, 0 < C ∧
  (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1:ℝ)/q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czR w N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1:ℝ)/q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r))
        ≤ C * (y/w + (Work.ZeroDensity.Jutila.czR w N q : ℝ)
            * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)))
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * (((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ)/w)^2))
        ≤ C * ((Work.ZeroDensity.Jutila.czR w N q : ℝ)^3/y^2)) := by
  obtain ⟨CH, hCH, hHarm⟩ := czHarmDecay_aux c hc
  obtain ⟨CS, hCS, hSig⟩ := CzSigDecayFinal c hc
  exact czRII_assembly hc CH hCH hHarm CS hCS hSig CzSigSqSumFinal CzSigSumLeFinal

end Work.ZeroDensity.Jutila.LzDiffAux
