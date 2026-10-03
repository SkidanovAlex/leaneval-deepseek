import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.WneDefs
import Submission.Work.FIArea1.offdiag_pi_range_le
import Submission.Work.FIArea1.gauss_prime_common_divisor

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-! ## Helper lemmas -/

/-- A non-zero common divisor of a point of the polar box lies in the box `gBox (KZ N)`:
its norm divides `gnorm z ≤ 2N ≤ (KZ N)²`. -/
lemma wneL_mem_gBox_KZ_of_dvd {Pa : Work.FITop.Params} {φ : ℝ} {z π : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) (hdvd : π ∣ z) (hπ0 : π ≠ 0) :
    π ∈ Work.FIPlan.gBox (KZ Pa.N) := by
  have hgnz : 0 < Work.FIPlan.gnorm z := by
    have h1 : Pa.N < (Work.FIPlan.gnorm z : ℝ) := (mem_polarSupp.mp hz).2.1.2.1
    have h2 : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith [Pa.hN1]
    exact_mod_cast h2
  have hgnπ0 : Work.FIPlan.gnorm π ≠ 0 := by
    intro h
    apply hπ0
    have : π.norm = 0 := by
      rw [Work.FIPlan.gnorm] at h
      exact Int.natAbs_eq_zero.mp h
    exact (Zsqrtd.norm_eq_zero_iff (by norm_num : (-1 : ℤ) < 0) π).mp this
  have hdvdgn : Work.FIPlan.gnorm π ∣ Work.FIPlan.gnorm z := by
    obtain ⟨u, hu⟩ := hdvd
    rw [hu, gnorm_mul]
    exact Nat.dvd_mul_right _ _
  have hle : Work.FIPlan.gnorm π ≤ Work.FIPlan.gnorm z := Nat.le_of_dvd hgnz hdvdgn
  have hleR : (Work.FIPlan.gnorm π : ℝ) ≤ 2 * Pa.N := by
    have h2 := wne_gnorm_le_two_N hz
    have h3 : (Work.FIPlan.gnorm π : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hle
    linarith
  have hcoord : (Work.FIPlan.gnorm π : ℝ) = (π.re.natAbs : ℝ)^2 + (π.im.natAbs : ℝ)^2 := by
    rw [gnorm_coords]; push_cast; ring
  rw [Work.FIArea2.mem_gBox_iff]
  have hKZ : KZ Pa.N = ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := rfl
  constructor
  · rw [Finset.mem_Icc]
    have h1 : ((π.re.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
      have h2 : ((π.re.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
        nlinarith [hcoord, sq_nonneg (π.im.natAbs : ℝ), hleR]
      have h3 : ((π.re.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
        rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (π.re.natAbs : ℝ))]
        exact Real.sqrt_le_sqrt h2
      exact h3.trans (Nat.le_ceil _)
    have h4 : π.re.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
    have h7 : |π.re| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast h4
    simp only [hKZ]
    exact abs_le.mp h7
  · rw [Finset.mem_Icc]
    have h1 : ((π.im.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
      have h2 : ((π.im.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
        nlinarith [hcoord, sq_nonneg (π.re.natAbs : ℝ), hleR]
      have h3 : ((π.im.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
        rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (π.im.natAbs : ℝ))]
        exact Real.sqrt_le_sqrt h2
      exact h3.trans (Nat.le_ceil _)
    have h4 : π.im.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
    have h7 : |π.im| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast h4
    simp only [hKZ]
    exact abs_le.mp h7

/-- The pointwise union bound: for fixed `(w, z₁, z₂)` with `w ≠ 0` the summand of `WneLhs` is at
most the sum over the common primes `π ∈ WnePi Pa` of the summands of `WneInner`. -/
lemma wneL_pointwise (Pa : Work.FITop.Params) (φ : ℝ) (w : GaussianInt) {z1 z2 : GaussianInt}
    (h1 : z1 ∈ polarSupp Pa φ) (h2 : z2 ∈ polarSupp Pa φ) :
    (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0
      else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))
    ≤ ∑ π ∈ WnePi Pa,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)) := by
  classical
  by_cases hcond : Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hcond]
    refine Finset.sum_nonneg (fun π _ => ?_)
    by_cases h : Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2)
    · rw [if_pos h]
    · rw [if_neg h]; positivity
  · push_neg at hcond
    obtain ⟨hΔ, hnc⟩ := hcond
    obtain ⟨π0, hprime, hd1, hd2, hgt⟩ := gauss_prime_common_divisor h1 h2 hnc
    have hmem : π0 ∈ WnePi Pa := by
      rw [mem_WnePi]
      exact ⟨wneL_mem_gBox_KZ_of_dvd h1 hd1 hprime.ne_zero, hprime, hgt⟩
    have hnn : ∀ π ∈ WnePi Pa,
        0 ≤ (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)) := by
      intro π _
      by_cases h : Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2)
      · rw [if_pos h]
      · rw [if_neg h]; positivity
    have hsingle := Finset.single_le_sum hnn hmem
    have hval : (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π0 ∣ z1 ∧ π0 ∣ z2) then 0
          else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
               * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))
        = (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ) := by
      rw [if_neg]
      rintro (h | h)
      · exact hΔ h
      · exact h ⟨hd1, hd2⟩
    rw [hval] at hsingle
    rw [if_neg (fun h => h.elim hΔ hnc)]
    exact hsingle


/-! ## The union bound -/

lemma wneL_lhs_le_sum (Pa : Work.FITop.Params) (φ : ℝ) :
    WneLhs Pa φ ≤ ∑ π ∈ WnePi Pa, WneInner Pa π := by
  classical
  set S : Finset GaussianInt := (Work.FIPlan.gBox (KR Pa.M)).erase 0 with hS
  set F : GaussianInt → GaussianInt → GaussianInt → ℝ :=
    (fun w z1 z2 =>
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))) with hF
  set G : GaussianInt → GaussianInt → GaussianInt → GaussianInt → ℝ :=
    (fun w z1 z2 π =>
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))) with hG
  have hL : WneLhs Pa φ
      = ∑ w ∈ S, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ, F w z1 z2 := by
    simp only [WneLhs, hS, hF]
  have hR : (∑ π ∈ WnePi Pa, WneInner Pa π)
      = ∑ π ∈ WnePi Pa, ∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π := by
    refine Finset.sum_congr rfl (fun π _ => ?_)
    simp only [WneInner, hS, hG]
  have step1 : (∑ w ∈ S, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ, F w z1 z2)
      ≤ (∑ w ∈ S, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
          ∑ π ∈ WnePi Pa, G w z1 z2 π) := by
    refine Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun z1 h1 =>
      Finset.sum_le_sum (fun z2 h2 => ?_)))
    exact wneL_pointwise Pa φ w h1 h2
  have step2 : (∑ w ∈ S, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
        ∑ π ∈ WnePi Pa, G w z1 z2 π)
      ≤ (∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N,
          ∑ π ∈ WnePi Pa, G w z1 z2 π) := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    have hsub : polarSupp Pa φ ⊆ Zbox Pa.N := wne_polarSupp_subset_Zbox Pa φ
    have hnn : ∀ z1 z2 : GaussianInt, 0 ≤ ∑ π ∈ WnePi Pa, G w z1 z2 π := by
      intro z1 z2
      refine Finset.sum_nonneg (fun π _ => ?_)
      by_cases h : Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2)
      · rw [hG]; simp only [h, if_true, le_refl]
      · rw [hG]; simp only [h, if_false]; positivity
    calc (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ, ∑ π ∈ WnePi Pa, G w z1 z2 π)
        ≤ (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ Zbox Pa.N, ∑ π ∈ WnePi Pa, G w z1 z2 π) :=
          Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun z2 _ _ => hnn z1 z2))
      _ ≤ (∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, ∑ π ∈ WnePi Pa, G w z1 z2 π) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun z1 _ _ => Finset.sum_nonneg (fun z2 _ => hnn z1 z2))
  have step3a : (∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, ∑ π ∈ WnePi Pa, G w z1 z2 π)
      = (∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ π ∈ WnePi Pa, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π) := by
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z1 _ => ?_))
    exact Finset.sum_comm
  have step3b : (∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ π ∈ WnePi Pa, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π)
      = (∑ w ∈ S, ∑ π ∈ WnePi Pa, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    exact Finset.sum_comm
  have step3c : (∑ w ∈ S, ∑ π ∈ WnePi Pa, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π)
      = (∑ π ∈ WnePi Pa, ∑ w ∈ S, ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N, G w z1 z2 π) :=
    Finset.sum_comm
  rw [hL, hR]
  exact step1.trans (step2.trans (step3a.le.trans (step3b.le.trans step3c.le)))


/-! ## The dyadic ranges -/

/-- **Dyadic level of a real number.**  If `1 ≤ t < s ≤ t * 2^K`, then some `k ≤ K` satisfies
`t * 2^k < s ≤ t * 2^{k+1}`, i.e. `s` lies in the dyadic range `(t 2^k, 2 (t 2^k)]`. -/
lemma wneL_exists_level {t s : ℝ} {K : ℕ} (hts : t < s) (hsK : s ≤ t * 2 ^ K) :
    ∃ k ≤ K, t * 2 ^ k < s ∧ s ≤ 2 * (t * 2 ^ k) := by
  set Ax : Finset ℕ := (Finset.range (K + 1)).filter (fun k => t * 2 ^ k < s) with hAx
  have hne : Ax.Nonempty := by
    exact ⟨0, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.succ_pos K), by simpa using hts⟩⟩
  have hmaxmem : Ax.max' hne ∈ Ax := Finset.max'_mem Ax hne
  have hmaxK : Ax.max' hne ≤ K := by
    have := (Finset.mem_filter.mp hmaxmem).1
    rw [Finset.mem_range] at this
    omega
  have hmaxcond : t * 2 ^ (Ax.max' hne) < s := (Finset.mem_filter.mp hmaxmem).2
  refine ⟨Ax.max' hne, hmaxK, hmaxcond, ?_⟩
  by_contra hcon
  push Not at hcon
  have hk1 : 2 * (t * 2 ^ (Ax.max' hne)) = t * 2 ^ (Ax.max' hne + 1) := by ring
  by_cases hle : Ax.max' hne + 1 ≤ K
  · have hmem : Ax.max' hne + 1 ∈ Ax :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [← hk1]; exact hcon⟩
    have := Finset.le_max' Ax (Ax.max' hne + 1) hmem
    omega
  · have hKn : Ax.max' hne = K := by omega
    have h2 : s ≤ t * 2 ^ (Ax.max' hne) := by rw [hKn]; exact hsK
    nlinarith [hcon, h2]

/-- **The dyadic-range bound.**  The union bound over the common Gaussian primes is
`≪ Pz^{-1} M^{1/2} N^{3/2} (log MN)^{516}`. -/
lemma wneL_dyadic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params), 2 ≤ Pa.N → Pa.N ≤ Pa.M →
      (∑ π ∈ WnePi Pa, WneInner Pa π)
        ≤ C * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := offdiag_pi_range_le
  refine ⟨C1 * 2 ^ 517 + 1, by positivity, fun Pa hN hNM => ?_⟩
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith
  have hM1 : (1 : ℝ) ≤ Pa.M := by linarith
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hM0 : (0 : ℝ) ≤ Pa.M := by linarith
  have hPzR1 : (1 : ℝ) ≤ (Pa.Pz : ℝ) := by
    have h : (1 : ℕ) ≤ Pa.Pz := le_trans (by norm_num) Pa.hP2
    exact_mod_cast h
  set m : ℕ := ⌈Pa.N⌉₊ with hm
  set K : ℕ := 2 * m + 2 with hK
  set A : ℝ := Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) with hAdef
  set L : ℝ := (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) with hLdef
  set L2 : ℝ := (Real.log (Pa.M * Pa.N + 2)) ^ (516 : ℕ) with hL2def
  set cond : GaussianInt → ℕ → Prop :=
    (fun π k => (Pa.Pz : ℝ) * 2 ^ k < (Work.FIPlan.gnorm π : ℝ) ∧
      (Work.FIPlan.gnorm π : ℝ) ≤ 2 * ((Pa.Pz : ℝ) * 2 ^ k)) with hconddef
  set Rf : ℕ → Finset GaussianInt :=
    (fun k => (Work.FIPlan.gBox (KZ Pa.N)).filter (fun π => Prime π ∧ cond π k)) with hRfdef
  -- the size of the primes in `Π`
  have hsqN : Real.sqrt (2 * Pa.N) ≤ Pa.N := by
    have hNN : 2 * Pa.N ≤ Pa.N ^ 2 := by nlinarith
    calc Real.sqrt (2 * Pa.N) ≤ Real.sqrt (Pa.N ^ 2) := Real.sqrt_le_sqrt hNN
      _ = Pa.N := Real.sqrt_sq hN0
  have hKZnat : (KZ Pa.N).natAbs = ⌈Real.sqrt (2 * Pa.N)⌉₊ := by
    rw [KZ]; exact Int.natAbs_natCast _
  have hKZle : (KZ Pa.N).natAbs ≤ m := by
    rw [hKZnat, hm]; exact Nat.ceil_mono hsqN
  have hmK : 2 * m ^ 2 ≤ 2 ^ K := by
    have hm_le : m ≤ 2 ^ m := le_of_lt (Nat.lt_two_pow_self (n := m))
    have hm2 : m ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hm_le 2
    rw [hK]
    calc 2 * m ^ 2 ≤ 2 * (2 ^ m) ^ 2 := by omega
      _ ≤ 4 * (2 ^ m) ^ 2 := by omega
      _ = 2 ^ (2 * m + 2) := by
          rw [show (2:ℕ) ^ (2 * m + 2) = 2 ^ (2 * m) * 2 ^ 2 from by rw [pow_add]]
          rw [show (2:ℕ) ^ (2 * m) = (2 ^ m) ^ 2 from by rw [← pow_mul]; ring_nf]
          ring
  have hPzpos : (0 : ℕ) < Pa.Pz := by
    have := Pa.hP2; omega
  have hsK : ∀ π ∈ WnePi Pa, (Work.FIPlan.gnorm π : ℝ) ≤ (Pa.Pz : ℝ) * 2 ^ K := by
    intro π hπ
    have h1 : Work.FIPlan.gnorm π ≤ 2 * (KZ Pa.N).natAbs ^ 2 :=
      Work.FIArea2.gnorm_le_of_mem_gBox (KZ_nonneg Pa.N) (mem_WnePi.mp hπ).1
    have h2 : (KZ Pa.N).natAbs ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hKZle 2
    have h3 : Work.FIPlan.gnorm π ≤ Pa.Pz * 2 ^ K := by
      have h4 : Work.FIPlan.gnorm π ≤ 2 * m ^ 2 := by omega
      have h6 : (2:ℕ) ^ K ≤ Pa.Pz * 2 ^ K := Nat.le_mul_of_pos_left (2 ^ K) hPzpos
      omega
    have h5 : ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ ((Pa.Pz * 2 ^ K : ℕ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h5
    exact h5
  have hcov : ∀ π ∈ WnePi Pa, ∃ k ≤ K, cond π k := by
    intro π hπ
    have hlt : (Pa.Pz : ℝ) < (Work.FIPlan.gnorm π : ℝ) := by
      have := (mem_WnePi.mp hπ).2.2
      exact_mod_cast this
    exact wneL_exists_level hlt (hsK π hπ)
  -- the union bound over the dyadic ranges
  have hstepA : (∑ π ∈ WnePi Pa, WneInner Pa π)
      ≤ ∑ π ∈ WnePi Pa, ∑ k ∈ Finset.range (K + 1),
          (if cond π k then WneInner Pa π else 0) := by
    refine Finset.sum_le_sum (fun π hπ => ?_)
    obtain ⟨k0, hk0K, hk0⟩ := hcov π hπ
    have hmem : k0 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have hnn : ∀ k ∈ Finset.range (K + 1),
        0 ≤ (if cond π k then WneInner Pa π else 0) := by
      intro k _
      by_cases h : cond π k
      · rw [if_pos h]; exact WneInner_nonneg Pa π
      · rw [if_neg h]
    have hsingle := Finset.single_le_sum hnn hmem
    rwa [if_pos hk0] at hsingle
  have hstepB : (∑ π ∈ WnePi Pa, ∑ k ∈ Finset.range (K + 1),
        (if cond π k then WneInner Pa π else 0))
      = ∑ k ∈ Finset.range (K + 1), ∑ π ∈ WnePi Pa,
          (if cond π k then WneInner Pa π else 0) :=
    Finset.sum_comm
  have hstepC : ∀ k ∈ Finset.range (K + 1),
      (∑ π ∈ WnePi Pa, (if cond π k then WneInner Pa π else 0))
        ≤ ∑ π ∈ Rf k, WneInner Pa π := by
    intro k _
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun π _ _ => WneInner_nonneg Pa π)
    intro π hπ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hπ
    obtain ⟨hg, hpr, hgt⟩ := mem_WnePi.mp h1
    exact Finset.mem_filter.mpr ⟨hg, hpr, h2⟩
  have hrange : ∀ k ∈ Finset.range (K + 1),
      (∑ π ∈ Rf k, WneInner Pa π)
        ≤ C1 * (A / ((Pa.Pz : ℝ) * 2 ^ k)) * L2 := by
    intro k _
    have hq1 : 1 ≤ (Pa.Pz : ℝ) * 2 ^ k := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      nlinarith [hPzR1, h2]
    have hmain := hC1 ((Pa.Pz : ℝ) * 2 ^ k) Pa.M Pa.N hq1 hN hNM
    -- `Rf k` is exactly the range of `offdiag_pi_range_le` at `q = Pz * 2^k`
    rw [hRfdef, hAdef, hL2def]
    simpa only [hconddef, WneInner] using hmain
  have hgeom : (∑ k ∈ Finset.range (K + 1), ((Pa.Pz : ℝ) * 2 ^ k)⁻¹)
      ≤ 2 * (Pa.Pz : ℝ)⁻¹ := by
    have hfac : ∀ k : ℕ, ((Pa.Pz : ℝ) * 2 ^ k)⁻¹ = (Pa.Pz : ℝ)⁻¹ * (1 / 2 : ℝ) ^ k := by
      intro k
      rw [mul_inv, ← inv_pow]
      norm_num
    calc (∑ k ∈ Finset.range (K + 1), ((Pa.Pz : ℝ) * 2 ^ k)⁻¹)
        = (Pa.Pz : ℝ)⁻¹ * ∑ k ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => hfac k)
      _ ≤ (Pa.Pz : ℝ)⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le (K + 1))
            (inv_nonneg.mpr (by linarith))
      _ = 2 * (Pa.Pz : ℝ)⁻¹ := by ring
  have hC1nn : 0 ≤ C1 := le_of_lt hC1pos
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hN0 _)
  have hMN4 : (4 : ℝ) ≤ Pa.M * Pa.N := by nlinarith
  have hL0 : 0 ≤ L := by
    rw [hLdef]; exact pow_nonneg (Real.log_nonneg (by linarith)) _
  have hL20 : 0 ≤ L2 := by
    rw [hL2def]; exact pow_nonneg (Real.log_nonneg (by linarith)) _
  have hL2L : L2 ≤ (2:ℝ) ^ 516 * L := by
    rw [hL2def, hLdef]
    have h1 : (0 : ℝ) ≤ Real.log (Pa.M * Pa.N) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (Pa.M * Pa.N + 2) := Real.log_nonneg (by linarith)
    have h3 : Real.log (Pa.M * Pa.N + 2) ≤ 2 * Real.log (Pa.M * Pa.N) := by
      have h4 : Pa.M * Pa.N + 2 ≤ (Pa.M * Pa.N) ^ (2 : ℕ) := by nlinarith
      have h5 : 0 < Pa.M * Pa.N + 2 := by linarith
      calc Real.log (Pa.M * Pa.N + 2) ≤ Real.log ((Pa.M * Pa.N) ^ (2 : ℕ)) :=
            Real.log_le_log h5 h4
        _ = 2 * Real.log (Pa.M * Pa.N) := by rw [Real.log_pow]; norm_num
    calc (Real.log (Pa.M * Pa.N + 2)) ^ (516 : ℕ)
        ≤ (2 * Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := pow_le_pow_left₀ h2 h3 516
      _ = (2:ℝ) ^ 516 * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by rw [mul_pow]
  have hsum : (∑ k ∈ Finset.range (K + 1), ∑ π ∈ Rf k, WneInner Pa π)
      ≤ 2 * C1 * A * L2 * (Pa.Pz : ℝ)⁻¹ := by
    calc (∑ k ∈ Finset.range (K + 1), ∑ π ∈ Rf k, WneInner Pa π)
        ≤ (∑ k ∈ Finset.range (K + 1), C1 * (A / ((Pa.Pz : ℝ) * 2 ^ k)) * L2) :=
          Finset.sum_le_sum hrange
      _ = C1 * A * L2 * (∑ k ∈ Finset.range (K + 1), ((Pa.Pz : ℝ) * 2 ^ k)⁻¹) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [div_eq_mul_inv]; ring
      _ ≤ C1 * A * L2 * (2 * (Pa.Pz : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg (mul_nonneg hC1nn hA0) hL20)
      _ = 2 * C1 * A * L2 * (Pa.Pz : ℝ)⁻¹ := by ring
  have hfinal : 2 * C1 * A * L2 * (Pa.Pz : ℝ)⁻¹
      ≤ (C1 * 2 ^ 517 + 1) * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * L := by
    have hkey : 2 * C1 * L2 ≤ (C1 * 2 ^ 517 + 1) * L := by
      have h1 : 2 * C1 * L2 ≤ 2 * C1 * ((2:ℝ) ^ 516 * L) :=
        mul_le_mul_of_nonneg_left hL2L (by linarith)
      have h2 : 2 * C1 * ((2:ℝ) ^ 516 * L) = C1 * 2 ^ 517 * L := by
        rw [show (2:ℝ) ^ 517 = 2 ^ 516 * 2 from by
          rw [show (517:ℕ) = 516 + 1 from rfl, pow_succ]]
        ring
      have h3 : C1 * 2 ^ 517 * L ≤ (C1 * 2 ^ 517 + 1) * L :=
        mul_le_mul_of_nonneg_right (by linarith) hL0
      exact h1.trans (h2.trans_le h3)
    have hPzi0 : 0 ≤ (Pa.Pz : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
    calc 2 * C1 * A * L2 * (Pa.Pz : ℝ)⁻¹
        = (2 * C1 * L2) * A * (Pa.Pz : ℝ)⁻¹ := by ring
      _ ≤ ((C1 * 2 ^ 517 + 1) * L) * A * (Pa.Pz : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hA0) hPzi0
      _ ≤ ((C1 * 2 ^ 517 + 1) * L) * (Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Pa.Pz : ℝ)⁻¹ := by rw [hAdef]
      _ = (C1 * 2 ^ 517 + 1) * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2)
            * Pa.N ^ ((3 : ℝ) / 2) * L := by ring
  calc (∑ π ∈ WnePi Pa, WneInner Pa π)
      ≤ (∑ π ∈ WnePi Pa, ∑ k ∈ Finset.range (K + 1),
          (if cond π k then WneInner Pa π else 0)) := hstepA
    _ = (∑ k ∈ Finset.range (K + 1), ∑ π ∈ WnePi Pa,
          (if cond π k then WneInner Pa π else 0)) := hstepB
    _ ≤ (∑ k ∈ Finset.range (K + 1), ∑ π ∈ Rf k, WneInner Pa π) :=
        Finset.sum_le_sum hstepC
    _ ≤ 2 * C1 * A * L2 * (Pa.Pz : ℝ)⁻¹ := hsum
    _ ≤ (C1 * 2 ^ 517 + 1) * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * L := hfinal

/-! ## The target -/

/-- **The `Δ ≠ 0` non-coprime pairs with `w ≠ 0` (the `Pz^{-1}` half of *FI* (5.22)).**

For every admissible set-up `Pa` and every `φ`, with `2 ≤ N ≤ M`, the number of triples
`(w, z₁, z₂)` with `w ≠ 0` in the outer box `|w|² ≲ M`, `z₁, z₂` in the polar box (5.14)
(`Work.FIArea1.polarSupp Pa φ`), the pair non-coprime in `ℤ[i]` and `Δ(z₁,z₂) ≠ 0`, counted with
multiplicity `Z(Re wz₁)·Z(Re wz₂)`, is at most `C Pz^{-1}M^{1/2}N^{3/2}(log MN)^{516}`.

*Route.*  By `Work.FIArea1.gauss_prime_common_divisor` every counted pair has a common Gaussian
prime `π` with `gnorm π > Pz`; since `π ∣ z₁ ∈ Zbox N` also `gnorm π ≤ 2N ≤ (KZ N)²`, so
`π ∈ (gBox (KZ N)).filter (Prime · ∧ Pz < gnorm ·)`.  Hence (union bound, `Finset.single_le_sum`)

`LHS ≤ ∑_{π ∈ Π} ∑_{w ∈ gBox (KR M).erase 0} ∑_{z₁,z₂ ∈ polarSupp} (Δ ≠ 0, π ∣ z₁, π ∣ z₂) Z Z`,

and `polarSupp` is replaced by the larger `Zbox N` (monotonicity, summands `≥ 0`).  Partitioning
`Π` by the dyadic ranges `gnorm π ∈ (Pz 2^k, Pz 2^{k+1}]` (`k ≤ K`, `K` large enough that
`Pz 2^K ≥ 2N`; each `π ∈ Π` lies in one of them because `gnorm π ≤ 2N`) the `k`-th piece is exactly
the left-hand side of `Work.FIArea1.offdiag_pi_range_le` with `q = Pz * 2^k`, so it is at most
`C (M^{1/2}N^{3/2}/(Pz2^k))(log MN)^{516}`.  Summing the geometric series
`∑_k 2^{-k} ≤ 2` gives the display. -/
theorem offdiag_delta_ne_wne_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      2 ≤ Pa.N → Pa.N ≤ Pa.M →
      (∑ w ∈ (Work.FIPlan.gBox (Work.FIArea1.KR Pa.M)).erase 0,
        ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ, ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
        ≤ C * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  obtain ⟨C, hCpos, hC⟩ := wneL_dyadic_bound
  refine ⟨C, hCpos, fun Pa φ hN hNM => ?_⟩
  show WneLhs Pa φ ≤ _
  exact (wneL_lhs_le_sum Pa φ).trans (hC Pa hN hNM)

end

end Work.FIArea1
