import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.gnorm_inv_sums
import Submission.Work.FIArea1.gauss_prime_common_divisor

set_option maxHeartbeats 4000000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts about the polar box -/

/-- `θ ≤ 1`: from `θ = (log x)^{-A'}`, `log x ≥ 1` and `A' ≥ 0`. -/
lemma wzero_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by
    have : (0 : ℕ) < Pa.x := by linarith [Pa.hx]
    exact_mod_cast this
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le hx0]
    have : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hA' : (0 : ℝ) ≤ Pa.A' := by
    have h1 := Pa.hA'
    have hA0 : (0 : ℝ) ≤ Pa.A := le_of_lt Pa.hA
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) by positivity]
  calc (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    _ = 1 := Real.rpow_zero _

/-- A point of the polar box has norm `> N`. -/
lemma wzero_gnorm_gt_N (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : Pa.N < (Work.FIPlan.gnorm z : ℝ) := by
  rw [mem_polarSupp] at hz
  exact hz.2.1.2.1

/-- A point of the polar box has norm `≤ 2N`. -/
lemma wzero_polarSupp_gnorm_le (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  rw [mem_polarSupp] at hz
  have hle : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hz.2.1.2.2.1
  have hθ := wzero_theta_le_one Pa
  have hN0 : 0 ≤ Pa.N := by linarith [Pa.hN1]
  have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by
    nlinarith [mul_le_mul_of_nonneg_right hθ hN0, hN0]
  linarith

/-! ## 2. The set `Π` of large-norm Gaussian primes in the inner box -/

/-- `Π = {π ∈ gBox (KZ N) : π prime, |π|² > Pz}`. -/
def piSet (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Prime d ∧ Pa.Pz < Work.FIPlan.gnorm d)

lemma mem_piSet {Pa : Work.FITop.Params} {d : GaussianInt} :
    d ∈ piSet Pa ↔ d ∈ Work.FIPlan.gBox (KZ Pa.N) ∧ Prime d
      ∧ Pa.Pz < Work.FIPlan.gnorm d := by
  rw [piSet, Finset.mem_filter]

/-- `Π ⊆ (gBox (KZ N)).filter (Pz < |·|²)`. -/
lemma piSet_subset_filter_gnorm (Pa : Work.FITop.Params) :
    piSet Pa ⊆ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d) := by
  intro d hd
  rw [mem_piSet] at hd
  exact Finset.mem_filter.mpr ⟨hd.1, hd.2.2⟩

/-- A Gaussian prime dividing a polar-box point lies in the inner box `gBox (KZ N)`. -/
lemma prime_mem_gBox_KZ (Pa : Work.FITop.Params) (φ : ℝ) {z π : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) (hπ : Prime π) (hd : π ∣ z) :
    π ∈ Work.FIPlan.gBox (KZ Pa.N) := by
  rw [Work.FIArea2.mem_gBox_iff]
  have hzN : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := wzero_polarSupp_gnorm_le Pa φ hz
  have hzgt : Pa.N < (Work.FIPlan.gnorm z : ℝ) := wzero_gnorm_gt_N Pa φ hz
  have hzpos : 0 < Work.FIPlan.gnorm z := by
    have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
    have : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
    exact_mod_cast this
  have hz0 : z ≠ 0 := fun h =>
    (Nat.pos_iff_ne_zero.mp hzpos) ((Work.FIArea2.gnorm_eq_zero_iff z).mpr h)
  have hgnπ_le : Work.FIPlan.gnorm π ≤ Work.FIPlan.gnorm z := by
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by
      intro h; rw [h, mul_zero] at hk; exact hz0 hk
    have h1 : Work.FIPlan.gnorm z = Work.FIPlan.gnorm π * Work.FIPlan.gnorm k := by
      rw [hk, gnorm_mul]
    have h2 : 1 ≤ Work.FIPlan.gnorm k := by
      rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm k) with h | h
      · exact absurd ((Work.FIArea2.gnorm_eq_zero_iff k).mp h) hk0
      · exact h
    calc Work.FIPlan.gnorm π = Work.FIPlan.gnorm π * 1 := (mul_one _).symm
      _ ≤ Work.FIPlan.gnorm π * Work.FIPlan.gnorm k := Nat.mul_le_mul_left _ h2
      _ = Work.FIPlan.gnorm z := h1.symm
  have hnormπ : (Work.FIPlan.gnorm π : ℝ) ≤ 2 * Pa.N :=
    le_trans (by exact_mod_cast hgnπ_le) hzN
  have hcoord : ∀ y : ℤ, y = π.re ∨ y = π.im → y ∈ Finset.Icc (-(KZ Pa.N)) (KZ Pa.N) := by
    intro y hy
    have hy2 : (y : ℝ) ^ 2 ≤ 2 * Pa.N := by
      have hg : (Work.FIPlan.gnorm π : ℤ) = π.re ^ 2 + π.im ^ 2 := gnorm_int π
      have h1 : (y : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm π : ℤ) := by
        rcases hy with rfl | rfl
        · rw [hg]; nlinarith [sq_nonneg π.im]
        · rw [hg]; nlinarith [sq_nonneg π.re]
      have h2 : ((y : ℤ) ^ 2 : ℝ) ≤ (Work.FIPlan.gnorm π : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have habs : |(y : ℝ)| ≤ Real.sqrt (2 * Pa.N) := by
      rw [← Real.sqrt_sq_eq_abs (y : ℝ)]
      exact Real.sqrt_le_sqrt hy2
    have hle : |y| ≤ KZ Pa.N := by
      have h1 : ((|y| : ℤ) : ℝ) ≤ ((KZ Pa.N : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        refine le_trans habs ?_
        rw [KZ]; push_cast; exact Nat.le_ceil _
      exact_mod_cast h1
    exact Finset.mem_Icc.mpr (abs_le.mp hle)
  exact ⟨hcoord π.re (Or.inl rfl), hcoord π.im (Or.inr rfl)⟩

/-! ## 3. The union bound over `Π` -/

/-- **The union bound**: the number of `Δ ≠ 0` non-coprime polar pairs is at most
`∑_{π ∈ Π} (♯{z ∈ polarSupp : π ∣ z})²`. -/
lemma wzero_union_bound (Pa : Work.FITop.Params) (φ : ℝ) :
    (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0 else 1))
    ≤ ∑ π ∈ piSet Pa, (((polarSupp Pa φ).filter (fun z => π ∣ z)).card : ℝ) ^ 2 := by
  set PS := polarSupp Pa φ with hPS
  have hpoint : ∀ z1 ∈ PS, ∀ z2 ∈ PS,
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then (0 : ℝ) else 1)
      ≤ ∑ π ∈ piSet Pa, (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) := by
    intro z1 h1 z2 h2
    by_cases hc : Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2
    · simp [hc]
    · simp only [hc, if_false]
      push Not at hc
      obtain ⟨π, hprime, hd1, hd2, hPz⟩ := gauss_prime_common_divisor h1 h2 hc.2
      have hmem : π ∈ piSet Pa := by
        rw [mem_piSet]
        exact ⟨prime_mem_gBox_KZ Pa φ h1 hprime hd1, hprime, hPz⟩
      have hterm : (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) = 1 := by simp [hd1, hd2]
      calc (1 : ℝ) = (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) := hterm.symm
        _ ≤ ∑ π' ∈ piSet Pa, (if π' ∣ z1 ∧ π' ∣ z2 then (1 : ℝ) else 0) :=
            Finset.single_le_sum (f := fun π' => (if π' ∣ z1 ∧ π' ∣ z2 then (1 : ℝ) else 0))
              (fun i _ => by positivity) hmem
  calc (∑ z1 ∈ PS, ∑ z2 ∈ PS,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then (0 : ℝ) else 1))
      ≤ ∑ z1 ∈ PS, ∑ z2 ∈ PS, ∑ π ∈ piSet Pa, (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun z1 h1 => Finset.sum_le_sum (fun z2 h2 => hpoint z1 h1 z2 h2))
    _ = ∑ π ∈ piSet Pa, ∑ z1 ∈ PS, ∑ z2 ∈ PS,
          (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) := by
        have h1 : (∑ z1 ∈ PS, ∑ z2 ∈ PS, ∑ π ∈ piSet Pa,
              (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0))
            = ∑ z1 ∈ PS, ∑ π ∈ piSet Pa, ∑ z2 ∈ PS,
              (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun z1 _ => Finset.sum_comm)
        rw [h1]
        exact Finset.sum_comm
    _ = ∑ π ∈ piSet Pa, (((PS.filter (fun z => π ∣ z)).card : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro π _
        have hstep : ∀ z1 ∈ PS, ∀ z2 ∈ PS,
            (if π ∣ z1 ∧ π ∣ z2 then (1 : ℝ) else 0)
              = (if π ∣ z1 then (1 : ℝ) else 0) * (if π ∣ z2 then (1 : ℝ) else 0) := by
          intro z1 _ z2 _
          by_cases h1 : π ∣ z1 <;> by_cases h2 : π ∣ z2 <;> simp [h1, h2]
        rw [Finset.sum_congr rfl (fun z1 h1 => Finset.sum_congr rfl (fun z2 h2 => hstep z1 h1 z2 h2))]
        rw [← Finset.sum_mul_sum, Finset.sum_boole]
        ring

/-! ## 4. The per-`π` lattice count -/

/-- The elementary lattice-point bound `(2⌈√U⌉+1)² ≤ 15(U+1)`. -/
lemma ceil_sqrt_sq_le (U : ℝ) (hU : 0 ≤ U) :
    (((2 * (Nat.ceil (Real.sqrt U)) + 1) ^ 2 : ℕ) : ℝ) ≤ 15 * (U + 1) := by
  have h1 : (Nat.ceil (Real.sqrt U) : ℝ) < Real.sqrt U + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg U)
  have hcast : (((2 * (Nat.ceil (Real.sqrt U)) + 1) ^ 2 : ℕ) : ℝ)
      = (2 * (Nat.ceil (Real.sqrt U) : ℝ) + 1) ^ 2 := by push_cast; ring
  rw [hcast]
  have hs : 2 * Real.sqrt U ≤ U + 1 := by
    nlinarith [sq_nonneg (Real.sqrt U - 1), Real.sq_sqrt hU, Real.sqrt_nonneg U]
  have h3 : (2 * (Nat.ceil (Real.sqrt U) : ℝ) + 1) ^ 2 ≤ (2 * Real.sqrt U + 3) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    linarith
  have h4 : (2 * Real.sqrt U + 3) ^ 2 ≤ 15 * (U + 1) := by
    nlinarith [hs, Real.sq_sqrt hU]
  linarith

/-- For `π ∈ Π`, the multiples of `π` in the polar box number at most `15(2N/|π|² + 1)`. -/
lemma pi_dvd_count_le (Pa : Work.FITop.Params) (φ : ℝ) {π : GaussianInt}
    (hπ : π ∈ piSet Pa) :
    (((polarSupp Pa φ).filter (fun z => π ∣ z)).card : ℝ)
      ≤ 15 * (2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1) := by
  set PS := polarSupp Pa φ with hPS
  have hprime : Prime π := (mem_piSet.mp hπ).2.1
  have hgpos : 0 < (Work.FIPlan.gnorm π : ℝ) := by
    have hne : Work.FIPlan.gnorm π ≠ 0 := by
      intro h0
      exact hprime.ne_zero ((Work.FIArea2.gnorm_eq_zero_iff π).mp h0)
    exact_mod_cast Nat.pos_of_ne_zero hne
  set U : ℝ := 2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ with hUdef
  have hUnn : 0 ≤ U := by
    rw [hUdef]
    exact mul_nonneg (by linarith [Pa.hN1] : (0 : ℝ) ≤ 2 * Pa.N) (inv_nonneg.mpr hgpos.le)
  set R : ℤ := (Nat.ceil (Real.sqrt U) : ℤ) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact Int.natCast_nonneg _
  have hsub : PS.filter (fun z => π ∣ z) ⊆ (Work.FIPlan.gBox R).image (fun y => π * y) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzPS, hdvd⟩ := hz
    obtain ⟨y, rfl⟩ := hdvd
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    rw [Work.FIArea2.mem_gBox_iff]
    have hgn : (Work.FIPlan.gnorm (π * y) : ℝ) ≤ 2 * Pa.N := wzero_polarSupp_gnorm_le Pa φ hzPS
    rw [gnorm_mul, Nat.cast_mul] at hgn
    have hy_le : (Work.FIPlan.gnorm y : ℝ) ≤ U := by
      rw [hUdef]
      rw [← div_eq_mul_inv, le_div_iff₀ hgpos]
      rw [mul_comm]
      exact hgn
    have hy_coord : ∀ c : ℤ, c = y.re ∨ c = y.im → c ∈ Finset.Icc (-R) R := by
      intro c hc
      have hcy : (c : ℝ) ^ 2 ≤ U := by
        have hsq : ((c : ℤ) ^ 2 : ℝ) ≤ (Work.FIPlan.gnorm y : ℝ) := by
          have hg : (Work.FIPlan.gnorm y : ℤ) = y.re ^ 2 + y.im ^ 2 := gnorm_int y
          have h1 : (c : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm y : ℤ) := by
            rcases hc with rfl | rfl
            · rw [hg]; nlinarith [sq_nonneg y.im]
            · rw [hg]; nlinarith [sq_nonneg y.re]
          exact_mod_cast h1
        push_cast at hsq
        linarith
      have habs : |(c : ℝ)| ≤ Real.sqrt U := by
        rw [← Real.sqrt_sq_eq_abs (c : ℝ)]
        exact Real.sqrt_le_sqrt hcy
      have hle : |c| ≤ R := by
        rw [hRdef]
        have h1 : ((|c| : ℤ) : ℝ) ≤ ((Nat.ceil (Real.sqrt U) : ℤ) : ℝ) := by
          rw [Int.cast_abs]
          push_cast
          exact le_trans habs (Nat.le_ceil _)
        exact_mod_cast h1
      exact Finset.mem_Icc.mpr (abs_le.mp hle)
    exact ⟨hy_coord y.re (Or.inl rfl), hy_coord y.im (Or.inr rfl)⟩
  calc ((PS.filter (fun z => π ∣ z)).card : ℝ)
      ≤ ((Work.FIPlan.gBox R).image (fun y => π * y)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Work.FIPlan.gBox R).card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ = (((2 * R.natAbs + 1) ^ 2 : ℕ) : ℝ) := by rw [card_gBox R hRnn]
    _ = (((2 * Nat.ceil (Real.sqrt U) + 1) ^ 2 : ℕ) : ℝ) := by rw [hRdef, Int.natAbs_natCast]
    _ ≤ 15 * (U + 1) := ceil_sqrt_sq_le U hUnn
    _ = 15 * (2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1) := by rw [hUdef]

/-! ## 5. The cardinality of `Π` -/

/-- `♯Π ≤ 45 N`. -/
lemma card_piSet_le (Pa : Work.FITop.Params) (hN2 : 2 ≤ Pa.N) :
    ((piSet Pa).card : ℝ) ≤ 45 * Pa.N := by
  have hNpos : 0 < Pa.N := by linarith
  have hs2N : (0 : ℝ) ≤ 2 * Pa.N := by linarith
  have hstep : (piSet Pa).card ≤ (2 * (KZ Pa.N).natAbs + 1) ^ 2 := by
    calc (piSet Pa).card ≤ (Work.FIPlan.gBox (KZ Pa.N)).card := Finset.card_filter_le _ _
      _ = (2 * (KZ Pa.N).natAbs + 1) ^ 2 := card_gBox (KZ Pa.N) (KZ_nonneg Pa.N)
  have hKZval : (((KZ Pa.N).natAbs : ℕ) : ℝ) = (Nat.ceil (Real.sqrt (2 * Pa.N)) : ℝ) := by
    have h1 : (KZ Pa.N).natAbs = Nat.ceil (Real.sqrt (2 * Pa.N)) := by
      rw [KZ]; exact Int.natAbs_natCast _
    rw [h1]
  have h3 : (Nat.ceil (Real.sqrt (2 * Pa.N)) : ℝ) < Real.sqrt (2 * Pa.N) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have h4 : Real.sqrt (2 * Pa.N) ≤ Pa.N := by
    calc Real.sqrt (2 * Pa.N) ≤ Real.sqrt (Pa.N ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hN2, hNpos])
      _ = Pa.N := Real.sqrt_sq hNpos.le
  have hbound : (((2 * (KZ Pa.N).natAbs + 1 : ℕ) : ℝ)) ^ 2 ≤ 45 * Pa.N := by
    have hcast : ((2 * (KZ Pa.N).natAbs + 1 : ℕ) : ℝ)
        = 2 * (((KZ Pa.N).natAbs : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, hKZval]
    have h7 : 2 * (Nat.ceil (Real.sqrt (2 * Pa.N)) : ℝ) + 1 < 2 * Real.sqrt (2 * Pa.N) + 3 := by
      linarith
    have h8 : (2 * (Nat.ceil (Real.sqrt (2 * Pa.N)) : ℝ) + 1) ^ 2
        ≤ (2 * Real.sqrt (2 * Pa.N) + 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h7.le 2
    have hs : 2 * Real.sqrt (2 * Pa.N) ≤ 2 * Pa.N + 1 := by
      nlinarith [sq_nonneg (Real.sqrt (2 * Pa.N) - 1), Real.sq_sqrt hs2N]
    have h9 : (2 * Real.sqrt (2 * Pa.N) + 3) ^ 2 ≤ 45 * Pa.N := by
      nlinarith [hs, Real.sq_sqrt hs2N, hNpos]
    linarith
  calc ((piSet Pa).card : ℝ) ≤ (((2 * (KZ Pa.N).natAbs + 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hstep
    _ = ((2 * (KZ Pa.N).natAbs + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring
    _ ≤ 45 * Pa.N := hbound

/-! ## 6. The arithmetic facts -/

/-- `N ≤ (MN)^{1/2}`. -/
lemma wzero_N_le_sqrt_MN (Pa : Work.FITop.Params) (hN2 : 2 ≤ Pa.N) :
    Pa.N ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) := by
  have hNpos : 0 < Pa.N := by linarith
  have hMN : Pa.N ^ 2 ≤ Pa.M * Pa.N := by nlinarith [Pa.hMge, hNpos]
  rw [← Real.sqrt_eq_rpow (Pa.M * Pa.N)]
  calc Pa.N = Real.sqrt (Pa.N ^ 2) := (Real.sqrt_sq hNpos.le).symm
    _ ≤ Real.sqrt (Pa.M * Pa.N) := Real.sqrt_le_sqrt hMN

/-- `N ≤ M^{3/4}N^{3/4}` and `N² ≤ M^{1/2}N^{3/2}`. -/
lemma wzero_quarter_bounds (Pa : Work.FITop.Params) (hN2 : 2 ≤ Pa.N) :
    Pa.N ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
      ∧ Pa.N ^ 2 ≤ Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by
  have hNpos : 0 < Pa.N := by linarith
  have hMpos : 0 < Pa.M := by linarith [Pa.hM1]
  have hsq : Pa.N ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) := wzero_N_le_sqrt_MN Pa hN2
  have hPnn : (0 : ℝ) ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) := by positivity
  constructor
  · have hsplit : (Pa.M * Pa.N) ^ ((3 : ℝ) / 4)
        = (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) := by
      rw [show ((3 : ℝ) / 4) = (1 : ℝ) / 2 + (1 : ℝ) / 4 by norm_num,
        Real.rpow_add (by positivity)]
    have hone : (1 : ℝ) ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by nlinarith [Pa.hM1, hN2]) (by norm_num)
    calc Pa.N ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) := hsq
      _ ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) :=
          le_mul_of_one_le_right hPnn hone
      _ = (Pa.M * Pa.N) ^ ((3 : ℝ) / 4) := hsplit.symm
      _ = Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow hMpos.le hNpos.le
  · have hT : Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
        = (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) * Pa.N := by
      have h1 : Pa.N ^ ((3 : ℝ) / 2) = Pa.N ^ ((1 : ℝ) / 2) * Pa.N := by
        rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
      rw [h1, ← mul_assoc, ← Real.mul_rpow hMpos.le hNpos.le]
    rw [hT]
    calc Pa.N ^ 2 = Pa.N * Pa.N := by ring
      _ ≤ (Pa.M * Pa.N) ^ ((1 : ℝ) / 2) * Pa.N :=
          mul_le_mul_of_nonneg_right hsq hNpos.le

/-- `log(KZ N + 2) ≤ log 5 + log(MN)`. -/
lemma wzero_log_KZ_le (Pa : Work.FITop.Params) (hN2 : 2 ≤ Pa.N) :
    Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ) ≤ Real.log 5 + Real.log (Pa.M * Pa.N) := by
  have hNpos : 0 < Pa.N := by linarith
  have hMN : Pa.N ≤ Pa.M * Pa.N := by
    have := mul_le_mul_of_nonneg_right Pa.hM1 hNpos.le
    linarith [this]
  have hKZ : (KZ Pa.N : ℝ) + 2 ≤ 5 * Pa.N := by
    have h3 : (KZ Pa.N : ℝ) < Real.sqrt (2 * Pa.N) + 1 := by
      rw [KZ]; push_cast; exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h4 : Real.sqrt (2 * Pa.N) ≤ Pa.N := by
      calc Real.sqrt (2 * Pa.N) ≤ Real.sqrt (Pa.N ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [hN2, hNpos])
        _ = Pa.N := Real.sqrt_sq hNpos.le
    linarith
  have h5 : (5 : ℝ) * Pa.N ≤ 5 * (Pa.M * Pa.N) := by nlinarith [hMN]
  have hcast : ((((KZ Pa.N : ℤ) + 2 : ℤ)) : ℝ) = (KZ Pa.N : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hpos : (0 : ℝ) < (KZ Pa.N : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (KZ Pa.N : ℝ) := by exact_mod_cast KZ_nonneg Pa.N
    linarith
  calc Real.log ((KZ Pa.N : ℝ) + 2) ≤ Real.log (5 * Pa.N) := Real.log_le_log hpos hKZ
    _ = Real.log 5 + Real.log Pa.N := Real.log_mul (by norm_num) (ne_of_gt hNpos)
    _ ≤ Real.log 5 + Real.log (Pa.M * Pa.N) := by
        have := Real.log_le_log hNpos hMN
        linarith

/-- The constant of the final estimate (as a function of `C₁`). -/
def wzeroConstant (C₁ : ℝ) : ℝ :=
  900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹)
    + 900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹)
    + 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹)
    + 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) + 1

lemma wzeroConstant_pos {C₁ : ℝ} (h : 0 < C₁) : 0 < wzeroConstant C₁ := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (Real.log 2) ^ (516 : ℕ) := pow_pos h2 516
  have hq : (0 : ℝ) < (Real.log 2) ^ (515 : ℕ) := pow_pos h2 515
  rw [wzeroConstant]
  positivity

lemma wzeroConstant_ge_A {C₁ : ℝ} (h : 0 < C₁) :
    900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹) ≤ wzeroConstant C₁ := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (Real.log 2) ^ (516 : ℕ) := pow_pos h2 516
  have hq : (0 : ℝ) ≤ (Real.log 2) ^ (515 : ℕ) := pow_nonneg h2.le 515
  rw [wzeroConstant]
  have h1 : (0 : ℝ) ≤ 900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹) := by positivity
  have h3 : (0 : ℝ) ≤ 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹) := by positivity
  have h4 : (0 : ℝ) ≤ 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) := by positivity
  linarith

lemma wzeroConstant_ge_QQ {C₁ : ℝ} (h : 0 < C₁) :
    900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹)
      + 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹)
      + 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) ≤ wzeroConstant C₁ := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (0 : ℝ) < (Real.log 2) ^ (516 : ℕ) := pow_pos h2 516
  have hq : (0 : ℝ) ≤ (Real.log 2) ^ (515 : ℕ) := pow_nonneg h2.le 515
  rw [wzeroConstant]
  have h1 : (0 : ℝ) ≤ 900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹) := by positivity
  linarith

/-- The final numerical comparison. -/
lemma wzero_arith (Pa : Work.FITop.Params) (hN2 : 2 ≤ Pa.N) {C₁ : ℝ} (hC₁ : 0 < C₁) :
    900 * C₁ * Pa.N ^ 2 * ((Pa.Pz : ℝ)⁻¹)
        + 900 * C₁ * Pa.N * (1 + Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ))
        + 10125 * Pa.N
    ≤ wzeroConstant C₁ * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
        + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
      * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  set L := Real.log (Pa.M * Pa.N) with hLdef
  set Q := Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) with hQdef
  set Rr := (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) with hRdef
  have hNpos : 0 < Pa.N := by linarith
  have hMN2 : (2 : ℝ) ≤ Pa.M * Pa.N := by
    have := mul_le_mul_of_nonneg_right Pa.hM1 (by linarith : (0 : ℝ) ≤ Pa.N)
    linarith [this]
  have hLpos : 0 < L := by
    rw [hLdef]; apply Real.log_pos; linarith
  have hL2le : Real.log 2 ≤ L := by
    rw [hLdef]; apply Real.log_le_log (by norm_num); linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hMpos : 0 < Pa.M := by linarith [Pa.hM1]
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (Real.rpow_nonneg hMpos.le _) (Real.rpow_nonneg hNpos.le _)
  have hRnn : 0 ≤ Rr := by
    rw [hRdef]
    have h1 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
    have h2 : (0 : ℝ) ≤ Pa.M ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hMpos.le _
    have h3 : (0 : ℝ) ≤ Pa.N ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hNpos.le _
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hNleQ : Pa.N ≤ Q := by rw [hQdef]; exact (wzero_quarter_bounds Pa hN2).1
  have hN2leR : Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹ ≤ Rr := by
    rw [hRdef]
    have := mul_le_mul_of_nonneg_right (wzero_quarter_bounds Pa hN2).2
      (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (Pa.Pz : ℝ)))
    calc Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹
        ≤ (Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)) * (Pa.Pz : ℝ)⁻¹ := this
      _ = (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by ring
  have hL516 : (Real.log 2) ^ (516 : ℕ) ≤ L ^ (516 : ℕ) :=
    pow_le_pow_left₀ hlog2pos.le hL2le 516
  have hL515 : (Real.log 2) ^ (515 : ℕ) ≤ L ^ (515 : ℕ) :=
    pow_le_pow_left₀ hlog2pos.le hL2le 515
  have hLpos516 : (0 : ℝ) ≤ L ^ (516 : ℕ) := pow_nonneg hLpos.le 516
  have hp516 : (0 : ℝ) < (Real.log 2) ^ (516 : ℕ) := pow_pos hlog2pos 516
  have hp515 : (0 : ℝ) < (Real.log 2) ^ (515 : ℕ) := pow_pos hlog2pos 515
  have hone516 : (1 : ℝ) ≤ (((Real.log 2) ^ (516 : ℕ))⁻¹) * L ^ (516 : ℕ) := by
    rw [inv_mul_eq_div, one_le_div hp516]; exact hL516
  have hl5 : (0 : ℝ) < 1 + Real.log 5 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5); linarith
  -- (1) `900 C₁ ≤ wzeroConstant C₁ * L^516`
  have hconst1 : 900 * C₁ ≤ wzeroConstant C₁ * L ^ (516 : ℕ) := by
    have hle1 : 900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹) ≤ wzeroConstant C₁ :=
      wzeroConstant_ge_A hC₁
    have h2 : 900 * C₁ ≤ 900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹) * L ^ (516 : ℕ) := by
      have := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 900 * C₁) hone516
      nlinarith [this]
    have h3 : 900 * C₁ * (((Real.log 2) ^ (516 : ℕ))⁻¹) * L ^ (516 : ℕ)
        ≤ wzeroConstant C₁ * L ^ (516 : ℕ) :=
      mul_le_mul_of_nonneg_right hle1 hLpos516
    linarith [h2, h3]
  -- (2) `L ≤ L^516 * ((log 2)^515)⁻¹`
  have hLle : L ≤ L ^ (516 : ℕ) * (((Real.log 2) ^ (515 : ℕ))⁻¹) := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp515]
    calc L * (Real.log 2) ^ (515 : ℕ) = (Real.log 2) ^ (515 : ℕ) * L := by ring
      _ ≤ L ^ (515 : ℕ) * L := mul_le_mul_of_nonneg_right hL515 hLpos.le
      _ = L ^ (516 : ℕ) := by
          rw [← pow_succ]
  -- the `Rr` piece
  have hA : 900 * C₁ * Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹ ≤ wzeroConstant C₁ * Rr * L ^ (516 : ℕ) := by
    have ha : 900 * C₁ * Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹
        = 900 * C₁ * (Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹) := by ring
    rw [ha]
    have h1 : 900 * C₁ * (Pa.N ^ 2 * (Pa.Pz : ℝ)⁻¹) ≤ 900 * C₁ * Rr :=
      mul_le_mul_of_nonneg_left hN2leR (by positivity)
    have h2 : 900 * C₁ * Rr ≤ wzeroConstant C₁ * Rr * L ^ (516 : ℕ) := by
      have h3 := mul_le_mul_of_nonneg_right hconst1 hRnn
      nlinarith [h3]
    linarith [h1, h2]
  -- the `Q` pieces together
  have hQpart : 900 * C₁ * Pa.N * (1 + Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ)) + 10125 * Pa.N
      ≤ wzeroConstant C₁ * Q * L ^ (516 : ℕ) := by
    have hlogKZ : Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ) ≤ Real.log 5 + L := by
      rw [hLdef]; exact wzero_log_KZ_le Pa hN2
    have hB1 : 900 * C₁ * Pa.N * (1 + Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ))
        ≤ 900 * C₁ * Pa.N * (1 + (Real.log 5 + L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hB2 : 900 * C₁ * Pa.N * (1 + (Real.log 5 + L))
        = 900 * C₁ * Pa.N * (1 + Real.log 5) + 900 * C₁ * Pa.N * L := by ring
    rw [hB2] at hB1
    have hB3 : 900 * C₁ * Pa.N * (1 + Real.log 5)
        ≤ 900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
      have h2 : 900 * C₁ * Pa.N * (1 + Real.log 5) ≤ 900 * C₁ * (1 + Real.log 5) * Q := by
        have := mul_le_mul_of_nonneg_left hNleQ
          (by positivity : (0 : ℝ) ≤ 900 * C₁ * (1 + Real.log 5))
        nlinarith [this]
      have h3 : 900 * C₁ * (1 + Real.log 5) * Q
          ≤ 900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
        have hc : (0 : ℝ) ≤ 900 * C₁ * (1 + Real.log 5) * Q := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hone516 hc]
      linarith [h2, h3]
    have hB4 : 900 * C₁ * Pa.N * L
        ≤ 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
      have h2 : 900 * C₁ * Pa.N * L ≤ 900 * C₁ * Q * L := by
        have := mul_le_mul_of_nonneg_left hNleQ (by positivity : (0 : ℝ) ≤ 900 * C₁ * L)
        nlinarith [this]
      have h3 : 900 * C₁ * Q * L
          ≤ 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
        have hc : (0 : ℝ) ≤ 900 * C₁ * Q := by positivity
        have hh := mul_le_mul_of_nonneg_left hLle hc
        nlinarith [hh]
      linarith [h2, h3]
    have hC3 : 10125 * Pa.N ≤ 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
      have h2 : 10125 * Pa.N ≤ 10125 * Q := by nlinarith [hNleQ]
      have h3 : 10125 * Q ≤ 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) * Q * L ^ (516 : ℕ) := by
        have hc : (0 : ℝ) ≤ 10125 * Q := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hone516 hc]
      linarith [h2, h3]
    have hconst : 900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹)
        + 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹)
        + 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹) ≤ wzeroConstant C₁ :=
      wzeroConstant_ge_QQ hC₁
    have hsum : (900 * C₁ * (1 + Real.log 5) * (((Real.log 2) ^ (516 : ℕ))⁻¹)
        + 900 * C₁ * (((Real.log 2) ^ (515 : ℕ))⁻¹)
        + 10125 * (((Real.log 2) ^ (516 : ℕ))⁻¹)) * Q * L ^ (516 : ℕ)
        ≤ wzeroConstant C₁ * Q * L ^ (516 : ℕ) := by
      have := mul_le_mul_of_nonneg_right hconst (by positivity : (0 : ℝ) ≤ Q * L ^ (516 : ℕ))
      nlinarith [this]
    linarith [hB1, hB3, hB4, hC3, hsum]
  linarith [hA, hQpart]

/-! ## 7. The counting bound -/

/-- The counting bound `S ≤ 900 C₁ N²/Pz + 900 C₁ N (1 + log(KZ N + 2)) + 10125 N`. -/
lemma wzero_sum_le (Pa : Work.FITop.Params) (φ : ℝ) (hN2 : 2 ≤ Pa.N) {C₁ : ℝ}
    (hC₁ : ∀ (R : ℤ) (P : ℕ), 0 ≤ R → 1 ≤ P →
      (∑ d ∈ (Work.FIPlan.gBox R).filter (fun d => P < Work.FIPlan.gnorm d),
          ((Work.FIPlan.gnorm d : ℝ))⁻¹ ^ 2) ≤ C₁ / (P : ℝ) ∧
      (∑ d ∈ Work.FIPlan.gBox R, ((Work.FIPlan.gnorm d : ℝ))⁻¹)
          ≤ C₁ * (1 + Real.log ((R : ℝ) + 2))) :
    (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0 else 1))
      ≤ 900 * C₁ * Pa.N ^ 2 * ((Pa.Pz : ℝ)⁻¹)
        + 900 * C₁ * Pa.N * (1 + Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ))
        + 10125 * Pa.N := by
  have hPz1 : 1 ≤ Pa.Pz := by linarith [Pa.hP2]
  have hC₁R := hC₁ (KZ Pa.N) Pa.Pz (KZ_nonneg Pa.N) hPz1
  set S2 := ∑ π ∈ piSet Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2 with hS2def
  set S1 := ∑ π ∈ piSet Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ with hS1def
  have hS2 : S2 ≤ C₁ / (Pa.Pz : ℝ) := by
    rw [hS2def]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (piSet_subset_filter_gnorm Pa)
      (fun i _ _ => by positivity)) hC₁R.1
  have hS1 : S1 ≤ C₁ * (1 + Real.log (((KZ Pa.N : ℤ) : ℝ) + 2)) := by
    rw [hS1def]
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (by intro d hd; rw [mem_piSet] at hd; exact hd.1) (fun i _ _ => by positivity)) hC₁R.2
  have hcard : ((piSet Pa).card : ℝ) ≤ 45 * Pa.N := card_piSet_le Pa hN2
  calc (∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then (0 : ℝ) else 1))
      ≤ ∑ π ∈ piSet Pa, (((polarSupp Pa φ).filter (fun z => π ∣ z)).card : ℝ) ^ 2 :=
        wzero_union_bound Pa φ
    _ ≤ ∑ π ∈ piSet Pa, (15 * (2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1)) ^ 2 := by
        apply Finset.sum_le_sum; intro π hπ
        exact pow_le_pow_left₀ (by positivity) (pi_dvd_count_le Pa φ hπ) 2
    _ = 225 * (∑ π ∈ piSet Pa, (2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro π _; ring
    _ = 225 * (4 * Pa.N ^ 2 * S2 + 4 * Pa.N * S1 + ((piSet Pa).card : ℝ)) := by
        congr 1
        rw [hS2def, hS1def]
        have he : ∀ π : GaussianInt, (2 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1) ^ 2
            = 4 * Pa.N ^ 2 * (((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2)
              + 4 * Pa.N * ((Work.FIPlan.gnorm π : ℝ))⁻¹ + 1 := fun π => by ring
        simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
        simp [nsmul_eq_mul]
    _ ≤ 225 * (4 * Pa.N ^ 2 * (C₁ / (Pa.Pz : ℝ))
          + 4 * Pa.N * (C₁ * (1 + Real.log (((KZ Pa.N : ℤ) : ℝ) + 2)))
          + 45 * Pa.N) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h1 : 4 * Pa.N ^ 2 * S2 ≤ 4 * Pa.N ^ 2 * (C₁ / (Pa.Pz : ℝ)) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
        have h2 : 4 * Pa.N * S1 ≤ 4 * Pa.N * (C₁ * (1 + Real.log (((KZ Pa.N : ℤ) : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hS1 (by positivity)
        linarith [h1, h2, hcard]
    _ = 900 * C₁ * Pa.N ^ 2 * ((Pa.Pz : ℝ)⁻¹)
        + 900 * C₁ * Pa.N * (1 + Real.log (((KZ Pa.N : ℤ) + 2 : ℤ) : ℝ))
        + 10125 * Pa.N := by
        rw [div_eq_mul_inv]
        push_cast
        ring

/-! ## 8. The main estimate -/

attribute [local instance] Classical.propDecidable

/-- **The `w = 0` slice of the `Δ ≠ 0` non-coprime pairs.**

For every admissible set-up `Pa` and every `φ` with `2 ≤ N`, the number of pairs `(z₁,z₂)` of polar
box points (5.14) that are not coprime in `ℤ[i]` and have `Δ(z₁,z₂) ≠ 0` is at most
`C(M^{3/4}N^{3/4} + Pz^{-1}M^{1/2}N^{3/2})(log MN)^{516}`. -/
theorem offdiag_delta_ne_wzero_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ), 2 ≤ Pa.N →
      (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ, ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ,
        (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0 else 1))
        ≤ C * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := gnorm_inv_sums
  refine ⟨wzeroConstant C₁, wzeroConstant_pos hC₁pos, ?_⟩
  intro Pa φ hN2
  exact le_trans (wzero_sum_le Pa φ hN2 hC₁) (wzero_arith Pa hN2 hC₁pos)

end

end Work.FIArea1
