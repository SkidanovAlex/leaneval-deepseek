import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.Prop172Classical
import Submission.Work.FIArea7.prop172defs
import Submission.Work.FIArea7.gammaSwap
import Submission.Work.FIArea7.tauLeRpow
import Submission.Work.FIArea7.pairEllSum2Eps
import Submission.Work.FIArea7.smallCInner2Eps
import Submission.Work.FIArea7.rpowMulLeTwo
import Submission.Work.FIArea7.rpowMulLeGen
import Submission.Work.FIArea7.expSlack172
import Submission.Work.FIArea7.pairExp172
import Submission.Work.FIArea7.floorRpowHalfLe


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary consequences of the axioms of `Params`

The smoothing parameter `θ = (log x)^{-A'}` of (4.15) is at most `1` (so that the annulus
`N < u ≤ (1+θ)N` lies inside `|z|² ≤ 4N`), and the box radius `radN Pa = ⌈√(4N)⌉₊` dominates the
annulus. -/

lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hA'pos : 0 ≤ Pa.A' := by
    have h1 : (0 : ℝ) < 2 * Pa.A + 2 ^ (20 : ℕ) := by
      have := Pa.hA
      positivity
    linarith [Pa.hA']
  have hlog : 1 < Real.log (Pa.x : ℝ) := by
    have h1 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3)
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hlog) (by linarith)

lemma radN_nonneg (Pa : Work.FITop.Params) : (0 : ℤ) ≤ Work.FITop.radN Pa :=
  Int.natCast_nonneg _

lemma radN_natAbs (Pa : Work.FITop.Params) :
    (Work.FITop.radN Pa).natAbs = ⌈Real.sqrt (4 * Pa.N)⌉₊ := by
  rw [Work.FITop.radN, Int.natAbs_natCast]

/-- `radN Pa² ≥ 4N`: the outer box of `§5` contains the annulus `N < |z|² ≤ (1+θ)N`. -/
lemma fourN_le_radN_sq (Pa : Work.FITop.Params) :
    4 * (Pa.N : ℝ) ≤ ((Work.FITop.radN Pa).natAbs : ℝ) ^ 2 := by
  rw [radN_natAbs]
  have h1 : Real.sqrt (4 * Pa.N) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (0 : ℝ) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_nonneg _
  have h3 : Real.sqrt (4 * Pa.N) ^ 2 = 4 * Pa.N :=
    Real.sq_sqrt (by linarith [Pa.hN1] : (0 : ℝ) ≤ 4 * Pa.N)
  have := pow_le_pow_left₀ h2 h1 2
  rw [h3] at this
  exact this

/-- Membership in the box, in coordinates. -/
lemma mem_gBox_iff_coords {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re, z.im), ?_, by cases z; rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- `((R.natAbs : ℤ)) ^ 2 = R ^ 2`. -/
lemma natAbs_sq_cast (R : ℤ) : ((R.natAbs : ℤ)) ^ 2 = R ^ 2 := by
  rw [Int.natCast_natAbs, sq_abs]

/-- The norm of a member of the box `gBox R` is at most `2R²` (for `R ≥ 0`). -/
lemma gnorm_le_two_sq {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) : Work.FIPlan.gnorm z ≤ 2 * R.natAbs ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_gBox_iff_coords.mp hz
  have hcoords : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have hzre : z.re ^ 2 ≤ R ^ 2 := by nlinarith
  have hzim : z.im ^ 2 ≤ R ^ 2 := by nlinarith
  have h3' : (Work.FIPlan.gnorm z : ℤ) ≤ ((2 * R.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [hcoords]
    have hcast : ((2 * R.natAbs ^ 2 : ℕ) : ℤ) = 2 * R ^ 2 := by
      push_cast
      rw [sq_abs]
    rw [hcast]; nlinarith
  exact_mod_cast h3'

/-- A Gaussian integer of norm `n` lies in the box `gBox R` (for `R ≥ 0`) as soon as
`n ≤ R²`. -/
lemma mem_gBox_of_gnorm_eq' {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt} {n : ℕ}
    (hz : Work.FIPlan.gnorm z = n) (hn : (n : ℤ) ≤ R ^ 2) : z ∈ Work.FIPlan.gBox R := by
  rw [mem_gBox_iff_coords]
  have hcoords : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := norm_eq z
  have h1 : z.re ^ 2 ≤ R ^ 2 := by rw [hz] at hcoords; nlinarith
  have h2 : z.im ^ 2 ≤ R ^ 2 := by rw [hz] at hcoords; nlinarith
  have h3 : |z.re| ≤ |R| := sq_le_sq.mp h1
  have h4 : |z.im| ≤ |R| := sq_le_sq.mp h2
  rw [abs_of_nonneg hR] at h3 h4
  rw [abs_le] at h3 h4
  exact ⟨h3.1, h3.2, h4.1, h4.2⟩

/-- A Gaussian integer of norm `n ≥ 1` lies in `gBox n`. -/
lemma mem_gBox_of_gnorm_eq_nat {z : GaussianInt} {n : ℕ} (hn : 1 ≤ n)
    (hz : Work.FIPlan.gnorm z = n) : z ∈ Work.FIPlan.gBox (n : ℤ) := by
  refine mem_gBox_of_gnorm_eq' (by positivity) hz ?_
  have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  nlinarith

/-- `gnorm` of a non-zero Gaussian integer is at least one. -/
lemma one_le_gnorm_of_ne_zero {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ Work.FIPlan.gnorm z :=
  Nat.one_le_iff_ne_zero.mpr (fun h => hz (gnorm_eq_zero_iff.mp h))

lemma grossenChar_eq_uniPow (chi : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) :
    grossenChar chi k z = chi z * uniPow z k := rfl

/-- The summand of `SChiRad`, with `radBeta` unfolded. -/
lemma radBeta_mul_eq (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ) (chi : GaussianInt → ℂ)
    (m : ℤ) (z : GaussianInt) :
    radBeta Pa P Cc z * JKSym z * chi z * uniPow z m =
      (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
        (((P (Work.FIPlan.gnorm z) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
          * Work.FIPlan.gammaTrunc Cc (Work.FIPlan.gnorm z) : ℝ)) : ℂ)
          * (grossenChar chi m z * JKSym z) else 0) := by
  rw [grossenChar_eq_uniPow]
  unfold radBeta
  split
  · push_cast
    ring
  · simp

/-- On a fibre of `gnorm`, `NoSmallPrimes` is constant. -/
lemma noSmallPrimesNat_gnorm (Pa : Work.FITop.Params) {z : GaussianInt} {n : ℕ}
    (hz : Work.FIPlan.gnorm z = n) :
    Work.FITop4.NoSmallPrimes Pa z ↔ NoSmallPrimesNat Pa n := by
  subst hz
  exact Iff.rfl

/-- The fibre of the box over a norm: for `1 ≤ n` and `n ≤ radN Pa²`, the primary points of
`gBox (radN Pa)` of norm `n` are exactly the primary points of `gBox n` of norm `n`. -/
lemma filter_gnorm_eq (Pa : Work.FITop.Params) {n : ℕ} (hn : 1 ≤ n)
    (hnR : (n : ℤ) ≤ Work.FITop.radN Pa ^ 2) :
    (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
        (fun z => Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z)
      = (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z => Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z) := by
  ext z
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mem_gBox_of_gnorm_eq_nat hn h2.1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_gBox_of_gnorm_eq' (radN_nonneg Pa) h2.1 hnR, h2⟩

/-- Removing `0` from the box does not change a fibre over `n ≥ 1`. -/
lemma filter_erase_gnorm (Pa : Work.FITop.Params) {n : ℕ} (hn : 1 ≤ n) :
    ((Work.FIPlan.gBox (Work.FITop.radN Pa)).erase 0).filter
        (fun z => Work.FIPlan.gnorm z = n)
      = (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
        (fun z => Work.FIPlan.gnorm z = n) := by
  rw [Finset.filter_erase]
  refine Finset.erase_eq_of_notMem ?_
  intro h
  rw [Finset.mem_filter] at h
  have h0 : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
    simp [Work.FIPlan.gnorm]
  rw [h.2] at h0
  omega

/-- **(*FI* 25.1), fibre form**: the contribution of the primary `z` of norm `n` to `SChiRad` is
`[n free of small primes] · P(n) μ(n) γ(n;C) · λ(n)`. -/
lemma fiber_gnorm_sum_eq (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ)
    (chi : GaussianInt → ℂ) (m : ℤ)
    (hPsupp : ∀ u, P u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2 * (Work.FITop.radN Pa).natAbs ^ 2) :
    (∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Work.FIPlan.gnorm z = n),
        radBeta Pa P Cc z * JKSym z * chi z * uniPow z m)
      = (if NoSmallPrimesNat Pa n
          then (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
            * quadEigen (grossenChar chi m) n
          else 0) := by
  classical
  rw [Finset.sum_filter]
  have hstep : ∀ z : GaussianInt,
      (if Work.FIPlan.gnorm z = n then
          radBeta Pa P Cc z * JKSym z * chi z * uniPow z m else 0)
      = (if Work.FIPlan.gnorm z = n then
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
            (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
              * (grossenChar chi m z * JKSym z) else 0) else 0) := by
    intro z
    by_cases hz : Work.FIPlan.gnorm z = n
    · rw [if_pos hz, radBeta_mul_eq Pa P Cc chi m z, hz, if_pos rfl]
    · rw [if_neg hz, if_neg hz]
  rw [Finset.sum_congr rfl (fun z _ => hstep z)]
  by_cases hNn : NoSmallPrimesNat Pa n
  · have hstep2 : ∀ z : GaussianInt,
        (if Work.FIPlan.gnorm z = n then
            (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
              (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
                * (grossenChar chi m z * JKSym z) else 0) else 0)
        = (if Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z then
            (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
              * (grossenChar chi m z * JKSym z) else 0) := by
      intro z
      by_cases hz : Work.FIPlan.gnorm z = n
      · by_cases hA : Work.FIPlan.IsPrimary z
        · have hNz : Work.FITop4.NoSmallPrimes Pa z := (noSmallPrimesNat_gnorm Pa hz).mpr hNn
          rw [if_pos hz, if_pos ⟨hA, hNz⟩, if_pos ⟨hz, hA⟩]
        · rw [if_pos hz, if_neg (fun h => hA h.1), if_neg (fun h => hA h.2)]
      · rw [if_neg hz, if_neg (by tauto : ¬ (Work.FIPlan.gnorm z = n ∧ Work.FIPlan.IsPrimary z))]
    rw [Finset.sum_congr rfl (fun z _ => hstep2 z), ← Finset.sum_filter, ← Finset.mul_sum,
      if_pos hNn]
    by_cases hc0 : P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n = 0
    · have hc : (((P n * (ArithmeticFunction.moebius n : ℝ)
          * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ) = 0 := by
        rw [hc0]; norm_num
      rw [hc, zero_mul, zero_mul]
    · have hn0 : P n ≠ 0 := fun h => hc0 (by rw [h]; ring)
      obtain ⟨-, hNle⟩ := hPsupp n hn0
      have hnt : (n : ℤ) ≤ Work.FITop.radN Pa ^ 2 := by
        have hle : (n : ℝ) ≤ ((Work.FITop.radN Pa).natAbs : ℝ) ^ 2 := by
          refine le_trans ?_ (fourN_le_radN_sq Pa)
          have hθ : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [theta_le_one Pa, Pa.hN1]
          linarith
        rw [radN_natAbs] at hle
        rw [Work.FITop.radN]
        exact_mod_cast hle
      congr 1
      rw [quadEigen_eq_sum, ← filter_gnorm_eq Pa hn1 hnt]
  · have hstep2 : ∀ z : GaussianInt,
        (if Work.FIPlan.gnorm z = n then
            (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
              (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
                * (grossenChar chi m z * JKSym z) else 0) else 0) = 0 := by
      intro z
      by_cases hz : Work.FIPlan.gnorm z = n
      · rw [if_pos hz, if_neg (by
          intro hc
          exact hNn ((noSmallPrimesNat_gnorm Pa hz).mp hc.2))]
      · rw [if_neg hz]
    rw [Finset.sum_congr rfl (fun z _ => hstep2 z), Finset.sum_const_zero, if_neg hNn]

/-- **(*FI* 25.1)**: the sum `S^m_χ(β')` of (17.14), grouped by `n = |z|²`, is
`Σ_{(n,Π)=1} P(n) μ(n) γ(n;C) λ(n)`. -/
theorem SChiRad_eq_sum_quadEigen (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ)
    (chi : GaussianInt → ℂ) (m : ℤ)
    (hPsupp : ∀ u, P u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    SChiRad Pa P Cc chi m
      = ∑ n ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
          (if NoSmallPrimesNat Pa n
            then (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
              * quadEigen (grossenChar chi m) n
            else 0) := by
  classical
  have hR0 : (0 : ℤ) ≤ Work.FITop.radN Pa := radN_nonneg Pa
  have hzero : radBeta Pa P Cc 0 * JKSym 0 * chi 0 * uniPow 0 m = 0 := by
    have h : ¬ Work.FIPlan.IsPrimary (0 : GaussianInt) := by
      intro hc
      obtain ⟨k, hk⟩ := hc.1
      have hk' : (0 : ℤ) = 2 * k + 1 := by simpa using hk
      omega
    simp [radBeta, h]
  have h0mem : (0 : GaussianInt) ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) := by
    rw [mem_gBox_iff_coords]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> linarith
  have herase : SChiRad Pa P Cc chi m
      = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).erase 0,
          radBeta Pa P Cc z * JKSym z * chi z * uniPow z m := by
    rw [SChiRad]
    rw [← Finset.sum_erase_add (s := Work.FIPlan.gBox (Work.FITop.radN Pa))
      (f := fun z => radBeta Pa P Cc z * JKSym z * chi z * uniPow z m) (a := 0) h0mem,
      hzero, add_zero]
  rw [herase]
  have hmap : ∀ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).erase 0,
      Work.FIPlan.gnorm z ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2) := by
    intro z hz
    rw [Finset.mem_erase] at hz
    rw [Finset.mem_Icc]
    exact ⟨one_le_gnorm_of_ne_zero hz.1, gnorm_le_two_sq hR0 hz.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun z => radBeta Pa P Cc z * JKSym z * chi z * uniPow z m)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_Icc] at hn
  rw [filter_erase_gnorm Pa hn.1]
  exact fiber_gnorm_sum_eq Pa P Cc chi m hPsupp hn.1 hn.2

/-- **Absorption of polylogarithms.**  For every `A ≥ 0` and `δ > 0` there is `N₀` with
`(log N)^A ≤ N^δ` for all `N ≥ N₀` — this is how the polylogarithmic losses of the estimates of
§25 are absorbed into the saving `N^{-δ₁}` by taking `x₀` (hence `N`) large. -/
theorem log_pow_le_rpow (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (Real.log (N : ℝ)) ^ A ≤ (N : ℝ) ^ δ := by
  refine ⟨⌈Real.exp ((2 * A / δ + 1) ^ 2)⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℕ) ≤ N := by
      have h0 : (0 : ℕ) ≤ ⌈Real.exp ((2 * A / δ + 1) ^ 2)⌉₊ := Nat.zero_le _
      omega
    exact_mod_cast h1
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hlogN : (2 * A / δ + 1) ^ 2 ≤ Real.log (N : ℝ) := by
    have h1 : Real.exp ((2 * A / δ + 1) ^ 2) ≤ (N : ℝ) := by
      have hc : Real.exp ((2 * A / δ + 1) ^ 2)
          ≤ ((⌈Real.exp ((2 * A / δ + 1) ^ 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp ((2 * A / δ + 1) ^ 2)⌉₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast hN
      linarith
    have h2 : Real.log (Real.exp ((2 * A / δ + 1) ^ 2)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hlogpos : 0 < Real.log (N : ℝ) := by
    have h0 : (0 : ℝ) < 2 * A / δ + 1 := by
      have h1 := hA
      have h2 := hδ
      positivity
    have h1 : (0 : ℝ) < (2 * A / δ + 1) ^ 2 := sq_pos_of_pos h0
    linarith
  have h3 : Real.log (Real.log (N : ℝ)) ≤ 2 * Real.sqrt (Real.log (N : ℝ)) := by
    have h := Real.log_le_rpow_div hlogpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    have hsq : (Real.log (N : ℝ)) ^ ((1 : ℝ) / 2) = Real.sqrt (Real.log (N : ℝ)) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsq] at h
    have h2 : Real.sqrt (Real.log (N : ℝ)) / (1 / 2) = 2 * Real.sqrt (Real.log (N : ℝ)) := by
      ring
    linarith [h, h2 ▸ h]
  have h4 : A * Real.log (Real.log (N : ℝ)) ≤ δ * Real.log (N : ℝ) := by
    have h5 : (2 * A / δ + 1) ≤ Real.sqrt (Real.log (N : ℝ)) := Real.le_sqrt_of_sq_le hlogN
    have h6 : (2 * A / δ) * δ ≤ Real.sqrt (Real.log (N : ℝ)) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have h7 : (2 * A / δ) * δ = 2 * A := by field_simp
    rw [h7] at h6
    have h8 : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ))
        = Real.log (N : ℝ) := Real.mul_self_sqrt hlogpos.le
    nlinarith [h3, hA, h6, h8, hδ, Real.sqrt_nonneg (Real.log (N : ℝ))]
  calc (Real.log (N : ℝ)) ^ A
      = Real.exp (A * Real.log (Real.log (N : ℝ))) := by
        rw [Real.rpow_def_of_pos hlogpos, mul_comm]
    _ ≤ Real.exp (δ * Real.log (N : ℝ)) := Real.exp_le_exp.mpr h4
    _ = (N : ℝ) ^ δ := by rw [Real.rpow_def_of_pos hNpos, mul_comm]

/-- The `j = 1` case of the derivative hypothesis of *FI* (4.14): `|P'| ≤ cMoll 1 (θN)^{-1}`. -/
lemma deriv_bound_of_iteratedDeriv (Pa : Work.FITop.Params) {P : ℝ → ℝ}
    (hder : ∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
      |iteratedDeriv j P u| ≤ Work.FITop4.cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) :
    ∀ u : ℝ, |deriv P u| ≤ Work.FITop4.cMoll 1 * (Pa.θ * Pa.N) ^ (-(1 : ℝ)) := by
  intro u
  have h := hder 1 (by norm_num) u
  rwa [show ((1 : ℕ) : ℝ) = 1 by norm_num, iteratedDeriv_one] at h

/-- **The total-variation factor** entering every estimate of §25 is bounded by the constant
`cMoll 1 + 1 = 1025`: with `K = cMoll 1 (θN)^{-1}` and the support `(a,b] ⊆ (N,(1+θ)N]` one has
`K|b-a| + 1 ≤ cMoll 1 + 1`. -/
lemma tv_factor_le (Pa : Work.FITop.Params) {a b K : ℝ}
    (hK : K = Work.FITop4.cMoll 1 * (Pa.θ * Pa.N) ^ (-(1 : ℝ)))
    (ha : Pa.N ≤ a) (hb : b ≤ (1 + Pa.θ) * Pa.N) (hba : a ≤ b) :
    K * |b - a| + 1 ≤ Work.FITop4.cMoll 1 + 1 := by
  have hθ := Pa.hθ0
  have hN : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hpos : 0 < Pa.θ * Pa.N := mul_pos hθ hN
  have h1 : (Pa.θ * Pa.N) ^ (-(1 : ℝ)) = (Pa.θ * Pa.N)⁻¹ := by
    rw [Real.rpow_neg_one]
  have hK' : K = Work.FITop4.cMoll 1 / (Pa.θ * Pa.N) := by
    rw [hK, h1, div_eq_mul_inv]
  have hcm : 0 < Work.FITop4.cMoll 1 := Work.FITop4.cMoll_pos 1
  have h2 : |b - a| ≤ Pa.θ * Pa.N := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith [hb, ha, hba]
  have h3 : K * |b - a| ≤ Work.FITop4.cMoll 1 := by
    rw [hK']
    have h4 : Work.FITop4.cMoll 1 / (Pa.θ * Pa.N) * |b - a|
        ≤ Work.FITop4.cMoll 1 / (Pa.θ * Pa.N) * (Pa.θ * Pa.N) := by
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rwa [div_mul_cancel₀ _ hpos.ne'] at h4
  linarith

/-- **(25.1) + (25.2): the *FI* §25 reduction of `SChiRad` to the double sum over `(c,ℓ)`.**
Uses the Möbius exchange `Work.FIArea7.gammaSwap`. -/
theorem SChiRad_eq_doubleSum
    (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ) (chi : GaussianInt → ℂ) (m : ℤ)
    (hCc1 : 1 ≤ Cc)
    (hPsupp : ∀ u, P u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    SChiRad Pa P Cc chi m
      = ∑ c ∈ (Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2)).filter
            (fun c : ℕ => (c : ℝ) ≤ Cc),
          (ArithmeticFunction.moebius c : ℂ) ^ 2 * nspInd Pa c *
            ∑ ℓ ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
              (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
                * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
                * quadEigen (grossenChar chi m) (c * ℓ) else 0) := by
  classical
  have hTa : 2 ≤ (Work.FITop.radN Pa).natAbs := by
    have h4 := fourN_le_radN_sq Pa
    have hN1 := Pa.hN1
    have : (2 : ℝ) ≤ ((Work.FITop.radN Pa).natAbs : ℝ) := by nlinarith
    exact_mod_cast this
  have hT1 : 1 ≤ 2 * (Work.FITop.radN Pa).natAbs ^ 2 := by nlinarith [hTa]
  rw [SChiRad_eq_sum_quadEigen Pa P Cc chi m hPsupp]
  have h1 : ∀ n : ℕ,
      (if NoSmallPrimesNat Pa n then
        (((P n * (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Cc n) : ℝ) : ℂ)
          * quadEigen (grossenChar chi m) n else 0)
      = (nspInd Pa n * (P n : ℂ)) * (ArithmeticFunction.moebius n : ℂ)
          * ((Work.FIPlan.gammaTrunc Cc n : ℝ) : ℂ) * quadEigen (grossenChar chi m) n := by
    intro n
    by_cases hn : NoSmallPrimesNat Pa n
    · rw [if_pos hn]
      unfold nspInd
      rw [if_pos hn]
      push_cast
      ring
    · rw [if_neg hn]
      unfold nspInd
      rw [if_neg hn]
      ring
  rw [Finset.sum_congr rfl (fun n _ => h1 n)]
  have hw : ∀ n : ℕ, 2 * (Work.FITop.radN Pa).natAbs ^ 2 < n →
      (nspInd Pa n * (P n : ℂ)) = 0 := by
    intro n hn
    have hPn : P n = 0 := by
      by_contra hne
      obtain ⟨-, hle⟩ := hPsupp n hne
      have hθ := theta_le_one Pa
      have hN1 := Pa.hN1
      have h4 := fourN_le_radN_sq Pa
      have hTN : (1 + Pa.θ) * Pa.N ≤ ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      have hn' : ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) < (n : ℝ) := by
        exact_mod_cast hn
      linarith
    rw [hPn, Complex.ofReal_zero, mul_zero]
  rw [gammaSwap (fun n => nspInd Pa n * (P n : ℂ)) Cc (2 * (Work.FITop.radN Pa).natAbs ^ 2)
        (fun n => quadEigen (grossenChar chi m) n) hCc1 hT1 hw]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hinner : (∑ ℓ ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
        (if Nat.Coprime c ℓ then (ArithmeticFunction.moebius ℓ : ℂ)
          * (nspInd Pa (c * ℓ) * ((P (((c * ℓ : ℕ)) : ℝ)) : ℂ))
          * quadEigen (grossenChar chi m) (c * ℓ) else 0))
      = nspInd Pa c * ∑ ℓ ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
          (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
            * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
            * quadEigen (grossenChar chi m) (c * ℓ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    by_cases hcop : Nat.Coprime c ℓ
    · rw [if_pos hcop, if_pos hcop, nspInd_mul Pa hcop]
      push_cast
      ring
    · rw [if_neg hcop, if_neg hcop, mul_zero]
  rw [hinner]
  ring


/-! ## Assembly helpers for the *FI* §25 reduction

The pieces below turn the double sum of `SChiRad_eq_doubleSum` into a sum over the two ranges
`c ≤ Zc` (handled by `smallCInner2` at each `c`, see `PROP172_PLAN.md`) and `Zc < c ≤ Cmax`
(handled by `pairEllSum2`), and then absorb the resulting polylogarithmic losses into the saving
`N^{-δ₁}`. -/

/-- The `c`-range of the double sum: `1 ≤ c ≤ A` together with `(c : ℝ) ≤ Cc` is
`Icc 1 (min A ⌊Cc⌋₊)`. -/
lemma filter_Icc_le_floor (A : ℕ) {Cc : ℝ} (hCc : 0 ≤ Cc) :
    (Finset.Icc 1 A).filter (fun c : ℕ => (c : ℝ) ≤ Cc) = Finset.Icc 1 (min A ⌊Cc⌋₊) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, le_min h2 (Nat.le_floor h3)⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, le_trans h3 (min_le_left _ _)⟩, ?_⟩
    have h4 : (c : ℝ) ≤ ((⌊Cc⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast le_trans h3 (min_le_right _ _)
    exact le_trans h4 (Nat.floor_le hCc)

/-- Splitting `Icc 1 Cmax` at `Zc ≤ Cmax`. -/
lemma sum_Icc_split (Zc Cmax : ℕ) (h : Zc ≤ Cmax) (f : ℕ → ℂ) :
    ∑ c ∈ Finset.Icc 1 Cmax, f c
      = (∑ c ∈ Finset.Icc 1 Zc, f c)
        + ∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), f c := by
  have hset : (Finset.Icc 1 Cmax).filter (fun c : ℕ => ¬ Zc < c) = Finset.Icc 1 Zc := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h4⟩; exact ⟨⟨h1, le_trans h4 h⟩, h4⟩
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Cmax) (fun c => Zc < c) f, hset,
    add_comm]

/-- A sum over `Icc 1 A` equals the sum over `Icc 1 T` when the summand vanishes above `T`. -/
lemma sum_Icc_of_vanishing (A T : ℕ) (hT : T ≤ A) (g : ℕ → ℂ) (h0 : ∀ ℓ, T < ℓ → g ℓ = 0) :
    ∑ ℓ ∈ Finset.Icc 1 A, g ℓ = ∑ ℓ ∈ Finset.Icc 1 T, g ℓ := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hT⟩
  · intro x hx hxT
    simp only [Finset.mem_Icc] at hx hxT
    rcases not_and_or.mp hxT with h | h
    · omega
    · exact h0 x (not_le.mp h)

/-- `Σ_{c ≤ Z} c^s ≤ Z^{s+1}` for `s ≥ 0` — the trivial bound (each of the `Z` terms is `≤ Z^s`). -/
lemma sum_Icc_rpow_le_of_nonneg (Z : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ s ≤ (Z : ℝ) ^ (s + 1) := by
  rcases Nat.eq_zero_or_pos Z with hZ | hZ
  · subst hZ
    simp [Real.zero_rpow (by linarith : s + 1 ≠ 0)]
  calc ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ s
      ≤ ∑ c ∈ Finset.Icc 1 Z, (Z : ℝ) ^ s := by
        apply Finset.sum_le_sum
        intro c hc
        rw [Finset.mem_Icc] at hc
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hc.2) hs
    _ = ((Finset.Icc 1 Z).card : ℝ) * (Z : ℝ) ^ s := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Z : ℝ) * (Z : ℝ) ^ s := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        have hcard : (Finset.Icc 1 Z).card ≤ Z := by
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcard
    _ = (Z : ℝ) ^ (s + 1) := by
        rw [Real.rpow_add_one (by positivity : (Z : ℝ) ≠ 0), mul_comm]

/-- `Σ_{c ≤ Z} c^s ≤ Z` for `s ≤ 0` — each term is at most `1`. -/
lemma sum_Icc_rpow_le_of_nonpos (Z : ℕ) {s : ℝ} (hs : s ≤ 0) :
    ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ s ≤ (Z : ℝ) := by
  calc ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ s
      ≤ ∑ _c ∈ Finset.Icc 1 Z, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [Finset.mem_Icc] at hc
        have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.1
        simpa using Real.rpow_le_one_of_one_le_of_nonpos h1 hs
    _ = ((Finset.Icc 1 Z).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (Z : ℝ) := by
        have hcard : (Finset.Icc 1 Z).card ≤ Z := by
          rw [Nat.card_Icc]; omega
        exact_mod_cast hcard

/-- **The divisor function is bounded by a constant times any fixed positive power of `n`.**
This is the form of `tauLeRpow` needed to absorb the `τ(c d)` factors of the estimates of §25
(`d ≤ N^{δ₁}` and `c ≤ N^{η''}`). -/
lemma tau_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨n₀, h₀⟩ := tauLeRpow ε hε
  refine ⟨(∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ) := by positivity
    linarith
  · intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
    have hCle : (1 : ℝ) ≤ (∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1 := by
      have h : (0 : ℝ) ≤ ∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ) := by positivity
      linarith
    by_cases hn₀ : n₀ ≤ n
    · have h1 := h₀ n hn₀
      calc ((n.divisors.card : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := h1
        _ = 1 * (n : ℝ) ^ ε := (one_mul _).symm
        _ ≤ ((∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1) * (n : ℝ) ^ ε :=
            mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by positivity) _)
    · have hmem : n ∈ Finset.Icc 1 n₀ := Finset.mem_Icc.mpr ⟨hn, by omega⟩
      have h1 : ((n.divisors.card : ℕ) : ℝ)
          ≤ ∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ) :=
        Finset.single_le_sum (f := fun i => ((i.divisors.card : ℕ) : ℝ))
          (fun i _ => by positivity) hmem
      have h2 : (∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1
          ≤ ((∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1) * (n : ℝ) ^ ε := by
        calc (∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1
            = ((∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1) * 1 :=
              (mul_one _).symm
          _ ≤ ((∑ i ∈ Finset.Icc 1 n₀, ((i.divisors.card : ℕ) : ℝ)) + 1) * (n : ℝ) ^ ε :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
      linarith

/-- **Absorption of a polylogarithmic factor.**  For any `C > 0`, any real `A` and any `ν > 0`
there is `x₀ ≥ 1` with `C (log(M+2))^A ≤ M^ν` for all `M ≥ x₀`.  This is the only place where the
polylogarithmic losses of the estimates of §25 are paid for, by taking `x₀` (hence `N`) large. -/
lemma absorb_log (C A ν : ℝ) (hC : 0 < C) (hν : 0 < ν) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ M : ℕ, x₀ ≤ (M : ℝ) →
      C * (Real.log ((M : ℝ) + 2)) ^ A ≤ (M : ℝ) ^ ν := by
  obtain ⟨N₀, hN₀⟩ := log_pow_le_rpow (max A 0) (ν / 2) (le_max_right _ _) (by positivity)
  refine ⟨(N₀ : ℝ) + C ^ (1 / ν) + (C * 2 ^ (ν / 2)) ^ (2 / ν) + 4, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (N₀ : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ C ^ (1 / ν) := Real.rpow_nonneg hC.le _
    have h3 : (0 : ℝ) ≤ (C * 2 ^ (ν / 2)) ^ (2 / ν) := by positivity
    linarith
  · intro M hM
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by
      have h1 : (0 : ℝ) ≤ (N₀ : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ C ^ (1 / ν) := Real.rpow_nonneg hC.le _
      have h3 : (0 : ℝ) ≤ (C * 2 ^ (ν / 2)) ^ (2 / ν) := by positivity
      linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
    have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log ((M : ℝ) + 2) := by
      have h1 : Real.log 3 ≤ Real.log ((M : ℝ) + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h2 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        exact Real.exp_one_lt_three
      linarith
    have hClog : C ≤ (M : ℝ) ^ ν := by
      have h1 : C ^ (1 / ν) ≤ (M : ℝ) := by
        have h0 : (0 : ℝ) ≤ (N₀ : ℝ) + (C * 2 ^ (ν / 2)) ^ (2 / ν) + 4 := by positivity
        linarith [h0]
      calc C = (C ^ (1 / ν)) ^ ν := by
              rw [← Real.rpow_mul hC.le, show (1 / ν) * ν = 1 by field_simp, Real.rpow_one]
        _ ≤ (M : ℝ) ^ ν := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) h1 hν.le
    by_cases hA : A ≤ 0
    · have h3 : (Real.log ((M : ℝ) + 2)) ^ A ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlog1 hA
      calc C * (Real.log ((M : ℝ) + 2)) ^ A ≤ C * 1 :=
            mul_le_mul_of_nonneg_left h3 hC.le
        _ = C := by ring
        _ ≤ (M : ℝ) ^ ν := hClog
    · push_neg at hA
      have h30 : (Real.log ((M : ℝ) + 2)) ^ A ≤ (Real.log ((M : ℝ) + 2)) ^ (max A 0) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left A 0)
      have h31 : (Real.log ((M : ℝ) + 2)) ^ (max A 0) ≤ ((M : ℝ) + 2) ^ (ν / 2) := by
        have h6 : (N₀ : ℕ) ≤ M + 2 := by
          have h5 : (N₀ : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by
            push_cast
            have h7 : (0 : ℝ) ≤ C ^ (1 / ν) := Real.rpow_nonneg hC.le _
            have h8 : (0 : ℝ) ≤ (C * 2 ^ (ν / 2)) ^ (2 / ν) := by positivity
            linarith
          exact_mod_cast h5
        simpa using hN₀ (M + 2) h6
      have h32 : ((M : ℝ) + 2) ^ (ν / 2) ≤ (2 * (M : ℝ)) ^ (ν / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      have h33 : (2 * (M : ℝ)) ^ (ν / 2) = (2 : ℝ) ^ (ν / 2) * (M : ℝ) ^ (ν / 2) :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMpos.le
      have h8 : C * (2 : ℝ) ^ (ν / 2) ≤ (M : ℝ) ^ (ν / 2) := by
        have h9 : (C * (2 : ℝ) ^ (ν / 2)) ^ (2 / ν) ≤ (M : ℝ) := by
          have h0 : (0 : ℝ) ≤ (N₀ : ℝ) + C ^ (1 / ν) + 4 := by positivity
          linarith
        calc C * (2 : ℝ) ^ (ν / 2) = ((C * (2 : ℝ) ^ (ν / 2)) ^ (2 / ν)) ^ (ν / 2) := by
              rw [← Real.rpow_mul (show (0 : ℝ) ≤ C * 2 ^ (ν / 2) by positivity),
                show (2 / ν) * (ν / 2) = 1 by field_simp, Real.rpow_one]
          _ ≤ (M : ℝ) ^ (ν / 2) := Real.rpow_le_rpow (by positivity) h9 (by positivity)
      have h7 : C * ((2 : ℝ) ^ (ν / 2) * (M : ℝ) ^ (ν / 2)) ≤ (M : ℝ) ^ ν := by
        calc C * ((2 : ℝ) ^ (ν / 2) * (M : ℝ) ^ (ν / 2))
            = (C * (2 : ℝ) ^ (ν / 2)) * (M : ℝ) ^ (ν / 2) := by ring
          _ ≤ (M : ℝ) ^ (ν / 2) * (M : ℝ) ^ (ν / 2) :=
              mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hMpos.le _)
          _ = (M : ℝ) ^ (ν / 2 + ν / 2) := (Real.rpow_add hMpos _ _).symm
          _ = (M : ℝ) ^ ν := by congr 1; ring
      calc C * (Real.log ((M : ℝ) + 2)) ^ A
          ≤ C * (Real.log ((M : ℝ) + 2)) ^ (max A 0) :=
            mul_le_mul_of_nonneg_left h30 hC.le
        _ ≤ C * ((M : ℝ) + 2) ^ (ν / 2) := mul_le_mul_of_nonneg_left h31 hC.le
        _ ≤ C * (2 * (M : ℝ)) ^ (ν / 2) := mul_le_mul_of_nonneg_left h32 hC.le
        _ = C * ((2 : ℝ) ^ (ν / 2) * (M : ℝ) ^ (ν / 2)) := by rw [h33]
        _ ≤ (M : ℝ) ^ ν := h7

/-- **The final arithmetic step of §25**: a bound of the shape
`C (log(M+2))^A M^{1-ν+t}` with `δ + t < ν` is `≤ M^{1-δ}` for `M ≥ x₀`. -/
lemma absorb_final (C A ν δ t : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hνt : δ + t < ν) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ M : ℕ, x₀ ≤ (M : ℝ) →
      C * (Real.log ((M : ℝ) + 2)) ^ A * (M : ℝ) ^ (1 - ν + t) ≤ (M : ℝ) ^ (1 - δ) := by
  have hνδt : 0 < ν - δ - t := by linarith
  obtain ⟨x₀, hx₀, hb⟩ := absorb_log C A (ν - δ - t) hC hνδt
  refine ⟨max x₀ 1, le_max_right _ _, ?_⟩
  intro M hM
  have h1 : x₀ ≤ (M : ℝ) := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have h := hb M h1
  calc C * (Real.log ((M : ℝ) + 2)) ^ A * (M : ℝ) ^ (1 - ν + t)
      = (C * (Real.log ((M : ℝ) + 2)) ^ A) * (M : ℝ) ^ (1 - ν + t) := by ring
    _ ≤ (M : ℝ) ^ (ν - δ - t) * (M : ℝ) ^ (1 - ν + t) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hMpos.le _)
    _ = (M : ℝ) ^ ((ν - δ - t) + (1 - ν + t)) := (Real.rpow_add hMpos _ _).symm
    _ = (M : ℝ) ^ (1 - δ) := by congr 1; ring

/-- **(25.1) + (25.2) with the `c`-range written as `Icc 1 Cmax`** (`Cmax = min box ⌊C⌋₊`): the
sum `SChiRad` is a sum over `c ≤ Cmax` of `μ(c)² (c,Π)-indicator` times the inner `ℓ`-sum. -/
lemma SChiRad_eq_sum_Cmax (Pa : Work.FITop.Params) (P : ℝ → ℝ) (Cc : ℝ)
    (chi : GaussianInt → ℂ) (m : ℤ) (hCc1 : 1 ≤ Cc)
    (hPsupp : ∀ u, P u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    SChiRad Pa P Cc chi m
      = ∑ c ∈ Finset.Icc 1 (min (2 * (Work.FITop.radN Pa).natAbs ^ 2) ⌊Cc⌋₊),
          (ArithmeticFunction.moebius c : ℂ) ^ 2 * nspInd Pa c *
            ∑ ℓ ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2),
              (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
                * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
                * quadEigen (grossenChar chi m) (c * ℓ) else 0) := by
  rw [SChiRad_eq_doubleSum Pa P Cc chi m hCc1 hPsupp,
    ← filter_Icc_le_floor (2 * (Work.FITop.radN Pa).natAbs ^ 2) (le_trans zero_le_one hCc1)]

/-- `Σ_{c ≤ Z} c·τ(c d) ≤ C d^δ Z^{2+δ}` when `τ(c d) ≤ C (c d)^δ`. -/
lemma sum_c_mul_tau_le (Z dd : ℕ) {δ Ct : ℝ} (hδ : 0 ≤ δ) (hCt : 0 < Ct)
    (hτ : ∀ c : ℕ, 1 ≤ c →
      ((c * dd).divisors.card : ℝ) ≤ Ct * ((c : ℝ) * (dd : ℝ)) ^ δ) :
    ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) * ((c * dd).divisors.card : ℝ)
      ≤ Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (2 + δ) := by
  have hpt : ∀ c ∈ Finset.Icc 1 Z, (c : ℝ) * ((c * dd).divisors.card : ℝ)
      ≤ Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ (1 + δ) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have h1 := hτ c hc.1
    have h2 : ((c : ℝ) * (dd : ℝ)) ^ δ = (c : ℝ) ^ δ * (dd : ℝ) ^ δ :=
      Real.mul_rpow (by positivity) (by positivity)
    calc (c : ℝ) * ((c * dd).divisors.card : ℝ)
        ≤ (c : ℝ) * (Ct * ((c : ℝ) * (dd : ℝ)) ^ δ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ (1 + δ) := by
          rw [h2]
          have h3 : (c : ℝ) * (Ct * ((c : ℝ) ^ δ * (dd : ℝ) ^ δ))
              = Ct * (dd : ℝ) ^ δ * ((c : ℝ) ^ (1 : ℝ) * (c : ℝ) ^ δ) := by
            rw [Real.rpow_one]; ring
          rw [h3, ← Real.rpow_add hcpos]
  calc ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) * ((c * dd).divisors.card : ℝ)
      ≤ ∑ c ∈ Finset.Icc 1 Z, Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ (1 + δ) :=
        Finset.sum_le_sum hpt
    _ = Ct * (dd : ℝ) ^ δ * ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ (1 + δ) := by
        rw [Finset.mul_sum]
    _ ≤ Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (1 + δ + 1) := by
        apply mul_le_mul_of_nonneg_left (sum_Icc_rpow_le_of_nonneg Z (by linarith))
        positivity
    _ = Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (2 + δ) := by
        congr 2
        ring

/-- `Σ_{c ≤ Z} τ(c d) ≤ C d^δ Z^{1+δ}` when `τ(c d) ≤ C (c d)^δ`. -/
lemma sum_tau_le (Z dd : ℕ) {δ Ct : ℝ} (hδ : 0 ≤ δ) (hCt : 0 < Ct)
    (hτ : ∀ c : ℕ, 1 ≤ c →
      ((c * dd).divisors.card : ℝ) ≤ Ct * ((c : ℝ) * (dd : ℝ)) ^ δ) :
    ∑ c ∈ Finset.Icc 1 Z, ((c * dd).divisors.card : ℝ)
      ≤ Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (1 + δ) := by
  have hpt : ∀ c ∈ Finset.Icc 1 Z, ((c * dd).divisors.card : ℝ)
      ≤ Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ δ := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have h1 := hτ c hc.1
    have h2 : ((c : ℝ) * (dd : ℝ)) ^ δ = (c : ℝ) ^ δ * (dd : ℝ) ^ δ :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [h2] at h1
    calc ((c * dd).divisors.card : ℝ) ≤ Ct * ((c : ℝ) ^ δ * (dd : ℝ) ^ δ) := h1
      _ = Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ δ := by ring
  calc ∑ c ∈ Finset.Icc 1 Z, ((c * dd).divisors.card : ℝ)
      ≤ ∑ c ∈ Finset.Icc 1 Z, Ct * (dd : ℝ) ^ δ * (c : ℝ) ^ δ :=
        Finset.sum_le_sum hpt
    _ = Ct * (dd : ℝ) ^ δ * ∑ c ∈ Finset.Icc 1 Z, (c : ℝ) ^ δ := by
        rw [Finset.mul_sum]
    _ ≤ Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (δ + 1) := by
        apply mul_le_mul_of_nonneg_left (sum_Icc_rpow_le_of_nonneg Z hδ)
        positivity
    _ = Ct * (dd : ℝ) ^ δ * (Z : ℝ) ^ (1 + δ) := by
        congr 2
        ring

/-- `‖∑_{c ∈ s} w c * f c‖ ≤ ∑_{c ∈ s} B c` when `‖w c‖ ≤ 1` and `‖f c‖ ≤ B c` on `s`. -/
lemma norm_sum_le_of_bound (s : Finset ℕ) (w f : ℕ → ℂ) (B : ℕ → ℝ)
    (hw : ∀ c, ‖w c‖ ≤ 1) (hf : ∀ c ∈ s, ‖f c‖ ≤ B c) :
    ‖∑ c ∈ s, w c * f c‖ ≤ ∑ c ∈ s, B c := by
  calc ‖∑ c ∈ s, w c * f c‖ ≤ ∑ c ∈ s, ‖w c * f c‖ := norm_sum_le _ _
    _ = ∑ c ∈ s, ‖w c‖ * ‖f c‖ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [norm_mul]
    _ ≤ ∑ c ∈ s, B c := by
        apply Finset.sum_le_sum
        intro c hc
        exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hw c)) (hf c hc)

/-- `absorb_log` in the form needed for the paper's `N`, which is a real number. -/
lemma absorb_log_real (C A ν : ℝ) (hC : 0 < C) (hν : 0 < ν) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ M : ℝ, x₀ ≤ M →
      C * (Real.log (M + 2)) ^ A ≤ M ^ ν := by
  have hC' : 0 < C * (2 : ℝ) ^ (max A 0) := by
    have h1 : 0 < (2 : ℝ) ^ (max A 0) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  obtain ⟨x₀, hx₀1, hx₀⟩ := absorb_log (C * (2 : ℝ) ^ (max A 0)) A ν hC' hν
  refine ⟨max (max (x₀ + 1) 2) (C ^ (1 / ν) + 1) + 1, ?_, ?_⟩
  · have h1 : (2 : ℝ) ≤ max (max (x₀ + 1) 2) (C ^ (1 / ν) + 1) :=
      le_trans (le_max_right (x₀ + 1) 2) (le_max_left (max (x₀ + 1) 2) (C ^ (1 / ν) + 1))
    linarith
  · intro M hM
    have hMx0 : x₀ + 1 ≤ M := by
      have h1 : x₀ + 1 ≤ max (max (x₀ + 1) 2) (C ^ (1 / ν) + 1) :=
        le_trans (le_max_left (x₀ + 1) 2) (le_max_left (max (x₀ + 1) 2) (C ^ (1 / ν) + 1))
      linarith
    have hM2 : (2 : ℝ) ≤ M := by
      have h1 : (2 : ℝ) ≤ max (max (x₀ + 1) 2) (C ^ (1 / ν) + 1) :=
        le_trans (le_max_right (x₀ + 1) 2) (le_max_left (max (x₀ + 1) 2) (C ^ (1 / ν) + 1))
      linarith
    have hMC : C ^ (1 / ν) + 1 ≤ M := by
      have h1 : C ^ (1 / ν) + 1 ≤ max (max (x₀ + 1) 2) (C ^ (1 / ν) + 1) :=
        le_max_right (max (x₀ + 1) 2) (C ^ (1 / ν) + 1)
      linarith
    have hMpos : (0 : ℝ) < M := by linarith
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three
    have hNge : x₀ ≤ ((⌊M⌋₊ : ℕ) : ℝ) := by
      have h1 : M < ((⌊M⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one M
      linarith
    have hh := hx₀ ⌊M⌋₊ hNge
    have hNle : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le (le_of_lt hMpos)
    have hlogN : (1 : ℝ) ≤ Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2) := by
      have h1 : Real.log 3 ≤ Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hlogM1 : (1 : ℝ) ≤ Real.log (M + 2) := by
      have h1 : Real.log 3 ≤ Real.log (M + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hlogM : Real.log (M + 2) ≤ 2 * Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2) := by
      have h1 : M + 2 ≤ 2 * (((⌊M⌋₊ : ℕ) : ℝ) + 2) := by
        have h2 : M < ((⌊M⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one M
        linarith
      have h2 := Real.log_le_log (by linarith : (0 : ℝ) < M + 2) h1
      have h3 : Real.log (2 * (((⌊M⌋₊ : ℕ) : ℝ) + 2))
          = Real.log 2 + Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2) :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hMCle : C ≤ M ^ ν := by
      have h1 : C ^ (1 / ν) ≤ M := by linarith
      calc C = (C ^ (1 / ν)) ^ ν := by
              rw [← Real.rpow_mul hC.le, show (1 / ν) * ν = 1 by field_simp, Real.rpow_one]
        _ ≤ M ^ ν := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) h1 hν.le
    by_cases hA : A ≤ 0
    · have h1 : (Real.log (M + 2)) ^ A ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlogM1 hA
      calc C * (Real.log (M + 2)) ^ A ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC.le
        _ = C := by ring
        _ ≤ M ^ ν := hMCle
    · push_neg at hA
      have h1 : (Real.log (M + 2)) ^ A
          ≤ (2 * Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2)) ^ A :=
        Real.rpow_le_rpow (by linarith) hlogM hA.le
      have h2 : (2 * Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2)) ^ A
          = (2 : ℝ) ^ A * (Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2)) ^ A :=
        Real.mul_rpow (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ A = (2 : ℝ) ^ (max A 0) := by
        rw [max_eq_left hA.le]
      have h4 : ((⌊M⌋₊ : ℕ) : ℝ) ^ ν ≤ M ^ ν :=
        Real.rpow_le_rpow (by positivity) hNle hν.le
      calc C * (Real.log (M + 2)) ^ A
          ≤ C * ((2 : ℝ) ^ A * (Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2)) ^ A) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hC.le
        _ = (C * (2 : ℝ) ^ (max A 0)) * (Real.log (((⌊M⌋₊ : ℕ) : ℝ) + 2)) ^ A := by
            rw [h3]; ring
        _ ≤ ((⌊M⌋₊ : ℕ) : ℝ) ^ ν := hh
        _ ≤ M ^ ν := h4

/-- `absorb_final` in the form needed for the paper's `N`. -/
lemma absorb_final_real (C A ν δ t : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hνt : δ + t < ν) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ M : ℝ, x₀ ≤ M →
      C * (Real.log (M + 2)) ^ A * M ^ (1 - ν + t) ≤ M ^ (1 - δ) := by
  have hνδt : 0 < ν - δ - t := by linarith
  obtain ⟨x₀, hx₀, hb⟩ := absorb_log_real C A (ν - δ - t) hC hνδt
  refine ⟨max x₀ 1, le_max_right _ _, ?_⟩
  intro M hM
  have h1 : x₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : (1 : ℝ) ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : (0 : ℝ) < M := by linarith
  have h := hb M h1
  calc C * (Real.log (M + 2)) ^ A * M ^ (1 - ν + t)
      = (C * (Real.log (M + 2)) ^ A) * M ^ (1 - ν + t) := by ring
    _ ≤ M ^ (ν - δ - t) * M ^ (1 - ν + t) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hMpos.le _)
    _ = M ^ ((ν - δ - t) + (1 - ν + t)) := (Real.rpow_add hMpos _ _).symm
    _ = M ^ (1 - δ) := by congr 1; ring

/-- ***FI* Proposition 17.2 (17.18), from Props. 23.1–23.2 and Theorem 2ψ.**

The §25 argument of *FI*: `SChiRad` is the double sum of (25.1)+(25.2); the range
`c > N^{η''}` is the pair bilinear form (25.4) (`pairEllSum2`), while the range `c ≤ N^{η''}` is
handled by the inner `ℓ`-estimate of (24.13) (`smallCInner2`, applied at each `c` with `x = ⌊b/c⌋`).
The four savings

  `1/77 - 2/r² - 2η''`,  `1/24 - η''`,  `1/(12r²) - η''`,  `η''/12`

(with `r = 13`, `η'' = min η (1/(100 r²))`) are all positive and dominate `ν`; the
polylogarithmic losses and the divisor factors `τ(c d)` are absorbed into `N^{δ₁}` by
`absorb_final`, taking `x₀` (hence `N`) large. -/
theorem prop172classical (h31 : Work.FIArea7.Prop231) (h32 : Work.FIArea7.Prop232)
    (h2psi : Work.FIArea7.Theorem2psi) : Work.FIArea7.Prop172Classical := by
  intro η hη0 hη32
  -- ## (A) the numerical parameters of §25
  set r : ℕ := 13 with hr
  have hr2 : 2 ≤ r := by rw [hr]; norm_num
  set η'' : ℝ := min η (1 / (100 * (r : ℝ) ^ 2)) with hη''
  have hη''0 : 0 < η'' := lt_min hη0 (by positivity)
  have hη''η : η'' ≤ η := min_le_left _ _
  have hη''e : η'' ≤ 1 / (100 * (r : ℝ) ^ 2) := min_le_right _ _
  have hη''16900 : η'' ≤ 1 / 16900 := by
    refine le_trans hη''e ?_
    rw [hr]; norm_num
  have hs1 : 0 < 1 / 77 - 2 / (r : ℝ) ^ 2 - 2 * η'' := by
    have h1 : (3 : ℝ) / 6160 ≤ 1 / 77 - 2 / (r : ℝ) ^ 2 := by rw [hr]; norm_num
    linarith
  have hs1le : 1 / 77 - 2 / (r : ℝ) ^ 2 - 2 * η'' ≤ 1 := by
    have h1 : (0 : ℝ) ≤ 2 / (r : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ η'' := hη''0.le
    have h3 : (1 : ℝ) / 77 ≤ 1 := by norm_num
    linarith only [h1, h2, h3]
  have hs2 : 0 < 1 / 24 - η'' := by linarith
  have hs3 : 0 < 1 / (12 * (r : ℝ) ^ 2) - η'' := by
    have h1 : (1 : ℝ) / 2028 ≤ 1 / (12 * (r : ℝ) ^ 2) := by rw [hr]; norm_num
    linarith
  have hs4 : 0 < η'' / 12 := by positivity
  set ν : ℝ := min (min (1 / 77 - 2 / (r : ℝ) ^ 2 - 2 * η'') (1 / 24 - η''))
      (min (1 / (12 * (r : ℝ) ^ 2) - η'') (η'' / 12)) with hν
  have hν0 : 0 < ν := lt_min (lt_min hs1 hs2) (lt_min hs3 hs4)
  have hν1 : ν ≤ 1 / 77 - 2 / (r : ℝ) ^ 2 - 2 * η'' :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hν2 : ν ≤ 1 / 24 - η'' := le_trans (min_le_left _ _) (min_le_right _ _)
  have hν3 : ν ≤ 1 / (12 * (r : ℝ) ^ 2) - η'' :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hν4 : ν ≤ η'' / 12 := le_trans (min_le_right _ _) (min_le_right _ _)
  set δ₁ : ℝ := ν / 16 with hδ₁
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hδ₁ν : 5 * δ₁ < ν := by rw [hδ₁]; linarith
  -- *FI* (23.8) now carries a power loss `(MN + c + 2)^ε`; run the §25 estimates with the fixed
  -- small loss `ε₀` and absorb the resulting `N^{2ε₀}` into the final saving.
  set ε₀ : ℝ := ν / 16 with hε₀
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; positivity
  have hνle1 : ν ≤ 1 := le_trans hν1 hs1le
  have hε₀1 : ε₀ ≤ 1 := by
    rw [hε₀]
    exact div_le_one_of_le₀ (le_trans hνle1 (by norm_num)) (by norm_num)
  have hδ₁ε : 5 * δ₁ + 2 * ε₀ < ν := by
    rw [hδ₁, hε₀]
    linarith only [hν0]
  obtain ⟨Cpair, Apair, hCpair, hApair, hpair⟩ := pairEllSum2Eps h31 ε₀ hε₀0
  obtain ⟨Csm, Asm, hCsm, hAsm, hsm⟩ := smallCInner2Eps h31 h2psi ε₀ hε₀0
  -- the divisor bound `τ(n) ≤ Ct n^{δ₁/4}`
  obtain ⟨Ct, hCt1, hCt⟩ := tau_le_mul_rpow (δ₁ / 4) (by positivity)
  have hCt0 : 0 < Ct := lt_of_lt_of_le zero_lt_one hCt1
  have hCtpt : ∀ cc dd : ℕ, 1 ≤ cc → 1 ≤ dd →
      ((cc * dd).divisors.card : ℝ) ≤ Ct * ((cc : ℝ) * (dd : ℝ)) ^ (δ₁ / 4) := by
    intro cc dd hc hd
    have h1 : 1 ≤ cc * dd := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 := hCt (cc * dd) h1
    rwa [Nat.cast_mul] at h2
  -- ## (B) the final constants and the absorption threshold
  set ρ1 : ℝ := 76 / 77 + 2 / (r : ℝ) ^ 2 with hρ1
  set ρ2 : ℝ := 23 / 24 with hρ2
  set ρ3 : ℝ := 1 - 1 / (12 * (r : ℝ) ^ 2) with hρ3
  have hρ10 : 0 < ρ1 := by rw [hρ1]; positivity
  have hρ20 : 0 < ρ2 := by rw [hρ2]; norm_num
  have hρ30 : 0 < ρ3 := by rw [hρ3]; rw [hr]; norm_num
  set Ctv : ℝ := Work.FITop4.cMoll 1 + 1 with hCtv
  have hCtv0 : 0 < Ctv := by
    rw [hCtv]
    have h1 := Work.FITop4.cMoll_pos 1
    linarith
  set Atot : ℝ := max Asm Apair with hAtot
  set Cfin : ℝ := ((Csm * Ctv * Ct * ((2:ℝ) ^ ρ1 + (2:ℝ) ^ ρ2 + (2:ℝ) ^ ρ3) * 2
      + Cpair * Ctv * (2:ℝ) ^ ((11 : ℝ) / 12) * (4:ℝ) ^ ((1 : ℝ) / 12)) * 2)
      * (2:ℝ) ^ (max Atot 0) * 16 with hCfin
  have hCfin0 : 0 < Cfin := by
    simp only [hCfin]
    have hp1 : 0 < (2:ℝ) ^ ρ1 := Real.rpow_pos_of_pos (by norm_num) _
    have hp2 : 0 < (2:ℝ) ^ ρ2 := Real.rpow_pos_of_pos (by norm_num) _
    have hp3 : 0 < (2:ℝ) ^ ρ3 := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : 0 < (2:ℝ) ^ ρ1 + (2:ℝ) ^ ρ2 + (2:ℝ) ^ ρ3 := by linarith
    have h2 : 0 < Csm * Ctv * Ct * ((2:ℝ) ^ ρ1 + (2:ℝ) ^ ρ2 + (2:ℝ) ^ ρ3) * 2 := by positivity
    have h3 : 0 < Cpair * Ctv * (2:ℝ) ^ ((11 : ℝ) / 12) * (4:ℝ) ^ ((1 : ℝ) / 12) := by
      positivity
    have h4 : 0 < (2:ℝ) ^ (max Atot 0) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  obtain ⟨x₀abs, hx₀abs1, hx₀abs⟩ := absorb_final_real Cfin Atot ν δ₁ (4 * δ₁ + 2 * ε₀) hCfin0 hδ₁0
    (by linarith only [hδ₁ε])
  set Xthr : ℝ := 2 ^ (64 * (r * r) + 64) with hXthr
  have hXthr1 : (1 : ℝ) ≤ Xthr := by
    rw [hXthr]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨δ₁, 1, max (x₀abs ^ 4) Xthr, hδ₁0, one_pos, ?_⟩
  intro Pa hx0 hηeq P Cc d chi m hPcont hP0 hP1 hPsupp hPder hCc1 hCcN hd1 hchi1
    hchimul hper1 hper2 hmd
  -- ## (C) local data
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hx0abs : x₀abs ≤ Pa.N := by
    have h1 : x₀abs ^ 4 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx0
    have h2 : (x₀abs ^ 4) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (x₀abs ^ 4) ^ ((1 : ℝ) / 4) = x₀abs := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ x₀abs)]
      norm_num
    have h4 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [show (3:ℝ) ≤ (Pa.x:ℝ) by exact_mod_cast Pa.hx]) (by linarith)
    have h5 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ Pa.N := by
      rw [← hηeq]; exact le_of_lt Pa.hNlo
    linarith [h2, h4, h5]
  have hXthrN : Xthr ^ ((1 : ℝ) / 4) ≤ Pa.N := by
    have h1 : Xthr ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx0
    have h2 : Xthr ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h4 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [show (3:ℝ) ≤ (Pa.x:ℝ) by exact_mod_cast Pa.hx]) (by linarith)
    have h5 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + η) ≤ Pa.N := by
      rw [← hηeq]; exact le_of_lt Pa.hNlo
    linarith
  set Mx : ℝ := Pa.N with hMx
  set Bx : ℝ := (1 + Pa.θ) * Pa.N with hBx
  have hMx1 : (1 : ℝ) ≤ Mx := by rw [hMx]; exact hN1
  have hMxpos : (0 : ℝ) < Mx := lt_of_lt_of_le zero_lt_one hMx1
  have hBxM : Bx ≤ 2 * Mx := by
    rw [hBx, hMx]
    have hθ := theta_le_one Pa
    have hN := Pa.hN1
    nlinarith
  have hBxpos : 0 < Bx := by
    rw [hBx]
    have hθ := Pa.hθ0
    have hN := Pa.hN1
    positivity
  set Rd : ℕ := (Work.FITop.radN Pa).natAbs with hRd
  set bx : ℕ := 2 * Rd ^ 2 with hbx
  have hRd4 : 4 * Pa.N ≤ (Rd : ℝ) ^ 2 := by
    rw [hRd]; exact fourN_le_radN_sq Pa
  have hbxM : 2 * Mx ≤ (bx : ℝ) := by
    rw [hbx, hMx]; push_cast; linarith
  have hbx1 : 1 ≤ bx := by
    have h1 : (1 : ℝ) ≤ (bx : ℝ) := le_trans (by linarith : (1:ℝ) ≤ 2 * Mx) hbxM
    exact_mod_cast h1
  -- the box radius is at most `20 N`: `Rd = ⌈√(4N)⌉₊ < √(4N) + 1 ≤ 2N + 1`
  have hbx_le : (bx : ℝ) ≤ 20 * Mx := by
    have hRd_lt : (Rd : ℝ) ≤ Real.sqrt (4 * Mx) + 1 := by
      rw [hRd, radN_natAbs, hMx]
      exact le_of_lt (Nat.ceil_lt_add_one (Real.sqrt_nonneg (4 * Pa.N)))
    have hRd0 : (0 : ℝ) ≤ (Rd : ℝ) := Nat.cast_nonneg _
    have hsq : (Rd : ℝ) ^ 2 ≤ 9 * Mx := by
      have h1 : (Rd : ℝ) ^ 2 ≤ (Real.sqrt (4 * Mx) + 1) ^ 2 := by
        nlinarith only [hRd_lt, hRd0, Real.sqrt_nonneg (4 * Mx)]
      have h3 : Real.sqrt (4 * Mx) ^ 2 = 4 * Mx := Real.sq_sqrt (by linarith only [hMx1])
      have h4 : Real.sqrt (4 * Mx) ≤ 2 * Mx := by
        rw [Real.sqrt_le_left (by linarith only [hMx1])]
        nlinarith only [hMx1]
      have h2 : (Real.sqrt (4 * Mx) + 1) ^ 2 ≤ 9 * Mx := by nlinarith only [h3, h4, hMx1]
      linarith only [h1, h2]
    rw [hbx]
    push_cast
    linarith only [hsq, hMx1]
  set Kx : ℝ := Work.FITop4.cMoll 1 * (Pa.θ * Pa.N) ^ (-(1 : ℝ)) with hKx
  have hKder : ∀ u : ℝ, |deriv P u| ≤ Kx := by
    intro u; rw [hKx]; exact deriv_bound_of_iteratedDeriv Pa hPder u
  have htv : Kx * |Bx - Mx| + 1 ≤ Ctv := by
    have hba : Mx ≤ Bx := by
      simp only [hMx, hBx]
      nlinarith [Pa.hθ0, Pa.hN1]
    have h := tv_factor_le (Pa := Pa) (a := Mx) (b := Bx) (K := Kx) hKx
      (le_of_eq hMx.symm) (le_of_eq hBx.symm) hba
    simp only [hCtv]
    exact h
  have hPsupp' : ∀ u : ℝ, P u ≠ 0 → Mx < u ∧ u ≤ Bx := by
    intro u hu
    have h := hPsupp u hu
    rw [hMx, hBx]
    exact h
  have hMxBig : (2 : ℝ) ^ (2 * ((r : ℝ) * (r : ℝ))) ≤ Mx := by
    have h1 : Xthr ^ ((1 : ℝ) / 4) ≤ Mx := by rw [hMx]; exact hXthrN
    have h2 : Xthr ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (16 * ((r : ℝ) * (r : ℝ)) + 16) := by
      rw [hXthr, ← Real.rpow_natCast (2 : ℝ) (64 * (r * r) + 64),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    have h3 : (2 : ℝ) ^ (2 * ((r : ℝ) * (r : ℝ))) ≤ Xthr ^ ((1 : ℝ) / 4) := by
      rw [h2]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [sq_nonneg (r : ℝ)]
    exact le_trans h3 h1
  have hhalf : (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) ≤ Mx ^ (1 - η'') := by
    have h3 : ((2 : ℝ) ^ (2 * ((r : ℝ) * (r : ℝ)))) ^ ((1 : ℝ) / 2) ≤ Mx ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hMxBig (by norm_num)
    have h4 : Mx ^ ((1 : ℝ) / 2) ≤ Mx ^ (1 - η'') :=
      Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith)
    have h5 : ((2 : ℝ) ^ (2 * ((r : ℝ) * (r : ℝ)))) ^ ((1 : ℝ) / 2)
        = (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    exact le_trans (h5 ▸ h3) h4
  -- ## (D) the `c`-ranges of (25.2)–(25.4)
  set A0 : ℕ := ⌊Cc⌋₊ with hA0
  set Cmax : ℕ := min bx A0 with hCmax
  set Zc0 : ℕ := ⌊Mx ^ η''⌋₊ with hZc0
  set Zc : ℕ := min Cmax Zc0 with hZc
  have hA01 : 1 ≤ A0 := by rw [hA0]; exact Nat.le_floor (by simpa using hCc1)
  have hA0Cc : (A0 : ℝ) ≤ Cc := by
    rw [hA0]; exact Nat.floor_le (le_trans zero_le_one hCc1)
  have hCmax1 : 1 ≤ Cmax := by rw [hCmax]; exact le_min hbx1 hA01
  have hCmaxA0 : Cmax ≤ A0 := by rw [hCmax]; exact min_le_right _ _
  have hCmaxCc : (Cmax : ℝ) ≤ Cc := le_trans (by exact_mod_cast hCmaxA0) hA0Cc
  have hZc01 : 1 ≤ Zc0 := by
    rw [hZc0]
    exact Nat.le_floor (by simpa using (Real.one_le_rpow hMx1 hη''0.le : (1 : ℝ) ≤ Mx ^ η''))
  have hZc0Mx : (Zc0 : ℝ) ≤ Mx ^ η'' := by
    rw [hZc0]; exact Nat.floor_le (Real.rpow_nonneg hMxpos.le _)
  have hZcCmax : Zc ≤ Cmax := by rw [hZc]; exact min_le_left _ _
  have hZcZc0 : Zc ≤ Zc0 := by rw [hZc]; exact min_le_right _ _
  have hZc1 : 1 ≤ Zc := by rw [hZc]; exact le_min hCmax1 hZc01
  have hZcMx : (Zc : ℝ) ≤ Mx ^ η'' := le_trans (by exact_mod_cast hZcZc0) hZc0Mx
  have hη''1 : η'' ≤ 1 := by linarith [hη''η, hη32]
  have hZcleMx : (Zc : ℝ) ≤ Mx := by
    refine le_trans hZcMx ?_
    calc Mx ^ η'' ≤ Mx ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMx1 hη''1
      _ = Mx := Real.rpow_one Mx
  -- ## (E) the two halves of the double sum
  set G : ℕ → ℂ := fun c => ∑ ℓ ∈ Finset.Icc 1 bx,
      (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
        * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
        * quadEigen (grossenChar chi m) (c * ℓ) else 0) with hG
  set W : ℕ → ℂ := fun c => (ArithmeticFunction.moebius c : ℂ) ^ 2 * nspInd Pa c with hW
  set Tf : ℕ → ℕ := fun c => ⌊Bx / (c : ℝ)⌋₊ with hTf
  have hSi : SChiRad Pa P Cc chi m = ∑ c ∈ Finset.Icc 1 Cmax, W c * G c :=
    SChiRad_eq_sum_Cmax Pa P Cc chi m hCc1 hPsupp
  have hW1 : ∀ c, ‖W c‖ ≤ 1 := by
    intro c
    simp only [hW]
    have hm : ‖(ArithmeticFunction.moebius c : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := c)
    have h1 : ‖(ArithmeticFunction.moebius c : ℂ) ^ 2‖ ≤ 1 := by
      rw [norm_pow]
      nlinarith [norm_nonneg ((ArithmeticFunction.moebius c : ℂ))]
    calc ‖(ArithmeticFunction.moebius c : ℂ) ^ 2 * nspInd Pa c‖
        = ‖(ArithmeticFunction.moebius c : ℂ) ^ 2‖ * ‖nspInd Pa c‖ := norm_mul _ _
      _ ≤ 1 * 1 :=
          mul_le_mul h1 (norm_nspInd_le_one Pa c) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hTfB : ∀ c, (Tf c : ℝ) ≤ Bx := by
    intro c
    rw [hTf]
    have h1 : (0 : ℝ) ≤ Bx / (c : ℝ) := by positivity
    have h2 : Bx / (c : ℝ) ≤ Bx := by
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp [hBxpos.le]
      · have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
        rw [div_le_iff₀ hcpos]
        have h3 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
        nlinarith only [h3, hBxpos]
    exact le_trans (Nat.floor_le h1) h2
  -- ### the small-`c` half: (24.13) at each `c ≤ Zc`
  have hN1 : ∀ c : ℕ, (0 : ℝ) ≤ Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm := by
    intro c
    have hA : (0 : ℝ) ≤ (Real.log ((Tf c : ℝ) + 2)) ^ Asm :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hB1 : (0 : ℝ) ≤ (Tf c : ℝ) := by positivity
    have hB : (0 : ℝ) ≤ (c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3 := by
      have h1 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ1 := Real.rpow_nonneg hB1 _
      have h2 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ2 := Real.rpow_nonneg hB1 _
      have h3 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ3 := Real.rpow_nonneg hB1 _
      have h4 : (0 : ℝ) ≤ (c : ℝ) := by positivity
      nlinarith only [h1, h2, h3, h4]
    have h1 : (0 : ℝ) ≤ Csm := hCsm.le
    have h2 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (((c * d).divisors.card : ℝ)) := by positivity
    have h4 : (0 : ℝ) ≤ (|(m : ℝ)| + 1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) hB) hA
  have hBnd1 : ∀ c ∈ Finset.Icc 1 Zc, ‖G c‖ ≤
      (6 * Mx ^ (2 * ε₀)) * (Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    obtain ⟨hc1, hcZ⟩ := hc
    have hcZc0 : c ≤ Zc0 := le_trans hcZ hZcZc0
    have hcMx : (c : ℝ) ≤ Mx ^ η'' := le_trans (by exact_mod_cast hcZc0) hZc0Mx
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc1
    have hMxleBx : Mx ≤ Bx := by rw [hBx]; nlinarith [Pa.hθ0, hNpos]
    have hcleBx : (c : ℝ) ≤ Bx := by
      refine le_trans (le_trans hcMx ?_) hMxleBx
      calc Mx ^ η'' ≤ Mx ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMx1 hη''1
        _ = Mx := Real.rpow_one Mx
    have hTfbx : Tf c ≤ bx := by
      have h2 : ((⌊Bx / (c : ℝ)⌋₊ : ℕ) : ℝ) ≤ (bx : ℝ) := by
        refine le_trans (Nat.floor_le (by positivity)) ?_
        rw [div_le_iff₀ hcpos]
        have h3 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
        have h4 : (0 : ℝ) < (bx : ℝ) := by positivity
        nlinarith only [h3, hBxM, hbxM, h4]
      rw [hTf]
      exact_mod_cast h2
    have hTf1 : 1 ≤ Tf c := by
      rw [hTf]
      apply Nat.le_floor
      rw [le_div_iff₀ hcpos]
      simpa using hcleBx
    have hTfbig : (2 : ℝ) ^ (r * r) ≤ (Tf c : ℝ) := by
      have hrr : (2 : ℝ) ^ (r * r) = (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) (r * r)]
        congr 1
        push_cast
        ring
      rw [hrr]
      have h1 : (c : ℝ) * (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) ≤ Mx := by
        have h2 : (c : ℝ) * (2 : ℝ) ^ ((r : ℝ) * (r : ℝ))
            ≤ Mx ^ η'' * (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right hcMx (by positivity)
        have h3 : Mx ^ η'' * (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) ≤ Mx ^ η'' * Mx ^ (1 - η'') :=
          mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hMxpos.le _)
        have h4 : Mx ^ η'' * Mx ^ (1 - η'') = Mx ^ (η'' + (1 - η'')) :=
          (Real.rpow_add hMxpos _ _).symm
        have h5 : η'' + (1 - η'') = 1 := by ring
        rw [h4, h5, Real.rpow_one] at h3
        linarith only [h2, h3]
      have h6 : ((2 ^ (r * r) : ℕ) : ℝ) ≤ Bx / (c : ℝ) := by
        have h3 : (2 : ℝ) ^ ((r : ℝ) * (r : ℝ)) * (c : ℝ) ≤ Bx := by
          rw [mul_comm]
          linarith only [h1, hMxleBx]
        push_cast
        rw [le_div_iff₀ hcpos, hrr]
        exact h3
      have h7 : 2 ^ (r * r) ≤ Tf c := by
        rw [hTf]; exact Nat.le_floor h6
      exact_mod_cast h7
    have hconv : G c = ∑ ℓ ∈ Finset.Icc 1 (Tf c),
        (if Nat.Coprime c ℓ then nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)
          * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
          * quadEigen (grossenChar chi m) (c * ℓ) else 0) := by
      rw [hG]
      refine sum_Icc_of_vanishing bx (Tf c) hTfbx _ ?_
      intro ℓ hℓ
      have hℓB : Bx < (c : ℝ) * (ℓ : ℝ) := by
        have h1 : Bx / (c : ℝ) < (ℓ : ℝ) := by
          have h2 : Bx / (c : ℝ) < ((Tf c : ℕ) : ℝ) + 1 := by
            simpa [hTf] using Nat.lt_floor_add_one (Bx / (c : ℝ))
          have h3 : ((Tf c : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hℓ
          linarith only [h2, h3]
        have h2 := (div_lt_iff₀ hcpos).mp h1
        linarith only [h2]
      have hP0 : P ((c : ℝ) * (ℓ : ℝ)) = 0 := by
        by_contra hne
        exact absurd (hPsupp' _ hne).2 (not_le.mpr hℓB)
      rw [hP0]
      simp
    have hloss : (((Tf c : ℝ) + (c : ℝ) + 2) ^ ε₀) ≤ 6 * Mx ^ (2 * ε₀) := by
      have h1 : (Tf c : ℝ) + (c : ℝ) + 2 ≤ 6 * Mx := by
        have h2 : (Tf c : ℝ) ≤ Bx := hTfB c
        linarith only [h2, hcleBx, hBxM, hMx1]
      have h4 : (0 : ℝ) ≤ (Tf c : ℝ) + (c : ℝ) + 2 := by positivity
      calc ((Tf c : ℝ) + (c : ℝ) + 2) ^ ε₀ ≤ (6 * Mx) ^ ε₀ := Real.rpow_le_rpow h4 h1 hε₀0.le
        _ = (6 : ℝ) ^ ε₀ * Mx ^ ε₀ := Real.mul_rpow (by norm_num) hMxpos.le
        _ ≤ 6 * Mx ^ (2 * ε₀) := by
            have h5 : (6 : ℝ) ^ ε₀ ≤ 6 := by
              calc (6 : ℝ) ^ ε₀ ≤ (6 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hε₀1
                _ = 6 := Real.rpow_one 6
            have h6 : Mx ^ ε₀ ≤ Mx ^ (2 * ε₀) :=
              Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith only [hε₀0])
            exact mul_le_mul h5 h6 (Real.rpow_nonneg hMxpos.le _) (by norm_num)
    have hbase := hsm Pa chi m d c r (Tf c) P Mx Bx Kx hd1 hc1 hTf1 hr2 hTfbig hchi1 hchimul
      hper1 hper2 (hPcont.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) (le_trans zero_le_one hMx1)
      hP0 hP1 hPsupp' hKder
    rw [hconv]
    refine le_trans hbase ?_
    have hKx0 : (0 : ℝ) ≤ Kx := by
      rw [hKx]
      exact mul_nonneg (Work.FITop4.cMoll_pos 1).le
        (Real.rpow_nonneg (mul_nonneg Pa.hθ0.le (le_trans zero_le_one Pa.hN1)) _)
    have hD0 : (0 : ℝ) ≤ Kx * |Bx - Mx| + 1 := by
      have h1 : (0 : ℝ) ≤ Kx * |Bx - Mx| := mul_nonneg hKx0 (abs_nonneg _)
      linarith only [h1]
    have hF0 : (0 : ℝ) ≤ Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm := by
      have ht1 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ1 := Real.rpow_nonneg (by positivity) _
      have ht2 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ2 := Real.rpow_nonneg (by positivity) _
      have ht3 : (0 : ℝ) ≤ (Tf c : ℝ) ^ ρ3 := Real.rpow_nonneg (by positivity) _
      have htm : (0 : ℝ) ≤ (c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3 := by
        have h4 : (0 : ℝ) ≤ (c : ℝ) := by positivity
        exact add_nonneg (add_nonneg (mul_nonneg h4 ht1) ht2) ht3
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCsm.le (by positivity))
        (by positivity)) (by have := abs_nonneg (m : ℝ); linarith)) htm)
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
    have hcomb : ((Tf c : ℝ) + (c : ℝ) + 2) ^ ε₀ * (Kx * |Bx - Mx| + 1)
        ≤ (6 * Mx ^ (2 * ε₀)) * Ctv :=
      mul_le_mul hloss htv hD0 (mul_nonneg (by norm_num) (Real.rpow_nonneg hMxpos.le _))
    calc Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
          * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
          * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * (((Tf c : ℝ) + (c : ℝ) + 2) ^ ε₀)
          * (Kx * |Bx - Mx| + 1)
        = (Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
            * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
            * (Real.log ((Tf c : ℝ) + 2)) ^ Asm)
          * (((Tf c : ℝ) + (c : ℝ) + 2) ^ ε₀ * (Kx * |Bx - Mx| + 1)) := by ring
      _ ≤ (Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
            * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
            * (Real.log ((Tf c : ℝ) + 2)) ^ Asm)
          * ((6 * Mx ^ (2 * ε₀)) * Ctv) := mul_le_mul_of_nonneg_left hcomb hF0
      _ = (6 * Mx ^ (2 * ε₀)) * (Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
            * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
            * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) := by ring
  have hsmall : ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖ ≤
      ∑ c ∈ Finset.Icc 1 Zc, (6 * Mx ^ (2 * ε₀)) * (Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) :=
    norm_sum_le_of_bound _ _ _ _ hW1 hBnd1
  have hsmall2 : ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖ ≤
      (6 * Mx ^ (2 * ε₀)) * (∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) :=
    le_trans hsmall (le_of_eq (Finset.mul_sum _ _ _).symm)
  -- ## (F) the big-`c` half: the pair `(c,ℓ)` bilinear form (25.4)
  have heq : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c),
        ∑ ℓ ∈ Finset.Icc 1 bx,
          (if Nat.Coprime c ℓ then W c * (nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ))
            * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
            * quadEigen (grossenChar chi m) (c * ℓ) else 0))
      = ∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c := by
    apply Finset.sum_congr rfl
    intro c _
    rw [hG, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    by_cases hcl : Nat.Coprime c ℓ
    · rw [if_pos hcl, if_pos hcl]; ring
    · rw [if_neg hcl, if_neg hcl, mul_zero]
  have hbe : ∀ ℓ : ℕ, ‖nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)‖ ≤ 1 := by
    intro ℓ
    calc ‖nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ)‖
        = ‖nspInd Pa ℓ‖ * ‖(ArithmeticFunction.moebius ℓ : ℂ)‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_nspInd_le_one Pa ℓ) (by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := ℓ)) (norm_nonneg _)
          (by norm_num)
      _ = 1 := by ring
  have hpair1 : ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c‖ ≤
      Cpair * max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
        * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀) * (Real.log (Bx + 2)) ^ Apair
        * (Kx * |Bx - Mx| + 1) := by
    rw [← heq]
    exact hpair chi m d Zc Cmax bx W (fun ℓ => nspInd Pa ℓ * (ArithmeticFunction.moebius ℓ : ℂ))
      P Mx Bx Kx hd1 hZc1 hCmax1 hbx1 hW1 hbe hchi1 hchimul
      (hPcont.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) (le_trans zero_le_one hMx1) hBxpos.le hP0 hP1
      hPsupp' hKder
  have hins : (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c)
      = insert Zc ((Finset.Icc 1 Cmax).filter (fun c => Zc < c)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases eq_or_lt_of_le h3 with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
      · subst h; exact ⟨⟨hZc1, hZcCmax⟩, le_refl _⟩
      · exact ⟨⟨h1, h2⟩, le_of_lt h3⟩
  have hnotmem : Zc ∉ (Finset.Icc 1 Cmax).filter (fun c => Zc < c) := by
    rw [Finset.mem_filter]
    exact fun h => absurd h.2 (lt_irrefl Zc)
  have hbig : ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c‖ ≤
      Cpair * max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
        * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀) * (Real.log (Bx + 2)) ^ Apair
        * (Kx * |Bx - Mx| + 1)
      + (6 * Mx ^ (2 * ε₀)) * (∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) := by
    have hsum : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c)
        = W Zc * G Zc
          + ∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c := by
      rw [hins, Finset.sum_insert hnotmem]
    have h4 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c)
        = (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c) - W Zc * G Zc := by
      rw [hsum]; ring
    have hX : ‖W Zc * G Zc‖ ≤
        (6 * Mx ^ (2 * ε₀)) * (∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
          * (|(m : ℝ)| + 1)
          * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
          * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) := by
      have h1 : ‖W Zc * G Zc‖ ≤ ‖G Zc‖ := by
        rw [norm_mul]
        calc ‖W Zc‖ * ‖G Zc‖ ≤ 1 * ‖G Zc‖ :=
              mul_le_mul_of_nonneg_right (hW1 Zc) (norm_nonneg _)
          _ = ‖G Zc‖ := by ring
      have h2 : ‖G Zc‖ ≤
          (6 * Mx ^ (2 * ε₀)) * (Csm * (d : ℝ) * (((Zc * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
            * ((Zc : ℝ) * (Tf Zc : ℝ) ^ ρ1 + (Tf Zc : ℝ) ^ ρ2 + (Tf Zc : ℝ) ^ ρ3)
            * (Real.log ((Tf Zc : ℝ) + 2)) ^ Asm * Ctv) :=
        hBnd1 Zc (Finset.mem_Icc.mpr ⟨hZc1, le_refl Zc⟩)
      have h5 : Csm * (d : ℝ) * (((Zc * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
          * ((Zc : ℝ) * (Tf Zc : ℝ) ^ ρ1 + (Tf Zc : ℝ) ^ ρ2 + (Tf Zc : ℝ) ^ ρ3)
          * (Real.log ((Tf Zc : ℝ) + 2)) ^ Asm * Ctv
          ≤ ∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
            * (|(m : ℝ)| + 1)
            * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
            * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv :=
        Finset.single_le_sum (f := fun c => Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
          * (|(m : ℝ)| + 1)
          * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
          * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv)
          (fun c _ => mul_nonneg (hN1 c) hCtv0.le)
          (Finset.mem_Icc.mpr ⟨hZc1, le_refl Zc⟩)
      have h6 : (6 * Mx ^ (2 * ε₀)) * (Csm * (d : ℝ) * (((Zc * d).divisors.card : ℝ))
            * (|(m : ℝ)| + 1)
            * ((Zc : ℝ) * (Tf Zc : ℝ) ^ ρ1 + (Tf Zc : ℝ) ^ ρ2 + (Tf Zc : ℝ) ^ ρ3)
            * (Real.log ((Tf Zc : ℝ) + 2)) ^ Asm * Ctv)
          ≤ (6 * Mx ^ (2 * ε₀)) * (∑ c ∈ Finset.Icc 1 Zc,
              Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
              * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
              * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg (by norm_num) (Real.rpow_nonneg hMxpos.le _))
      exact le_trans h1 (le_trans h2 h6)
    calc ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c‖
        = ‖(∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c) - W Zc * G Zc‖ := by
          rw [h4]
      _ ≤ ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc ≤ c), W c * G c‖ + ‖W Zc * G Zc‖ :=
          norm_sub_le _ _
      _ ≤ Cpair * max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
            * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀) * (Real.log (Bx + 2)) ^ Apair
            * (Kx * |Bx - Mx| + 1)
          + (6 * Mx ^ (2 * ε₀)) * (∑ c ∈ Finset.Icc 1 Zc,
              Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
              * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
              * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv) := by
          exact add_le_add hpair1 hX

  -- ## (G) the arithmetic of §25: absorption of the losses into `Mx^{1-δ₁}`
  have hdMx : (d : ℝ) ≤ Mx ^ δ₁ := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have h3 : (1 : ℝ) ≤ (|(m : ℝ)| + 1) := by
      have h := abs_nonneg (m : ℝ)
      linarith
    have h4 : (d : ℝ) ≤ (d : ℝ) * (|(m : ℝ)| + 1) := by nlinarith only [h1, h3]
    have h5 : (d : ℝ) * (|(m : ℝ)| + 1) ≤ Mx ^ δ₁ := by
      have hh := hmd
      rw [hMx] at hh
      exact hh
    linarith only [h4, h5]
  have hmdMx : (|(m : ℝ)| + 1) ≤ Mx ^ δ₁ := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have h3 : (1 : ℝ) ≤ (|(m : ℝ)| + 1) := by
      have h := abs_nonneg (m : ℝ)
      linarith
    have h4 : (|(m : ℝ)| + 1) ≤ (d : ℝ) * (|(m : ℝ)| + 1) := by nlinarith only [h1, h3]
    have h5 : (d : ℝ) * (|(m : ℝ)| + 1) ≤ Mx ^ δ₁ := by
      have hh := hmd
      rw [hMx] at hh
      exact hh
    linarith only [h4, h5]
  have hdδ : (d : ℝ) ^ (δ₁ / 4) ≤ Mx ^ (δ₁ * δ₁ / 4) := by
    calc (d : ℝ) ^ (δ₁ / 4) ≤ (Mx ^ δ₁) ^ (δ₁ / 4) :=
          Real.rpow_le_rpow (by positivity) hdMx (by positivity)
      _ = Mx ^ (δ₁ * (δ₁ / 4)) := (Real.rpow_mul hMxpos.le δ₁ (δ₁ / 4)).symm
      _ = Mx ^ (δ₁ * δ₁ / 4) := by congr 1; ring
  set L2 : ℝ := Real.log (2 * Mx + 2) with hL2
  have hL21 : (1 : ℝ) ≤ L2 := by
    rw [hL2]
    have h1 : Real.log 3 ≤ Real.log (2 * Mx + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three
    linarith
  have hL2nn : (0 : ℝ) ≤ L2 := le_trans zero_le_one hL21
  have hlogBx : Real.log (Bx + 2) ≤ L2 := by
    rw [hL2]
    exact Real.log_le_log (by linarith) (by linarith only [hBxM])
  have hlogBx0 : (0 : ℝ) ≤ Real.log (Bx + 2) := Real.log_nonneg (by linarith)
  -- ### the two slack factors `d` and `|m|+1` of (25.4)
  have hdm : (d : ℝ) * (|(m : ℝ)| + 1) ≤ Mx ^ (2 * δ₁) := by
    have h1 : (d : ℝ) * (|(m : ℝ)| + 1) ≤ Mx ^ δ₁ * Mx ^ δ₁ :=
      mul_le_mul hdMx hmdMx (by positivity) (Real.rpow_nonneg hMxpos.le _)
    calc (d : ℝ) * (|(m : ℝ)| + 1) ≤ Mx ^ δ₁ * Mx ^ δ₁ := h1
      _ = Mx ^ (δ₁ + δ₁) := (Real.rpow_add hMxpos _ _).symm
      _ = Mx ^ (2 * δ₁) := by congr 1; ring
  have hdtot : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
      ≤ Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) := by
    calc (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
        ≤ Mx ^ (2 * δ₁) * Mx ^ (δ₁ * δ₁ / 4) :=
          mul_le_mul hdm hdδ (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hMxpos.le _)
      _ = Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) := (Real.rpow_add hMxpos _ _).symm
  -- ### the exponent comparisons `γᵢ + 2δ₁ + δ₁²/4 ≤ 1 - ν + 4δ₁`
  have hδ₁1 : δ₁ ≤ 1 := by
    rw [hδ₁]
    exact div_le_one_of_le₀ (le_trans hνle1 (by norm_num)) (by norm_num)
  have hνρ1 : ρ1 + 2 * η'' ≤ 1 - ν := by
    have h1 : ρ1 + 2 * η'' = 1 - (1 / 77 - 2 / (r : ℝ) ^ 2 - 2 * η'') := by
      rw [hρ1]; ring
    rw [h1]
    exact sub_le_sub_left hν1 1
  have hνρ2 : ρ2 + η'' ≤ 1 - ν := by
    have h1 : ρ2 + η'' = 1 - (1 / 24 - η'') := by rw [hρ2]; ring
    rw [h1]
    exact sub_le_sub_left hν2 1
  have hνρ3 : ρ3 + η'' ≤ 1 - ν := by
    have h1 : ρ3 + η'' = 1 - (1 / (12 * (r : ℝ) ^ 2) - η'') := by rw [hρ3]; ring
    rw [h1]
    exact sub_le_sub_left hν3 1
  have hexp := expSlack172 (η := η'') (ν := ν) (δ := δ₁) (ρ1 := ρ1) (ρ2 := ρ2) (ρ3 := ρ3)
    hη''0.le hη''1 hδ₁0.le hδ₁1 hνρ1 hνρ2 hνρ3
  have he1 : 2 * δ₁ + δ₁ * δ₁ / 4 + (η'' * (2 + δ₁ / 4) + ρ1) ≤ 1 - ν + 4 * δ₁ := hexp.1
  have he2 : 2 * δ₁ + δ₁ * δ₁ / 4 + (η'' * (1 + δ₁ / 4) + ρ2) ≤ 1 - ν + 4 * δ₁ := hexp.2.1
  have he3 : 2 * δ₁ + δ₁ * δ₁ / 4 + (η'' * (1 + δ₁ / 4) + ρ3) ≤ 1 - ν + 4 * δ₁ := hexp.2.2
  -- ### the three terms of (25.4) after absorbing `d (|m|+1) d^{δ₁/4}`
  have hZ1n : (0 : ℝ) ≤ (Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Zc) _) (Real.rpow_nonneg hBxpos.le _)
  have hZ2n : (0 : ℝ) ≤ (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Zc) _) (Real.rpow_nonneg hBxpos.le _)
  have hZ3n : (0 : ℝ) ≤ (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Zc) _) (Real.rpow_nonneg hBxpos.le _)
  have hZsum0 : (0 : ℝ) ≤ (Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1
      + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3 := by
    linarith only [hZ1n, hZ2n, hZ3n]
  have ht1 : (Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1
      ≤ (2 : ℝ) ^ ρ1 * Mx ^ (η'' * (2 + δ₁ / 4) + ρ1) :=
    rpowMulLeTwo hMx1 (by positivity : (0 : ℝ) ≤ (Zc : ℝ)) hZcMx hBxpos.le hBxM
      (by linarith only [hδ₁0]) hρ10.le (le_refl _)
  have ht2 : (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
      ≤ (2 : ℝ) ^ ρ2 * Mx ^ (η'' * (1 + δ₁ / 4) + ρ2) :=
    rpowMulLeTwo hMx1 (by positivity : (0 : ℝ) ≤ (Zc : ℝ)) hZcMx hBxpos.le hBxM
      (by linarith only [hδ₁0]) hρ20.le (le_refl _)
  have ht3 : (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3
      ≤ (2 : ℝ) ^ ρ3 * Mx ^ (η'' * (1 + δ₁ / 4) + ρ3) :=
    rpowMulLeTwo hMx1 (by positivity : (0 : ℝ) ≤ (Zc : ℝ)) hZcMx hBxpos.le hBxM
      (by linarith only [hδ₁0]) hρ30.le (le_refl _)
  have ht1' : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
        * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1) ≤ (2 : ℝ) ^ ρ1 * Mx ^ (1 - ν + 4 * δ₁) := by
    have h1 : Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (2 + δ₁ / 4) + ρ1)
        ≤ Mx ^ (1 - ν + 4 * δ₁) := by
      rw [← Real.rpow_add hMxpos]
      exact Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith only [he1])
    calc (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
          * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1)
        ≤ Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * ((2 : ℝ) ^ ρ1 * Mx ^ (η'' * (2 + δ₁ / 4) + ρ1)) :=
          mul_le_mul hdtot ht1 hZ1n (Real.rpow_nonneg hMxpos.le _)
      _ = (2 : ℝ) ^ ρ1 * (Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (2 + δ₁ / 4) + ρ1)) := by
          ring
      _ ≤ (2 : ℝ) ^ ρ1 * Mx ^ (1 - ν + 4 * δ₁) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
  have ht2' : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
        * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2) ≤ (2 : ℝ) ^ ρ2 * Mx ^ (1 - ν + 4 * δ₁) := by
    have h1 : Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (1 + δ₁ / 4) + ρ2)
        ≤ Mx ^ (1 - ν + 4 * δ₁) := by
      rw [← Real.rpow_add hMxpos]
      exact Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith only [he2])
    calc (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
          * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2)
        ≤ Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * ((2 : ℝ) ^ ρ2 * Mx ^ (η'' * (1 + δ₁ / 4) + ρ2)) :=
          mul_le_mul hdtot ht2 hZ2n (Real.rpow_nonneg hMxpos.le _)
      _ = (2 : ℝ) ^ ρ2 * (Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (1 + δ₁ / 4) + ρ2)) := by
          ring
      _ ≤ (2 : ℝ) ^ ρ2 * Mx ^ (1 - ν + 4 * δ₁) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
  have ht3' : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
        * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3) ≤ (2 : ℝ) ^ ρ3 * Mx ^ (1 - ν + 4 * δ₁) := by
    have h1 : Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (1 + δ₁ / 4) + ρ3)
        ≤ Mx ^ (1 - ν + 4 * δ₁) := by
      rw [← Real.rpow_add hMxpos]
      exact Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith only [he3])
    calc (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
          * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3)
        ≤ Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * ((2 : ℝ) ^ ρ3 * Mx ^ (η'' * (1 + δ₁ / 4) + ρ3)) :=
          mul_le_mul hdtot ht3 hZ3n (Real.rpow_nonneg hMxpos.le _)
      _ = (2 : ℝ) ^ ρ3 * (Mx ^ (2 * δ₁ + δ₁ * δ₁ / 4) * Mx ^ (η'' * (1 + δ₁ / 4) + ρ3)) := by
          ring
      _ ≤ (2 : ℝ) ^ ρ3 * Mx ^ (1 - ν + 4 * δ₁) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)
  have hU : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
        * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
            + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3)
      ≤ ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * Mx ^ (1 - ν + 4 * δ₁) := by
    have hsplit : (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
          * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
              + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3)
        = (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
            * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1)
          + (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
            * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2)
          + (d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
            * ((Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3) := by ring
    rw [hsplit]
    refine le_trans (add_le_add (add_le_add ht1' ht2') ht3') ?_
    exact le_of_eq (by ring)
  -- ### the small-`c` sum, (G) assembled
  -- ### the small-`c` sum
  have hpt : ∀ c : ℕ, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ)) * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv
      ≤ Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm
        * (((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)) := by
    intro c
    have h1 : (Tf c : ℝ) ^ ρ1 ≤ Bx ^ ρ1 := Real.rpow_le_rpow (by positivity) (hTfB c) hρ10.le
    have h2 : (Tf c : ℝ) ^ ρ2 ≤ Bx ^ ρ2 := Real.rpow_le_rpow (by positivity) (hTfB c) hρ20.le
    have h3 : (Tf c : ℝ) ^ ρ3 ≤ Bx ^ ρ3 := Real.rpow_le_rpow (by positivity) (hTfB c) hρ30.le
    have h4 : (c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3
        ≤ (c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3 := by
      have h5 : (c : ℝ) * (Tf c : ℝ) ^ ρ1 ≤ (c : ℝ) * Bx ^ ρ1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith only [h5, h2, h3]
    have h6 : (Real.log ((Tf c : ℝ) + 2)) ^ Asm ≤ (Real.log (Bx + 2)) ^ Asm :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith))
        (Real.log_le_log (by linarith) (by linarith only [hTfB c])) hAsm.le
    have hτ : (0 : ℝ) ≤ ((c * d).divisors.card : ℝ) := by positivity
    have hS2 : (0 : ℝ) ≤ (c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3 := by
      have h7 : (0 : ℝ) ≤ Bx ^ ρ1 := Real.rpow_nonneg hBxpos.le _
      have h8 : (0 : ℝ) ≤ Bx ^ ρ2 := Real.rpow_nonneg hBxpos.le _
      have h9 : (0 : ℝ) ≤ Bx ^ ρ3 := Real.rpow_nonneg hBxpos.le _
      have h10 : (0 : ℝ) ≤ (c : ℝ) := by positivity
      nlinarith only [h7, h8, h9, h10]
    have hL1 : (0 : ℝ) ≤ (Real.log ((Tf c : ℝ) + 2)) ^ Asm :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have key : ((c * d).divisors.card : ℝ)
          * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
          * (Real.log ((Tf c : ℝ) + 2)) ^ Asm
        ≤ ((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)
          * (Real.log (Bx + 2)) ^ Asm := by
      have hA : (0 : ℝ) ≤ ((c * d).divisors.card : ℝ) * (Real.log ((Tf c : ℝ) + 2)) ^ Asm :=
        mul_nonneg hτ hL1
      calc ((c * d).divisors.card : ℝ)
            * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
            * (Real.log ((Tf c : ℝ) + 2)) ^ Asm
          = (((c * d).divisors.card : ℝ) * (Real.log ((Tf c : ℝ) + 2)) ^ Asm)
              * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3) := by ring
        _ ≤ (((c * d).divisors.card : ℝ) * (Real.log ((Tf c : ℝ) + 2)) ^ Asm)
              * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3) :=
            mul_le_mul_of_nonneg_left h4 hA
        _ ≤ (((c * d).divisors.card : ℝ) * (Real.log (Bx + 2)) ^ Asm)
              * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3) := by
            have h7 : ((c * d).divisors.card : ℝ) * (Real.log ((Tf c : ℝ) + 2)) ^ Asm
                ≤ ((c * d).divisors.card : ℝ) * (Real.log (Bx + 2)) ^ Asm :=
              mul_le_mul_of_nonneg_left h6 hτ
            exact mul_le_mul_of_nonneg_right h7 hS2
        _ = ((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)
              * (Real.log (Bx + 2)) ^ Asm := by ring
    calc Csm * (d : ℝ) * ((c * d).divisors.card : ℝ) * (|(m : ℝ)| + 1)
          * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
          * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv
        = (Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv)
            * (((c * d).divisors.card : ℝ)
              * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
              * (Real.log ((Tf c : ℝ) + 2)) ^ Asm) := by ring
      _ ≤ (Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv)
            * (((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)
              * (Real.log (Bx + 2)) ^ Asm) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm
            * (((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)) := by ring
  have hstep1 : (∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv)
      ≤ Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm
        * ∑ c ∈ Finset.Icc 1 Zc,
            (((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun c _ => hpt c)
  have hstep2 : (∑ c ∈ Finset.Icc 1 Zc,
        (((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)))
      ≤ Ct * (d : ℝ) ^ (δ₁ / 4)
        * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
            + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3) := by
    have hsplit : ∀ c ∈ Finset.Icc 1 Zc,
        ((c * d).divisors.card : ℝ) * ((c : ℝ) * Bx ^ ρ1 + Bx ^ ρ2 + Bx ^ ρ3)
        = ((c : ℝ) * ((c * d).divisors.card : ℝ)) * Bx ^ ρ1
          + ((c * d).divisors.card : ℝ) * Bx ^ ρ2
          + ((c * d).divisors.card : ℝ) * Bx ^ ρ3 := by
      intro c _; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    have h1 := sum_c_mul_tau_le Zc d (by positivity : (0:ℝ) ≤ δ₁ / 4) hCt0
      (fun c hc => hCtpt c d hc hd1)
    have h2 := sum_tau_le Zc d (by positivity : (0:ℝ) ≤ δ₁ / 4) hCt0
      (fun c hc => hCtpt c d hc hd1)
    have hb1 : (0 : ℝ) ≤ Bx ^ ρ1 := Real.rpow_nonneg hBxpos.le _
    have hb2 : (0 : ℝ) ≤ Bx ^ ρ2 := Real.rpow_nonneg hBxpos.le _
    have hb3 : (0 : ℝ) ≤ Bx ^ ρ3 := Real.rpow_nonneg hBxpos.le _
    have hc1 := mul_le_mul_of_nonneg_right h1 hb1
    have hc2 := mul_le_mul_of_nonneg_right h2 hb2
    have hc3 := mul_le_mul_of_nonneg_right h2 hb3
    linarith only [hc1, hc2, hc3]
  have hstep3 : Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm
        * (Ct * (d : ℝ) ^ (δ₁ / 4)
          * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
              + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3))
      ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * L2 ^ Atot
          * Mx ^ (1 - ν + 4 * δ₁) := by
    have hLb : (Real.log (Bx + 2)) ^ Asm ≤ L2 ^ Atot := by
      calc (Real.log (Bx + 2)) ^ Asm ≤ L2 ^ Asm :=
            Real.rpow_le_rpow hlogBx0 hlogBx hAsm.le
        _ ≤ L2 ^ Atot := Real.rpow_le_rpow_of_exponent_le hL21 (le_max_left _ _)
    have hccoef : (0 : ℝ) ≤ Csm * Ctv * Ct := mul_nonneg (mul_nonneg hCsm.le hCtv0.le) hCt0.le
    have hstepa : (Real.log (Bx + 2)) ^ Asm
          * ((d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
            * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
                + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3))
        ≤ L2 ^ Atot * (((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3)
            * Mx ^ (1 - ν + 4 * δ₁)) := by
      refine mul_le_mul hLb hU ?_ (Real.rpow_nonneg hL2nn _)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (by have := abs_nonneg (m : ℝ); linarith))
          (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hZsum0
    calc Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm
          * (Ct * (d : ℝ) ^ (δ₁ / 4)
            * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
                + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3))
        = (Csm * Ctv * Ct) * ((Real.log (Bx + 2)) ^ Asm
            * ((d : ℝ) * (|(m : ℝ)| + 1) * (d : ℝ) ^ (δ₁ / 4)
              * ((Zc : ℝ) ^ (2 + δ₁ / 4) * Bx ^ ρ1 + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ2
                  + (Zc : ℝ) ^ (1 + δ₁ / 4) * Bx ^ ρ3))) := by ring
      _ ≤ (Csm * Ctv * Ct) * (L2 ^ Atot * (((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3)
            * Mx ^ (1 - ν + 4 * δ₁))) := mul_le_mul_of_nonneg_left hstepa hccoef
      _ = Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * L2 ^ Atot
            * Mx ^ (1 - ν + 4 * δ₁) := by ring
  have hSB : (∑ c ∈ Finset.Icc 1 Zc, Csm * (d : ℝ) * (((c * d).divisors.card : ℝ))
        * (|(m : ℝ)| + 1)
        * ((c : ℝ) * (Tf c : ℝ) ^ ρ1 + (Tf c : ℝ) ^ ρ2 + (Tf c : ℝ) ^ ρ3)
        * (Real.log ((Tf c : ℝ) + 2)) ^ Asm * Ctv)
      ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * L2 ^ Atot
          * Mx ^ (1 - ν + 4 * δ₁) := by
    have hFnn : (0 : ℝ) ≤ Csm * (d : ℝ) * (|(m : ℝ)| + 1) * Ctv * (Real.log (Bx + 2)) ^ Asm :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hCsm.le (Nat.cast_nonneg d))
          (by have := abs_nonneg (m : ℝ); linarith)) hCtv0.le)
        (Real.rpow_nonneg hlogBx0 _)
    refine le_trans hstep1 ?_
    refine le_trans (mul_le_mul_of_nonneg_left hstep2 hFnn) ?_
    refine le_trans hstep3 ?_
    have h0 : (0 : ℝ) ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCsm.le hCtv0.le) hCt0.le)
        (by have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ1 := Real.rpow_nonneg (by norm_num) _
            have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ2 := Real.rpow_nonneg (by norm_num) _
            have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ3 := Real.rpow_nonneg (by norm_num) _
            linarith only [h1, h2, h3])
    have hc : Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3)
        ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 := by
      linarith only [h0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL2nn _))
      (Real.rpow_nonneg hMxpos.le _)
  -- ## (H) the pair term and the conclusion
  have hPB1 : Zc0 ≤ Cmax →
      Cpair * max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
        * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀) * (Real.log (Bx + 2)) ^ Apair
        * (Kx * |Bx - Mx| + 1)
      ≤ (30 * Mx ^ (2 * ε₀)) * (Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)
          * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) := by
    intro hle0
    have hZcge : Mx ^ η'' / 2 ≤ (Zc : ℝ) := by
      rw [hZc, min_eq_right hle0, hZc0]
      exact floorRpowHalfLe hMx1 hη''0.le
    have hZcpos : (0 : ℝ) < (Zc : ℝ) := by positivity
    have hBxZc : Bx / (Zc : ℝ) ≤ 4 * Mx ^ (1 - η'') := by
      rw [div_le_iff₀ hZcpos]
      have h1 : Mx ^ (1 - η'') * (Mx ^ η'' / 2) ≤ Mx ^ (1 - η'') * (Zc : ℝ) :=
        mul_le_mul_of_nonneg_left hZcge (Real.rpow_nonneg hMxpos.le _)
      have h2 : Mx ^ (1 - η'') * Mx ^ η'' = Mx := by
        rw [← Real.rpow_add hMxpos]
        norm_num
      linarith only [h1, h2, hBxM]
    have hMxEth : Mx ^ (1 - η) ≤ 4 * Mx ^ (1 - η'') := by
      have h1 : Mx ^ (1 - η) ≤ Mx ^ (1 - η'') :=
        Real.rpow_le_rpow_of_exponent_le hMx1 (by linarith only [hη''η])
      linarith only [h1, Real.rpow_nonneg hMxpos.le (1 - η'')]
    have hmax : max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ≤ 4 * Mx ^ (1 - η'') := by
      refine max_le ?_ hBxZc
      exact le_trans (le_trans hCmaxCc hCcN) hMxEth
    have hmaxn : (0 : ℝ) ≤ max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) :=
      le_trans (Nat.cast_nonneg Cmax) (le_max_left _ _)
    have hc12 : max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12)
        ≤ (4 * Mx ^ (1 - η'')) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow hmaxn hmax (by norm_num)
    have hp : (4 * Mx ^ (1 - η'')) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
        ≤ (4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12) * Mx ^ (1 - ν + 4 * δ₁) :=
      rpowMulLeGen hMx1 (by norm_num) hBxpos.le hBxM (by norm_num) (by norm_num)
        (pairExp172 hδ₁0.le hν4)
    have hcomb : max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
        ≤ (4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12) * Mx ^ (1 - ν + 4 * δ₁) :=
      le_trans (mul_le_mul_of_nonneg_right hc12 (Real.rpow_nonneg hBxpos.le _)) hp
    have hlogS : (Real.log (Bx + 2)) ^ Apair ≤ L2 ^ Atot := by
      calc (Real.log (Bx + 2)) ^ Apair ≤ L2 ^ Apair :=
            Real.rpow_le_rpow hlogBx0 hlogBx hApair.le
        _ ≤ L2 ^ Atot := Real.rpow_le_rpow_of_exponent_le hL21 (le_max_right _ _)
    have hKx0 : (0 : ℝ) ≤ Kx := by
      rw [hKx]
      exact mul_nonneg (Work.FITop4.cMoll_pos 1).le
        (Real.rpow_nonneg (mul_nonneg Pa.hθ0.le (le_trans zero_le_one Pa.hN1)) _)
    have hKmono : (0 : ℝ) ≤ Kx * |Bx - Mx| + 1 := by
      have h1 : (0 : ℝ) ≤ Kx * |Bx - Mx| := mul_nonneg hKx0 (abs_nonneg _)
      linarith only [h1]
    have hX0 : (0 : ℝ) ≤ (4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12)
        * Mx ^ (1 - ν + 4 * δ₁) :=
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg hMxpos.le _)
    have h1 : max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
          * (Real.log (Bx + 2)) ^ Apair
        ≤ ((4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12) * Mx ^ (1 - ν + 4 * δ₁))
            * L2 ^ Atot :=
      mul_le_mul hcomb hlogS (Real.rpow_nonneg hlogBx0 _) hX0
    have h2 : max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
          * (Real.log (Bx + 2)) ^ Apair * (Kx * |Bx - Mx| + 1)
        ≤ (((4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12) * Mx ^ (1 - ν + 4 * δ₁))
            * L2 ^ Atot) * Ctv :=
      mul_le_mul h1 htv hKmono (mul_nonneg hX0 (Real.rpow_nonneg hL2nn _))
    have hloss : (Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀ ≤ 30 * Mx ^ (2 * ε₀) := by
      have hCmaxMx : (Cmax : ℝ) ≤ Mx := by
        refine le_trans hCmaxCc (le_trans hCcN ?_)
        simpa using Real.rpow_le_rpow_of_exponent_le hMx1
          (by linarith only [hη0] : (1 : ℝ) - η ≤ 1)
      have hcb : (Cmax : ℝ) * (bx : ℝ) ≤ Mx * (20 * Mx) :=
        mul_le_mul hCmaxMx hbx_le (Nat.cast_nonneg bx) hMxpos.le
      have hMx2 : Mx ≤ Mx * Mx := le_mul_of_one_le_left hMxpos.le hMx1
      have h1 : Bx + (Cmax : ℝ) * (bx : ℝ) + 2 ≤ 30 * (Mx * Mx) := by
        linarith only [hBxM, hcb, hMx2, hMx1]
      have h3 : (0 : ℝ) ≤ Bx + (Cmax : ℝ) * (bx : ℝ) + 2 := by positivity
      have h6 : (0 : ℝ) ≤ Mx * Mx := mul_nonneg hMxpos.le hMxpos.le
      calc (Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀ ≤ (30 * (Mx * Mx)) ^ ε₀ :=
            Real.rpow_le_rpow h3 h1 hε₀0.le
        _ = (30 : ℝ) ^ ε₀ * (Mx * Mx) ^ ε₀ := Real.mul_rpow (by norm_num) h6
        _ = (30 : ℝ) ^ ε₀ * Mx ^ (2 * ε₀) := by
              rw [Real.mul_rpow hMxpos.le hMxpos.le, ← Real.rpow_add hMxpos]
              congr 1
              ring
        _ ≤ 30 * Mx ^ (2 * ε₀) := by
              have h5 : (30 : ℝ) ^ ε₀ ≤ 30 := by
                calc (30 : ℝ) ^ ε₀ ≤ (30 : ℝ) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hε₀1
                  _ = 30 := Real.rpow_one 30
              exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hMxpos.le _)
    have hloss0 : (0 : ℝ) ≤ (Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀ :=
      Real.rpow_nonneg (by positivity) _
    have hcore0 : (0 : ℝ) ≤ (((4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12)
          * Mx ^ (1 - ν + 4 * δ₁)) * L2 ^ Atot) * Ctv :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hMxpos.le _))
          (Real.rpow_nonneg hL2nn _)) hCtv0.le
    calc Cpair * max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
          * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀) * (Real.log (Bx + 2)) ^ Apair
          * (Kx * |Bx - Mx| + 1)
        = Cpair * ((max ((Cmax : ℝ)) (Bx / (Zc : ℝ)) ^ ((1 : ℝ) / 12) * Bx ^ ((11 : ℝ) / 12)
            * (Real.log (Bx + 2)) ^ Apair * (Kx * |Bx - Mx| + 1))
            * ((Bx + (Cmax : ℝ) * (bx : ℝ) + 2) ^ ε₀)) := by ring
      _ ≤ Cpair * (((((4 : ℝ) ^ ((1 : ℝ) / 12) * (2 : ℝ) ^ ((11 : ℝ) / 12)
            * Mx ^ (1 - ν + 4 * δ₁)) * L2 ^ Atot) * Ctv) * (30 * Mx ^ (2 * ε₀))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 hloss hloss0 hcore0) hCpair.le
      _ = (30 * Mx ^ (2 * ε₀)) * (Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)
            * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) := by ring
  -- ### the final absorption
  have hlog2 : L2 ^ Atot ≤ (2 : ℝ) ^ (max Atot 0) * (Real.log (Mx + 2)) ^ Atot := by
    have h1 : L2 ≤ 2 * Real.log (Mx + 2) := by
      rw [hL2]
      have h2 : Real.log (2 * Mx + 2) ≤ Real.log (2 * (Mx + 2)) :=
        Real.log_le_log (by linarith) (by linarith)
      have h3 : Real.log (2 * (Mx + 2)) = Real.log 2 + Real.log (Mx + 2) :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log (Mx + 2) := Real.log_le_log (by norm_num) (by linarith)
      linarith only [h2, h3, h4]
    have hAtot0 : (0 : ℝ) ≤ Atot := by
      rw [hAtot]
      exact le_trans hAsm.le (le_max_left _ _)
    have h2 : L2 ^ Atot ≤ (2 * Real.log (Mx + 2)) ^ Atot :=
      Real.rpow_le_rpow hL2nn h1 hAtot0
    have h3 : (2 * Real.log (Mx + 2)) ^ Atot
        = (2 : ℝ) ^ Atot * (Real.log (Mx + 2)) ^ Atot :=
      Real.mul_rpow (by norm_num) (Real.log_nonneg (by linarith))
    have h4 : (2 : ℝ) ^ Atot ≤ (2 : ℝ) ^ (max Atot 0) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left _ _)
    calc L2 ^ Atot ≤ (2 * Real.log (Mx + 2)) ^ Atot := h2
      _ = (2 : ℝ) ^ Atot * (Real.log (Mx + 2)) ^ Atot := h3
      _ ≤ (2 : ℝ) ^ (max Atot 0) * (Real.log (Mx + 2)) ^ Atot :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  have hA1nn : (0 : ℝ) ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ1 := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ2 := Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ ρ3 := Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hCsm.le hCtv0.le) hCt0.le) (by linarith only [h1, h2, h3]))
      (by norm_num)
  have hA2nn : (0 : ℝ) ≤ Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hCpair.le hCtv0.le) (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  have hL2M : (0 : ℝ) ≤ L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁) :=
    mul_nonneg (Real.rpow_nonneg hL2nn _) (Real.rpow_nonneg hMxpos.le _)
  have hK0 : (0 : ℝ) ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
      + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30 :=
    add_nonneg (mul_nonneg hA1nn (by norm_num)) (mul_nonneg hA2nn (by norm_num))
  have hKle : Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
      + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30
      ≤ (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
          + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16 := by
    have ha : Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
        ≤ Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 32 :=
      mul_le_mul_of_nonneg_left (by norm_num : (12 : ℝ) ≤ 32) hA1nn
    have hb : Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30
        ≤ Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 32 :=
      mul_le_mul_of_nonneg_left (by norm_num : (30 : ℝ) ≤ 32) hA2nn
    have hsum := add_le_add ha hb
    have h32 : Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 32
          + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 32
        = (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
          + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16 := by
      ring
    exact le_trans hsum (le_of_eq h32)
  have hfinal : ∀ K : ℝ, 0 ≤ K →
      K ≤ (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16 →
      K * Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))
        ≤ Cfin * (Real.log (Mx + 2)) ^ Atot * Mx ^ (1 - ν + (4 * δ₁ + 2 * ε₀)) := by
    intro K hK0 hKle
    have hcoe : (0 : ℝ) ≤ (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16 :=
      mul_nonneg (mul_nonneg (add_nonneg hA1nn hA2nn) (by norm_num)) (by norm_num)
    have hMx2 : (0 : ℝ) ≤ Mx ^ (2 * ε₀) := Real.rpow_nonneg hMxpos.le _
    have hMxE : (0 : ℝ) ≤ Mx ^ (1 - ν + 4 * δ₁) := Real.rpow_nonneg hMxpos.le _
    have h2 : Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))
        ≤ Mx ^ (2 * ε₀) * (((2 : ℝ) ^ (max Atot 0) * (Real.log (Mx + 2)) ^ Atot)
            * Mx ^ (1 - ν + 4 * δ₁)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog2 hMxE) hMx2
    calc K * Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))
        = K * (Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))) := by ring
      _ ≤ ((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16)
          * (Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))) :=
          mul_le_mul_of_nonneg_right hKle (mul_nonneg hMx2 hL2M)
      _ ≤ ((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16)
          * (Mx ^ (2 * ε₀) * (((2 : ℝ) ^ (max Atot 0) * (Real.log (Mx + 2)) ^ Atot)
              * Mx ^ (1 - ν + 4 * δ₁))) := mul_le_mul_of_nonneg_left h2 hcoe
      _ = (((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16)
            * (2 : ℝ) ^ (max Atot 0)) * (Real.log (Mx + 2)) ^ Atot
            * (Mx ^ (2 * ε₀) * Mx ^ (1 - ν + 4 * δ₁)) := by ring
      _ = (((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)) * 2 * 16)
            * (2 : ℝ) ^ (max Atot 0)) * (Real.log (Mx + 2)) ^ Atot
            * Mx ^ (2 * ε₀ + (1 - ν + 4 * δ₁)) := by
          rw [← Real.rpow_add hMxpos]
      _ = Cfin * (Real.log (Mx + 2)) ^ Atot * Mx ^ (1 - ν + (4 * δ₁ + 2 * ε₀)) := by
          have hexp : 2 * ε₀ + (1 - ν + 4 * δ₁) = 1 - ν + (4 * δ₁ + 2 * ε₀) := by ring
          rw [hexp, hCfin]
          ring
  have hfin : ‖SChiRad Pa P Cc chi m‖
      ≤ Cfin * (Real.log (Mx + 2)) ^ Atot * Mx ^ (1 - ν + (4 * δ₁ + 2 * ε₀)) := by
    have hE2 : (0 : ℝ) ≤ 6 * Mx ^ (2 * ε₀) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hMxpos.le _)
    have hs : ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖
        ≤ (6 * Mx ^ (2 * ε₀)) * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
            * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) :=
      le_trans hsmall2 (mul_le_mul_of_nonneg_left hSB hE2)
    by_cases hcase : Zc0 ≤ Cmax
    · have hPB := hPB1 hcase
      have hb : ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c‖
          ≤ (30 * Mx ^ (2 * ε₀)) * (Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12)
              * (4 : ℝ) ^ ((1 : ℝ) / 12) * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))
            + (6 * Mx ^ (2 * ε₀)) * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
              * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) := by
        refine le_trans hbig (add_le_add hPB ?_)
        exact mul_le_mul_of_nonneg_left hSB hE2
      have htri : ‖∑ c ∈ Finset.Icc 1 Cmax, W c * G c‖
          ≤ ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖
            + ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c‖ := by
        rw [sum_Icc_split Zc Cmax hZcCmax (f := fun c => W c * G c)]
        exact norm_add_le _ _
      have htot : ‖∑ c ∈ Finset.Icc 1 Cmax, W c * G c‖
          ≤ ((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
              + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30)
              * Mx ^ (2 * ε₀)) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) :=
        le_trans (le_trans htri (add_le_add hs hb)) (le_of_eq (by ring))
      rw [hSi]
      exact le_trans htot (hfinal _ hK0 hKle)
    · push_neg at hcase
      have hZceq : Zc = Cmax := by rw [hZc]; exact min_eq_left (le_of_lt hcase)
      have hsum0 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c => Zc < c), W c * G c) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [Finset.mem_filter, Finset.mem_Icc] at hc
        rw [← hZceq] at hc
        exact absurd hc.2 (not_lt.mpr hc.1.2)
      have htri : ‖∑ c ∈ Finset.Icc 1 Cmax, W c * G c‖ ≤ ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖ := by
        rw [sum_Icc_split Zc Cmax hZcCmax (f := fun c => W c * G c), hsum0, add_zero]
      have htot : ‖∑ c ∈ Finset.Icc 1 Zc, W c * G c‖
          ≤ ((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
              + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30)
              * Mx ^ (2 * ε₀)) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) := by
        refine le_trans hs ?_
        calc (6 * Mx ^ (2 * ε₀)) * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2
              * L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))
            = (6 * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2))
              * (Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))) := by ring
          _ ≤ (12 * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2))
              * (Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 12) hA1nn)
                (mul_nonneg (Real.rpow_nonneg hMxpos.le _) hL2M)
          _ ≤ (12 * (Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2)
                + 30 * (Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12)))
              * (Mx ^ (2 * ε₀) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁))) :=
              mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right (mul_nonneg (by norm_num) hA2nn))
                (mul_nonneg (Real.rpow_nonneg hMxpos.le _) hL2M)
          _ = ((Csm * Ctv * Ct * ((2 : ℝ) ^ ρ1 + (2 : ℝ) ^ ρ2 + (2 : ℝ) ^ ρ3) * 2 * 12
                + Cpair * Ctv * (2 : ℝ) ^ ((11 : ℝ) / 12) * (4 : ℝ) ^ ((1 : ℝ) / 12) * 30)
                * Mx ^ (2 * ε₀)) * (L2 ^ Atot * Mx ^ (1 - ν + 4 * δ₁)) := by ring
      rw [hSi]
      exact le_trans htri (le_trans htot (hfinal _ hK0 hKle))
  calc ‖SChiRad Pa P Cc chi m‖
      ≤ Cfin * (Real.log (Mx + 2)) ^ Atot * Mx ^ (1 - ν + (4 * δ₁ + 2 * ε₀)) := hfin
    _ ≤ Mx ^ (1 - δ₁) := hx₀abs Mx (by rw [hMx]; exact hx0abs)
    _ = 1 * Mx ^ (1 - δ₁) := by ring

end

end Work.FIArea7

