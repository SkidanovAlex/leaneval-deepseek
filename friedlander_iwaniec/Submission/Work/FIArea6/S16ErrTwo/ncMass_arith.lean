import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.NcDefs
import Submission.Work.FIArea3.tau_gnorm_gBox_bound
import Submission.Work.FIArea3.tau_le_two_mul_card_dvd
import Submission.Work.FIArea1.gnorm_inv_sums

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary box API -/

/-- Membership in the Gaussian box `gBox R` gives the coordinate bounds. -/
lemma mem_gBox_coords {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image] at hz
  obtain ⟨p, hp, heq⟩ := hz
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have h1 : p.1 = z.re := by simpa using congrArg Zsqrtd.re heq
  have h2 : p.2 = z.im := by simpa using congrArg Zsqrtd.im heq
  exact ⟨h1 ▸ hp1, h2 ▸ hp2⟩

/-- `gnorm π` is positive on `ncPi Pa`, because `Pz ≥ 2 < gnorm π`. -/
lemma gnorm_pos_of_mem_ncPi (Pa : Work.FITop.Params) {π : GaussianInt} (hπ : π ∈ ncPi Pa) :
    (0 : ℝ) < (Work.FIPlan.gnorm π : ℝ) := by
  have hPz : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have := Pa.hP2
    exact_mod_cast (by omega : 0 < Pa.Pz)
  have hlt : (Pa.Pz : ℝ) < (Work.FIPlan.gnorm π : ℝ) := by
    have := gnorm_gt_Pz_of_mem_ncPi hπ
    exact_mod_cast this
  linarith

/-- `1 ≤ gnorm π` on `ncPi Pa`. -/
lemma one_le_gnorm_of_mem_ncPi (Pa : Work.FITop.Params) {π : GaussianInt}
    (hπ : π ∈ ncPi Pa) : (1 : ℝ) ≤ (Work.FIPlan.gnorm π : ℝ) := by
  have h2 : (2 : ℝ) ≤ (Pa.Pz : ℝ) := by exact_mod_cast Pa.hP2
  have hlt : (Pa.Pz : ℝ) < (Work.FIPlan.gnorm π : ℝ) := by
    have := gnorm_gt_Pz_of_mem_ncPi hπ
    exact_mod_cast this
  linarith

/-! ## 1. Arithmetic of `ncPi` -/

/-- `|π|² ≤ 16N` for `π ∈ ncPi Pa`: `π` lies in `gBox (ncKb Pa)` with
`ncKb Pa = ⌈√(2N)⌉`, so `|π|² ≤ 2(√(2N)+1)² ≤ 16N` as `N ≥ 1`. -/
lemma ncPi_gnorm_le_16 (Pa : Work.FITop.Params) {π : GaussianInt} (hπ : π ∈ ncPi Pa) :
    ((Work.FIPlan.gnorm π : ℝ)) ≤ 16 * Pa.N := by
  have hmem : π ∈ Work.FIPlan.gBox (Work.FIArea6.ncKb Pa) := (mem_ncPi.mp hπ).1
  obtain ⟨hre, him⟩ := mem_gBox_coords hmem
  rw [Finset.mem_Icc] at hre him
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hK0 : (0 : ℝ) ≤ (Work.FIArea6.ncKb Pa : ℝ) := by
    have : (0 : ℤ) ≤ Work.FIArea6.ncKb Pa := by simp [Work.FIArea6.ncKb]
    exact_mod_cast this
  have hKlt : (Work.FIArea6.ncKb Pa : ℝ) < Real.sqrt (2 * Pa.N) + 1 := by
    have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * Pa.N))
    simpa [Work.FIArea6.ncKb] using h
  have hre' : |((π.re : ℤ) : ℝ)| ≤ (Work.FIArea6.ncKb Pa : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast hre.1, by exact_mod_cast hre.2⟩
  have him' : |((π.im : ℤ) : ℝ)| ≤ (Work.FIArea6.ncKb Pa : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast him.1, by exact_mod_cast him.2⟩
  have hsq1 : ((π.re : ℤ) : ℝ) ^ 2 ≤ (Work.FIArea6.ncKb Pa : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hre' 2
    rwa [sq_abs] at h
  have hsq2 : ((π.im : ℤ) : ℝ) ^ 2 ≤ (Work.FIArea6.ncKb Pa : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) him' 2
    rwa [sq_abs] at h
  have hgn : ((Work.FIPlan.gnorm π : ℕ) : ℝ)
      = ((π.re : ℤ) : ℝ) ^ 2 + ((π.im : ℤ) : ℝ) ^ 2 :=
    Work.FIArea3.gnorm_eq_re_sq_add_im_sq π
  have hsqrt_le : Real.sqrt (2 * Pa.N) ≤ Pa.N + 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg Pa.N]⟩
  have hKsq : (Work.FIArea6.ncKb Pa : ℝ) ^ 2 ≤ (Real.sqrt (2 * Pa.N) + 1) ^ 2 := by
    have hfac1 : 0 ≤ Real.sqrt (2 * Pa.N) + 1 - (Work.FIArea6.ncKb Pa : ℝ) := by linarith
    have hfac2 : 0 ≤ Real.sqrt (2 * Pa.N) + 1 + (Work.FIArea6.ncKb Pa : ℝ) := by linarith
    nlinarith [hfac1, hfac2]
  rw [hgn]
  have hsqr : (Real.sqrt (2 * Pa.N)) ^ 2 = 2 * Pa.N := Real.sq_sqrt (by linarith)
  calc ((π.re : ℤ) : ℝ) ^ 2 + ((π.im : ℤ) : ℝ) ^ 2
      ≤ 2 * (Work.FIArea6.ncKb Pa : ℝ) ^ 2 := by linarith
    _ ≤ 2 * (Real.sqrt (2 * Pa.N) + 1) ^ 2 := by linarith
    _ = 2 * (2 * Pa.N + 2 * Real.sqrt (2 * Pa.N) + 1) := by nlinarith [hsqr]
    _ ≤ 16 * Pa.N := by linarith [hsqrt_le, hN1]

/-- `1 ≤ ncRad Pa π` on `ncPi Pa`. -/
lemma ncRad_ge_one (Pa : Work.FITop.Params) {π : GaussianInt} (hπ : π ∈ ncPi Pa) :
    1 ≤ ncRad Pa π := by
  have hg : (0 : ℝ) < (Work.FIPlan.gnorm π : ℝ) := gnorm_pos_of_mem_ncPi Pa hπ
  have hrpos : 0 < Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) :=
    Real.sqrt_pos.mpr (div_pos (by linarith [Pa.hN1] : (0 : ℝ) < 8 * Pa.N) hg)
  have hceil : 1 ≤ Nat.ceil (Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ))) := by
    rcases Nat.eq_zero_or_pos (Nat.ceil (Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ))))
      with h0 | hpos
    · exfalso
      have hle := Nat.le_ceil (Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)))
      rw [h0] at hle
      simp only [Nat.cast_zero] at hle
      linarith
    · exact hpos
  unfold ncRad
  exact_mod_cast hceil

/-- `(2·ncRad Pa π + 3)² ≤ 1568·N/|π|²` on `ncPi Pa`. -/
lemma ncRad_sq_le (Pa : Work.FITop.Params) {π : GaussianInt} (hπ : π ∈ ncPi Pa) :
    (2 * (ncRad Pa π : ℝ) + 3) ^ 2 ≤ 1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ) := by
  have hg : (0 : ℝ) < (Work.FIPlan.gnorm π : ℝ) := gnorm_pos_of_mem_ncPi Pa hπ
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  set r : ℝ := Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) with hrdef
  have hargp : 0 < 8 * Pa.N / (Work.FIPlan.gnorm π : ℝ) :=
    div_pos (by linarith [Pa.hN1] : (0 : ℝ) < 8 * Pa.N) hg
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hargp
  have hrt : r ^ 2 = 8 * Pa.N / (Work.FIPlan.gnorm π : ℝ) := by
    rw [hrdef]; exact Real.sq_sqrt hargp.le
  have hceil : (ncRad Pa π : ℝ) < r + 1 := by
    have h := Nat.ceil_lt_add_one hrpos.le
    simpa [ncRad, hrdef] using h
  have hg16 : (Work.FIPlan.gnorm π : ℝ) ≤ 16 * Pa.N := ncPi_gnorm_le_16 Pa hπ
  have hrge : (1 : ℝ) / 2 ≤ r := by
    have hquarter : (1 : ℝ) / 4 ≤ 8 * Pa.N / (Work.FIPlan.gnorm π : ℝ) := by
      rw [le_div_iff₀ hg]
      nlinarith [hg16, hN0]
    calc (1 : ℝ) / 2 = Real.sqrt ((1 : ℝ) / 4) := by
          rw [show (1 : ℝ) / 4 = ((1 : ℝ) / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) := Real.sqrt_le_sqrt hquarter
      _ = r := by rw [hrdef]
  have hrad1 : (1 : ℝ) ≤ (ncRad Pa π : ℝ) := by
    have := ncRad_ge_one Pa hπ
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ 2 * (ncRad Pa π : ℝ) + 3 := by linarith
  have hbound : 2 * (ncRad Pa π : ℝ) + 3 ≤ 12 * r := by linarith
  have hsq : (2 * (ncRad Pa π : ℝ) + 3) ^ 2 ≤ (12 * r) ^ 2 :=
    pow_le_pow_left₀ hnn hbound 2
  have hNdiv : (0 : ℝ) ≤ Pa.N / (Work.FIPlan.gnorm π : ℝ) := by positivity
  calc (2 * (ncRad Pa π : ℝ) + 3) ^ 2 ≤ (12 * r) ^ 2 := hsq
    _ = 144 * r ^ 2 := by ring
    _ = 144 * (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) := by rw [hrt]
    _ = 1152 * (Pa.N / (Work.FIPlan.gnorm π : ℝ)) := by ring
    _ ≤ 1568 * (Pa.N / (Work.FIPlan.gnorm π : ℝ)) := by linarith
    _ = 1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ) := by ring

/-- `(1 + log(2·ncRad Pa π + 3))² ≤ 36·(1 + log(2+N))²` on `ncPi Pa`.

Route: `2·ncRad + 3 ≤ 2N+9 ≤ 11(2+N) ≤ (2+N)^4` (as `N ≥ 1`), so
`log(2·ncRad+3) ≤ 4log(2+N)` and `1 + 4log(2+N) ≤ 6(1 + log(2+N))`. -/
lemma ncRad_log_le (Pa : Work.FITop.Params) {π : GaussianInt} (hπ : π ∈ ncPi Pa) :
    (1 + Real.log (2 * (ncRad Pa π : ℝ) + 3)) ^ 2
      ≤ 36 * (1 + Real.log (2 + Pa.N)) ^ 2 := by
  have hg : (0 : ℝ) < (Work.FIPlan.gnorm π : ℝ) := gnorm_pos_of_mem_ncPi Pa hπ
  have hg1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm π : ℝ) := one_le_gnorm_of_mem_ncPi Pa hπ
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  set r : ℝ := Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) with hrdef
  have hargp : 0 < 8 * Pa.N / (Work.FIPlan.gnorm π : ℝ) :=
    div_pos (by linarith : (0 : ℝ) < 8 * Pa.N) hg
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hargp
  have hceil : (ncRad Pa π : ℝ) < r + 1 := by
    have h := Nat.ceil_lt_add_one hrpos.le
    simpa [ncRad, hrdef] using h
  have hrn : r ≤ Pa.N + 2 := by
    have hx : 8 * Pa.N / (Work.FIPlan.gnorm π : ℝ) ≤ 8 * Pa.N := by
      rw [div_le_iff₀ hg]
      nlinarith [hg1, hN0]
    calc r = Real.sqrt (8 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) := by rw [hrdef]
      _ ≤ Real.sqrt (8 * Pa.N) := Real.sqrt_le_sqrt hx
      _ ≤ Pa.N + 2 := by
          rw [Real.sqrt_le_iff]
          exact ⟨by linarith, by nlinarith [sq_nonneg (Pa.N - 2)]⟩
  have hargp2 : 0 < 2 * (ncRad Pa π : ℝ) + 3 := by
    have h1 : (1 : ℝ) ≤ (ncRad Pa π : ℝ) := by
      have := ncRad_ge_one Pa hπ
      exact_mod_cast this
    linarith
  -- the numeric chain `2·ncRad+3 ≤ (2+N)^4`
  have h2r : 2 * (ncRad Pa π : ℝ) + 3 ≤ 2 * Pa.N + 9 := by linarith
  have h11 : 2 * Pa.N + 9 ≤ 11 * (2 + Pa.N) := by linarith
  have h3 : (3 : ℝ) ≤ 2 + Pa.N := by linarith
  have h9 : (9 : ℝ) ≤ (2 + Pa.N) ^ 2 := by nlinarith [h3, sq_nonneg (2 + Pa.N - 3)]
  have hcube : (11 : ℝ) ≤ (2 + Pa.N) ^ 3 := by nlinarith [h9, h3]
  have hpow : 11 * (2 + Pa.N) ≤ (2 + Pa.N) ^ 4 := by nlinarith [hcube, h3]
  have hlog : Real.log (2 * (ncRad Pa π : ℝ) + 3) ≤ 4 * Real.log (2 + Pa.N) := by
    have hle : 2 * (ncRad Pa π : ℝ) + 3 ≤ (2 + Pa.N) ^ 4 := le_trans (le_trans h2r h11) hpow
    have h1 : Real.log (2 * (ncRad Pa π : ℝ) + 3) ≤ Real.log ((2 + Pa.N) ^ 4) :=
      Real.log_le_log hargp2 hle
    have hp4 : Real.log ((2 + Pa.N) ^ 4) = 4 * Real.log (2 + Pa.N) := by
      rw [Real.log_pow]; push_cast; ring
    linarith
  have htarget : 1 + Real.log (2 * (ncRad Pa π : ℝ) + 3) ≤ 6 * (1 + Real.log (2 + Pa.N)) := by
    have hL0 : (0 : ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
    linarith
  have hnn : (0 : ℝ) ≤ 1 + Real.log (2 * (ncRad Pa π : ℝ) + 3) := by
    have h1 : (1 : ℝ) ≤ 2 * (ncRad Pa π : ℝ) + 3 := by
      have hr1 : (1 : ℝ) ≤ (ncRad Pa π : ℝ) := by
        have := ncRad_ge_one Pa hπ
        exact_mod_cast this
      linarith
    have h2 : 0 ≤ Real.log (2 * (ncRad Pa π : ℝ) + 3) := Real.log_nonneg h1
    linarith
  calc (1 + Real.log (2 * (ncRad Pa π : ℝ) + 3)) ^ 2
      ≤ (6 * (1 + Real.log (2 + Pa.N))) ^ 2 := pow_le_pow_left₀ hnn htarget 2
    _ = 36 * (1 + Real.log (2 + Pa.N)) ^ 2 := by ring

/-! ## 2. The reciprocal logarithmic sum over a box, with the explicit constant `100` -/

/-- `invPair m n = 1/(m² + n²)`. -/
private def invPair (m n : ℕ) : ℝ := (((m : ℝ) ^ 2 + (n : ℝ) ^ 2))⁻¹

private lemma invPair_nonneg (m n : ℕ) : 0 ≤ invPair m n := by
  unfold invPair; positivity

/-- **The explicit-constant form of the second conjunct of `Work.FIArea1.gnorm_inv_sums`**:
`Σ_{d ∈ gBox R} |d|^{-2} ≤ 100(1 + log(R+2))` for `R ≥ 0`. -/
lemma gBox_inv_sum_le (R : ℤ) (hR : 0 ≤ R) :
    (∑ d ∈ Work.FIPlan.gBox R, ((Work.FIPlan.gnorm d : ℝ))⁻¹)
      ≤ 100 * (1 + Real.log ((R : ℝ) + 2)) := by
  have hRc : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hstep : (∑ d ∈ Work.FIPlan.gBox R, ((Work.FIPlan.gnorm d : ℝ))⁻¹)
      = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R,
          invPair a.natAbs b.natAbs := by
    rw [Work.FIArea1.sum_gBox_eq]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Work.FIArea1.gnorm_mk_cast a b, invPair]
  rw [hstep]
  have hN : (∑ m ∈ Finset.Icc 0 R.natAbs, ∑ n ∈ Finset.Icc 0 R.natAbs, invPair m n)
      ≤ 4 + 2 * (1 + Real.log (R.natAbs : ℝ)) := by
    rw [Work.FIArea1.sum_Icc_zero_split]
    have hrow : (∑ n ∈ Finset.Icc 0 R.natAbs, invPair 0 n) ≤ 2 := by
      rw [Work.FIArea1.Icc_zero_eq_insert,
        Finset.sum_insert (by simp [Finset.mem_Icc]),
        show invPair 0 0 = 0 by simp [invPair], zero_add]
      refine le_trans (le_of_eq ?_) (Work.FIArea1.sum_Icc_inv_sq_le_two R.natAbs)
      apply Finset.sum_congr rfl
      intro n _
      simp [invPair]
    have hcol : (∑ m ∈ Finset.Icc 1 R.natAbs, invPair m 0) ≤ 2 := by
      refine le_trans (le_of_eq ?_) (Work.FIArea1.sum_Icc_inv_sq_le_two R.natAbs)
      apply Finset.sum_congr rfl
      intro n _
      simp [invPair]
    have hcore : (∑ m ∈ Finset.Icc 1 R.natAbs, ∑ n ∈ Finset.Icc 1 R.natAbs, invPair m n)
        ≤ 2 * (1 + Real.log (R.natAbs : ℝ)) := Work.FIArea1.sum_inv_quad_le R.natAbs
    linarith
  refine le_trans (Work.FIArea1.pair_natAbs_le R hR invPair invPair_nonneg) ?_
  have hcast : ((R.natAbs : ℕ) : ℝ) = (R : ℝ) := by
    rw [← Int.cast_natCast (R.natAbs), Int.natAbs_of_nonneg hR]
  have hlog : Real.log (R.natAbs : ℝ) ≤ Real.log ((R : ℝ) + 2) := by
    rcases eq_or_lt_of_le hR with h | h
    · rw [← h]
      have h1 : Real.log (((0 : ℤ).natAbs : ℕ) : ℝ) = 0 := by simp
      rw [h1]
      exact Real.log_nonneg (by norm_num)
    · rw [hcast]
      exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  have hlog2 : (0 : ℝ) ≤ Real.log ((R : ℝ) + 2) := Real.log_nonneg (by linarith)
  nlinarith [hN, hlog, hlog2]

/-- **The reciprocal-square mass of the candidate primes**:
`Σ_{π ∈ ncPi Pa} |π|^{-4} ≤ 300(1 + log(2+N))/Pz`. -/
lemma ncPi_inv_sq_sum_le (Pa : Work.FITop.Params) :
    (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2)
      ≤ 300 * (1 + Real.log (2 + Pa.N)) / (Pa.Pz : ℝ) := by
  have hPzpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have := Pa.hP2
    exact_mod_cast (by omega : 0 < Pa.Pz)
  have hpt : ∀ π ∈ ncPi Pa,
      ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2
        ≤ (Pa.Pz : ℝ)⁻¹ * ((Work.FIPlan.gnorm π : ℝ))⁻¹ := by
    intro π hπ
    have hgpos : (0 : ℝ) < (Work.FIPlan.gnorm π : ℝ) := gnorm_pos_of_mem_ncPi Pa hπ
    have hPzle : (Pa.Pz : ℝ) ≤ (Work.FIPlan.gnorm π : ℝ) := by
      have := gnorm_gt_Pz_of_mem_ncPi hπ
      exact_mod_cast (le_of_lt this)
    have hinv : ((Work.FIPlan.gnorm π : ℝ))⁻¹ ≤ (Pa.Pz : ℝ)⁻¹ :=
      (inv_le_inv₀ hgpos hPzpos).mpr hPzle
    calc ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2
        = ((Work.FIPlan.gnorm π : ℝ))⁻¹ * ((Work.FIPlan.gnorm π : ℝ))⁻¹ := by ring
      _ ≤ (Pa.Pz : ℝ)⁻¹ * ((Work.FIPlan.gnorm π : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
  have hsum1 : (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2)
      ≤ (Pa.Pz : ℝ)⁻¹ * (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hsum2 : (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹)
      ≤ 300 * (1 + Real.log (2 + Pa.N)) := by
    have hsub : ncPi Pa ⊆ Work.FIPlan.gBox (Work.FIArea6.ncKb Pa) :=
      fun x hx => (mem_ncPi.mp hx).1
    have h1 : (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹)
        ≤ ∑ d ∈ Work.FIPlan.gBox (Work.FIArea6.ncKb Pa),
            ((Work.FIPlan.gnorm d : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have h2 : (∑ d ∈ Work.FIPlan.gBox (Work.FIArea6.ncKb Pa),
          ((Work.FIPlan.gnorm d : ℝ))⁻¹)
        ≤ 100 * (1 + Real.log ((Work.FIArea6.ncKb Pa : ℝ) + 2)) := by
      refine gBox_inv_sum_le _ ?_
      simp [Work.FIArea6.ncKb]
    have h3 : 1 + Real.log ((Work.FIArea6.ncKb Pa : ℝ) + 2)
        ≤ 3 * (1 + Real.log (2 + Pa.N)) := by
      have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
      have hK0 : (0 : ℝ) ≤ (Work.FIArea6.ncKb Pa : ℝ) := by
        have : (0 : ℤ) ≤ Work.FIArea6.ncKb Pa := by simp [Work.FIArea6.ncKb]
        exact_mod_cast this
      have hKlt : (Work.FIArea6.ncKb Pa : ℝ) < Real.sqrt (2 * Pa.N) + 1 := by
        have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * Pa.N))
        simpa [Work.FIArea6.ncKb] using h
      have hsq : Real.sqrt (2 * Pa.N) ≤ Pa.N + 1 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by linarith, by nlinarith [sq_nonneg Pa.N]⟩
      have hKle : (Work.FIArea6.ncKb Pa : ℝ) + 2 ≤ Pa.N + 4 := by linarith
      have hsq2 : Pa.N + 4 ≤ (2 + Pa.N) ^ 2 := by nlinarith [hN1, sq_nonneg Pa.N]
      have harg : 0 < (Work.FIArea6.ncKb Pa : ℝ) + 2 := by linarith
      have hp2 : Real.log ((2 + Pa.N) ^ 2) = 2 * Real.log (2 + Pa.N) := by
        rw [Real.log_pow]; push_cast; ring
      have hlog : Real.log ((Work.FIArea6.ncKb Pa : ℝ) + 2) ≤ 2 * Real.log (2 + Pa.N) := by
        have h := Real.log_le_log harg (le_trans hKle hsq2)
        linarith
      have hL0 : (0 : ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
      linarith
    linarith
  calc (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2)
      ≤ (Pa.Pz : ℝ)⁻¹ * (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹) := hsum1
    _ = (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹) / (Pa.Pz : ℝ) := by
        rw [inv_mul_eq_div]
    _ ≤ 300 * (1 + Real.log (2 + Pa.N)) / (Pa.Pz : ℝ) :=
        div_le_div_of_nonneg_right hsum2 hPzpos.le

/-! ## 3. The box `τ`-average with the explicit constant `1024` -/

/-- The average of `τ(|z|²)` over the box `gBox R`, with the explicit constant of
`Work.FIArea3.tau_gnorm_gBox_bound`. -/
theorem tauG_gBox_explicit (R : ℤ) (hR : 1 ≤ R) :
    (∑ z ∈ Work.FIPlan.gBox R, tauG z)
      ≤ 1024 * (2 * (R : ℝ) + 3) ^ 2
          * (1 + Real.log (2 * (R : ℝ) + 3)) ^ (2 : ℕ) := by
  show (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 1024 * (2 * (R : ℝ) + 3) ^ 2
          * (1 + Real.log (2 * (R : ℝ) + 3)) ^ (2 : ℕ)
  have hR0 : (0 : ℤ) ≤ R := by omega
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  set D : ℕ := Nat.ceil (2 * (R : ℝ) + 2) with hDdef
  have hDge : 2 * (R : ℝ) + 2 ≤ (D : ℝ) := Nat.le_ceil _
  have hDlt : (D : ℝ) < 2 * (R : ℝ) + 3 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (R : ℝ) + 2 by linarith)
    linarith
  have hDle : (D : ℝ) ≤ 2 * (R : ℝ) + 3 := le_of_lt hDlt
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hD1 : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · rw [h0] at hD0; norm_num at hD0
    · exact hpos
  -- Step 1: the pointwise hyperbola bound
  have hpt : ∀ z ∈ Work.FIPlan.gBox R,
      (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        ≤ 2 * (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    intro z hz
    refine Work.FIArea3.tau_le_two_mul_card_dvd _ _ ?_
    have hg : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
      rw [Work.FIArea3.gnorm_eq_re_sq_add_im_sq z]
      obtain ⟨hre, him⟩ := mem_gBox_coords hz
      rw [Finset.mem_Icc] at hre him
      have h1 : ((z.re : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hre.2
      have h1' : -((R : ℝ)) ≤ ((z.re : ℤ) : ℝ) := by exact_mod_cast hre.1
      have h3 : ((z.im : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast him.2
      have h3' : -((R : ℝ)) ≤ ((z.im : ℤ) : ℝ) := by exact_mod_cast him.1
      nlinarith [sq_nonneg (((z.re : ℤ) : ℝ)), sq_nonneg (((z.im : ℤ) : ℝ))]
    have hsqrt2 : Real.sqrt (2 * (R : ℝ) ^ 2) = Real.sqrt 2 * (R : ℝ) := by
      have hsq : 2 * (R : ℝ) ^ 2 = (Real.sqrt 2 * (R : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsq, Real.sqrt_sq (by positivity)]
    calc Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ)
        ≤ Real.sqrt (2 * (R : ℝ) ^ 2) := Real.sqrt_le_sqrt hg
      _ = Real.sqrt 2 * (R : ℝ) := hsqrt2
      _ ≤ (D : ℝ) := by
          have h4 : Real.sqrt 2 ≤ 2 := by
            rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
          nlinarith [Real.sqrt_nonneg 2, hR1, hDge]
  -- Step 2: exchange the order of summation
  have hswap : (∑ z ∈ Work.FIPlan.gBox R,
        (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ))
      = ∑ d ∈ Finset.Icc 1 D,
          (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    have h1 : ∀ z : GaussianInt,
        (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          = ∑ d ∈ Finset.Icc 1 D, (if d ∣ Work.FIPlan.gnorm z then (1 : ℝ) else 0) := by
      intro z
      rw [Finset.card_filter]
      push_cast
      rfl
    have h2 : ∀ d : ℕ,
        (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
          = ∑ z ∈ Work.FIPlan.gBox R, (if d ∣ Work.FIPlan.gnorm z then (1 : ℝ) else 0) := by
      intro d
      rw [Finset.card_filter]
      push_cast
      rfl
    simp only [h1, h2]
    exact Finset.sum_comm
  -- Step 3: bound each count
  have hcount : ∀ d ∈ Finset.Icc 1 D,
      (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hsq : (0 : ℝ) ≤ (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by positivity
    have hcast : (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
        ≤ (d : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by
      have h := Work.FIArea3.rho_le_four_pow d hd1
      calc (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
          ≤ ((d * d.divisors.card : ℕ) : ℝ) := by exact_mod_cast h
        _ = (d : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by push_cast; ring
    calc (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
            * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 :=
          Work.FIArea3.card_gBox_filter_dvd_gnorm R d hd1
      _ ≤ ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hcast hsq
  -- Step 4: the divisor sums
  have hS1 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
      ≤ (1 + Real.log (D : ℝ)) ^ 2 :=
    Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le D hD1
  have hS2 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
      ≤ (D : ℝ) * (1 + Real.log (D : ℝ)) :=
    Commons.NumberTheory.DivisorSum.sum_card_divisors_le D hD1
  have hS3 : (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
      ≤ (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ))) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (D : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      have hdD : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2
      exact mul_le_mul_of_nonneg_right hdD (by positivity)
    calc (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 D, (D : ℝ) * ((d.divisors.card : ℕ) : ℝ) := h1
      _ = (D : ℝ) * ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ))) :=
          mul_le_mul_of_nonneg_left hS2 hD0.le
  -- assemble
  have hstep : (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ 2 * ∑ d ∈ Finset.Icc 1 D,
          (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
            + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
            + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))) := by
    calc (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ ∑ z ∈ Work.FIPlan.gBox R,
            2 * (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ z ∈ Work.FIPlan.gBox R,
            (((Finset.Icc 1 D).filter (fun d => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
          rw [Finset.mul_sum]
      _ = 2 * ∑ d ∈ Finset.Icc 1 D,
            (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
          rw [hswap]
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 D,
            ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
          have h := Finset.sum_le_sum hcount
          linarith
      _ = 2 * ∑ d ∈ Finset.Icc 1 D,
          (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
            + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
            + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
          have hd0 : (d : ℝ) ≠ 0 := by positivity
          field_simp
          ring
  have hpieces : (∑ d ∈ Finset.Icc 1 D,
        (4 * (R : ℝ) ^ 2 * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
          + 8 * (R : ℝ) * ((d.divisors.card : ℕ) : ℝ)
          + 4 * ((d : ℝ) * ((d.divisors.card : ℕ) : ℝ))))
      = 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
        + 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
        + 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  rw [hpieces] at hstep
  -- final arithmetic
  set L : ℝ := 1 + Real.log (D : ℝ) with hLdef
  set Lp : ℝ := 1 + Real.log (2 * (R : ℝ) + 3) with hLpdef
  have hL0 : 1 ≤ L := by
    have : (0 : ℝ) ≤ Real.log (D : ℝ) := Real.log_nonneg (by linarith)
    rw [hLdef]; linarith
  have hLp0 : 1 ≤ Lp := by
    have : (0 : ℝ) ≤ Real.log (2 * (R : ℝ) + 3) := Real.log_nonneg (by linarith)
    rw [hLpdef]; linarith
  have hLL : L ≤ Lp := by
    have : Real.log (D : ℝ) ≤ Real.log (2 * (R : ℝ) + 3) := Real.log_le_log hD0 hDle
    rw [hLdef, hLpdef]; linarith
  have hLL2 : L ^ 2 ≤ Lp ^ 2 := pow_le_pow_left₀ (by linarith) hLL 2
  have hRL : (R : ℝ) ≤ 2 * (R : ℝ) + 3 := by linarith
  have hRsq : (R : ℝ) ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 := by nlinarith [hR1]
  have hRD : (R : ℝ) * (D : ℝ) ≤ (2 * (R : ℝ) + 3) ^ 2 := by
    nlinarith [hR1, hDle, hD0, hRpos]
  have hDsq : (D : ℝ) ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 := by
    have h := mul_le_mul hDle hDle (le_of_lt hD0) (by linarith : (0 : ℝ) ≤ 2 * (R : ℝ) + 3)
    nlinarith [h]
  have hLp_le : Lp ≤ Lp ^ 2 := by nlinarith [hLp0]
  have hnonneg : (0 : ℝ) ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by positivity
  have hB : 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
      + 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
      + 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
      ≤ 512 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
    have hb1 : 4 * (R : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
        ≤ 4 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h1 : (R : ℝ) ^ 2 * L ^ 2 ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
        have := mul_le_mul hRsq hLL2 (sq_nonneg L) (by positivity : (0 : ℝ) ≤ (2 * (R : ℝ) + 3) ^ 2)
        linarith [this]
      have h2 := mul_le_mul_of_nonneg_left hS1 (by positivity : (0 : ℝ) ≤ 4 * (R : ℝ) ^ 2)
      nlinarith [h1, h2]
    have hb2 : 8 * (R : ℝ) * (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℕ) : ℝ))
        ≤ 8 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h2 : (D : ℝ) * (1 + Real.log (D : ℝ)) ≤ (2 * (R : ℝ) + 3) * Lp := by
        rw [hLpdef]
        exact mul_le_mul hDle hLL (by linarith [hD0]) (by linarith)
      have h3 : (R : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ)))
          ≤ (2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * Lp) :=
        mul_le_mul hRL h2 (by positivity) (by linarith)
      have h4 := mul_le_mul_of_nonneg_left hS2 (by positivity : (0 : ℝ) ≤ 8 * (R : ℝ))
      have h5 : (R : ℝ) * ((2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * Lp))
          = ((2 * (R : ℝ) + 3) ^ 2 * Lp) * (R : ℝ) := by ring
      nlinarith [h3, h4, h5, hnonneg, hLp0, hRpos, hRL]
    have hb3 : 4 * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * ((d.divisors.card : ℕ) : ℝ))
        ≤ 4 * (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 := by
      have h2 : (D : ℝ) * ((D : ℝ) * (1 + Real.log (D : ℝ)))
          ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp := by
        rw [hLpdef]
        have h3 : (D : ℝ) * ((D : ℝ) * L) ≤ (2 * (R : ℝ) + 3) * ((2 * (R : ℝ) + 3) * L) :=
          mul_le_mul hDle (mul_le_mul hDle (le_refl L) (by linarith) (by linarith)) (by positivity)
            (by linarith)
        nlinarith [h3]
      have h4 := mul_le_mul_of_nonneg_left hS3 (by norm_num : (0 : ℝ) ≤ 4)
      have h5 : (2 * (R : ℝ) + 3) ^ 2 * Lp ≤ (2 * (R : ℝ) + 3) ^ 2 * Lp ^ 2 :=
        mul_le_mul_of_nonneg_left hLp_le (by positivity)
      linarith [h2, h4, h5]
    linarith [hb1, hb2, hb3, hnonneg]
  linarith [hstep, hB]

/-! ## 4. The arithmetic endgame -/

/-- **The arithmetic endgame of the non-coprime mass**:
`Σ_{π ∈ ncPi} (τ(|π|²)·Σ_{w ∈ gBox (ncRad Pa π)} τ(|w|²))² ≤ 10^20·N²(1+log(2+N))^14/Pz`.

Route.  `τ(|π|²) ≤ 3` for `π ∈ ncPi` (`prime_of_mem_ncPi` + `tauG_le_three_of_prime`).  The box
`τ`-sum is bounded by `tauG_gBox_explicit`; for `R = ncRad Pa π ≥ 1` one has
`(2R+3)² ≤ 1568·N/|π|²` and `(1+log(2R+3))² ≤ 36·(1+log(2+N))²` (`ncRad_sq_le`, `ncRad_log_le`),
so `Σ_{π∈ncPi}(τ(|π|²)Σ_w τ)² ≤ 9·1024²·1568²·36²·N²(1+log(2+N))^4·Σ_{π∈ncPi}|π|^{-4}`, and since
`|π|² > Pz` on `ncPi`, `Σ_{π∈ncPi}|π|^{-4} ≤ 300(1+log(2+N))/Pz`
(`ncPi_inv_sq_sum_le`).  The constants assemble far below `10^20`, and the exponent
`4+1 = 5 ≤ 14` is absorbed by `1+log(2+N) ≥ 1` (`Pa.hN1`). -/
theorem ncMass_arith (Pa : Work.FITop.Params) :
    (∑ π ∈ Work.FIArea6.S16ErrTwo.ncPi Pa,
        (Work.FIArea6.S16ErrTwo.tauG π
          * (∑ w ∈ Work.FIPlan.gBox (Work.FIArea6.S16ErrTwo.ncRad Pa π),
              Work.FIArea6.S16ErrTwo.tauG w)) ^ 2)
      ≤ 10 ^ 20 * Pa.N ^ (2 : ℕ) * (1 + Real.log (2 + Pa.N)) ^ (14 : ℕ) / (Pa.Pz : ℝ) := by
  set L : ℝ := 1 + Real.log (2 + Pa.N) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have : (0 : ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    linarith
  have hPzpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
    have := Pa.hP2
    exact_mod_cast (by omega : 0 < Pa.Pz)
  set C0 : ℝ := 9 * 1024 ^ 2 * 1568 ^ 2 * 36 ^ 2 with hC0def
  have hpt : ∀ π ∈ ncPi Pa,
      (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2
        ≤ C0 * Pa.N ^ 2 * L ^ 4 * ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2 := by
    intro π hπ
    have hsq := ncRad_sq_le Pa hπ
    have hlog := ncRad_log_le Pa hπ
    have hrad1 := ncRad_ge_one Pa hπ
    have htau : tauG π ≤ 3 := tauG_le_three_of_prime (prime_of_mem_ncPi hπ)
    have hbox : (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)
        ≤ 1024 * (2 * (ncRad Pa π : ℝ) + 3) ^ 2
            * (1 + Real.log (2 * (ncRad Pa π : ℝ) + 3)) ^ (2 : ℕ) :=
      tauG_gBox_explicit (ncRad Pa π) hrad1
    have hboxnn : 0 ≤ ∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w :=
      Finset.sum_nonneg (fun w _ => tauG_nonneg w)
    set A : ℝ := 2 * (ncRad Pa π : ℝ) + 3 with hAdef
    set B : ℝ := 1 + Real.log (2 * (ncRad Pa π : ℝ) + 3) with hBdef
    have h1 : tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)
        ≤ 3 * (1024 * A ^ 2 * B ^ 2) := by
      rw [hAdef, hBdef]
      exact mul_le_mul htau hbox hboxnn (by norm_num)
    have h1nn : 0 ≤ tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w) :=
      mul_nonneg (tauG_nonneg π) hboxnn
    have h2 : (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2
        ≤ (3 * (1024 * A ^ 2 * B ^ 2)) ^ 2 := pow_le_pow_left₀ h1nn h1 2
    have hA2 : A ^ 2 ≤ 1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ) := by
      rw [hAdef]; exact hsq
    have hB2 : B ^ 2 ≤ 36 * L ^ 2 := by
      rw [hBdef]; exact hlog
    have hA4 : A ^ 4 ≤ (1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
      calc A ^ 4 = (A ^ 2) ^ 2 := by ring
        _ ≤ (1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hA2 2
    have hB4 : B ^ 4 ≤ (36 * L ^ 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
      calc B ^ 4 = (B ^ 2) ^ 2 := by ring
        _ ≤ (36 * L ^ 2) ^ 2 := pow_le_pow_left₀ h0 hB2 2
    calc (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2
        ≤ (3 * (1024 * A ^ 2 * B ^ 2)) ^ 2 := h2
      _ = 9 * 1024 ^ 2 * A ^ 4 * B ^ 4 := by ring
      _ ≤ 9 * 1024 ^ 2 * (1568 * Pa.N / (Work.FIPlan.gnorm π : ℝ)) ^ 2 * (36 * L ^ 2) ^ 2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hA4 (by norm_num : (0 : ℝ) ≤ 9 * 1024 ^ 2)) hB4
            (by positivity) (by positivity)
      _ = C0 * Pa.N ^ 2 * L ^ 4 * ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2 := by
          rw [hC0def, inv_pow]
          field_simp
  have hsum : (∑ π ∈ ncPi Pa,
        (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2)
      ≤ C0 * Pa.N ^ 2 * L ^ 4 * (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  have hInv : (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2)
      ≤ 300 * L / (Pa.Pz : ℝ) := by
    simpa [hLdef] using ncPi_inv_sq_sum_le Pa
  have hconst : C0 * 300 ≤ (10 : ℝ) ^ 20 := by
    rw [hC0def]; norm_num
  have hL5 : L ^ 5 ≤ L ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
  calc (∑ π ∈ ncPi Pa,
        (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2)
      ≤ C0 * Pa.N ^ 2 * L ^ 4 * (∑ π ∈ ncPi Pa, ((Work.FIPlan.gnorm π : ℝ))⁻¹ ^ 2) := hsum
    _ ≤ C0 * Pa.N ^ 2 * L ^ 4 * (300 * L / (Pa.Pz : ℝ)) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
    _ = (C0 * 300) * Pa.N ^ 2 * L ^ 5 / (Pa.Pz : ℝ) := by ring
    _ ≤ 10 ^ 20 * Pa.N ^ 2 * L ^ 14 / (Pa.Pz : ℝ) := by
        apply div_le_div_of_nonneg_right _ hPzpos.le
        have hstep1 : (C0 * 300) * Pa.N ^ 2 * L ^ 5 ≤ (10 : ℝ) ^ 20 * Pa.N ^ 2 * L ^ 5 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst (by positivity))
            (by positivity)
        have hstep2 : (10 : ℝ) ^ 20 * Pa.N ^ 2 * L ^ 5 ≤ (10 : ℝ) ^ 20 * Pa.N ^ 2 * L ^ 14 :=
          mul_le_mul_of_nonneg_left hL5 (by positivity)
        linarith

end

end Work.FIArea6.S16ErrTwo
