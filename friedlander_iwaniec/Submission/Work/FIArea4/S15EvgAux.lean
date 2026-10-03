import Mathlib
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.p14_uncond

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# FI §15: the support scale of the stratum arrays `S15strU`

The stratum array `S15strU β u t ℓ e` is supported (in the coefficient `β`) on the points
`z = ⟨e·ρ, s⟩` whose image `⟨e·ρ, s⟩` lies in the polar box, hence has norm `≤ (1+θ)N ≤ 2N` and
in particular `(e·ρ)² ≤ 2N`, `s² ≤ 2N`.  This module fixes the resulting *support scale*
`√(2N)` and the three integer box parameters of the variance chain:

* `S15RR Pa = ⌈√(2N)⌉`: the `Im`-index bound of every stratum, and the `e`-cutoff beyond which
  the stratum array vanishes;
* `S15Re Pa e = ⌈√(2N)/e⌉`: the `Re`-index bound of the stratum `e`;
* `S15E0 Pa = ⌊√(2N)⌋`: the cutoff for `e` (for `e > S15E0 Pa` the stratum array is identically
  zero, so only `e ≤ S15E0 Pa` contribute to the variance sum);
* `S15RN Pa = ⌈√(4·N)⌉`: `Work.FITop.radN Pa` read as a natural number.
-/

/-- `√(2N)`, the support scale of the §15 stratum arrays. -/
def S15aN (Pa : Work.FITop.Params) : ℝ := Real.sqrt (2 * Pa.N)

/-- `⌈√(2N)⌉`, the `Im`-index bound of every stratum (and the cutoff for `e`). -/
def S15RR (Pa : Work.FITop.Params) : ℕ := ⌈S15aN Pa⌉₊

/-- `⌈√(2N)/e⌉`, the `Re`-index bound of the stratum `e`. -/
def S15Re (Pa : Work.FITop.Params) (e : ℕ) : ℕ := ⌈S15aN Pa / (e : ℝ)⌉₊

/-- `⌊√(2N)⌋`, the cutoff for the stratum parameter `e`: for `e > S15E0 Pa` the stratum array
`S15strU β u t ℓ e` vanishes identically. -/
def S15E0 (Pa : Work.FITop.Params) : ℕ := ⌊S15aN Pa⌋₊

/-- `⌈√(4N)⌉`, i.e. `Work.FITop.radN Pa` as a natural number. -/
def S15RN (Pa : Work.FITop.Params) : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊

lemma radN_eq_S15RN (Pa : Work.FITop.Params) : Work.FITop.radN Pa = (S15RN Pa : ℤ) := rfl

lemma S15aN_nonneg (Pa : Work.FITop.Params) : 0 ≤ S15aN Pa := Real.sqrt_nonneg _

lemma S15aN_ge_one (Pa : Work.FITop.Params) : 1 ≤ S15aN Pa := by
  rw [S15aN]
  have h0 : (0 : ℝ) ≤ 2 * Pa.N := by linarith [Pa.hN1]
  have h2 : (1 : ℝ) ≤ 2 * Pa.N := by linarith [Pa.hN1]
  have := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (2 * Pa.N), this]

lemma S15aN_sq (Pa : Work.FITop.Params) : S15aN Pa ^ 2 = 2 * Pa.N :=
  Real.sq_sqrt (by linarith [Pa.hN1])

/-- `θ ≤ 1`: `θ = (log x)^{-A'}` with `log x > 1` and `A' > 0`. -/
lemma S15theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx : 1 < Real.log (Pa.x : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hxl : 0 < Real.log (Pa.x : ℝ) := lt_trans one_pos hx
  have hA : 0 < Pa.A' := by linarith [Pa.hA, Pa.hA']
  have h1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) ^ Pa.A' := Real.one_le_rpow hx.le hA.le
  rw [Pa.hθ, Real.rpow_neg hxl.le]
  exact inv_le_one_of_one_le₀ h1

/-- `1 ≤ ⌈√(2N)⌉`. -/
lemma S15RR_ge_one (Pa : Work.FITop.Params) : 1 ≤ S15RR Pa :=
  Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le one_pos (S15aN_ge_one Pa))

/-- `1 ≤ ⌊√(2N)⌋`. -/
lemma S15E0_ge_one (Pa : Work.FITop.Params) : 1 ≤ S15E0 Pa :=
  (Nat.one_le_floor_iff (S15aN Pa)).mpr (S15aN_ge_one Pa)

/-- `⌈√(2N)⌉ ≤ 2√(2N)`. -/
lemma S15RR_le (Pa : Work.FITop.Params) : (S15RR Pa : ℝ) ≤ 2 * S15aN Pa := by
  have h : (S15RR Pa : ℝ) < S15aN Pa + 1 := Nat.ceil_lt_add_one (S15aN_nonneg Pa)
  have h1 : 1 ≤ S15aN Pa := S15aN_ge_one Pa
  linarith

/-- `⌊√(2N)⌋ ≤ √(2N)`. -/
lemma S15E0_le (Pa : Work.FITop.Params) : (S15E0 Pa : ℝ) ≤ S15aN Pa :=
  Nat.floor_le (S15aN_nonneg Pa)

/-- For `1 ≤ e` the `Re`-index bound satisfies `⌈√(2N)/e⌉ < √(2N)/e + 1`. -/
lemma S15Re_lt (Pa : Work.FITop.Params) {e : ℕ} (he : 1 ≤ e) :
    (S15Re Pa e : ℝ) < S15aN Pa / (e : ℝ) + 1 := by
  rw [S15Re]
  refine Nat.ceil_lt_add_one ?_
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  exact div_nonneg (S15aN_nonneg Pa) (le_of_lt hepos)

/-- For `e ≤ ⌊√(2N)⌋` the `Re`-index bound satisfies `⌈√(2N)/e⌉ ≤ 2√(2N)/e`. -/
lemma S15Re_le (Pa : Work.FITop.Params) {e : ℕ} (he : 1 ≤ e) (he' : e ≤ S15E0 Pa) :
    (S15Re Pa e : ℝ) ≤ 2 * S15aN Pa / (e : ℝ) := by
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hAe : (1 : ℝ) ≤ S15aN Pa / (e : ℝ) := by
    rw [le_div_iff₀ hepos, one_mul]
    exact le_trans (by exact_mod_cast he') (S15E0_le Pa)
  have hlt := S15Re_lt Pa he
  have h2 : S15aN Pa / (e : ℝ) + 1 ≤ 2 * (S15aN Pa / (e : ℝ)) := by linarith
  have h3 : 2 * (S15aN Pa / (e : ℝ)) = 2 * S15aN Pa / (e : ℝ) := by ring
  linarith [h3 ▸ h2]

/-- `1 ≤ ⌈√(2N)/e⌉` for every `e ≥ 1`. -/
lemma S15Re_ge_one (Pa : Work.FITop.Params) {e : ℕ} (he : 1 ≤ e) : 1 ≤ S15Re Pa e := by
  rw [S15Re]
  exact Nat.one_le_ceil_iff.mpr (div_pos (lt_of_lt_of_le one_pos (S15aN_ge_one Pa))
    (by exact_mod_cast he))

/-- `√(2N) ≤ radN Pa` (as a real number). -/
lemma S15aN_le_radN (Pa : Work.FITop.Params) : S15aN Pa ≤ (Work.FITop.radN Pa : ℝ) := by
  have h : (Work.FITop.radN Pa : ℤ) = ((S15RN Pa : ℕ) : ℤ) := rfl
  have h2 : S15aN Pa ≤ (S15RN Pa : ℝ) := by
    rw [S15aN, S15RN]
    have hN : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    have hle : 2 * Pa.N ≤ 4 * Pa.N := by linarith
    calc Real.sqrt (2 * Pa.N) ≤ Real.sqrt (4 * Pa.N) := Real.sqrt_le_sqrt hle
      _ ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℝ) := Nat.le_ceil _
  rw [Work.FITop.radN]
  exact_mod_cast h2

end

end Work.FIArea4
