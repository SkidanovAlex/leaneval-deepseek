import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.JutilaPieces.S3MainTermDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3PhiAsymptotic
import Submission.Work.LinnikAreas.JutilaPieces.S3HarmonicSum

/-!
# The `S₃` main term via the `Φ`-model (`JutilaPieces/S3RouteAux`)

Writing `x_q = N/(qz)` and `M = N/(qrt)`, the per-term algebra
`s3c(rt) = (π²/6)⁻¹ pfac(r)pfac(t)` (for coprime `r,t`) gives

`(N/q)·Φ(x_q) = Σ_{r,t ≤ ⌊x_q⌋, (r,t)=1} μ(r)μ(t)·s3c(rt)·M·Bcont(z,N,q,r,t)`

with `Bcont` the bracket with the *real* cut-off, so the continuous model `s3cont` of `Bz3Defs`
is exactly `Σ_q (N/q)·Φ(N/(qz))`.  Hence
`T − N log(N/z) = (s3exact − s3cont) + (s3cont − N log(N/z))`, with `|s3exact − s3cont| ≤ C·N`
by an elementary floor/bracket estimate and `|s3cont − N log(N/z)| ≤ C·N` from the proven
`S3PhiAsymptotic` (`|Φ(x) − 1| ≤ C/(log x)²`) plus `S3HarmonicSum`.
-/

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- Pointwise identity: the `s3cont` summand in terms of the `Φ`-summand. -/
lemma s3cont_term_eq (z N q r t : ℕ) (hq : q ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0)
    (hz : z ≠ 0) (hc : Nat.Coprime r t) :
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      (Work.LinnikAreas.Density4.BzS3.s3c (r * t) *
          ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
        (((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
            (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1)))
      = ((N : ℝ) / (q : ℝ)) *
          ((Real.pi ^ 2 / 6)⁻¹ *
            (if Nat.Coprime r t then
              s3w r * s3w t *
                ((Real.log (((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (r : ℝ)) - 1)
                  * (Real.log (((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (t : ℝ)) - 1) + 1)
            else 0)) := by
  simp only [if_pos hc]
  have h1 : ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)
      = ((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (r : ℝ) := by
    field_simp
  have h2 : ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)
      = ((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (t : ℝ) := by
    field_simp
  rw [h1, h2]
  have hc1 : Work.LinnikAreas.Density4.BzS3.s3c (r * t)
      = (Real.pi ^ 2 / 6)⁻¹ * (s3pfac r * s3pfac t) := by
    rw [show Work.LinnikAreas.Density4.BzS3.s3c (r * t)
        = (Real.pi ^ 2 / 6)⁻¹ * s3pfac (r * t) from rfl, s3pfac_mul hr ht hc]
  rw [hc1]
  unfold s3w s3pfac
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  field_simp

/-- **The continuous model as a `Φ`-sum.** -/
lemma s3cont_eq_phi_sum (z N : ℕ) (hz : 0 < z) :
    Work.ZeroDensity.Jutila.s3cont z N
      = ∑ q ∈ Finset.Icc 1 (N / z),
          ((N : ℝ) / (q : ℝ)) * s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) := by
  have hfl : ∀ q : ℕ, ⌊(N : ℝ) / ((q : ℝ) * (z : ℝ))⌋₊ = N / (q * z) := by
    intro q
    rw [show (N : ℝ) / ((q : ℝ) * (z : ℝ)) = (N : ℝ) / (((q * z : ℕ)) : ℝ) by
      push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  unfold Work.ZeroDensity.Jutila.s3cont s3Phi
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hq0 : q ≠ 0 := by
    have h1 := (Finset.mem_Icc.mp hq).1; omega
  rw [hfl q]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have hr0 : r ≠ 0 := by
    have h1 := (Finset.mem_Icc.mp hr).1; omega
  have ht0 : t ≠ 0 := by
    have h1 := (Finset.mem_Icc.mp ht).1; omega
  by_cases hc : Nat.Coprime r t
  · have := s3cont_term_eq z N q r t hq0 hr0 ht0 (by omega) hc
    simpa only [mul_assoc] using this
  · simp [hc]

/-- `⌊M⌋·|log(⌊M⌋/M)| ≤ 1` for `M ≥ 1`: the key "floor defect times logarithm" bound. -/
lemma floor_log_defect (M : ℝ) (hM : 1 ≤ M) :
    ((Nat.floor M : ℕ) : ℝ) * |Real.log (((Nat.floor M : ℕ) : ℝ) / M)| ≤ 1 := by
  set m : ℕ := Nat.floor M with hm
  have hm1 : 1 ≤ m := by
    have h0 : 0 < ⌊M⌋₊ := Nat.floor_pos.mpr hM
    omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hle : (m : ℝ) ≤ M := Nat.floor_le (le_of_lt hMpos)
  have hlt : M < (m : ℝ) + 1 := Nat.lt_floor_add_one M
  have hr : M / (m : ℝ) ≤ 1 + 1 / (m : ℝ) := by
    rw [div_le_iff₀ hmR]
    have : (1 + 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) + 1 := by
      field_simp
    rw [this]; linarith only [hlt]
  have hr1 : 1 ≤ M / (m : ℝ) := (one_le_div hmR).mpr hle
  have hlog : |Real.log ((m : ℝ) / M)| ≤ 1 / (m : ℝ) := by
    have h1 : Real.log ((m : ℝ) / M) = -Real.log (M / (m : ℝ)) := by
      rw [Real.log_div (ne_of_gt hmR) (ne_of_gt hMpos),
        Real.log_div (ne_of_gt hMpos) (ne_of_gt hmR)]; ring
    rw [h1, abs_neg]
    have h2 : 0 ≤ Real.log (M / (m : ℝ)) := Real.log_nonneg hr1
    rw [abs_of_nonneg h2]
    have h3 : Real.log (M / (m : ℝ)) ≤ 1 / (m : ℝ) := by
      calc Real.log (M / (m : ℝ)) ≤ M / (m : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ ≤ 1 / (m : ℝ) := by linarith only [hr]
    exact h3
  calc ((m : ℕ) : ℝ) * |Real.log (((m : ℕ) : ℝ) / M)| ≤ (m : ℝ) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hmR)
    _ = 1 := by field_simp

/-- **Pointwise floor bound.**  For `q, r, t ≥ 1` with `r, t ≤ x = N/(qz)`, the floor bracket at
`⌊M⌋` (`M = N/(qrt)`) differs from the real one by at most a constant times
`(1 + log(x/r))(1 + log(x/t))`. -/
lemma s3floor_pointwise (z N q r t : ℕ) (hq : q ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0)
    (hz : z ≠ 0) (hqrt : q * r * t ≤ N)
    (hxr : (r : ℝ) ≤ (N : ℝ) / ((q : ℝ) * (z : ℝ)))
    (hxt : (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * (z : ℝ))) :
    |(((N / (q * r * t) : ℕ)) : ℝ) *
        (((Real.log ((((N / (q * r * t) : ℕ)) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
            (Real.log ((((N / (q * r * t) : ℕ)) : ℝ) * (r : ℝ) / (z : ℝ)) - 1)) + 1)
      - ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
        (((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
            (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1)) + 1)|
      ≤ 6 * (1 + Real.log (((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (r : ℝ)))
          * (1 + Real.log (((N : ℝ) / ((q : ℝ) * (z : ℝ))) / (t : ℝ))) := by
  set M : ℝ := (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) with hMdef
  set mf : ℝ := ((N / (q * r * t) : ℕ) : ℝ) with hmfdef
  set x : ℝ := (N : ℝ) / ((q : ℝ) * (z : ℝ)) with hxdef
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hr)
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ht)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < q * r * t) hqrt
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- `mf = ⌊M⌋`
  have hmf : mf = ((⌊M⌋₊ : ℕ) : ℝ) := by
    rw [hmfdef, hMdef]
    rw [show (N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) = (N : ℝ) / (((q * r * t : ℕ)) : ℝ) by
      push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    rw [le_div_iff₀ (by positivity)]
    have hcast : (((q * r * t : ℕ)) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqrt
    push_cast at hcast ⊢
    linarith only [hcast]
  have hmfpos : 0 < mf := by
    rw [hmf]; exact_mod_cast (Nat.floor_pos.mpr hM1)
  have hz0 : (z : ℝ) ≠ 0 := ne_of_gt hzR
  have ht0 : (t : ℝ) ≠ 0 := ne_of_gt htR
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hm0 : mf ≠ 0 := ne_of_gt hmfpos
  -- the log shifts: both logs move by `δ = log(mf/M)`
  have hδ1 : Real.log (mf * (t : ℝ) / (z : ℝ)) = Real.log (x / (r : ℝ)) + Real.log (mf / M) := by
    have heq : mf * (t : ℝ) / (z : ℝ) = (x / (r : ℝ)) * (mf / M) := by
      rw [hmf, hMdef, hxdef]
      field_simp
    rw [heq, Real.log_mul (ne_of_gt (div_pos hxpos hrR)) (ne_of_gt (div_pos hmfpos hMpos))]
  have hδ2 : Real.log (mf * (r : ℝ) / (z : ℝ)) = Real.log (x / (t : ℝ)) + Real.log (mf / M) := by
    have heq : mf * (r : ℝ) / (z : ℝ) = (x / (t : ℝ)) * (mf / M) := by
      rw [hmf, hMdef, hxdef]
      field_simp
    rw [heq, Real.log_mul (ne_of_gt (div_pos hxpos htR)) (ne_of_gt (div_pos hmfpos hMpos))]
  -- the two log factors, at the real cut-off
  have hA : 0 ≤ Real.log (x / (r : ℝ)) := Real.log_nonneg (by
    rw [le_div_iff₀ hrR]; simpa using hxr)
  have hB : 0 ≤ Real.log (x / (t : ℝ)) := Real.log_nonneg (by
    rw [le_div_iff₀ htR]; simpa using hxt)
  set A : ℝ := Real.log (x / (r : ℝ)) with hAdef
  set B : ℝ := Real.log (x / (t : ℝ)) with hBdef
  set δ : ℝ := Real.log (mf / M) with hδdef
  have hδbound : mf * |δ| ≤ 1 := by
    rw [hδdef, hmf]
    exact floor_log_defect M hM1
  have hδabs : |δ| ≤ 1 := by
    have h1 : (1:ℝ) ≤ mf := by
      rw [hmf]; exact_mod_cast (Nat.succ_le_of_lt (Nat.floor_pos.mpr hM1))
    calc |δ| = 1 * |δ| := by ring
      _ ≤ mf * |δ| := by
          apply mul_le_mul_of_nonneg_right h1 (abs_nonneg δ)
      _ ≤ 1 := hδbound
  have hmlog1 : Real.log (M * (t : ℝ) / (z : ℝ)) = Real.log (x / (r : ℝ)) := by
    rw [hMdef, hxdef]
    congr 1
    field_simp
  have hmlog2 : Real.log (M * (r : ℝ) / (z : ℝ)) = Real.log (x / (t : ℝ)) := by
    rw [hMdef, hxdef]
    congr 1
    field_simp
  -- the algebraic core
  have hG1 : (((Real.log (mf * (t : ℝ) / (z : ℝ)) - 1) *
      (Real.log (mf * (r : ℝ) / (z : ℝ)) - 1) + 1))
      = (A + δ - 1) * (B + δ - 1) + 1 := by
    rw [hδ1, hδ2, hAdef, hBdef, hδdef]
  have hG2 : (((Real.log (M * (t : ℝ) / (z : ℝ)) - 1) * (Real.log (M * (r : ℝ) / (z : ℝ)) - 1) + 1))
      = (A - 1) * (B - 1) + 1 := by rw [hmlog1, hmlog2, hAdef, hBdef]
  rw [hG1, hG2]
  have hmle : mf - M ≤ 1 := by linarith only [Nat.floor_le (le_of_lt hMpos), hmf, hMpos]
  have hMle : M - mf ≤ 1 := by linarith only [Nat.lt_floor_add_one M, hmf]
  have habs1 : |mf - M| ≤ 1 := abs_le.mpr ⟨by linarith only [hMle], hmle⟩
  have hkey : mf * ((A + δ - 1) * (B + δ - 1) + 1) - M * ((A - 1) * (B - 1) + 1)
      = (mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1)) + mf * δ ^ 2 := by
    ring
  rw [hkey]
  have h1 : |(A - 1) * (B - 1) + 1| ≤ (1 + A) * (1 + B) + 1 := by
    rw [abs_le]
    constructor <;> linarith only [hA, hB, mul_nonneg hA hB]
  have h2 : |mf * δ * ((A - 1) + (B - 1))| ≤ (1 + A) + (1 + B) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hmfpos)]
    have h4 : |(A - 1) + (B - 1)| ≤ (1 + A) + (1 + B) := by
      rw [abs_le]; constructor <;> linarith only [hA, hB]
    calc mf * |δ| * |(A - 1) + (B - 1)| ≤ 1 * ((1 + A) + (1 + B)) := by
          apply mul_le_mul hδbound h4 (abs_nonneg _) (by norm_num)
      _ = (1 + A) + (1 + B) := by ring
  have h5 : |mf * δ ^ 2| ≤ 1 := by
    rw [abs_mul, abs_pow, abs_of_nonneg (le_of_lt hmfpos)]
    have h6 : |δ| ^ 2 ≤ |δ| := by nlinarith only [hδabs, abs_nonneg δ]
    calc mf * |δ| ^ 2 ≤ mf * |δ| := mul_le_mul_of_nonneg_left h6 (le_of_lt hmfpos)
      _ ≤ 1 := hδbound
  have hsum := abs_add_le ((mf - M) * ((A - 1) * (B - 1) + 1))
    (mf * δ * ((A - 1) + (B - 1)) + mf * δ ^ 2)
  have hsplit := abs_add_le (mf * δ * ((A - 1) + (B - 1))) (mf * δ ^ 2)
  have hfin : |(mf - M) * ((A - 1) * (B - 1) + 1)|
      ≤ (1 + A) * (1 + B) + 1 := by
    rw [abs_mul]
    calc |mf - M| * |(A - 1) * (B - 1) + 1| ≤ 1 * ((1 + A) * (1 + B) + 1) :=
          mul_le_mul habs1 h1 (abs_nonneg _) (by norm_num)
      _ = (1 + A) * (1 + B) + 1 := by ring
  have hsum1 : |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1))|
      ≤ ((1 + A) * (1 + B) + 1) + ((1 + A) + (1 + B)) := by
    calc |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1))|
        ≤ |(mf - M) * ((A - 1) * (B - 1) + 1)| + |mf * δ * ((A - 1) + (B - 1))| :=
          abs_add_le _ _
      _ ≤ ((1 + A) * (1 + B) + 1) + ((1 + A) + (1 + B)) := add_le_add hfin h2
  have htot : |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1)) + mf * δ ^ 2|
      ≤ ((1 + A) * (1 + B) + 1) + ((1 + A) + (1 + B)) + 1 := by
    calc |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1)) + mf * δ ^ 2|
        = |((mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1))) + mf * δ ^ 2| := by ring_nf
      _ ≤ |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1))| + |mf * δ ^ 2| :=
          abs_add_le _ _
      _ ≤ (((1 + A) * (1 + B) + 1) + ((1 + A) + (1 + B))) + 1 := add_le_add hsum1 h5
  calc |(mf - M) * ((A - 1) * (B - 1) + 1) + mf * δ * ((A - 1) + (B - 1)) + mf * δ ^ 2|
      ≤ ((1 + A) * (1 + B) + 1) + ((1 + A) + (1 + B)) + 1 := htot
    _ ≤ 6 * (1 + A) * (1 + B) := by linarith only [hA, hB, mul_nonneg hA hB]

end

end Work.LinnikAreas.JutilaPieces
