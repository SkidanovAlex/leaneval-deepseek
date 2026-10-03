import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTAreas.A7

/-!
# The normalised bound on the modulation phase `P(N t)`

The `g`-side symbol of §6 is the modulated bump
`φ̃_{N,t}(ξ) = φ̃_N(ξ) · e(P(Nt) ξ)`, whose profile is `gProfile d k₂` rescaled by
`gScale d N k₂ = 2^{d (Log N - k₂)}` (`varphitildeNt_eq_profile`).  The shift of its Fourier
transform is the number `PevalR P (N t)`, and in the model approximation it is natural to compare
that shift with the frequency scale `gScale d N k₂`; this file supplies the resulting elementary
bound, uniform in `t ∈ [-1,1]` and in `N`:

  `|PevalR P (N t)| / gScale d N k₂ ≤ (S + 1) · 3^d · (1 + 2^{d k₂})`,
  with `S = ∑_{i ≤ P.natDegree} |P.coeff i|` the `ℓ¹`-norm of the coefficients.

**The mathematics.**  With `L = Log N = log₂ max(N,2)` one has `gScale d N k₂ = 2^{dL} / 2^{d k₂}`,
and `max(N,2) < 2^{L+1}`, so `1 + N ≤ 2·2^L` and hence
`(1 + N)^{deg} ≤ (2·2^L)^{deg} = 2^{deg} · 2^{L·deg} ≤ 2^d · 2^{dL}` for `deg = P.natDegree ≤ d`.
Combined with the polynomial growth estimate `|PevalR P (N t)| ≤ S · (1+N)^{deg}`
(`abs_PevalR_mul_le`) and `2^d ≤ 3^d`, `2^{d k₂} ≤ 1 + 2^{d k₂}` this gives the claim.  The
constant `3^d` is the room left by `1 + N ≤ 2 · 2^{Log N}` and `deg ≤ d`.
-/

/-- The two ways of writing the `g`-side frequency scale: multiplying `gScale d N k₂` by the
denominator `2^{d k₂}` recovers the numerator `2^{d Log N}`.  This is the bridge between the
`zpow`-valued `gScale` and the natural powers used in the estimates. -/
private lemma gScale_mul_pow (d N k₂ : ℕ) :
    gScale d N k₂ * (2 : ℝ) ^ (d * k₂) = (2 : ℝ) ^ (d * Nat.log 2 (max N 2)) := by
  have hZ : (d : ℤ) * (Work.Analysis.EndVar.logN N - (k₂ : ℤ)) + ↑(d * k₂)
      = ↑(d * Nat.log 2 (max N 2)) := by
    simp only [Work.Analysis.EndVar.logN]
    push_cast
    ring
  rw [show gScale d N k₂
        = (2:ℝ) ^ ((d:ℤ) * (Work.Analysis.EndVar.logN N - (k₂:ℤ))) from rfl]
  rw [← zpow_natCast (2:ℝ) (d*k₂), ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), hZ, zpow_natCast]

/-- The polynomial growth bound for the modulation phase, normalised by the frequency scale
`gScale d N k₂`.  Everything is explicit: only the coefficient `ℓ¹`-norm enters. -/
theorem abs_PevalR_div_gScale_le (P : Polynomial ℤ) (d N k₂ : ℕ) (hd : P.natDegree ≤ d)
    {t : ℝ} (ht : |t| ≤ 1) :
    |PevalR P ((N : ℝ) * t)| / gScale d N k₂
      ≤ ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) + 1) * 3 ^ d
          * (1 + (2 : ℝ) ^ (d * k₂)) := by
  classical
  set S : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| with hSdef
  set L : ℕ := Nat.log 2 (max N 2) with hLdef
  set A : ℝ := (2:ℝ)^(d*L) with hAdef
  set B : ℝ := (2:ℝ)^(d*k₂) with hBdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hGpos : 0 < gScale d N k₂ := by rw [gScale]; positivity
  -- `gScale` is the quotient `A / B`
  have hGA : gScale d N k₂ * B = A := by
    rw [hAdef, hBdef, hLdef]; exact gScale_mul_pow d N k₂
  have hBAnn : 0 ≤ B / A := div_nonneg hBnn hApos.le
  have hinv : (gScale d N k₂)⁻¹ = B / A := by
    rw [eq_div_iff (ne_of_gt hApos), ← hGA, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hGpos), one_mul]
  -- the polynomial growth of `1 + N` against the scale `A`
  have hpoly : (1 + (N:ℝ)) ^ P.natDegree ≤ (2:ℝ)^d * A := by
    have hlt : max N 2 < 2 ^ (L + 1) := by
      rw [hLdef]; exact Nat.lt_pow_succ_log_self (by norm_num) (max N 2)
    have hN : N + 1 ≤ 2^(L+1) := by
      have h1 : N ≤ max N 2 := le_max_left _ _
      omega
    have hreal : (1 + (N:ℝ)) ≤ 2 * (2:ℝ)^L := by
      have hc : ((N+1 : ℕ) : ℝ) ≤ ((2^(L+1) : ℕ) : ℝ) := by exact_mod_cast hN
      have h1 : (1 + (N:ℝ)) = ((N+1 : ℕ) : ℝ) := by push_cast; ring
      rw [h1]
      calc ((N+1 : ℕ) : ℝ) ≤ ((2^(L+1) : ℕ) : ℝ) := hc
        _ = 2 * (2:ℝ)^L := by rw [pow_succ']; push_cast; ring
    calc (1 + (N:ℝ))^P.natDegree
        ≤ (2 * (2:ℝ)^L)^P.natDegree := pow_le_pow_left₀ (by positivity) hreal _
      _ = (2:ℝ)^P.natDegree * ((2:ℝ)^L)^P.natDegree := mul_pow _ _ _
      _ = (2:ℝ)^P.natDegree * (2:ℝ)^(L * P.natDegree) := by rw [pow_mul]
      _ ≤ (2:ℝ)^d * (2:ℝ)^(d * L) := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · exact pow_le_pow_right₀ (by norm_num) hd
          · refine pow_le_pow_right₀ (by norm_num) ?_
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left L hd
      _ = (2:ℝ)^d * A := by rw [← hAdef]
  have hPeval := abs_PevalR_mul_le P N ht
  rw [← hSdef] at hPeval
  have hAdivB : A * (B / A) = B := by
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ B (ne_of_gt hApos)
  calc |PevalR P ((N:ℝ)*t)| / gScale d N k₂
      = |PevalR P ((N:ℝ)*t)| * (gScale d N k₂)⁻¹ := by rw [div_eq_mul_inv]
    _ = |PevalR P ((N:ℝ)*t)| * (B / A) := by rw [hinv]
    _ ≤ (S * (1+(N:ℝ))^P.natDegree) * (B/A) :=
        mul_le_mul_of_nonneg_right hPeval hBAnn
    _ ≤ (S * ((2:ℝ)^d * A)) * (B/A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hSnn) hBAnn
    _ = S * (2:ℝ)^d * B := by
        rw [show S * ((2:ℝ)^d * A) * (B/A) = S * (2:ℝ)^d * (A * (B/A)) by ring, hAdivB]
    _ ≤ (S + 1) * 3^d * (1 + B) := by
        have h1 : S * (2:ℝ)^d ≤ (S+1) * 3^d := by
          refine mul_le_mul (le_add_of_nonneg_right (zero_le_one)) ?_ (by positivity) (by positivity)
          exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 3) d
        have h2 : B ≤ 1 + B := le_add_of_nonneg_left (zero_le_one)
        calc S * (2:ℝ)^d * B = (S*(2:ℝ)^d) * B := by ring
          _ ≤ ((S+1)*3^d) * (1+B) := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (S+1)*3^d*(1+B) := by ring
    _ = ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) + 1) * 3^d
          * (1 + (2:ℝ)^(d*k₂)) := by rw [hSdef, hBdef]

end Work.KMTAreas.A7
