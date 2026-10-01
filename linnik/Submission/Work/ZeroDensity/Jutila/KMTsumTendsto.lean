/-
# The limit of the Riesz-weighted `1/κ` Möbius sum `Tsum N t`

For squarefree `t`,

`Tsum N t = Σ_{r ≤ N, (r,t)=1} (μ(r)/κ(r))·log(N/r)  ⟶  ζ(2)·κ(t)/t = (π²/6)·κ(t)/t`

(`κ(n) = n·∏_{p|n}(1+1/p)`, so `κ(t)/t = ∏_{p|t}(1+1/p)` for squarefree `t`).

The analytic input is the sharp Mertens-type evaluation
`Work.LinnikAreas.Density4.mobius_kappa_log_sum`, which for every `A` bounds
`|Σ_{n ≤ Q,(n,r)=1} (μ(n)/(n∏_{p|n}(1+1/p)))·log(Q/n) − (∏_{p|r}(1+1/p))·ζ(2)|`
by `C·σ_{-1/2}(r)·log(2+Q)^{-A}`.  Since `κ(n)` is *by definition* `n·∏_{p|n}(1+1/p)`, the
weighted sum there is literally `Tsum ⌊Q⌋₊ r`; taking `A = 1`, `r = t` and letting `Q → ∞`
gives the limit, the error `C·σ_{-1/2}(t)·log(2+Q)^{-1}` tending to `0`.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.LinnikAreas.Density4.mobius_kappa_log_sum

namespace Work.ZeroDensity.Jutila

open Filter

theorem KMTsumTendsto (t : ℕ) (ht : Squarefree t) :
    Filter.Tendsto (fun N : ℕ => Tsum N t) Filter.atTop (nhds ((Real.pi ^ 2 / 6) * (kappa t / (t : ℝ)))) := by
  obtain ⟨C, _hC, hb⟩ := Work.LinnikAreas.Density4.mobius_kappa_log_sum 1
  -- `t ≠ 0`: `4*4 ∣ 0`, so `Squarefree 0` would force `IsUnit 4`.
  have ht0 : t ≠ 0 := by
    intro h
    subst h
    have h4 : IsUnit (4 : ℕ) := ht 4 (dvd_zero (4 * 4))
    rw [Nat.isUnit_iff] at h4
    omega
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
  set P : ℝ := ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℝ)) with hP
  -- The Mertens-type estimate, transported to `Tsum`.
  have hbound : ∀ᶠ N in Filter.atTop, ‖Tsum N t - P * (Real.pi ^ 2 / 6)‖ ≤
      (C * sigHalf t) * Real.log (2 + (N : ℝ)) ^ (-1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hQ : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h := hb (N : ℝ) t hQ ht1
    rw [Nat.floor_natCast] at h
    simpa only [Tsum, kappa, hP, sigHalf, Real.norm_eq_abs] using h
  -- The error envelope tends to `0`.
  have hlog : Tendsto (fun N : ℕ => Real.log (2 + (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_left Filter.atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hpow : Tendsto (fun N : ℕ => Real.log (2 + (N : ℝ)) ^ (-1 : ℝ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp hlog
  have hmain : Tendsto (fun N : ℕ => (C * sigHalf t) * Real.log (2 + (N : ℝ)) ^ (-1 : ℝ))
      atTop (nhds 0) := by
    simpa using hpow.const_mul (C * sigHalf t)
  have hsub : Tendsto (fun N : ℕ => Tsum N t - P * (Real.pi ^ 2 / 6)) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hmain
  have hlim : Tendsto (fun N : ℕ => Tsum N t) atTop (nhds (P * (Real.pi ^ 2 / 6))) := by
    have h2 := hsub.add (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => P * (Real.pi ^ 2 / 6)) atTop (nhds (P * (Real.pi ^ 2 / 6))))
    simpa using h2
  -- `κ(t)/t = ∏_{p|t}(1+1/p) = P` (here `t ≠ 0`).
  have htarget : (Real.pi ^ 2 / 6) * (kappa t / (t : ℝ)) = P * (Real.pi ^ 2 / 6) := by
    rw [hP]
    unfold kappa
    have ht0' : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
    field_simp
  rw [htarget]
  exact hlim

end Work.ZeroDensity.Jutila
