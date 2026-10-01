import Mathlib

namespace Work.LinnikAreas.JutilaPieces

/-- Cast bounds for natural division: for `0 < d`, the real number `N / d`
lies between the (cast of the) natural quotient `N / d` and that quotient plus one. -/
theorem div_cast_bounds (N d : ℕ) (hd : 0 < d) :
    ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) ∧ (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hN : (N:ℝ) = (d:ℝ)*((N/d:ℕ):ℝ) + ((N%d:ℕ):ℝ) := by
    have h := congrArg (fun k : ℕ => (k:ℝ)) (Nat.div_add_mod N d)
    push_cast at h
    linarith [h]
  have hMeq : (N:ℝ)/(d:ℝ) = ((N/d:ℕ):ℝ) + ((N%d:ℕ):ℝ)/(d:ℝ) := by
    rw [hN, add_div, mul_div_cancel_left₀ _ hdR.ne']
  constructor
  · have h1 : (0:ℝ) ≤ ((N%d:ℕ):ℝ)/(d:ℝ) := div_nonneg (Nat.cast_nonneg _) hdR.le
    linarith [hMeq]
  · have hmod : ((N%d:ℕ):ℝ) < (d:ℝ) := by exact_mod_cast Nat.mod_lt N hd
    have h1 : ((N%d:ℕ):ℝ)/(d:ℝ) < 1 := (div_lt_one hdR).mpr hmod
    linarith [hMeq]

/-- The elementary logarithm bound behind the `S₃` expansion: for `1 ≤ M ≤ x ≤ M + 1`,
the quantity `|log(M/x)|` is at most `2/x`. -/
theorem log_ratio_le (M x : ℝ) (hM : 1 ≤ M) (hMx : M ≤ x) (hxM : x ≤ M + 1) :
    |Real.log (M/x)| ≤ 2/x := by
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hxpos : 0 < x := lt_of_lt_of_le hMpos hMx
  have hMxpos : 0 < M/x := div_pos hMpos hxpos
  have hle1 : M/x ≤ 1 := (div_le_one hxpos).mpr hMx
  have hlog : Real.log (M/x) ≤ 0 := Real.log_nonpos hMxpos.le hle1
  rw [abs_of_nonpos hlog]
  have hxM' : x/M ≤ 1 + 1/M := by
    rw [div_le_iff₀ hMpos]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hMpos.ne']
    exact hxM
  have hone : (0:ℝ) < 1 + 1/M := by positivity
  have h1 : -Real.log (M/x) = Real.log (x/M) := by
    rw [Real.log_div hxpos.ne' hMpos.ne', Real.log_div hMpos.ne' hxpos.ne']; ring
  rw [h1]
  have h2 : Real.log (x/M) ≤ Real.log (1 + 1/M) := Real.log_le_log (div_pos hxpos hMpos) hxM'
  have h3 : Real.log (1 + 1/M) ≤ 1/M := by
    have := Real.log_le_sub_one_of_pos hone
    linarith
  have h4 : (1:ℝ)/M ≤ 2/x := by
    have hx2 : 0 < x/2 := by linarith
    have h2M : x/2 ≤ M := by linarith [hM, hxM]
    have h := one_div_le_one_div_of_le hx2 h2M
    rwa [one_div_div] at h
  linarith [h2, h3, h4]

/-- The exact logarithm identity: with all arguments positive,
`log(M·t/z) − (log(n/c) − log(z/t)) = log(M·c/n)`. -/
theorem log_identity (M t z n c : ℝ) (hM : 0 < M) (ht : 0 < t) (hz : 0 < z)
    (hn : 0 < n) (hc : 0 < c) :
    Real.log (M*t/z) - (Real.log (n/c) - Real.log (z/t)) = Real.log (M*c/n) := by
  have hMn : M ≠ 0 := hM.ne'
  have htn : t ≠ 0 := ht.ne'
  have hzn : z ≠ 0 := hz.ne'
  have hnn : n ≠ 0 := hn.ne'
  have hcn : c ≠ 0 := hc.ne'
  have h1 : Real.log (M*t/z) = Real.log M + Real.log t - Real.log z := by
    rw [Real.log_div (mul_ne_zero hMn htn) hzn, Real.log_mul hMn htn]
  have h2 : Real.log (n/c) = Real.log n - Real.log c := Real.log_div hnn hcn
  have h3 : Real.log (z/t) = Real.log z - Real.log t := Real.log_div hzn htn
  have h4 : Real.log (M*c/n) = Real.log M + Real.log c - Real.log n := by
    rw [Real.log_div (mul_ne_zero hMn hcn) hnn, Real.log_mul hMn hcn]
  rw [h1, h2, h3, h4]; ring

/-- **Step 1 of the `S₃` main-term bookkeeping: the floor/log expansion** (for the target
`S3MainTerm` of `Work.ZeroDensity.Jutila` / `BzS3.S3_main_term`; the statement is pure Mathlib, so it
needs no import and cannot drift against those definitions).  For naturals with `q, r, t ≥ 1`,
`z ≥ 2` and `q·r·t ≤ N`,

  `|log(⌊N/(qrt)⌋·t/z) − (log(N/(qrt)) − log(z/t))| ≤ 2·(qrt)/N`.

Proof: with `M = N/(qrt)` (ℕ-division) and `x = N/(qrt) ∈ ℝ`, `qrt ≥ 1` gives `M = ⌊x⌋`, and
`qrt ≤ N` gives `x ≥ 1`, so `M ≥ 1` and `M ≤ x < M+1 ≤ 2M`.  Since `x·t/z = N/(qrz)`, one has
`log x − log(z/t) = log(x·t/z)`, so the difference above is exactly `log(M/x)`, whence
`|log(M/x)| = log(x/M) ≤ log(1 + 1/M) ≤ 1/M ≤ 2/x = 2qrt/N`.  All log arguments are positive by the
hypotheses.  (Reviewed: brute-forced numerically over `N < 300`, `z < 50` and all admissible
`q, r, t` with no violation.) -/
theorem S3LogExpansion {N q r t z : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hz : 2 ≤ z) (hqr : q * r * t ≤ N) :
    |Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ))
      - (Real.log ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
          - Real.log ((z : ℝ) / (t : ℝ)))|
    ≤ 2 * (((q : ℝ) * (r : ℝ) * (t : ℝ)) / (N : ℝ)) := by
  have hdpos : 0 < q * r * t := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le hdpos hqr
  set c : ℝ := (q:ℝ)*(r:ℝ)*(t:ℝ) with hc
  set n : ℝ := (N:ℝ) with hn
  set M : ℕ := N / (q*r*t) with hM
  set x : ℝ := n / c with hx
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have htR : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hcpos : 0 < c := by rw [hc]; positivity
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hNpos
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hqr)
  obtain ⟨hMle0, hxlt0⟩ := div_cast_bounds N (q*r*t) hdpos
  have hcast : (((q*r*t : ℕ)) : ℝ) = c := by rw [hc]; push_cast; ring
  rw [hcast] at hMle0 hxlt0
  have hMle : (M:ℝ) ≤ x := by rw [hM, hx, hn]; exact hMle0
  have hxlt : x < (M:ℝ) + 1 := by rw [hM, hx, hn]; exact hxlt0
  have hxle : x ≤ (M:ℝ) + 1 := le_of_lt hxlt
  have hMposR : (0:ℝ) < (M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
    linarith
  have htpos : 0 < (t:ℝ) := by linarith [htR]
  have hzpos : 0 < (z:ℝ) := by
    have : (2:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
    linarith
  have hlogid : Real.log ((M:ℝ) * (t:ℝ) / (z:ℝ)) - (Real.log x - Real.log ((z:ℝ)/(t:ℝ)))
      = Real.log ((M:ℝ) * c / n) := by
    rw [hx]
    exact log_identity (M:ℝ) (t:ℝ) (z:ℝ) n c hMposR htpos hzpos hnpos hcpos
  have hb := log_ratio_le (M:ℝ) x (by exact_mod_cast hM1) hMle hxle
  have hMxeq : (M:ℝ) * c / n = (M:ℝ) / x := by
    rw [hx]; field_simp
  have h2eq : 2 / x = 2 * (c / n) := by
    rw [hx]; field_simp
  rw [hlogid, hMxeq, ← h2eq]
  exact hb

end Work.LinnikAreas.JutilaPieces
