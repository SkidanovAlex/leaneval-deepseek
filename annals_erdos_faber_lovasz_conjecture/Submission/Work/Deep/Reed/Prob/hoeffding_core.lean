import Submission.Work.Deep.Sparse.Prelude
open Set

namespace Work.Deep.Reed.Prob

/-! ## The core inequality behind Hoeffding's bound

Writing `A u = p * exp ((1 - p) * u)`, `B u = (1 - p) * exp (-(p * u))` and
`φ = A + B`, the proof proceeds exactly as in the sketch: `φ > 0`, `h = log ∘ φ` has
`h'' = (φ'' φ - (φ')²)/φ² = A * B / φ² ≤ 1/4` (since `(A - B)² ≥ 0`), and the auxiliary
`K = u/4 - φ'/φ` satisfies `K' = 1/4 - h'' ≥ 0`, `K 0 = 0`.  Hence `K ≤ 0` on `(-∞,0]`,
`K ≥ 0` on `[0,∞)`, so `G = u²/8 - h`, whose derivative is `K`, is antitone on `(-∞,0]`
and monotone on `[0,∞)` with `G 0 = 0`, giving `G ≥ 0`, i.e. `log (φ u) ≤ u²/8`. -/

/-- `A u = p * exp ((1 - p) * u)`. -/
private noncomputable def hA (p : ℝ) : ℝ → ℝ := fun u => p * Real.exp ((1 - p) * u)

/-- `B u = (1 - p) * exp (-(p * u))`. -/
private noncomputable def hB (p : ℝ) : ℝ → ℝ := fun u => (1 - p) * Real.exp (-(p * u))

/-- `φ = A + B`, the (uncentred) exponential moment. -/
private noncomputable def hphi (p : ℝ) : ℝ → ℝ := fun u => hA p u + hB p u

/-- `φ' u = (1 - p) * A u - p * B u`. -/
private noncomputable def hphi₁ (p : ℝ) : ℝ → ℝ := fun u => (1 - p) * hA p u - p * hB p u

/-- `φ'' u = (1 - p)^2 * A u + p^2 * B u`. -/
private noncomputable def hphi₂ (p : ℝ) : ℝ → ℝ := fun u => (1 - p) ^ 2 * hA p u + p ^ 2 * hB p u

/-- `K u = u / 4 - φ' u / φ u`. -/
private noncomputable def hK (p : ℝ) : ℝ → ℝ := fun u => u / 4 - hphi₁ p u / hphi p u

/-- `G u = u^2 / 8 - log (φ u)`. -/
private noncomputable def hG (p : ℝ) : ℝ → ℝ := fun u => u ^ 2 / 8 - Real.log (hphi p u)

private theorem hasDerivAt_hA (p u : ℝ) : HasDerivAt (hA p) ((1 - p) * hA p u) u := by
  have h1 : HasDerivAt (fun x : ℝ => (1 - p) * x) (1 - p) u := by
    simpa using (hasDerivAt_id u).const_mul (1 - p)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp ((1 - p) * x))
      (Real.exp ((1 - p) * u) * (1 - p)) u := h1.exp
  have h3 : HasDerivAt (fun x : ℝ => p * Real.exp ((1 - p) * x))
      (p * (Real.exp ((1 - p) * u) * (1 - p))) u := h2.const_mul p
  exact h3.congr_deriv (by simp only [hA]; ring)

private theorem hasDerivAt_hB (p u : ℝ) : HasDerivAt (hB p) (-(p * hB p u)) u := by
  have h1 : HasDerivAt (fun x : ℝ => -(p * x)) (-p) u := by
    have h : HasDerivAt (fun x : ℝ => p * x) (p * 1) u := (hasDerivAt_id u).const_mul p
    exact h.neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(p * x)))
      (Real.exp (-(p * u)) * (-p)) u := h1.exp
  have h3 : HasDerivAt (fun x : ℝ => (1 - p) * Real.exp (-(p * x)))
      ((1 - p) * (Real.exp (-(p * u)) * (-p))) u := h2.const_mul (1 - p)
  exact h3.congr_deriv (by simp only [hB]; ring)

private theorem hasDerivAt_hphi (p u : ℝ) : HasDerivAt (hphi p) (hphi₁ p u) u := by
  have h := (hasDerivAt_hA p u).add (hasDerivAt_hB p u)
  exact h.congr_deriv (by simp only [hphi₁]; ring)

private theorem hasDerivAt_hphi₁ (p u : ℝ) : HasDerivAt (hphi₁ p) (hphi₂ p u) u := by
  have h1 : HasDerivAt (fun x : ℝ => (1 - p) * hA p x) ((1 - p) * ((1 - p) * hA p u)) u :=
    (hasDerivAt_hA p u).const_mul (1 - p)
  have h2 : HasDerivAt (fun x : ℝ => p * hB p x) (p * (-(p * hB p u))) u :=
    (hasDerivAt_hB p u).const_mul p
  exact (h1.sub h2).congr_deriv (by simp only [hphi₂]; ring)

/-- The Wronskian identity `φ'' φ - (φ')² = A * B`. -/
private theorem hA_hB_key (p u : ℝ) :
    hphi₂ p u * hphi p u - hphi₁ p u * hphi₁ p u = hA p u * hB p u := by
  simp only [hphi₂, hphi₁, hphi, hA, hB]; ring

private theorem hasDerivAt_hK (p u : ℝ) (hpφ : hphi p u ≠ 0) :
    HasDerivAt (hK p) (1 / 4 - hA p u * hB p u / (hphi p u) ^ 2) u := by
  have h1 : HasDerivAt (fun x : ℝ => x / 4) (1 / 4) u := (hasDerivAt_id u).div_const 4
  have h2 : HasDerivAt (fun x : ℝ => hphi₁ p x / hphi p x)
      ((hphi₂ p u * hphi p u - hphi₁ p u * hphi₁ p u) / (hphi p u) ^ 2) u :=
    (hasDerivAt_hphi₁ p u).div (hasDerivAt_hphi p u) hpφ
  exact (h1.sub h2).congr_deriv (by rw [hA_hB_key p u])

private theorem hasDerivAt_hG (p u : ℝ) (hpφ : hphi p u ≠ 0) :
    HasDerivAt (hG p) (hK p u) u := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 8) (u / 4) u := by
    have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u ^ 1 * 1) u := (hasDerivAt_id u).pow 2
    exact (h.div_const 8).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (hphi p x)) (hphi₁ p u / hphi p u) u :=
    (hasDerivAt_hphi p u).log hpφ
  exact (h1.sub h2).congr_deriv (by simp only [hK])

/-- `φ` is everywhere positive when `0 ≤ p ≤ 1`. -/
private theorem hphi_pos (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : ℝ) : 0 < hphi p u := by
  have hA0 : 0 ≤ hA p u := by rw [hA]; exact mul_nonneg hp0 (Real.exp_pos _).le
  rcases lt_or_eq_of_le hp1 with h | h
  · have hBpos : 0 < hB p u := by
      rw [hB]; exact mul_pos (by linarith) (Real.exp_pos _)
    have : hphi p u = hA p u + hB p u := rfl
    linarith
  · subst h
    have : hphi 1 u = 1 := by simp [hphi, hA, hB]
    rw [this]; norm_num

private theorem hphi_zero (p : ℝ) : hphi p 0 = 1 := by simp [hphi, hA, hB]

private theorem hphi₁_zero (p : ℝ) : hphi₁ p 0 = 0 := by
  simp [hphi₁, hA, hB]
  ring

private theorem hK_zero (p : ℝ) : hK p 0 = 0 := by simp [hK, hphi₁_zero, hphi_zero]

private theorem hG_zero (p : ℝ) : hG p 0 = 0 := by simp [hG, hphi_zero]

/-- `K' = 1/4 - A B / φ² ≥ 0`, because `4 A B ≤ (A + B)² = φ²`. -/
private theorem hK_deriv_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : ℝ) :
    0 ≤ 1 / 4 - hA p u * hB p u / (hphi p u) ^ 2 := by
  have hφpos := hphi_pos p hp0 hp1 u
  have hφ2pos : 0 < (hphi p u) ^ 2 := sq_pos_of_pos hφpos
  have h4 : 4 * (hA p u * hB p u) ≤ (hphi p u) ^ 2 := by
    have hid : (hphi p u) ^ 2 - 4 * (hA p u * hB p u) = (hA p u - hB p u) ^ 2 := by
      simp only [hphi, hA, hB]; ring
    nlinarith [sq_nonneg (hA p u - hB p u)]
  have hle : hA p u * hB p u / (hphi p u) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hφ2pos]; linarith
  linarith

private theorem hK_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Monotone (hK p) :=
  monotone_of_deriv_nonneg
    (fun x => (hasDerivAt_hK p x (ne_of_gt (hphi_pos p hp0 hp1 x))).differentiableAt)
    (fun x => by
      rw [(hasDerivAt_hK p x (ne_of_gt (hphi_pos p hp0 hp1 x))).deriv]
      exact hK_deriv_nonneg p hp0 hp1 x)

/-- **The core inequality behind Hoeffding's bound.**  For `0 ≤ p ≤ 1` and every real `u`,

`(1 - p) * exp (-(p * u)) + p * exp ((1 - p) * u) ≤ exp (u ^ 2 / 8)`.

Equivalently `log (φ u) ≤ u²/8` for `φ u = (1-p) e^{-pu} + p e^{(1-p)u}`; this is the sharp
log-moment-generating bound for a centred variable in an interval of length 1 and argument `u`
(equality is approached for `p = 1/2` as `u → 0`).

Proof sketch.  `p = 0` and `p = 1` are immediate (`1 ≤ exp (u^2/8)`).  For `0 < p < 1` put
`A u = p * exp ((1-p)*u)`, `B u = (1-p) * exp (-(p*u))`, `φ = A + B` (so `φ u > 0`, `φ 0 = 1`).
Then `φ' = (1-p)*A - p*B`, `φ'' = (1-p)^2*A + p^2*B`, and the polynomial identity
`φ'' * φ - (φ')^2 = A * B` holds (`ring`), while `4*A*B ≤ (A+B)^2` because `(A-B)^2 ≥ 0`.
Hence `h := Real.log ∘ φ` has `h'' = (φ'' φ - (φ')²)/φ² = A*B/φ² ≤ 1/4`, `h 0 = 0`, `h' 0 = 0`.
Now `K u := u/4 - (φ' u)/(φ u)` satisfies `K' = 1/4 - h'' ≥ 0` and `K 0 = 0`, so `K ≤ 0` on
`(-∞,0]` and `K ≥ 0` on `[0,∞)`; with `G u := u^2/8 - h u` one has `G' = K`, so `G` is
antitone on `(-∞,0]`, monotone on `[0,∞)`, and `G 0 = 0`; hence `G ≥ 0`, i.e. `h u ≤ u²/8`.
Exponentiate with `Real.log_le_iff_le_exp`.

Useful API: `HasDerivAt.log`, `HasDerivAt.div`, `HasDerivAt.deriv`,
`monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`, `convex_Ici`, `interior_Ici`.
Expected final name: `Work.Deep.Reed.Prob.hoeffding_core`. -/
theorem hoeffding_core {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-(p * u)) + p * Real.exp ((1 - p) * u) ≤ Real.exp (u ^ 2 / 8) := by
  have hφpos (x : ℝ) : 0 < hphi p x := hphi_pos p hp0 hp1 x
  have hKmono : Monotone (hK p) := hK_mono p hp0 hp1
  have hK0 : hK p 0 = 0 := hK_zero p
  have hGderiv (x : ℝ) : HasDerivAt (hG p) (hK p x) x := hasDerivAt_hG p x (ne_of_gt (hφpos x))
  have hGdiff : Differentiable ℝ (hG p) := fun x => (hGderiv x).differentiableAt
  have hGcont : Continuous (hG p) := hGdiff.continuous
  have hG0 : hG p 0 = 0 := hG_zero p
  have hKi : ∀ x ≥ 0, 0 ≤ hK p x := fun x hx => by rw [← hK0]; exact hKmono hx
  have hKii : ∀ x ≤ 0, hK p x ≤ 0 := fun x hx => by rw [← hK0]; exact hKmono hx
  have hGnn : 0 ≤ hG p u := by
    rcases le_or_gt u 0 with hu | hu
    · have hder : ∀ x ∈ interior (Iic (0:ℝ)), deriv (hG p) x ≤ 0 := by
        intro x hx
        rw [interior_Iic, mem_Iio] at hx
        rw [(hGderiv x).deriv]
        exact hKii x hx.le
      have hmvt := (convex_Iic (0:ℝ)).image_sub_le_mul_sub_of_deriv_le (f := hG p) (C := 0)
        hGcont.continuousOn hGdiff.differentiableOn hder u (mem_Iic.mpr hu) 0 (mem_Iic.mpr le_rfl) hu
      rw [hG0, zero_mul] at hmvt
      linarith
    · have hder : ∀ x ∈ interior (Ici (0:ℝ)), 0 ≤ deriv (hG p) x := by
        intro x hx
        rw [interior_Ici, mem_Ioi] at hx
        rw [(hGderiv x).deriv]
        exact hKi x hx.le
      have hmvt := (convex_Ici (0:ℝ)).mul_sub_le_image_sub_of_le_deriv (f := hG p) (C := 0)
        hGcont.continuousOn hGdiff.differentiableOn hder 0 (mem_Ici.mpr le_rfl) u (mem_Ici.mpr hu.le) hu.le
      rw [hG0, zero_mul] at hmvt
      linarith
  have hlog : Real.log (hphi p u) ≤ u ^ 2 / 8 := by
    have h : 0 ≤ u ^ 2 / 8 - Real.log (hphi p u) := hGnn
    linarith
  have hfin : hphi p u ≤ Real.exp (u ^ 2 / 8) := (Real.log_le_iff_le_exp (hφpos u)).1 hlog
  calc (1 - p) * Real.exp (-(p * u)) + p * Real.exp ((1 - p) * u)
      = hphi p u := by simp only [hphi, hA, hB]; ring
    _ ≤ Real.exp (u ^ 2 / 8) := hfin

end Work.Deep.Reed.Prob
