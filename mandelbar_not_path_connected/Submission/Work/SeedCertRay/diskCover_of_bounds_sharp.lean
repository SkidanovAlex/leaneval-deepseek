import Mathlib
import Submission.Work.SeedCertRay.Disk
import Submission.Work.SeedCertRay.norm_sub_le_of_halfplane

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# SeedCertRay — the *sharp* disk version of the `(D1)` square-root cover estimate

This is the sharp companion of `diskCover_of_bounds`: the same covering condition (D1) of the
certified ray chain, but with the drift hypothesis stated with the sharp constant

  `‖(z - c) - w₀ ^ 2‖ ≤ ρ (2 s - ρ)`

in place of the squared form `‖(z - c) - w₀ ^ 2‖ ^ 2 ≤ 2 ρ ^ 2 s ^ 2` of the non-sharp version.
The conclusion is again that a preimage `u` of `z` under `T_c u = conj u ^ 2 + c` lies in `E` or
in `-E`, where `E` contains the disk of radius `ρ` about `conj w₀`.

The mathematical content is the two-factor estimate for `a = ‖u - conj w₀‖` and
`b = ‖u + conj w₀‖`:

* `a * b = ‖conj u ^ 2 - w₀ ^ 2‖ ≤ ρ (2 s - ρ)`,
* `a ^ 2 + b ^ 2 = 2 ‖u‖ ^ 2 + 2 ‖w₀‖ ^ 2 ≥ 4 s ^ 2` (parallelogram law, `s ^ 2 ≤ ‖u‖ ^ 2`,
  `s ^ 2 ≤ ‖w₀‖ ^ 2`).

If both `a > ρ` and `b > ρ`, then `(a - ρ)(b - ρ) > 0` gives `ρ (a + b) < a b + ρ ^ 2 ≤ 2 ρ s`,
hence `a + b < 2 s` and so `a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 < 4 s ^ 2`, a contradiction.  Thus
`min a b ≤ ρ`, which is exactly the covering condition.
-/

namespace Work.SeedCertRay

/-- **Sharp two-factor estimate.**  If the product `a * b` is at most `ρ * (2 * s - ρ)` and
`4 * s ^ 2 ≤ a ^ 2 + b ^ 2`, with `ρ ≥ 0`, then at least one of `a`, `b` is at most `ρ`. -/
private lemma sharp_min_le {a b s ρ : ℝ} (hρ : 0 ≤ ρ)
    (hab : a * b ≤ ρ * (2 * s - ρ)) (h4 : 4 * s ^ 2 ≤ a ^ 2 + b ^ 2) :
    a ≤ ρ ∨ b ≤ ρ := by
  by_contra h
  push_neg at h
  obtain ⟨ha, hb⟩ := h
  have hprod : 0 < (a - ρ) * (b - ρ) := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  have h1 : ρ * (a + b) < a * b + ρ ^ 2 := by nlinarith [hprod]
  have h2 : ρ * (a + b) < 2 * ρ * s := by nlinarith [h1, hab]
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · rw [← hρ0] at h2; linarith
  · have h2' : ρ * (a + b) < ρ * (2 * s) := by nlinarith [h2]
    have h3 : a + b < 2 * s := (mul_lt_mul_iff_of_pos_left hρpos).mp h2'
    have hab0 : 0 ≤ a + b := by nlinarith [hρ, ha, hb]
    have hsq : (a + b) ^ 2 < (2 * s) ^ 2 := by
      have hm := mul_self_lt_mul_self hab0 h3
      nlinarith [hm]
    have hle : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [ha, hb]
    nlinarith [hsq, hle, h4]

/-- `(u - conj w₀) (u + conj w₀) = conj (conj u ^ 2 - w₀ ^ 2)`. -/
private lemma conj_sq_sub_sharp (u w0 : ℂ) :
    starRingEnd ℂ ((starRingEnd ℂ u) ^ 2 - w0 ^ 2) =
      (u - starRingEnd ℂ w0) * (u + starRingEnd ℂ w0) := by
  simp only [map_sub, map_pow]
  rw [Complex.conj_conj]
  ring

theorem diskCover_of_bounds_sharp (D : Work.SeedCertRay.Disk) (X : Work.SeedCertRay.Box) (E : Work.SeedCertRay.Disk) (w0re w0im s ρ : ℚ) (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (hρ2 : (ρ : ℝ) ≤ 2 * (s : ℝ)) (hZ : ∀ z c : ℂ, D.mem z → X.mem c → ‖(z - c) - (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I) ^ 2‖ ≤ (ρ : ℝ) * (2 * (s : ℝ) - (ρ : ℝ))) (hZl : ∀ z c : ℂ, D.mem z → X.mem c → (s : ℝ) ^ 2 ≤ ‖z - c‖) (hs2 : (s : ℝ) ^ 2 ≤ (w0re : ℝ) ^ 2 + (w0im : ℝ) ^ 2) (hE : ∀ u : ℂ, ‖u - starRingEnd ℂ (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I)‖ ≤ (ρ : ℝ) → E.mem u) : Work.SeedCertRay.DiskCover D X E := by
  intro z c u hz hc hTu
  set w0 : ℂ := ((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I with hw0
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  -- `T_c u = z` gives `z - c = conj u ^ 2`.
  have hzc : z - c = (starRingEnd ℂ u) ^ 2 := by
    rw [← hTu]
    simp only [LeanEval.ComplexAnalysis.Tantibar]
    ring
  -- `‖w₀‖ ^ 2 = w0re ^ 2 + w0im ^ 2`.
  have hw0n : ‖w0‖ ^ 2 = (w0re : ℝ) ^ 2 + (w0im : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw0]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
    ring
  have hs2' : (s : ℝ) ^ 2 ≤ ‖w0‖ ^ 2 := by rw [hw0n]; exact hs2
  -- `s ^ 2 ≤ ‖u‖ ^ 2` from `s ^ 2 ≤ ‖z - c‖ = ‖conj u ^ 2‖`.
  have hsu : (s : ℝ) ^ 2 ≤ ‖u‖ ^ 2 := by
    have h := hZl z c hz hc
    rw [hzc, norm_pow, Complex.norm_conj] at h
    exact h
  -- The product of the two distances.
  have hab : ‖u - starRingEnd ℂ w0‖ * ‖u + starRingEnd ℂ w0‖
      ≤ (ρ : ℝ) * (2 * (s : ℝ) - (ρ : ℝ)) := by
    have h := hZ z c hz hc
    rw [hzc, ← Complex.norm_conj, conj_sq_sub_sharp u w0, norm_mul] at h
    exact h
  -- The parallelogram identity gives `a ^ 2 + b ^ 2 ≥ 4 s ^ 2`.
  have h4 : 4 * (s : ℝ) ^ 2
      ≤ ‖u - starRingEnd ℂ w0‖ ^ 2 + ‖u + starRingEnd ℂ w0‖ ^ 2 := by
    have hpar := parallelogram_law_with_norm (𝕜 := ℂ) u (starRingEnd ℂ w0)
    have h1 : ‖u - starRingEnd ℂ w0‖ ^ 2 + ‖u + starRingEnd ℂ w0‖ ^ 2
        = 2 * (‖u‖ ^ 2 + ‖starRingEnd ℂ w0‖ ^ 2) := by
      linarith [hpar]
    have hww : (s : ℝ) ^ 2 ≤ ‖starRingEnd ℂ w0‖ ^ 2 := by
      rw [Complex.norm_conj]; exact hs2'
    rw [h1]
    linarith
  obtain h | h := sharp_min_le hρ0 hab h4
  · exact Or.inl (hE u h)
  · refine Or.inr (hE (-u) ?_)
    have heq : ‖(-u) - starRingEnd ℂ w0‖ = ‖u + starRingEnd ℂ w0‖ := by
      rw [show (-u) - starRingEnd ℂ w0 = -(u + starRingEnd ℂ w0) by ring, norm_neg]
    rw [heq]
    exact h

end Work.SeedCertRay
