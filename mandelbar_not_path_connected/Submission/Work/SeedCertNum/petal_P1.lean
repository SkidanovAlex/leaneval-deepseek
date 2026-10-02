import Mathlib
import Submission.Work.SeedCertNum.Petal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- The algebraic step of `petal_P1`: writing `u' = u (1 + A u + ε)`, the Fatou coordinate at
`u'` equals the Fatou coordinate at `u` plus `1` plus the explicit error term
`η = -w(u) ε + w(u) (A u + ε)² / (1 + A u + ε)`.  The two hypotheses `hu`, `hε` are exactly the
non-vanishing of the factors of `A u' = A u (1 + A u + ε)`. -/
theorem fatouW_step {z₁ A u ε : ℂ} (hA : A ≠ 0) (hu : u ≠ 0) (hε : 1 + A * u + ε ≠ 0) :
    fatouW z₁ A (z₁ + u * (1 + A * u + ε)) =
      fatouW z₁ A (z₁ + u) + 1 +
        (-(fatouW z₁ A (z₁ + u) * ε) +
          fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε)) := by
  simp only [fatouW]
  have h1 : z₁ + u * (1 + A * u + ε) - z₁ = u * (1 + A * u + ε) := by ring
  have h2 : z₁ + u - z₁ = u := by ring
  rw [h1, h2]
  field_simp
  ring

/-- **P1 of the petal model** (`NOTES_LEAD_mandelbar_noncusp.md` §2.5): points of the sphere
`‖u‖ = ρ₁` are mapped by `F` *out of* the repelling petal `Work.SeedCert.petal z₁ A R`.

The hypotheses are the Taylor model, the smallness of the quadratic part, and the two certified
constants: `F (z₁ + u) = z₁ + u + A u² + E u` and `‖E u‖ ≤ M ‖u‖³` for `‖u‖ ≤ ρ₂` (with `ρ₁ < ρ₂`),
`A ≠ 0`, and, with `a := ‖A‖ ρ₁`, `κ := M ρ₁ / ‖A‖`,
  `a (1 + κ) < 1`   (so that `1 + A u + ε` stays away from `0`),
  `(C1) κ + a (1+κ)² / (1 - a (1+κ)) ≤ 1 - δ`   and   `(C2) R ≥ 1/a`.

Proof: put `u' := F (z₁+u) - z₁ = u (1 + A u + ε)` with `ε = E u / u`, `‖ε‖ ≤ M ρ₁² = κ a`; then
`w(u') = -1/(A u') = w(u) + 1 + η` with
`η = -w(u) ε + w(u) (A u + ε)²/(1 + A u + ε)`, `|w(u)| = 1/a`, `|A u| = a`,
`|A u + ε| ≤ a(1+κ)`, `|1 + A u + ε| ≥ 1 - a(1+κ) > 0` (using `a(1+κ) < 1`), whence `‖η‖ ≤ η*`
with `η*` the left hand side of `(C1)`.  Hence
`Re w(u') ≥ Re w(u) + 1 - η* ≥ -1/a + δ > -R` (using `Re w(u) ≥ -|w(u)| = -1/a` and `(C2)`), so
`u' ∉ petal z₁ A R`; and `u' ≠ 0` because `u ≠ 0`. -/
theorem petal_P1 {F E : ℂ → ℂ} {z₁ A : ℂ} {M ρ₁ ρ₂ δ R : ℝ}
    (hA : A ≠ 0) (hM : 0 ≤ M) (hρ₁ : 0 < ρ₁) (hρρ : ρ₁ < ρ₂) (hδ : 0 < δ)
    (hsmall : (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) < 1)
    (hmodel : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → F (z₁ + u) = z₁ + u + A * u ^ 2 + E u)
    (hE : ∀ u : ℂ, ‖u‖ ≤ ρ₂ → ‖E u‖ ≤ M * ‖u‖ ^ 3)
    (hC1 : M * ρ₁ / ‖A‖ + (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖) ^ 2
              / (1 - (‖A‖ * ρ₁) * (1 + M * ρ₁ / ‖A‖)) ≤ 1 - δ)
    (hC2 : 1 / (‖A‖ * ρ₁) ≤ R) :
    ∀ u : ℂ, ‖u‖ = ρ₁ → F (z₁ + u) ∉ Work.SeedCert.petal z₁ A R := by
  intro u hu
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    linarith
  have hule : ‖u‖ ≤ ρ₂ := by rw [hu]; exact hρρ.le
  set a : ℝ := ‖A‖ * ρ₁ with ha
  set κ : ℝ := M * ρ₁ / ‖A‖ with hκ
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hsmall' : a * (1 + κ) < 1 := by rw [ha, hκ]; exact hsmall
  have hD_pos : 0 < 1 - a * (1 + κ) := by linarith
  have hC1' : κ + a * (1 + κ) ^ 2 / (1 - a * (1 + κ)) ≤ 1 - δ := by
    rw [ha, hκ]; exact hC1
  have hC2' : 1 / a ≤ R := by rw [ha]; exact hC2
  -- the error term `ε = E u / u`
  set ε : ℂ := E u / u with hε
  have hεu : E u = ε * u := by rw [hε]; field_simp
  have hε_bound : ‖ε‖ ≤ a * κ := by
    have h1 : ‖E u / u‖ ≤ M * ρ₁ ^ 2 := by
      have h : ‖E u‖ ≤ M * ρ₁ ^ 3 := by simpa [hu] using hE u hule
      calc ‖E u / u‖ = ‖E u‖ / ρ₁ := by rw [norm_div, hu]
        _ ≤ M * ρ₁ ^ 3 / ρ₁ := div_le_div_of_nonneg_right h hρ₁.le
        _ = M * ρ₁ ^ 2 := by field_simp
    have h2 : M * ρ₁ ^ 2 = a * κ := by rw [ha, hκ]; field_simp
    rw [hε]
    linarith
  have hFu' : F (z₁ + u) = z₁ + u * (1 + A * u + ε) := by
    rw [hmodel u hule, hεu]
    ring
  -- the elementary norm estimates
  have hAu : ‖A * u‖ = a := by rw [norm_mul, hu, ha]
  have hx_bound : ‖A * u + ε‖ ≤ a * (1 + κ) := by
    calc ‖A * u + ε‖ ≤ ‖A * u‖ + ‖ε‖ := norm_add_le _ _
      _ ≤ a + a * κ := by rw [hAu]; linarith [hε_bound]
      _ = a * (1 + κ) := by ring
  have hd_lb : 1 - a * (1 + κ) ≤ ‖1 + A * u + ε‖ := by
    have h := norm_sub_le ((1 : ℂ) + (A * u + ε)) (A * u + ε)
    rw [add_sub_cancel_right, norm_one] at h
    have h2 : (1 : ℂ) + (A * u + ε) = 1 + A * u + ε := by ring
    rw [h2] at h
    linarith [hx_bound]
  have hden : 1 + A * u + ε ≠ 0 := by
    have hpos : 0 < ‖1 + A * u + ε‖ := lt_of_lt_of_le hD_pos hd_lb
    intro h0
    rw [h0, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hw : ‖fatouW z₁ A (z₁ + u)‖ = 1 / a := by
    simp only [fatouW]
    have h2 : z₁ + u - z₁ = u := by ring
    rw [h2, ha]
    simp [hu]
  -- the algebraic identity `w(u') = w(u) + 1 + η`
  set η : ℂ := -(fatouW z₁ A (z₁ + u) * ε) +
      fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε) with hη
  have hid : fatouW z₁ A (F (z₁ + u)) = fatouW z₁ A (z₁ + u) + 1 + η := by
    rw [hFu', hη]
    exact fatouW_step hA hu0 hden
  -- the two halves of the bound `‖η‖ ≤ η*`
  have hterm1 : ‖fatouW z₁ A (z₁ + u) * ε‖ ≤ κ := by
    rw [norm_mul, hw]
    calc (1 / a) * ‖ε‖ ≤ (1 / a) * (a * κ) :=
          mul_le_mul_of_nonneg_left hε_bound (by positivity)
      _ = κ := by field_simp
  have hterm2 : ‖fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε)‖
      ≤ a * (1 + κ) ^ 2 / (1 - a * (1 + κ)) := by
    rw [norm_div, norm_mul, norm_pow, hw]
    have hnum : (1 / a) * ‖A * u + ε‖ ^ 2 ≤ (1 / a) * (a * (1 + κ)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hx_bound 2) (by positivity)
    calc (1 / a) * ‖A * u + ε‖ ^ 2 / ‖1 + A * u + ε‖
        ≤ (1 / a) * (a * (1 + κ)) ^ 2 / (1 - a * (1 + κ)) :=
          div_le_div₀ (by positivity) hnum hD_pos hd_lb
      _ = a * (1 + κ) ^ 2 / (1 - a * (1 + κ)) := by field_simp
  have hη_bound : ‖η‖ ≤ κ + a * (1 + κ) ^ 2 / (1 - a * (1 + κ)) := by
    have hsplit : ‖η‖ ≤ ‖fatouW z₁ A (z₁ + u) * ε‖
        + ‖fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε)‖ := by
      rw [hη]
      calc ‖-(fatouW z₁ A (z₁ + u) * ε) +
              fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε)‖
          ≤ ‖-(fatouW z₁ A (z₁ + u) * ε)‖
            + ‖fatouW z₁ A (z₁ + u) * (A * u + ε) ^ 2 / (1 + A * u + ε)‖ :=
            norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith [hsplit, hterm1, hterm2]
  -- real part of the identity
  have hwre : -(1 / a) ≤ (fatouW z₁ A (z₁ + u)).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (fatouW z₁ A (z₁ + u)))).1
    rw [hw] at h
    exact h
  have hre : (fatouW z₁ A (F (z₁ + u))).re
      = (fatouW z₁ A (z₁ + u)).re + 1 + η.re := by
    rw [hid]
    simp [Complex.add_re]
  have hmain : -R < (fatouW z₁ A (F (z₁ + u))).re := by
    have heta : -‖η‖ ≤ η.re := (abs_le.mp (Complex.abs_re_le_norm η)).1
    have h1 : -(1 / a) + 1 - (κ + a * (1 + κ) ^ 2 / (1 - a * (1 + κ)))
        ≤ (fatouW z₁ A (F (z₁ + u))).re := by
      rw [hre]
      linarith [hwre, heta, hη_bound]
    linarith [h1, hC1', hC2', hδ]
  simp only [Work.SeedCert.mem_petal]
  rintro ⟨-, hlt⟩
  linarith [hlt, hmain]

end Work.SeedCertNum
