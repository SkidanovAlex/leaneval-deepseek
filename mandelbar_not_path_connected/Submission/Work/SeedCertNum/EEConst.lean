/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Item E-E: the numerical constants of the petal model

The explicit dyadic constants supplied to `petal_P1`/`petal_P2`:
`ρ₂ = 2^-11` (the Taylor radius), `ρ₁ = 2^-12` (the petal radius), `R = 7` (the petal depth),
`δ = 1/4` (the drift), and `M = K/6` with `K = 5056372` the certified bound on `‖F'''‖` over
`Xz ⊕ [-ρ₂,ρ₂]²` (`Submission/Work/SeedCertNum/EE.lean`).

**`R = 4`.**  The ray area needs the *same* model at `R = 4`; that sharper set of constants lives in
`Submission/Work/SeedCertNum/EEConst4.lean` (`ee_petal_constants4`, `RpetalR4 = 4`).

`ee_petal_constants` checks the three conditions of the petal lemma:
`a(1+κ) < 1` with `a = ‖A‖ρ₁`, `κ = Mρ₁/‖A‖`; `(C1)`; `(C2) R ≥ 1/a`; and `1 ≤ R‖A‖ρ₁`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Export
import Submission.Work.SeedCertNum.A3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

/-- The Taylor radius `ρ₂ = 2^-11`. -/
def rho2 : Dya := dy 1 11

/-- The petal radius `ρ₁ = 2^-12`. -/
def rho1 : Dya := dy 1 12

/-- The certified bound `K` for `‖F'''‖`. -/
def Kee : Dya := dy 5056372 0

/-- The Taylor constant `M = K/6`. -/
def Mee : ℝ := Kee.toReal / 6

/-- The petal depth. -/
def Rpetal : ℝ := 7

/-- The petal drift. -/
def deltap : ℝ := 1 / 4

theorem rho2R : rho2.toReal = (2 : ℝ) ^ (-11 : ℤ) := by
  simp [rho2, dy, Dya.toReal]

theorem rho1R : rho1.toReal = (2 : ℝ) ^ (-12 : ℤ) := by
  simp [rho1, dy, Dya.toReal]

theorem rho1_pos : 0 < rho1.toReal := by rw [rho1R]; norm_num

theorem rho1_lt_rho2 : rho1.toReal < rho2.toReal := by
  rw [rho1R, rho2R]; norm_num

theorem Kee_toReal : Kee.toReal = 5056372 := by simp [Kee, dy, Dya.toReal]

theorem Mee_eq : Mee = 5056372 / 6 := by simp [Mee, Kee_toReal]

theorem rho1_eq : rho1.toReal = 1 / 4096 := by rw [rho1R]; norm_num

theorem Aquad_norm_bounds : (681 : ℝ) ≤ ‖Aquad‖ ∧ ‖Aquad‖ ≤ 683 := by
  have hb := Aquad_normsq_bounds
  refine ⟨?_, ?_⟩
  · nlinarith [hb.1, norm_nonneg Aquad]
  · nlinarith [hb.2, norm_nonneg Aquad]

/-- **The constants of the petal model.**  All the numerical hypotheses of `petal_P1`/`petal_P2`
at the certified point: `A ≠ 0`, `0 < ρ₁ < ρ₂`, `0 < δ`, `1 ≤ R‖A‖ρ₁`, the smallness
`a(1+κ) < 1`, and the conditions `(C1)`, `(C2)`. -/
theorem ee_petal_constants :
    Aquad ≠ 0 ∧ 0 < rho1.toReal ∧ 0 < deltap ∧ rho1.toReal < rho2.toReal ∧
    1 ≤ Rpetal * ‖Aquad‖ * rho1.toReal ∧
    (‖Aquad‖ * rho1.toReal) * (1 + Mee * rho1.toReal / ‖Aquad‖) < 1 ∧
    Mee * rho1.toReal / ‖Aquad‖ +
      (‖Aquad‖ * rho1.toReal) * (1 + Mee * rho1.toReal / ‖Aquad‖) ^ 2 /
        (1 - (‖Aquad‖ * rho1.toReal) * (1 + Mee * rho1.toReal / ‖Aquad‖)) ≤ 1 - deltap ∧
    Rpetal ≥ 1 / (‖Aquad‖ * rho1.toReal) := by
  obtain ⟨hlo, hhi⟩ := Aquad_norm_bounds
  have hA := Aquad_ne_zero
  have hApos : 0 < ‖Aquad‖ := norm_pos_iff.mpr hA
  have hs : (‖Aquad‖ * rho1.toReal) * (1 + Mee * rho1.toReal / ‖Aquad‖) ≤ 0.2172 := by
    rw [Mee_eq, rho1_eq]
    have := hApos
    field_simp
    nlinarith [hlo, hhi]
  refine ⟨hA, rho1_pos, by norm_num [deltap], rho1_lt_rho2, ?_, ?_, ?_, ?_⟩
  · rw [Rpetal, rho1_eq]; nlinarith
  · exact lt_of_le_of_lt hs (by norm_num)
  · have ha : 0 ≤ ‖Aquad‖ * rho1.toReal := mul_nonneg (norm_nonneg _) rho1_pos.le
    have hk : Mee * rho1.toReal / ‖Aquad‖ ≤ 0.3022 := by
      rw [Mee_eq, rho1_eq, div_le_iff₀ hApos]
      nlinarith [hlo]
    have h1k : (1 : ℝ) ≤ 1 + Mee * rho1.toReal / ‖Aquad‖ := by
      have h3 : 0 ≤ Mee * rho1.toReal / ‖Aquad‖ :=
        div_nonneg (mul_nonneg (by rw [Mee_eq]; norm_num) rho1_pos.le) hApos.le
      linarith
    have h2k : 1 + Mee * rho1.toReal / ‖Aquad‖ ≤ 1.3022 := by linarith [hk]
    have hden : 0.7828 ≤ 1 - ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖) := by
      linarith [hs]
    have hdenpos : 0 < 1 - ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖) := by
      linarith [hs]
    have hprod : ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖) ^ 2 ≤ 0.2172 * 1.3022 := by
      calc ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖) ^ 2
          = (‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖))
              * (1 + Mee * rho1.toReal / ‖Aquad‖) := by ring
        _ ≤ 0.2172 * 1.3022 := mul_le_mul hs h2k (le_trans (by linarith [h1k]) (by norm_num)) (by norm_num)
    have hfr : ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖) ^ 2 /
        (1 - ‖Aquad‖ * rho1.toReal * (1 + Mee * rho1.toReal / ‖Aquad‖)) ≤ 0.3615 := by
      rw [div_le_iff₀ hdenpos]
      have hA2 : (0.2172 : ℝ) * 1.3022 ≤ 0.3615 * 0.7828 := by norm_num1
      have hA3 : 0.3615 * 0.7828 ≤ 0.3615 * (1 - ‖Aquad‖ * rho1.toReal
          * (1 + Mee * rho1.toReal / ‖Aquad‖)) := by linarith [hden]
      linarith
    have hd : (1 : ℝ) - deltap = 3 / 4 := by norm_num [deltap]
    rw [hd]; linarith
  · rw [Rpetal, rho1_eq, ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < ‖Aquad‖ * (1 / 4096))]
    nlinarith [hlo]

end

end Work.SeedCert
