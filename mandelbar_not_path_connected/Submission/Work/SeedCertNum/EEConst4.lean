/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Item E-E: the **`R = 4`** constants of the petal model (the ray area's interface)

The sibling module `EEConst.lean` certifies the petal model at `R = 7`, `ρ₁ = 2^-12` with the
conservative `M = Kee/6` (`Kee = 5056372`).  The ray area `SeedCertRay` however certifies its
level-`71..80` disks only against `Re w < -4` (its emitted integer data has `RRM = 4 · 2^40`), and
its data is *tight*: re-running the emitted `petalDskB` inequality with `RRM = 5 · 2^40` already
fails at every level `71..80`.  `R = 4` is therefore forced, and with `R = 4` the conditions
`(C1)`, `(C2)` of `petal_P1`/`petal_P2` require `M < |A|²/(3a)` with `a = ‖A‖ρ₁ ≥ 1/4`, i.e.
`M < 645000` — strictly less than the `5056372/6 = 842729` of `EEConst.lean`.

This file supplies the sharper constants obtained from the *quarter-box* enclosure of `F'''`
(`Submission/Work/SeedCertNum/EESplit.lean`, where the `decide` checks that certify `Kee4` live):

* `ρ₂ = 2^-11` (the same Taylor radius as `EE.lean`);
* `ρ₁ = 1/2724` — the exact `(C2)` boundary `1/(‖A‖ρ₁) ≤ 4` at `‖A‖ = 681`; the largest `δ` comes
  from the smallest `ρ₁` that `(C2)` allows;
* `R = 4`, `δ = 1/32`;
* `Kee4 = 3400002` (a bound on `‖F'''‖` over the same box `Xz ⊕ [-ρ₂,ρ₂]²`, from the four
  quarter-boxes), `M = Kee4/6 = 566667`.

`ee_petal_constants4` discharges *all* the numerical hypotheses of `petal_P1`/`petal_P2`.
-/
import Mathlib
import Submission.Work.SeedCertNum.EE
import Submission.Work.SeedCertNum.A3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

/-- The certified bound `‖F'''‖ ≤ Kee4` over the four quarter boxes of `Xz2` (`EESplit.lean`). -/
def Kee4 : Dya := dy 3400002 0

/-- The Taylor constant `M = Kee4/6`. -/
def Mee4 : ℝ := Kee4.toReal / 6

/-- The petal radius `ρ₁ = 1/2724` (the `(C2)` boundary at `‖A‖ = 681`). -/
def rho1R4 : ℝ := 1 / 2724

/-- The Taylor radius `ρ₂ = 2^-11` (the same box `Xz2` as in `EE.lean`). -/
def rho2R4 : ℝ := rho2.toReal

/-- The petal depth of the ray area's certificate. -/
def RpetalR4 : ℝ := 4

/-- The petal drift. -/
def deltapR4 : ℝ := 1 / 32

theorem Kee4_toReal : Kee4.toReal = 3400002 := by simp [Kee4, dy, Dya.toReal]

theorem Mee4_eq : Mee4 = 566667 := by rw [Mee4, Kee4_toReal]; norm_num

theorem rho2R4_eq : rho2R4 = 2 ^ (-11 : ℤ) := rho2R

theorem rho1R4_pos : 0 < rho1R4 := by norm_num [rho1R4]

theorem rho1R4_lt_rho2R4 : rho1R4 < rho2R4 := by
  rw [rho1R4, rho2R4_eq]; norm_num

/-- **The `R = 4` constants of the petal model.**  Every numerical hypothesis of
`petal_P1`/`petal_P2` at the certified point: `A ≠ 0`, `0 < ρ₁ < ρ₂`, `0 < δ`, `1 ≤ R‖A‖ρ₁`
(equivalently `R ≥ 1/(‖A‖ρ₁)`, i.e. `Petal ⊆ closedBall z₁ ρ₁`), the smallness
`a(1+κ) < 1`, and the conditions `(C1)`, `(C2)`. -/
theorem ee_petal_constants4 :
    Aquad ≠ 0 ∧ 0 < rho1R4 ∧ 0 < deltapR4 ∧ rho1R4 < rho2R4 ∧
    1 ≤ RpetalR4 * ‖Aquad‖ * rho1R4 ∧
    (‖Aquad‖ * rho1R4) * (1 + Mee4 * rho1R4 / ‖Aquad‖) < 1 ∧
    Mee4 * rho1R4 / ‖Aquad‖ +
      (‖Aquad‖ * rho1R4) * (1 + Mee4 * rho1R4 / ‖Aquad‖) ^ 2 /
        (1 - (‖Aquad‖ * rho1R4) * (1 + Mee4 * rho1R4 / ‖Aquad‖)) ≤ 1 - deltapR4 ∧
    RpetalR4 ≥ 1 / (‖Aquad‖ * rho1R4) := by
  obtain ⟨hlo, hhi⟩ := Aquad_norm_bounds
  have hA := Aquad_ne_zero
  have hApos : 0 < ‖Aquad‖ := norm_pos_iff.mpr hA
  have hs : (‖Aquad‖ * rho1R4) * (1 + Mee4 * rho1R4 / ‖Aquad‖) ≤ 0.3272 := by
    rw [Mee4_eq, rho1R4]
    have := hApos
    field_simp
    nlinarith [hlo, hhi]
  refine ⟨hA, rho1R4_pos, by norm_num [deltapR4], rho1R4_lt_rho2R4, ?_, ?_, ?_, ?_⟩
  · rw [RpetalR4, rho1R4]; nlinarith
  · exact lt_of_le_of_lt hs (by norm_num)
  · have ha : 0 ≤ ‖Aquad‖ * rho1R4 := mul_nonneg (norm_nonneg _) rho1R4_pos.le
    have hk : Mee4 * rho1R4 / ‖Aquad‖ ≤ 0.3055 := by
      rw [Mee4_eq, rho1R4, div_le_iff₀ hApos]
      nlinarith [hlo]
    have h1k : (1 : ℝ) ≤ 1 + Mee4 * rho1R4 / ‖Aquad‖ := by
      have h3 : 0 ≤ Mee4 * rho1R4 / ‖Aquad‖ :=
        div_nonneg (mul_nonneg (by rw [Mee4_eq]; norm_num) rho1R4_pos.le) hApos.le
      linarith
    have h2k : 1 + Mee4 * rho1R4 / ‖Aquad‖ ≤ 1.3055 := by linarith [hk]
    have hden : 0.6728 ≤ 1 - ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖) := by
      linarith [hs]
    have hdenpos : 0 < 1 - ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖) := by
      linarith [hs]
    have hprod : ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖) ^ 2
        ≤ 0.3272 * 1.3055 := by
      calc ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖) ^ 2
          = (‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖))
              * (1 + Mee4 * rho1R4 / ‖Aquad‖) := by ring
        _ ≤ 0.3272 * 1.3055 :=
            mul_le_mul hs h2k (le_trans (by linarith [h1k]) (by norm_num)) (by norm_num)
    have hfr : ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖) ^ 2 /
        (1 - ‖Aquad‖ * rho1R4 * (1 + Mee4 * rho1R4 / ‖Aquad‖)) ≤ 0.6350 := by
      rw [div_le_iff₀ hdenpos]
      have hA2 : (0.3272 : ℝ) * 1.3055 ≤ 0.6350 * 0.6728 := by norm_num1
      have hA3 : 0.6350 * 0.6728 ≤ 0.6350 * (1 - ‖Aquad‖ * rho1R4
          * (1 + Mee4 * rho1R4 / ‖Aquad‖)) := by linarith [hden]
      linarith
    have hd : (1 : ℝ) - deltapR4 = 31 / 32 := by norm_num [deltapR4]
    rw [hd]; linarith
  · rw [RpetalR4, rho1R4, ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < ‖Aquad‖ * (1 / 2724))]
    nlinarith [hlo]

end

end Work.SeedCert
