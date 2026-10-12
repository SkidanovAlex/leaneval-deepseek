import ChallengeDeps
import Submission.Work.BoseB1Cube.sbCut_cube_le_mu
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSWE.regularBandThreshold`

The two vanishing-constant thresholds of the regular (band) branch: for **every** prescribed
constants `Cp, κ ≥ 0` there is a diluteness threshold `ε₀ > 0` such that at every admissible `μ`

    Cp · (sbCut μ (a v))³ ≤ μ / 100     and     κ · PBΓ v μ ≤ 1 / 50 .

Both quantities are explicit monomials in the diluteness `t = μ (a v)³`:

* `PBΓ v μ = K_B³ (μ(a v)³)^{1/2} = t^{287/646}` (`Work.BoseFixB1B.PBΓ_eq_rpow` here), and
* `(sbCut μ (a v))³ = μ · t^{145/323}` (the exact cube identity
  `Work.BoseB1Cube.sbCut_cube_eq_mul`),

so both thresholds are of the form `t ≤ ε` with `ε` determined by `Cp`, `κ`.  Note
`145/323 = 290/646 ≥ 287/646`, hence for `0 < t ≤ 1` one has `t^{145/323} ≤ t^{287/646} ≤ t^{287/646}`;
this is why a *single* threshold `t ≤ (max 1 (100Cp) (50κ))^{−646/287}` suffices for both rows.
-/

namespace Work.BoseSWE

open _root_.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The exact closed form of FS's `Γ`**: `PBΓ v μ = (μ (a v)³)^{287/646}`.

`PBΓ v μ = dlGamma (K_B) μ (a v) = K_B³·(μ(a v)³)^{1/2}` with `K_B = (μ(a v)³)^{−6/323}`, so
`PBΓ = (μ(a v)³)^{−18/323+1/2} = (μ(a v)³)^{287/646}`. -/
lemma PBΓ_eq_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hav : 0 < a v) (hμ : 0 < μ) :
    Work.BoseFixB1B.PBΓ v μ = (μ * (a v) ^ 3) ^ ((287 : ℝ) / 646) := by
  rw [Work.BoseFixB1B.PBΓ, Work.FockBridge.dlGamma, Work.BoseFixB1B.PBKB]
  simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have ht : 0 < μ * (a v) ^ 3 := by positivity
  rw [← Real.rpow_natCast ((μ * (a v) ^ 3) ^ (-6 / 323 : ℝ)) 3, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_add ht]
  norm_num

/-- **The two vanishing-constant thresholds.**  Taking
`ε₀ := min 1 (min (100Cp+1)^{−323/145} (50κ+1)^{−646/287})` makes both rows hold: for
`t = μ(a v)³ ≤ ε₀ ≤ 1` one has `t^{145/323} ≤ t^{287/646} ≤ (max 1 (100Cp) (50κ))^{−1}`, and the
two rows are `Cp·sbCut³ = μ·Cp·t^{145/323} ≤ μ/100` and `κ·PBΓ = κ·t^{287/646} ≤ 1/50`. -/
theorem regularBandThreshold {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {Cp κ : ℝ} (hCp : 0 ≤ Cp) (hκ : 0 ≤ κ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      Cp * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3 ≤ μ / 100
      ∧ κ * Work.BoseFixB1B.PBΓ v μ ≤ 1 / 50 := by
  refine ⟨min 1 (min ((100 * Cp + 1) ^ (-(323 / 145 : ℝ)))
      ((50 * κ + 1) ^ (-(646 / 287 : ℝ)))), ?_, ?_⟩
  · refine lt_min one_pos (lt_min ?_ ?_)
    · exact Real.rpow_pos_of_pos (by linarith) _
    · exact Real.rpow_pos_of_pos (by linarith) _
  · intro μ hAdm
    have hμ : 0 < μ := hAdm.1
    have hM1 : 0 < 100 * Cp + 1 := by linarith
    have hM2 : 0 < 50 * κ + 1 := by linarith
    have ht0 : 0 < μ * (a v) ^ 3 := by positivity
    have ht1 : μ * (a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_left _ _)
    have htA : μ * (a v) ^ 3 ≤ (100 * Cp + 1) ^ (-(323 / 145 : ℝ)) :=
      le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
    have htB : μ * (a v) ^ 3 ≤ (50 * κ + 1) ^ (-(646 / 287 : ℝ)) :=
      le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
    -- the two monomial bounds `t^{145/323} ≤ (100Cp+1)⁻¹`, `t^{287/646} ≤ (50κ+1)⁻¹`
    have hpowA : (μ * (a v) ^ 3) ^ ((145 : ℝ) / 323) ≤ (100 * Cp + 1)⁻¹ := by
      have hstep : (μ * (a v) ^ 3) ^ ((145 : ℝ) / 323)
          ≤ ((100 * Cp + 1) ^ (-(323 / 145 : ℝ))) ^ ((145 : ℝ) / 323) :=
        Real.rpow_le_rpow ht0.le htA (by norm_num)
      rwa [← Real.rpow_mul hM1.le,
        show -(323 / 145 : ℝ) * ((145 : ℝ) / 323) = -1 by norm_num, Real.rpow_neg_one] at hstep
    have hpowB : (μ * (a v) ^ 3) ^ ((287 : ℝ) / 646) ≤ (50 * κ + 1)⁻¹ := by
      have hstep : (μ * (a v) ^ 3) ^ ((287 : ℝ) / 646)
          ≤ ((50 * κ + 1) ^ (-(646 / 287 : ℝ))) ^ ((287 : ℝ) / 646) :=
        Real.rpow_le_rpow ht0.le htB (by norm_num)
      rwa [← Real.rpow_mul hM2.le,
        show -(646 / 287 : ℝ) * ((287 : ℝ) / 646) = -1 by norm_num, Real.rpow_neg_one] at hstep
    -- the two pure-real bookkeeping inequalities
    have hA3 : Cp * (100 * Cp + 1)⁻¹ ≤ (1 : ℝ) / 100 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hM1]
      linarith
    have hB3 : κ * (50 * κ + 1)⁻¹ ≤ (1 : ℝ) / 50 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hM2]
      linarith
    have hcube : (Work.BoseFixB1.sbCut μ (a v)) ^ 3
        = μ * (μ * (a v) ^ 3) ^ ((145 : ℝ) / 323) := by
      rw [Work.BoseB1Cube.sbCut_cube_eq_mul hμ hav]
      simp only [Work.BoseBox.fsXp]
    constructor
    · calc Cp * (Work.BoseFixB1.sbCut μ (a v)) ^ 3
          = Cp * (μ * (μ * (a v) ^ 3) ^ ((145 : ℝ) / 323)) := by rw [hcube]
        _ ≤ Cp * (μ * (100 * Cp + 1)⁻¹) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowA hμ.le) hCp
        _ = μ * (Cp * (100 * Cp + 1)⁻¹) := by ring
        _ ≤ μ * ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_left hA3 hμ.le
        _ = μ / 100 := by ring
    · calc κ * Work.BoseFixB1B.PBΓ v μ
          = κ * (μ * (a v) ^ 3) ^ ((287 : ℝ) / 646) := by rw [PBΓ_eq_rpow hav hμ]
        _ ≤ κ * (50 * κ + 1)⁻¹ := mul_le_mul_of_nonneg_left hpowB hκ
        _ ≤ 1 / 50 := hB3

end Work.BoseSWE
