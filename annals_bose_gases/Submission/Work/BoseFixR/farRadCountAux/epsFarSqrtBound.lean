import ChallengeDeps
import Submission.Work.BoseFixR.FarResidBaux.epsFar_le_inv_eight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `epsFarSqrtBound` — `√(epsFar) ≤ 1/100` and `epsFar^{-1/2} ≥ 1`

The far-leg consumers (`FarRadCount`, `FarCorr`) need the two *scalar* facts

  `√ε ≤ 1/100`  and  `ε^{−1/2} ≥ 1`,   `ε = Work.BoseFixR.epsFar v μ ρ`,

at admissible box data and `ε₀ ≤ 10^{-4000}`.  Both are immediate from the
already-proved `FarResidBaux.epsFar_le_inv_eight : ε ≤ 10^{-8}` together with
`ε > 0`:

* `ε ≤ 10^{-8} ≤ (1/100)²`, so `√ε ≤ 1/100` (`Real.sqrt_le_sqrt`, `Real.sqrt_sq`);
* `ε ≤ 10^{-8} ≤ 1`, so `√ε ≤ 1` (`Real.sqrt_le_one`), and
  `ε^{−1/2} = (√ε)^{−1} ≥ 1` (`Real.rpow_neg`, `Real.sqrt_eq_rpow`,
  `one_le_inv₀`).

The only point of care is positivity: the version available in
`Work.BoseFixR.FarEnvPos` (`farEnvPos_eps_pos`) assumes `0 < ρ`, while the
statement here assumes only `0 ≤ ρ`.  It is enough, because
`ε = √(𝓜/((ρ+μ)ℓ³))` with `𝓜 > 0` (`bigM_pos_of_params`), `μ > 0`, `ρ ≥ 0` and
`ℓ > 0` (`sideAt_pos`), so the radicand is strictly positive; the lemma
`epsFar_pos_of_nonneg` below records that.

The hypothesis `FarCond v μ ρ` is not used: the bound holds for every `ρ ≥ 0`.
It is carried because the request states it.
-/

namespace Work.BoseFixR.farRadCountAux

set_option linter.unusedVariables false

/-- Positivity of FS's `ε = √(𝓜/((ρ+μ)ℓ³))` at `0 ≤ ρ` (the version in
`Work.BoseFixR.FarEnvPos` needs `0 < ρ`): the radicand is a quotient of a
positive number by the positive product `(ρ+μ)ℓ³` (`ρ ≥ 0`, `μ > 0`, `ℓ > 0`). -/
lemma epsFar_pos_of_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ) :
    0 < Work.BoseFixR.epsFar v μ ρ := by
  have hM : 0 < Work.BoseFixR.bigMV v μ := Work.BoseBox.bigM_pos_of_params hμ hav
  have hℓ : 0 < Work.BoseFixR.ell v μ := by
    rw [Work.BoseFixR.ell]
    exact Work.BoseBox.sideAt_pos hμ hav
  rw [Work.BoseFixR.epsFar]
  exact Real.sqrt_pos_of_pos (div_pos hM (mul_pos (by linarith) (pow_pos hℓ 3)))

theorem epsFarSqrtBound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < BoseGases.a v) (hρ : 0 ≤ ρ) (hfar : Work.BoseFixR.FarCond v μ ρ) :
    Real.sqrt (Work.BoseFixR.epsFar v μ ρ) ≤ 1 / 100
      ∧ (1 : ℝ) ≤ (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) := by
  have hμ : 0 < μ := hAdm.1
  have hεle : Work.BoseFixR.epsFar v μ ρ ≤ 1 / 10 ^ 8 :=
    Work.BoseFixR.FarResidBaux.epsFar_le_inv_eight hAdm hε₀ hav hρ hfar
  have hpos : 0 < Work.BoseFixR.epsFar v μ ρ := epsFar_pos_of_nonneg hμ hav hρ
  refine ⟨?_, ?_⟩
  · -- `√ε ≤ 1/100`: compare squares, `ε ≤ 10^{-8} ≤ (1/100)²`
    have h2 : Work.BoseFixR.epsFar v μ ρ ≤ (1 / 100 : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) / 10 ^ 8 ≤ (1 / 100 : ℝ) ^ 2 := by norm_num
      linarith
    calc Real.sqrt (Work.BoseFixR.epsFar v μ ρ)
        ≤ Real.sqrt ((1 / 100 : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 1 / 100 := Real.sqrt_sq (by norm_num)
  · -- `ε^{-1/2} = (√ε)^{-1} ≥ 1` since `√ε ≤ 1`
    have h1 : Real.sqrt (Work.BoseFixR.epsFar v μ ρ) ≤ 1 := by
      refine Real.sqrt_le_one.mpr ?_
      have h2 : (1 : ℝ) / 10 ^ 8 ≤ 1 := by norm_num
      linarith
    have h3 : (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ))
        = (Real.sqrt (Work.BoseFixR.epsFar v μ ρ))⁻¹ := by
      rw [Real.rpow_neg hpos.le (1 / 2), ← Real.sqrt_eq_rpow]
    rw [h3]
    exact (one_le_inv₀ (Real.sqrt_pos_of_pos hpos)).mpr h1

end Work.BoseFixR.farRadCountAux
