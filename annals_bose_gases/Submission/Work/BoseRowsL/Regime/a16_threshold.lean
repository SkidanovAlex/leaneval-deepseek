import ChallengeDeps
import Submission.Work.BoseGateFS.GateThresholdsExist
import Submission.Work.BoseRowsL.Regime.rkh_threshold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.Regime

/-!
# `Work.BoseRowsL.Regime.a16_threshold` — FS's régime row `a K_H / (s ℓ) ≤ 1/16`

The row `a16` of `Work.BoseRowsL.HonestInterfaceL` (and of
`Work.BoseRowsFS.HonestInterface`): at the honest data `honE v h fc fu HM μ` and
at diluteness `μ (a v)³` below an absolute threshold,

  `aScat · K_H / (s · ℓ) ≤ 1/16`.

## The computation

With `t := μ (a v)³` the three honest scalars are, by definition (and using the
closed forms proved in `Submission/Work/BoseRowsL/Regime/rkh_threshold.lean` and
`Submission/Work/BoseRowsL/Regime/fourR_le_ell.lean`),

* `aScat = a v` (`rfl`),
* `K_H = (t^{549/1292})⁻¹ = t^{-549/1292}` (`honE_KH_eq`),
* `s = t^{1/323}` (`s` is `fsXp t 1`, and `fsXp t c = t^{c/323}`),
* `ℓ = a v · t^{-163/323}` — from `ℓ² = (a v)² t^{-326/323}` (`honE_ell_sq`)
  and `ℓ > 0`.

Hence

  `aScat · K_H / (s · ℓ) = t^{-549/1292} · t^{162/323} = t^{99/1292}`

(the factor `a v` cancels exactly), so the row is *equivalent* to

  `t^{99/1292} ≤ 1/16`,   i.e.   `t ≤ (1/16)^{1292/99}`.

The threshold `ε₁ := (1/16)^{1292/99}` therefore proves the row, and it is
sharp for this row (no factor `a v` or `R` enters — the row is a pure parameter
row, so it holds with an absolute threshold depending only on `a v`; indeed here
not even on `a v`).

The real-variable step is isolated in `a16_rpow_arith`.
-/

set_option linter.unusedVariables false

/-- **The threshold arithmetic of the `a16` row**, in closed form.

For `0 < t` and `t ≤ (1/16)^{1292/99}`,

  `16 · A · t^{-549/1292} ≤ A · t^{-162/323}`.

Indeed `t^{-162/323} = t^{-549/1292} · t^{-99/1292}`, so after cancelling
`t^{-549/1292} > 0` the claim is `16 ≤ t^{-99/1292}`, i.e. `t^{99/1292} ≤ 1/16`,
which is the hypothesis raised to the power `99/1292`:
`((1/16)^{1292/99})^{99/1292} = (1/16)`. -/
lemma a16_rpow_arith {A t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (h : t ≤ (1 / 16 : ℝ) ^ ((1292 : ℝ) / 99)) :
    16 * A * t ^ (-((549 : ℝ) / 1292)) ≤ A * t ^ (-((162 : ℝ) / 323)) := by
  have hpow : t ^ ((99 : ℝ) / 1292) ≤ (16 : ℝ)⁻¹ := by
    have h1 : t ^ ((99 : ℝ) / 1292) ≤ ((1 / 16 : ℝ) ^ ((1292 : ℝ) / 99)) ^ ((99 : ℝ) / 1292) :=
      Real.rpow_le_rpow ht.le h (by norm_num)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)] at h1
    rw [show ((1292 : ℝ) / 99) * ((99 : ℝ) / 1292) = 1 by norm_num, Real.rpow_one] at h1
    simpa using h1
  have hneg : (16 : ℝ) ≤ t ^ (-((99 : ℝ) / 1292)) := by
    rw [Real.rpow_neg ht.le]
    exact (le_inv_comm₀ (by norm_num : (0 : ℝ) < 16)
      (Real.rpow_pos_of_pos ht _)).mpr hpow
  have hexp : -((549 : ℝ) / 1292) + -((99 : ℝ) / 1292) = -((162 : ℝ) / 323) := by norm_num
  have hstep : 16 * t ^ (-((549 : ℝ) / 1292)) ≤ t ^ (-((162 : ℝ) / 323)) := by
    have h2 := mul_le_mul_of_nonneg_left hneg
      (le_of_lt (Real.rpow_pos_of_pos ht (-((549 : ℝ) / 1292))))
    rw [← Real.rpow_add ht, hexp] at h2
    linarith
  have h3 := mul_le_mul_of_nonneg_left hstep hA.le
  linarith

/-- **The honest `s` in closed form**: `s = (μ (a v)³)^{1/323}` (`s` is
`fsXp t 1` and `fsXp t c = t^{c/323}`). -/
lemma honE_s_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).s
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323) := by
  rw [show (Work.BoseRowsFS.honE v h fc fu HM μ).s
        = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 from rfl]
  rw [Work.BoseBox.fsXp, Work.BoseFixR.dil]

/-- **The honest `ℓ` in closed form**: `ℓ = a v · (μ (a v)³)^{-163/323}`.

From `honE_ell_sq` (`ℓ² = (a v)² t^{-326/323}`) and `ℓ > 0`; the sign is fixed
by positivity. -/
lemma honE_ell_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).ell
      = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323)) := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hellpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav]
    exact Work.BoseBoxFock.ellH_pos v μ
  have hell2 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 2
      = (_root_.BoseGases.a v) ^ 2 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((326 : ℝ) / 323)) := by
    rw [Work.BoseRowsL.Regime.honE_ell_sq HM μ hμ hav, div_eq_mul_inv, ← Real.rpow_neg ht0.le]
  have hsq : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 2
      = (_root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323))) ^ 2 := by
    rw [hell2, mul_pow,
      ← Real.rpow_natCast ((μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323))) 2,
      ← Real.rpow_mul ht0.le]
    norm_num
  have hb : 0 ≤ _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323)) := by
    positivity
  have habs : |(Work.BoseRowsFS.honE v h fc fu HM μ).ell|
      = |_root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323))| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rwa [abs_of_nonneg hellpos.le, abs_of_nonneg hb] at habs

/-- **The honest `s · ℓ` in closed form**: `s · ℓ = a v · (μ (a v)³)^{-162/323}`. -/
lemma honE_s_mul_ell_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).s * (Work.BoseRowsFS.honE v h fc fu HM μ).ell
      = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((162 : ℝ) / 323)) := by
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  rw [honE_s_rpow HM μ, honE_ell_rpow HM μ hμ hav]
  calc (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)
        * (_root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323)))
      = _root_.BoseGases.a v * ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((163 : ℝ) / 323))) := by ring
    _ = _root_.BoseGases.a v
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (((1 : ℝ) / 323) + -((163 : ℝ) / 323)) := by
        rw [← Real.rpow_add ht0]
    _ = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((162 : ℝ) / 323)) := by
        norm_num

/-- **FS's régime row `a K_H / (s ℓ) ≤ 1/16` at the honest model**, with an
absolute threshold.

There is `ε₁ > 0` (namely `(1/16)^{1292/99}`, which depends on nothing at all)
such that for every choice `HM` of honest modes and every `μ > 0` with
`μ (a v)³ ≤ ε₁` one has `aScat · K_H / (s · ℓ) ≤ 1/16` at `honE v h fc fu HM μ`.

With `t = μ(a v)³` the quotient is `t^{99/1292}` (the factor `a v` cancels
exactly), so the row is equivalent to `t^{99/1292} ≤ 1/16`; see the module
docstring and `a16_rpow_arith`. -/
theorem a16_threshold {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
      0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₁ →
      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
        / ((Work.BoseRowsFS.honE v h fc fu HM μ).s * (Work.BoseRowsFS.honE v h fc fu HM μ).ell)
        ≤ 1 / 16 := by
  refine ⟨(1 / 16 : ℝ) ^ ((1292 : ℝ) / 99), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro HM μ hμ ht
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hKH : (Work.BoseRowsFS.honE v h fc fu HM μ).KH
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-((549 : ℝ) / 1292)) := by
    rw [Work.BoseRowsL.Regime.honE_KH_eq HM μ hμ hav, ← Real.rpow_neg ht0.le]
  rw [Work.BoseRowsFS.honE_aScat, hKH, honE_s_mul_ell_rpow HM μ hμ hav]
  rw [div_le_iff₀ (by positivity)]
  have hkey := a16_rpow_arith (A := _root_.BoseGases.a v) (t := μ * (_root_.BoseGases.a v) ^ 3)
    hav ht0 ht
  linarith

end Work.BoseRowsL.Regime
