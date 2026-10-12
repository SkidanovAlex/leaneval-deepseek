import ChallengeDeps
import Submission.Work.BoseFixGlue.Params.kinRegime_of_params
import Submission.Work.BoseFixKin.FSRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixKin

/-!
# `Work.BoseFixKin.kinRegimeFS_of_params` — FS's parameter block is in the coupled regime

Node G1 of `BOSE_BCLASH_LEAD.md`.  The coupled regime `KinRegimeFS` (see `FSRegime.lean`)
bounds `b` only by the fixed FS constant `1/16`, keeps `s, ε_T ≤ c₀`, and adds the coupling
`ε_T · s ≤ c₀ · d`.  This file shows that FS's own parameter block satisfies it as soon as the
diluteness `t = μ (a v)³` is below the threshold `min 1 ((min c₀ 1)^431)`.

The two arithmetic ingredients (with `X = t^{1/323}`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`):

* `s, ε_T ≤ c₀` needs `X ≤ c₀`, i.e. `t ≤ c₀^323`;
* `ε_T s ≤ c₀ d` ⟺ `X^{3/4} ≤ c₀` (divide `X^{27/4} ≤ c₀ X⁶` by `X⁶`), i.e.
  `t^{3/1292} ≤ c₀`, i.e. `t ≤ c₀^{1292/3}`;

and `t ≤ min 1 ((min c₀ 1)^431)` implies `t ≤ c₀^γ` for every `0 ≤ γ ≤ 431` — because either
`c₀ ≥ 1`, in which case `t ≤ 1 ≤ c₀^γ`, or `c₀ < 1`, in which case `t ≤ c₀^431 ≤ c₀^γ`.  Both
`323 ≤ 431` and `1292/3 ≤ 431` (i.e. `431 · (3/4)/323 = 1293/1292 > 1`).  `b = bValue = 1/16`
gives `b ≤ 1/16` by `norm_num`.
-/

/-- **The `min 1`-threshold arithmetic.**  If `0 < c₀` and `t ≤ min 1 (c₀^δ)`, then
`t ≤ c₀^γ` for every `0 ≤ γ ≤ δ`: for `c₀ ≥ 1` one has `t ≤ 1 ≤ c₀^γ` (so the `min 1` is what
makes the statement true there), and for `c₀ < 1` the function `x ↦ c₀^x` is antitone. -/
theorem le_pow_of_le_min_one {t c₀ δ γ : ℝ} (hc₀ : 0 < c₀) (hγ : 0 ≤ γ) (hγδ : γ ≤ δ)
    (ht : t ≤ min 1 (c₀ ^ δ)) : t ≤ c₀ ^ γ := by
  by_cases h1 : 1 ≤ c₀
  · rw [min_eq_left (Real.one_le_rpow h1 (le_trans hγ hγδ))] at ht
    exact le_trans ht (Real.one_le_rpow h1 hγ)
  · have h1' : c₀ ≤ 1 := le_of_lt (not_le.mp h1)
    exact le_trans (le_trans ht (min_le_right _ _))
      (Real.rpow_le_rpow_of_exponent_ge hc₀ h1' hγδ)

/-- **`fsXp` below a threshold.**  For `c > 0`, the parameter `fsXp t c = t^{c/323}` is at most
`c₀` as soon as `t ≤ c₀^{323/c}` (raise both sides to the power `c/323`). -/
theorem fsXp_le_of_pow_le {t c₀ c : ℝ} (ht : 0 < t) (hc₀ : 0 < c₀) (hc : 0 < c)
    (htc : t ≤ c₀ ^ (323 / c)) : Work.BoseBox.fsXp t c ≤ c₀ := by
  have h1 : t ^ (c / 323) ≤ (c₀ ^ (323 / c)) ^ (c / 323) :=
    Real.rpow_le_rpow ht.le htc (by positivity)
  have h2 : (c₀ ^ (323 / c)) ^ (c / 323) = c₀ := by
    rw [← Real.rpow_mul hc₀.le, show 323 / c * (c / 323) = 1 by field_simp, Real.rpow_one]
  exact le_of_le_of_eq h1 h2

/-- **FS's parameter block satisfies the coupled regime `KinRegimeFS` for small diluteness**
(node G1 of `BOSE_BCLASH_LEAD.md`).

Threshold `ε := min 1 ((min c₀ 1)^431)`: with `t := μ (a v)³` and `X := t^(1/323)`, one has
`s = X`, `ε_T = X^(23/4)`, `d = X⁶` and `ε_T s = d · t^((3/4)/323)`, so `s, ε_T ≤ c₀` needs
`t ≤ c₀^323`, while the coupling `ε_T s ≤ c₀ d` needs `t^((3/4)/323) ≤ c₀`, i.e.
`t ≤ c₀^(1292/3)`, and `431 · (3/4)/323 = 1293/1292 > 1`.  `b = bValue = 1/16` gives
`b ≤ 1/16` by `norm_num`.  Template: `Submission/Work/BoseFixGlue/Params/kinRegime_of_params.lean`
(its `fsXp_le_of_small_diluteness` and its ten-conjunct unfold are reusable verbatim).

This is the `KinRegimeFS` analogue of `Work.BoseFixGlue.Params.kinRegime_of_params`; note the
list of ten conjuncts differs: `KinRegimeFS` has no `d ≤ c₀`, but has `d ≤ 1`, `s ≤ c₀`,
`ε_T ≤ c₀` and `ε_T * s ≤ c₀ * d`. -/
theorem kinRegimeFS_of_params {v : ℝ³ → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε →
      KinRegimeFS c₀ (Work.BoseFixGlue.ℓB v μ) (Work.BoseFixGlue.dB v μ)
        (Work.BoseFixGlue.sB v μ) (Work.BoseFixGlue.eTB v μ) (Work.BoseFixGlue.bB v μ) := by
  refine ⟨min 1 ((min c₀ 1) ^ (431 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos (lt_min hc₀ one_pos) _), ?_⟩
  intro μ hμ hle
  have hav3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  -- name the diluteness `t = μ (a v)³`
  set t : ℝ := μ * (_root_.BoseGases.a v) ^ 3 with ht_def
  have ht : 0 < t := by rw [ht_def]; exact mul_pos hμ hav3
  have ht1 : t ≤ 1 := le_trans hle (min_le_left _ _)
  -- the threshold is below `c₀^431`
  have hmin : (min c₀ 1) ^ (431 : ℝ) ≤ c₀ ^ (431 : ℝ) := by
    by_cases h1 : 1 ≤ c₀
    · rw [min_eq_right h1, Real.one_rpow]
      exact Real.one_le_rpow h1 (by norm_num)
    · rw [min_eq_left (le_of_lt (not_le.mp h1))]
  have ht431 : t ≤ c₀ ^ (431 : ℝ) := le_trans hle (le_trans (min_le_right _ _) hmin)
  have hmin1 : t ≤ min 1 (c₀ ^ (431 : ℝ)) := le_min ht1 ht431
  -- the three exponents actually needed, all `≤ 431`
  have htc323 : t ≤ c₀ ^ (323 : ℝ) :=
    le_pow_of_le_min_one (δ := 431) (γ := 323) hc₀ (by norm_num) (by norm_num) hmin1
  have htc56 : t ≤ c₀ ^ (1292 / 23 : ℝ) :=
    le_pow_of_le_min_one (δ := 431) (γ := 1292 / 23) hc₀ (by norm_num) (by norm_num) hmin1
  have htc430 : t ≤ c₀ ^ (1292 / 3 : ℝ) :=
    le_pow_of_le_min_one (δ := 431) (γ := 1292 / 3) hc₀ (by norm_num) (by norm_num) hmin1
  -- `s = X ≤ c₀`
  have hX : Work.BoseBox.fsXp t 1 ≤ c₀ := by
    refine fsXp_le_of_pow_le (c := 1) ht hc₀ (by norm_num) ?_
    rw [show (323 : ℝ) / 1 = 323 by norm_num]; exact htc323
  -- `ε_T = X^{23/4} ≤ c₀` (`323/(23/4) = 1292/23 ≤ 431`)
  have heT : Work.BoseBox.fsXp t (23 / 4) ≤ c₀ := by
    refine fsXp_le_of_pow_le (c := 23 / 4) ht hc₀ (by norm_num) ?_
    rw [show (323 : ℝ) / (23 / 4) = 1292 / 23 by norm_num]; exact htc56
  -- `X^{3/4} = t^{(3/4)/323} ≤ c₀` (`323/(3/4) = 1292/3 ≤ 431`)
  have hX34 : Work.BoseBox.fsXp t (3 / 4) ≤ c₀ := by
    refine fsXp_le_of_pow_le (c := 3 / 4) ht hc₀ (by norm_num) ?_
    rw [show (323 : ℝ) / (3 / 4) = 1292 / 3 by norm_num]; exact htc430
  -- `d = X⁶ ≤ 1`
  have hd1 : Work.BoseBox.fsXp t 6 ≤ 1 := Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  -- the coupling `ε_T s = d · X^{3/4} ≤ c₀ d`
  have hcoup :
      Work.BoseBox.fsXp t (23 / 4) * Work.BoseBox.fsXp t 1 ≤ c₀ * Work.BoseBox.fsXp t 6 := by
    calc Work.BoseBox.fsXp t (23 / 4) * Work.BoseBox.fsXp t 1
        = Work.BoseBox.fsXp t (23 / 4 + 1) := Work.BoseBox.fsXp_mul ht (23 / 4) 1
      _ = Work.BoseBox.fsXp t (6 + 3 / 4) := by norm_num
      _ = Work.BoseBox.fsXp t 6 * Work.BoseBox.fsXp t (3 / 4) :=
          (Work.BoseBox.fsXp_mul ht 6 (3 / 4)).symm
      _ ≤ Work.BoseBox.fsXp t 6 * c₀ :=
          mul_le_mul_of_nonneg_left hX34 (le_of_lt (Work.BoseBox.fsXp_pos ht))
      _ = c₀ * Work.BoseBox.fsXp t 6 := by ring
  -- the ten conjuncts of `KinRegimeFS c₀ ℓ d s ε_T b`
  rw [KinRegimeFS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 < ℓ = K_ℓ (μ · a v)^{-1/2}`
    rw [Work.BoseFixGlue.ℓB_def, Work.BoseBox.sideAt]
    refine Work.BoseBox.boxSide_pos hμ hav ?_
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `0 < d = X⁶`
    rw [Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `d ≤ 1`
    rw [Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact hd1
  · -- `0 < s = X`
    rw [Work.BoseFixGlue.sB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `s ≤ c₀`
    rw [Work.BoseFixGlue.sB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact hX
  · -- `0 < ε_T = X^{23/4}`
    rw [Work.BoseFixGlue.eTB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `ε_T ≤ c₀`
    rw [Work.BoseFixGlue.eTB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact heT
  · -- the coupling `ε_T s ≤ c₀ d`
    rw [Work.BoseFixGlue.eTB_def, Work.BoseFixGlue.sB_def, Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact hcoup
  · -- `0 < b = 1/16`
    rw [Work.BoseFixGlue.bB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num
  · -- `b ≤ 1/16`
    rw [Work.BoseFixGlue.bB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num

end Work.BoseFixKin
