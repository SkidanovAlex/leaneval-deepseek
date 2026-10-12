import ChallengeDeps
import Submission.Work.BoseFixGlue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixGlue.Params

/-!
# `Work.BoseFixGlue.Params.kinRegime_of_params` — the FS parameter regime at the
diluteness-correct parameters

FS `sec:params` (`eq:Xparameter`, `eq:Xchoice`) picks, at diluteness `t = μa³`,
the dimensionless parameters

`s = X = t^{1/323}`,  `d = X⁶ = t^{6/323}`,  `ε_T = X^{23/4} = t^{(23/4)/323}`,
`b = bValue = 1/16`,

all of which are `fsXp t c = t^{c/323}` with `c ≥ 0`.  FS `lem:LocKinEn` (and hence
the whole kinetic localisation) only needs them to lie in the *regime*
`Work.BoseKinLoc.KinRegime c₀`: positive, `d ≤ 1`, and all four bounded by a universal
constant `c₀`.

Since `t ↦ t^{c/323}` is antitone on `(0,1]` and `t^{1/323}` is the largest of the
three (`d` and `ε_T` are higher powers of `X`), the whole regime is *automatic* once
the diluteness is small enough that `X = (μa³)^{1/323} ≤ c₀`, i.e. once
`μa³ ≤ c₀^{323}`.  The only `v`-dependence enters through the scattering length
`a v > 0` (the diluteness is `μ (a v)³`), and `b = bValue ≤ c₀` is an explicit
hypothesis (it is FS's `con:b`).

This is the threshold lemma that lets every consumer of the box theorem work with
FS's parameters without carrying the parameter regime as a hypothesis.
-/

/-- **The threshold arithmetic of FS `sec:params`.**  For diluteness `0 < t ≤ 1` and
`1 ≤ c`, the parameter `fsXp t c = t^{c/323}` is at most `c₀` as soon as
`t ≤ c₀^{323}` (equivalently `t^{1/323} ≤ c₀`, since `c ↦ t^{c/323}` is antitone for
`t ≤ 1` and `1 ≤ c`). -/
theorem fsXp_le_of_small_diluteness {t c₀ c : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc₀ : 0 < c₀) (hc : 1 ≤ c) (htc : t ≤ c₀ ^ 323) :
    Work.BoseBox.fsXp t c ≤ c₀ := by
  -- `fsXp t 1 = t^{1/323} ≤ (c₀³²³)^{1/323} = c₀`
  have h1 : Work.BoseBox.fsXp t 1 ≤ c₀ := by
    have h1a : Work.BoseBox.fsXp t 1 ≤ Work.BoseBox.fsXp (c₀ ^ 323) 1 := by
      simp only [Work.BoseBox.fsXp]
      exact Real.rpow_le_rpow ht.le htc (by norm_num)
    have h2 : Work.BoseBox.fsXp (c₀ ^ 323) 1 = c₀ := by
      simp only [Work.BoseBox.fsXp]
      rw [← Real.rpow_natCast c₀ 323, ← Real.rpow_mul hc₀.le]
      norm_num
    linarith
  -- and `fsXp t c ≤ fsXp t 1` because `1 ≤ c` and `t ≤ 1`
  exact le_trans (Work.BoseBox.fsXp_le_fsXp ht ht1 hc) h1

/-- **FS `eq:BSlidingassp` holds automatically for small diluteness.**  There is `ε > 0`
such that whenever `μ (a v)³ ≤ ε`, FS's parameter block at diluteness `μ (a v)³` lies in
the kinetic regime `Work.BoseKinLoc.KinRegime c₀`: all of `ℓ(μ), d, s, ε_T, b` are
positive, `d ≤ 1`, and `d, s, ε_T, b ≤ c₀`.

The threshold is `ε = min 1 (c₀^{323})`: `min 1 _` gives `t ≤ 1` (needed for the
monotonicity of `c ↦ t^{c/323}`), and `c₀^{323}` is the diluteness at which the FS
parameter `X = (μa³)^{1/323}` reaches `c₀`. -/
theorem kinRegime_of_params {v : EuclideanSpace ℝ (Fin 3) → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hb : Work.BoseBox.bValue ≤ c₀) (hav : 0 < BoseGases.a v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * (BoseGases.a v) ^ 3 ≤ ε →
      Work.BoseKinLoc.KinRegime c₀ (Work.BoseFixGlue.ℓB v μ) (Work.BoseFixGlue.dB v μ)
        (Work.BoseFixGlue.sB v μ) (Work.BoseFixGlue.eTB v μ) (Work.BoseFixGlue.bB v μ) := by
  refine ⟨min 1 (c₀ ^ 323), lt_min one_pos (by positivity), ?_⟩
  intro μ hμ hle
  have hav3 : 0 < (BoseGases.a v) ^ 3 := by positivity
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := mul_pos hμ hav3
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hle (min_le_left _ _)
  have htc : μ * (BoseGases.a v) ^ 3 ≤ c₀ ^ 323 := le_trans hle (min_le_right _ _)
  rw [Work.BoseKinLoc.KinRegime]
  -- the ten conjuncts of `KinRegime`, in order
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 < ℓ = K_ℓ(μa)^{-1/2}`
    rw [Work.BoseFixGlue.ℓB_def, Work.BoseBox.sideAt]
    refine Work.BoseBox.boxSide_pos hμ hav ?_
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `0 < d = X⁶`
    rw [Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `d ≤ c₀`
    rw [Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact fsXp_le_of_small_diluteness ht ht1 hc₀ (by norm_num) htc
  · -- `d ≤ 1`
    rw [Work.BoseFixGlue.dB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
  · -- `0 < s = X`
    rw [Work.BoseFixGlue.sB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `s ≤ c₀`
    rw [Work.BoseFixGlue.sB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact fsXp_le_of_small_diluteness ht ht1 hc₀ (by norm_num) htc
  · -- `0 < ε_T = X^{23/4}`
    rw [Work.BoseFixGlue.eTB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  · -- `ε_T ≤ c₀`
    rw [Work.BoseFixGlue.eTB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact fsXp_le_of_small_diluteness ht ht1 hc₀ (by norm_num) htc
  · -- `0 < b = 1/16`
    rw [Work.BoseFixGlue.bB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num
  · -- `b ≤ c₀` (FS's `con:b`, carried as a hypothesis)
    rw [Work.BoseFixGlue.bB_def]
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact hb

end Work.BoseFixGlue.Params
