import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsEtaT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.honestFsI2` — the `hI2` row at the honest kernel

FS's `hI2` (`eq:I2-integral` + `lm:BogIntegral`) is the mass row
`ĝω(0) ≤ 1` of `FsI1Regime`.  At the honest kernel `bogKernel v R ρ μ` it is
*not* a consequence of the parameter regime alone (`ηT ≤ 1`, `B ≤ 100`, the
`√(ρa)` row) but of those rows together with the diluteness threshold

  `D ≤ (4π²/(a·√(11/10)·100²·2·10⁶·(323/156)))^{1292/645}`,

which is a fixed constant for fixed `(v, R)` — exactly the shape of the other
honest rows (`honestFsEtaT`, `honestFsCore`), so it can be absorbed in `ε₀`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

/-- The diluteness threshold constant of `honestFsI2`: `fsGω0 ≤ 1` follows from
`D^{645/1292} ≤ 1/fsI2BoundConst (a v)`.  It is the value at which the residual
bound `a·√(11/10)·100²·2·10⁶(323/156)·D^{645/1292}/(4π²)` equals `1`. -/
def fsI2BoundConst (a : ℝ) : ℝ :=
  a * Real.sqrt (11 / 10) * 100 ^ 2 * 2 * 10 ^ 6 * (323 / 156) / (4 * Real.pi ^ 2)

/-- **The `hI2` row of `FsI1Regime` at the honest kernel.**

FS's `hI2`: the mass coefficient `ĝω(0) = fsGω0 ρ (a v) K ≤ 1` for `K = bogKernel v R ρ μ`.

Route: `Work.BoseB6Est.fsI2_le_bound K : fsI2 K ≤ 2π·B²·T` and the definition
`fsGω0 ρz a K = a²·√(ρz·a)·fsI2 K/(2π)³`.  Hence
`fsGω0 ≤ a²√(ρa)·B²·T/(4π²)`.  `Core` gives `T ≤ 2·10⁶(323/156)·D^{-1/1292}`
(`D = dil v μ`) and `√(ρa) ≤ √(11/10)√D/a`.  For `B = 8π + ηT` one needs `ηT ≤ 1`
(same threshold family as `Work.BoseBogFS.honestFsEtaT`, which is already PROVED in
`Submission/Work/BoseBogFS/honestFsEtaT.lean`: `D^{645/1292} ≤ a/(C·R)`, or simply the
weaker `ηT ≤ 100 - 8π`), giving `B² ≤ 100²`.  The residual bound
`fsGω0 ≤ √(11/10)·100²·2·10⁶(323/156)/(4π²)·a·D^{645/1292}` is `≤ 1` for
`D ≤ (a·K)^{-1292/645}`, absorbable in `ε₀ = min (threshold) (coreBound v R)`. -/
theorem honestFsI2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      Work.BoseB6Est.fsGω0 ρ (_root_.BoseGases.a v) (Work.BoseBogFS.bogKernel v R ρ μ)
        ≤ 1 := by
  -- the `B ≤ 100` row, from the already proved sibling
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Work.BoseBogFS.honestFsEtaT (v := v) (R := R) hR hav
  have hYpos : 0 < fsI2BoundConst (_root_.BoseGases.a v) := by
    rw [fsI2BoundConst]; positivity
  have hthr0 : 0 < (1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645) :=
    Real.rpow_pos_of_pos (one_div_pos.mpr hYpos) _
  refine ⟨min ε₁ (min (Work.BoseBogFS.coreBound v R)
      ((1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645))), ?_, ?_⟩
  · exact lt_min hε₁pos (lt_min (Work.BoseBogFS.coreBound_pos hR hav) hthr0)
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hB100 : (bogKernel v R ρ μ).B ≤ 100 := (hε₁ μ hAdm₁ ρ hclose).2
  have hD0 : 0 < Work.BoseFixR.dil v μ := Work.BoseBogFS.dil_pos v hμ hav
  have hDδ : Work.BoseFixR.dil v μ ≤ min (Work.BoseBogFS.coreBound v R)
      ((1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645)) := by
    rw [Work.BoseFixR.dil]
    exact le_trans hAdm.2.1 (min_le_right _ _)
  have hDthr : Work.BoseFixR.dil v μ
      ≤ (1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645) :=
    le_trans hDδ (min_le_right _ _)
  have hCore : Work.BoseBogFS.Core v R μ ρ :=
    Work.BoseBogFS.core_bounds (v := v) (R := R) hR hav (δ := min (Work.BoseBogFS.coreBound v R)
      ((1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645)))
      (min_le_left _ _) μ ρ hμ hDδ hclose
  -- the residual bound `fsGω0 ≤ fsI2BoundConst (a v)·D^{645/1292}`
  have hmain : Work.BoseB6Est.fsGω0 ρ (_root_.BoseGases.a v) (bogKernel v R ρ μ)
      ≤ fsI2BoundConst (_root_.BoseGases.a v) * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
    have hI2 : Work.BoseB6Est.fsI2 (bogKernel v R ρ μ)
        ≤ 2 * Real.pi * (bogKernel v R ρ μ).B ^ 2 * (bogKernel v R ρ μ).T :=
      Work.BoseB6Est.fsI2_le_bound _
    have hTup : (bogKernel v R ρ μ).T
        ≤ 2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := by
      rw [bogKernel_T, max_eq_right hCore.hTpos.le]
      exact hCore.hTup
    have hA : Work.BoseB6Est.fsGω0 ρ (_root_.BoseGases.a v) (bogKernel v R ρ μ)
        ≤ ((_root_.BoseGases.a v) ^ 2 * Real.sqrt (ρ * _root_.BoseGases.a v)
            * (2 * Real.pi * (bogKernel v R ρ μ).B ^ 2 * (bogKernel v R ρ μ).T))
          / (2 * Real.pi) ^ 3 := by
      rw [Work.BoseB6Est.fsGω0]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hI2 (by positivity : (0:ℝ) ≤ _)
    have hB : ((_root_.BoseGases.a v) ^ 2 * Real.sqrt (ρ * _root_.BoseGases.a v)
            * (2 * Real.pi * (bogKernel v R ρ μ).B ^ 2 * (bogKernel v R ρ μ).T))
          / (2 * Real.pi) ^ 3
        = ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2)) * Real.sqrt (ρ * _root_.BoseGases.a v)
            * (bogKernel v R ρ μ).B ^ 2 * (bogKernel v R ρ μ).T := by
      field_simp
      ring
    have hC : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * Real.sqrt (ρ * _root_.BoseGases.a v)
            * (bogKernel v R ρ μ).B ^ 2 * (bogKernel v R ρ μ).T
        ≤ ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 * (2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))) := by
      have hnnA : (0:ℝ) ≤ (_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2) := by positivity
      have hs1nn : (0:ℝ) ≤ Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
          / _root_.BoseGases.a v := by positivity
      have hB2 : (bogKernel v R ρ μ).B ^ 2 ≤ 100 ^ 2 :=
        pow_le_pow_left₀ (Work.BoseB6Est.FsKernel.Bnn _) hB100 2
      have h2b : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * Real.sqrt (ρ * _root_.BoseGases.a v) * (bogKernel v R ρ μ).B ^ 2
          ≤ ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * (bogKernel v R ρ μ).B ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCore.hsqρa hnnA)
          (pow_nonneg (Work.BoseB6Est.FsKernel.Bnn _) 2)
      have h2c : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * (bogKernel v R ρ μ).B ^ 2
          ≤ ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 :=
        mul_le_mul_of_nonneg_left hB2 (mul_nonneg hnnA hs1nn)
      have h3a := mul_le_mul_of_nonneg_right (le_trans h2b h2c)
        (Work.BoseB6Est.FsKernel.Tnn (bogKernel v R ρ μ))
      have h3b : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 * (bogKernel v R ρ μ).T
          ≤ ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 * (2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))) :=
        mul_le_mul_of_nonneg_left hTup (by positivity)
      exact le_trans h3a h3b
    have hDeq : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
          * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))
        = (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
      rw [← Real.rpow_add hD0, show (1 : ℝ) / 2 + (-(1 / 1292 : ℝ)) = 645 / 1292 by norm_num]
    have hD' : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 * (2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)))
        = fsI2BoundConst (_root_.BoseGases.a v)
          * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
            * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))) := by
      rw [fsI2BoundConst]; field_simp
    have hD : ((_root_.BoseGases.a v) ^ 2 / (4 * Real.pi ^ 2))
            * (Real.sqrt (11 / 10) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)
            * 100 ^ 2 * (2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)))
        = fsI2BoundConst (_root_.BoseGases.a v) * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
      rw [hD', hDeq]
    exact le_trans hA (le_trans (le_of_eq hB) (le_trans hC (le_of_eq hD)))
  -- the diluteness threshold turns the residual bound into `≤ 1`
  have hpow : (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292)
      ≤ 1 / fsI2BoundConst (_root_.BoseGases.a v) := by
    have h2 : ((1 / fsI2BoundConst (_root_.BoseGases.a v)) ^ ((1292 : ℝ) / 645))
          ^ ((645 : ℝ) / 1292) = 1 / fsI2BoundConst (_root_.BoseGases.a v) := by
      rw [← Real.rpow_mul (le_of_lt (one_div_pos.mpr hYpos)),
        show (1292 : ℝ) / 645 * (645 / 1292) = 1 by norm_num, Real.rpow_one]
    exact le_trans (Real.rpow_le_rpow hD0.le hDthr (by norm_num)) (le_of_eq h2)
  calc Work.BoseB6Est.fsGω0 ρ (_root_.BoseGases.a v) (bogKernel v R ρ μ)
      ≤ fsI2BoundConst (_root_.BoseGases.a v) * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) :=
        hmain
    _ ≤ fsI2BoundConst (_root_.BoseGases.a v) * (1 / fsI2BoundConst (_root_.BoseGases.a v)) :=
        mul_le_mul_of_nonneg_left hpow hYpos.le
    _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hYpos)]

end Work.BoseBogFS
