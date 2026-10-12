import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogCellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogMeshInvSqLe` — the scaled mesh is bounded below by `2πX^{3/2}`

With `D = dil v μ = μ(a v)³ = X^{323}`, `X = fsX v μ = D^{1/323}`, the box side is
`ℓ = K_ℓ(μa)^{-1/2}` with `K_ℓ = (paramsAt μ (a v)).Kl = D^{-3/646}`, so that

  `(2π/ℓ) = 2π√(μa)·X^{3/2}`   and   `bogMesh v ρ μ = (2π/ℓ)/√(ρa) = 2πX^{3/2}√(μ/ρ)`.

Hence `(bogMesh v ρ μ)^{-2} = X^{-3}·ρ/(4π²μ) ≤ (11/(40π²))·X^{-3}`, the last step being
`Core.hρhi : ρ ≤ (11/10)μ`.  Equivalently `(bogMesh)² = 4π²μ/(K_ℓ²ρ)` and
`K_ℓ² = X^{-3}`.

This is the "`δ^{-2} = (2π)^{-2}X^{-3}`" row of
`Submission/Work/BoseBogFS/FINDING_cleanFun_tsum_session20.md` §1, with the `ρ/μ` factor
carried exactly.
-/

namespace Work.BoseBogFS

theorem bogMeshInvSqLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Work.BoseBogFS.Core v R μ ρ) :
    1 / (Work.BoseBogFS.bogMesh v ρ μ) ^ 2
      ≤ (11 / (40 * Real.pi ^ 2)) * (Work.BoseFixR.fsX v μ) ^ (-(3 : ℝ)) := by
  have ha : 0 < _root_.BoseGases.a v := hav
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hD0 : 0 < Work.BoseFixR.dil v μ := hC.hD0
  have hKl : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl :=
    Work.BoseBox.fsXp_pos hD0
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ ha
  have hρa : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ ha
  -- `K_ℓ² = X^{-3}`
  have hfar : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
      = (Work.BoseFixR.fsX v μ) ^ (-(3 : ℝ)) := by
    have h1 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
        = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(3 : ℝ)) := by
      show (Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(3 / 2)))^2 = _
      rw [Work.BoseBox.fsXp_pow hD0.le]
      norm_num
    have h2 : (Work.BoseFixR.fsX v μ) ^ (-(3 : ℝ))
        = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(3 : ℝ)) := by
      show (Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1) ^ (-(3 : ℝ)) = _
      rw [Work.BoseBox.fsXp_rpow hD0.le]
      norm_num
    rw [h1, h2]
  -- the square of the box side
  have hell2 : (Work.BoseFixR.ell v μ)^2
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
        * (μ * _root_.BoseGases.a v)⁻¹ := by
    rw [hC.hℓ, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) 2,
        ← Real.rpow_mul hμa.le]
    rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hsq : (Real.sqrt (ρ * _root_.BoseGases.a v))^2 = ρ * _root_.BoseGases.a v :=
    Real.sq_sqrt hρa.le
  -- the square of the scaled mesh
  have hδ2 : (Work.BoseBogFS.bogMesh v ρ μ)^2
      = 4 * Real.pi^2 * μ / (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2 * ρ) := by
    rw [Work.BoseBogFS.bogMesh, div_pow, div_pow, hell2, hsq]
    field_simp
    norm_num
  have hδinv : 1 / (Work.BoseBogFS.bogMesh v ρ μ)^2
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
        * (ρ / (4 * Real.pi^2 * μ)) := by
    rw [hδ2]
    field_simp
  -- the close-region ratio `ρ/μ ≤ 11/10`
  have hratio : ρ / (4 * Real.pi^2 * μ) ≤ 11 / (40 * Real.pi^2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hC.hρhi, Real.pi_pos]
  calc 1 / (Work.BoseBogFS.bogMesh v ρ μ)^2
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
        * (ρ / (4 * Real.pi^2 * μ)) := hδinv
    _ ≤ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2
        * (11 / (40 * Real.pi^2)) :=
        mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ = (11 / (40 * Real.pi^2))
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl)^2 := by ring
    _ = (11 / (40 * Real.pi^2)) * (Work.BoseFixR.fsX v μ) ^ (-(3 : ℝ)) := by rw [hfar]

end Work.BoseBogFS
