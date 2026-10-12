import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The `hEpsEta` row of `FsI1Regime` at the honest kernel.**

The kernel's `η = max 0 (16πR√(ρa))` is dominated by FS's error
`ε = lhyEps (a v) R ε_T K_ℓ s d μ` (the parameters of `paramsAt μ (a v)`).

Route: `Work.BoseBogFS.core_bounds` gives `Core v R μ ρ`; `Core.hη0` collapses the
`max 0`, `Core.hEeq` rewrites `lhyEps` as `lhyEpsX`, and `Core.hEμa` gives
`(μa)^{1/4}√R ≤ lhyEpsX`.  So it suffices that
`16πR√(ρa) ≤ (μa)^{1/4}√R`, which with `Core.hsqρa`/`Core.hsqμa`
(`√(ρa) ≤ √(11/10)√D/a`) is `16π√(11/10)√R·(μa)^{1/4} ≤ 1`, i.e.
`(μa)^{1/4} ≤ 1/(16π√(11/10)√R)`, i.e., fourth-powering,
`D ≤ a²/((16π)⁴(11/10)²R²)` with `D = dil v μ`.
Take `ε₀ = min (that) (coreBound v R) > 0`. -/
theorem honestFsEpsEta {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (Work.BoseBogFS.bogKernel v R ρ μ).η
        ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  -- the constant `A = 16π√(11/10)` of the estimate `η ≤ A·x² ≤ x`, `x = (μa)^{1/4}√R`,
  -- and the diluteness threshold `T₀ = a²/(A⁴R²)` which makes `A·x ≤ 1`
  set A : ℝ := 16 * Real.pi * Real.sqrt (11 / 10) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set T₀ : ℝ := (_root_.BoseGases.a v) ^ 2 / (A ^ 4 * R ^ 2) with hT0
  have hT0pos : 0 < T₀ := by
    rw [hT0]
    exact div_pos (pow_pos hav 2) (mul_pos (pow_pos hApos 4) (pow_pos hR 2))
  refine ⟨min (Work.BoseBogFS.coreBound v R) T₀,
    lt_min (Work.BoseBogFS.coreBound_pos hR hav) hT0pos, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDle : Work.BoseFixR.dil v μ ≤ min (Work.BoseBogFS.coreBound v R) T₀ := hAdm.2.1
  -- the shared parameter bounds of `honestFsCore`
  have hCore : Work.BoseBogFS.Core v R μ ρ :=
    Work.BoseBogFS.core_bounds (δ := min (Work.BoseBogFS.coreBound v R) T₀) hR hav
      (min_le_left _ _) μ ρ hμ hDle hclose
  have hDT : Work.BoseFixR.dil v μ ≤ T₀ := le_trans hDle (min_le_right _ _)
  -- `D ≤ a²/B²` with `B = A²R`
  set B : ℝ := A ^ 2 * R with hB
  have hBpos : 0 < B := by rw [hB]; exact mul_pos (pow_pos hApos 2) hR
  have hDB : Work.BoseFixR.dil v μ ≤ (_root_.BoseGases.a v) ^ 2 / B ^ 2 := by
    rw [hT0] at hDT
    have hBB : A ^ 4 * R ^ 2 = B ^ 2 := by rw [hB]; ring
    rwa [hBB] at hDT
  have hsqrtD : Real.sqrt (Work.BoseFixR.dil v μ) ≤ _root_.BoseGases.a v / B := by
    have h2 : Real.sqrt (Work.BoseFixR.dil v μ) ≤ Real.sqrt ((_root_.BoseGases.a v) ^ 2 / B ^ 2) :=
      Real.sqrt_le_sqrt hDB
    rw [Real.sqrt_div (sq_nonneg (_root_.BoseGases.a v)) (B ^ 2),
      Real.sqrt_sq (x := _root_.BoseGases.a v) hav.le, Real.sqrt_sq (x := B) hBpos.le] at h2
    exact h2
  -- `√(μa) = √D/a ≤ 1/B`
  have hsqrtmu : Real.sqrt (μ * _root_.BoseGases.a v) ≤ 1 / B := by
    rw [hCore.hsqμa]
    rw [div_le_iff₀ hav]
    have hDm : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) ≤ _root_.BoseGases.a v / B := by
      rw [← Real.sqrt_eq_rpow]; exact hsqrtD
    calc (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) ≤ _root_.BoseGases.a v / B := hDm
      _ = 1 / B * _root_.BoseGases.a v := by ring
  -- the algebra `((μa)^{1/4})² = √(μa)` and `(√R)² = R`
  have huu : (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)
      = Real.sqrt (μ * _root_.BoseGases.a v) := by
    rw [← Real.rpow_add (by positivity)]
    rw [show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  have hy0 : 0 ≤ A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) :=
    mul_nonneg (mul_nonneg hApos.le (Real.sqrt_nonneg R))
      (Real.rpow_nonneg (by positivity) _)
  have hx0 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg R)
  have hsR : Real.sqrt R * Real.sqrt R = R := by rw [← sq, Real.sq_sqrt hR.le]
  -- `(A√R(μa)^{1/4})² = A²R√(μa) ≤ 1`
  have hy2 : (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) ^ 2
      = A ^ 2 * R * Real.sqrt (μ * _root_.BoseGases.a v) := by
    have hu2 : ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) ^ 2
        = Real.sqrt (μ * _root_.BoseGases.a v) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [show (1 : ℝ) / 4 * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    calc (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) ^ 2
        = A ^ 2 * (Real.sqrt R) ^ 2 * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
      _ = A ^ 2 * R * Real.sqrt (μ * _root_.BoseGases.a v) := by rw [Real.sq_sqrt hR.le, hu2]
  have hy2le : (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4)) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [one_pow, hy2]
    calc A ^ 2 * R * Real.sqrt (μ * _root_.BoseGases.a v) ≤ A ^ 2 * R * (1 / B) :=
          mul_le_mul_of_nonneg_left hsqrtmu (mul_nonneg (pow_nonneg hApos.le 2) hR.le)
      _ = 1 := by rw [hB, mul_one_div]; exact div_self (ne_of_gt (by positivity))
  have hy1 : A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) ≤ 1 :=
    (pow_le_pow_iff_left₀ hy0 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).mp hy2le
  have hyx : (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4))
      * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R)
        = A * R * Real.sqrt (μ * _root_.BoseGases.a v) := by
    calc (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4))
          * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R)
        = A * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4))
            * (Real.sqrt R * Real.sqrt R) := by ring
      _ = A * Real.sqrt (μ * _root_.BoseGases.a v) * R := by rw [huu, hsR]
      _ = A * R * Real.sqrt (μ * _root_.BoseGases.a v) := by ring
  -- `16πR√(ρa) ≤ A·R·√(μa) = y·x ≤ x ≤ lhyEpsX`
  have hmain : 16 * Real.pi * R * Real.sqrt (ρ * _root_.BoseGases.a v)
      ≤ Work.BoseBogFS.lhyEpsX v R μ := by
    have hstep1 : 16 * Real.pi * R * Real.sqrt (ρ * _root_.BoseGases.a v)
        ≤ A * R * Real.sqrt (μ * _root_.BoseGases.a v) := by
      calc 16 * Real.pi * R * Real.sqrt (ρ * _root_.BoseGases.a v)
          ≤ 16 * Real.pi * R * (Real.sqrt (11 / 10)
              * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v) :=
            mul_le_mul_of_nonneg_left hCore.hsqρa (by positivity)
        _ = A * R * Real.sqrt (μ * _root_.BoseGases.a v) := by
            rw [hA, mul_div_assoc, ← hCore.hsqμa]; ring
    calc 16 * Real.pi * R * Real.sqrt (ρ * _root_.BoseGases.a v)
        ≤ A * R * Real.sqrt (μ * _root_.BoseGases.a v) := hstep1
      _ = (A * Real.sqrt R * (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4))
            * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R) := hyx.symm
      _ ≤ 1 * ((μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R) :=
            mul_le_mul_of_nonneg_right hy1 hx0
      _ = (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R := one_mul _
      _ ≤ Work.BoseBogFS.lhyEpsX v R μ := hCore.hEμa
  -- collapse the two `max`es and FS's error
  have heta : (Work.BoseBogFS.bogKernel v R ρ μ).η
      = 16 * Real.pi * R * Real.sqrt (ρ * _root_.BoseGases.a v) := by
    rw [Work.BoseBogFS.bogKernel_eta, max_eq_right hCore.hη0]
    rfl
  rw [heta, hCore.hEeq]
  exact hmain

end Work.BoseBogFS
