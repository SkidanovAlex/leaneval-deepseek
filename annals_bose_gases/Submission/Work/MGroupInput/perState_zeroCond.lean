import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- In the fully excited branch (`cS1 s Φ = 0`) the sector Parseval identity
`n₊ + S₁ = N·‖Φ‖²` collapses the excited count to the particle number. -/
theorem cnPlus_eq_of_cS1_eq_zero {N : ℕ} {s : ℝ} (hs : 0 < s) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N s, (Φ x) ^ 2) = 1)
    (hz : Submission.BoseGases.cS1 s Φ = 0) :
    Submission.BoseGases.cnPlus s Φ = (N : ℝ) := by
  have h1 := Submission.BoseGases.cnPlus_add_cS1 (N := N) (ℓ := s) hs hΦc.continuous
  rw [hnorm, mul_one] at h1
  linarith [h1, hz]

/-- The pure-arithmetic step of the zero-condensate branch of the `m`-arm:
on the window `6μ ≤ u ≤ 9μ` the target coefficient `(1/9)(μ−u)²` is dominated
by the `A₀`-bracket coefficient `(1/4)(u−μ)² − ½μ²`. -/
theorem one_ninth_le_quarter {u μ W : ℝ} (hμ : 0 < μ) (hu : 6 * μ ≤ u) (hW : 0 ≤ W) :
    (1 / 9) * (μ - u) ^ 2 * W ≤ ((1 / 4) * (u - μ) ^ 2 - (1 / 2) * μ ^ 2) * W := by
  have hu5 : 5 * μ ≤ u - μ := by linarith
  have hsq : (18 / 5) * μ ^ 2 ≤ (u - μ) ^ 2 := by
    nlinarith [hu5, hμ, sq_nonneg (u - μ)]
  have hkey : (1 / 9) * (μ - u) ^ 2 ≤ (1 / 4) * (u - μ) ^ 2 - (1 / 2) * μ ^ 2 := by
    nlinarith [hsq]
  exact mul_le_mul_of_nonneg_right hkey hW

theorem perState_zeroCond {P : ℕ} {s μ c₀ cgap : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_memL1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hRs : R ≤ s * Submission.BoseGases.chiR0) (hav : 0 < BoseGases.a v)
    (hs : 0 < s) (hμ : 0 < μ)
    (hcgap : 1 / (36 * s ^ 2) ≤ cgap)
    (hgap : (μ * (BoseGases.a v) * s ^ 2) * (1600 + 1850 * Submission.BoseGases.chiSup ^ 2) ≤ 1)
    (hP : 1 ≤ P) (hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ) (hCn : 6 * μ ≤ (P : ℝ) / s ^ 3)
    (Φ : Submission.BoseGases.X P → ℝ) (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox P s, (Φ x) ^ 2) = 1)
    (hz : Submission.BoseGases.cS1 s Φ = 0) :
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
      ≤ Work.KinPSuperadd.blockE s μ (Submission.BoseGases.wPairC s v)
          (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
          (Work.KinPSuperadd.diagSlotWord s c₀ cgap) P Φ := by
  have havnn : 0 ≤ BoseGases.a v := le_of_lt hav
  have hμnn : 0 ≤ μ := le_of_lt hμ
  -- the excited count equals the particle number on the `cS1 = 0` branch
  have hcP : Submission.BoseGases.cnPlus s Φ = (P : ℝ) :=
    cnPlus_eq_of_cS1_eq_zero (N := P) hs hΦc hnorm hz
  -- the pure arithmetic core of the fully excited case
  have hqar := Work.SmallBoxA0.qZeroArith (N := P) (s := s) (μ := μ)
    (a := BoseGases.a v) (q := Submission.BoseGases.chiSup ^ 2)
    hs hμ havnn (sq_nonneg Submission.BoseGases.chiSup) hwin hgap
  -- the crude one-body lower bound for the potential word
  have hqL := Submission.BoseGases.qLHSword_chosen_lower (N := P) (s := s) (R := R) (μ := μ) (v := v)
    hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμnn hΦc
  rw [hnorm, mul_one] at hqL
  have hsbox : Submission.BoseGases.sboxC P μ v
      = μ * (P : ℝ) * (16 * Real.pi * Submission.BoseGases.chiSup ^ 2 * (BoseGases.a v)) := by
    rw [Submission.BoseGases.sboxC]; ring
  rw [hsbox] at hqL
  -- the diagonal word's kinetic pieces are nonnegative
  have hpD : 0 ≤ Submission.BoseGases.pDiagForm s (Submission.BoseGases.fsKinCoeff c₀) Φ :=
    Work.KinPSuperadd.pDiagForm_nonneg hs (Submission.BoseGases.fsKinCoeff c₀)
      (Submission.BoseGases.fsKinCoeff_nonneg c₀) Φ
  -- the `ε_T`-gap constant dominates the box kinetic gap, and `cnPlus = P`
  have hkin : (P : ℝ) / (36 * s ^ 2) ≤ cgap * Submission.BoseGases.cnPlus s Φ := by
    rw [hcP, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [one_div] using hcgap) (by positivity)
  -- the final coefficient comparison `1/9 ≤ 1/4 − ½μ²/(u−μ)²`
  have hW : 0 ≤ 8 * Real.pi * (BoseGases.a v) * s ^ 3 := by positivity
  have harith := one_ninth_le_quarter (u := (P : ℝ) / s ^ 3) (μ := μ)
    (W := 8 * Real.pi * (BoseGases.a v) * s ^ 3) hμ hCn hW
  -- assembly
  rw [Work.KinPSuperadd.blockE_eq]
  rw [show Work.KinPSuperadd.diagSlotWord s c₀ cgap P Φ
      = cgap * Submission.BoseGases.cnPlus s Φ
        + Submission.BoseGases.pDiagForm s (Submission.BoseGases.fsKinCoeff c₀) Φ from rfl]
  linarith [hqar, hkin, hqL, hpD, harith]

end Work.MGroupInput
