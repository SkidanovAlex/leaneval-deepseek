import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.hatChi_decay_uniform
import Submission.Work.BoseBogFS.honestZPDefs
import Submission.Work.BoseBogFS.sum_hatChi_shifted_cube_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestZPBricks` — the two χ-bricks of the honest `FsBogData`

* `honestN_smul_modePos` — the coordinate identity `(n+1)·modePos n k i = π(2·k i − gridD n)`;
* `half_vec_eq`, `honestN_smul_modePos_vec` — the `WithLp`-bridge to the shifted cube;
* `honestChiNorm` — the `hχnorm` row of the honest `FsBogData`:
  `chiSqSum (honestN v μ ρ) (honestXh v μ ρ N K) ≤ ℓ³·1·(1 + 0)`, from the shifted-cube
  Parseval row `Work.BoseBogFS.sum_hatChi_shifted_cube_le` (the truncation deletes only
  non-negative terms and `(n+1) • modePos n k = (1/2) • vec (2k − gridD n)`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The mesh identity** (coordinatewise): `(n+1)·modePos n k i = π(2·k i − gridD n)`. -/
theorem honestN_smul_modePos {n : ℕ} (k : Work.BoseB6Est.modeIdx n) (i : Fin 3) :
    (((n : ℝ) + 1) * Work.BoseB6Est.modePos n k i)
      = Real.pi * (2 * ((k i : ℤ) : ℝ) - ((Work.BoseB6.gridD n : ℤ) : ℝ)) := by
  simp only [Work.BoseB6Est.modePos, Work.BoseBox.latticeCenter, Work.BoseB6.meshD,
    Work.BoseB6.gridD]
  push_cast <;> field_simp <;> ring

/-- `WithLp.toLp 2 (a • f) = a • WithLp.toLp 2 f`. -/
theorem toLp_smul {a : ℝ} {f : Fin 3 → ℝ} :
    WithLp.toLp 2 (a • f) = a • (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 3)) := rfl

/-- `(1/2) • vec m = WithLp.toLp 2 (π · m)`: half of the lattice vector. -/
theorem half_vec_eq (m : Fin 3 → ℤ) :
    (1 / 2 : ℝ) • Work.BoseB4.vec m
      = WithLp.toLp 2 (fun i : Fin 3 => Real.pi * ((m i : ℤ) : ℝ)) := by
  have h : Work.BoseB4.vec m
      = WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * ((m i : ℤ) : ℝ)) := rfl
  rw [h, ← toLp_smul]
  congr 1
  funext i
  show (1 / 2 : ℝ) * (2 * Real.pi * ((m i : ℤ) : ℝ)) = Real.pi * ((m i : ℤ) : ℝ)
  ring_nf

/-- **The bridge between the honest localisation's argument and the shifted cube**: on the mesh,
`(n+1) • modePos n k` is `(1/2) • vec (2k − gridD n)`. -/
theorem honestN_smul_modePos_vec (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (k : Work.BoseB6Est.modeIdx (honestN v μ ρ)) :
    WithLp.toLp 2 ((((honestN v μ ρ : ℕ) : ℝ) + 1)
        • Work.BoseB6Est.modePos (honestN v μ ρ) k)
      = (1 / 2 : ℝ) • Work.BoseB4.vec
          (fun i : Fin 3 =>
            2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)) := by
  have h1 : ((((honestN v μ ρ : ℕ) : ℝ) + 1)
        • Work.BoseB6Est.modePos (honestN v μ ρ) k)
      = fun i : Fin 3 => Real.pi
          * (2 * ((k i : ℤ) : ℝ) - ((Work.BoseB6.gridD (honestN v μ ρ) : ℤ) : ℝ)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact honestN_smul_modePos k i
  rw [h1, half_vec_eq]
  congr 1
  funext i
  push_cast <;> ring

/-- **The `hχnorm` row of the honest `FsBogData`.** -/
theorem honestChiNorm (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (K : Work.BoseB6Est.FsKernel) (hK : K.T = honestZPT v μ ρ N)
    (hcube : (∑ k : Fin 3 → Fin (Work.BoseB6.gridD (honestN v μ ρ)),
        (Work.BoseK15.corpusBox.hatChi
          ((1 / 2 : ℝ) • Work.BoseB4.vec
            (fun i : Fin 3 =>
              2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)))) ^ 2)
      ≤ 1) :
    Work.BoseB6Est.chiSqSum (honestN v μ ρ) (honestXh v μ ρ N K)
      ≤ (Work.BoseFixR.ell v μ) ^ 3 * 1 * (1 + 0) := by
  have hℓ3 : 0 ≤ (Work.BoseFixR.ell v μ) ^ 3 := by
    have h : 0 ≤ Work.BoseBox.sideAt μ (a v) := Work.BoseBogFS.sideAt_nonneg μ (a v)
    rw [ell_eq]
    positivity
  have hroot : Real.sqrt ((Work.BoseFixR.ell v μ) ^ 3) ^ 2 = (Work.BoseFixR.ell v μ) ^ 3 :=
    Real.sq_sqrt hℓ3
  have hterm : ∀ k : Work.BoseB6Est.modeIdx (honestN v μ ρ),
      (honestXh v μ ρ N K (Work.BoseB6Est.modePos (honestN v μ ρ) k)) ^ 2
        ≤ (Work.BoseFixR.ell v μ) ^ 3
          * (Work.BoseK15.corpusBox.hatChi
              ((1 / 2 : ℝ) • Work.BoseB4.vec
                (fun i : Fin 3 =>
                  2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)))) ^ 2 := by
    intro k
    rw [honestXh]
    by_cases hkt : Work.BoseB6Est.nrm (Work.BoseB6Est.modePos (honestN v μ ρ) k) ≤ K.T
    · rw [if_pos hkt]
      rw [honestN_smul_modePos_vec v μ ρ k, mul_pow, hroot]
    · rw [if_neg hkt, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hℓ3 (sq_nonneg _)
  rw [Work.BoseB6Est.chiSqSum]
  calc (∑ k : Work.BoseB6Est.modeIdx (honestN v μ ρ),
        (honestXh v μ ρ N K (Work.BoseB6Est.modePos (honestN v μ ρ) k)) ^ 2)
      ≤ ∑ k : Work.BoseB6Est.modeIdx (honestN v μ ρ),
          (Work.BoseFixR.ell v μ) ^ 3
            * (Work.BoseK15.corpusBox.hatChi
                ((1 / 2 : ℝ) • Work.BoseB4.vec
                  (fun i : Fin 3 =>
                    2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)))) ^ 2 :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (Work.BoseFixR.ell v μ) ^ 3
          * ∑ k : Work.BoseB6Est.modeIdx (honestN v μ ρ),
              (Work.BoseK15.corpusBox.hatChi
                ((1 / 2 : ℝ) • Work.BoseB4.vec
                  (fun i : Fin 3 =>
                    2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)))) ^ 2 :=
        (Finset.mul_sum Finset.univ _ _).symm
    _ ≤ (Work.BoseFixR.ell v μ) ^ 3 * 1 := mul_le_mul_of_nonneg_left hcube hℓ3
    _ = (Work.BoseFixR.ell v μ) ^ 3 * 1 * (1 + 0) := by ring

end Work.BoseBogFS
