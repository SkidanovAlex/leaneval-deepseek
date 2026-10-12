import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.mom2Summable
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sharpShiftRow` — the "sharp shift row" (lattice vs continuum kinetic)

## The target

For `ℓ > 0`, `c > 0`, `cℓ ≥ 4π`, `λ ∈ [5c/4, 7c/4]` and `g` smooth with
`tsupport g ⊆ closedBall 0 (ℓ/2)`:

    Σ_n ℓ⁻³·[‖k_n‖−λ]₊²·‖ĉ(k_n)‖²  ≤  (2π)⁻³ ∫_p [‖p‖−c]₊²·‖ĉ(p)‖² ,      k_n = (2π/ℓ)n .

This is a **critical Nyquist** comparison of the box lattice with the continuum: the support
condition makes the `ℓℤ³`-translates of `ball(ℓ/2)` meet only in measure-zero sets, so the
*lattice* and *continuum* measures `Σ_nℓ⁻³|ĉ(k_n)|²δ_{k_n}` and `(2π)⁻³|ĉ(p)|²dp` have equal
mass and equal second moment — `Work.BoseBoxFock.frame_lattice_ball` (PROVED) and
`Work.BoseBoxFock.moment2Lattice` (PROVED) — but *not* equal first moments; that difference is
the whole content.

## Status of this file (session 1 of the node; read `FINDING_sharpShiftRow.md`)

* **The statement is TRUE** — verified numerically, including the exact maximiser of the
  quadratic form over a rich `C^∞` radial Galerkin space (margin `−0.0274`, i.e. `1.4 × 10⁻³`
  of the term scale) and over five other families (angular momenta `l = 0,1,2`); no
  counterexample exists in anything tested; the numerical error is ≈ `15×` smaller than the
  margin.
* The statement is however **sharp** (as `cℓ → ∞` with the rest fixed, the margin tends to `0`,
  so it becomes an identity in that limit) and I did **not** prove it: it is a new sharp
  sampling inequality.  `FINDING_sharpShiftRow.md` contains the exact reduction to the two
  equivalent intermediate forms

      (♣♣)  Σ_{r_n<λ}ℓ⁻³(r_n−c)²ν_n + Σ_{r_n≥λ}ℓ⁻³(λ−c)(2r_n−λ−c)ν_n ≥ 2c(R1−S1) + Π
      (S′)  (2π)⁻³∫_{r≥c}(r−c)²ν ≥ Σ_{r_n≥λ}ℓ⁻³(r_n−λ)²ν_n ,

  (`ν_n := ℓ⁻³‖ĉ(k_n)‖²`, `ν := ‖ĉ‖²`, `Π := (2π)⁻³∫_{r<c}(c−r)²ν`; the equivalences use the
  two proved moment identities), the measured relative slack `8 %–76 %` of `(S′)` on all tested
  states (so estimates with a few percent of error would suffice — contrary to the naive split,
  whose slack is `0.04 %`), the exact first-moment identity
  `R1 − S1 = π⁻²Σ_{m≠0}∫∫g(x)ḡ(y)‖x−y+ℓm‖⁻⁴` (`aliasImageIdentity`, PROVED) that must be used
  for the aliasing excess, and two traps: the "matching-weight hole dominations" are FALSE
  (by 1 %–3 %).
* The helper lemmas below are proved: the left-hand side is antitone in the threshold, so
  **the hypothesis `λ ≤ 7c/4` is redundant** and it suffices to prove the statement at
  `λ = 5c/4`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- The left-hand side of the target, as a function of the threshold `λ`. -/
noncomputable def shiftRowLHS (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (lam : ℝ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
    ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `[r−c]₊²` is nonincreasing in `c`. -/
lemma fsKinCoeff_anti {c c' r : ℝ} (h : c ≤ c') :
    Submission.BoseGases.fsKinCoeff c' r ≤ Submission.BoseGases.fsKinCoeff c r := by
  rw [Submission.BoseGases.fsKinCoeff, Submission.BoseGases.fsKinCoeff]
  have key : max (r - c') 0 ≤ max (r - c) 0 := max_le_max (by linarith) le_rfl
  exact pow_le_pow_left₀ (le_max_right _ _) key 2

/-- `[r−c]₊² ≤ 2r² + 2c²` (used for summability). -/
lemma fsKinCoeff_le_two_mul (c r : ℝ) :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (r - c) 0 ≤ |r - c| := max_le (le_abs_self _) (abs_nonneg _)
  have h2 : (max (r - c) 0) ^ 2 ≤ |r - c| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
  rw [sq_abs] at h2
  nlinarith [h2, sq_nonneg (r + c)]

/-- **The left-hand side is antitone in the threshold.**  For a smooth compactly supported `g`
the family `n ↦ ℓ⁻³[r_n−λ]₊²‖ĉ(k_n)‖²` is summable for every `λ`, and increasing `λ` decreases
every term.  Consequently the target's hypothesis `λ ≤ 7c/4` is redundant: the statement at
`λ = 5c/4` implies it for every `λ ≥ 5c/4`. -/
theorem shiftRowLHS_antitone {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    Antitone (shiftRowLHS ℓ g) := by
  intro c c' hcc'
  -- pointwise domination
  have hpt : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c' ‖kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c ‖kmomInt ℓ n‖ *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fsKinCoeff_anti hcc') h2) h1
  -- summability of the threshold-`c` family, via `[r−c]₊² ≤ 2r² + 2c²`
  have h2s : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
    summable_lattice_kinFT_weight hℓ hg hgc 2
  have h0s : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (0:ℕ) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
    summable_lattice_kinFT_weight hℓ hg hgc 0
  have hmaj : Summable (fun n : Fin 3 → ℤ =>
      2 * ((ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        + 2 * c ^ 2 * ((ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (0:ℕ) *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)) :=
    (h2s.mul_left 2).add (h0s.mul_left (2 * c ^ 2))
  have hfam : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c ‖kmomInt ℓ n‖ *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
    · have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
      have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg h2 (Submission.BoseGases.fsKinCoeff_nonneg c _)) h1
    · have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
      have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
      have hb := fsKinCoeff_le_two_mul c ‖kmomInt ℓ n‖
      calc (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c ‖kmomInt ℓ n‖ *
              ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
          ≤ (ℓ ^ 3)⁻¹ * (2 * ‖kmomInt ℓ n‖ ^ 2 + 2 * c ^ 2) *
              ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb h2) h1
        _ = 2 * ((ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (2:ℕ) *
                ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
              + 2 * c ^ 2 * ((ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ (0:ℕ) *
                ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
            push_cast; ring
  have hfam' : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff c' ‖kmomInt ℓ n‖ *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hfam
    · have h1 : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
      have h2 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg h2 (Submission.BoseGases.fsKinCoeff_nonneg c' _)) h1
    · exact hpt n
  have hle := Summable.tsum_le_tsum hpt hfam' hfam
  simpa only [shiftRowLHS] using hle

/-- The target's `λ ≤ 7c/4` hypothesis is redundant: the statement at `λ = 5c/4` implies it
for every `λ ≥ 5c/4`. -/
theorem sharpShiftRow_of_worstCase
    (h : ∀ {ℓ c : ℝ}, 0 < ℓ → 0 < c → 4 * Real.pi ≤ c * ℓ →
      ∀ {g : EuclideanSpace ℝ (Fin 3) → ℂ}, ContDiff ℝ (⊤ : ENat) g → HasCompactSupport g →
      tsupport g ⊆ Metric.closedBall 0 (ℓ / 2) →
      (∑' n : Fin 3 → ℤ,
          (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff (5 * c / 4) ‖kmomInt ℓ n‖ *
            ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2))
    {ℓ c lam : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    (hlam1 : 5 * c / 4 ≤ lam) (hlam2 : lam ≤ 7 * c / 4)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖kmomInt ℓ n‖ *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hmono : shiftRowLHS ℓ g lam ≤ shiftRowLHS ℓ g (5 * c / 4) :=
    shiftRowLHS_antitone hℓ hg hgc hlam1
  exact le_trans (by simpa only [shiftRowLHS] using hmono) (h hℓ hc hcℓ hg hgc hgsupp)

theorem sharpShiftRow {ℓ c lam : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    (hlam1 : 5 * c / 4 ≤ lam) (hlam2 : lam ≤ 7 * c / 4)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Submission.BoseGases.fsKinCoeff lam ‖Work.BoseBoxFock.kmomInt ℓ n‖ *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  sorry

end Work.BoseBoxFock
