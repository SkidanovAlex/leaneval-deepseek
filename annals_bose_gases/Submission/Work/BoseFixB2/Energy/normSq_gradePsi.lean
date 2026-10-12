import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.Sector.normB_secProj_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.normSq_gradePsi`

FS §6 (`lem:LocMatrices`) grades a box state `Φ` by the sectors `1_{n₊=k}Φ` of the
excitation-number operator `n₊` and forms the norm profile

    `ψ_i = ‖1_{n₊=i}Φ‖ / ‖Φ‖`

(of `Work.BoseFixB2.gradePsi`).  The normalisation demanded by the localisation theorem
of Lieb–Solovej (`Work.UBBInputs3.normSq`, `Work.UBBInputs3.iRange`) is

    `normSq (iRange nn) ψ = 1`

for the window length `nn = fsNn v μ n`.  This is the content proved here: the profile is a
unit vector in the window range.

## Proof

Write `ℓ = fsSide v μ`, `N = fsNn v μ n ≥ n + 1` and `g = gradePsi v h μ n ℓ Φ`.  Then
`g j = 0` for `j ∉ [0,n]`, so the sum over `iRange N = [0,N−1]` collapses to the sum over
`[0,n]` (`Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside`); on `[0,n]`,

    `‖g j‖² = normB v μ n (vecZ ℓ Φ j) / normB v μ n Φ`

(`Complex.normSq_ofReal` and `Real.mul_self_sqrt`).  The remaining identity

    `Σ_{j∈[0,n]} normB v μ n (vecZ ℓ Φ j) = normB v μ n Φ`

is Pythagoras for the sectors (`sum_normB_vecZ_eq` below): for `ℓ > 0` it is
`normB_secProj_sum` after reindexing the ℤ-interval `[0,n]` to `range (n+1)`; for `ℓ ≤ 0`
the box `abox n ℓ` has measure zero as soon as `n ≥ 1` (so both sides vanish), while for
`n = 0` the single sector `vecZ ℓ Φ 0 = secProj ℓ 0 Φ` is `Φ` itself.  Dividing by
`normB v μ n Φ ≠ 0` (from the hypothesis `hpos`) gives the claim.

## Imports

`Mathlib`; the vocabulary `Submission.Work.BoseFixB2.Defs`; the sector Pythagoras
`Submission.Work.BoseFixB2.Sector.normB_secProj_sum`; and the ℤ-interval sum bookkeeping
`Submission.Work.UBBInputs3.MatLoc.Interval`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric Finset

namespace Work.BoseFixB2.Energy

open Submission.BoseGases Work.BoseFixB2 Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Elementary facts about the box norm -/

/-- `normB` is nonnegative: it is the box integral of a square. -/
lemma normB_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) : 0 ≤ Work.BoseBoxFix.normB v μ n Ψ := by
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (Ψ x))

/-! ## 2. The ℤ-interval sum over `[0,n]` as a sum over `range (n+1)` -/

/-- A sum over the ℤ-interval `[0,n]` is a sum over `range (n+1)`. -/
lemma sum_Icc_zero_cast_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), f j = ∑ k ∈ Finset.range (n + 1), f (k : ℤ) := by
  rw [Int.Icc_eq_finset_map (0 : ℤ) (n : ℤ), Finset.sum_map]
  refine Finset.sum_congr ?_ fun k _ => ?_
  · simp
  · simp

/-! ## 3. The box has measure zero for nonpositive side length -/

/-- For `ℓ ≤ 0` the centred cube `acube ℓ` has zero volume. -/
lemma acube_volume_eq_zero_of_nonpos (ℓ : ℝ) (hℓ : ℓ ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.acube ℓ) = 0 := by
  rcases lt_or_eq_of_le hℓ with h | h
  · have hemp : Submission.BoseGases.acube ℓ = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨y, hy⟩
      have h0 := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy 0
      simp only [Set.mem_Icc] at h0
      linarith [h0.1, h0.2]
    rw [hemp, MeasureTheory.measure_empty]
  · subst h
    rw [Submission.BoseGases.acube_volume 0 le_rfl]
    norm_num

/-- For `ℓ ≤ 0` and `n ≥ 1` the box `abox n ℓ` has zero measure (one factor already
collapses, the type `X n` being a product of at least one copy of `ℝ³`). -/
lemma abox_volume_eq_zero_of_one_le_of_nonpos (n : ℕ) (hn : 1 ≤ n) (ℓ : ℝ) (hℓ : ℓ ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) = 0 := by
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      = MeasureTheory.Measure.pi
          (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace ℝ (Fin 3)))) by rfl]
  rw [Submission.BoseGases.abox_eq_pi_acube, MeasureTheory.Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) ?_
  exact acube_volume_eq_zero_of_nonpos ℓ hℓ

/-! ## 4. `normB` vanishes when the box has measure zero -/

/-- The box `L²` norm square vanishes when the box has measure zero. -/
lemma sqNormB_eq_zero_of_volume_zero {n : ℕ} {ℓ : ℝ}
    (h : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) = 0) (Ψ : Submission.BoseGases.X n → ℝ) :
    Work.BoseKinLoc.sqNormB n ℓ Ψ = 0 := by
  simp only [Work.BoseKinLoc.sqNormB]
  exact MeasureTheory.setIntegral_measure_zero (fun x => (Ψ x) ^ 2) h

/-- `normB v μ n Ψ = 0` when `μ` gives a nonpositive side length and `n ≥ 1`. -/
lemma normB_eq_zero_of_one_le_of_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hℓ : Work.BoseFixB2.fsSide v μ ≤ 0)
    (Ψ : Submission.BoseGases.X n → ℝ) : Work.BoseBoxFix.normB v μ n Ψ = 0 := by
  rw [show Work.BoseBoxFix.normB v μ n Ψ
      = Work.BoseKinLoc.sqNormB n (Work.BoseFixB2.fsSide v μ) Ψ from rfl]
  exact sqNormB_eq_zero_of_volume_zero
    (abox_volume_eq_zero_of_one_le_of_nonpos n hn (Work.BoseFixB2.fsSide v μ) hℓ) Ψ

/-! ## 5. The value of the profile on one sector -/

/-- On the sector indices `j ∈ [0,n]`, the squared modulus of `gradePsi` is
`normB (vecZ ℓ Φ j) / normB Φ`. -/
lemma gradePsi_normSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (ℓ : ℝ) (j : ℤ)
    (hj : j ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    ‖Work.BoseFixB2.gradePsi v h μ n ℓ Φ j‖ ^ 2
      = Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ j)
        / Work.BoseBoxFix.normB v μ n Φ := by
  have h : 0 ≤ j ∧ j ≤ (n : ℤ) := by simpa [Finset.mem_Icc] using hj
  have hA : 0 ≤ Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ j) := normB_nonneg _
  have hB : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := normB_nonneg _
  rw [Work.BoseFixB2.gradePsi, if_pos h, Complex.sq_norm, Complex.normSq_ofReal]
  rw [div_mul_div_comm, Real.mul_self_sqrt hA, Real.mul_self_sqrt hB]

/-! ## 6. Pythagoras for the sectors, in the ℤ-indexed form needed here -/

/-- **The sector decomposition in the window range**: the box norms of the sectors of `Φ`,
padded by zeros to the window length (`vecZ`), add up to the box norm of `Φ`. -/
lemma sum_normB_vecZ_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    (∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
      = Work.BoseBoxFix.normB v μ n Φ := by
  by_cases hℓ : 0 < Work.BoseFixB2.fsSide v μ
  · have hstep : ∀ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j)
          = Work.BoseBoxFix.normB v μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) j.toNat Φ) := by
      intro j hj
      rw [Work.BoseFixB2.vecZ, if_pos (by simpa [Finset.mem_Icc] using hj)]
    refine Eq.trans (Finset.sum_congr rfl hstep) ?_
    rw [sum_Icc_zero_cast_eq_sum_range (fun j : ℤ => Work.BoseBoxFix.normB v μ n
      (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) j.toNat Φ)) n]
    simp only [Int.toNat_natCast]
    exact Work.BoseFixB2.Sector.normB_secProj_sum (h := h) hℓ hΦ
  · simp only [not_lt] at hℓ
    by_cases hn : n = 0
    · subst hn
      rw [show Finset.Icc (0 : ℤ) ((0 : ℕ) : ℤ) = {0} from by simp [Finset.Icc_self],
        Finset.sum_singleton]
      have hz : Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (0 : ℤ) = Φ := by
        rw [Work.BoseFixB2.vecZ, if_pos (by norm_num)]
        simp [Work.BoseFixB2.secProj, Work.BoseFixB2.jointProj]
      rw [hz]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [normB_eq_zero_of_one_le_of_nonpos (v := v) (μ := μ) hn1 hℓ Φ]
      exact Finset.sum_eq_zero
        (fun j _ => normB_eq_zero_of_one_le_of_nonpos (v := v) (μ := μ) hn1 hℓ _)

/-! ## 7. The target -/

theorem normSq_gradePsi {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ) : Work.UBBInputs3.normSq (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) = 1 := by
  have hNge : n + 1 ≤ Work.BoseFixB2.fsNn v μ n := by
    simpa only [Work.BoseFixB2.fsNn] using
      Work.BoseFixB2.succ_le_gradeNn n (𝓜 := Work.BoseFixB2.fsM v μ)
  have hNgeZ : (n : ℤ) ≤ ((Work.BoseFixB2.fsNn v μ n : ℕ) : ℤ) - 1 := by
    have h : (n : ℤ) + 1 ≤ (Work.BoseFixB2.fsNn v μ n : ℤ) := by exact_mod_cast hNge
    linarith
  have hvan : ∀ t : ℤ, t ∉ Finset.Icc (0 : ℤ) (n : ℤ) →
      ‖Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ t‖ ^ 2 = 0 := by
    intro t ht
    have hcond : ¬ (0 ≤ t ∧ t ≤ (n : ℤ)) := by simpa [Finset.mem_Icc] using ht
    rw [Work.BoseFixB2.gradePsi, if_neg hcond]
    simp
  have hstep1 : Work.UBBInputs3.normSq (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n))
      (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
      = ∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
          ‖Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j‖ ^ 2 := by
    rw [Work.UBBInputs3.normSq, Work.UBBInputs3.iRange]
    exact Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside _ le_rfl hNgeZ hvan
  have hstep2 : (∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
          ‖Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ j‖ ^ 2)
      = (∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ),
          Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j))
        / Work.BoseBoxFix.normB v μ n Φ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j hj => gradePsi_normSq (Work.BoseFixB2.fsSide v μ) j hj)
  rw [hstep1, hstep2, sum_normB_vecZ_eq (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hΦ,
    div_self (ne_of_gt hpos)]

end Work.BoseFixB2.Energy
