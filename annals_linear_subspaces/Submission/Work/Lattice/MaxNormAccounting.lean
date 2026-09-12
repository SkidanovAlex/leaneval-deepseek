import Mathlib
import Submission.Work.Lattice.MaxNormEndpoints
import Submission.Work.Lattice.AccountingOneSided
import Submission.Work.Polygon.AngularRanks

/-!
# The accounting for the max-norm Grayson polygon of the §3 flow

This module glues the max-norm polygon layer (`MaxNormPolygon`, `MaxNormEndpoints`) to the
abstract accounting of de Saxcé's Lemma 4 (`AccountingOneSided`):

* `maxSlope_mono` — the slopes of the polygon are nondecreasing (convexity);
* `sum_blockStart_mul_delta` — the **closure identity** `Σ_s Λ_s·(jb(s+1) − jb s) = Σ_{i<d} Λ_i`
  for the block boundaries `jb = blockStart`, which vanishes by `maxSlope_sum_eq_zero`;
* `slopeDeriv` / `levelDeriv` — the level derivatives `r_s = ċ_t(jb_s) = Σ_{i<jb_s} Λ_i'(t)`,
  with `r 0 = 0`, `r R = 0` (`Σ_{i<d} Λ_i ≡ 0`) and the identity
  `Σ_s Λ_s·(r(s+1) − r s) = Σ_{i<d} Λ_i(t)·Λ_i'(t)` (constancy of the slope on blocks);
* **`maxNorm_accounting`** — at a good time (`Σ_i Λ_i Λ_i' ≥ −1`, supplied by
  `MaxNormPolygon.maxSlope_good_time`) the accounting inequality
  `Σ_s Δ effPos_s · Λ_s ≤ ℓ(d−ℓ)/d` holds with the effective capacities `effPos` built from the
  level derivatives `r`.

Module `Submission.Work.Lattice.MaxNormAccounting`, namespace `Submission.MaxNormAccounting`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.MaxNormPolygon
open Submission.MaxNormEndpoints
open Submission.Polygon
open Submission.AngularRanks
open Submission.AccountingOneSided

namespace Submission.MaxNormAccounting

variable {d : ℕ}

/-- **The polygon slopes are nondecreasing** (convexity). -/
lemma maxSlope_mono {Λ₀ : Submodule ℤ (RD d)} {ℓ : ℕ} {t : ℝ} {i j : ℕ}
    (hij : i ≤ j) (hj : j + 1 ≤ d) :
    maxSlope (d := d) Λ₀ ℓ t i ≤ maxSlope (d := d) Λ₀ ℓ t j :=
  dslope_mono (maxPolygon_convex (d := d) Λ₀ ℓ t) hij hj

/-- **The running-maximum step** (range form of `AccountingOneSided.sum_delta_mul_le_of_le`):
if `ω' ≥ ω` with equal endpoints and the `Λ_s` are nondecreasing on `{0,…,R−1}`
(`Λ s ≤ Λ (s+1)` for `s + 2 ≤ R`), then `Σ_s Δω'_s·Λ_s ≤ Σ_s Δω_s·Λ_s`. -/
lemma sum_delta_mul_le_of_le_range {R : ℕ} {ω ω' Λ : ℕ → ℝ} (hω0 : ω 0 = 0) (hω'0 : ω' 0 = 0)
    (hωR : ω R = ω' R) (hle : ∀ s : ℕ, s ≤ R → ω s ≤ ω' s)
    (hmono : ∀ s : ℕ, s + 2 ≤ R → Λ s ≤ Λ (s + 1)) :
    ∑ s ∈ Finset.range R, (ω' (s + 1) - ω' s) * Λ s ≤
      ∑ s ∈ Finset.range R, (ω (s + 1) - ω s) * Λ s := by
  rw [abel_forward ω' Λ R, abel_forward ω Λ R, hω0, hω'0, hωR]
  simp only [zero_mul, sub_zero]
  have h1 : ∑ s ∈ Finset.range R, ω (s + 1) * (Λ (s + 1) - Λ s) ≤
      ∑ s ∈ Finset.range R, ω' (s + 1) * (Λ (s + 1) - Λ s) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hsR : s < R := Finset.mem_range.mp hs
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hsR) with hlt | heq
    · have hΔ : 0 ≤ Λ (s + 1) - Λ s := by
        have := hmono s (by omega)
        linarith
      exact mul_le_mul_of_nonneg_right (hle (s + 1) (Nat.succ_le_of_lt hsR)) hΔ
    · have hs1 : s + 1 = R := by omega
      have hEq : ω (s + 1) = ω' (s + 1) := by rw [hs1, hωR]
      rw [hEq]
  linarith

/-- **The closure identity of the accounting.**  With `jb := blockStart d c` the block
boundaries of `c` and `Λ_s := dslope c (jb s)` the block slopes,
`Σ_s Λ_s·(jb (s+1) − jb s) = Σ_{i<d} dslope c i`. -/
lemma sum_blockStart_mul_delta (c : ℕ → ℝ) :
    (∑ s ∈ Finset.range (numBlocks d c),
        dslope c (blockStart d c s) *
          (((blockStart d c (s + 1) : ℕ) : ℝ) - ((blockStart d c s : ℕ) : ℝ))) =
      ∑ i ∈ Finset.range d, dslope c i := by
  rw [sum_range_eq_sum_blocks (d := d) c (fun i => dslope c i)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hle : blockStart d c s ≤ blockStart d c (s + 1) := blockStart_mono d c s
  rw [← Nat.cast_sub hle, ← Nat.card_Ico]
  rw [Finset.sum_congr rfl (fun i hi => (dslope_eq_on_block c d s
    (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2))]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The closure identity in the max-norm-polygon vocabulary. -/
lemma sum_blockStart_maxSlope_mul_delta (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) *
          (((blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1) : ℕ) : ℝ) -
            ((blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℕ) : ℝ))) =
      ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ t i := by
  simpa only [maxSlope] using
    sum_blockStart_mul_delta (d := d) (maxPolygon (d := d) Λ₀ ℓ t)

/-- The derivative of the max-norm polygon slope `Λ_i`. -/
noncomputable def slopeDeriv (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  deriv (fun u => maxSlope (d := d) Λ₀ ℓ u i) t

/-- The level derivative `r_s = ċ_t(jb s) = Σ_{i<jb s} Λ_i'(t)`. -/
noncomputable def levelDeriv (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) (jb : ℕ → ℕ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (jb s), slopeDeriv (d := d) Λ₀ ℓ t i

/-- The accounting sum of the max-norm polygon at time `t`. -/
noncomputable def accSum (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) : ℝ :=
  let c := maxPolygon (d := d) Λ₀ ℓ t
  let jb : ℕ → ℕ := blockStart d c
  let jbR : ℕ → ℝ := fun s => (jb s : ℝ)
  let r := levelDeriv (d := d) Λ₀ ℓ t jb
  ∑ s ∈ Finset.range (numBlocks d c),
    (effPos d ℓ jbR r (s + 1) - effPos d ℓ jbR r s) * maxSlope (d := d) Λ₀ ℓ t (jb s)

/-- The unfolding of `accSum` (beta-reduced). -/
theorem accSum_apply (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    accSum (d := d) Λ₀ ℓ t =
      (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        (effPos d ℓ (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ))
            (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t))) (s + 1)
          - effPos d ℓ (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ))
            (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t))) s) *
        maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s)) := rfl

/-- The capacity sequence of the accounting: the effective positions computed from the level
derivatives of the max-norm polygon. -/
noncomputable def capacity (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) : ℕ → ℝ :=
  let c := maxPolygon (d := d) Λ₀ ℓ t
  let jb : ℕ → ℕ := blockStart d c
  fun s => effPos d ℓ (fun s => (jb s : ℝ)) (levelDeriv (d := d) Λ₀ ℓ t jb) s

/-- `accSum` in the vocabulary of the capacity sequence. -/
theorem accSum_eq_capacity (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    accSum (d := d) Λ₀ ℓ t =
      (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        (capacity (d := d) Λ₀ ℓ t (s + 1) - capacity (d := d) Λ₀ ℓ t s) *
          maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s)) := by
  rfl

/-- The endpoint values of the capacity sequence. -/
lemma capacity_zero (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    capacity (d := d) Λ₀ ℓ t 0 = 0 := by
  rw [capacity]
  dsimp only
  exact effPos_zero (d := d) (ℓ := ℓ) (by simp [blockStart_zero])
    (by rw [levelDeriv, blockStart_zero]; simp)

/-- The top endpoint of the capacity sequence is `ℓ` (given the vanishing of the top level
derivative). -/
lemma capacity_top {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {Λ₀ : Submodule ℤ (RD d)} {t : ℝ}
    (hrR : levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t))
      (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = 0) :
    capacity (d := d) Λ₀ ℓ t (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = (ℓ : ℝ) := by
  rw [capacity]
  dsimp only
  exact effPos_top (d := d) (ℓ := ℓ) hℓ0 hℓd (by simp [blockStart_numBlocks]) hrR

/-- **At a good time, the `accSum` of the max-norm polygon is bounded by `ℓ(d−ℓ)/d`.** -/
theorem accSum_le_of_good_time {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ}
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun u => maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
        ℓ u i.val) t)
    (hgood0 : -1 ≤ ∑ i : Fin d,
      maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
        ℓ t i.val *
      deriv (fun u => maxSlope (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ u i.val) t) :
    accSum (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
      ℓ t ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set Λ₀ : Submodule ℤ (RD d) :=
    Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  rw [accSum_apply]
  have hjb0 : (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ)) 0 = 0 := by
    simp [blockStart_zero]
  have hjbR : (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ))
      (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = (d : ℝ) := by
    simp [blockStart_numBlocks]
  have hr0 : levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) 0 = 0 := by
    rw [levelDeriv, blockStart_zero]
    simp
  have hderiv : deriv (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) t =
      ∑ i ∈ Finset.range d, slopeDeriv (d := d) Λ₀ ℓ t i := by
    have hfun : (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) =
        (∑ i ∈ Finset.range d, fun u => maxSlope (d := d) Λ₀ ℓ u i) := by
      funext u
      simp [Finset.sum_apply]
    rw [hfun]
    exact deriv_sum (u := Finset.range d)
      (A := fun i => fun u => maxSlope (d := d) Λ₀ ℓ u i) (x := t)
      (fun i hi => hdiff ⟨i, Finset.mem_range.mp hi⟩)
  have hrR : levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t))
      (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = 0 := by
    rw [levelDeriv, blockStart_numBlocks, ← hderiv]
    have hconst : (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) =
        (fun _ => (0 : ℝ)) := by
      funext u
      simpa [hΛ₀] using maxSlope_sum_eq_zero (d := d) hℓ0 hℓd g u
    rw [hconst, deriv_const]
  have hclosed : (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) *
          ((fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ)) (s + 1) -
            (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ)) s)) = 0 := by
    rw [sum_blockStart_maxSlope_mul_delta]
    simpa [hΛ₀] using maxSlope_sum_eq_zero (d := d) hℓ0 hℓd g t
  have hgood : -1 ≤ (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) *
          (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) (s + 1) -
            levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) s)) := by
    have hstep : (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
          maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) *
            (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) (s + 1) -
              levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) s)) =
        ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ t i * slopeDeriv (d := d) Λ₀ ℓ t i := by
      have hterm : ∀ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
          maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) *
            (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) (s + 1) -
              levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) s) =
            ∑ i ∈ Finset.Ico (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s)
                (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1)),
              maxSlope (d := d) Λ₀ ℓ t i * slopeDeriv (d := d) Λ₀ ℓ t i := by
        intro s _
        have hmono : blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s ≤
            blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1) := blockStart_mono _ _ _
        have hsub : levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) (s + 1) -
              levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)) s =
            ∑ i ∈ Finset.Ico (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s)
                (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1)),
              slopeDeriv (d := d) Λ₀ ℓ t i := by
          rw [levelDeriv, levelDeriv]
          exact (Finset.sum_Ico_eq_sub _ hmono).symm
        rw [hsub, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi1 : blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s ≤ i := (Finset.mem_Ico.mp hi).1
        have hi2 : i < blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1) := (Finset.mem_Ico.mp hi).2
        have heq : maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s) =
            maxSlope (d := d) Λ₀ ℓ t i := by
          have := dslope_eq_on_block (maxPolygon (d := d) Λ₀ ℓ t) d s hi1 hi2
          simpa only [maxSlope] using this.symm
        rw [heq]
      rw [Finset.sum_congr rfl hterm]
      exact (sum_range_eq_sum_blocks (d := d) (maxPolygon (d := d) Λ₀ ℓ t)
        (fun i => maxSlope (d := d) Λ₀ ℓ t i * slopeDeriv (d := d) Λ₀ ℓ t i)).symm
    rw [hstep]
    have hconv : (∑ i : Fin d,
          maxSlope (d := d) Λ₀ ℓ t i.val *
            deriv (fun u => maxSlope (d := d) Λ₀ ℓ u i.val) t) =
        ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ t i * slopeDeriv (d := d) Λ₀ ℓ t i := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => maxSlope (d := d) Λ₀ ℓ t i *
          deriv (fun u => maxSlope (d := d) Λ₀ ℓ u i) t) d]
      rfl
    rw [← hconv, hΛ₀]
    exact hgood0
  exact accounting_le_rate_inv (d := d) (ℓ := ℓ) hℓ0 hℓd
    (R := numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) (numBlocks_pos _ hd0)
    (fun s => (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s : ℝ))
    (levelDeriv (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t)))
    (fun s => maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s))
    hjb0 hjbR hr0 hrR hclosed hgood

/-- The top level derivative vanishes at a good time (differentiability of the slopes is
needed to commute the derivative with the finite sum). -/
theorem levelDeriv_top_eq_zero_of_good {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ}
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun u => maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
        ℓ u i.val) t) :
    levelDeriv (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t
      (blockStart d (maxPolygon (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t))
      (numBlocks d (maxPolygon (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t)) = 0 := by
  set Λ₀ : Submodule ℤ (RD d) :=
    Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  have hderiv : deriv (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) t =
      ∑ i ∈ Finset.range d, slopeDeriv (d := d) Λ₀ ℓ t i := by
    have hfun : (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) =
        (∑ i ∈ Finset.range d, fun u => maxSlope (d := d) Λ₀ ℓ u i) := by
      funext u
      simp [Finset.sum_apply]
    rw [hfun]
    exact deriv_sum (u := Finset.range d)
      (A := fun i => fun u => maxSlope (d := d) Λ₀ ℓ u i) (x := t)
      (fun i hi => hdiff ⟨i, Finset.mem_range.mp hi⟩)
  rw [levelDeriv, blockStart_numBlocks, ← hderiv]
  have hconst : (fun u => ∑ i ∈ Finset.range d, maxSlope (d := d) Λ₀ ℓ u i) =
      (fun _ => (0 : ℝ)) := by
    funext u
    simpa [hΛ₀] using maxSlope_sum_eq_zero (d := d) hℓ0 hℓd g u
  rw [hconst, deriv_const]

/-- **The accounting at a good time.**  For the §3 flow lattice `Λ₀ = g(ℤᵈ)` (`g` a linear
isometry) and every `T` there is a time `t ≥ T` at which the accounting inequality

    `Σ_s (effPos(s+1) − effPos s)·Λ_s ≤ ℓ(d−ℓ)/d`

holds, where `effPos` are the effective capacities built from the level derivatives of the
max-norm polygon. -/
theorem maxNorm_accounting {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      accSum (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
        ℓ t ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  obtain ⟨t, htT, hdiff, hgood0⟩ :=
    maxSlope_good_time (d := d) hℓ0 hℓd g (c := 1) one_pos T
  exact ⟨t, htT, accSum_le_of_good_time (d := d) hℓ0 hℓd g hdiff hgood0⟩

/-- **The running-maximum reduction.**  At a good time, any *capacity sequence* `ω` which
dominates the effective capacities and has the same endpoints (`ω 0 = 0`, `ω R = ℓ`) satisfies
the same bound `Σ_s Δω_s·Λ_s ≤ ℓ(d−ℓ)/d`. -/
lemma le_accSum_of_capacity_le {ℓ : ℕ} {Λ₀ : Submodule ℤ (RD d)} {t : ℝ} {ω : ℕ → ℝ}
    (hcap0 : capacity (d := d) Λ₀ ℓ t 0 = 0)
    (hcapR : capacity (d := d) Λ₀ ℓ t (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = (ℓ : ℝ))
    (hω0 : ω 0 = 0)
    (hωR : ω (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)) = (ℓ : ℝ))
    (hle : ∀ s ≤ numBlocks d (maxPolygon (d := d) Λ₀ ℓ t),
      capacity (d := d) Λ₀ ℓ t s ≤ ω s) :
    (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d) Λ₀ ℓ t)),
        (ω (s + 1) - ω s) *
          maxSlope (d := d) Λ₀ ℓ t (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s))
      ≤ accSum (d := d) Λ₀ ℓ t := by
  rw [accSum_eq_capacity]
  refine sum_delta_mul_le_of_le_range (R := numBlocks d (maxPolygon (d := d) Λ₀ ℓ t))
    (ω := capacity (d := d) Λ₀ ℓ t) (ω' := ω)
    (Λ := fun s => maxSlope (d := d) Λ₀ ℓ t
      (blockStart d (maxPolygon (d := d) Λ₀ ℓ t) s)) hcap0 hω0 ?_ hle ?_
  · rw [hcapR, hωR]
  · intro s hs
    have hb := blockStart_mono d (maxPolygon (d := d) Λ₀ ℓ t) s
    have hlt : blockStart d (maxPolygon (d := d) Λ₀ ℓ t) (s + 1) < d :=
      blockStart_lt_numBlocks _ _ (by omega)
    exact maxSlope_mono (d := d) (t := t) hb (by omega)

/-- **The position accounting at a good time.**  For the §3 flow lattice and every `T` there is
`t ≥ T` such that for *every* sequence `ω` with `ω 0 = 0`, `ω R = ℓ` which dominates the
effective capacities, the position-type accounting inequality `Σ_s Δω_s·Λ_s ≤ ℓ(d−ℓ)/d` holds.
(The extraction supplies `ω` = the positions of the flag members.) -/
theorem position_accounting {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∀ ω : ℕ → ℝ,
      ω 0 = 0 →
      ω (numBlocks d (maxPolygon (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t)) = (ℓ : ℝ) →
      (∀ s ≤ numBlocks d (maxPolygon (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t),
        capacity (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t s
          ≤ ω s) →
      (∑ s ∈ Finset.range (numBlocks d (maxPolygon (d := d)
            (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t)),
          (ω (s + 1) - ω s) *
            maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
              ℓ t (blockStart d (maxPolygon (d := d)
                (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t) s))
        ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  obtain ⟨t, htT, hdiff, hgood0⟩ :=
    maxSlope_good_time (d := d) hℓ0 hℓd g (c := 1) one_pos T
  refine ⟨t, htT, fun ω hω0 hωR hle => ?_⟩
  set Λ₀ : Submodule ℤ (RD d) :=
    Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  have hrR := levelDeriv_top_eq_zero_of_good (d := d) hℓ0 hℓd g (t := t) hdiff
  have hcapR := capacity_top (d := d) (ℓ := ℓ) hℓ0 hℓd hrR
  have hcap0 := capacity_zero (d := d) Λ₀ ℓ t
  have hacc := accSum_le_of_good_time (d := d) hℓ0 hℓd g (t := t) hdiff hgood0
  have hle' := le_accSum_of_capacity_le (d := d) (ℓ := ℓ) (Λ₀ := Λ₀) (t := t) (ω := ω)
    hcap0 hcapR hω0 hωR hle
  linarith [hacc, hle']

end Submission.MaxNormAccounting

end
