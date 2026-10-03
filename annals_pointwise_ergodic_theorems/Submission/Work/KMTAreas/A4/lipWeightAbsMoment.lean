import Mathlib
import Submission.Work.KMTAreas.A4.lipWeightTsumLe
import Submission.Work.KMTAreas.A4.lipWeightAbsMomentLattice
import Submission.Work.KMTAreas.A4.summable_tsum_eps_jbDecay_weighted_shift
import Submission.Work.KMTAreas.A4.lipWeightAbsMomentPointwise

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-!
# The absolute first moment of the smoothing weight `lipWeight`

The *decaying* part of the smoothing weight of Proposition `lip` of Krause--Mirek--Tao (§5) is
controlled by its absolute first moment

`∑_m ‖w(m)‖ max 0 (|m| - N')`,

`w(m) = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε(m-m'))`.  Because the smoothing scale is `ε`, this moment is
of size `1/ε` (not `1`), uniformly in `0 < ε ≤ 1` and `1 ≤ N'`.

The proof is a three-step reduction, each step of which is a separate module:

* `lipWeightAbsMomentPointwise` — the pointwise bound
  `‖w(m)‖ max 0 (|m|-N') ≤ C (N')⁻¹ ∑_{m' ∈ [1,N']} ε ⟨ε(m-m')⟩^{-12} |m-m'|`,
  using `max 0 (|m|-N') ≤ |m-m'|` for `m' ∈ [1,N']` and the Schwartz decay of `ψ`;
* `summable_tsum_eps_jbDecay_weighted_shift` — the lattice sum of the majorant is translation
  invariant, hence the `m`-sum of the majorant is `N'` times a single lattice sum;
* `lipWeightAbsMomentLattice` — that lattice sum is at most `2^61/ε`.

The final constant is therefore `C · 2^61`.
-/

/-- **The absolute first moment of the smoothing weight.**  For every Schwartz function `ψ` there
is `C > 0` with `∑_m ‖lipWeight ψ ε N' m‖ max 0 (|m| - N') ≤ C/ε` for all `0 < ε ≤ 1`, `1 ≤ N'`. -/
theorem lipWeightAbsMoment (ψ : Work.Analysis.InverseTheory.SchwartzR) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' →
      ∑' m : ℤ, ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))
        ≤ C / ε := by
  obtain ⟨C, hCpos, hC⟩ := lipWeightAbsMomentPointwise ψ
  refine ⟨C * (2 : ℝ) ^ 61, by positivity, ?_⟩
  intro ε hε0 hε1 N' hN'
  classical
  set J : Finset ℕ := Finset.Icc 1 N' with hJ
  set g : ℕ → ℤ → ℝ := fun y m => ε * jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)| with hg
  set G : ℤ → ℝ := fun m => ∑ y ∈ J, g y m with hG
  set D : ℝ := ∑' u : ℤ, ε * jbDecay 12 (ε * (u : ℝ)) * |(u : ℝ)| with hD
  have hN'0 : (0 : ℝ) < (N' : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'
    linarith
  have hN'ne : (N' : ℝ) ≠ 0 := ne_of_gt hN'0
  have hy : ∀ y ∈ J, Summable (g y) := by
    intro y hy
    rw [hg]
    simpa using (summable_tsum_eps_jbDecay_weighted_shift hε0 (y : ℤ)).1
  have hsum_eq : ∀ y ∈ J, (∑' m : ℤ, g y m) = D := by
    intro y hy
    rw [hg, hD]
    simpa using (summable_tsum_eps_jbDecay_weighted_shift hε0 (y : ℤ)).2
  have hGsumm : Summable G := by
    have hkey : (fun m : ℤ => ∑ y ∈ J, g y m) = ∑ y ∈ J, g y := by
      funext m
      rw [Finset.sum_apply]
    rw [hG, hkey]
    refine Finset.induction_on J
      (motive := fun t => (∀ y ∈ t, Summable (g y)) → Summable (∑ y ∈ t, g y)) ?_ ?_ hy
    · intro _; exact summable_zero
    · intro a s has ih hh'
      rw [Finset.sum_insert has]
      exact (hh' a (Finset.mem_insert_self a s)).add
        (ih (fun y hy' => hh' y (Finset.mem_insert_of_mem hy')))
  have hmajsumm : Summable (fun m : ℤ => C * (N' : ℝ)⁻¹ * G m) :=
    hGsumm.mul_left (C * (N' : ℝ)⁻¹)
  have hpoint : ∀ m : ℤ, ‖lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))
      ≤ C * (N' : ℝ)⁻¹ * G m := by
    intro m
    rw [hG, hg]
    exact hC hε0 hε1 hN' m
  have hlhs : Summable (fun m : ℤ => ‖lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (le_max_left 0 _))
      hpoint hmajsumm
  have hle := Summable.tsum_le_tsum hpoint hlhs hmajsumm
  have hmul : (∑' m : ℤ, C * (N' : ℝ)⁻¹ * G m) = C * (N' : ℝ)⁻¹ * ∑' m : ℤ, G m :=
    Summable.tsum_mul_left _ hGsumm
  have hGval : (∑' m : ℤ, G m) = (N' : ℝ) * D := by
    rw [hG, Summable.tsum_finsetSum hy]
    rw [Finset.sum_congr rfl (fun y hy' => hsum_eq y hy')]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hJcard : (J.card : ℝ) = (N' : ℝ) := by
      rw [hJ, Nat.card_Icc]
      have h : N' + 1 - 1 = N' := by omega
      rw [h]
    rw [hJcard]
  have hDle : D ≤ (2 : ℝ) ^ 61 / ε := by
    rw [hD]
    exact lipWeightAbsMomentLattice hε0 hε1
  calc ∑' m : ℤ, ‖lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))
      ≤ ∑' m : ℤ, C * (N' : ℝ)⁻¹ * G m := hle
    _ = C * (N' : ℝ)⁻¹ * ∑' m : ℤ, G m := hmul
    _ = C * (N' : ℝ)⁻¹ * ((N' : ℝ) * D) := by rw [hGval]
    _ = C * D := by
        have h2 : C * (N' : ℝ)⁻¹ * ((N' : ℝ) * D) = C * ((N' : ℝ)⁻¹ * (N' : ℝ)) * D := by ring
        rw [h2, inv_mul_cancel₀ hN'ne, mul_one]
    _ ≤ C * ((2 : ℝ) ^ 61 / ε) := mul_le_mul_of_nonneg_left hDle hCpos.le
    _ = C * (2 : ℝ) ^ 61 / ε := by ring

end Work.KMTAreas.A4
