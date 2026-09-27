import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.cesaro_tail_bound
import Submission.Work.EKLComp.BirkhoffDefs

/-!
# `hopf_cesaro_bound`: the Hopf argument, Cesàro form

For `u ∈ Uminus t = G⁻(t)` (the horospherical subgroup contracted by `aDiag t`) and a function
`f : X₃ → ℝ` which is *uniformly* continuous in the group-displacement sense (`hf`) and bounded
(`hB`), the Birkhoff averages of `f` along the `aDiag t`-orbit of `u • x` and of `x` become
eventually `ε`-close.

## Proof

Write `T y = aDiag t • y` and `v n = aDiag t ^ n * u * (aDiag t ^ n)⁻¹`.  Since the action is a
group action,

  `T^[n] (u • x) = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • T^[n] x = v n • T^[n] x`,

and `v n → 1` (`Work.EKLC6Core.tendsto_conj_mem_uminus`).  Choosing `W` for `hf` at `ε/2`, there
is `N` with `v n ∈ W` for all `n ≥ N`.  Hence the `n`-th summands of the two Birkhoff sums are
`≤ ε/2` for `n ≥ N` and `≤ 2B` for `n < N` (boundedness, triangle inequality).  Averaging over
`n < k` with `k ≥ N` therefore costs `N·2B` in the head and `k·ε/2` in the tail, and choosing
`4BN ≤ εk` makes the head term `≤ ε/2`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The arithmetic `ε/3`-slack estimate of the Hopf argument: if `4 B N ≤ ε k` (with `B ≥ 0`,
`ε > 0`, `k ≥ 1`) then the Cesàro head term is at most `ε/2`. -/
theorem cesaro_slack {B N ε : ℝ} {k : ℕ} (hε : 0 < ε) (hk : 1 ≤ k)
    (h4 : 4 * B * N ≤ ε * k) :
    (k : ℝ)⁻¹ * (2 * B * N + (ε / 2) * (k : ℝ)) ≤ ε := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h2 : 2 * B * N * (k : ℝ)⁻¹ ≤ ε / 2 := by
    have h : (2 * B * N) ≤ (ε / 2) * (k : ℝ) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hkR))
    have hkk : ((ε / 2) * (k : ℝ)) * (k : ℝ)⁻¹ = ε / 2 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hkR), mul_one]
    nlinarith [h3, hkk]
  have hsplit : (k : ℝ)⁻¹ * (2 * B * N + (ε / 2) * (k : ℝ))
      = 2 * B * N * (k : ℝ)⁻¹ + ε / 2 := by
    field_simp
  rw [hsplit]
  linarith

theorem hopf_cesaro_bound (t : Fin 3 → ℝ) {u : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLC6Core.Uminus t) {f : Work.EKLContract.X3 → ℝ}
    (hf : ∀ ε > 0, ∃ W : Set Work.EKLContract.SL3, IsOpen W ∧ (1 : Work.EKLContract.SL3) ∈ W ∧
      ∀ v ∈ W, ∀ x : Work.EKLContract.X3, |f (v • x) - f x| ≤ ε)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (x : Work.EKLContract.X3) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K,
      |Work.EKLComp.Birkhoff.birkA (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)
          f k (u • x)
        - Work.EKLComp.Birkhoff.birkA (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)
          f k x| ≤ ε := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (f x)) (hB x)
  -- the uniform continuity modulus at `ε/2`, and the contraction of `u`
  obtain ⟨W, hWopen, hW1, hWbd⟩ := hf (ε / 2) (by linarith)
  have hev : ∀ᶠ n in Filter.atTop, aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ W :=
    (tendsto_conj_mem_uminus t u hu).eventually (hWopen.mem_nhds hW1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- the threshold `K`
  obtain ⟨K0, hK0⟩ := exists_nat_ge (4 * B * N / ε)
  refine ⟨max K0 (max N 1), fun k hk => ?_⟩
  have hkN : N ≤ k := le_trans (le_trans (le_max_left N 1) (le_max_right K0 (max N 1))) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right N 1) (le_max_right K0 (max N 1))) hk
  have hkK0 : (K0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast le_trans (le_max_left K0 (max N 1)) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hinv : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hkpos)
  have h4 : 4 * B * (N : ℝ) ≤ ε * (k : ℝ) := by
    have h : 4 * B * (N : ℝ) / ε ≤ (k : ℝ) := le_trans hK0 hkK0
    have h' := mul_le_mul_of_nonneg_right h (le_of_lt hε)
    rw [div_mul_cancel₀ _ (ne_of_gt hε)] at h'
    linarith
  set T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun y => aDiag t • y with hT
  -- the orbit identity `T^[n] (u • x) = v n • T^[n] x`
  have horbit : ∀ n : ℕ, T^[n] (u • x) = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • (T^[n] x) := by
    intro n
    simp only [hT, smul_iterate]
    simp only [← mul_smul]
    group
  -- the two pointwise bounds on the summands
  have hhead : ∀ n, n < N → |f (T^[n] (u • x)) - f (T^[n] x)| ≤ 2 * B := by
    intro n _
    calc |f (T^[n] (u • x)) - f (T^[n] x)|
        ≤ |f (T^[n] (u • x))| + |f (T^[n] x)| := by
          rw [sub_eq_add_neg, ← abs_neg (f (T^[n] x))]
          exact abs_add_le _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring
  have htail : ∀ n, N ≤ n → |f (T^[n] (u • x)) - f (T^[n] x)| ≤ ε / 2 := by
    intro n hn
    rw [horbit n]
    exact hWbd _ (hN n hn) _
  -- the Birkhoff difference as one Cesàro average of differences
  have hbirk : ∀ z : Work.EKLContract.X3,
      Work.EKLComp.Birkhoff.birkA T f k z = (k : ℝ)⁻¹ * ∑ n ∈ Finset.range k, f (T^[n] z) :=
    fun z => Work.EKLComp.Birkhoff.birkA_def T f k z
  have hdiff : Work.EKLComp.Birkhoff.birkA T f k (u • x)
        - Work.EKLComp.Birkhoff.birkA T f k x
      = (k : ℝ)⁻¹ * ∑ n ∈ Finset.range k, (f (T^[n] (u • x)) - f (T^[n] x)) := by
    rw [hbirk, hbirk, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  calc |(k : ℝ)⁻¹ * ∑ n ∈ Finset.range k, (f (T^[n] (u • x)) - f (T^[n] x))|
      ≤ (k : ℝ)⁻¹ * ∑ n ∈ Finset.range k, |f (T^[n] (u • x)) - f (T^[n] x)| := by
        rw [abs_mul, abs_of_nonneg hinv]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv
    _ ≤ (k : ℝ)⁻¹ * (2 * B * (N : ℝ) + (ε / 2) * (k : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hinv
        exact cesaro_tail_bound hkN hhead htail (by linarith)
    _ ≤ ε := cesaro_slack hε hk1 h4

end Work.EKLC6Core
