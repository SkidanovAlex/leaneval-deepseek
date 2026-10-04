import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.SupBound
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3: pointwise bounds and decay of the Fourier coefficients of the localised components

For a `1`-periodic `C^∞` function `f` on the flat torus with coefficient family `c = fourierCoeff f`
and weighted `ℓ²` square `CSq s c = Σ_k ⟨k⟩^{2s} ‖c k‖²`, a single coefficient is dominated by the
whole series, because all terms are nonnegative:

* `‖c μ‖² ≤ CSq 0 c`  — in particular `‖c μ‖ ≤ √(CSq 0 c)`;
* `(‖c μ‖ ⟨μ⟩^M)² = ‖c μ‖² ⟨μ⟩^{2M} ≤ CSq (2M) c`  — in particular
  `‖c μ‖ ⟨μ⟩^M ≤ √(CSq (2M) c)`.

Composing with `CSq s (fourierCoeff (Rper i h a b)) ≤ BNorm s h` (a single entry of the defining
triple sum, by `sum3_single_le`) and with the hypothesis `BNorm s (u m t) ≤ B s` gives the two
assertions of `coeffFun_bound_and_decay`: the `L^∞`-type bound `‖û(μ)‖ ≤ √(B 0)` and the weighted
decay `‖û(μ)‖ ⟨μ⟩^M ≤ √(B (2M))` which is the `H^M` uniform control used by the Galerkin scheme.
-/

noncomputable section

namespace Work.Diff.STE.Lead

open Work.Diff.STE

/-! ## Single-term bounds inside `CSq` -/

/-- A single summand of `CSq s c` is at most the whole (summable, nonnegative) series. -/
private lemma term_le_CSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (s : ℕ) (μ : ι → ℤ)
    (hsum : Summable fun k : ι → ℤ => (wt k) ^ s * ‖c k‖ ^ 2) :
    ‖c μ‖ ^ 2 * (wt μ) ^ s ≤ CSq s c := by
  have h := Summable.le_tsum hsum μ
    (fun j _ => mul_nonneg (pow_nonneg (le_of_lt (wt_pos j)) s) (sq_nonneg _))
  simpa only [CSq, mul_comm] using h

/-- The `L^∞` bound on the Fourier coefficients: `‖c μ‖ ≤ √(CSq 0 c)`. -/
private lemma norm_le_sqrt_CSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (μ : ι → ℤ) (hsum : Summable fun k : ι → ℤ => ‖c k‖ ^ 2) :
    ‖c μ‖ ≤ Real.sqrt (CSq 0 c) := by
  have hsum' : Summable fun k : ι → ℤ => (wt k) ^ 0 * ‖c k‖ ^ 2 := by
    simpa only [pow_zero, one_mul] using hsum
  have h := term_le_CSq c 0 μ hsum'
  simp only [pow_zero, mul_one] at h
  rw [Real.le_sqrt (norm_nonneg _) (CSq_nonneg 0 c)]
  exact h

/-- The weighted decay of a single Fourier coefficient: `‖c μ‖ ⟨μ⟩^M ≤ √(CSq (2M) c)`. -/
private lemma norm_mul_wt_pow_le_sqrt_CSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (M : ℕ) (μ : ι → ℤ)
    (hsum : Summable fun k : ι → ℤ => (wt k) ^ (2 * M) * ‖c k‖ ^ 2) :
    ‖c μ‖ * (wt μ) ^ M ≤ Real.sqrt (CSq (2 * M) c) := by
  have h := term_le_CSq c (2 * M) μ hsum
  rw [Real.le_sqrt (mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt (wt_pos μ)) M))
    (CSq_nonneg _ _)]
  calc (‖c μ‖ * (wt μ) ^ M) ^ 2 = ‖c μ‖ ^ 2 * (wt μ) ^ (2 * M) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm M 2]
    _ ≤ CSq (2 * M) c := h

/-! ## The target statement -/

theorem coeffFun_bound_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (B : ℕ → ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t) a b))
    (hper : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t) a b))
    (hBnd : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (hB0 : (0 : ℝ) ≤ B 0) :
    (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
        (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ →
        ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ ≤ Real.sqrt (B 0))
    ∧ (∀ (M : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
        (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ →
        ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M
          ≤ Real.sqrt (B (2 * M))) := by
  constructor
  · -- the `L^∞` bound, from Parseval summability at level `0`
    intro i a b μ m t ht
    have hc := summable_weighted_fourierCoeff_of_contDiff (D.Rper i (u m t) a b)
      (hsm m t i a b) (hper m t i a b) 0
    have hc0 : Summable fun k : Fin (Module.finrank ℝ E) → ℤ =>
        ‖fourierCoeff (D.Rper i (u m t) a b) k‖ ^ 2 := by
      simpa only [pow_zero, one_mul] using hc
    -- the squared bound `‖û(μ)‖² ≤ BNorm 0 (u m t) ≤ B 0`
    have hsq : ‖fourierCoeff (D.Rper i (u m t) a b) μ‖ ^ 2 ≤ B 0 := by
      have h1 : ‖fourierCoeff (D.Rper i (u m t) a b) μ‖ ^ 2
          ≤ CSq 0 (fourierCoeff (D.Rper i (u m t) a b)) := by
        have h := term_le_CSq (fourierCoeff (D.Rper i (u m t) a b)) 0 μ
          (by simpa only [pow_zero, one_mul] using hc)
        simpa only [pow_zero, mul_one] using h
      refine h1.trans ?_
      refine (sum3_single_le
        (fun i' a' b' => CSq 0 (fourierCoeff (D.Rper i' (u m t) a' b')))
        (fun i' a' b' => CSq_nonneg 0 _) i a b).trans ?_
      simpa only [B3Data.BNorm] using hBnd m t ht 0
    rw [Real.le_sqrt (norm_nonneg _) hB0]
    exact hsq
  · -- the weighted decay, from Parseval summability at level `2M`
    intro M i a b μ m t ht
    have hc := summable_weighted_fourierCoeff_of_contDiff (D.Rper i (u m t) a b)
      (hsm m t i a b) (hper m t i a b) (2 * M)
    refine (norm_mul_wt_pow_le_sqrt_CSq (fourierCoeff (D.Rper i (u m t) a b)) M μ hc).trans
      (Real.sqrt_le_sqrt ?_)
    refine (sum3_single_le
      (fun i' a' b' => CSq (2 * M) (fourierCoeff (D.Rper i' (u m t) a' b')))
      (fun i' a' b' => CSq_nonneg (2 * M) _) i a b).trans ?_
    simpa only [B3Data.BNorm] using hBnd m t ht (2 * M)

end Work.Diff.STE.Lead
