import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.trivial_interface

/-!
# The Jurkat–Richert framework with a **real** sift limit

The interface `Submission.ChenPlan.IsLinear` uses a *real* sift limit `z`, and so does the
parameter `s = log D / log z` of the linear sieve.  The `Framework.lean` vocabulary instead uses a
*natural* sift limit `Z`, which forces the parameter to be `log D / log Z`; since the only natural
number available is `Z = ⌈z⌉ ≥ z`, that parameter is strictly *smaller* than the interface's, and
the gap is not absorbable against the tabulated envelope `Utab` (whose grid is coarse — the
transfer fails exactly at the grid points, see `PLAN.md`).

Here we redo the vocabulary with a **real** sift limit.  Because the primes below a real `z` are
exactly the natural numbers `p < ⌈z⌉₊`, everything is a rewriting of the natural theory:
`siftedSumR A z = siftedSumLt A ⌈z⌉₊` and `VfR A z = Vf A ⌈z⌉₊` (`siftedSumR_eq_siftedSumLt`,
`VfR_eq_Vf`), so all the natural-limit lemmas remain available.

* `siftedSumR A z` : the mass of the support elements not divisible by any prime of `P` below `z`.
* `VfR A z` : `∏_{p ∣ P, p < z} (1 - ν p)`.
* `UpperValidR K U a b` / `LowerValidR K L a b` : the pair `(U,L)` is a valid
  upper/lower envelope for every linear sieve problem with `IsLinear · z K` and parameter
  `s = log D / log z ∈ [a,b]`; `UpperValidAllR`/`LowerValidAllR` drop the upper end.
* `jrUR U L T` / `jrLR U L T` : the Jurkat–Richert transform with stepping function `T`
  (`s ↦ T s ≥ s`), `s · U_new s = T s · U (T s) - ∫_s^{T s} L (t - 1) dt`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

noncomputable section

/-- Sifted sum with a **real** sift limit: the weight of the support elements that are not
divisible by any prime of `P` which is `< z`. -/
noncomputable def siftedSumR (A : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ n ∈ A.support,
    if ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → ¬ p ∣ n then A.weights n else 0

/-- `VfR A z = ∏_{p ∣ P, p < z} (1 - ν p)`: the product of the sieve factors over the primes of
`P` below the real sift limit `z`. -/
noncomputable def VfR (A : BoundingSieve) (z : ℝ) : ℝ :=
  ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - A.nu p)

theorem siftedSumR_eq_siftedSumLt (A : BoundingSieve) (z : ℝ) :
    siftedSumR A z = siftedSumLt A ⌈z⌉₊ := by
  unfold siftedSumR siftedSumLt
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  simp only [Nat.lt_ceil]

theorem VfR_eq_Vf (A : BoundingSieve) (z : ℝ) : VfR A z = Vf A ⌈z⌉₊ := by
  unfold VfR Vf
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.lt_ceil]

theorem VfR_factor_nonneg (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    0 ≤ 1 - A.nu p := Vf_factor_nonneg A hp

theorem VfR_factor_le_one (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    1 - A.nu p ≤ 1 := Vf_factor_le_one A hp

theorem VfR_factor_pos (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    0 < 1 - A.nu p := Vf_factor_pos A hp

theorem VfR_nonneg (A : BoundingSieve) (z : ℝ) : 0 ≤ VfR A z := by
  rw [VfR_eq_Vf]; exact Vf_nonneg A _

theorem VfR_pos (A : BoundingSieve) (z : ℝ) : 0 < VfR A z := by
  rw [VfR_eq_Vf]; exact Vf_pos A _

theorem VfR_le_one (A : BoundingSieve) (z : ℝ) : VfR A z ≤ 1 := by
  rw [VfR_eq_Vf]; exact Vf_le_one A _

/-- `VfR` is nonincreasing in the sift limit. -/
theorem VfR_anti (A : BoundingSieve) {z z' : ℝ} (h : z ≤ z') : VfR A z' ≤ VfR A z := by
  rw [VfR_eq_Vf A z', VfR_eq_Vf A z]
  exact Vf_anti A (Nat.ceil_le.mpr (le_trans h (Nat.le_ceil z')))

/-- If every prime of `P` is below `z`, then `VfR A z = sieveV A`. -/
theorem VfR_eq_sieveV (A : BoundingSieve) {z : ℝ}
    (hz : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z) :
    VfR A z = Submission.ChenPlan.sieveV A := by
  unfold VfR Submission.ChenPlan.sieveV
  congr 1
  exact Finset.filter_true_of_mem (fun p hp => hz p hp)

/-- If every prime of `P` is below `z`, then `siftedSumR A z = A.siftedSum`. -/
theorem siftedSumR_eq_siftedSum (A : BoundingSieve) {z : ℝ}
    (hz : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z) : siftedSumR A z = A.siftedSum := by
  rw [siftedSumR_eq_siftedSumLt A z]
  exact siftedSumLt_eq_siftedSum A (fun p hp => Nat.lt_ceil.mpr (hz p hp))

theorem siftedSumR_nonneg (A : BoundingSieve) (z : ℝ) : 0 ≤ siftedSumR A z := by
  rw [siftedSumR_eq_siftedSumLt]; exact siftedSumLt_nonneg A _

/-- `siftedSumR` is nonincreasing in the sift limit. -/
theorem siftedSumR_anti (A : BoundingSieve) {z z' : ℝ} (h : z ≤ z') :
    siftedSumR A z' ≤ siftedSumR A z := by
  unfold siftedSumR
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hc : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z → ¬ p ∣ n
  · rw [if_pos hc]
    by_cases hc' : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z' → ¬ p ∣ n
    · rw [if_pos hc']
    · rw [if_neg hc']; exact A.weights_nonneg n
  · rw [if_neg hc]
    by_cases hc' : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z' → ¬ p ∣ n
    · exact absurd (fun p hp hpz => hc' p hp (lt_of_lt_of_le hpz h)) hc
    · rw [if_neg hc']

/-- The interface hypothesis `IsLinear` (verbatim). -/
def IsLinearR (A : BoundingSieve) (z K : ℝ) : Prop := Submission.ChenPlan.IsLinear A z K

/-- **Upper validity with a real sift limit**. -/
def UpperValidR (K : ℝ) (U : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (z D : ℝ),
    2 ≤ z → D₀ ≤ D → Submission.ChenPlan.IsLinear A z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log z → Real.log D / Real.log z ≤ b →
    siftedSumR A z ≤ A.totalMass * VfR A z * (U (Real.log D / Real.log z) + η)
      + Submission.ChenPlan.remSum A D

/-- **Lower validity with a real sift limit**. -/
def LowerValidR (K : ℝ) (L : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (z D : ℝ),
    2 ≤ z → D₀ ≤ D → Submission.ChenPlan.IsLinear A z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log z → Real.log D / Real.log z ≤ b →
    A.totalMass * VfR A z * (L (Real.log D / Real.log z) - η) - Submission.ChenPlan.remSum A D
      ≤ siftedSumR A z

/-- Upper validity with no upper end of the parameter range. -/
def UpperValidAllR (K : ℝ) (U : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (z D : ℝ),
    2 ≤ z → D₀ ≤ D → Submission.ChenPlan.IsLinear A z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log z →
    siftedSumR A z ≤ A.totalMass * VfR A z * (U (Real.log D / Real.log z) + η)
      + Submission.ChenPlan.remSum A D

/-- Lower validity with no upper end of the parameter range. -/
def LowerValidAllR (K : ℝ) (L : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (z D : ℝ),
    2 ≤ z → D₀ ≤ D → Submission.ChenPlan.IsLinear A z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log z →
    A.totalMass * VfR A z * (L (Real.log D / Real.log z) - η) - Submission.ChenPlan.remSum A D
      ≤ siftedSumR A z

theorem upperValidR_of_all {K : ℝ} {U : ℝ → ℝ} {a b : ℝ} (h : UpperValidAllR K U a) :
    UpperValidR K U a b :=
  fun η hη => by
    obtain ⟨D₀, hD₀⟩ := h η hη
    exact ⟨D₀, fun A z D hz hD hlin hX ha _ => hD₀ A z D hz hD hlin hX ha⟩

theorem lowerValidR_of_all {K : ℝ} {L : ℝ → ℝ} {a b : ℝ} (h : LowerValidAllR K L a) :
    LowerValidR K L a b :=
  fun η hη => by
    obtain ⟨D₀, hD₀⟩ := h η hη
    exact ⟨D₀, fun A z D hz hD hlin hX ha _ => hD₀ A z D hz hD hlin hX ha⟩

/-- A *larger* upper function is still valid. -/
theorem UpperValidR.mono {K : ℝ} {U U' : ℝ → ℝ} {a b : ℝ} (h : UpperValidR K U a b)
    (hle : ∀ s, U s ≤ U' s) : UpperValidR K U' a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  refine ⟨D₀, fun A z D hz hD hlin hX ha hb => ?_⟩
  have h0 := hD₀ A z D hz hD hlin hX ha hb
  have hV : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  have hstep : A.totalMass * VfR A z * (U (Real.log D / Real.log z) + η)
      ≤ A.totalMass * VfR A z * (U' (Real.log D / Real.log z) + η) :=
    mul_le_mul_of_nonneg_left (by linarith [hle (Real.log D / Real.log z)]) hV
  exact le_trans h0 (add_le_add hstep le_rfl)

/-- A *smaller* lower function is still valid. -/
theorem LowerValidR.mono {K : ℝ} {L L' : ℝ → ℝ} {a b : ℝ} (h : LowerValidR K L a b)
    (hle : ∀ s, L' s ≤ L s) : LowerValidR K L' a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  refine ⟨D₀, fun A z D hz hD hlin hX ha hb => ?_⟩
  have h0 := hD₀ A z D hz hD hlin hX ha hb
  have hV : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  have hstep : A.totalMass * VfR A z * (L' (Real.log D / Real.log z) - η)
      ≤ A.totalMass * VfR A z * (L (Real.log D / Real.log z) - η) :=
    mul_le_mul_of_nonneg_left (by linarith [hle (Real.log D / Real.log z)]) hV
  exact le_trans (sub_le_sub_right hstep _) h0

/-- The zero function is a valid lower envelope. -/
theorem lowerValidR_zero (K a b : ℝ) : LowerValidR K (fun _ => 0) a b := by
  intro η hη
  refine ⟨0, fun A z D _ _ _ hX _ _ => ?_⟩
  have hVnn : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  have hle : A.totalMass * VfR A z * ((0:ℝ) - η) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hVnn (by linarith)
  linarith [remSum_nonneg A D, siftedSumR_nonneg A z]

theorem lowerValidAllR_zero (K a : ℝ) : LowerValidAllR K (fun _ => 0) a := by
  intro η hη
  refine ⟨0, fun A z D _ _ _ hX _ => ?_⟩
  have hVnn : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  have hle : A.totalMass * VfR A z * ((0:ℝ) - η) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hVnn (by linarith)
  linarith [remSum_nonneg A D, siftedSumR_nonneg A z]

/-- The minimum of two valid upper envelopes is valid. -/
theorem upperValidR_min {K : ℝ} {U U' : ℝ → ℝ} {a b : ℝ}
    (h : UpperValidR K U a b) (h' : UpperValidR K U' a b) :
    UpperValidR K (fun s => min (U s) (U' s)) a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  obtain ⟨D₀', hD₀'⟩ := h' η hη
  refine ⟨max D₀ D₀', fun A z D hz hD hlin hX ha hb => ?_⟩
  have h1 := hD₀ A z D hz (le_trans (le_max_left _ _) hD) hlin hX ha hb
  have h2 := hD₀' A z D hz (le_trans (le_max_right _ _) hD) hlin hX ha hb
  have hV : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  show siftedSumR A z ≤ A.totalMass * VfR A z *
      (min (U (Real.log D / Real.log z)) (U' (Real.log D / Real.log z)) + η)
      + Submission.ChenPlan.remSum A D
  by_cases hle : U (Real.log D / Real.log z) ≤ U' (Real.log D / Real.log z)
  · rw [min_eq_left hle]; exact h1
  · rw [min_eq_right (le_of_lt (not_le.mp hle))]; exact h2

/-- The maximum of two valid lower envelopes is valid. -/
theorem lowerValidR_max {K : ℝ} {L L' : ℝ → ℝ} {a b : ℝ}
    (h : LowerValidR K L a b) (h' : LowerValidR K L' a b) :
    LowerValidR K (fun s => max (L s) (L' s)) a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  obtain ⟨D₀', hD₀'⟩ := h' η hη
  refine ⟨max D₀ D₀', fun A z D hz hD hlin hX ha hb => ?_⟩
  have h1 := hD₀ A z D hz (le_trans (le_max_left _ _) hD) hlin hX ha hb
  have h2 := hD₀' A z D hz (le_trans (le_max_right _ _) hD) hlin hX ha hb
  show A.totalMass * VfR A z *
      (max (L (Real.log D / Real.log z)) (L' (Real.log D / Real.log z)) - η)
      - Submission.ChenPlan.remSum A D ≤ siftedSumR A z
  by_cases hle : L (Real.log D / Real.log z) ≤ L' (Real.log D / Real.log z)
  · rw [max_eq_right hle]; exact h2
  · rw [max_eq_left (le_of_lt (not_le.mp hle))]; exact h1

/-- **The `D > P` regime.**  When the level exceeds the modulus `P` and every prime of `P` is
below the sift limit, the Möbius identity gives the upper inequality for any envelope `U` with
`U s ≥ 1`. -/
theorem upper_of_prodPrimes_ltR (A : BoundingSieve) {z D η : ℝ}
    (hD : (A.prodPrimes : ℝ) < D) (hX : 0 ≤ A.totalMass)
    (hzp : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z) (hη : 0 ≤ η)
    {U : ℝ → ℝ} (hU : 1 ≤ U (Real.log D / Real.log z)) :
    siftedSumR A z ≤ A.totalMass * VfR A z * (U (Real.log D / Real.log z) + η)
      + Submission.ChenPlan.remSum A D := by
  have htriv := siftedSum_le_trivial A hD
  have hVpos : 0 < Submission.ChenPlan.sieveV A := sieveV_pos A
  have hVnn : 0 ≤ A.totalMass * Submission.ChenPlan.sieveV A := mul_nonneg hX hVpos.le
  have h1 : 1 ≤ U (Real.log D / Real.log z) + η := by linarith
  have hmul : A.totalMass * Submission.ChenPlan.sieveV A
      ≤ A.totalMass * Submission.ChenPlan.sieveV A * (U (Real.log D / Real.log z) + η) := by
    calc A.totalMass * Submission.ChenPlan.sieveV A
        = A.totalMass * Submission.ChenPlan.sieveV A * 1 := (mul_one _).symm
      _ ≤ A.totalMass * Submission.ChenPlan.sieveV A * (U (Real.log D / Real.log z) + η) :=
          mul_le_mul_of_nonneg_left h1 hVnn
  rw [siftedSumR_eq_siftedSum A hzp, VfR_eq_sieveV A hzp]
  linarith

/-- **The `D > P` regime** for the lower bound. -/
theorem lower_of_prodPrimes_ltR (A : BoundingSieve) {z D c : ℝ}
    (hD : (A.prodPrimes : ℝ) < D) (hX : 0 ≤ A.totalMass)
    (hzp : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z) (hc : c ≤ 1) :
    A.totalMass * VfR A z * c - Submission.ChenPlan.remSum A D ≤ siftedSumR A z := by
  rw [siftedSumR_eq_siftedSum A hzp, VfR_eq_sieveV A hzp]
  exact trivial_le_siftedSum A hD hX hc

end

end Work.ChenPlan.LinearSieve
