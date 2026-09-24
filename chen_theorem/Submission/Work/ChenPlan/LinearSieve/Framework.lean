import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.basic

/-!
# The Jurkat–Richert framework for the linear sieve

Vocabulary of the Jurkat–Richert iteration for Mathlib's `BoundingSieve`, plus everything in the
framework that needs no sieve input at all.

* `Vf A Z` : the product `∏_{p ∣ P, p < Z} (1 - ν p)` over the primes of `P` below the sift limit
  `Z`.  For `Z` above every prime of `P` it is `sieveV A`.
* `IsLinearNat A Z K` : the interface hypothesis `IsLinear A z K`, phrased with the *natural* sift
  limit `Z` (so that Buchstab splits happen at natural numbers).  `IsLinear A z K` implies
  `IsLinearNat A Z K` for every `Z ≥ z`.
* `UpperValid K U a b` / `LowerValid K L a b` : the pair `(U, L)` satisfies the linear sieve
  upper/lower inequality, for every sieve problem with `IsLinearNat · z K`, on the parameter range
  `s = log D / log Z ∈ [a,b]` (`UpperValidAll`/`LowerValidAll` drop the upper end).
* `jrU U L T` / `jrL U L T` : the Jurkat–Richert transform with endpoint `T`,
  `s · U_new s = T · U T - ∫_s^T L (t - 1) dt`, `s · L_new s = T · L T - ∫_s^T U (t - 1) dt`.

The two main targets of the chapter (see `PLAN.md`) are the *Jurkat–Richert step* (the transform
preserves validity) and the existence of a valid pair realising the interface's `Utab` and
`993/1000`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

noncomputable section

/-- `Vf A Z = ∏_{p ∣ P, p < Z} (1 - ν p)`: the product of the sieve factors over the primes of
`P` below the sift limit `Z`. -/
noncomputable def Vf (A : BoundingSieve) (Z : ℕ) : ℝ :=
  ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => p < Z), (1 - A.nu p)

theorem Vf_factor_nonneg (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    0 ≤ 1 - A.nu p := by
  have hpP : p ∣ A.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have := A.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
  linarith

theorem Vf_factor_le_one (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    1 - A.nu p ≤ 1 := by
  have hpP : p ∣ A.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have := A.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
  linarith

theorem Vf_factor_pos (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    0 < 1 - A.nu p := by
  have hpP : p ∣ A.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have := A.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
  linarith

theorem Vf_nonneg (A : BoundingSieve) (Z : ℕ) : 0 ≤ Vf A Z := by
  unfold Vf
  exact Finset.prod_nonneg (fun p hp => Vf_factor_nonneg A (Finset.mem_filter.mp hp).1)

theorem Vf_pos (A : BoundingSieve) (Z : ℕ) : 0 < Vf A Z := by
  unfold Vf
  exact Finset.prod_pos (fun p hp => Vf_factor_pos A (Finset.mem_filter.mp hp).1)

theorem Vf_le_one (A : BoundingSieve) (Z : ℕ) : Vf A Z ≤ 1 := by
  unfold Vf
  exact Finset.prod_le_one₀ (fun p hp => le_of_lt (Vf_factor_pos A (Finset.mem_filter.mp hp).1))
    (fun p hp => Vf_factor_le_one A (Finset.mem_filter.mp hp).1)

/-- `Vf` is nonincreasing in the sift limit. -/
theorem Vf_anti (A : BoundingSieve) {Z Z' : ℕ} (h : Z ≤ Z') : Vf A Z' ≤ Vf A Z := by
  unfold Vf
  refine Finset.prod_le_prod_of_subset_of_le_one₀ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, lt_of_lt_of_le hp.2 h⟩
  · intro p hp
    exact Vf_factor_nonneg A (Finset.mem_filter.mp hp).1
  · intro p hp _
    exact Vf_factor_le_one A (Finset.mem_filter.mp hp).1

/-- If every prime of `P` is below the sift limit `Z`, then `Vf A Z = sieveV A`. -/
theorem Vf_eq_sieveV (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) : Vf A Z = Submission.ChenPlan.sieveV A := by
  unfold Vf Submission.ChenPlan.sieveV
  congr 1
  exact Finset.filter_true_of_mem (fun p hp => hZ p hp)

/-- Coprimality with a squarefree modulus, tested prime by prime. -/
theorem coprime_prodPrimes_iff (A : BoundingSieve) (n : ℕ) :
    Nat.Coprime A.prodPrimes n ↔ ∀ p ∈ A.prodPrimes.primeFactors, ¬ p ∣ n := by
  have key : Nat.Coprime (∏ p ∈ A.prodPrimes.primeFactors, p) n
      ↔ ∀ p ∈ A.prodPrimes.primeFactors, ¬ p ∣ n := by
    rw [Nat.coprime_prod_left_iff]
    constructor
    · intro h p hp hpn
      exact (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp (h p hp) hpn
    · intro h p hp
      rw [(Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd]
      exact h p hp
  rwa [Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree] at key

/-- If every prime of `P` is below the sift limit `Z`, then `siftedSumLt A Z = A.siftedSum`. -/
theorem siftedSumLt_eq_siftedSum (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) : siftedSumLt A Z = A.siftedSum := by
  unfold siftedSumLt BoundingSieve.siftedSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h : ∀ p ∈ A.prodPrimes.primeFactors, ¬ p ∣ n
  · rw [if_pos (fun p hp _ => h p hp), if_pos ((coprime_prodPrimes_iff A n).mpr h)]
  · push Not at h
    obtain ⟨p, hp, hpn⟩ := h
    rw [if_neg (fun hc => hc p hp (hZ p hp) hpn),
      if_neg (fun hc => ((coprime_prodPrimes_iff A n).mp hc) p hp hpn)]

/-- `siftedSumLt` is nonnegative. -/
theorem siftedSumLt_nonneg (A : BoundingSieve) (Z : ℕ) : 0 ≤ siftedSumLt A Z := by
  unfold siftedSumLt
  refine Finset.sum_nonneg (fun n _ => ?_)
  split_ifs
  · exact BoundingSieve.weights_nonneg A n
  · exact le_rfl

/-- The interface remainder sum is nonnegative. -/
theorem remSum_nonneg (A : BoundingSieve) (D : ℝ) : 0 ≤ Submission.ChenPlan.remSum A D := by
  unfold Submission.ChenPlan.remSum
  refine Finset.sum_nonneg (fun d _ => ?_)
  exact mul_nonneg (by positivity) (abs_nonneg _)

/-- The inverse sieve factors over the primes of `P` above `w` multiply to at least `1`. -/
theorem one_le_prod_inv (A : BoundingSieve) (w : ℝ) :
    1 ≤ ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - A.nu p)⁻¹ := by
  refine Finset.one_le_prod₀ (fun p hp => ?_)
  have hp' : p ∈ A.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
  exact (one_le_inv₀ (Vf_factor_pos A hp')).mpr (Vf_factor_le_one A hp')

/-- The interface hypothesis `IsLinear`, phrased with a *natural* sift limit `Z`. -/
def IsLinearNat (A : BoundingSieve) (Z : ℕ) (K : ℝ) : Prop :=
  (∀ p ∈ A.prodPrimes.primeFactors, p < Z) ∧
  ∀ w : ℝ, 2 ≤ w → w < (Z : ℝ) →
    (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - A.nu p)⁻¹)
      ≤ (Real.log Z / Real.log w) * (1 + K / Real.log w)

/-- `IsLinear A z K` implies `IsLinearNat A Z K` for every natural `Z ≥ z` (with `0 ≤ K`). -/
theorem isLinearNat_of_isLinear (A : BoundingSieve) {z : ℝ} {Z : ℕ} {K : ℝ}
    (hz : 2 ≤ z) (hK : 0 ≤ K) (hZ : z ≤ (Z : ℝ)) (h : Submission.ChenPlan.IsLinear A z K) :
    IsLinearNat A Z K := by
  obtain ⟨hprimes, hprod⟩ := h
  refine ⟨fun p hp => by exact_mod_cast (lt_of_lt_of_le (hprimes p hp) hZ), fun w hw2 hwZ => ?_⟩
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  rcases lt_or_ge w z with hwz | hwz
  · have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    have h1 := hprod w hw2 hwz
    have hone := one_le_prod_inv A w
    have hpos : 0 < Real.log z / Real.log w := div_pos hlogz hlogw
    have h2 : 0 ≤ 1 + K / Real.log w :=
      (mul_nonneg_iff_of_pos_left hpos).mp (le_trans zero_le_one (le_trans hone h1))
    have hle : Real.log z / Real.log w ≤ Real.log (Z : ℝ) / Real.log w :=
      div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hZ) hlogw.le
    calc (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - A.nu p)⁻¹)
        ≤ (Real.log z / Real.log w) * (1 + K / Real.log w) := h1
      _ ≤ (Real.log (Z : ℝ) / Real.log w) * (1 + K / Real.log w) :=
          mul_le_mul_of_nonneg_right hle h2
  · -- `z ≤ w`: no prime of `P` is `≥ w`, the product is empty
    have hempty : A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)) = ∅ :=
      Finset.filter_false_of_mem (fun p hp hle' => by
        have := hprimes p hp
        linarith)
    rw [hempty, Finset.prod_empty]
    have hlogZ : Real.log w ≤ Real.log (Z : ℝ) := Real.log_le_log (by linarith) hwZ.le
    have h1 : 1 ≤ Real.log Z / Real.log w := (one_le_div hlogw).mpr hlogZ
    have h2 : 1 ≤ 1 + K / Real.log w := by
      have : 0 ≤ K / Real.log w := div_nonneg hK hlogw.le
      linarith
    nlinarith [h1, h2]

/-- **Upper validity**: the function `U` is a valid upper bound for the linear sieve on the
parameter range `[a,b]`. -/
def UpperValid (K : ℝ) (U : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
    2 ≤ Z → D₀ ≤ D → IsLinearNat A Z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log Z → Real.log D / Real.log Z ≤ b →
    siftedSumLt A Z
      ≤ A.totalMass * Vf A Z * (U (Real.log D / Real.log Z) + η) + Submission.ChenPlan.remSum A D

/-- **Lower validity**: the function `L` is a valid lower bound for the linear sieve on the
parameter range `[a,b]`. -/
def LowerValid (K : ℝ) (L : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
    2 ≤ Z → D₀ ≤ D → IsLinearNat A Z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log Z → Real.log D / Real.log Z ≤ b →
    A.totalMass * Vf A Z * (L (Real.log D / Real.log Z) - η) - Submission.ChenPlan.remSum A D
      ≤ siftedSumLt A Z

/-- Upper validity with no upper end of the parameter range. -/
def UpperValidAll (K : ℝ) (U : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
    2 ≤ Z → D₀ ≤ D → IsLinearNat A Z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log Z →
    siftedSumLt A Z
      ≤ A.totalMass * Vf A Z * (U (Real.log D / Real.log Z) + η) + Submission.ChenPlan.remSum A D

/-- Lower validity with no upper end of the parameter range. -/
def LowerValidAll (K : ℝ) (L : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
    2 ≤ Z → D₀ ≤ D → IsLinearNat A Z K → 0 ≤ A.totalMass →
    a ≤ Real.log D / Real.log Z →
    A.totalMass * Vf A Z * (L (Real.log D / Real.log Z) - η) - Submission.ChenPlan.remSum A D
      ≤ siftedSumLt A Z

theorem upperValid_of_all {K : ℝ} {U : ℝ → ℝ} {a b : ℝ} (h : UpperValidAll K U a) :
    UpperValid K U a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  exact ⟨D₀, fun A Z D hZ hD hlin hX ha _ => hD₀ A Z D hZ hD hlin hX ha⟩

theorem lowerValid_of_all {K : ℝ} {L : ℝ → ℝ} {a b : ℝ} (h : LowerValidAll K L a) :
    LowerValid K L a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  exact ⟨D₀, fun A Z D hZ hD hlin hX ha _ => hD₀ A Z D hZ hD hlin hX ha⟩

theorem UpperValid.mono {K : ℝ} {U U' : ℝ → ℝ} {a b : ℝ} (h : UpperValid K U a b)
    (hle : ∀ s, U s ≤ U' s) : UpperValid K U' a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  refine ⟨D₀, fun A Z D hZ hD hlin hX ha hb => ?_⟩
  have h0 := hD₀ A Z D hZ hD hlin hX ha hb
  have hV : 0 ≤ A.totalMass * Vf A Z := mul_nonneg hX (Vf_nonneg A Z)
  have hstep : A.totalMass * Vf A Z * (U (Real.log D / Real.log Z) + η)
      ≤ A.totalMass * Vf A Z * (U' (Real.log D / Real.log Z) + η) :=
    mul_le_mul_of_nonneg_left (by linarith [hle (Real.log D / Real.log Z)]) hV
  exact le_trans h0 (add_le_add hstep le_rfl)

/-- A *smaller* lower function is still valid. -/
theorem LowerValid.mono {K : ℝ} {L L' : ℝ → ℝ} {a b : ℝ} (h : LowerValid K L a b)
    (hle : ∀ s, L' s ≤ L s) : LowerValid K L' a b := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := h η hη
  refine ⟨D₀, fun A Z D hZ hD hlin hX ha hb => ?_⟩
  have h0 := hD₀ A Z D hZ hD hlin hX ha hb
  have hV : 0 ≤ A.totalMass * Vf A Z := mul_nonneg hX (Vf_nonneg A Z)
  have hstep : A.totalMass * Vf A Z * (L' (Real.log D / Real.log Z) - η)
      ≤ A.totalMass * Vf A Z * (L (Real.log D / Real.log Z) - η) :=
    mul_le_mul_of_nonneg_left (by linarith [hle (Real.log D / Real.log Z)]) hV
  exact le_trans (sub_le_sub_right hstep _) h0

theorem lowerValid_zero (K a b : ℝ) : LowerValid K (fun _ => 0) a b := by
  intro η hη
  refine ⟨0, fun A Z D _ _ _ hX _ _ => ?_⟩
  have hVnn : 0 ≤ A.totalMass * Vf A Z := mul_nonneg hX (Vf_nonneg A Z)
  have hle : A.totalMass * Vf A Z * ((0:ℝ) - η) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hVnn (by linarith)
  linarith [remSum_nonneg A D, siftedSumLt_nonneg A Z]

theorem lowerValidAll_zero (K a : ℝ) : LowerValidAll K (fun _ => 0) a := by
  intro η hη
  refine ⟨0, fun A Z D _ _ _ hX _ => ?_⟩
  have hVnn : 0 ≤ A.totalMass * Vf A Z := mul_nonneg hX (Vf_nonneg A Z)
  have hle : A.totalMass * Vf A Z * ((0:ℝ) - η) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hVnn (by linarith)
  linarith [remSum_nonneg A D, siftedSumLt_nonneg A Z]

/-- Glue two functions at a parameter `m`. -/
noncomputable def glue (U₁ U₂ : ℝ → ℝ) (m : ℝ) : ℝ → ℝ :=
  fun s => if s ≤ m then U₁ s else U₂ s

theorem upperValid_glue {K : ℝ} {U₁ U₂ : ℝ → ℝ} {a m b : ℝ}
    (h₁ : UpperValid K U₁ a m) (h₂ : UpperValid K U₂ m b) :
    UpperValid K (glue U₁ U₂ m) a b := by
  intro η hη
  obtain ⟨D₁, hD₁⟩ := h₁ η hη
  obtain ⟨D₂, hD₂⟩ := h₂ η hη
  refine ⟨max D₁ D₂, fun A Z D hZ hD hlin hX ha hb => ?_⟩
  by_cases hs : Real.log D / Real.log Z ≤ m
  · rw [glue, if_pos hs]
    exact hD₁ A Z D hZ (le_trans (le_max_left _ _) hD) hlin hX ha hs
  · rw [glue, if_neg hs]
    exact hD₂ A Z D hZ (le_trans (le_max_right _ _) hD) hlin hX (le_of_lt (lt_of_not_ge hs)) hb

theorem lowerValid_glue {K : ℝ} {L₁ L₂ : ℝ → ℝ} {a m b : ℝ}
    (h₁ : LowerValid K L₁ a m) (h₂ : LowerValid K L₂ m b) :
    LowerValid K (glue L₁ L₂ m) a b := by
  intro η hη
  obtain ⟨D₁, hD₁⟩ := h₁ η hη
  obtain ⟨D₂, hD₂⟩ := h₂ η hη
  refine ⟨max D₁ D₂, fun A Z D hZ hD hlin hX ha hb => ?_⟩
  by_cases hs : Real.log D / Real.log Z ≤ m
  · rw [glue, if_pos hs]
    exact hD₁ A Z D hZ (le_trans (le_max_left _ _) hD) hlin hX ha hs
  · rw [glue, if_neg hs]
    exact hD₂ A Z D hZ (le_trans (le_max_right _ _) hD) hlin hX (le_of_lt (lt_of_not_ge hs)) hb

/-- The (`0`-extended) lower function used in the Jurkat–Richert upper transform: parameters
below `1` carry the trivially valid lower bound `0`. -/
noncomputable def extendL (L : ℝ → ℝ) : ℝ → ℝ := fun u => if u < 1 then 0 else L u

/-- **Jurkat–Richert upper transform** with endpoint `T`:
`s · U_new s = T · U T - ∫_s^T L (t - 1) dt`, with `L` extended by `0` below `1`. -/
noncomputable def jrU (U L : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := fun s =>
  (T * U T - ∫ t in s..T, extendL L (t - 1)) / s

/-- **Jurkat–Richert lower transform** with endpoint `T` (the value `0` is used for `s < 2`,
where the recursion is unavailable; `0` is always a valid lower function). -/
noncomputable def jrL (U L : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := fun s =>
  if s < 2 then 0 else (T * L T - ∫ t in s..T, U (t - 1)) / s

end

end Work.ChenPlan.LinearSieve
