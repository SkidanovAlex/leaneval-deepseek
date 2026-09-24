import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.identity_defs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile

/-!
# The sharp-normalised linear sieve: vocabulary (JR2)

The route to `linear_sieve_v6` fixed by the project lead (message of this session):

1. **`SharpNorm A z ε`** — the *sharp* (constant-excess) product normalisation
   `∏_{w ≤ p < z'}(1 - ν p)⁻¹ ≤ (1+ε)·log z'/log w` for ALL `2 ≤ w < z' ≤ z`.
   This is BJS (arXiv:2207.09452) eq. (2) / Nathanson's `(Ω₂(1,L))` with the *constant* excess
   `ε = L/log w`, which is exactly what their `T_n`-induction (`lemma:expf_n`) consumes.

2. **`LayerSharpBound C ρ`** — the per-layer Rosser–Iwaniec bound under `SharpNorm`:
   `T_n(D,z) ≤ VfR z·(profC (n-1) s + ε·C·ρ^{n-1}·errH s)`, `s = log D/log z`.
   (BJS's `f_n(s) + ε τ_n e² h(s)`, with their `τ_n`-recursion replaced by the simpler
   geometric shape `C ρ^{n-1}`; `Σ_n ρ^{n-1} < ∞` is all the glue needs.)

3. The sharp-normalised sieve bound (`sharp_sieve_upper/lower`), the `Q`-trick reducing the
   v6 contract's hypotheses (with `u₀ = exp(K/ε)`) to `SharpNorm` on the `P/Q`-problem at level
   `D/Q`, and the assembly against `Utab` / `993/1000`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

/-- **The sharp (constant-excess) product normalisation.**  `∏_{w ≤ p < z'}(1 - ν p)⁻¹ ≤
(1+ε)·log z'/log w` for all `2 ≤ w < z' ≤ z` (the range-uniform form of BJS eq. (2)). -/
def SharpNorm (A : BoundingSieve) (z ε : ℝ) : Prop :=
  ∀ w z' : ℝ, 2 ≤ w → w < z' → z' ≤ z →
    (∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - A.nu p)⁻¹)
      ≤ (1 + ε) * (Real.log z' / Real.log w)

/-- `SharpNorm` restricts to sub-limits. -/
theorem SharpNorm.sub {A : BoundingSieve} {z ε : ℝ} (h : SharpNorm A z ε) {z' : ℝ}
    (hz' : z' ≤ z) : SharpNorm A z' ε :=
  fun w z'' hw hlt hle => h w z'' hw hlt (le_trans hle hz')

/-- `VfR A u = VfR A Z · ∏_{u ≤ p < Z}(1 - ν p)⁻¹` for `u ≤ Z`. -/
theorem VfR_eq_mul_prod_inv (A : BoundingSieve) {u Z : ℝ} (huZ : u ≤ Z) :
    VfR A u = VfR A Z *
      ∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < Z), (1 - A.nu p)⁻¹ := by
  set s := A.prodPrimes.primeFactors with hs
  set sZ := s.filter (fun p : ℕ => (p : ℝ) < Z) with hsZ
  set mid := s.filter (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < Z) with hmid
  have h1 : sZ.filter (fun p : ℕ => (p : ℝ) < u) = s.filter (fun p : ℕ => (p : ℝ) < u) := by
    rw [hsZ, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h huZ, h⟩⟩)
  have h2 : sZ.filter (fun p : ℕ => ¬ (p : ℝ) < u) = mid := by
    rw [hsZ, hmid, Finset.filter_filter]
    exact Finset.filter_congr (fun p _ => ⟨fun h => ⟨not_lt.mp h.2, h.1⟩,
      fun h => ⟨h.2, not_lt.mpr h.1⟩⟩)
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := sZ)
    (f := fun p : ℕ => 1 - A.nu p) (p := fun p : ℕ => (p : ℝ) < u)
  rw [h1, h2] at hsplit
  have hVZ : VfR A Z = ∏ p ∈ sZ, (1 - A.nu p) := by
    rw [VfR, hsZ, hs]
  have hVu : VfR A u = ∏ p ∈ s.filter (fun p : ℕ => (p : ℝ) < u), (1 - A.nu p) := by
    rw [VfR, hs]
  have hprodpos : 0 < ∏ p ∈ mid, (1 - A.nu p) := by
    refine Finset.prod_pos (fun p hp => ?_)
    rw [hmid, Finset.mem_filter] at hp
    exact VfR_factor_pos A hp.1
  have hinv : ∏ p ∈ mid, (1 - A.nu p)⁻¹ = (∏ p ∈ mid, (1 - A.nu p))⁻¹ :=
    Finset.prod_inv_distrib _
  rw [hVu, hVZ, ← hsplit, hinv, mul_assoc, mul_inv_cancel₀ (ne_of_gt hprodpos), mul_one]

/-- The normalised product comparison `VfR A u ≤ VfR A Z·((1+ε)·log Z/log u)` from `SharpNorm`
(for `2 ≤ u ≤ Z ≤ z`). -/
theorem VfR_le_of_sharpNorm {A : BoundingSieve} {z ε : ℝ} (hε : 0 ≤ ε)
    (h : SharpNorm A z ε) {u Z : ℝ} (hu : 2 ≤ u) (huZ : u ≤ Z) (hZz : Z ≤ z) :
    VfR A u ≤ VfR A Z * ((1 + ε) * (Real.log Z / Real.log u)) := by
  rcases lt_or_eq_of_le huZ with hlt | heq
  · rw [VfR_eq_mul_prod_inv A huZ]
    exact mul_le_mul_of_nonneg_left (h u Z hu hlt hZz) (le_of_lt (VfR_pos A Z))
  · subst heq
    rw [div_self (ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < u))), mul_one]
    exact le_mul_of_one_le_right (le_of_lt (VfR_pos A u)) (by linarith)

/-- **The per-layer Rosser–Iwaniec bound under the sharp normalisation** (BJS `lemma:expf_n`
with the explicit geometric allowance `ε·C·(n+1)·ρ^{n-1}·errH s`, `Σ_n ρ^n < ∞`). -/
def LayerSharpBound (C ρ : ℝ) : Prop :=
  ∀ {A : BoundingSieve} {ε D z : ℝ}, 0 ≤ ε → ε ≤ 1/100 → 2 ≤ z → 1 ≤ D →
    SharpNorm A z ε →
    ∀ n : ℕ, 1 ≤ n →
      (Odd n → 1 ≤ Real.log D / Real.log z) →
      (Even n → 2 ≤ Real.log D / Real.log z) →
    T A n D z ≤ VfR A z *
      (profC (n - 1) (Real.log D / Real.log z)
        + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH (Real.log D / Real.log z))

/-- **The sharp-normalised sieve, upper form** (the `λ⁺` Rosser–Iwaniec sieve under the constant
excess `ε`): with the error written out as `ε·C₂·errH s`, so that the caller can make it smaller
than any `η` by choosing `ε` small.  No threshold on `D` is needed (only `s ≥ 1`). -/
def SharpSieveUpper (C ρ C₂ : ℝ) : Prop :=
  LayerSharpBound C ρ →
  ∀ (A : BoundingSieve) (ε Z D : ℝ), 0 ≤ ε → ε ≤ 1/100 → 2 ≤ Z → 1 ≤ D →
    SharpNorm A Z ε → 0 ≤ A.totalMass →
    1 ≤ Real.log D / Real.log Z →
    siftedSumR A Z
      ≤ A.totalMass * VfR A Z
        * (1 + riPhi (Real.log D / Real.log Z)
            + ε * C₂ * errH (Real.log D / Real.log Z))
        + Submission.ChenPlan.remSum A D

/-- **The sharp-normalised sieve, lower form** (the `λ⁻` Rosser–Iwaniec sieve under the constant
excess `ε`), for `s ≥ 2` (`D ≥ Z²`, the classical restriction of the lower sieve). -/
def SharpSieveLower (C ρ C₂ : ℝ) : Prop :=
  LayerSharpBound C ρ →
  ∀ (A : BoundingSieve) (ε Z D : ℝ), 0 ≤ ε → ε ≤ 1/100 → 2 ≤ Z → 1 ≤ D →
    SharpNorm A Z ε → 0 ≤ A.totalMass →
    2 ≤ Real.log D / Real.log Z →
    A.totalMass * VfR A Z
        * (1 - riPsi (Real.log D / Real.log Z)
            - ε * C₂ * errH (Real.log D / Real.log Z))
      - Submission.ChenPlan.remSum A D
      ≤ siftedSumR A Z

/-! ## The `Q`-trick vocabulary -/

/-- `Q = ∏_{p ∣ P, p < u₀} p`: the product of the small primes that the `Q`-trick removes from the
sieve. -/
noncomputable def Qmod (A : BoundingSieve) (u₀ : ℝ) : ℕ :=
  ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀), p

theorem Qmod_dvd (A : BoundingSieve) (u₀ : ℝ) : Qmod A u₀ ∣ A.prodPrimes := by
  have h := Finset.prod_dvd_prod_of_subset
    (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀))
    A.prodPrimes.primeFactors (fun p : ℕ => p) (Finset.filter_subset _ _)
  unfold Qmod
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree]
  exact h

/-- The `P/Q` sub-sieve: same support, weights, `totalMass` and `ν`, but the sifting primes
restricted to those above `u₀` (`prodPrimes = P/Q`).  Only `prodPrimes` and `nu` matter for
`RI.Gp`/`RI.Gm`. -/
noncomputable def subSieve (A : BoundingSieve) (Q : ℕ) (hQ : Q ∣ A.prodPrimes) : BoundingSieve where
  support := A.support
  prodPrimes := A.prodPrimes / Q
  prodPrimes_squarefree :=
    Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hQ) A.prodPrimes_squarefree
  weights := A.weights
  weights_nonneg := A.weights_nonneg
  totalMass := A.totalMass
  nu := A.nu
  nu_mult := A.nu_mult
  nu_pos_of_prime := fun p hp hpdvd =>
    A.nu_pos_of_prime p hp (dvd_trans hpdvd (Nat.div_dvd_of_dvd hQ))
  nu_lt_one_of_prime := fun p hp hpdvd =>
    A.nu_lt_one_of_prime p hp (dvd_trans hpdvd (Nat.div_dvd_of_dvd hQ))

/-- **The sharp-normalised `λ⁺` main-term bound** (the `Gp` form of `SharpSieveUpper`), from the
per-layer bound. -/
def SharpGp (C ρ C₂ : ℝ) : Prop :=
  LayerSharpBound C ρ →
  ∀ (A : BoundingSieve) (ε Z D : ℝ), 0 ≤ ε → ε ≤ 1/100 → 2 ≤ Z → 1 ≤ D →
    SharpNorm A Z ε →
    1 ≤ Real.log D / Real.log Z →
    RI.Gp A Z D ≤ VfR A Z * (1 + riPhi (Real.log D / Real.log Z)
      + ε * C₂ * errH (Real.log D / Real.log Z))

/-- **The sharp-normalised `λ⁻` main-term bound** (the `Gm` form of `SharpSieveLower`), from the
per-layer bound. -/
def SharpGm (C ρ C₂ : ℝ) : Prop :=
  LayerSharpBound C ρ →
  ∀ (A : BoundingSieve) (ε Z D : ℝ), 0 ≤ ε → ε ≤ 1/100 → 2 ≤ Z → 1 ≤ D →
    SharpNorm A Z ε →
    2 ≤ Real.log D / Real.log Z →
    VfR A Z * (1 - riPsi (Real.log D / Real.log Z)
      - ε * C₂ * errH (Real.log D / Real.log Z))
      ≤ RI.Gm A Z D

/-! ## The two numerical inputs of the final assembly -/

/-- The sharp Selberg bound for the low parameter range `1/4 ≤ s ≤ 2`
(`JR2/selberg_sharp_low.lean`). -/
def SelbergLow : Prop :=
  ∀ K : ℝ, 0 ≤ K →
    Work.ChenPlan.LinearSieve.UpperValid K
      (fun s : ℝ => 2 * Real.exp Real.eulerMascheroniConstant / s) (1/4) 2

/-- `riUp` and `riPsi` are Lipschitz on `[2, ∞)` (`JR2/riUp_riPsi_lipschitz.lean`). -/
def RiLipschitz : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ C ≤ 100 ∧
    (∀ s t : ℝ, 2 ≤ t → t ≤ s → |riUp t - riUp s| ≤ C * (s - t)) ∧
    (∀ s t : ℝ, 2 ≤ t → t ≤ s → |riPsi t - riPsi s| ≤ C * (s - t))

end

end Work.ChenPlan.LinearSieve.JR2
