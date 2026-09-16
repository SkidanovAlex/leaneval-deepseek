import Submission.ZagierHoffmanProof.Carlitz
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Anderson–Thakur polynomials (Dac §4.2)

The Anderson–Thakur polynomials `α_n(t) ∈ A[t]` (`A = F[X]`, `q = Nat.card F`) are defined by the
generating series
```
∑_{n ≥ 1} (α_n(t) / Γ_n) x ^ n = x (1 - ∑_{j ≥ 0} (γ_j(t) / D_j) x ^ (q ^ j)) ^ (-1),
```
`γ_0 = 1`, `γ_j(t) = ∏_{ℓ=1}^{j} (θ ^ (q ^ j) - t ^ (q ^ ℓ))`, where `D_j` are the Carlitz
factorials and `Γ_n` the Carlitz arithmetic `Γ`-function (`Submission.ZagierHoffmanProof.Carlitz`).

We work in the fraction field of the polynomial ring `A[t] = (F[X])[X]`, which contains both `θ`
(the image of `X ∈ F[X]`) and the independent variable `t`; the generating identity is replaced by
the coefficient recursion `c_0 = 1`, `c_n = ∑_{j : q^j ≤ n} (γ_j/D_j) c_{n-q^j}`, so that
`α_n = Γ_n * c_{n-1}`.

The main result here is the easy range of the classical fact `α_n = 1` for `1 ≤ n ≤ q`; the
arithmetic content (the integrality `α_n ∈ A[t]` for all `n`, Dac `[3, (3.7.3)]`) is the next step.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

section AT

/-- The ambient field `F(θ, t)`, realised as the fraction field of `A[t] = (F[X])[X]`. -/
noncomputable abbrev atQ (F : Type*) [Field F] [Finite F] :=
  FractionRing ((F[X])[X])

/-- `θ` in the two-variable field. -/
noncomputable def atTheta : atQ F :=
  algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (Polynomial.X : F[X]))

/-- The variable `t` in the two-variable field. -/
noncomputable def atT : atQ F := algebraMap ((F[X])[X]) (atQ F) Polynomial.X

/-- `γ_j(t) = ∏_{ℓ=1}^{j} (θ ^ (q^j) - t ^ (q^ℓ))` (with `γ_0 = 1`). -/
noncomputable def atGamma (j : ℕ) : atQ F :=
  ∏ l ∈ Finset.Icc 1 j, ((atTheta F) ^ (Nat.card F ^ j) - (atT F) ^ (Nat.card F ^ l))

@[simp]
lemma atGamma_zero : atGamma F 0 = 1 := by
  rw [atGamma]
  simp

/-- `D_j ∈ A` viewed in the two-variable field. -/
noncomputable def atD (j : ℕ) : atQ F :=
  algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzFact F j))

lemma atD_ne_zero (j : ℕ) : atD F j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective ((F[X])[X]) (atQ F))).mpr
    (Polynomial.C_ne_zero.mpr (carlitzFact_ne_zero F j))

/-- The coefficient sequence of the Anderson–Thakur generating series:
`c_0 = 1`, `c_n = ∑_{j : q^j ≤ n} (γ_j / D_j) c_{n - q^j}`. -/
noncomputable def atCoeff (n : ℕ) : atQ F :=
  Nat.strongRecOn n fun m ih =>
    if hm : m = 0 then 1 else
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m),
        (atGamma F j) * (atD F j)⁻¹ * ih (m - Nat.card F ^ j) (by
          have h1 : 0 < Nat.card F ^ j := pow_pos (by have := carlitz_card_ge_two F; omega) j
          exact Nat.sub_lt (Nat.pos_of_ne_zero hm) h1)

lemma atCoeff_zero : atCoeff F 0 = 1 := by
  rw [atCoeff, Nat.strongRecOn_eq]
  simp

/-- The Anderson–Thakur polynomial `α_n = Γ_n * c_{n-1}`. -/
noncomputable def atAlpha (n : ℕ) : atQ F :=
  algebraMap ((F[X])[X]) (atQ F) (Polynomial.C (carlitzGamma F n)) * atCoeff F (n - 1)

lemma pow_card_le_pow {j : ℕ} (hj : 1 ≤ j) : Nat.card F ≤ Nat.card F ^ j := by
  have h := Nat.pow_le_pow_right (by have := carlitz_card_ge_two F; omega : 1 ≤ Nat.card F) hj
  simpa using h

/-- `Γ_n = 1` for `n ≤ q`. -/
lemma carlitzGamma_eq_one_of_le {n : ℕ} (hn : n ≤ Nat.card F) : carlitzGamma F n = 1 := by
  rw [carlitzGamma]
  refine Finset.prod_eq_one fun j hj => ?_
  rw [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [carlitzFact_zero]
    simp
  · have h1 : Nat.card F ≤ Nat.card F ^ j := pow_card_le_pow F h
    have h2 : (n - 1) / Nat.card F ^ j = 0 := Nat.div_eq_of_lt (by omega)
    rw [h2, Nat.zero_mod, pow_zero]

/-- The recursion for the Anderson–Thakur coefficients, in terms of `atCoeff` itself. -/
lemma atCoeff_succ {m : ℕ} (hm : m ≠ 0) :
    atCoeff F m
      = ∑ j ∈ (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m),
          (atGamma F j) * (atD F j)⁻¹ * atCoeff F (m - Nat.card F ^ j) := by
  conv_lhs => rw [atCoeff, Nat.strongRecOn_eq]
  simp only [dif_neg hm]
  rfl

/-- `c_n = 1` for `n < q`. -/
lemma atCoeff_eq_one_of_lt {n : ℕ} (hn : n < Nat.card F) : atCoeff F n = 1 := by
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact atCoeff_zero F
    · rw [atCoeff_succ F (Nat.pos_iff_ne_zero.mp h)]
      have hs : (Finset.range (m + 1)).filter (fun j => Nat.card F ^ j ≤ m) = {0} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.succ_pos m, by rw [pow_zero]; omega⟩
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_range] at hj
          by_contra h0
          have h1 : Nat.card F ≤ Nat.card F ^ j :=
            pow_card_le_pow F (Nat.one_le_iff_ne_zero.mpr h0)
          omega
      rw [hs, Finset.sum_singleton, atGamma_zero, Nat.pow_zero]
      simp only [atD, carlitzFact_zero, map_one, inv_one, mul_one, one_mul]
      exact ih (m - 1) (Nat.sub_lt h Nat.one_pos) (by omega)

/-- ★ `α_n = 1` for `1 ≤ n ≤ q` (the classical easy range of the Anderson–Thakur polynomials). -/
theorem atAlpha_eq_one_of_le {n : ℕ} (h1 : 1 ≤ n) (hn : n ≤ Nat.card F) : atAlpha F n = 1 := by
  rw [atAlpha, carlitzGamma_eq_one_of_le F hn, atCoeff_eq_one_of_lt F (by omega)]
  simp

end AT

end ZagierHoffmanPositiveChar
