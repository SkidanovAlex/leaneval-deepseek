import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Work.BourgainPlan.Maximal.foundations

/-!
# The polynomial Weyl kernel and its major-arc model (the non-monic "pre-interval" form)

The `ℓ²` half of Bourgain's proof for a polynomial `P` of degree `d` with leading coefficient
`c = P.leadingCoeff > 0` runs on the arc decomposition of the torus

* at the `c`-scaled frequency `c·θ`, the arcs are the `a/q + l` with `1 ≤ q ≤ N^δ`, `(a,q) = 1`,
  `l ∈ [-1, c]`, of radius `N^{-(d-δ)}`;
* on such an arc the Weyl kernel is
  `W_{q·c}(a + l·q) · Φ_N(θ − (a/q + l)/c)`, where
  `W_{Q}(b) = Q⁻¹ ∑_{r<Q} e(b P r / Q)` is the complete sum of *modulus* `Q = q·c` and
  `Φ_N(β) = ∫_0^1 e(β P(N s)) ds` is the profile **at the offset** `θ − (a/q + l)/c`.

The modulus `q·c` (rather than `q`) and the profile at the *offset* (rather than at `c·θ`) are the
two features that distinguish the general polynomial from the pure power `X^d`; they are the
"pre-interval (lead-`P`) bookkeeping" of Bourgain (1989), §6, cf. the archived notes
`OLD_NOTES/Submission/Work/Analysis/ExponentialSums/poly_kernel_maximal_lp_STATUS.md`.

This file only records the vocabulary and its elementary bounds; the approximation statements and
the maximal estimates are separate (delegated) lemmas.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

/-- The integer polynomial `P` read as a real polynomial. -/
noncomputable def toRealPoly (P : Polynomial ℤ) : Polynomial ℝ := P.map (Int.castRingHom ℝ)

/-- The **oscillatory profile** of `P` at scale `N`: `Φ_N(β) = ∫_0^1 e(β P(N s)) ds`
(Bourgain's `𝔞_N`). -/
noncomputable def polyProfile (P : Polynomial ℤ) (N : ℕ) (β : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
    ((β * (Polynomial.eval (((N : ℝ) * s)) (toRealPoly P)) : ℝ) : ℂ))

/-- The **complete sum of modulus `Q`** for `P`: `W_Q(b) = Q⁻¹ ∑_{r<Q} e(b P r / Q)`. -/
noncomputable def polyWeight (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) : ℂ :=
  ((Q : ℂ))⁻¹ * ∑ r ∈ Finset.range Q,
    Complex.exp (2 * Real.pi * Complex.I *
      ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))

/-- A single arc term of the model, at the `c`-scaled arc `l + a/q`: the arc condition is
`|c θ − (a/q + l)| ≤ N^{-(d-δ)}` and the value is the complete sum of modulus `q·c` times the
profile at the offset `θ − (a/q + l)/c`. -/
noncomputable def polyModelTermPre (P : Polynomial ℤ) (N q : ℕ) (a : ℕ) (l : ℤ) (θ : ℝ) : ℂ :=
  polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)
    * polyProfile P N (θ - (((a : ℝ) / (q : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ)))

/-- The `q`-th major-arc block of the model of the `P`-kernel (non-monic form). -/
noncomputable def polyMajorArcBlockPre (P : Polynomial ℤ) (δ : ℝ) (N : ℕ) (θ : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q,
    if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        if |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
            ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - δ))
        then polyModelTermPre P N q a l θ else 0
    else 0

/-- The **major-arc model** of the `P`-kernel (non-monic form): `q` ranges over `1 ≤ q ≤ N^δ`. -/
noncomputable def polyMajorArcModelPre (P : Polynomial ℤ) (δ : ℝ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)), polyMajorArcBlockPre P δ N θ q

/-- The **Weyl kernel** of `P`: `N⁻¹ ∑_{n<N} e(θ P(n))`. -/
noncomputable def polyWeylKernel (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
    Complex.exp (2 * Real.pi * Complex.I * (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))

/-- The model multiplier at the dyadic scale `2^k` applied to `g` (sum over its finite support
`s`): the ℓ² maximal function of this family is the content of the model maximal inequality. -/
noncomputable def polyTkMax (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ)/4) (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

/-! ## Elementary bounds -/

/-- The exponential of a real phase has norm one. -/
lemma norm_exp_two_pi_I_mul (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma norm_polyWeight_le_one (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) : ‖polyWeight P Q b‖ ≤ 1 := by
  unfold polyWeight
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp
  · rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (Q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range Q,
          Complex.exp (2 * Real.pi * Complex.I *
            ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))‖
        ≤ (Q : ℝ)⁻¹ * ∑ r ∈ Finset.range Q,
            ‖Complex.exp (2 * Real.pi * Complex.I *
              ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (Q : ℝ)⁻¹ * ∑ _r ∈ Finset.range Q, (1 : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          exact norm_exp_two_pi_I_mul _
      _ = (Q : ℝ)⁻¹ * (Q : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ = 1 := inv_mul_cancel₀ (by positivity : (Q : ℝ) ≠ 0)

lemma norm_polyProfile_le_one (P : Polynomial ℤ) (N : ℕ) (β : ℝ) : ‖polyProfile P N β‖ ≤ 1 := by
  unfold polyProfile
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)) ?_
  simp_rw [norm_exp_two_pi_I_mul]
  simp

/-- The profile at the origin is `1`. -/
lemma polyProfile_zero (P : Polynomial ℤ) (N : ℕ) : polyProfile P N 0 = 1 := by
  unfold polyProfile
  simp

lemma norm_polyModelTermPre_le_one (P : Polynomial ℤ) (N q : ℕ) (a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖polyModelTermPre P N q a l θ‖ ≤ 1 := by
  rw [polyModelTermPre, norm_mul]
  exact mul_le_one₀ (norm_polyWeight_le_one P _ _) (norm_nonneg _) (norm_polyProfile_le_one P N _)

/-- The block is bounded by its number of arc terms, `q · (c + 2)` with `c = lead P`. -/
lemma norm_polyMajorArcBlockPre_le (P : Polynomial ℤ) (δ : ℝ) (N q : ℕ) (θ : ℝ) :
    ‖polyMajorArcBlockPre P δ N θ q‖ ≤ (q : ℝ) * ((P.leadingCoeff + 2).toNat : ℝ) := by
  unfold polyMajorArcBlockPre
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a ∈ Finset.range q,
      ‖(if Nat.gcd a q = 1 then
        ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          if |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
              ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) then polyModelTermPre P N q a l θ else 0
        else 0 : ℂ)‖ ≤ ((P.leadingCoeff + 2).toNat : ℝ) := by
    intro a _
    by_cases hg : Nat.gcd a q = 1
    · rw [if_pos hg]
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            ‖(if |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
                ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) then polyModelTermPre P N q a l θ else 0 : ℂ)‖
          ≤ ∑ _l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro l _
            by_cases h : |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
                ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - δ))
            · rw [if_pos h]; exact norm_polyModelTermPre_le_one P N q a l θ
            · rw [if_neg h]; simp
        _ = ((P.leadingCoeff + 2).toNat : ℝ) := by
            rw [Finset.sum_const]
            have hcard : (Finset.Icc (-1 : ℤ) P.leadingCoeff).card
                = (P.leadingCoeff + 2).toNat := by
              rw [Int.card_Icc]; congr 1; ring
            rw [hcard, nsmul_eq_mul, mul_one]
    · rw [if_neg hg, norm_zero]; positivity
  calc ∑ a ∈ Finset.range q,
        ‖(if Nat.gcd a q = 1 then
          ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            if |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
                ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - δ)) then polyModelTermPre P N q a l θ else 0
          else 0 : ℂ)‖
      ≤ ∑ _a ∈ Finset.range q, ((P.leadingCoeff + 2).toNat : ℝ) := Finset.sum_le_sum hterm
    _ = (q : ℝ) * ((P.leadingCoeff + 2).toNat : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.BourgainPlan.Maximal
