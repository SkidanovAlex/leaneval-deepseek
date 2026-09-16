import Mathlib.RingTheory.LaurentSeries
import Submission.ZagierHoffmanProof.Carlitz
import Submission.ZagierHoffmanProof.LSeries
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup

/-!
# The Kummer field carrying the Anderson–Thakur period constant

The period function of Anderson–Thakur is
`Ω = (-θ)^{-q/(q-1)}·∏_{i≥1}(1 - t/θ^{q^i})`; the normalising constant `μ = (-θ)^{-q/(q-1)}`
satisfies `μ^{q-1} = -θ^{-q}` and *does not* lie in `K∞ = F((1/θ))`.  The purpose of this file is
to record that Mathlib already contains a field in which both `θ` and `μ` live, together with a
complete `ℤᵐ⁰`-valued valuation: the field `L = F((y))` of Laurent series (`LaurentSeries F`), with

  `θ := -y^{-(q-1)}`,  `μ := y^q`.

Indeed the `y`-adic valuation has `v θ = exp (q-1)` and `v μ = exp (-q)`, and

  `μ^{q-1} = y^{q(q-1)} = -θ^{-q}`

(here `-θ^{-q} = (-1)^{-q}y^{q(q-1)} = ±y^{q(q-1)}`, and the sign works out in every
characteristic: in characteristic `2`, `-1 = 1`; otherwise `q` is odd and `-(-1)^q = 1`).

`L` is the Kummer extension `K∞(θ^{1/(q-1)})` of `K∞` (totally ramified of degree `q-1`) times the
constant field extension `F_{q^2}/F_q` needed for the `(q-1)`-st root of `-1` in general; but with
the choice `θ = -y^{-(q-1)}` no constant extension is needed at all, because
`-θ^{-q} = y^{q(q-1)}` is already a `(q-1)`-st power (namely `μ^{q-1}`).

The accompanying `Valued` and `CompleteSpace` instances (both from Mathlib) mean that the whole
`Ω`/`ε`/`L`-series development applies over `L`, **provided** the `θ`-dependent lemmas are
generalised from `v θ = exp 1` to `v θ = exp d` (`d = q-1` here).  That generalisation is the
recorded next step; see `PLAN.md` SESSION 302 LOG §4.

## Main results

* `kummerTheta`, `kummerMu`, `kummerY` — the elements `θ`, `μ`, `y` of `F((y))`.
* `v_kummerTheta`, `v_kummerMu` — their valuations.
* `kummerMu_pow_eq_neg_theta_inv` — `μ^{q-1} = -(θ^q)⁻¹` (the period-constant relation).
* `neg_one_pow_card` — `(-1)^q = -1`.
* `isSmall_kummerMu` — `v μ ≤ exp (-1)`, i.e. `μ` is "small" (so `Ω` is a Tate series).
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology
open LaurentSeries HahnSeries

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The cardinality of a finite field is at least one. -/
lemma card_pos_le (F : Type*) [Field F] [Finite F] : 1 ≤ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos

/-- **Sign lemma**: `(-1)^q = -1` for `q = Nat.card F` the cardinality of a finite field. -/
lemma neg_one_pow_card_field : ((-1 : F) ^ Nat.card F) = -1 := by
  by_cases h2 : ringChar F = 2
  · have h : (-1 : F) = 1 := neg_one_eq_one_iff.mpr h2
    rw [h, one_pow, ← h]
  · obtain ⟨n, hprime, hn⟩ := card_eq_ringChar_pow F
    rw [hn]
    exact Odd.neg_one_pow (Odd.pow (hprime.odd_of_ne_two h2))

section elements

/-- The uniformiser `y ∈ F((y))`. -/
noncomputable def kummerY : LaurentSeries F := HahnSeries.single 1 (1 : F)

/-- `θ := -y^{-(q-1)}` — the element of `F((y))` playing the role of `θ = X` in `K∞`. -/
noncomputable def kummerTheta : LaurentSeries F :=
  HahnSeries.single (-(((Nat.card F - 1 : ℕ)) : ℤ)) (-1 : F)

/-- `μ := y^q` — the period constant: `μ^{q-1} = -θ^{-q}`. -/
noncomputable def kummerMu : LaurentSeries F := HahnSeries.single ((Nat.card F : ℕ) : ℤ) (1 : F)

lemma kummerY_pow (F : Type*) [Field F] [Finite F] (n : ℕ) :
    kummerY F ^ n = HahnSeries.single (n : ℤ) (1 : F) := by
  rw [kummerY, HahnSeries.single_pow]
  simp

lemma kummerMu_eq (F : Type*) [Field F] [Finite F] :
    kummerMu F = kummerY F ^ Nat.card F := by
  rw [kummerMu, kummerY_pow]

lemma kummerTheta_eq (F : Type*) [Field F] [Finite F] :
    kummerTheta F
      = -(HahnSeries.single (-(((Nat.card F - 1 : ℕ)) : ℤ)) (1 : F) : LaurentSeries F) := by
  rw [kummerTheta, ← HahnSeries.single_neg]

/-- The valuation of `θ`.  Note the exponent `q-1` (not `1` as for `X ∈ K∞`). -/
lemma v_kummerTheta : Valued.v (kummerTheta F) = WithZero.exp (((Nat.card F : ℕ) : ℤ) - 1) := by
  have hcast : ((((Nat.card F - 1 : ℕ)) : ℤ)) = ((Nat.card F : ℕ) : ℤ) - 1 := by
    have h1 : 1 ≤ Nat.card F := card_pos_le F
    push_cast [Nat.cast_sub h1]
    ring
  rw [kummerTheta, hcast, HahnSeries.single_neg, Valuation.map_neg,
    LaurentSeries.valuation_single_zpow]
  congr 1
  ring

/-- The valuation of the period constant `μ = y^q`. -/
lemma v_kummerMu : Valued.v (kummerMu F) = WithZero.exp (-((Nat.card F : ℕ) : ℤ)) := by
  rw [kummerMu, LaurentSeries.valuation_single_zpow]

/-- `μ` is "small": its valuation is `≤ exp (-1)`.  This is the convergence condition for the
`L`-series over `L`. -/
lemma v_kummerMu_le_one : Valued.v (kummerMu F) ≤ WithZero.exp (-1) := by
  rw [v_kummerMu]
  refine WithZero.exp_le_exp.mpr ?_
  have h : 1 ≤ Nat.card F := card_pos_le F
  have : (1 : ℤ) ≤ ((Nat.card F : ℕ) : ℤ) := by exact_mod_cast h
  omega

/-- **The period-constant relation** `μ^{q-1} · θ^q = -1`. -/
theorem kummerMu_pow_mul_theta_pow :
    kummerMu F ^ (Nat.card F - 1) * kummerTheta F ^ Nat.card F = -1 := by
  have h1 : 1 ≤ Nat.card F := card_pos_le F
  have hsign : ((-1 : F) ^ Nat.card F) = -1 := neg_one_pow_card_field F
  simp only [kummerMu, kummerTheta, HahnSeries.single_pow, nsmul_eq_mul, one_pow, hsign,
    HahnSeries.single_mul_single]
  have hexp : (((Nat.card F - 1 : ℕ)) : ℤ) * ((Nat.card F : ℕ) : ℤ)
      + ((Nat.card F : ℕ) : ℤ) * (-(((Nat.card F - 1 : ℕ)) : ℤ)) = 0 := by
    push_cast [Nat.cast_sub h1]
    ring
  rw [show ((Nat.card F - 1 : ℕ) : ℤ) * ((Nat.card F : ℕ) : ℤ)
        + ((Nat.card F : ℕ) : ℤ) * (-(((Nat.card F - 1 : ℕ)) : ℤ))
      = (0 : ℤ) from hexp]
  simp [HahnSeries.single_neg, HahnSeries.single_zero_one]

/-- **The period-constant relation** `μ^{q-1} = -(θ^q)⁻¹`, equivalently `μ^{q-1} = -θ^{-q}`. -/
theorem kummerMu_pow_eq_neg_theta_inv :
    kummerMu F ^ (Nat.card F - 1) = -(kummerTheta F ^ Nat.card F)⁻¹ := by
  have h := kummerMu_pow_mul_theta_pow F
  have hne : kummerTheta F ^ Nat.card F ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact absurd h (by norm_num)
  calc kummerMu F ^ (Nat.card F - 1)
      = kummerMu F ^ (Nat.card F - 1)
          * (kummerTheta F ^ Nat.card F * (kummerTheta F ^ Nat.card F)⁻¹) := by
        rw [mul_inv_cancel₀ hne, mul_one]
    _ = (kummerMu F ^ (Nat.card F - 1) * kummerTheta F ^ Nat.card F)
          * (kummerTheta F ^ Nat.card F)⁻¹ := by ring
    _ = -1 * (kummerTheta F ^ Nat.card F)⁻¹ := by rw [h]
    _ = -(kummerTheta F ^ Nat.card F)⁻¹ := by ring

end elements

end ZagierHoffmanPositiveChar
