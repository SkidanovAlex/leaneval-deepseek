import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.FwVec4Prime2` — the quartic `f̂₄ = fwVec a b h 4` is irreducible

`fwVec a b h 4 = f̂₄` is the fourth component of the forward link map
`f = kleinTwP ∘ kleinTwStereo (p, ·)` of the `T`-twisted Crauder--Katz link on the affine chart
`chart3 = ![0, x₀, x₁, x₂, 1]`, at the `K`-rational point `p = kleinPointT a b h`.  Geometrically
`{f̂₄ = 0} = f^{-1}({w₄ = 0})` is the preimage of the hyperplane at infinity of the target chart.

The purpose of this file is to prove that `f̂₄` is **irreducible** for all `a b h ≠ 0` and all
fields `K` (no characteristic restriction).  This is the missing input `hirr` of
`Work.MotK.TGen.FwVec4KerEq`, hence of the census statement `Work.MotK.TGen.FwVec4Rational`.

## The explicit normal form

`kleinTwStereo` is linear in its first argument and `kleinTwP4` is quadratic in its argument, so the
division `b/(a·h)` occurring in `kleinPointT` can be cleared.  Writing
`fwPointS a b h = (a·h, 0, a·h, b, 0) = (a·h) • kleinPointT a b h` one has

* `fwVec a b h 4 = (a·h)⁻² · fwP4S a b h`,  `fwP4S a b h = kleinTwP4 (stereo (fwPointS) chart3)`,
* `fwP4S a b h = C (a·h³) · fwG a b h`   (`fwG` explicit, division-free),
* `C a · fwVec a b h 4 = C h · fwG a b h`.

`fwG` is a *cubic in `x₁`* whose leading coefficient is `-C (a³b⁴)`, a unit; transporting along the
variable identification `tau3 : K[x₀,x₁,x₂] ≃ K[x₀,x₂][X]` (`x₁ ↦ X`) gives the cubic
`fwGp a b h = -C(a³b⁴)·X³ + C(β₂)·X² + C(β₁)·X + C(β₀)`.

## The proof of irreducibility

We show that `fwGp a b h` has no root `r ∈ K[x₀,x₂]`; then `fwGp` is irreducible (a cubic over a
domain with unit leading coefficient admitting a proper factorisation would have a root), and
irreducibility is transported back along `tau3`.

The root equation `-(C c₀)·r³ + β₂·r² + β₁·r + β₀ = 0` (`c₀ = a³b⁴`) is impossible by a degree
argument in the variable `x₂`: with `e = (r).degreeOf 1` and the coefficient data

* `degreeOf 1 β₂ ≤ 1`,  `degreeOf 1 β₁ ≤ 2`,  `degreeOf 1 β₀ = 4`,

the term `r³` dominates (`3e > 1 + 2e`, `> 2 + e`, `> 4` for `e ≥ 2`) unless `e ≤ 1`, in which case
the `x₂⁴`-term of `β₀` survives — the terms `r³`, `β₂r²`, `β₁r` all have `x₂`-degree at most `3`.
This works in every characteristic.

The only external inputs are the definitions of the twisted link data (`KleinTwData`, `LinkTwData`,
`TwAmbh`, ... ) together with `ChartDefs`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MvPolynomial

namespace Work.MotK.TGen

/-! ## 1.  Clearing the denominators of `kleinPointT` -/

/-- The `(a·h)`-multiple `(a·h, 0, a·h, b, 0)` of the `K`-rational point `kleinPointT a b h`; it
clears the denominator `a·h` of the third coordinate. -/
noncomputable def fwPointS {K : Type} [Field K] (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K
  | 0 => MvPolynomial.C (a * h)
  | 1 => 0
  | 2 => MvPolynomial.C (a * h)
  | 3 => MvPolynomial.C b
  | 4 => 0

/-- The polar form `kleinTwBilin` of the T-invariant quadric is linear in its first argument. -/
theorem kleinTwBilin_smul_left {R : Type*} [CommRing R] (a b h c : R) (u v : Fin 5 → R) :
    kleinTwBilin a b h (c • u) v = c * kleinTwBilin a b h u v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply, Pi.smul_apply]
  first | refl_ring1 | ring

/-- The twisted inverse stereographic projection is linear in its first (the point) argument. -/
theorem kleinTwStereo_smul_left {R : Type*} [CommRing R] (a b h c : R) (p v : Fin 5 → R) :
    kleinTwStereo a b h (c • p) v = c • kleinTwStereo a b h p v := by
  funext i
  simp only [kleinTwStereo, Pi.smul_apply, kleinTwBilin_smul_left]
  first | refl_ring1 | ring

/-- The twisted Pfaffian `p₄` is homogeneous of degree two in its argument. -/
theorem kleinTwP4_smul {R : Type*} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    kleinTwP4 a b h (c • y) = c ^(2:ℕ) * kleinTwP4 a b h y := by
  simp only [kleinTwP4, Pi.smul_apply]
  first | refl_ring1 | ring

/-- `kleinPointT a b h` is the `(a·h)⁻¹`-multiple of the integral point `fwPointS a b h`. -/
theorem pRa_eq_smul_fwPointS {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    pRa a b h = (MvPolynomial.C ((a * h)⁻¹) : MvPolynomial (Fin 3) K) • fwPointS a b h := by
  have hne : a * h ≠ 0 := mul_ne_zero ha hh
  funext i
  fin_cases i
  · simp only [fwPointS, pRa, kleinPointT, Pi.smul_apply, smul_eq_mul]
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · simp only [fwPointS, pRa, kleinPointT, Pi.smul_apply, smul_eq_mul, mul_zero, map_zero]
  · simp only [fwPointS, pRa, kleinPointT, Pi.smul_apply, smul_eq_mul]
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · simp only [fwPointS, pRa, kleinPointT, Pi.smul_apply, smul_eq_mul]
    rw [← map_mul]; congr 1; rw [div_eq_mul_inv, mul_comm]
  · simp only [fwPointS, pRa, kleinPointT, Pi.smul_apply, smul_eq_mul, mul_zero, map_zero]

/-! ## 2.  The explicit normal form of `f̂₄` -/

/-- The (division-free) `f̂₄`-numerator `kleinTwP4 (stereo (fwPointS) chart3)`. -/
noncomputable def fwP4S {K : Type} [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwP4 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (fwPointS a b h)
      (chart3 K))

/-- `f̂₄ = (a·h)⁻² · fwP4S`, i.e. clearing the denominator of `kleinPointT`. -/
theorem fwVec_four_eq {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    fwVec a b h 4 = (MvPolynomial.C ((a * h)⁻¹)) ^(2:ℕ) * fwP4S a b h := by
  have h4 : fwVec a b h 4 = kleinTwP4 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
        (chart3 K)) := rfl
  rw [h4, pRa_eq_smul_fwPointS a b h ha hh, kleinTwStereo_smul_left, kleinTwP4_smul]
  rfl

/-- The explicit quartic `fwG` with `fwP4S a b h = C (a·h³) · fwG a b h`; it is a cubic in `X 1`
with coefficients in `K[x₀,x₂]`, and `a · f̂₄ = h · fwG`. -/
noncomputable def fwG {K : Type} [Field K] (a b h : K) : MvPolynomial (Fin 3) K :=
  - MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ)) * MvPolynomial.X 1 ^(3:ℕ)
  + (-MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X 0 * MvPolynomial.X 2
      - MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ) * h) * MvPolynomial.X 2) * MvPolynomial.X 1 ^(2:ℕ)
  + (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ)) * MvPolynomial.X 0 ^(2:ℕ)
      - MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X 0 * MvPolynomial.X 2 ^(2:ℕ)
      - MvPolynomial.C (a ^(2:ℕ) * b ^(5:ℕ) * h) * MvPolynomial.X 0) * MvPolynomial.X 1
  + (-(MvPolynomial.C (a ^(6:ℕ) * b * h ^(2:ℕ)) * MvPolynomial.X 2 ^(4:ℕ))
      + (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X 2 * MvPolynomial.X 0 ^(2:ℕ)
        - MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X 0 ^(2:ℕ)
        - MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X 2 * MvPolynomial.X 0
        - 2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X 2 ^(2:ℕ) * MvPolynomial.X 0))

/-- `fwP4S a b h = C (a·h³) · fwG a b h` (a pure polynomial identity). -/
theorem fwP4S_eq {K : Type} [Field K] (a b h : K) :
    fwP4S a b h = MvPolynomial.C (a * h ^(3:ℕ)) * fwG a b h := by
  simp only [fwP4S, fwPointS, fwG, kleinTwP4, kleinTwStereo, kleinTwQ, kleinTwP0, kleinTwBilin,
    chart3, Pi.add_apply]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_succ]
  first | refl_ring1 | ring

/-- **The normal form of `f̂₄`**: `C a · f̂₄ = C h · fwG`. -/
theorem Ca_fwVec_four {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    MvPolynomial.C a * fwVec a b h 4 = MvPolynomial.C h * fwG a b h := by
  have hne : a * h ^(2:ℕ) ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hh)
  have h1 : (MvPolynomial.C (a * h)) ^(2:ℕ) * fwVec a b h 4 = fwP4S a b h := by
    rw [fwVec_four_eq a b h ha hh, ← mul_assoc, ← mul_pow,
      show MvPolynomial.C (a * h) * MvPolynomial.C ((a * h)⁻¹) = 1 from by
        rw [← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hh), map_one],
      one_pow, one_mul]
  have h3 : (MvPolynomial.C (a * h)) ^(2:ℕ) * fwVec a b h 4 =
      MvPolynomial.C (a * h ^(3:ℕ)) * fwG a b h := h1.trans (fwP4S_eq a b h)
  have hCa : (MvPolynomial.C (a * h ^(2:ℕ)) : MvPolynomial (Fin 3) K) * MvPolynomial.C a =
      (MvPolynomial.C (a * h)) ^(2:ℕ) := by
    rw [← map_mul, ← map_pow]; congr 1; ring
  have hCh : (MvPolynomial.C (a * h ^(2:ℕ)) : MvPolynomial (Fin 3) K) * MvPolynomial.C h =
      MvPolynomial.C (a * h ^(3:ℕ)) := by
    rw [← map_mul]; congr 1; ring
  have hmain : (MvPolynomial.C (a * h ^(2:ℕ)) : MvPolynomial (Fin 3) K)
        * (MvPolynomial.C a * fwVec a b h 4) =
      (MvPolynomial.C (a * h ^(2:ℕ)) : MvPolynomial (Fin 3) K)
        * (MvPolynomial.C h * fwG a b h) := by
    rw [← mul_assoc, ← mul_assoc, hCa, hCh]
    exact h3
  exact mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hne) hmain

/-! ## 3.  The `x₂`-graded coefficients of `fwG` -/

/-- The coefficient of `X 1 ^ 2` in `fwG` (as a polynomial in `X 0` and `X 2`). -/
noncomputable def fwBeta2 {K : Type} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  -MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1
    - MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2)

/-- The coefficient of `X 1` in `fwG`. -/
noncomputable def fwBeta1 {K : Type} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
    - MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 ^(2:ℕ)
    - MvPolynomial.C (a ^(2:ℕ) * b ^(5:ℕ) * h) * MvPolynomial.X (0 : Fin 2)

/-- The constant coefficient of `fwG`; its `X 2`-degree is `4`. -/
noncomputable def fwBeta0 {K : Type} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  -(MvPolynomial.C (a ^(6:ℕ) * b * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2) ^(4:ℕ))
  + (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      - MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      - MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2)
      - 2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)
        * MvPolynomial.X (0 : Fin 2))

theorem degreeOf_fwBeta2 {K : Type} [Field K] (a b h : K) : (fwBeta2 a b h).degreeOf 1 ≤ 1 := by
  have hA : (-MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 1 := by
    rw [show (-MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)
        = (-(MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2))) * MvPolynomial.X 1
        from by ring]
    calc _ ≤ (-(MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2)) :
            MvPolynomial (Fin 2) K).degreeOf 1 + 1 := MvPolynomial.degreeOf_mul_X_self 1 _
      _ ≤ 1 := by
          have : (-(MvPolynomial.C (a ^(6:ℕ) * b) * MvPolynomial.X (0 : Fin 2)) :
              MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 := by
            rw [MvPolynomial.degreeOf_neg]
            refine (MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X (0 : Fin 2)) 1 (a ^(6:ℕ) * b)).trans ?_
            rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
          omega
  have hB : (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ) * h) * MvPolynomial.X (1 : Fin 2) :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 1 := by
    calc _ ≤ (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ) * h) :
            MvPolynomial (Fin 2) K).degreeOf 1 + (MvPolynomial.X (1 : Fin 2)).degreeOf 1 :=
          MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 1 := by rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self]
  rw [fwBeta2]
  exact (MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le hA hB)

theorem degreeOf_fwBeta1 {K : Type} [Field K] (a b h : K) : (fwBeta1 a b h).degreeOf 1 ≤ 2 := by
  have h1 : (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    calc _ ≤ (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ)) :
            MvPolynomial (Fin 2) K).degreeOf 1 + (MvPolynomial.X (0 : Fin 2) ^(2:ℕ)).degreeOf 1 :=
          MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 2 := by
          rw [MvPolynomial.degreeOf_C,
            MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 2) ≠ 0)]
          norm_num
  have h2 : (MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 ^(2:ℕ) :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    calc _ ≤ (MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X (0 : Fin 2) :
            MvPolynomial (Fin 2) K).degreeOf 1 + (MvPolynomial.X (1 : Fin 2) ^(2:ℕ)).degreeOf 1 :=
          MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 2 := by
          have : (MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X (0 : Fin 2) :
              MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 := by
            refine (MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X (0 : Fin 2)) 1 (a ^(7:ℕ) * h)).trans ?_
            rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
          rw [MvPolynomial.degreeOf_X_self_pow]
          omega
  have h3 : (MvPolynomial.C (a ^(2:ℕ) * b ^(5:ℕ) * h) * MvPolynomial.X (0 : Fin 2) :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    calc _ ≤ (MvPolynomial.C (a ^(2:ℕ) * b ^(5:ℕ) * h) :
            MvPolynomial (Fin 2) K).degreeOf 1 + (MvPolynomial.X (0 : Fin 2)).degreeOf 1 :=
          MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 2 := by
          rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
          norm_num
  rw [fwBeta1]
  have h4 : (MvPolynomial.C (a ^(4:ℕ) * b ^(3:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      - MvPolynomial.C (a ^(7:ℕ) * h) * MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 ^(2:ℕ) :
        MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 :=
    (MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le h1 h2)
  exact (MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le h4 h3)

theorem degreeOf_fwBeta0 {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) : (fwBeta0 a b h).degreeOf 1 = 4 := by
  have hc : (MvPolynomial.C (a ^(6:ℕ) * b * h ^(2:ℕ)) : MvPolynomial (Fin 2) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha) hb) (pow_ne_zero 2 hh))
  have hlead : (-(MvPolynomial.C (a ^(6:ℕ) * b * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2) ^(4:ℕ)) :
      MvPolynomial (Fin 2) K).degreeOf 1 = 4 := by
    rw [MvPolynomial.degreeOf_neg,
      MvPolynomial.degreeOf_mul_eq hc (pow_ne_zero 4 (MvPolynomial.X_ne_zero 1)),
      MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow]
  have hA : (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2)
      * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) : MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    rw [show (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) : MvPolynomial (Fin 2) K)
        = (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ))
          * MvPolynomial.X 1 from by ring]
    calc _ ≤ (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
            MvPolynomial (Fin 2) K).degreeOf 1 + 1 := MvPolynomial.degreeOf_mul_X_self 1 _
      _ ≤ 2 := by
          have : (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
              MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 := by
            calc _ ≤ (MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) :
                    MvPolynomial (Fin 2) K).degreeOf 1
                  + (MvPolynomial.X (0 : Fin 2) ^(2:ℕ)).degreeOf 1 :=
                  MvPolynomial.degreeOf_mul_le 1 _ _
              _ ≤ 0 := by
                  rw [MvPolynomial.degreeOf_C,
                    MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 2) ≠ 0)]
          omega
  have hB : (MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
      MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    calc _ ≤ (MvPolynomial.C (b ^(7:ℕ)) : MvPolynomial (Fin 2) K).degreeOf 1
            + (MvPolynomial.X (0 : Fin 2) ^(2:ℕ)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 2 := by
          rw [MvPolynomial.degreeOf_C,
            MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 2) ≠ 0)]
          norm_num
  have hCv : (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2)
      * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    rw [show (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
        = (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (0 : Fin 2))
          * MvPolynomial.X 1 from by ring]
    calc _ ≤ (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (0 : Fin 2) :
            MvPolynomial (Fin 2) K).degreeOf 1 + 1 := MvPolynomial.degreeOf_mul_X_self 1 _
      _ ≤ 2 := by
          have : (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (0 : Fin 2) :
              MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 := by
            calc _ ≤ (MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) :
                    MvPolynomial (Fin 2) K).degreeOf 1
                  + (MvPolynomial.X (0 : Fin 2)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
              _ ≤ 0 := by
                  rw [MvPolynomial.degreeOf_C,
                    MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
          omega
  have hD : (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)
      * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K).degreeOf 1 ≤ 2 := by
    rw [show (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)
        * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
        = (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (0 : Fin 2))
          * MvPolynomial.X 1 ^(2:ℕ) from by ring]
    calc _ ≤ (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (0 : Fin 2) :
            MvPolynomial (Fin 2) K).degreeOf 1
            + (MvPolynomial.X (1 : Fin 2) ^(2:ℕ)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
      _ ≤ 2 := by
          have hcoef : (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (0 : Fin 2) :
              MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 := by
            calc _ ≤ (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) :
                    MvPolynomial (Fin 2) K).degreeOf 1
                  + (MvPolynomial.X (0 : Fin 2)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
              _ ≤ 0 := by
                  rw [MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 2) ≠ 0)]
                  have h2c : (2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) :
                      MvPolynomial (Fin 2) K).degreeOf 1 = 0 := by
                    rw [show (2 : MvPolynomial (Fin 2) K) = MvPolynomial.C 2 from rfl, ← map_mul]
                    exact MvPolynomial.degreeOf_C _ _
                  omega
          rw [MvPolynomial.degreeOf_X_self_pow]
          omega
  have hrest : ((MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2)
      * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      - MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
      - MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2)
      - 2 * MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h) * MvPolynomial.X (1 : Fin 2) ^(2:ℕ)
        * MvPolynomial.X (0 : Fin 2)) : MvPolynomial (Fin 2) K).degreeOf 1 <
      (-(MvPolynomial.C (a ^(6:ℕ) * b * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2) ^(4:ℕ)) :
        MvPolynomial (Fin 2) K).degreeOf 1 := by
    rw [hlead]
    have h1 : ((MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
        - MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ) :
          MvPolynomial (Fin 2) K)).degreeOf 1 ≤ 2 :=
      (MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le hA hB)
    have h2 : ((MvPolynomial.C (a ^(5:ℕ) * b ^(2:ℕ) * h) * MvPolynomial.X (1 : Fin 2)
        * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
        - MvPolynomial.C (b ^(7:ℕ)) * MvPolynomial.X (0 : Fin 2) ^(2:ℕ)
        - MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ)) * MvPolynomial.X (1 : Fin 2)
          * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)).degreeOf 1 ≤ 2 :=
      (MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le h1 hCv)
    exact lt_of_le_of_lt ((MvPolynomial.degreeOf_sub_le 1 _ _).trans (max_le h2 hD)) (by norm_num)
  rw [fwBeta0, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hrest, hlead]

/-! ## 4.  The no-root argument -/

/-- **A cubic with unit leading coefficient over a domain, satisfying the `x₂`-degree bounds
`≤ 1`, `≤ 2`, `= 4`, has no root.**  The term `r³` dominates unless `(r).degreeOf 1 ≤ 1`, in which
case the `x₂⁴`-term of `B0` survives. -/
theorem no_root_aux {K : Type} [Field K] (c : K) (hc : c ≠ 0)
    (B2 B1 B0 : MvPolynomial (Fin 2) K)
    (h2 : B2.degreeOf 1 ≤ 1) (h1 : B1.degreeOf 1 ≤ 2) (h0 : B0.degreeOf 1 = 4) :
    ∀ r : MvPolynomial (Fin 2) K,
      -(MvPolynomial.C c * r ^(3:ℕ)) + B2 * r ^(2:ℕ) + B1 * r + B0 ≠ 0 := by
  intro r hE
  have hCc : (MvPolynomial.C c : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.C_ne_zero.mpr hc
  rcases eq_or_ne r 0 with rfl | hr
  · have hB0 : B0 = 0 := by simpa using hE
    have : B0.degreeOf 1 = 0 := by rw [hB0, MvPolynomial.degreeOf_zero]
    omega
  · have hpow3 : (r ^(3:ℕ)).degreeOf 1 = 3 * r.degreeOf 1 := by
      rw [MvPolynomial.degreeOf_pow_eq 1 r 3 hr, mul_comm]
    have hCc3 : (MvPolynomial.C c * r ^(3:ℕ)).degreeOf 1 = 3 * r.degreeOf 1 := by
      rw [MvPolynomial.degreeOf_mul_eq hCc (pow_ne_zero 3 hr), MvPolynomial.degreeOf_C, zero_add,
        hpow3]
    have hpow2 : (r ^(2:ℕ)).degreeOf 1 = 2 * r.degreeOf 1 := by
      rw [MvPolynomial.degreeOf_pow_eq 1 r 2 hr, mul_comm]
    by_cases he : 2 ≤ r.degreeOf 1
    · have hB2r : (B2 * r ^(2:ℕ)).degreeOf 1 ≤ 1 + 2 * r.degreeOf 1 := by
        calc _ ≤ B2.degreeOf 1 + (r ^(2:ℕ)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
          _ ≤ 1 + 2 * r.degreeOf 1 := by rw [hpow2]; omega
      have hB1r : (B1 * r).degreeOf 1 ≤ 2 + r.degreeOf 1 := by
        calc _ ≤ B1.degreeOf 1 + r.degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
          _ ≤ 2 + r.degreeOf 1 := by omega
      have hrest : (B2 * r ^(2:ℕ) + B1 * r + B0).degreeOf 1 < 3 * r.degreeOf 1 := by
        refine (MvPolynomial.degreeOf_add_le 1 _ _).trans_lt ?_
        refine max_lt ?_ ?_
        · exact (MvPolynomial.degreeOf_add_le 1 _ _).trans_lt
            (max_lt (lt_of_le_of_lt hB2r (by omega)) (lt_of_le_of_lt hB1r (by omega)))
        · rw [h0]; omega
      have hdegE : (-(MvPolynomial.C c * r ^(3:ℕ)) + (B2 * r ^(2:ℕ) + B1 * r + B0)).degreeOf 1 =
          3 * r.degreeOf 1 := by
        rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (q := B2 * r ^(2:ℕ) + B1 * r + B0)
          (by rw [MvPolynomial.degreeOf_neg, hCc3]; exact hrest), MvPolynomial.degreeOf_neg, hCc3]
      have hE' : -(MvPolynomial.C c * r ^(3:ℕ)) + (B2 * r ^(2:ℕ) + B1 * r + B0) = 0 := by
        simpa only [add_assoc] using hE
      rw [hE', MvPolynomial.degreeOf_zero] at hdegE
      omega
    · push Not at he
      have hterm1 : (-(MvPolynomial.C c * r ^(3:ℕ)) : MvPolynomial (Fin 2) K).degreeOf 1 ≤ 3 := by
        rw [MvPolynomial.degreeOf_neg, hCc3]; omega
      have hterm2 : (B2 * r ^(2:ℕ)).degreeOf 1 ≤ 3 := by
        calc _ ≤ B2.degreeOf 1 + (r ^(2:ℕ)).degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
          _ ≤ 1 + 2 * r.degreeOf 1 := by rw [hpow2]; omega
          _ ≤ 3 := by omega
      have hterm3 : (B1 * r).degreeOf 1 ≤ 3 := by
        calc _ ≤ B1.degreeOf 1 + r.degreeOf 1 := MvPolynomial.degreeOf_mul_le 1 _ _
          _ ≤ 2 + r.degreeOf 1 := by omega
          _ ≤ 3 := by omega
      have hup : (((-(MvPolynomial.C c * r ^(3:ℕ))) + B2 * r ^(2:ℕ)) + B1 * r).degreeOf 1 ≤ 3 := by
        have h12 : (((-(MvPolynomial.C c * r ^(3:ℕ))) + B2 * r ^(2:ℕ)) :
            MvPolynomial (Fin 2) K).degreeOf 1 ≤ 3 :=
          (MvPolynomial.degreeOf_add_le 1 _ _).trans (max_le hterm1 hterm2)
        exact (MvPolynomial.degreeOf_add_le 1 _ _).trans (max_le h12 hterm3)
      have hdegE : (B0 + (((-(MvPolynomial.C c * r ^(3:ℕ))) + B2 * r ^(2:ℕ)) + B1 * r)).degreeOf 1 = 4 := by
        rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
          (h := lt_of_le_of_lt hup (by rw [h0]; norm_num)), h0]
      have hE'' : B0 + (((-(MvPolynomial.C c * r ^(3:ℕ))) + B2 * r ^(2:ℕ)) + B1 * r) = 0 := by
        rw [← hE]; exact add_comm _ _
      rw [hE'', MvPolynomial.degreeOf_zero] at hdegE
      omega

/-! ## 5.  The cubic `fwGp` and its irreducibility -/

/-- The image of `fwG` under the variable identification `tau3` (`X 1 ↦ Polynomial.X`): a cubic in
one variable over `K[x₀,x₂]`. -/
noncomputable def fwGp {K : Type} [Field K] (a b h : K) : Polynomial (MvPolynomial (Fin 2) K) :=
  Polynomial.C (-(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ)))) * Polynomial.X ^(3:ℕ)
  + (Polynomial.C (fwBeta2 a b h) * Polynomial.X ^(2:ℕ)
    + (Polynomial.C (fwBeta1 a b h) * Polynomial.X + Polynomial.C (fwBeta0 a b h)))

theorem fwGp_deg_le {K : Type} [Field K] (a b h : K) :
    (Polynomial.C (fwBeta2 a b h) * Polynomial.X ^(2:ℕ)
      + (Polynomial.C (fwBeta1 a b h) * Polynomial.X + Polynomial.C (fwBeta0 a b h)) :
        Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 2 := by
  have h1 : (Polynomial.C (fwBeta2 a b h) * Polynomial.X ^(2:ℕ) :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 2 := by
    calc (Polynomial.C (fwBeta2 a b h) * Polynomial.X ^(2:ℕ) :
            Polynomial (MvPolynomial (Fin 2) K)).natDegree
        ≤ (Polynomial.C (fwBeta2 a b h)).natDegree
          + (Polynomial.X ^(2:ℕ) : Polynomial (MvPolynomial (Fin 2) K)).natDegree :=
          Polynomial.natDegree_mul_le
      _ = 2 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  have h2 : (Polynomial.C (fwBeta1 a b h) * Polynomial.X + Polynomial.C (fwBeta0 a b h) :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 1 := by
    have h2a : (Polynomial.C (fwBeta1 a b h) * Polynomial.X :
        Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 1 := by
      calc (Polynomial.C (fwBeta1 a b h) * Polynomial.X :
              Polynomial (MvPolynomial (Fin 2) K)).natDegree
          ≤ (Polynomial.C (fwBeta1 a b h)).natDegree
            + (Polynomial.X : Polynomial (MvPolynomial (Fin 2) K)).natDegree :=
            Polynomial.natDegree_mul_le
        _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le h2a ?_)
    rw [Polynomial.natDegree_C]
    norm_num
  exact (Polynomial.natDegree_add_le _ _).trans (max_le h1 (h2.trans (by norm_num)))

theorem fwGp_natDegree {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (fwGp a b h).natDegree = 3 := by
  have hne : (-(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ))) : MvPolynomial (Fin 2) K) ≠ 0 :=
    neg_ne_zero.mpr (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 4 hb)))
  have hA : (Polynomial.C (-(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ)))) * Polynomial.X ^(3:ℕ) :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree = 3 := by
    rw [Polynomial.natDegree_C_mul hne, Polynomial.natDegree_X_pow]
  rw [fwGp]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (by rw [hA]; exact lt_of_le_of_lt (fwGp_deg_le a b h) (by norm_num))]
  exact hA

theorem fwGp_coeff3 {K : Type} [Field K] (a b h : K) :
    (fwGp a b h).coeff 3 = -(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ))) := by
  have h2 : (Polynomial.C (fwBeta2 a b h) * Polynomial.X ^(2:ℕ)
      + (Polynomial.C (fwBeta1 a b h) * Polynomial.X + Polynomial.C (fwBeta0 a b h)) :
        Polynomial (MvPolynomial (Fin 2) K)).natDegree < 3 :=
    lt_of_le_of_lt (fwGp_deg_le a b h) (by norm_num)
  rw [fwGp, Polynomial.coeff_add,
    Polynomial.coeff_eq_zero_of_natDegree_lt h2,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp

theorem fwGp_leadingCoeff {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (fwGp a b h).leadingCoeff = -(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ))) := by
  rw [← Polynomial.coeff_natDegree, fwGp_natDegree a b h ha hb, fwGp_coeff3 a b h]

theorem fwGp_isUnit_leadingCoeff {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsUnit (fwGp a b h).leadingCoeff := by
  have hne : (a ^(3:ℕ) * b ^(4:ℕ) : K) ≠ 0 := mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 4 hb)
  rw [fwGp_leadingCoeff a b h ha hb]
  exact ⟨⟨-(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ))), -(MvPolynomial.C ((a ^(3:ℕ) * b ^(4:ℕ))⁻¹)),
    by rw [neg_mul_neg, ← map_mul, mul_inv_cancel₀ hne, map_one],
    by rw [neg_mul_neg, ← map_mul, inv_mul_cancel₀ hne, map_one]⟩, rfl⟩

theorem fwGp_eval {K : Type} [Field K] (a b h : K) (r : MvPolynomial (Fin 2) K) :
    (fwGp a b h).eval r = -(MvPolynomial.C (a ^(3:ℕ) * b ^(4:ℕ)) * r ^(3:ℕ)) + fwBeta2 a b h * r ^(2:ℕ)
      + fwBeta1 a b h * r + fwBeta0 a b h := by
  simp only [fwGp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  first | refl_ring1 | ring

/-- **`fwGp a b h` has no root.** -/
theorem fwGp_no_root {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ r : MvPolynomial (Fin 2) K, ¬ (fwGp a b h).IsRoot r := by
  intro r hr
  rw [Polynomial.IsRoot, fwGp_eval a b h r] at hr
  exact no_root_aux (a ^(3:ℕ) * b ^(4:ℕ)) (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 4 hb))
    (fwBeta2 a b h) (fwBeta1 a b h) (fwBeta0 a b h)
    (degreeOf_fwBeta2 a b h) (degreeOf_fwBeta1 a b h) (degreeOf_fwBeta0 a b h ha hb hh) r hr

/-- **A cubic over a domain with unit leading coefficient and no root is irreducible.**  (A proper
factorisation would produce a linear factor; the leading coefficient of that factor is a unit, so
the factor has a root in the base ring.) -/
theorem irreducible_of_no_root {R : Type*} [CommRing R] [IsDomain R]
    (f : Polynomial R) (hdeg : f.natDegree = 3) (hlc : IsUnit f.leadingCoeff)
    (hroot : ∀ r : R, ¬ f.IsRoot r) : Irreducible f := by
  obtain ⟨u, hu⟩ : ∃ u : Rˣ, (↑u : R) = f.leadingCoeff := ⟨hlc.unit, IsUnit.unit_spec hlc⟩
  have hwne : (↑u⁻¹ : R) ≠ 0 := Units.ne_zero u⁻¹
  have hgmonic : (Polynomial.C (↑u⁻¹ : R) * f).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hu,
      Units.inv_mul]
  have hgdeg : (Polynomial.C (↑u⁻¹ : R) * f).natDegree = 3 := by
    rw [Polynomial.natDegree_C_mul hwne, hdeg]
  have hkey : (Polynomial.C (↑u⁻¹ : R) * f) * Polynomial.C (↑u : R) = f := by
    rw [mul_assoc, mul_comm f, ← mul_assoc, ← Polynomial.C_mul, Units.inv_mul, Polynomial.C_1,
      one_mul]
  have hassoc : Associated (Polynomial.C (↑u⁻¹ : R) * f) f :=
    ⟨(Polynomial.isUnit_C.mpr u.isUnit).unit, by rw [IsUnit.unit_spec]; exact hkey⟩
  rw [← hassoc.irreducible_iff]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hgmonic
    (by rw [hgdeg]; norm_num) (by rw [hgdeg])]
  apply Multiset.eq_zero_of_forall_notMem
  intro r hr
  rw [Polynomial.mem_roots hgmonic.ne_zero] at hr
  apply hroot r
  rw [Polynomial.IsRoot] at hr ⊢
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hr
  exact (mul_eq_zero.mp hr).resolve_left hwne

/-- **`fwGp a b h` is irreducible.** -/
theorem fwGp_irreducible {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) : Irreducible (fwGp a b h) :=
  irreducible_of_no_root (fwGp a b h) (fwGp_natDegree a b h ha hb)
    (fwGp_isUnit_leadingCoeff a b h ha hb) (fwGp_no_root a b h ha hb hh)

/-! ## 6.  Transport along `K[x₀,x₁,x₂] ≃ K[x₀,x₂][X]` -/

/-- The permutation `0 ↦ 1 ↦ 0`, `2 ↦ 2` of `Fin 3`. -/
def tauPerm : Fin 3 ≃ Fin 3 where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide
  right_inv := by decide

/-- The variable identification `K[x₀,x₁,x₂] ≃ₐ[K] K[x₀,x₂][X]` with `X 1 ↦ X`, `X 0 ↦ C X 0`,
`X 2 ↦ C X 1`. -/
noncomputable def tau3 {K : Type} [Field K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.renameEquiv K tauPerm).trans (MvPolynomial.finSuccEquiv K 2)

theorem tau3_X_zero {K : Type} [Field K] :
    tau3 (K := K) (MvPolynomial.X 0) = Polynomial.C (MvPolynomial.X 0) := by
  rw [tau3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  show MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (1 : Fin 3)) = _
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem tau3_X_one {K : Type} [Field K] :
    tau3 (K := K) (MvPolynomial.X 1) = Polynomial.X := by
  rw [tau3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  show MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (0 : Fin 3)) = _
  exact MvPolynomial.finSuccEquiv_X_zero

theorem tau3_X_two {K : Type} [Field K] :
    tau3 (K := K) (MvPolynomial.X 2) = Polynomial.C (MvPolynomial.X 1) := by
  rw [tau3, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  show MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (2 : Fin 3)) = _
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem tau3_C {K : Type} [Field K] (r : K) :
    tau3 (K := K) (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 3), (tau3 (K := K)).commutes,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq K (Fin 2)]

/-- `tau3 (fwG a b h) = fwGp a b h`. -/
theorem tau3_fwG {K : Type} [Field K] (a b h : K) : tau3 (K := K) (fwG a b h) = fwGp a b h := by
  have h2 : tau3 (K := K) (2 : MvPolynomial (Fin 3) K) =
      Polynomial.C (2 : MvPolynomial (Fin 2) K) := by
    rw [show (2 : MvPolynomial (Fin 3) K) = MvPolynomial.C (2 : K) from rfl, tau3_C]
    rfl
  simp only [fwG, fwGp, fwBeta0, fwBeta1, fwBeta2, tau3_X_zero, tau3_X_one, tau3_X_two, tau3_C, h2,
    map_add, map_sub, map_mul, map_pow, map_neg]
  ring_nf

/-- **`fwG a b h` is irreducible.** -/
theorem fwG_irreducible {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Irreducible (fwG a b h) := by
  rw [← MulEquiv.irreducible_iff (tau3 (K := K)), tau3_fwG]
  exact fwGp_irreducible a b h ha hb hh

/-! ## 7.  The unit bookkeeping and the main theorem -/

/-- `C x` is a unit of the multivariate polynomial ring over a field, for `x ≠ 0`. -/
theorem mv_isUnit_C {K : Type} [Field K] {σ : Type*} (x : K) (hx : x ≠ 0) :
    IsUnit (MvPolynomial.C x : MvPolynomial σ K) :=
  ⟨⟨MvPolynomial.C x, MvPolynomial.C x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hx, map_one]⟩, rfl⟩

/-- `u * a` is associated to `a` when `u` is a unit. -/
theorem associated_mul_unit_left {M : Type*} [CommMonoid M] {u : M} (a : M) (hu : IsUnit u) :
    Associated (u * a) a := by
  obtain ⟨w, rfl⟩ := hu
  exact ⟨w⁻¹, by rw [mul_assoc, mul_comm a (↑w⁻¹), ← mul_assoc, Units.mul_inv, one_mul]⟩

/-- **The quartic `f̂₄ = fwVec a b h 4` is irreducible**, for all `a b h ≠ 0` over any field. -/
theorem FwVec4Prime2 {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Irreducible (Work.MotK.TGen.fwVec a b h 4) := by
  have h1 : MvPolynomial.C a * fwVec a b h 4 = MvPolynomial.C h * fwG a b h :=
    Ca_fwVec_four a b h ha hh
  have hEq : Associated (MvPolynomial.C a * fwVec a b h 4) (MvPolynomial.C h * fwG a b h) := by
    rw [h1]
  have hassoc : Associated (fwVec a b h 4) (fwG a b h) :=
    ((associated_mul_unit_left _ (mv_isUnit_C a ha)).symm.trans hEq).trans
      (associated_mul_unit_left _ (mv_isUnit_C h hh))
  exact hassoc.irreducible_iff.mpr (fwG_irreducible a b h ha hb hh)

end Work.MotK.TGen
