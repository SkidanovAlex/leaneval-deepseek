import Mathlib
import Submission.Work.MotK.TwRuling.TwSixCoeffDefs
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.KleinTwPMapApply
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Work.MotK.TwRuling

open MvPolynomial

/-! ## §1 Naturality of the twisted ruling data under a ring homomorphism -/

section Nat

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Naturality of the standard basis vector. -/
theorem twE_map (σ : R →+* S) (k i : Fin 5) :
    σ (Work.MotK.kleinE (R := R) k i) = Work.MotK.kleinE (R := S) k i := by
  by_cases h : i = k <;> simp [Work.MotK.kleinE, h]

/-- Naturality of the polar form of the twisted quadric. -/
theorem twBilin_map (σ : R →+* S) (a b h : R) (u v : Fin 5 → R) :
    σ (Work.MotK.kleinTwBilin a b h u v)
      = Work.MotK.kleinTwBilin (σ a) (σ b) (σ h) (fun i => σ (u i)) (fun i => σ (v i)) := by
  simp only [Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, Pi.add_apply,
    map_add, map_mul, map_pow, map_neg, map_sub]

/-- Naturality of the tangent vectors. -/
theorem twTan_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) (k : Fin 5) :
    (fun i => σ (Work.MotK.kleinTwTan a b h c k i))
      = Work.MotK.kleinTwTan (σ a) (σ b) (σ h) (fun i => σ (c i)) k := by
  funext i
  simp only [Work.MotK.kleinTwTan, map_sub, map_mul, twBilin_map, twE_map]

/-- Naturality of the polarised twisted Pfaffian map. -/
theorem twPolarP_map (σ : R →+* S) (a b h : R) (x y : Fin 5 → R) (k : Fin 5) :
    σ (Work.MotK.kleinTwPolarP a b h x y k)
      = Work.MotK.kleinTwPolarP (σ a) (σ b) (σ h) (fun i => σ (x i)) (fun i => σ (y i)) k := by
  have h1 : (fun i => σ ((x + y) i)) = (fun i => σ (x i)) + (fun i => σ (y i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [Work.MotK.kleinTwPolarP]
  rw [map_sub, map_sub, Work.MotK.KleinTwPMapApply, h1, Work.MotK.KleinTwPMapApply,
    Work.MotK.KleinTwPMapApply]

/-- Naturality of the first ruling vector. -/
theorem twRuleA_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) :
    (fun i => σ (Work.MotK.kleinTwRuleA a b h c i))
      = Work.MotK.kleinTwRuleA (σ a) (σ b) (σ h) (fun i => σ (c i)) := by
  funext i
  simp only [Work.MotK.kleinTwRuleA, twPolarP_map, twTan_map]

/-- Naturality of the second ruling vector. -/
theorem twRuleB_map (σ : R →+* S) (a b h : R) (c : Fin 5 → R) :
    (fun i => σ (Work.MotK.kleinTwRuleB a b h c i))
      = Work.MotK.kleinTwRuleB (σ a) (σ b) (σ h) (fun i => σ (c i)) := by
  funext i
  simp only [Work.MotK.kleinTwRuleB, twPolarP_map, twTan_map]

/-- Naturality of the twisted inverse cubic. -/
theorem twR0_map (σ : R →+* S) (a b h : R) (y : Fin 5 → R) :
    σ (Work.MotK.kleinTwR0 a b h y)
      = Work.MotK.kleinTwR0 (σ a) (σ b) (σ h) (fun i => σ (y i)) := by
  simp only [Work.MotK.kleinTwR0, map_add, map_sub, map_mul, map_pow, map_neg]

end Nat

/-! ## §2 The coefficient forms of `R₀(A + T·B)` -/

section Main

variable {L : Type*} [Field L]

/-- The `T`-coefficient of `R₀(A + T·B)` (with the numeral `2` written as a sum, so that
`Polynomial.C` can be pushed inside without touching numerals). -/
def sdC1 (a b h : L) (A B : Fin 5 → L) : L :=
  -a * b ^(3:ℕ) * h * (A 3 * A 4 * B 3 + (A 3 * A 4 * B 3 + (A 3) ^(2:ℕ) * B 4))
    - a * b ^(3:ℕ) * h ^(2:ℕ) * (B 1 * (A 2) ^(2:ℕ) + (A 1 * A 2 * B 2 + A 1 * A 2 * B 2))
    + a ^(2:ℕ) * b ^(2:ℕ) * ((A 0) ^(2:ℕ) * B 0 + ((A 0) ^(2:ℕ) * B 0 + (A 0) ^(2:ℕ) * B 0))
    + a ^(3:ℕ) * b * h * (A 2 * A 4 * B 4 + (A 2 * A 4 * B 4 + (A 4) ^(2:ℕ) * B 2))
    + a ^(3:ℕ) * b * h ^(2:ℕ) * (A 1 * A 3 * B 1 + (A 1 * A 3 * B 1 + (A 1) ^(2:ℕ) * B 3))
    - a ^(4:ℕ) * h * (A 0 * A 1 * B 4 + A 0 * B 1 * A 4 + B 0 * A 1 * A 4)
    - b ^(4:ℕ) * h * (A 0 * A 2 * B 3 + A 0 * B 2 * A 3 + B 0 * A 2 * A 3)

/-- The `T²`-coefficient of `R₀(A + T·B)`. -/
def sdC2 (a b h : L) (A B : Fin 5 → L) : L :=
  -a * b ^(3:ℕ) * h * ((B 3) ^(2:ℕ) * A 4 + (A 3 * B 3 * B 4 + A 3 * B 3 * B 4))
    - a * b ^(3:ℕ) * h ^(2:ℕ) * (A 1 * (B 2) ^(2:ℕ) + (A 2 * B 1 * B 2 + A 2 * B 1 * B 2))
    + a ^(2:ℕ) * b ^(2:ℕ) * (A 0 * (B 0) ^(2:ℕ) + (A 0 * (B 0) ^(2:ℕ) + A 0 * (B 0) ^(2:ℕ)))
    + a ^(3:ℕ) * b * h * (A 2 * (B 4) ^(2:ℕ) + (A 4 * B 2 * B 4 + A 4 * B 2 * B 4))
    + a ^(3:ℕ) * b * h ^(2:ℕ) * ((B 1) ^(2:ℕ) * A 3 + (A 1 * B 1 * B 3 + A 1 * B 1 * B 3))
    - a ^(4:ℕ) * h * (A 0 * B 1 * B 4 + B 0 * A 1 * B 4 + B 0 * B 1 * A 4)
    - b ^(4:ℕ) * h * (A 0 * B 2 * B 3 + B 0 * A 2 * B 3 + B 0 * B 2 * A 3)

/-- Decomposition of `R₀(A + T·B)` in the polynomial ring, by the four `T`-coefficients. -/
theorem kleinTwR0_add_X_mul (a b h : L) (A B : Fin 5 → L) :
    Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
        (fun k => Polynomial.C (A k) + Polynomial.X * Polynomial.C (B k))
      = Polynomial.C (Work.MotK.kleinTwR0 a b h A)
        + Polynomial.C (sdC1 a b h A B) * Polynomial.X
        + Polynomial.C (sdC2 a b h A B) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (Work.MotK.kleinTwR0 a b h B) * Polynomial.X ^(3:ℕ) := by
  simp only [Work.MotK.kleinTwR0, sdC1, sdC2, map_add, map_sub, map_mul, map_pow, map_neg]
  first | refl_ring1 | ring

/-- The coefficient of `T^3` in `R₀(A + T·B)` is `R₀(B)`. -/
theorem coeff_three_kleinTwR0 (a b h : L) (A B : Fin 5 → L) :
    (Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
        (fun k => Polynomial.C (A k) + Polynomial.X * Polynomial.C (B k))).coeff 3
      = Work.MotK.kleinTwR0 a b h B := by
  rw [kleinTwR0_add_X_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]
  norm_num
  try ring

/-- The coefficient of `T^2` in `R₀(A + T·B)`. -/
theorem coeff_two_kleinTwR0 (a b h : L) (A B : Fin 5 → L) :
    (Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
        (fun k => Polynomial.C (A k) + Polynomial.X * Polynomial.C (B k))).coeff 2
      = sdC2 a b h A B := by
  rw [kleinTwR0_add_X_mul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]
  norm_num
  try ring

/-- Naturality of the whole construction: evaluating `sdCoeff6` at a point `W` equals taking the
`T^j`-coefficient of `R₀(A(W) + T·B(W))`. -/
theorem aeval_sdCoeff6 (a b h : L) (W : Fin 5 → L) (j : ℕ) :
    MvPolynomial.aeval W (sdCoeff6 L a b h j)
      = (Work.MotK.kleinTwR0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
          (fun k => Polynomial.C (Work.MotK.kleinTwRuleA a b h W k)
            + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB a b h W k))).coeff j := by
  let Φ : MvPolynomial (Fin 5) L →+* L := (MvPolynomial.aeval W).toRingHom
  have hfa : Φ (MvPolynomial.C a) = a := by
    show MvPolynomial.aeval W (MvPolynomial.C a) = a
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
  have hfb : Φ (MvPolynomial.C b) = b := by
    show MvPolynomial.aeval W (MvPolynomial.C b) = b
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
  have hfh : Φ (MvPolynomial.C h) = h := by
    show MvPolynomial.aeval W (MvPolynomial.C h) = h
    rw [MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
  have hfX : (fun i : Fin 5 => Φ (MvPolynomial.X i : MvPolynomial (Fin 5) L)) = W := by
    funext i
    show MvPolynomial.aeval W (MvPolynomial.X i : MvPolynomial (Fin 5) L) = W i
    rw [MvPolynomial.aeval_X]
  have hAy : (fun i : Fin 5 => Φ
      (Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin 5) L)) i))
      = Work.MotK.kleinTwRuleA a b h W := by
    rw [twRuleA_map (R := MvPolynomial (Fin 5) L) (S := L) (σ := Φ)]
    rw [hfa, hfb, hfh, hfX]
  have hBy : (fun i : Fin 5 => Φ
      (Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin 5) L)) i))
      = Work.MotK.kleinTwRuleB a b h W := by
    rw [twRuleB_map (R := MvPolynomial (Fin 5) L) (S := L) (σ := Φ)]
    rw [hfa, hfb, hfh, hfX]
  have hmap : (Polynomial.mapRingHom Φ (coeffPoly L a b h)).coeff j
      = MvPolynomial.aeval W ((coeffPoly L a b h).coeff j) := by
    change (Polynomial.map Φ (coeffPoly L a b h)).coeff j
      = MvPolynomial.aeval W ((coeffPoly L a b h).coeff j)
    rw [Polynomial.coeff_map]
    rfl
  rw [sdCoeff6_eq, ← hmap]
  have hCa : Polynomial.mapRingHom Φ (Polynomial.C (MvPolynomial.C a)) = Polynomial.C a := by
    change Polynomial.map Φ (Polynomial.C (MvPolynomial.C a)) = Polynomial.C a
    rw [Polynomial.map_C, hfa]
  have hCb : Polynomial.mapRingHom Φ (Polynomial.C (MvPolynomial.C b)) = Polynomial.C b := by
    change Polynomial.map Φ (Polynomial.C (MvPolynomial.C b)) = Polynomial.C b
    rw [Polynomial.map_C, hfb]
  have hCh : Polynomial.mapRingHom Φ (Polynomial.C (MvPolynomial.C h)) = Polynomial.C h := by
    change Polynomial.map Φ (Polynomial.C (MvPolynomial.C h)) = Polynomial.C h
    rw [Polynomial.map_C, hfh]
  have hY : (fun i => Polynomial.mapRingHom Φ
        (Polynomial.C (qA L a b h i) + Polynomial.X * Polynomial.C (qB L a b h i)))
      = fun k => Polynomial.C (Work.MotK.kleinTwRuleA a b h W k)
          + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB a b h W k) := by
    funext i
    change Polynomial.map Φ
        (Polynomial.C (qA L a b h i) + Polynomial.X * Polynomial.C (qB L a b h i))
      = Polynomial.C (Work.MotK.kleinTwRuleA a b h W i)
          + Polynomial.X * Polynomial.C (Work.MotK.kleinTwRuleB a b h W i)
    simp only [qA_apply, qB_apply, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X]
    rw [congrFun hAy i, congrFun hBy i]
  simp only [coeffPoly]
  rw [twR0_map (σ := Polynomial.mapRingHom Φ)]
  rw [hCa, hCb, hCh, hY]

end Main

/-! ## §3 The explicit point and its evaluation -/

section Pt

variable {L : Type*} [Field L]

/-- The ruling vectors of the twisted link at the explicit point
`z = (a·h·α, 0, a·h·α², b, b·h·α³)`. -/
theorem twRuleA_pt (a b h α : L) :
    Work.MotK.kleinTwRuleA a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 0 = 0 ∧
    Work.MotK.kleinTwRuleA a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 1
      = -(a ^(2:ℕ) * α * b ^(4:ℕ) * h) * (α ^(5:ℕ) * h ^(2:ℕ) + 2) ∧
    Work.MotK.kleinTwRuleA a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 2
      = α ^(3:ℕ) * b * h ^(2:ℕ) * (2 * a ^(5:ℕ) + b ^(5:ℕ)) ∧
    Work.MotK.kleinTwRuleA a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 3
      = a * α ^(5:ℕ) * b ^(5:ℕ) * h ^(3:ℕ) ∧
    Work.MotK.kleinTwRuleA a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 4
      = 2 * a ^(5:ℕ) * α ^(2:ℕ) * b * h ^(2:ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
      Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
      Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
    simp only [Pi.single_apply, Fin.isValue]
    norm_num
    first | refl_ring1 | ring

/-- The second ruling vector at the explicit point `z = (a·h·α, 0, a·h·α², b, b·h·α³)`. -/
theorem twRuleB_pt (a b h α : L) :
    Work.MotK.kleinTwRuleB a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 0 = 0 ∧
    Work.MotK.kleinTwRuleB a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 1
      = -3 * a ^(4:ℕ) * α ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) ∧
    Work.MotK.kleinTwRuleB a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 2
      = -(a ^(2:ℕ) * b ^(4:ℕ) * h) ∧
    Work.MotK.kleinTwRuleB a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 3
      = -3 * a ^(3:ℕ) * α ^(2:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) ∧
    Work.MotK.kleinTwRuleB a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 4
      = -2 * a ^(2:ℕ) * α ^(4:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
      Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
      Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
    simp only [Pi.single_apply, Fin.isValue]
    norm_num
    first | refl_ring1 | ring

/-- The five twisted Pfaffians at the explicit point `z = (a·h·α, 0, a·h·α², b, b·h·α³)`. -/
theorem twP_pt (a b h α : L) :
    Work.MotK.kleinTwP a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 0 = 0 ∧
    Work.MotK.kleinTwP a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 1 = 0 ∧
    Work.MotK.kleinTwP a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 2
      = -(a * α * b ^(3:ℕ) * h) * (h ^(2:ℕ) * α ^(5:ℕ) + 1) ∧
    Work.MotK.kleinTwP a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 3 = 0 ∧
    Work.MotK.kleinTwP a b h
        (![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] : Fin 5 → L) 4
      = -(a * b ^(3:ℕ) * h) * (h ^(2:ℕ) * α ^(5:ℕ) + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold Work.MotK.kleinTwP Work.MotK.kleinTwP0 Work.MotK.kleinTwP1 Work.MotK.kleinTwP2
      Work.MotK.kleinTwP3 Work.MotK.kleinTwP4
    norm_num
    first | refl_ring1 | ring

end Pt

end Work.MotK.TwRuling

namespace Work.MotK.TwRuling

/-- The explicit graded point `z = (a·h·α, 0, a·h·α², b, b·h·α³)` with `α⁵ = -1/h²` lies on the
twisted Klein quartic (`kehrTwP`, untwisted: `h` is only a coefficient here) and the two degree-6
coefficient forms evaluate there to `a⁹α³b⁸h⁶(27a⁵-11b⁵)` resp. `a⁷αb¹⁰h⁵(57a⁵-b⁵)`.

Route: `simp only [sdCoeff6, coeffPoly, qA_apply, qB_apply]` then push `MvPolynomial.aeval` through
`kleinTwR0`, `kleinTwRuleA`, `kleinTwRuleB` (`Work.MotK.KleinTwRulingQuinticMem`-style naturality,
or directly `simp` on the unfolded definitions) to reduce to an identity in the *field* `L`;
finally prove that identity with `ring_nf`-style manipulation after replacing `α⁵` by `-1/h²`
(e.g. prove `LHS - RHS = (α^5 + h⁻²) * G` for an explicit `G`, or reduce powers of `α` with
`Polynomial`/`Finsupp` bookkeeping).  The two coefficient values and the five Pfaffian vanishings
have been verified symbolically (`ℚ(a,b,h,α)` modulo `α⁵ = -1/h²`). -/
theorem sdCoeff6_eval_family (L : Type*) [Field L] (a b h α : L) (hab : a * b ≠ 0) (hh : h ≠ 0)
    (hα : α ^(5:ℕ) = -(1 / h ^(2:ℕ))) :
    (MvPolynomial.aeval (fun i => ![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] i)
        (Work.MotK.TwRuling.sdCoeff6 L a b h 3)
      = a ^(9:ℕ) * α ^(3:ℕ) * b ^(8:ℕ) * h ^(6:ℕ) * (27 * a ^(5:ℕ) - 11 * b ^(5:ℕ)))
    ∧ (MvPolynomial.aeval (fun i => ![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] i)
        (Work.MotK.TwRuling.sdCoeff6 L a b h 2)
      = a ^(7:ℕ) * α * b ^(10:ℕ) * h ^(5:ℕ) * (57 * a ^(5:ℕ) - b ^(5:ℕ)))
    ∧ (∀ k : Fin 5, Work.MotK.kleinTwP a b h
        (fun i => ![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] i) k = 0) := by
  set W : Fin 5 → L := fun i => ![a * h * α, 0, a * h * α ^(2:ℕ), b, b * h * α ^(3:ℕ)] i with hW
  have hz : h ^(2:ℕ) * α ^(5:ℕ) + 1 = 0 := by rw [hα]; field_simp; ring
  have hA0 : Work.MotK.kleinTwRuleA a b h W 0 = 0 := by
    rw [hW]; exact (twRuleA_pt a b h α).1
  have hA1 : Work.MotK.kleinTwRuleA a b h W 1 = -(a ^(2:ℕ) * α * b ^(4:ℕ) * h) * (α ^(5:ℕ) * h ^(2:ℕ) + 2) := by
    rw [hW]; exact (twRuleA_pt a b h α).2.1
  have hA2 : Work.MotK.kleinTwRuleA a b h W 2 = α ^(3:ℕ) * b * h ^(2:ℕ) * (2 * a ^(5:ℕ) + b ^(5:ℕ)) := by
    rw [hW]; exact (twRuleA_pt a b h α).2.2.1
  have hA3 : Work.MotK.kleinTwRuleA a b h W 3 = a * α ^(5:ℕ) * b ^(5:ℕ) * h ^(3:ℕ) := by
    rw [hW]; exact (twRuleA_pt a b h α).2.2.2.1
  have hA4 : Work.MotK.kleinTwRuleA a b h W 4 = 2 * a ^(5:ℕ) * α ^(2:ℕ) * b * h ^(2:ℕ) := by
    rw [hW]; exact (twRuleA_pt a b h α).2.2.2.2
  have hB0 : Work.MotK.kleinTwRuleB a b h W 0 = 0 := by
    rw [hW]; exact (twRuleB_pt a b h α).1
  have hB1 : Work.MotK.kleinTwRuleB a b h W 1 = -3 * a ^(4:ℕ) * α ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) := by
    rw [hW]; exact (twRuleB_pt a b h α).2.1
  have hB2 : Work.MotK.kleinTwRuleB a b h W 2 = -(a ^(2:ℕ) * b ^(4:ℕ) * h) := by
    rw [hW]; exact (twRuleB_pt a b h α).2.2.1
  have hB3 : Work.MotK.kleinTwRuleB a b h W 3 = -3 * a ^(3:ℕ) * α ^(2:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) := by
    rw [hW]; exact (twRuleB_pt a b h α).2.2.2.1
  have hB4 : Work.MotK.kleinTwRuleB a b h W 4 = -2 * a ^(2:ℕ) * α ^(4:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) := by
    rw [hW]; exact (twRuleB_pt a b h α).2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [aeval_sdCoeff6 a b h W 3,
      coeff_three_kleinTwR0 a b h (Work.MotK.kleinTwRuleA a b h W) (Work.MotK.kleinTwRuleB a b h W)]
    simp only [Work.MotK.kleinTwR0, hB0, hB1, hB2, hB3, hB4]
    linear_combination (norm := first | refl_ring1 | ring1)
      (-27 * a ^(14:ℕ) * α ^(3:ℕ) * b ^(8:ℕ) * h ^(6:ℕ) + 14 * a ^(9:ℕ) * α ^(3:ℕ) * b ^(13:ℕ) * h ^(6:ℕ)) * hz
  · rw [aeval_sdCoeff6 a b h W 2,
      coeff_two_kleinTwR0 a b h (Work.MotK.kleinTwRuleA a b h W) (Work.MotK.kleinTwRuleB a b h W)]
    simp only [sdC2, hA0, hA1, hA2, hA3, hA4, hB0, hB1, hB2, hB3, hB4]
    linear_combination (norm := first | refl_ring1 | ring1)
      (-a ^(12:ℕ) * α ^(6:ℕ) * b ^(10:ℕ) * h ^(7:ℕ) - 57 * a ^(12:ℕ) * α * b ^(10:ℕ) * h ^(5:ℕ)
        - 8 * a ^(7:ℕ) * α ^(6:ℕ) * b ^(15:ℕ) * h ^(7:ℕ) + 3 * a ^(7:ℕ) * α * b ^(15:ℕ) * h ^(5:ℕ)) * hz
  · intro k
    fin_cases k
    · rw [hW]; exact (twP_pt a b h α).1
    · rw [hW]; exact (twP_pt a b h α).2.1
    · rw [hW]
      exact ((twP_pt a b h α).2.2.1).trans (by rw [hz, mul_zero])
    · rw [hW]; exact (twP_pt a b h α).2.2.2.1
    · rw [hW]
      exact ((twP_pt a b h α).2.2.2.2).trans (by rw [hz, mul_zero])

end Work.MotK.TwRuling
