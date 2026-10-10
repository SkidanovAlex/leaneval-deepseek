import Mathlib
import Submission.Work.MotK.TwRuling.ParamVec
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Work.MotK.TwRuling

/-!
# The zeroth coordinate of `kleinTwR` at the characteristic-two parametrisation

`paramVec K D h` is the characteristic-two parametrisation of the target ruling divisor
(`Submission/Work/MotK/TwRuling/ParamVec.lean`).  This file proves that the inverse cubic map
`kleinTwR` does not vanish at `paramVec`, i.e.

  `kleinTwR A B H (paramVec K D h) 0 ≠ 0`      (`A,B,H` = the images of `D.a,D.b,h` in `sdA`).

## Proof

In the ring `S := sdA K D h = RatFunc ↥(twistFieldTG K D h)`, `paramVec K D h` is `A⁻¹ • Z` where
`Z = ![0, A t, A y₂ + B H y₄ t, B y₁ + A H y₃ t, A]` and `t = RatFunc.X`.  Since `kleinTwR0` is
homogeneous of degree `3`, it suffices to show `kleinTwR0 A B H Z ≠ 0`.

Clearing and using the characteristic-two identities `(x+y)² = x² + y²` gives (over any commutative
ring with `2 = 0`) the identity

  `kleinTwR0 A B H Z = A²BH · ((A⁴y₂ - B⁴y₁²) + A²BH(A y₄ - B y₂²)t + A²BH(A y₁ - BHy₃²)t² + H²(A⁴y₃ - B⁴Hy₄²)t³)`.

The coefficients of this polynomial in `t` all lie in the base field `F := ↥(twistFieldTG K D h)`
(`A,B,H,y_i` are images of elements of `F`), and `t = RatFunc.X` is transcendental over `F`.  So if
`kleinTwR0 A B H Z = 0` then the coefficient `A²BH·(A y₄ - B y₂²)` of `t` and the coefficient
`A²BH·(A y₁ - B H y₃²)` of `t²` vanish; since `A,B,H ≠ 0` this means
`A y₄ = B y₂²` and `A y₁ = B H y₃²`.

But the twisted Pfaffians `kleinTwP A B H (sdY K D h) = 0` (with `sdY 0 = 1`) together with these
two equations are contradictory: combining the equations with `p₁` and `p₄` gives `y₁y₃ = 0` and
`y₂y₄ = 0`, and then every one of the four cases contradicts `p₀` and `p₂`.  Hence the zeroth
coordinate is nonzero.
-/

section Helpers

/-- In characteristic two, `(x + y)² = x² + y²`. -/
private lemma pvz_add_sq {R : Type} [CommRing R] (h2 : (2 : R) = 0) (x y : R) :
    (x + y) ^(2:ℕ) = x ^(2:ℕ) + y ^(2:ℕ) := by
  have h : (x + y) ^(2:ℕ) = x ^(2:ℕ) + 2 * (x * y) + y ^(2:ℕ) := by ring
  rw [h, h2]
  refl_ring1

/-- The characteristic-two evaluation of `kleinTwR0` at the cleared parametrisation point. -/
private theorem pvz_R0_w {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (a b hh y1 y2 y3 y4 t : R) :
    Work.MotK.kleinTwR0 a b hh
        ![0, a * t, a * y2 + b * hh * y4 * t, b * y1 + a * hh * y3 * t, a]
      = a ^(2:ℕ) * b * hh *
          ((a ^(4:ℕ) * y2 - b ^(4:ℕ) * y1 ^(2:ℕ)) + (a ^(2:ℕ) * b * hh * (a * y4 - b * y2 ^(2:ℕ))) * t
            + (a ^(2:ℕ) * b * hh * (a * y1 - b * hh * y3 ^(2:ℕ))) * t ^(2:ℕ)
            + (hh ^(2:ℕ) * (a ^(4:ℕ) * y3 - b ^(4:ℕ) * hh * y4 ^(2:ℕ))) * t ^(3:ℕ)) := by
  have hs2 : (a * y2 + b * hh * y4 * t) ^(2:ℕ)
      = a ^(2:ℕ) * y2 ^(2:ℕ) + b ^(2:ℕ) * hh ^(2:ℕ) * y4 ^(2:ℕ) * t ^(2:ℕ) := by
    rw [pvz_add_sq h2]
    refl_ring1
  have hs3 : (b * y1 + a * hh * y3 * t) ^(2:ℕ)
      = b ^(2:ℕ) * y1 ^(2:ℕ) + a ^(2:ℕ) * hh ^(2:ℕ) * y3 ^(2:ℕ) * t ^(2:ℕ) := by
    rw [pvz_add_sq h2]
    refl_ring1
  simp only [Work.MotK.kleinTwR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    hs2, hs3]
  refl_ring1

/-- `kleinTwR0` is homogeneous of degree three in the vector. -/
private theorem pvz_smul0 {R : Type} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwR0 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR0 a b h y := by
  simp only [Work.MotK.kleinTwR0, Pi.smul_apply, smul_eq_mul]
  refl_ring1

/-- The coefficient of `X` of `monomial 0 c₀ + monomial 1 c₁ + monomial 2 c₂ + monomial 3 c₃`. -/
private lemma pvz_coeff_one {L : Type} [CommSemiring L] (c0 c1 c2 c3 : L) :
    (Polynomial.monomial 0 c0 + Polynomial.monomial 1 c1 + Polynomial.monomial 2 c2
      + Polynomial.monomial 3 c3 : Polynomial L).coeff 1 = c1 := by
  have e0 : (Polynomial.monomial 0 c0 : Polynomial L).coeff 1 = 0 :=
    Polynomial.coeff_monomial_of_ne c0 (by norm_num : (1 : ℕ) ≠ 0)
  have e1 : (Polynomial.monomial 1 c1 : Polynomial L).coeff 1 = c1 :=
    Polynomial.coeff_monomial_same 1 c1
  have e2 : (Polynomial.monomial 2 c2 : Polynomial L).coeff 1 = 0 :=
    Polynomial.coeff_monomial_of_ne c2 (by norm_num : (1 : ℕ) ≠ 2)
  have e3 : (Polynomial.monomial 3 c3 : Polynomial L).coeff 1 = 0 :=
    Polynomial.coeff_monomial_of_ne c3 (by norm_num : (1 : ℕ) ≠ 3)
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, e0, e1, e2, e3]
  first | refl_ring1 | ring

/-- The coefficient of `X²` of `monomial 0 c₀ + monomial 1 c₁ + monomial 2 c₂ + monomial 3 c₃`. -/
private lemma pvz_coeff_two {L : Type} [CommSemiring L] (c0 c1 c2 c3 : L) :
    (Polynomial.monomial 0 c0 + Polynomial.monomial 1 c1 + Polynomial.monomial 2 c2
      + Polynomial.monomial 3 c3 : Polynomial L).coeff 2 = c2 := by
  have e0 : (Polynomial.monomial 0 c0 : Polynomial L).coeff 2 = 0 :=
    Polynomial.coeff_monomial_of_ne c0 (by norm_num : (2 : ℕ) ≠ 0)
  have e1 : (Polynomial.monomial 1 c1 : Polynomial L).coeff 2 = 0 :=
    Polynomial.coeff_monomial_of_ne c1 (by norm_num : (2 : ℕ) ≠ 1)
  have e2 : (Polynomial.monomial 2 c2 : Polynomial L).coeff 2 = c2 :=
    Polynomial.coeff_monomial_same 2 c2
  have e3 : (Polynomial.monomial 3 c3 : Polynomial L).coeff 2 = 0 :=
    Polynomial.coeff_monomial_of_ne c3 (by norm_num : (2 : ℕ) ≠ 3)
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, e0, e1, e2, e3]
  first | refl_ring1 | ring

/-- `RatFunc.X` is transcendental, so `aeval RatFunc.X` is injective. -/
private lemma pvz_aeval_injective (L : Type) [Field L] :
    Function.Injective
      (Polynomial.aeval (RatFunc.X : RatFunc L)  : Polynomial L →ₐ[L] RatFunc L) :=
  transcendental_iff_injective.mp RatFunc.transcendental_X

/-- **Coefficient extraction over `RatFunc`.**  A vanishing element of the form
`c₀ + c₁·X + c₂·X² + c₃·X³` with coefficients in the base field forces `c₁ = c₂ = 0`. -/
private lemma pvz_extract {L : Type} [Field L] (c0 c1 c2 c3 : L)
    (h : algebraMap L (RatFunc L) c0 + algebraMap L (RatFunc L) c1 * RatFunc.X
          + algebraMap L (RatFunc L) c2 * RatFunc.X ^(2:ℕ)
          + algebraMap L (RatFunc L) c3 * RatFunc.X ^(3:ℕ) = 0) :
    c1 = 0 ∧ c2 = 0 := by
  have hinj := pvz_aeval_injective L
  have hP : (Polynomial.monomial 0 c0 + Polynomial.monomial 1 c1 + Polynomial.monomial 2 c2
      + Polynomial.monomial 3 c3 : Polynomial L) = 0 := by
    apply hinj
    rw [map_zero]
    simpa only [Polynomial.aeval_add, Polynomial.aeval_monomial, pow_zero, pow_one, mul_one]
      using h
  constructor
  · have h1 : (Polynomial.monomial 0 c0 + Polynomial.monomial 1 c1 + Polynomial.monomial 2 c2
        + Polynomial.monomial 3 c3 : Polynomial L).coeff 1 = 0 := by
      have h1' := congrArg (fun p : Polynomial L => p.coeff 1) hP
      simpa using h1'
    rwa [pvz_coeff_one] at h1
  · have h2 : (Polynomial.monomial 0 c0 + Polynomial.monomial 1 c1 + Polynomial.monomial 2 c2
        + Polynomial.monomial 3 c3 : Polynomial L).coeff 2 = 0 := by
      have h2' := congrArg (fun p : Polynomial L => p.coeff 2) hP
      simpa using h2'
    rwa [pvz_coeff_two] at h2

/-- **The contradiction used at the end.**  If the twisted Klein coordinates `1, Y₁, …, Y₄` satisfy
the twisted Pfaffians `p₀, p₁, p₂, p₄` and if `A Y₄ = B Y₂²`, `A Y₁ = B H Y₃²`, then all is zero;
but the Klein parameters are units. -/
private lemma pvz_contra {L : Type} [Field L] (A B H Y1 Y2 Y3 Y4 : L)
    (hA : A ≠ 0) (hB : B ≠ 0) (hH : H ≠ 0)
    (e0 : -A * B + A ^(2:ℕ) * H * Y2 * Y3 - B ^(2:ℕ) * H * Y1 * Y4 = 0)
    (e1 : -A * B * Y2 ^(2:ℕ) + A ^(2:ℕ) * Y4 - B ^(2:ℕ) * Y1 * Y3 = 0)
    (e2 : -A * B * H * Y4 ^(2:ℕ) + A ^(2:ℕ) * Y1 * Y2 - B ^(2:ℕ) * Y3 = 0)
    (e4 : -A * B * H * Y3 ^(2:ℕ) + A ^(2:ℕ) * Y1 - B ^(2:ℕ) * H * Y2 * Y4 = 0)
    (d1 : A * Y4 - B * Y2 ^(2:ℕ) = 0) (d2 : A * Y1 - B * H * Y3 ^(2:ℕ) = 0) : False := by
  have hAY4 : A * Y4 = B * Y2 ^(2:ℕ) := sub_eq_zero.mp d1
  have hAY1 : A * Y1 = B * H * Y3 ^(2:ℕ) := sub_eq_zero.mp d2
  have hmain : A ^(2:ℕ) * H * (Y2 * Y3) - B ^(2:ℕ) * H * (Y1 * Y4) = A * B := by
    linear_combination (norm := refl_ring1) e0
  have h13 : Y1 * Y3 = 0 := by
    have hkey : B ^(2:ℕ) * (Y1 * Y3) = 0 := by
      have h := e1
      have hA2 : A ^(2:ℕ) * Y4 = A * B * Y2 ^(2:ℕ) := by
        calc A ^(2:ℕ) * Y4 = A * (A * Y4) := by ring
          _ = A * (B * Y2 ^(2:ℕ)) := by rw [hAY4]
          _ = A * B * Y2 ^(2:ℕ) := by ring
      rw [hA2] at h
      linear_combination (norm := refl_ring1) (-1 : L) * h
    exact (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hB)
  have h24 : Y2 * Y4 = 0 := by
    have hkey : B ^(2:ℕ) * H * (Y2 * Y4) = 0 := by
      have h := e4
      have hA2 : A ^(2:ℕ) * Y1 = A * B * H * Y3 ^(2:ℕ) := by
        calc A ^(2:ℕ) * Y1 = A * (A * Y1) := by ring
          _ = A * (B * H * Y3 ^(2:ℕ)) := by rw [hAY1]
          _ = A * B * H * Y3 ^(2:ℕ) := by ring
      rw [hA2] at h
      linear_combination (norm := refl_ring1) (-1 : L) * h
    exact (mul_eq_zero.mp hkey).resolve_left (mul_ne_zero (pow_ne_zero 2 hB) hH)
  rcases mul_eq_zero.mp h13 with hY1 | hY3
  · -- `Y1 = 0`
    have hAB : A ^(2:ℕ) * H * (Y2 * Y3) = A * B := by
      have h := hmain
      rw [hY1] at h
      simpa using h
    have hne : Y2 * Y3 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hAB
      exact (mul_ne_zero hA hB) hAB.symm
    have hY2 : Y2 ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
    have hY4 : Y4 = 0 := by
      rcases mul_eq_zero.mp h24 with h | h
      · exact absurd h hY2
      · exact h
    have hY3' : Y3 = 0 := by
      have h := e2
      rw [hY1, hY4] at h
      have h' : B ^(2:ℕ) * Y3 = 0 := by linear_combination (-1 : L) * h
      exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hB)
    exact hne (by rw [hY3', mul_zero])
  · -- `Y3 = 0`
    have hAB : B ^(2:ℕ) * H * (Y1 * Y4) = -(A * B) := by
      have h := hmain
      rw [hY3] at h
      linear_combination (norm := refl_ring1) (-1 : L) * h
    have hne : Y1 * Y4 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hAB
      exact (mul_ne_zero hA hB) (neg_eq_zero.mp hAB.symm)
    have hY1' : Y1 ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
    have hY4' : Y4 ≠ 0 := fun hz => hne (by rw [hz, mul_zero])
    have hY2 : Y2 = 0 := by
      rcases mul_eq_zero.mp h24 with h | h
      · exact h
      · exact absurd h hY4'
    have hY4'' : Y4 = 0 := by
      have h := e2
      rw [hY2, hY3] at h
      have h' : A * B * H * Y4 ^(2:ℕ) = 0 := by linear_combination (-1 : L) * h
      rcases mul_eq_zero.mp h' with h3 | h3
      · exact absurd h3 (mul_ne_zero (mul_ne_zero hA hB) hH)
      · exact sq_eq_zero_iff.mp h3
    exact hY4' hY4''

/-- The zeroth twisted Klein coordinate is one. -/
private theorem pvz_sdY_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) : Work.MotK.TGen.sdY K D h 0 = 1 := by
  have h0 : Work.MotK.twCoordG K D h 0 = 1 := Work.MotK.TGen.twCoordG_zero K D hD h
  have hsub : (⟨Work.MotK.twCoordG K D h 0,
      IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
        (Set.mem_range_self 0)⟩ : ↥(Work.MotK.twistFieldTG K D h)) = 1 :=
    Subtype.ext h0
  rw [Work.MotK.TGen.sdY, hsub, map_one]

end Helpers

/-- **The zeroth coordinate of the inverse cubic map at the characteristic-two parametrisation is
nonzero.** -/
theorem kleinTwR_paramVec_zero_ne_zero (K : Type) [Field K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        (Work.MotK.TwRuling.paramVec K D h) 0 ≠ 0 := by
  set A : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) D.a with hAdef
  set B : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) D.b with hBdef
  set H : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) h with hHdef
  set Y : Fin 5 → Work.MotK.TGen.sdA K D h := Work.MotK.TGen.sdY K D h with hYdef
  -- the images of the Klein parameters in the target function field are units
  have hAne : A ≠ 0 := by
    rw [hAdef]
    intro hzero
    have hDa : D.a = 0 :=
      (algebraMap K (Work.MotK.TGen.sdA K D h)).injective (by rw [hzero, map_zero])
    exact hD.ab_ne (by rw [hDa, zero_mul])
  have hBne : B ≠ 0 := by
    rw [hBdef]
    intro hzero
    have hDb : D.b = 0 :=
      (algebraMap K (Work.MotK.TGen.sdA K D h)).injective (by rw [hzero, map_zero])
    exact hD.ab_ne (by rw [hDb, mul_zero])
  have hHne : H ≠ 0 := by
    rw [hHdef]
    intro hzero
    exact hh ((algebraMap K (Work.MotK.TGen.sdA K D h)).injective (by rw [hzero, map_zero]))
  have hY0 : Y 0 = 1 := by
    rw [hYdef]
    exact pvz_sdY_zero K D hD h
  have hPf : ∀ k : Fin 5, Work.MotK.kleinTwP A B H Y k = 0 := by
    intro k
    have hk := sdY_curve K D hD h hh k
    simpa only [← hAdef, ← hBdef, ← hHdef, ← hYdef] using hk
  -- the coefficients live in the twist field `F`
  set aF : ↥(Work.MotK.twistFieldTG K D h) :=
    algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a with haFdef
  set bF : ↥(Work.MotK.twistFieldTG K D h) :=
    algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b with hbFdef
  set hF0 : ↥(Work.MotK.twistFieldTG K D h) :=
    algebraMap K ↥(Work.MotK.twistFieldTG K D h) h with hhF0def
  set yF : Fin 5 → ↥(Work.MotK.twistFieldTG K D h) := fun i =>
    ⟨Work.MotK.twCoordG K D h i,
      IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
        (Set.mem_range_self i)⟩ with hyFdef
  have hAeq : A = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) aF := by
    rw [hAdef]
    exact IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
      (Work.MotK.TGen.sdA K D h) D.a
  have hBeq : B = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) bF := by
    rw [hBdef]
    exact IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
      (Work.MotK.TGen.sdA K D h) D.b
  have hHeq : H = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) hF0 := by
    rw [hHdef]
    exact IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
      (Work.MotK.TGen.sdA K D h) h
  have hYF : ∀ i : Fin 5, Y i = algebraMap ↥(Work.MotK.twistFieldTG K D h)
      (Work.MotK.TGen.sdA K D h) (yF i) := by
    intro i
    rw [hYdef]
    rfl
  -- the four coefficients of the bracket
  set d0F : ↥(Work.MotK.twistFieldTG K D h) :=
    aF ^(4:ℕ) * (yF 2) - bF ^(4:ℕ) * ((yF 1)) ^(2:ℕ) with hd0Fdef
  set c1F : ↥(Work.MotK.twistFieldTG K D h) :=
    aF ^(2:ℕ) * bF * hF0 * (aF * (yF 4) - bF * ((yF 2)) ^(2:ℕ)) with hc1Fdef
  set c2F : ↥(Work.MotK.twistFieldTG K D h) :=
    aF ^(2:ℕ) * bF * hF0 * (aF * (yF 1) - bF * hF0 * ((yF 3)) ^(2:ℕ)) with hc2Fdef
  set c3F : ↥(Work.MotK.twistFieldTG K D h) :=
    hF0 ^(2:ℕ) * (aF ^(4:ℕ) * (yF 3) - bF ^(4:ℕ) * hF0 * ((yF 4)) ^(2:ℕ)) with hc3Fdef
  have hd0 : A ^(4:ℕ) * (Y 2) - B ^(4:ℕ) * ((Y 1)) ^(2:ℕ)
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) d0F := by
    rw [hAeq, hBeq, hYF 2, hYF 1]
    simp only [← map_mul, ← map_pow, ← map_sub]
    rfl
  have hd1 : A ^(2:ℕ) * B * H * (A * (Y 4) - B * ((Y 2)) ^(2:ℕ))
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c1F := by
    rw [hAeq, hBeq, hHeq, hYF 4, hYF 2]
    simp only [← map_mul, ← map_pow, ← map_sub]
    rfl
  have hd2 : A ^(2:ℕ) * B * H * (A * (Y 1) - B * H * ((Y 3)) ^(2:ℕ))
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c2F := by
    rw [hAeq, hBeq, hHeq, hYF 1, hYF 3]
    simp only [← map_mul, ← map_pow, ← map_sub]
    rfl
  have hd3 : H ^(2:ℕ) * (A ^(4:ℕ) * (Y 3) - B ^(4:ℕ) * H * ((Y 4)) ^(2:ℕ))
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c3F := by
    rw [hAeq, hBeq, hHeq, hYF 3, hYF 4]
    simp only [← map_mul, ← map_pow, ← map_sub]
    rfl
  -- the cleared parametrisation point and the bracket
  set br : Work.MotK.TGen.sdA K D h :=
    (A ^(4:ℕ) * (Y 2) - B ^(4:ℕ) * ((Y 1)) ^(2:ℕ))
      + (A ^(2:ℕ) * B * H * (A * (Y 4) - B * ((Y 2)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h)
      + (A ^(2:ℕ) * B * H * (A * (Y 1) - B * H * ((Y 3)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(2:ℕ)
      + (H ^(2:ℕ) * (A ^(4:ℕ) * (Y 3) - B ^(4:ℕ) * H * ((Y 4)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(3:ℕ) with hbrdef
  set Zc : Fin 5 → Work.MotK.TGen.sdA K D h :=
    ![0, A * (RatFunc.X : Work.MotK.TGen.sdA K D h), A * (Y 2) + B * H * (Y 4) * (RatFunc.X : Work.MotK.TGen.sdA K D h), B * (Y 1) + A * H * (Y 3) * (RatFunc.X : Work.MotK.TGen.sdA K D h), A] with hZcdef
  have h2S : (2 : Work.MotK.TGen.sdA K D h) = 0 := by
    rw [← map_ofNat (algebraMap K (Work.MotK.TGen.sdA K D h)) 2, h2, map_zero]
  have hR0w : Work.MotK.kleinTwR0 A B H Zc = A ^(2:ℕ) * B * H * br := by
    rw [hZcdef, hbrdef]
    exact pvz_R0_w h2S A B H (Y 1) (Y 2) (Y 3) (Y 4) (RatFunc.X : Work.MotK.TGen.sdA K D h)
  -- the bracket is nonzero
  have hbrne : br ≠ 0 := by
    intro hbr0
    have h2' : (A ^(4:ℕ) * (Y 2) - B ^(4:ℕ) * ((Y 1)) ^(2:ℕ))
        + (A ^(2:ℕ) * B * H * (A * (Y 4) - B * ((Y 2)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h)
        + (A ^(2:ℕ) * B * H * (A * (Y 1) - B * H * ((Y 3)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(2:ℕ)
        + (H ^(2:ℕ) * (A ^(4:ℕ) * (Y 3) - B ^(4:ℕ) * H * ((Y 4)) ^(2:ℕ))) * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(3:ℕ) = 0 := by
      rw [← hbrdef]
      exact hbr0
    have h3 : algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) d0F
        + algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c1F * (RatFunc.X : Work.MotK.TGen.sdA K D h)
        + algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c2F * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(2:ℕ)
        + algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h) c3F * (RatFunc.X : Work.MotK.TGen.sdA K D h) ^(3:ℕ)
        = 0 := by
      rw [hd0, hd1, hd2, hd3] at h2'
      exact h2'
    obtain ⟨hc1, hc2⟩ := pvz_extract d0F c1F c2F c3F h3
    have hd1S : A * (Y 4) - B * ((Y 2)) ^(2:ℕ) = 0 := by
      have h : A ^(2:ℕ) * B * H * (A * (Y 4) - B * ((Y 2)) ^(2:ℕ)) = 0 := by rw [hd1, hc1, map_zero]
      exact (mul_eq_zero.mp h).resolve_left
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hHne)
    have hd2S : A * (Y 1) - B * H * ((Y 3)) ^(2:ℕ) = 0 := by
      have h : A ^(2:ℕ) * B * H * (A * (Y 1) - B * H * ((Y 3)) ^(2:ℕ)) = 0 := by rw [hd2, hc2, map_zero]
      exact (mul_eq_zero.mp h).resolve_left
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hHne)
    have e0 : -A * B + A ^(2:ℕ) * H * (Y 2) * (Y 3) - B ^(2:ℕ) * H * (Y 1) * (Y 4) = 0 := by
      have h := hPf 0
      simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP0, Matrix.cons_val_zero] at h
      rw [hY0] at h
      simpa using h
    have e1 : -A * B * (Y 2) ^(2:ℕ) + A ^(2:ℕ) * (Y 4) - B ^(2:ℕ) * (Y 1) * (Y 3) = 0 := by
      have h := hPf 1
      simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] at h
      rw [hY0] at h
      simpa using h
    have e2 : -A * B * H * (Y 4) ^(2:ℕ) + A ^(2:ℕ) * (Y 1) * (Y 2) - B ^(2:ℕ) * (Y 3) = 0 := by
      have h := hPf 2
      simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP2, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two] at h
      rw [hY0] at h
      simpa using h
    have e4 : -A * B * H * (Y 3) ^(2:ℕ) + A ^(2:ℕ) * (Y 1) - B ^(2:ℕ) * H * (Y 2) * (Y 4) = 0 := by
      have h := hPf 4
      simp only [Work.MotK.kleinTwP, Work.MotK.kleinTwP4, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four] at h
      rw [hY0] at h
      simpa using h
    exact pvz_contra A B H (Y 1) (Y 2) (Y 3) (Y 4) hAne hBne hHne e0 e1 e2 e4 hd1S hd2S
  -- the final assembly
  show Work.MotK.kleinTwR A B H (Work.MotK.TwRuling.paramVec K D h) 0 ≠ 0
  simp only [Work.MotK.kleinTwR, Matrix.cons_val_zero]
  intro hzero
  have hAB : A * (B / A) = B := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hAne]
  have hZc : Zc = A • Work.MotK.TwRuling.paramVec K D h := by
    rw [hZcdef]
    funext j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
    rcases hj with h | h | h | h | h <;> subst h
    · simp only [Work.MotK.TwRuling.paramVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hAdef, ← hBdef, ← hHdef]
      refl_ring1
    · simp only [Work.MotK.TwRuling.paramVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hAdef, ← hBdef, ← hHdef]
    · simp only [Work.MotK.TwRuling.paramVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hAdef, ← hBdef, ← hHdef]
      linear_combination (norm := refl_ring1) (-(H * (Y 4) * (RatFunc.X : Work.MotK.TGen.sdA K D h))) * hAB
    · simp only [Work.MotK.TwRuling.paramVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hAdef, ← hBdef, ← hHdef]
      linear_combination (norm := refl_ring1) (-((Y 1))) * hAB
    · simp only [Work.MotK.TwRuling.paramVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hAdef, ← hBdef, ← hHdef]
      refl_ring1
  have hhom : Work.MotK.kleinTwR0 A B H Zc
      = A ^(3:ℕ) * Work.MotK.kleinTwR0 A B H (Work.MotK.TwRuling.paramVec K D h) := by
    rw [hZc]
    exact pvz_smul0 A B H A (Work.MotK.TwRuling.paramVec K D h)
  have hze : Work.MotK.kleinTwR0 A B H Zc = 0 := by
    rw [hhom, hzero, mul_zero]
  have hbr0 : br = 0 := by
    have h := hR0w
    rw [hze] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hHne)
  exact hbrne hbr0

end Work.MotK.TwRuling
