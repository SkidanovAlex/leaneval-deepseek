import Mathlib
import Submission.Work.MotK.TwRuling.ParamVec
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotK.TwRuling

/-!
# The parametrised ruling point in characteristic two

`Work.MotK.TwRuling.paramVec K D h = ![0, t, y₂ + (b/a) h y₄ t, (b/a) y₁ + h y₃ t, 1]` is the
characteristic-two parametrisation of the target ruling divisor (see
`Submission/Work/MotK/TwRuling/SdualTClass_charTwo.lean`).  The content of this file is that the
inverse cubic map `kleinTwR` is projectively constant along this parametrisation:

  `kleinTwR (paramVec) i = (sdY i) · kleinTwR (paramVec) 0`.

This is *not* the ruling identity `KleinTwRuleEval`: in characteristic `2` the two ruling vectors
`A(y)`, `B(y)` coincide (`kleinTwBilin c (kleinE 0) = -2ab c₀ = 0`), so the ruling "line" of `y`
degenerates to a point and `paramVec` is genuinely *not* on it.  The proof is therefore a direct
certificate: after clearing the denominators by `a` and using the homogeneity
`kleinTwR (c • y) = c³ • kleinTwR y`, the claim becomes the polynomial identity
`R_i(w) - y_i R_0(w) ≡ 0` where `w = ![0, at, a y₂ + b h y₄ t, b y₁ + a h y₃ t, a]`, the relations
being the five twisted Pfaffians `kleinTwP` evaluated at `![1, y₁, y₂, y₃, y₄]`.

Over `ℤ` the cofactor combination carries an exact residual `2 · Q` — the difference vanishes only
modulo `2`.  We record the residual explicitly (`kleinTwR_cert_*` below) so that the Lean proof
never needs `ring` to know that `2 = 0`; the hypothesis `(2 : K) = 0` is applied afterwards.
-/

/-- `fin_cases` on `Fin 5` produces proof-carrying literals `⟨k, _⟩`; these `rfl` lemmas turn them
back into the standard literals so that the `Matrix.cons_val_*` simplification lemmas apply. -/
private theorem f5_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
private theorem f5_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
private theorem f5_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
private theorem f5_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
private theorem f5_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl

/-- The affine chart vector `![1, y₁, y₂, y₃, y₄]` of the twisted Klein coordinates (`y₀ = 1`). -/
noncomputable def chartVec {R : Type} [CommRing R] (y1 y2 y3 y4 : R) : Fin 5 → R :=
  ![1, y1, y2, y3, y4]

/-- The cleared parametrisation point `a • paramVec`, i.e.
`![0, a t, a y₂ + b h y₄ t, b y₁ + a h y₃ t, a]`. -/
noncomputable def wVec {R : Type} [CommRing R] (a b h t y1 y2 y3 y4 : R) : Fin 5 → R :=
  ![0, a * t, a * y2 + b * h * y4 * t, b * y1 + a * h * y3 * t, a]

/-! ## The four certificates (polynomial identities over any commutative ring) -/

theorem kleinTwR_cert_one {R : Type} [CommRing R] (a b h t y1 y2 y3 y4 : R) :
    Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) (1 : Fin 5)
      - chartVec y1 y2 y3 y4 (1 : Fin 5)
          * Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) 0
    = (a ^(5:ℕ) * h * t + a ^(2:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(3:ℕ) * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 0
      + (a ^(2:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) * t * y2)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 2
      + (a ^(4:ℕ) * b * h ^(2:ℕ) * t ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) * t * y3)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 3
      + (a ^(4:ℕ) * b * h ^(3:ℕ) * t ^(3:ℕ) * y3 + a ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 4
      + 2 * (-a ^(7:ℕ) * h ^(2:ℕ) * t * y2 * y3 - a ^(6:ℕ) * b * h ^(3:ℕ) * t ^(3:ℕ) * y1 * y3
            - a ^(6:ℕ) * b * h ^(3:ℕ) * t ^(2:ℕ) * y3 * y4 + a ^(6:ℕ) * b * h * t - a ^(6:ℕ) * b * h * y1 * y2
            + a ^(5:ℕ) * b ^(2:ℕ) * h ^(4:ℕ) * t ^(3:ℕ) * y3 ^(3:ℕ) - a ^(5:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t * y1 * y4
            + 2 * a ^(4:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y1 * y3 ^(2:ℕ)
            + a ^(3:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y1 * y2 * y4
            + a ^(3:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) * t * y2 * y4 ^(2:ℕ)
            + 3 * a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ) * t * y1 ^(2:ℕ) * y3
            + a ^(2:ℕ) * b ^(5:ℕ) * h ^(4:ℕ) * t ^(3:ℕ) * y1 * y4 ^(2:ℕ) + a ^(2:ℕ) * b ^(5:ℕ) * h ^(2:ℕ) * t * y2 * y3
            + a ^(2:ℕ) * b ^(5:ℕ) * h * y1 ^(3:ℕ)) := by
  simp only [wVec, chartVec, Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
    Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.kleinTwP,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3,
    Work.MotK.kleinTwP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  first | refl_ring1 | ring

theorem kleinTwR_cert_two {R : Type} [CommRing R] (a b h t y1 y2 y3 y4 : R) :
    Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) (2 : Fin 5)
      - chartVec y1 y2 y3 y4 (2 : Fin 5)
          * Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) 0
    = (a ^(4:ℕ) * b * h ^(2:ℕ) * t ^(3:ℕ))
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 0
      + (a ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t * y2)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 1
      + (a ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) + a * b ^(4:ℕ) * h ^(2:ℕ) * t * y3)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 2
      + (b ^(5:ℕ) * h ^(2:ℕ) * t * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 3
      + (a ^(2:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(3:ℕ) * y4 + b ^(5:ℕ) * h * t)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 4
      + 2 * (-a ^(6:ℕ) * b * h ^(3:ℕ) * t ^(3:ℕ) * y2 * y3 + a ^(5:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(3:ℕ)
            - a ^(5:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y1 * y2 + a ^(4:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y4 ^(2:ℕ)
            + a ^(4:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) * t * y2 ^(3:ℕ) + a ^(3:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y2 ^(2:ℕ) * y4
            + a ^(2:ℕ) * b ^(5:ℕ) * h ^(4:ℕ) * t ^(3:ℕ) * y2 * y4 ^(2:ℕ)
            - a ^(2:ℕ) * b ^(5:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y1 * y3 * y4 - a ^(2:ℕ) * b ^(5:ℕ) * h * t * y1
            + a * b ^(6:ℕ) * h ^(2:ℕ) * t * y3 ^(2:ℕ) + b ^(7:ℕ) * h ^(2:ℕ) * t * y2 * y4) := by
  simp only [wVec, chartVec, Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
    Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.kleinTwP,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3,
    Work.MotK.kleinTwP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  first | refl_ring1 | ring

theorem kleinTwR_cert_three {R : Type} [CommRing R] (a b h t y1 y2 y3 y4 : R) :
    Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) (3 : Fin 5)
      - chartVec y1 y2 y3 y4 (3 : Fin 5)
          * Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) 0
    = (a ^(4:ℕ) * b + a * b ^(4:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 0
      + (a * b ^(4:ℕ) * h * y2)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 2
      + (a ^(3:ℕ) * b ^(2:ℕ) * h * t + a * b ^(4:ℕ) * h * y3)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 3
      + (a ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y3 + a ^(2:ℕ) * b ^(3:ℕ) * h * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 4
      + 2 * (-a ^(6:ℕ) * b * h * y2 * y3 - a ^(5:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t * y3 * y4 + a ^(5:ℕ) * b ^(2:ℕ)
            + a ^(4:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y3 ^(3:ℕ) + a ^(4:ℕ) * b ^(3:ℕ) * h * t * y1 ^(2:ℕ)
            + a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ) * t * y1 * y3 ^(2:ℕ) - a ^(3:ℕ) * b ^(4:ℕ) * h * y1 * y2 ^(2:ℕ)
            - a ^(2:ℕ) * b ^(5:ℕ) * h ^(2:ℕ) * t * y1 * y2 * y4 + a ^(2:ℕ) * b ^(5:ℕ) * h ^(2:ℕ) * y2 * y4 ^(2:ℕ)
            + a ^(2:ℕ) * b ^(5:ℕ) * h * y1 ^(2:ℕ) * y3 + a * b ^(6:ℕ) * h * y2 * y3) := by
  simp only [wVec, chartVec, Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
    Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.kleinTwP,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3,
    Work.MotK.kleinTwP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  first | refl_ring1 | ring

theorem kleinTwR_cert_four {R : Type} [CommRing R] (a b h t y1 y2 y3 y4 : R) :
    Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) (4 : Fin 5)
      - chartVec y1 y2 y3 y4 (4 : Fin 5)
          * Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) 0
    = (a ^(5:ℕ) * h * t ^(2:ℕ))
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 0
      + (a ^(4:ℕ) * b * h * y2)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 1
      + (a ^(4:ℕ) * b * h * t + a ^(2:ℕ) * b ^(3:ℕ) * h * y3)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 2
      + (a * b ^(4:ℕ) * h * y4)
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 3
      + (a ^(3:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y4 + a * b ^(4:ℕ))
        * Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) 4
      + 2 * (-a ^(7:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y2 * y3 - a ^(6:ℕ) * b * h ^(3:ℕ) * t ^(3:ℕ) * y3 * y4
            + a ^(6:ℕ) * b * h * t ^(2:ℕ) - a ^(6:ℕ) * b * h * t * y1 * y2 - a ^(6:ℕ) * b * h * y2 * y4
            - a ^(5:ℕ) * b ^(2:ℕ) * h ^(2:ℕ) * t ^(2:ℕ) * y1 * y4 + a ^(5:ℕ) * b ^(2:ℕ) * h * y2 ^(3:ℕ)
            + a ^(4:ℕ) * b ^(3:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y3 ^(2:ℕ) * y4
            + 2 * a ^(4:ℕ) * b ^(3:ℕ) * h ^(2:ℕ) * t * y2 ^(2:ℕ) * y4
            + 3 * a ^(3:ℕ) * b ^(4:ℕ) * h ^(3:ℕ) * t ^(2:ℕ) * y2 * y4 ^(2:ℕ)
            + a ^(3:ℕ) * b ^(4:ℕ) * h ^(2:ℕ) * t * y1 * y3 * y4 - a ^(3:ℕ) * b ^(4:ℕ) * y1
            + a ^(2:ℕ) * b ^(5:ℕ) * h ^(4:ℕ) * t ^(3:ℕ) * y4 ^(3:ℕ) + a ^(2:ℕ) * b ^(5:ℕ) * h * y1 ^(2:ℕ) * y4
            + a ^(2:ℕ) * b ^(5:ℕ) * h * y3 ^(2:ℕ) + a * b ^(6:ℕ) * h * y2 * y4) := by
  simp only [wVec, chartVec, Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
    Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.kleinTwP,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3,
    Work.MotK.kleinTwP4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  first | refl_ring1 | ring

/-! ## The abstract characteristic-two statement -/

/-- Homogeneity of the twisted inverse map: `kleinTwR a b h (c • y) = c³ • kleinTwR a b h y`. -/
theorem kleinTwR_smul' {R : Type} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwR a b h (c • y) = c ^(3:ℕ) • Work.MotK.kleinTwR a b h y := by
  funext k
  fin_cases k
  · show Work.MotK.kleinTwR0 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR0 a b h y
    simp only [Work.MotK.kleinTwR0, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR1 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR1 a b h y
    simp only [Work.MotK.kleinTwR1, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR2 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR2 a b h y
    simp only [Work.MotK.kleinTwR2, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR3 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR3 a b h y
    simp only [Work.MotK.kleinTwR3, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR4 a b h (c • y) = c ^(3:ℕ) * Work.MotK.kleinTwR4 a b h y
    simp only [Work.MotK.kleinTwR4, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring

/-- **The characteristic-two parametrised ruling identity**, in the cleared coordinates
`wVec = a • paramVec`.  It is a formal consequence of the five twisted Pfaffians `kleinTwP` at
`![1, y₁, y₂, y₃, y₄]` together with `2 = 0`. -/
theorem kleinTwR_wVec {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    (a b h t y1 y2 y3 y4 : R)
    (hp : ∀ k : Fin 5, Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) k = 0) :
    ∀ i : Fin 5,
      Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) i
        = chartVec y1 y2 y3 y4 i
            * Work.MotK.kleinTwR a b h (wVec a b h t y1 y2 y3 y4) 0 := by
  intro i
  have h0 : Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) (0 : Fin 5) = 0 := hp 0
  have h1 : Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) (1 : Fin 5) = 0 := hp 1
  have h2' : Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) (2 : Fin 5) = 0 := hp 2
  have h3 : Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) (3 : Fin 5) = 0 := hp 3
  have h4 : Work.MotK.kleinTwP a b h (chartVec y1 y2 y3 y4) (4 : Fin 5) = 0 := hp 4
  fin_cases i
  · simp only [Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, chartVec, wVec, f5_0, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, one_mul]
  · have hc := kleinTwR_cert_one a b h t y1 y2 y3 y4
    simp only [h0, h1, h2', h3, h4, mul_zero, add_zero, h2, zero_mul] at hc
    simp only [f5_1] at hc ⊢
    exact sub_eq_zero.mp hc
  · have hc := kleinTwR_cert_two a b h t y1 y2 y3 y4
    simp only [h0, h1, h2', h3, h4, mul_zero, add_zero, h2, zero_mul] at hc
    simp only [f5_2] at hc ⊢
    exact sub_eq_zero.mp hc
  · have hc := kleinTwR_cert_three a b h t y1 y2 y3 y4
    simp only [h0, h1, h2', h3, h4, mul_zero, add_zero, h2, zero_mul] at hc
    simp only [f5_3] at hc ⊢
    exact sub_eq_zero.mp hc
  · have hc := kleinTwR_cert_four a b h t y1 y2 y3 y4
    simp only [h0, h1, h2', h3, h4, mul_zero, add_zero, h2, zero_mul] at hc
    simp only [f5_4] at hc ⊢
    exact sub_eq_zero.mp hc

/-! ## The zeroth twisted coordinate -/

theorem sdY_zero' (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) :
    Work.MotK.TGen.sdY K D h 0 = 1 := by
  have h0 : Work.MotK.twCoordG K D h 0 = 1 := Work.MotK.TGen.twCoordG_zero K D hD h
  have hsub : (⟨Work.MotK.twCoordG K D h 0,
      IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
        (Set.mem_range_self 0)⟩ : ↥(Work.MotK.twistFieldTG K D h)) = 1 :=
    Subtype.ext h0
  rw [Work.MotK.TGen.sdY, hsub, map_one]

/-! ## The target -/

theorem kleinTwR_param (K : Type) [Field K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (Work.MotK.TwRuling.paramVec K D h) i
        = Work.MotK.TGen.sdY K D h i *
          Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (Work.MotK.TwRuling.paramVec K D h) 0 := by
  intro i
  set A : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) D.a with hA
  set B : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) D.b with hB
  set H : Work.MotK.TGen.sdA K D h := algebraMap K (Work.MotK.TGen.sdA K D h) h with hH
  have h2R : (2 : Work.MotK.TGen.sdA K D h) = 0 := by
    rw [← map_ofNat (algebraMap K (Work.MotK.TGen.sdA K D h)) 2, h2, map_zero]
  have hA_ne : (A : Work.MotK.TGen.sdA K D h) ≠ 0 := by
    rw [hA]
    intro hzero
    have hDa : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
    exact hDa ((algebraMap K (Work.MotK.TGen.sdA K D h)).injective (by rw [hzero, map_zero]))
  set Y := Work.MotK.TGen.sdY K D h with hY
  have hY0 : Y 0 = 1 := by rw [hY]; exact sdY_zero' K D hD h
  have hYeq : Y = chartVec (Y 1) (Y 2) (Y 3) (Y 4) := by
    funext j
    fin_cases j
    · simpa only [chartVec, f5_0, Matrix.cons_val_zero] using hY0
    · simp only [chartVec, f5_1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
    · simp only [chartVec, f5_2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
    · simp only [chartVec, f5_3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
    · simp only [chartVec, f5_4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  have hp : ∀ k : Fin 5, Work.MotK.kleinTwP A B H (chartVec (Y 1) (Y 2) (Y 3) (Y 4)) k = 0 := by
    intro k
    have h := sdY_curve K D hD h hh k
    rw [← hYeq, hY, hA, hB, hH]
    exact h
  -- the parametrisation point is `A • paramVec`
  have hAB : A * (B / A) = B := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hA_ne]
  have hw : wVec A B H (RatFunc.X) (Y 1) (Y 2) (Y 3) (Y 4)
      = A • Work.MotK.TwRuling.paramVec K D h := by
    funext j
    fin_cases j
    · simp only [wVec, Work.MotK.TwRuling.paramVec, f5_0, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hA, ← hB,
        ← hH, ← hY]
      try ring
    · simp only [wVec, Work.MotK.TwRuling.paramVec, f5_1, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hA, ← hB,
        ← hH, ← hY]
      try ring
    · simp only [wVec, Work.MotK.TwRuling.paramVec, f5_2, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hA, ← hB,
        ← hH, ← hY]
      rw [mul_add]
      congr 1
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hAB]
      try ring
    · simp only [wVec, Work.MotK.TwRuling.paramVec, f5_3, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hA, ← hB,
        ← hH, ← hY]
      rw [mul_add]
      congr 1
      rw [← mul_assoc, hAB]
      try ring
    · simp only [wVec, Work.MotK.TwRuling.paramVec, f5_4, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Pi.smul_apply, smul_eq_mul, ← hA, ← hB,
        ← hH, ← hY]
      try ring
  have hmain := kleinTwR_wVec h2R A B H (RatFunc.X) (Y 1) (Y 2) (Y 3) (Y 4) hp i
  rw [hw] at hmain
  rw [congrFun (kleinTwR_smul' A B H A (Work.MotK.TwRuling.paramVec K D h)) i,
    congrFun (kleinTwR_smul' A B H A (Work.MotK.TwRuling.paramVec K D h)) 0] at hmain
  simp only [Pi.smul_apply, smul_eq_mul] at hmain
  have hYi : chartVec (Y 1) (Y 2) (Y 3) (Y 4) i = Y i := (congrFun hYeq i).symm
  rw [hYi] at hmain
  have hA3 : (A : Work.MotK.TGen.sdA K D h) ^(3:ℕ) ≠ 0 := pow_ne_zero 3 hA_ne
  refine mul_left_cancel₀ hA3 ?_
  rw [hmain]
  first | refl_ring1 | ring

end Work.MotK.TwRuling
