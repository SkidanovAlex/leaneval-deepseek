import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.BwASDefs` — the explicit cubic `bwVecAS2 · 4` and its structure

The target chart denominator of the corrected AS chart is

  `bwVecAS2 a b g 4 = π_{e₀}(R^AS(tchart))₄ = (R^AS(tchart))₄`,

the fourth component of the inverse quadro-cubic map `R^AS` evaluated at the target chart vector
`tchart = (1, X₀, X₁, X₂, 0)` of `Work.MotAS.CensusAS2`.  This file unfolds that component
completely: it is the **cubic**

  `bwASpoly a b g = bwASQ a b g + bwASR a b g`,

where (with `d = a² − ab − b²`, `e = a² + b²`, `γ = 2a⁴ + a³b − 2a²b² − ab³ + 2b⁴`)

* `bwASQ = γ·X₁² − d²·X₀X₂ − 2·e·d·X₂²` (homogeneous of degree `2`),
* `bwASR = γ·X₀²X₁ − e·d·X₀X₁X₂ − 2·e·d·X₁³ + γ·X₁X₂² − g·d²·X₂³` (homogeneous of degree `3`).

The two facts that make this polynomial tractable are

* it is a cubic in `X₂` over `K[X₀,X₁]` with **unit** leading coefficient `κ = −g·d²`, and
* in characteristic `5` the scalar `γ` factors as `γ = 3·(b − 2a)²·d`, so that `d ≠ 0` forces
  `γ ≠ 0` (this is why `ASGood`'s non-degeneracy `a² − ab − b² ≠ 0` is exactly what makes the
  surface `{bwASpoly = 0}` a non-degenerate cubic surface).

The projective closure `{W·bwASQ + bwASR = 0} ⊆ ℙ³` is *linear in `W`*, hence birational to `ℙ²`
via `(X₀:X₁:X₂:W) ↦ (X₀:X₁:X₂)`; consequently the surface `{bwASpoly = 0} ⊆ 𝔸³` is rational and
the divisor `(bwASpoly)` of `𝔸³` is *junk* in the sense of `Work.MotV.JunkClass` — the content of
`Work.MotAS.censusAS2_junk_bwVec4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [CommRing K]

/-- `C 2 = 2` in `MvPolynomial (Fin 3) K`, usable as a `simp` lemma when pushing `C` inside an
expression (Mathlib's `map_ofNat` cannot fire on the bare function `C`; this version is stated for
the concrete numeral `2`, which is all that occurs in the definition of `bwASpoly`). -/
theorem C_two : (C (2 : K) : MvPolynomial (Fin 3) K) = 2 := map_ofNat _ 2

/-- The scalar `γ = 2a⁴ + a³b − 2a²b² − ab³ + 2b⁴` (the `X₀²X₁`- and `X₁²`-coefficient of the
cubic). -/
noncomputable def asGam (a b : K) : K := 2 * a ^ 4 + a ^ 3 * b - 2 * a ^ 2 * b ^ 2 - a * b ^ 3
  + 2 * b ^ 4

/-- The scalar `d = a² − ab − b²` (the Klein non-degeneracy; `d ≠ 0` is `ASGood`). -/
noncomputable def asDel (a b : K) : K := a ^ 2 - a * b - b ^ 2

/-- The scalar `e = a² + b²`. -/
noncomputable def asEps (a b : K) : K := a ^ 2 + b ^ 2

/-- **The degree-two part** of `bwVecAS2 · 4`: `γX₁² − d²X₀X₂ − 2edX₂²`. -/
noncomputable def bwASQ (a b g : K) : MvPolynomial (Fin 3) K :=
  C (asGam a b) * (X 1) ^ 2 - C ((asDel a b) ^ 2) * X 0 * X 2
    - C (2 * asEps a b * asDel a b) * (X 2) ^ 2

/-- **The degree-three part** of `bwVecAS2 · 4`:
`γX₀²X₁ − edX₀X₁X₂ − 2edX₁³ + γX₁X₂² − gd²X₂³`. -/
noncomputable def bwASR (a b g : K) : MvPolynomial (Fin 3) K :=
  C (asGam a b) * (X 0) ^ 2 * X 1 - C (asEps a b * asDel a b) * X 0 * X 1 * X 2
    - C (2 * asEps a b * asDel a b) * (X 1) ^ 3
    + C (asGam a b) * X 1 * (X 2) ^ 2 - C (g * (asDel a b) ^ 2) * (X 2) ^ 3

/-- **The explicit cubic `bwASpoly a b g = bwVecAS2 a b g 4`.** -/
noncomputable def bwASpoly (a b g : K) : MvPolynomial (Fin 3) K := bwASQ a b g + bwASR a b g

/-- **The target chart denominator is the explicit cubic.**  A `ring`-level evaluation of
`kleinRAS4` at `tchart = (1, X₀, X₁, X₂, 0)`. -/
theorem bwVecAS2_four_eq_bwASpoly (a b g : K) :
    bwVecAS2 a b g 4 = bwASpoly a b g := by
  simp only [bwVecAS2, Work.MotK.kleinTwPi, pAS0, tchart, kleinRAS, kleinRAS4,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  simp only [bwASpoly, bwASQ, bwASR, asGam, asDel, asEps]
  simp only [C_mul, C_add, C_sub, C_pow, C_two]
  first | refl_ring1 | ring

/-! ## The scalar identities in characteristic `5` -/

/-- **The scalar `γ` factors through the non-degeneracy `d = a² − ab − b²`**, in characteristic `5`:
`γ = 3·(b − 2a)²·d`.  (The identity holds up to the multiple `−5·(2a⁴ − 5a³b + a²b² + 2ab³ − b⁴)`
in general, which is why characteristic `5` is needed.) -/
theorem asGam_eq [CharP K 5] (a b : K) :
    asGam a b = 3 * (b - 2 * a) ^ 2 * asDel a b := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  rw [asGam, asDel]
  linear_combination (norm := first | refl_ring1 | ring1) (-2 * a ^ 4 + 5 * a ^ 3 * b - a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + b ^ 4) * h5

/-- **`3 ≠ 0` in characteristic `5`.** -/
theorem three_ne_zero [CharP K 5] [Nontrivial K] : (3 : K) ≠ 0 := by
  have h3 : (3 : K) * 2 = 1 := by
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    linear_combination (norm := first | refl_ring1 | ring1) h5
  intro h
  rw [h, zero_mul] at h3
  exact zero_ne_one h3

/-- **`b − 2a` does not vanish when `d = a² − ab − b²` does not** (characteristic `5`): if `b = 2a`
then `d = −5a² = 0`. -/
theorem sub_two_mul_ne_zero [CharP K 5] (a b : K) (hd : asDel a b ≠ 0) : b - 2 * a ≠ 0 := by
  intro h
  apply hd
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  rw [asDel]
  linear_combination (norm := first | refl_ring1 | ring1) (-a ^ 2) * h5 + (-(b + 3 * a)) * h

/-- **`γ ≠ 0` as soon as `d ≠ 0`**, in characteristic `5`. -/
theorem asGam_ne_zero [CharP K 5] [IsDomain K] (a b : K) (hd : asDel a b ≠ 0) :
    asGam a b ≠ 0 := by
  rw [asGam_eq a b]
  exact mul_ne_zero (mul_ne_zero three_ne_zero (pow_ne_zero 2 (sub_two_mul_ne_zero a b hd))) hd

/-- **`d² ≠ 0`** as soon as `d ≠ 0` (needed for the leading coefficient of the cubic in `X₂`). -/
theorem asDel_sq_ne_zero [IsDomain K] (a b : K) (hd : asDel a b ≠ 0) :
    (asDel a b) ^ 2 ≠ 0 := pow_ne_zero 2 hd

/-! ## Homogeneity of the two parts -/

/-- `X i` is homogeneous of degree `1` (specialised to `MvPolynomial (Fin 3) K`). -/
theorem isHomogeneous_X_fin3 (i : Fin 3) :
    (MvPolynomial.X i : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_X (R := K) i

/-- `C r * X i` is homogeneous of degree `1` (specialised to `MvPolynomial (Fin 3) K`). -/
theorem isHomogeneous_C_mul_X_fin3 (r : K) (i : Fin 3) :
    (MvPolynomial.C r * MvPolynomial.X i : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_C_mul_X (R := K) r i

/-- `C r * X i ^ n` is homogeneous of degree `n` (specialised to `MvPolynomial (Fin 3) K`). -/
theorem isHomogeneous_C_mul_X_pow_fin3 (r : K) (i : Fin 3) (n : ℕ) :
    (MvPolynomial.C r * MvPolynomial.X i ^ n : MvPolynomial (Fin 3) K).IsHomogeneous n :=
  MvPolynomial.isHomogeneous_C_mul_X_pow (R := K) r i n

/-- `bwASQ a b g` is homogeneous of degree `2`. -/
theorem bwASQ_isHomogeneous (a b g : K) : (bwASQ a b g).IsHomogeneous 2 := by
  have h1 : (C (asGam a b) * (X 1) ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    isHomogeneous_C_mul_X_pow_fin3 (asGam a b) 1 2
  have h2 : (C ((asDel a b) ^ 2) * X 0 * X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    (isHomogeneous_C_mul_X_fin3 ((asDel a b) ^ 2) 0).mul (isHomogeneous_X_fin3 2)
  have h3 : (C (2 * asEps a b * asDel a b) * (X 2) ^ 2 :
      MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
    isHomogeneous_C_mul_X_pow_fin3 (2 * asEps a b * asDel a b) 2 2
  rw [bwASQ]
  exact (h1.sub h2).sub h3

/-- `bwASR a b g` is homogeneous of degree `3`. -/
theorem bwASR_isHomogeneous (a b g : K) : (bwASR a b g).IsHomogeneous 3 := by
  have hA : (C (asGam a b) * (X 0) ^ 2 * X 1 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    (isHomogeneous_C_mul_X_pow_fin3 (asGam a b) 0 2).mul (isHomogeneous_X_fin3 1)
  have hB : (C (asEps a b * asDel a b) * X 0 * X 1 * X 2 :
      MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    ((isHomogeneous_C_mul_X_fin3 (asEps a b * asDel a b) 0).mul
      (isHomogeneous_X_fin3 1)).mul (isHomogeneous_X_fin3 2)
  have hC : (C (2 * asEps a b * asDel a b) * (X 1) ^ 3 :
      MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    isHomogeneous_C_mul_X_pow_fin3 (2 * asEps a b * asDel a b) 1 3
  have hD : (C (asGam a b) * X 1 * (X 2) ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    (isHomogeneous_C_mul_X_fin3 (asGam a b) 1).mul ((isHomogeneous_X_fin3 2).pow 2)
  have hE : (C (g * (asDel a b) ^ 2) * (X 2) ^ 3 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    isHomogeneous_C_mul_X_pow_fin3 (g * (asDel a b) ^ 2) 2 3
  rw [bwASR]
  exact (((hA.sub hB).sub hC).add hD).sub hE

/-- **`bwASQ` is the degree-`2` homogeneous component** of `bwASpoly`. -/
theorem homogeneousComponent_two (a b g : K) :
    homogeneousComponent 2 (bwASpoly a b g) = bwASQ a b g := by
  have hQ : homogeneousComponent 2 (bwASQ a b g) = bwASQ a b g :=
    homogeneousComponent_eq_self (bwASQ_isHomogeneous a b g)
  have hR : homogeneousComponent 2 (bwASR a b g) = 0 := by
    rw [homogeneousComponent_of_mem (show bwASR a b g ∈ homogeneousSubmodule (Fin 3) K 3 from
      bwASR_isHomogeneous a b g)]
    norm_num
  rw [bwASpoly, map_add, hQ, hR, add_zero]

/-- **`bwASR` is the degree-`3` homogeneous component** of `bwASpoly`. -/
theorem homogeneousComponent_three (a b g : K) :
    homogeneousComponent 3 (bwASpoly a b g) = bwASR a b g := by
  have hQ : homogeneousComponent 3 (bwASQ a b g) = 0 := by
    rw [homogeneousComponent_of_mem (show bwASQ a b g ∈ homogeneousSubmodule (Fin 3) K 2 from
      bwASQ_isHomogeneous a b g)]
    norm_num
  have hR : homogeneousComponent 3 (bwASR a b g) = bwASR a b g :=
    homogeneousComponent_eq_self (bwASR_isHomogeneous a b g)
  rw [bwASpoly, map_add, hQ, hR, zero_add]

/-! ## Non-vanishing of the cubic

The cubic is non-zero because its `X₂³`-coefficient `−g·d²` is a non-zero *constant*.  Rather than
computing a coefficient of a multivariate polynomial, we evaluate the cubic at the generic point
`(X₀,X₁,X₂) = (t,1,0)` of a line: the value is `γ·t² + (γ − 2ed) ∈ K[t]`, a quadratic whose
leading coefficient `γ` is non-zero. -/

/-- **The cubic evaluated at `(X₀, X₁, X₂) = (t, 1, 0)`**: `γ·t² + (γ − 2ed)`. -/
theorem aeval_bwASpoly_aux (a b g : K) :
    MvPolynomial.aeval (fun i : Fin 3 =>
        (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASpoly a b g)
      = Polynomial.C (asGam a b) * Polynomial.X ^ 2
        + Polynomial.C (asGam a b - 2 * asEps a b * asDel a b) := by
  simp only [bwASpoly, bwASQ, bwASR, asGam, asDel, asEps]
  simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  norm_num
  first | refl_ring1 | ring

/-- Coefficient of `t²` in the value at `(t,1,0)`. -/
theorem coeff_two_aeval_bwASpoly_aux (a b g : K) :
    (MvPolynomial.aeval (fun i : Fin 3 =>
        (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASpoly a b g)).coeff 2
      = asGam a b := by
  rw [aeval_bwASpoly_aux]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]
  norm_num

/-- **The cubic is non-zero** as soon as `d ≠ 0` (the `X₂³`-coefficient `−g·d²` is non-zero when
`g ≠ 0`, but the evaluation below only needs `d ≠ 0`). -/
theorem bwASpoly_ne_zero [CharP K 5] [IsDomain K] (a b g : K) (hd : asDel a b ≠ 0)
    (_hg : g ≠ 0) : bwASpoly a b g ≠ 0 := by
  intro h
  have h3 := coeff_two_aeval_bwASpoly_aux (K := K) a b g
  have h2 : (MvPolynomial.aeval (fun i : Fin 3 =>
      (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASpoly a b g)) = 0 := by
    rw [h]
    exact map_zero _
  rw [h2] at h3
  simp only [Polynomial.coeff_zero] at h3
  exact asGam_ne_zero a b hd h3.symm

/-! ## The cubic as a polynomial in `X₂`, and the two homogeneous parts

These are the shapes in which the children of `BwASDefs` use the cubic: the collected form
`bwASpoly = C κ · X₂³ + α·X₂² + β·X₂ + δ` with `κ = −g d²` a unit of `K[X₀,X₁]`, and the
non-vanishing of the two homogeneous parts `bwASQ` (degree 2) and `bwASR` (degree 3). -/

/-- **The cubic collected in `X₂`**: `bwASpoly = C κ X₂³ + α X₂² + β X₂ + δ` with
`κ = −g·d²`, `α = C γ X₁ − C (2ed)`, `β = −C (ed) X₀X₁ − C (d²) X₀` and
`δ = C γ X₀²X₁ − C (2ed) X₁³ + C γ X₁²`. -/
theorem bwASpoly_decomp (a b g : K) :
    bwASpoly a b g
      = -(C (g * (asDel a b) ^ 2)) * (X 2) ^ 3
        + (C (asGam a b) * X 1 - C (2 * asEps a b * asDel a b)) * (X 2) ^ 2
        + (-(C (asEps a b * asDel a b) * X 0 * X 1) - C ((asDel a b) ^ 2) * X 0) * X 2
        + (C (asGam a b) * (X 0) ^ 2 * X 1 - C (2 * asEps a b * asDel a b) * (X 1) ^ 3
            + C (asGam a b) * (X 1) ^ 2) := by
  simp only [bwASpoly, bwASQ, bwASR]
  first | refl_ring1 | ring

/-- **The degree-two part is non-zero** as soon as `γ ≠ 0`: its value at `(X₀,X₁,X₂) = (t,1,0)` is
the constant `γ`. -/
theorem bwASQ_ne_zero (a b g : K) (hγ : asGam a b ≠ 0) : bwASQ a b g ≠ 0 := by
  intro h
  have h1 : MvPolynomial.aeval (fun i : Fin 3 =>
      (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASQ a b g)
      = Polynomial.C (asGam a b) := by
    simp only [bwASQ, asGam, asDel, asEps]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Polynomial.algebraMap_eq]
    norm_num
    try ring
  have h2 : (MvPolynomial.aeval (fun i : Fin 3 =>
      (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASQ a b g)) = 0 := by
    rw [h]
    exact map_zero _
  rw [h2] at h1
  have h3 := congrArg (fun p : Polynomial K => p.coeff 0) h1
  simp only [Polynomial.coeff_C, Polynomial.coeff_zero] at h3
  exact hγ h3.symm

/-- **The degree-three part is non-zero** as soon as `γ ≠ 0`: its value at `(X₀,X₁,X₂) = (t,1,0)`
is `γt² − 2ed`, a quadratic with leading coefficient `γ`. -/
theorem bwASR_ne_zero (a b g : K) [NoZeroDivisors K] (hγ : asGam a b ≠ 0) :
    bwASR a b g ≠ 0 := by
  intro h
  have h1 : MvPolynomial.aeval (fun i : Fin 3 =>
      (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASR a b g)
      = Polynomial.C (asGam a b) * Polynomial.X ^ 2
        - Polynomial.C (2 * asEps a b * asDel a b) := by
    simp only [bwASR, asGam, asDel, asEps]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Polynomial.algebraMap_eq]
    norm_num
    try ring
  have h2 : (MvPolynomial.aeval (fun i : Fin 3 =>
      (![Polynomial.X, 1, 0] : Fin 3 → Polynomial K) i) (bwASR a b g)) = 0 := by
    rw [h]
    exact map_zero _
  rw [h2] at h1
  have h3 := congrArg (fun p : Polynomial K => p.coeff 2) h1
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_zero] at h3
  norm_num at h3
  exact hγ h3.symm

end Work.MotAS
