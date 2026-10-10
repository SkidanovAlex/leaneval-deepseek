import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.censusAS2_fwVec0_ne_zero` — the `0`-th component of the corrected AS chart map

This file proves that the source denominator of the *corrected* AS Crauder–Katz chart,

  `f̂₀ = fwVecAS2 (aK D) (bK D) (fAS 𝕜) 0`

(`Submission/Work/MotAS/CensusAS2.lean`, where `fwVecAS2 a b g = kleinPAS a b g ∘ kleinStereoAS`
evaluated at the source chart vector `chart3 = (0,X₀,X₁,X₂,1)` and the stereographic point
`pAS0 = e₀ = (1,0,0,0,0)`), is **not the zero polynomial** for an `ASGood` Klein datum.  It is one
of the four non-vanishing inputs of `FdivAS2_ne_zero_of` / `GdivAS2_ne_zero_of`
(`Submission/Work/MotAS/CensusAS2Aux.lean`).

## Proof

`f̂₀` is a polynomial of total degree `4` in `X₀,X₁,X₂`; contrary to the *old* chart point
`pAS = 288 · e₀` (where evaluating at the origin of the chart gives the polynomial
`-82944 · a b (a²−ab−b²)(4a²−ab−4b²)`, which may vanish for admissible `(a,b)`), the corrected
component is detected by **two** points of the chart:

* at the origin `(0,0,0)` the value is `a b (a²+b²)²` (`aeval_zero_fwVecAS2_zero`);
* at `(0,1,0)` the value is `-b² (a²−ab−b²)(2a²+ab+b²)` (`aeval_010_fwVecAS2_zero`).

If both vanished, then from the first `a²+b² = 0` (as `a b ≠ 0`) and from the second
`2a²+ab+b² = 0` (as `b² ≠ 0` and `a²−ab−b² ≠ 0`); subtracting twice the first from the second
gives `b(a−b) = 0`, hence `a = b`, whence `2a² = a²+b² = 0`, i.e. `a = 0` (as `2 ≠ 0` in
characteristic `5`) — contradicting `a ≠ 0`.

The two evaluation lemmas are stated in characteristic `5` (they are *not* identities over `ℤ`:
over `ℤ` the values are `-a b (a²−ab−b²)(4a²−ab−4b²)` and
`(a²−ab−b²)(25a⁴−20a³b+18a²b²+4ab³+9b⁴)`, and the difference is exactly `5 × (…)`); each is
proved by first establishing the `ℤ`-identity with `ring`, and then reducing modulo
`5 = 0` using `sub_eq_zero`.
-/

set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

/-- **The value of `fwVecAS2 · 0` at the origin of the chart** is `a b (a²+b²)²` in
characteristic `5` (over `ℤ` it is `-a b (a²−ab−b²)(4a²−ab−4b²)`). -/
theorem aeval_zero_fwVecAS2_zero {K : Type*} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) (fwVecAS2 a b g 0)
      = a * b * (a ^ 2 + b ^ 2) ^ 2 := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hcc : MvPolynomial.constantCoeff (2 : MvPolynomial (Fin 3) K) = (2 : K) :=
    map_natCast MvPolynomial.constantCoeff 2
  have hZ : MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) (fwVecAS2 a b g 0)
      = -(a * b * ((a ^ 2 - a * b - b ^ 2) * (4 * a ^ 2 - a * b - 4 * b ^ 2))) := by
    simp only [fwVecAS2, kleinPAS, kleinPAS0, kleinStereoAS, kleinBilinAS, kleinQAS, pAS0,
      Work.MotK.chart3, Pi.add_apply, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    simp
    try simp only [hcc]
    first | refl_ring1 | ring
  rw [hZ]
  have hk : -(a * b * ((a ^ 2 - a * b - b ^ 2) * (4 * a ^ 2 - a * b - 4 * b ^ 2)))
        - a * b * (a ^ 2 + b ^ 2) ^ 2
      = (5 : K) * (-(a * b * (a ^ 4 - a ^ 3 * b - a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4))) := by ring
  have h2 : -(a * b * ((a ^ 2 - a * b - b ^ 2) * (4 * a ^ 2 - a * b - 4 * b ^ 2)))
        - a * b * (a ^ 2 + b ^ 2) ^ 2 = 0 := by rw [hk, h5, zero_mul]
  exact sub_eq_zero.mp h2

/-- **The value of `fwVecAS2 · 0` at `(X₀,X₁,X₂) = (0,1,0)`** is `-b² (a²−ab−b²)(2a²+ab+b²)` in
characteristic `5`. -/
theorem aeval_010_fwVecAS2_zero {K : Type*} [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.aeval (fun i : Fin 3 => (![0, 1, 0] : Fin 3 → K) i) (fwVecAS2 a b g 0)
      = -(b ^ 2 * (a ^ 2 - a * b - b ^ 2) * (2 * a ^ 2 + a * b + b ^ 2)) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hcc : MvPolynomial.constantCoeff (2 : MvPolynomial (Fin 3) K) = (2 : K) :=
    map_natCast MvPolynomial.constantCoeff 2
  have hZ : MvPolynomial.aeval (fun i : Fin 3 => (![0, 1, 0] : Fin 3 → K) i)
        (fwVecAS2 a b g 0)
      = (a ^ 2 - a * b - b ^ 2) * (25 * a ^ 4 - 20 * a ^ 3 * b + 18 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3
          + 9 * b ^ 4) := by
    simp only [fwVecAS2, kleinPAS, kleinPAS0, kleinStereoAS, kleinBilinAS, kleinQAS, pAS0,
      Work.MotK.chart3, Pi.add_apply, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]
    simp
    try simp only [hcc]
    first | refl_ring1 | ring
  rw [hZ]
  have hk : (a ^ 2 - a * b - b ^ 2) * (25 * a ^ 4 - 20 * a ^ 3 * b + 18 * a ^ 2 * b ^ 2
          + 4 * a * b ^ 3 + 9 * b ^ 4)
        - -(b ^ 2 * (a ^ 2 - a * b - b ^ 2) * (2 * a ^ 2 + a * b + b ^ 2))
      = (5 : K) * ((a ^ 2 - a * b - b ^ 2) * (5 * a ^ 4 - 4 * a ^ 3 * b + 4 * a ^ 2 * b ^ 2
          + a * b ^ 3 + 2 * b ^ 4)) := by ring
  have h2 : (a ^ 2 - a * b - b ^ 2) * (25 * a ^ 4 - 20 * a ^ 3 * b + 18 * a ^ 2 * b ^ 2
          + 4 * a * b ^ 3 + 9 * b ^ 4)
        - -(b ^ 2 * (a ^ 2 - a * b - b ^ 2) * (2 * a ^ 2 + a * b + b ^ 2)) = 0 := by
    rw [hk, h5, zero_mul]
  exact sub_eq_zero.mp h2

/-- **`fwVecAS2 · 0` does not vanish** as soon as `a b ≠ 0` and `a² − ab − b² ≠ 0`: the two chart
points `(0,0,0)` and `(0,1,0)` together detect the polynomial. -/
theorem fwVecAS2_zero_ne_zero_gen {K : Type*} [Field K] [CharP K 5] (a b g : K) (ha : a ≠ 0)
    (hb : b ≠ 0) (hu : a ^ 2 - a * b - b ^ 2 ≠ 0) : fwVecAS2 a b g 0 ≠ 0 := by
  by_cases hz : MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) (fwVecAS2 a b g 0) = 0
  · intro hP
    have h1 : MvPolynomial.aeval (fun i : Fin 3 => (![0, 1, 0] : Fin 3 → K) i)
        (fwVecAS2 a b g 0) = 0 := by rw [hP, map_zero]
    rw [aeval_010_fwVecAS2_zero (a := a) (b := b) (g := g)] at h1
    rw [aeval_zero_fwVecAS2_zero (a := a) (b := b) (g := g)] at hz
    have hq : 2 * a ^ 2 + a * b + b ^ 2 = 0 := by
      have h1' : b ^ 2 * (a ^ 2 - a * b - b ^ 2) * (2 * a ^ 2 + a * b + b ^ 2) = 0 := by
        simpa using neg_eq_zero.mp h1
      rcases mul_eq_zero.mp h1' with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (pow_ne_zero 2 hb)
        · exact absurd h' hu
      · exact h
    have ha2b2 : a ^ 2 + b ^ 2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' ha
        · exact absurd h' hb
      · rw [pow_two] at h; exact mul_self_eq_zero.mp h
    have hab : a * b - b ^ 2 = 0 := by
      have hh : (2 * a ^ 2 + a * b + b ^ 2) - 2 * (a ^ 2 + b ^ 2) = a * b - b ^ 2 := by ring
      rw [← hh, hq, ha2b2]; ring
    have hab' : b * (a - b) = 0 := by
      have hh : a * b - b ^ 2 = b * (a - b) := by ring
      rw [← hh]; exact hab
    have habeq : a = b := by
      rcases mul_eq_zero.mp hab' with h | h
      · exact absurd h hb
      · exact sub_eq_zero.mp h
    have h2a2 : (2 : K) * a ^ 2 = 0 := by
      have hh : a ^ 2 + b ^ 2 = 2 * a ^ 2 := by rw [habeq]; ring
      rw [← hh]; exact ha2b2
    have h2ne : (2 : K) ≠ 0 := by
      intro hh
      have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp hh
      norm_num at hd
    have ha2 : a ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2a2 with h | h
      · exact absurd h h2ne
      · exact h
    have ha0 : a = 0 := by rw [pow_two] at ha2; exact mul_self_eq_zero.mp ha2
    exact ha ha0
  · intro hP
    exact hz (by rw [hP, map_zero])

/-- **The `0`-th component of the corrected AS forward chart map is nonzero.**  This is the
non-vanishing input of `FdivAS2_ne_zero_of` for the source divisor of `CensusAS2`. -/
theorem censusAS2_fwVec0_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 0 ≠ 0 := by
  have hDa : D.a ≠ 0 := fun h => hD.1.ab_ne (by rw [h, zero_mul])
  have hDb : D.b ≠ 0 := fun h => hD.1.ab_ne (by rw [h, mul_zero])
  have ha : aK D ≠ 0 := by
    rw [aK]
    intro h
    exact hDa ((algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [h, map_zero]))
  have hb : bK D ≠ 0 := by
    rw [bK]
    intro h
    exact hDb ((algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [h, map_zero]))
  exact fwVecAS2_zero_ne_zero_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) ha hb
    (aK_sq_sub_ne D hD)

end Work.MotAS
