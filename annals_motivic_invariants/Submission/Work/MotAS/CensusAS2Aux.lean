import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusLinAS
import Submission.Work.MotAS.censusAS_sAS_ne_zero
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.CensusAS2Aux` — the vacuous `linAS2` clause and the `cubAS2 → bwVecAS2` reduction

Two of the eleven conjuncts of `Work.MotAS.CensusAS2` are *consequences* of the others and are
proved here, so that only the genuinely geometric clauses have to be delegated:

* **`linAS2` is a unit.**  `linAS2 a b = b^AS(p, chart3)` is the polar form of the AS quadric at the
  chart point `p = e₀ = (1,0,0,0,0)` and the source chart vector `chart3 = (0,X₀,X₁,X₂,1)`.  The
  quadratic form `kleinQAS` has no `y₀²`-term and the only monomial involving `y₀` is `y₀y₄`, so the
  polar form sees only the fourth coordinate: `b^AS(e₀, v) = -2(a²−ab−b²)·v₄`
  (`kleinBilinAS_pAS0`), and `chart3` has `v₄ = 1`.  Hence `linAS2 a b = -2(a²−ab−b²)`, a unit under
  `ASGood` (`a² − ab − b² ≠ 0`), and the `linAS2` junk clause of the census is *vacuous*.

* **The `cubAS2` clause reduces to the `bwVecAS2 · 4` clause.**  The target polar factor is
  `cubAS2 a b g = b^AS(e₀, R^AS(tchart)) = -2(a²−ab−b²)·(R^AS(tchart))₄`, while
  `bwVecAS2 a b g 4 = π_{e₀}(R^AS(tchart))₄ = (R^AS(tchart))₄` because `p₄ = 0`; so
  `cubAS2 = linAS2 · bwVecAS2 4` with `linAS2` a unit, and a prime containing `cubAS2` contains
  `bwVecAS2 4`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- `pAS0 K` as a literal vector, for the `Matrix`/`Fin` reductions. -/
theorem pAS0_eq_vec {K : Type*} [CommRing K] :
    pAS0 K = (![(1 : MvPolynomial (Fin 3) K), 0, 0, 0, 0] : Fin 5 → MvPolynomial (Fin 3) K) := by
  funext i
  fin_cases i <;> simp [pAS0]

/-- **The polar form of the AS quadric at the chart point `e₀`** is `-2(a²−ab−b²)·v₄`. -/
theorem kleinBilinAS_pAS0 {K : Type*} [Field K] (a b : K)
    (v : Fin 5 → MvPolynomial (Fin 3) K) :
    kleinBilinAS (C a) (C b) (pAS0 K) v
      = -(2 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2) * v 4 := by
  rw [kleinBilinAS, pAS0_eq_vec]
  simp only [kleinQAS, Pi.add_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    zero_add]
  refl_ring1

/-- **`linAS2` is the constant `-2 (a² − ab − b²)`**: the source polar factor of the corrected
AS chart. -/
theorem linAS2_eq_const {K : Type*} [Field K] (a b : K) :
    linAS2 a b = -(2 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2) := by
  have hchart : Work.MotK.chart3 K = ![0, X 0, X 1, X 2, 1] := rfl
  have hlin : linAS2 a b = kleinBilinAS (C a) (C b) (pAS0 K) (Work.MotK.chart3 K) := rfl
  rw [hlin, kleinBilinAS, pAS0_eq_vec, hchart]
  simp only [kleinQAS, Pi.add_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    zero_add, add_zero]
  refl_ring1

/-- `bwVecAS2 · 4` is the fourth component of `R^AS(tchart)`: the projection `π_{e₀}` only changes
the zeroth coordinate, and `pAS0 · 4 = 0`. -/
theorem bwVecAS2_four_eq {K : Type*} [Field K] (a b g : K) :
    bwVecAS2 a b g 4 = kleinRAS (C a) (C b) (C g) (tchart K) 4 := by
  simp only [bwVecAS2, Work.MotK.kleinTwPi, pAS0_four, mul_zero, sub_zero]

/-- **The target polar factor is `linAS2 · bwVecAS2 · 4`.** -/
theorem cubAS2_eq {K : Type*} [Field K] (a b g : K) :
    cubAS2 a b g = linAS2 a b * bwVecAS2 a b g 4 := by
  have h1 : cubAS2 a b g
      = -(2 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2)
          * kleinRAS (C a) (C b) (C g) (tchart K) 4 := by
    rw [cubAS2, kleinBilinAS_pAS0]
  rw [h1, linAS2_eq_const, bwVecAS2_four_eq]

/-- **`linAS2 (aK D) (bK D)` is a unit** under `ASGood D`. -/
theorem isUnit_linAS2 (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    IsUnit (linAS2 (aK D) (bK D)) := by
  have hc2 : aK D ^ 2 - aK D * bK D - bK D ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  rw [linAS2_eq_const]
  have hfac : (C (aK D) ^ 2 - C (aK D) * C (bK D) - C (bK D) ^ 2
      : MvPolynomial (Fin 3) (RatFunc 𝕜)) = C (aK D ^ 2 - aK D * bK D - bK D ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  rw [hfac]
  have h2 : IsUnit (2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) := by
    refine ⟨⟨2, 288, ?_, ?_⟩, rfl⟩
    · rw [show (2 * 288 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 576 by norm_num, num_576]
    · rw [show (288 * 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 576 by norm_num, num_576]
  exact IsUnit.mul h2.neg (isUnit_C hc2)

/-- **The `linAS2` clause of `CensusAS2` is vacuous**: the polar factor is a unit, hence lies in no
proper prime ideal. -/
theorem censusAS2_linAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      linAS2 (aK D) (bK D) ∈ x.asIdeal → Work.MotV.JunkClass (RatFunc 𝕜) x := by
  intro x _ hx
  exact absurd (Ideal.eq_top_of_isUnit_mem x.asIdeal hx (isUnit_linAS2 D hD)) x.isPrime.ne_top

/-- **The `cubAS2` clause of `CensusAS2` follows from the `bwVecAS2 · 4` clause**: a prime exhibiting
`cubAS2 = linAS2 · bwVecAS2 4` must contain `bwVecAS2 4`, since `linAS2` is a unit. -/
theorem censusAS2_cubAS_of_bwVec4 (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (hbw : ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) :
    ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      cubAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x := by
  intro x hx hxc
  haveI : x.asIdeal.IsPrime := x.2
  rw [cubAS2_eq] at hxc
  rcases x.2.mem_or_mem hxc with h | h
  · exact absurd (Ideal.eq_top_of_isUnit_mem x.asIdeal h (isUnit_linAS2 D hD)) x.isPrime.ne_top
  · exact hbw x hx h

/-- **The source divisor is nonzero** as soon as its two non-unit factors are: the polar factor
`linAS2` is a unit. -/
theorem FdivAS2_ne_zero_of (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hfw : fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 0 ≠ 0)
    (hs : sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0) :
    FdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 := by
  rw [FdivAS2]
  exact mul_ne_zero (mul_ne_zero (isUnit_linAS2 D hD).ne_zero hs) hfw

/-- **The target divisor is nonzero** as soon as its two non-unit factors are: the target polar
factor is `linAS2 · bwVecAS2 · 4` with `linAS2` a unit. -/
theorem GdivAS2_ne_zero_of (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hbw : bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ≠ 0)
    (hsd : sdualAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0) :
    GdivAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 := by
  rw [GdivAS2, cubAS2_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (isUnit_linAS2 D hD).ne_zero hbw) hsd) hbw

/-- `kleinBilinAS` is linear in its first argument. -/
theorem kleinBilinAS_smul_left {K : Type*} [CommRing K] (a b c : K) (u v : Fin 5 → K) :
    kleinBilinAS a b (fun i => c * u i) v = c * kleinBilinAS a b u v := by
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply, Pi.mul_apply]
  refl_ring1

/-- `kleinStereoAS` is linear in the stereographic point `p`. -/
theorem kleinStereoAS_smul_left {K : Type*} [CommRing K] (a b c : K) (p v : Fin 5 → K) :
    kleinStereoAS a b (fun i => c * p i) v = fun i => c * kleinStereoAS a b p v i := by
  funext i
  simp only [kleinStereoAS, Pi.mul_apply, kleinBilinAS_smul_left]
  refl_ring1

/-- The AS source secant quintic is homogeneous of degree `5` in the coordinates. -/
theorem kleinSecAS_smul_aux {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinSecAS a b g (fun i => c * v i) = c ^ 5 * kleinSecAS a b g v := by
  simp only [kleinSecAS, Pi.mul_apply]
  refl_ring1

/-- `pAS = 288 • pAS0`: the two stereographic points differ by the constant `288`. -/
theorem pAS_eq_smul_pAS0 {K : Type*} [CommRing K] :
    pAS K = fun i => (288 : MvPolynomial (Fin 3) K) * pAS0 K i := by
  funext i
  fin_cases i <;> simp [pAS, pAS0, C_288]

/-- **`sAS = 288⁵ · sAS2`**: the two source ruling quintics (old and corrected chart point) differ
by the unit constant `288⁵ = 3`. -/
theorem sAS_eq_scale {K : Type*} [Field K] (a b g : K) :
    sAS a b g = (288 : MvPolynomial (Fin 3) K) ^ 5 * sAS2 a b g := by
  have hp : kleinStereoAS (C a) (C b) (pAS K) (Work.MotK.chart3 K)
      = fun i => (288 : MvPolynomial (Fin 3) K)
          * kleinStereoAS (C a) (C b) (pAS0 K) (Work.MotK.chart3 K) i := by
    rw [pAS_eq_smul_pAS0]
    exact kleinStereoAS_smul_left (C a) (C b) 288 (pAS0 K) (Work.MotK.chart3 K)
  rw [sAS, sAS2, hp, kleinSecAS_smul_aux]

/-- **`sAS2 ≠ 0`** for a good AS datum, from the proved `sAS ≠ 0` of the (degenerate) old chart
point: the two differ by the constant `288⁵`. -/
theorem sAS2_ne_zero (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    sAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 := by
  have h := Work.MotAS.censusAS_sAS_ne_zero 𝕜 D hD
  intro h0
  exact h (by rw [sAS_eq_scale, h0, mul_zero])

end Work.MotAS
