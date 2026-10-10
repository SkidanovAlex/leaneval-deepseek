import Mathlib
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.CensusASOld
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The polar factor `linAS` of the AS census is a unit (its junk clause is vacuous)

Part of the census `Work.MotAS.CensusAS` (`Submission/Work/MotAS/linkCertAS.lean`).

For the AS chart the stereographic point is the **constant** vector `pAS = 288 • e₀`
(`ChartDefs.pAS`, equal to `MotAS.stereoPt w` for every `w`).  Consequently the polar factor of the
source equation,

  `linAS a b = kleinBilinAS (C a) (C b) (pAS K) (Work.MotK.chart3 K)`,

is the **constant** `-576 (a² − ab − b²)`: the quadratic form `kleinQAS` has no `y₀²`-term, so the
polar form `b^AS(pAS, v)` sees only the `y₀y₄`-coefficient `2(−a²+ab+b²)` and the chart coordinate
`v₄ = 1`, giving `b^AS(288 e₀, v) = 576(−a²+ab+b²)·v₄`.

Under `ASGood D` the scalar `a² − ab − b²` is nonzero in the field `RatFunc 𝕜`, so
`linAS (aK D) (bK D)` is a **unit** of `MvPolynomial (Fin 3) (RatFunc 𝕜)`.  Hence the clause
`linAS ∈ x.asIdeal → JunkClass` of `CensusAS` is *vacuous*: a proper prime contains no unit.

(This is the "degenerate polar factor" flagged in the `MotAS` handoff.  It is harmless for the
certificate — the clause is discharged here — and it reflects that the AS chart point is the image
of the split all-ones point rather than of `Work.MotK.kleinPointT`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The constant `288 : K` of the stereographic point, as a plain `MvPolynomial` numeral. -/
theorem C_288 {K : Type*} [CommRing K] :
    (C (288 : K) : MvPolynomial (Fin 3) K) = (288 : MvPolynomial (Fin 3) K) :=
  map_natCast C 288

/-- `pAS K` is the constant vector `288 • e₀`, as a literal vector of `MvPolynomial` numerals. -/
theorem pAS_eq_vec {K : Type*} [CommRing K] :
    pAS K = (![(288 : MvPolynomial (Fin 3) K), 0, 0, 0, 0] : Fin 5 → MvPolynomial (Fin 3) K) := by
  funext i
  fin_cases i <;> simp [pAS, C_288]

/-- **The polar factor of the AS chart is the constant `-576 (a² − ab − b²)`.** -/
theorem linAS_eq {K : Type*} [Field K] (a b : K) :
    linAS a b = -(576 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2) := by
  have hchart : Work.MotK.chart3 K = ![0, X 0, X 1, X 2, 1] := rfl
  have hlin : linAS a b = kleinBilinAS (C a) (C b) (pAS K) (Work.MotK.chart3 K) := rfl
  rw [hlin, kleinBilinAS, pAS_eq_vec, hchart]
  simp only [kleinQAS, Pi.add_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    zero_add, add_zero]
  first | refl_ring1 | ring

/-- **The polar form of the AS quadric at the constant chart point `288 • e₀`** is the linear form
`-576 (a² − ab − b²) · v₄`: the quadratic form `kleinQAS` has no `y₀²`-term and only the `y₀y₄`-term
involves `y₀`, so the polar form sees only the fourth coordinate of `v`.  (Taking `v = chart3`, whose
fourth coordinate is `1`, this gives `linAS`; taking `v = kleinRAS (chart3)` it identifies `cubAS`.)
-/
theorem kleinBilinAS_pAS {K : Type*} [Field K] (a b : K)
    (v : Fin 5 → MvPolynomial (Fin 3) K) :
    kleinBilinAS (C a) (C b) (pAS K) v
      = -(576 : MvPolynomial (Fin 3) K) * (C a ^ 2 - C a * C b - C b ^ 2) * v 4 := by
  rw [kleinBilinAS, pAS_eq_vec]
  simp only [kleinQAS, Pi.add_apply, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    zero_add, add_zero]
  first | refl_ring1 | ring

/-- `C c` is a unit of a polynomial ring over a field as soon as `c ≠ 0`. -/
theorem isUnit_C {K : Type*} [Field K] {c : K} (hc : c ≠ 0) :
    IsUnit (C c : MvPolynomial (Fin 3) K) :=
  ⟨⟨C c, C c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩, rfl⟩

/-- `aK D ^ 2 - aK D * bK D - bK D ^ 2` is nonzero for the pushed Klein data of `ASGood D`. -/
theorem aK_sq_sub_ne (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    aK D ^ 2 - aK D * bK D - bK D ^ 2 ≠ 0 := by
  have hcoe : aK D ^ 2 - aK D * bK D - bK D ^ 2
      = (algebraMap 𝕜 (RatFunc 𝕜)) (D.a ^ 2 - D.a * D.b - D.b ^ 2) := by
    simp only [aK, bK, map_sub, map_mul, map_pow]
  rw [hcoe]
  intro h
  exact hD.2.2.2 ((algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [h, map_zero]))

/-- `576` is nonzero in `RatFunc 𝕜` for `𝕜` of characteristic `5`. -/
theorem ne_zero_576 : ((576 : ℕ) : RatFunc 𝕜) ≠ 0 := by
  have hmap : ((576 : ℕ) : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) ((576 : ℕ) : 𝕜) := by
    rw [map_natCast]
  rw [hmap]
  intro h
  have h0 : ((576 : ℕ) : 𝕜) = 0 := (algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [h, map_zero])
  have h5 : ((5 : ℕ) : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
  have hone : ((576 : ℕ) : 𝕜) = 1 := by
    rw [show (576 : ℕ) = 5 * 115 + 1 from by norm_num, Nat.cast_add, Nat.cast_mul, h5, zero_mul,
      zero_add, Nat.cast_one]
  rw [hone] at h0
  exact one_ne_zero h0

/-- In characteristic `5` the numeral `576` is `1` in the polynomial ring. -/
theorem num_576 (K : Type*) [CommRing K] [CharP K 5] :
    (576 : MvPolynomial (Fin 3) K) = 1 := by
  have h2 : (576 : MvPolynomial (Fin 3) K) = C ((576 : ℕ) : K) := (map_natCast C 576).symm
  have h : ((576 : ℕ) : K) = 1 := by
    rw [show (576 : ℕ) = 5 * 115 + 1 from by norm_num, Nat.cast_add, Nat.cast_mul,
      CharP.cast_eq_zero K 5, zero_mul, zero_add, Nat.cast_one]
  rw [h2, h, map_one]

/-- **`linAS (aK D) (bK D)` is a unit** for `ASGood D`. -/
theorem isUnit_linAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    IsUnit (linAS (aK D) (bK D)) := by
  have hc2 : aK D ^ 2 - aK D * bK D - bK D ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  rw [linAS_eq]
  have hfac : (C (aK D) ^ 2 - C (aK D) * C (bK D) - C (bK D) ^ 2
      : MvPolynomial (Fin 3) (RatFunc 𝕜)) = C (aK D ^ 2 - aK D * bK D - bK D ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  rw [hfac, num_576]
  exact IsUnit.mul (show IsUnit (-(1 : MvPolynomial (Fin 3) (RatFunc 𝕜))) from
    ⟨⟨-1, -1, by ring, by ring⟩, rfl⟩) (isUnit_C hc2)

/-- **`cubAS` is a constant multiple of the fourth component of the inverse chart map**: the second
polar factor of the AS census is `-576 (aK² − aK bK − bK²) · (kleinRAS (chart3))₄`.  Hence the
`cubAS` junk clause of `CensusAS` reduces to the junk-ness of that explicit cubic. -/
theorem cubAS_eq (D : Work.MotV.KleinData 𝕜) :
    cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
      = -(576 : MvPolynomial (Fin 3) (RatFunc 𝕜))
          * (C (aK D) ^ 2 - C (aK D) * C (bK D) - C (bK D) ^ 2)
          * kleinRAS (C (aK D)) (C (bK D)) (C (Work.MotV.fAS 𝕜))
              (Work.MotK.chart3 (RatFunc 𝕜)) 4 :=
  kleinBilinAS_pAS (aK D) (bK D) _

/-- **The `linAS` clause of `CensusAS` is vacuous**: the polar factor is a unit, so it lies in no
proper prime ideal. -/
theorem censusAS_linAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      linAS (aK D) (bK D) ∈ x.asIdeal → Work.MotV.JunkClass (RatFunc 𝕜) x := by
  intro x _ hx
  exact absurd (Ideal.eq_top_of_isUnit_mem x.asIdeal hx (isUnit_linAS D hD)) x.isPrime.ne_top

/-- **The census with the (vacuous) `linAS` clause removed.**  Proving this is enough: the
`linAS` conjunct of `CensusAS` is supplied by `censusAS_linAS`. -/
def CensusAS' (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) : Prop :=
  ∃ (hpr : (Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)} :
      Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))).IsPrime),
    Ideal.height (Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)}) = 1 ∧
    Nonempty (Work.MotV.resF (RatFunc 𝕜)
        ⟨Ideal.span {sdualAS (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hpr⟩ ≃ₐ[RatFunc 𝕜]
      RatFunc ↥(twistFieldAS D (Work.MotV.fAS 𝕜))) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
    Nonempty (Work.MotV.resF (RatFunc 𝕜) x ≃ₐ[RatFunc 𝕜]
        RatFunc ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) ∨
      Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      cubAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  (∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x) ∧
  FdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
  Nonempty (Localization.Away (FdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) ≃ₐ[RatFunc 𝕜]
    Localization.Away (GdivAS (aK D) (bK D) (Work.MotV.fAS 𝕜)))

/-- `CensusAS'` implies the full census (the missing conjunct is `censusAS_linAS`). -/
theorem censusAS_of_censusAS' (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hc : CensusAS' D hD) : CensusAS D hD := by
  obtain ⟨hpr, hht, hres, hS, hCub, hFw, hBw, hFne, hGne, hΦ⟩ := hc
  exact ⟨hpr, hht, hres, hS, censusAS_linAS D hD, hCub, hFw, hBw, hFne, hGne, hΦ⟩

/-- **`linkCertAS` from the reduced census** (the `linAS` clause of `CensusAS` is supplied here). -/
theorem linkCertAS_of_censusAS' (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hc : CensusAS' D hD) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜) ↥(twistFieldAS D (Work.MotV.fAS 𝕜))
      ↥(twistFieldAS D (2 • Work.MotV.fAS 𝕜))) :=
  linkCertAS_of_censusAS D hD (censusAS_of_censusAS' D hD hc)

end Work.MotAS

