import Mathlib
import Submission.Work.C17y.gen_van
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.hasDerivAt_rval
import Submission.Work.GenShared.rreg_Dv

set_option linter.unusedVariables false

namespace Work.C17y

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

noncomputable section

/-! ## Evaluating the connection on the regular locus

The connection `∂ = Dv p2 p1 p0 rn rd` is built from field operations on `ℂ(x)`, so its
value at a point where all the denominators involved are nonzero is obtained by replacing
each rational function by its evaluation.  These three lemmas record the result for the three
components of `∂n`. -/

/-- The value of the first component of the connection,
`∂₁(a,b,c) = a' − (p₀/p₂)b + Σᵢ cᵢ rᵢ` with `rᵢ = rnᵢ/rdᵢ`. -/
lemma Rval_Dv_fst {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ) (n : W k)
    {z : ℂ} (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) (hc : ∀ i, Rreg (n.2.2 i) z) :
    Rval (Dv p2 p1 p0 rn rd n).1 z
      = Rval (dRat n.1) z - (p0.eval z / p2.eval z) * Rval n.2.1 z
        + ∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z) := by
  have hsum : Rreg (∑ i, n.2.2 i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i))) z := by
    apply rreg_sum
    intro i
    exact rreg_mul (hc i) (rreg_div_poly (hrd i))
  have h1 : Rval (Dv p2 p1 p0 rn rd n).1 z
      = Rval (dRat n.1 - algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * n.2.1
          + ∑ i, n.2.2 i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i))) z := by
    simp only [Dv]
  rw [h1, Rval_add _ _ _ (rreg_sub (rreg_dRat ha) (rreg_mul (rreg_div_poly hp2) hb)) hsum,
    Rval_sub _ _ _ (rreg_dRat ha) (rreg_mul (rreg_div_poly hp2) hb),
    Rval_mul _ _ _ (rreg_div_poly hp2) hb,
    Rval_sum _ _ (fun i => rreg_mul (hc i) (rreg_div_poly (hrd i)))]
  simp only [Rval_div p0 p2 z hp2]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Rval_mul _ _ _ (hc i) (rreg_div_poly (hrd i)), Rval_div _ _ _ (hrd i)]

/-- The value of the second component of the connection, `∂₂(a,b,c) = a + b' − (p₁/p₂)b`. -/
lemma Rval_Dv_snd {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ) (n : W k)
    {z : ℂ} (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) (hc : ∀ i, Rreg (n.2.2 i) z) :
    Rval (Dv p2 p1 p0 rn rd n).2.1 z
      = Rval n.1 z + Rval (dRat n.2.1) z - (p1.eval z / p2.eval z) * Rval n.2.1 z := by
  have h1 : Rval (Dv p2 p1 p0 rn rd n).2.1 z
      = Rval (n.1 + dRat n.2.1 - algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * n.2.1) z := by
    simp only [Dv]
  rw [h1, Rval_sub _ _ _ (rreg_add ha (rreg_dRat hb)) (rreg_mul (rreg_div_poly hp2) hb),
    Rval_add _ _ _ ha (rreg_dRat hb), Rval_mul _ _ _ (rreg_div_poly hp2) hb,
    Rval_div p1 p2 z hp2]

/-- The value of the third component of the connection, `∂₃(a,b,c) = (cᵢ')ᵢ`. -/
lemma Rval_Dv_trd {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ) (n : W k)
    {z : ℂ} (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) (hc : ∀ i, Rreg (n.2.2 i) z) :
    ∀ i, Rval ((Dv p2 p1 p0 rn rd n).2.2 i) z = Rval (dRat (n.2.2 i)) z := by
  intro i
  simp only [Dv]

/-- **The derivative of the relation function is the relation function of the connection.**

`Work.GenShared.Wev y1 J n z = Rval n.1 z * y1 z + Rval n.2.1 z * deriv y1 z + ∑ i, Rval (n.2.2 i) z * J i z`
is the function attached to a coefficient tuple `n : W k = K^2 × (Fin k → K)`, `K = ℂ(x)`; and
`Work.GenShared.Dv p2 p1 p0 rn rd n` is the connection
`∂(a,b,c) = (a' − (p₀/p₂)b + Σ cᵢ rᵢ,  a + b' − (p₁/p₂)b,  (cᵢ')ᵢ)` with `rᵢ = rnᵢ/rdᵢ`, where `' = Submission.CDT.dRat`.

If `y1` solves `p₂ y₁'' + p₁ y₁' + p₀ y₁ = 0` on the ball, `J i` is a primitive of `(rn i/rd i)·y1`,
and at the point `z` all coefficients of `n` are regular, `p2 z ≠ 0`, `(rd i) z ≠ 0` and `y1'` is
differentiable, then the function `w ↦ Wev y1 J n w` has derivative `Wev y1 J (Dv … n) z` at `z`.

Proof: differentiate termwise (product rule, `Work.GenShared.hasDerivAt_rval` for the `Rval` factors),
use `J i' = rn i(z)/rd i(z) * y1 z`, and replace the second derivative `deriv (deriv y1) z` by the
value `-(p1 z/p2 z) * deriv y1 z - (p0 z/p2 z) * y1 z` supplied by the ODE (legitimate since
`p2 z ≠ 0`).  The `Rval` of the components of `Dv … n` is expanded with the lemmas `Rval_add`,
`Rval_sub`, `Rval_mul`, `Rval_sum`, `Rval_neg` of `Work.C17y.gen_van` and
`Work.GenShared.Rval_div`, all of which apply because the relevant denominators are nonvanishing. -/
theorem hasDerivAt_wev {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ} {n : Work.GenShared.W k} {z : ℂ}
    (hz : z ∈ Metric.ball x0 δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    (hode : ∀ w ∈ Metric.ball x0 δ,
      p2.eval w * deriv (deriv y1) w + p1.eval w * deriv y1 w + p0.eval w * y1 w = 0)
    (hJderiv : ∀ i, ∀ w ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval w / (rd i).eval w * y1 w) w)
    (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (hy1'' : DifferentiableAt ℂ (deriv y1) z)
    (ha : (n.1).denom.eval z ≠ 0) (hb : (n.2.1).denom.eval z ≠ 0)
    (hc : ∀ i, (n.2.2 i).denom.eval z ≠ 0) :
    HasDerivAt (fun w => Work.GenShared.Wev y1 J n w)
      (Work.GenShared.Wev y1 J (Work.GenShared.Dv p2 p1 p0 rn rd n) z) z := by
  -- ### The point `z` lies in an open ball, so everything is differentiable there
  have hzn : Metric.ball x0 δ ∈ nhds z := (Metric.isOpen_ball).mem_nhds hz
  -- ### The two substitutions supplied by the hypotheses
  -- the second derivative of `y1` at `z`, from the differential equation
  have hddy : deriv (deriv y1) z
      = -(p1.eval z / p2.eval z) * deriv y1 z - (p0.eval z / p2.eval z) * y1 z := by
    have key : deriv (deriv y1) z
        = (-(p1.eval z * deriv y1 z + p0.eval z * y1 z)) / p2.eval z := by
      rw [eq_div_iff hp2]
      have h := hode z hz
      linear_combination h
    rw [key]
    field_simp
    ring
  -- the derivative of `J i` at `z`, from `hJderiv` (uniqueness of the derivative)
  have hJv : ∀ i, deriv (J i) z = (rn i).eval z / (rd i).eval z * y1 z :=
    fun i => (hJderiv i z hz).deriv
  -- ### Termwise differentiation of `Wev`
  have hy1 : HasDerivAt y1 (deriv y1 z) z := (hy1d.differentiableAt hzn).hasDerivAt
  have hdydy : HasDerivAt (deriv y1) (deriv (deriv y1) z) z := hy1''.hasDerivAt
  have hJ' : ∀ i, HasDerivAt (J i) (deriv (J i) z) z :=
    fun i => ((hJd i).differentiableAt hzn).hasDerivAt
  have hA : HasDerivAt (fun w => Rval n.1 w) (Rval (dRat n.1) z) z :=
    Work.GenShared.hasDerivAt_rval n.1 z ha
  have hB : HasDerivAt (fun w => Rval n.2.1 w) (Rval (dRat n.2.1) z) z :=
    Work.GenShared.hasDerivAt_rval n.2.1 z hb
  have hC : ∀ i, HasDerivAt (fun w => Rval (n.2.2 i) w) (Rval (dRat (n.2.2 i)) z) z :=
    fun i => Work.GenShared.hasDerivAt_rval (n.2.2 i) z (hc i)
  have hpart1 : HasDerivAt (fun w => Rval n.1 w * y1 w)
      (Rval (dRat n.1) z * y1 z + Rval n.1 z * deriv y1 z) z := hA.mul hy1
  have hpart2 : HasDerivAt (fun w => Rval n.2.1 w * deriv y1 w)
      (Rval (dRat n.2.1) z * deriv y1 z + Rval n.2.1 z * deriv (deriv y1) z) z := hB.mul hdydy
  have hpart3 : HasDerivAt (fun w => ∑ i, Rval (n.2.2 i) w * J i w)
      (∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)) z :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hC i).mul (hJ' i))
  -- the derivative is the explicit expansion of `WevD`
  have htotal : HasDerivAt (fun w => Wev y1 J n w)
      (Rval (dRat n.1) z * y1 z + Rval n.1 z * deriv y1 z
        + (Rval (dRat n.2.1) z * deriv y1 z + Rval n.2.1 z * deriv (deriv y1) z)
        + ∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)) z :=
    (hpart1.add hpart2).add hpart3
  -- ### Folding the factor `y1 z` out of the last sum
  have hsumfac : (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z * y1 z))
      = (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z)) * y1 z := by
    rw [show (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z * y1 z))
        = ∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z) * y1 z from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring]
    rw [Finset.sum_mul]
  -- ### The derivative value is `Wev` of the connection applied to `n`
  have hWev : Wev y1 J (Dv p2 p1 p0 rn rd n) z
      = Rval (dRat n.1) z * y1 z + Rval n.1 z * deriv y1 z
        + (Rval (dRat n.2.1) z * deriv y1 z + Rval n.2.1 z * deriv (deriv y1) z)
        + ∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z) := by
    have key1 := Rval_Dv_fst p2 p1 p0 rn rd n hp2 hrd ha hb hc
    have key2 := Rval_Dv_snd p2 p1 p0 rn rd n hp2 hrd ha hb hc
    have key3 := Rval_Dv_trd p2 p1 p0 rn rd n hp2 hrd ha hb hc
    simp only [Wev]
    rw [key1, key2]
    simp only [key3]
    rw [hddy]
    simp only [hJv]
    rw [Finset.sum_add_distrib, hsumfac]
    ring
  rw [← hWev] at htotal
  exact htotal

end

end Work.C17y
