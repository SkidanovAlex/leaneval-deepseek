import Mathlib
import Submission.Work.GenShared.wevD

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

noncomputable section

/-- The value of the first component of `Dv`, expanded into `Rval`s of the individual
coefficients: `Rval (∂n).1 z = (a')z - (p₀/p₂)z·(b)z + Σᵢ (cᵢ)z·(rᵢ)z`. -/
lemma Rval_Dv_fst {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (n : W k) {z : ℂ}
    (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) (hc : ∀ i, Rreg (n.2.2 i) z) :
    Rval (Dv p2 p1 p0 rn rd n).1 z
      = Rval (dRat n.1) z - (p0.eval z / p2.eval z) * Rval n.2.1 z
        + ∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z) := by
  rw [Dv]
  dsimp only
  rw [Rval_add_of (rreg_sub (rreg_dRat ha) (rreg_mul (rreg_div_poly hp2) hb))
        (Rreg_finset_sum Finset.univ _
          (fun i _ => rreg_mul (hc i) (rreg_div_poly (hrd i)))),
      Rval_sub_of (rreg_dRat ha) (rreg_mul (rreg_div_poly hp2) hb),
      Rval_mul_of (rreg_div_poly hp2) hb, Rval_div_poly_of p0 p2 z hp2,
      Rval_finset_sum Finset.univ _
        (fun i _ => rreg_mul (hc i) (rreg_div_poly (hrd i)))]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Rval_mul_of (hc i) (rreg_div_poly (hrd i)), Rval_div_poly_of (rn i) (rd i) z (hrd i)]

/-- The value of the second component of `Dv`, expanded:
`Rval (∂n).2.1 z = (a)z + (b')z - (p₁/p₂)z·(b)z`. -/
lemma Rval_Dv_snd {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (n : W k) {z : ℂ}
    (hp2 : p2.eval z ≠ 0)
    (ha : Rreg n.1 z) (hb : Rreg n.2.1 z) :
    Rval (Dv p2 p1 p0 rn rd n).2.1 z
      = Rval n.1 z + Rval (dRat n.2.1) z - (p1.eval z / p2.eval z) * Rval n.2.1 z := by
  rw [Dv]
  dsimp only
  rw [Rval_sub_of (rreg_add ha (rreg_dRat hb)) (rreg_mul (rreg_div_poly hp2) hb),
      Rval_add_of ha (rreg_dRat hb),
      Rval_mul_of (rreg_div_poly hp2) hb, Rval_div_poly_of p1 p2 z hp2]

/-- The value of the third component of `Dv`. -/
lemma Rval_Dv_trd {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (n : W k) (z : ℂ) (i : Fin k) :
    Rval ((Dv p2 p1 p0 rn rd n).2.2 i) z = Rval (dRat (n.2.2 i)) z := rfl

/-- The identity `Wev y1 J (Dv … n) z = WevD y1 J n z` expressing that the connection `Dv`
annihilates the vanishing module `N = ker (Wev ·)` once the first period `y1` satisfies the
associated order-two ODE and the `Jᵢ` have the prescribed derivative. -/
theorem wev_Dv_eq {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (x0 : ℂ) {δ : ℝ} (hp2ne : ∀ z ∈ Metric.ball x0 δ, p2.eval z ≠ 0)
    (hrdne : ∀ i, ∀ z ∈ Metric.ball x0 δ, (rd i).eval z ≠ 0)
    (y1 : ℂ → ℂ)
    (hode : ∀ z ∈ Metric.ball x0 δ,
      p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z + p0.eval z * y1 z = 0)
    (J : Fin k → ℂ → ℂ)
    (hJderiv : ∀ i, ∀ z ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval z / (rd i).eval z * y1 z) z)
    {n : Work.GenShared.W k} {z : ℂ} (hz : z ∈ Metric.ball x0 δ)
    (ha : Work.GenShared.Rreg n.1 z) (hb : Work.GenShared.Rreg n.2.1 z)
    (hc : ∀ i, Work.GenShared.Rreg (n.2.2 i) z) :
    Work.GenShared.Wev y1 J (Work.GenShared.Dv p2 p1 p0 rn rd n) z =
      Work.GenShared.WevD y1 J n z := by
  have hA : p2.eval z ≠ 0 := hp2ne z hz
  have hode_z : p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z
      + p0.eval z * y1 z = 0 := hode z hz
  -- the second derivative of `y1` in terms of `y1` and `y1'`
  have hw : deriv (deriv y1) z
      = -(p0.eval z / p2.eval z * y1 z + p1.eval z / p2.eval z * deriv y1 z) := by
    have h1 : p2.eval z * deriv (deriv y1) z
        = -(p1.eval z * deriv y1 z + p0.eval z * y1 z) := by
      linear_combination hode_z
    field_simp
    linear_combination h1
  -- the derivatives of the `Jᵢ`
  have hJ : ∀ i, deriv (J i) z = (rn i).eval z / (rd i).eval z * y1 z :=
    fun i => (hJderiv i z hz).deriv
  rw [Wev, WevD]
  rw [Rval_Dv_fst p2 p1 p0 rn rd n hA (fun i => hrdne i z hz) ha hb hc,
      Rval_Dv_snd p2 p1 p0 rn rd n hA ha hb]
  dsimp only [Dv]
  have hsum : (∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z))
      = (∑ i, Rval (dRat (n.2.2 i)) z * J i z)
        + (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z * y1 z)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hJ i])
  rw [hsum]
  have hS : (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z * y1 z))
      = (∑ i, Rval (n.2.2 i) z * ((rn i).eval z / (rd i).eval z)) * y1 z := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hS, hw]
  ring

end

end Work.GenShared
