import Mathlib
import Submission.Work.Mostow.betweenVec

/-!
# Transitivity of betweenness for the hyperbolic distance

If `y` lies on the geodesic from `x` to `z` (i.e. `hdist x z = hdist x y + hdist y z`) and
`z` lies on the geodesic from `y` to `w` (`hdist y w = hdist y z + hdist z w`), with `y ≠ z`,
then the four points are collinear in the order `x, y, z, w`, so that
`hdist x w = hdist x y + hdist y w`.

The proof is the hyperboloid computation (chart model `E n`, Minkowski form `mink_localIsomDefs`).
`betweenVec` expresses `hlift y` as an affine combination of `hlift x`, `hlift z`, and
`hlift z` as an affine combination of `hlift y`, `hlift w`; eliminating `hlift z` shows
`- mink_localIsomDefs (hlift x) (hlift w) = cosh (hdist x y + hdist y w)`, while on the other hand
`- mink_localIsomDefs (hlift x) (hlift w) = cosh (hdist x w)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace BetweenTrans

variable {n : ℕ}

lemma hdist_nonneg' (u v : E n) : 0 ≤ hdist u v :=
  Real.arcosh_nonneg (Btw.one_le_cosh_hdist u v)

/-- The elementary hyperbolic identity behind the transitivity of betweenness:
`sinh (b+e) cosh (a+b) − sinh e cosh a = sinh b cosh (a+(b+e))`. -/
lemma trig_between (a b e : ℝ) :
    Real.sinh (b + e) * Real.cosh (a + b) - Real.sinh e * Real.cosh a
      = Real.sinh b * Real.cosh (a + (b + e)) := by
  have h : Real.cosh b * Real.cosh (a + b) - Real.sinh b * Real.sinh (a + b)
      = Real.cosh a := by
    have hh := Real.cosh_sub (a + b) b
    rw [add_sub_cancel_right] at hh
    linarith [hh]
  have hc : Real.cosh (a + (b + e))
      = Real.cosh (a + b) * Real.cosh e + Real.sinh (a + b) * Real.sinh e := by
    rw [show a + (b + e) = (a + b) + e from by ring, Real.cosh_add]
  rw [hc, Real.sinh_add]
  linear_combination Real.sinh e * h

end BetweenTrans

open BetweenTrans

theorem betweenTrans {n : ℕ} (x y z w : E n) (hyz : y ≠ z)
    (h1 : hdist x z = hdist x y + hdist y z) (h2 : hdist y w = hdist y z + hdist z w) :
    hdist x w = hdist x y + hdist y w := by
  set a := hdist x y with ha
  set b := hdist y z with hb
  set c := hdist x z with hc
  set e := hdist z w with he
  set f := hdist y w with hf
  have ha0 : 0 ≤ a := hdist_nonneg' x y
  have hb0 : 0 ≤ b := hdist_nonneg' y z
  have he0 : 0 ≤ e := hdist_nonneg' z w
  have hf0 : 0 ≤ f := hdist_nonneg' y w
  have hbpos : 0 < b :=
    lt_of_le_of_ne hb0 (Ne.symm fun h0 => hyz ((Btw.hdist_eq_zero y z).mp h0))
  have hfpos : 0 < f := by rw [h2]; linarith
  have hxz : x ≠ z := by
    intro hxzeq
    have hcz : c = 0 := by rw [hc, hxzeq, Btw.hdist_self]
    linarith
  have hyw : y ≠ w := by
    intro hyweq
    have hfw : f = 0 := by rw [hf, hyweq, Btw.hdist_self]
    linarith
  have hY : hlift y = (Real.sinh b / Real.sinh c) • hlift x
      + (Real.sinh a / Real.sinh c) • hlift z := betweenVec x y z hxz h1
  have hZ : hlift z = (Real.sinh e / Real.sinh f) • hlift y
      + (Real.sinh b / Real.sinh f) • hlift w := betweenVec y z w hyw h2
  have hsub : (Real.sinh b / Real.sinh f) • hlift w
      = hlift z - (Real.sinh e / Real.sinh f) • hlift y := by
    rw [hZ, add_sub_cancel_left]
  have hmink : (Real.sinh b / Real.sinh f) * mink_localIsomDefs (hlift x) (hlift w)
      = mink_localIsomDefs (hlift x) (hlift z)
        - (Real.sinh e / Real.sinh f) * mink_localIsomDefs (hlift x) (hlift y) := by
    have := congrArg (fun V => mink_localIsomDefs (hlift x) V) hsub
    simpa only [Btw.mink_smul_right, Btw.mink_sub_right] using this
  have hxzc : mink_localIsomDefs (hlift x) (hlift z) = -Real.cosh c := Btw.mink_hlift_neg_cosh x z
  have hxyc : mink_localIsomDefs (hlift x) (hlift y) = -Real.cosh a := Btw.mink_hlift_neg_cosh x y
  have hminkA : (Real.sinh b / Real.sinh f) * mink_localIsomDefs (hlift x) (hlift w)
      = -Real.cosh c + (Real.sinh e / Real.sinh f) * Real.cosh a := by
    rw [hmink, hxzc, hxyc]; ring
  have hsf : Real.sinh f ≠ 0 := by rw [Real.sinh_ne_zero]; intro h0; linarith
  have hsb : Real.sinh b ≠ 0 := by rw [Real.sinh_ne_zero]; intro h0; linarith
  have hmink2 : Real.sinh b * mink_localIsomDefs (hlift x) (hlift w)
      = - Real.sinh f * Real.cosh c + Real.sinh e * Real.cosh a := by
    have := hminkA
    field_simp at this
    linarith [this]
  have hprod : Real.sinh f * Real.cosh c - Real.sinh e * Real.cosh a
      = Real.sinh b * Real.cosh (a + f) := by
    rw [h1, h2]
    exact trig_between a b e
  have hkey : Real.sinh b * mink_localIsomDefs (hlift x) (hlift w)
      = Real.sinh b * (- Real.cosh (a + f)) := by
    linarith [hmink2, hprod]
  have hM : mink_localIsomDefs (hlift x) (hlift w) = - Real.cosh (a + f) :=
    mul_left_cancel₀ hsb hkey
  have hcw : Real.cosh (hdist x w) = - mink_localIsomDefs (hlift x) (hlift w) := by
    rw [Btw.mink_hlift_neg_cosh]; ring
  have hcosh : Real.cosh (hdist x w) = Real.cosh (a + f) := by
    rw [hcw, hM, neg_neg]
  have hfin : hdist x w = a + f := by
    rw [← Real.arcosh_cosh (hdist_nonneg' x w), hcosh]
    exact Real.arcosh_cosh (add_nonneg (hdist_nonneg' x y) (hdist_nonneg' y w))
  exact hfin

end Work.Mostow
