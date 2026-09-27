import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.betweenVec
import Submission.Work.Mostow.segfunHasDerivAt
import Submission.Work.Mostow.segfunSpeed
import Submission.Work.Mostow.compSegfunDeriv
import Submission.Work.Mostow.diniEstimate
import Submission.Work.Mostow.propagate

/-!
# A C¹ map with `gH`-isometric differential is 1-Lipschitz

`lipschitzCurve` turns the local ("Dini") estimate `diniEstimate` into a global bound along a
curve of unit hyperbolic speed, by the propagation lemma `propagate`.  `isometryLipschitz`
applies it to the image of the geodesic segment from `u` to `v` under such a map `F`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

theorem hdist_self' (u : E n) : hdist u u = 0 := (hdist_eq_zero_iff u u).mpr rfl

theorem sinh_hdist_ne_zero_of (p q : E n) (hd : hdist p q ≠ 0) :
    Real.sinh (hdist p q) ≠ 0 :=
  fun h => hd (Real.sinh_eq_zero.mp h)

theorem segfun_zero (p q : E n) (hd : hdist p q ≠ 0) : segfun p q 0 = p := by
  simp only [segfun, sub_zero, Real.sinh_zero, zero_div, zero_smul, add_zero]
  rw [div_self (sinh_hdist_ne_zero_of p q hd), one_smul]

theorem segfun_end (p q : E n) (hd : hdist p q ≠ 0) : segfun p q (hdist p q) = q := by
  simp only [segfun, sub_self, Real.sinh_zero, zero_div, zero_smul, zero_add]
  rw [div_self (sinh_hdist_ne_zero_of p q hd), one_smul]

/-- A curve of unit hyperbolic speed has endpoint distance at most the parameter difference. -/
theorem lipschitzCurve (γ : ℝ → E n) (a b : ℝ) (hab : a ≤ b)
    (hcont : Continuous (fun p : E n × E n => hdist p.1 p.2))
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (hder : ∀ t ∈ Set.Icc a b, HasDerivAt γ (deriv γ t) t)
    (hsp : ∀ t ∈ Set.Icc a b, gH (γ t) (deriv γ t) = 1) :
    hdist (γ a) (γ b) ≤ b - a := by
  refine propagate a b hab γ ?_ htri ?_
  · have hγ : ContinuousOn γ (Set.Icc a b) :=
      fun t ht => (hder t ht).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun t : ℝ => ((γ a), γ t)) (Set.Icc a b) :=
      ContinuousOn.prodMk continuousOn_const hγ
    have h3 : ContinuousOn (fun t : ℝ => ((fun p : E n × E n => hdist p.1 p.2) ((γ a), γ t)))
        (Set.Icc a b) :=
      hcont.comp_continuousOn h2
    simpa using h3
  · intro t ht ε hε
    exact diniEstimate γ t (deriv γ t) (hder t ⟨ht.1, le_of_lt ht.2⟩)
      (hsp t ⟨ht.1, le_of_lt ht.2⟩) ε hε

/-- A `C¹` map whose differential is an isometry for `gH` is 1-Lipschitz for `hdist`. -/
theorem isometryLipschitz (F : E n → E n) (hF : ContDiff ℝ 1 F)
    (hiso : ∀ u v, gH (F u) (fderiv ℝ F u v) = gH u v)
    (hcont : Continuous (fun p : E n × E n => hdist p.1 p.2))
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z) :
    ∀ u v, hdist (F u) (F v) ≤ hdist u v := by
  intro u v
  rcases eq_or_ne u v with h | huv
  · subst h
    rw [hdist_self', hdist_self']
  · have hd : 0 < hdist u v := hdist_pos_of_ne huv
    have h1 : ∀ t ∈ Set.Icc (0 : ℝ) (hdist u v),
        HasDerivAt (fun s => F (segfun u v s)) (deriv (fun s => F (segfun u v s)) t) t := by
      intro t ht
      have hcd := (compSegfunDeriv F hF hiso u v huv t ht).1
      rw [hcd.deriv]
      exact hcd
    have h2 : ∀ t ∈ Set.Icc (0 : ℝ) (hdist u v),
        gH ((fun s => F (segfun u v s)) t) (deriv (fun s => F (segfun u v s)) t) = 1 := by
      intro t ht
      have hcd := compSegfunDeriv F hF hiso u v huv t ht
      rw [hcd.1.deriv]
      exact hcd.2
    have h3 := lipschitzCurve (fun s => F (segfun u v s)) 0 (hdist u v) hd.le hcont htri h1 h2
    have hz : segfun u v 0 = u := segfun_zero u v hd.ne'
    have he : segfun u v (hdist u v) = v := segfun_end u v hd.ne'
    simpa [Function.comp_def, hz, he] using h3

end Work.Mostow
