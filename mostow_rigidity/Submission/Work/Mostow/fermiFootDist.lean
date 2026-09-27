import Mathlib
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.blkMap_linBlk

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-! ### Elementary facts about `hdist` and the Fermi chart

We need the general identity `cosh (hdist u v) = tpart u * tpart v - inner u v`
and its consequence `cosh (hdist v v) = 1`, plus `0 ≤ hdist`, together with the
observation that `coordEmb k m v = fermi k m v 0` is the foot of the Fermi chart.
-/

/-- `tpart u ^ 2 = 1 + ‖u‖ ^ 2`. -/
private lemma tpart_sq_aux {n : ℕ} (u : E n) : tpart u ^ 2 = 1 + ‖u‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Reverse Cauchy–Schwarz in the chart: the argument of `arcosh` is at least `1`. -/
private lemma one_le_hdist_arg {n : ℕ} (u v : E n) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have ha : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by nlinarith [sq_nonneg ‖u‖])]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

/-- `cosh (hdist u v) = tpart u * tpart v - inner u v`. -/
private lemma cosh_hdist_aux {n : ℕ} (u v : E n) :
    Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist]; exact Real.cosh_arcosh (one_le_hdist_arg u v)

/-- `0 ≤ hdist u v`. -/
private lemma hdist_nonneg_aux {n : ℕ} (u v : E n) : 0 ≤ hdist u v := by
  rw [hdist]; exact Real.arcosh_nonneg (one_le_hdist_arg u v)

/-- `cosh (hdist v v) = 1`. -/
private lemma cosh_hdist_self {n : ℕ} (v : E n) : Real.cosh (hdist v v) = 1 := by
  have h : tpart v * tpart v - inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h2 := tpart_sq_aux v
    nlinarith
  rw [cosh_hdist_aux, h]

/-- The standard stratum point `coordEmb k m v` is the foot `fermi k m v 0`. -/
private lemma coordEmb_eq_fermi_zero (k m : ℕ) (v : E k) :
    coordEmb k m v = fermi k m v 0 := by
  ext i
  simp [coordEmb, fermi]

/-- The distance-squared formula for a Fermi point and an arbitrary stratum point. -/
private lemma cosh_hdist_fermi_coordEmb {k m : ℕ} (v v' : E k) (w : E m) :
    Real.cosh (hdist (fermi k m v w) (coordEmb k m v'))
      = Real.cosh ‖w‖ * Real.cosh (hdist v v') := by
  rw [coordEmb_eq_fermi_zero, cosh_hdist_fermi]
  simp [sinhc]

open Submission.Mostow in
theorem fermiFootDist (k m : ℕ) :
    (∀ (v : E k) (w : E m), hdist (fermi k m v w) (coordEmb k m v) = ‖w‖) ∧
    (∀ (v v' : E k) (w : E m), ‖w‖ ≤ hdist (fermi k m v w) (coordEmb k m v')) ∧
    (∀ u : E (k + m), hdist u (coordEmb k m (fermiInv k m u).1) = Real.arsinh ‖nrmC k m u‖) ∧
    (∀ (u : E (k + m)) (v' : E k), Real.arsinh ‖nrmC k m u‖ ≤ hdist u (coordEmb k m v')) := by
  have h1 : ∀ (v : E k) (w : E m), hdist (fermi k m v w) (coordEmb k m v) = ‖w‖ := by
    intro v w
    have hk : Real.cosh (hdist (fermi k m v w) (coordEmb k m v)) = Real.cosh ‖w‖ := by
      rw [cosh_hdist_fermi_coordEmb v v w, cosh_hdist_self, mul_one]
    exact Real.cosh_injOn (hdist_nonneg_aux _ _) (norm_nonneg w) hk
  have h2 : ∀ (v v' : E k) (w : E m), ‖w‖ ≤ hdist (fermi k m v w) (coordEmb k m v') := by
    intro v v' w
    have hcos : Real.cosh ‖w‖ ≤ Real.cosh (hdist (fermi k m v w) (coordEmb k m v')) := by
      rw [cosh_hdist_fermi_coordEmb v v' w]
      have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh (hdist v v')) (Real.cosh_pos ‖w‖).le
      simpa using h
    have h := Real.cosh_le_cosh.mp hcos
    rwa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg (hdist_nonneg_aux _ _)] at h
  refine ⟨h1, h2, ?_, ?_⟩
  · intro u
    have hf : fermi k m (fermiInv k m u).1 (fermiInv k m u).2 = u := (fermi_inv k m).2.1 u
    have hc : hdist (fermi k m (fermiInv k m u).1 (fermiInv k m u).2)
        (coordEmb k m (fermiInv k m u).1) = ‖(fermiInv k m u).2‖ := h1 _ _
    rw [hf] at hc
    rw [hc, norm_fermiInv_snd]
  · intro u v'
    have hf : fermi k m (fermiInv k m u).1 (fermiInv k m u).2 = u := (fermi_inv k m).2.1 u
    have hc : ‖(fermiInv k m u).2‖ ≤ hdist (fermi k m (fermiInv k m u).1 (fermiInv k m u).2)
        (coordEmb k m v') := h2 _ _ _
    rw [hf] at hc
    rw [← norm_fermiInv_snd]
    exact hc

end

end Work.Mostow
