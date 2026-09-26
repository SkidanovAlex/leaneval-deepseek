import Mathlib

/-! # The automorphisms of the unit disc `z ↦ (z - a)/(1 - āz)`.

Auxiliary lemmas for `Work.Smooth.SphereJordan.planeDomain_homeo_unitBall`.

* `unitDisc_mobius_map` : for `‖a‖ < 1` the map `z ↦ (z - a)/(1 - star a * z)` is defined and
  maps the open unit disc into itself;
* `unitDisc_mobius_inj` : it is injective on the open unit disc;
* `unitDisc_mobius_hasDerivAt` : its derivative, equal to
  `(1 - ‖a‖²)/(1 - star a * z)²`.
-/

namespace Work.Smooth.SphereJordan

open Metric

lemma star_mul_self_eq (a : ℂ) : star a * a = ((Complex.normSq a : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.normSq_eq_norm_sq]
  push_cast
  ring

lemma mul_star_self_eq (a : ℂ) : a * star a = ((Complex.normSq a : ℝ) : ℂ) := by
  rw [Complex.star_def]; exact Complex.mul_conj a

lemma normSq_unitDisc_mobius (a z : ℂ) :
    Complex.normSq (1 - star a * z) - Complex.normSq (z - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.star_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem unitDisc_mobius_map (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - star a * z ≠ 0 ∧ ‖(z - a) / (1 - star a * z)‖ < 1 := by
  have ha' : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz' : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hkey := normSq_unitDisc_mobius a z
  have hpos : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq z) :=
    mul_pos (by linarith) (by linarith)
  have hlt : Complex.normSq (z - a) < Complex.normSq (1 - star a * z) := by linarith
  have hden : 1 - star a * z ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hlt
    have := Complex.normSq_nonneg (z - a)
    linarith
  have h1 : ‖z - a‖ ^ 2 < ‖1 - star a * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hlt
  have h2 : ‖z - a‖ < ‖1 - star a * z‖ := by
    have h3 := sq_lt_sq.mp h1
    simpa [abs_of_nonneg (norm_nonneg _)] using h3
  refine ⟨hden, ?_⟩
  rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) h2)]
  exact h2

theorem unitDisc_mobius_inj (a z w : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (h : (z - a) / (1 - star a * z) = (w - a) / (1 - star a * w)) : z = w := by
  have hz' : (1 : ℂ) - star a * z ≠ 0 := (unitDisc_mobius_map a z ha hz).1
  have hw' : (1 : ℂ) - star a * w ≠ 0 := (unitDisc_mobius_map a w ha hw).1
  have ha' : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h' : (z - a) * (1 - star a * w) = (w - a) * (1 - star a * z) :=
    (div_eq_div_iff hz' hw').mp h
  have h4 : (z - w) * (1 - star a * a) = 0 := by
    have h5 : (z - a) * (1 - star a * w) - (w - a) * (1 - star a * z)
        = (z - w) * (1 - star a * a) := by ring
    rw [h', sub_self] at h5
    exact h5.symm
  have h6 : (1 : ℂ) - ((Complex.normSq a : ℝ) : ℂ) ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    simp at hre
    linarith
  rw [star_mul_self_eq] at h4
  rcases mul_eq_zero.mp h4 with h7 | h7
  · exact sub_eq_zero.mp h7
  · exact absurd h7 h6

theorem unitDisc_mobius_hasDerivAt (a z : ℂ) (hne : (1 : ℂ) - star a * z ≠ 0) :
    HasDerivAt (fun w => (w - a) / (1 - star a * w))
      ((1 - ((Complex.normSq a : ℝ) : ℂ)) / (1 - star a * z) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have hden : HasDerivAt (fun w : ℂ => 1 - star a * w) (-(star a)) z := by
    simpa using ((hasDerivAt_id z).const_mul (star a)).const_sub (1 : ℂ)
  have h := hnum.div hden hne
  have hnum_eq : (1 : ℂ) * (1 - star a * z) - (z - a) * (-(star a))
      = 1 - ((Complex.normSq a : ℝ) : ℂ) := by
    have hz1 : star a * z = z * star a := mul_comm _ _
    have ha1 : a * star a = ((Complex.normSq a : ℝ) : ℂ) := mul_star_self_eq a
    rw [hz1]
    rw [show (1 : ℂ) * (1 - z * star a) - (z - a) * (-(star a)) = 1 - a * star a by ring]
    rw [ha1]
  rw [hnum_eq] at h
  exact h

end Work.Smooth.SphereJordan
