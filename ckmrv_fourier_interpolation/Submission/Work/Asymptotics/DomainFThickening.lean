/-
# The `1/16`-thickening `nbdF` of `closure 𝓕`

The geometric lemma `Work.Asymptotics.exists_neighbour_nbdh_of_Propagates` needs an open
neighbourhood `O_F` of `closure 𝓕` with the property that no *non*-neighbour `γ ∈ SL(2,ℤ)`
sends a point of `O_F` into `O_F`.  The proof shrinks a neighbourhood produced by
`Work.Asymptotics.exists_Mp_nbdh` further to the explicit thickening

  `nbdF = {z ∈ ℍ : -1/16 < Re z < 1 + 1/16, ‖z‖ > 15/16, ‖z - 1‖ > 15/16}`

of `closure 𝓕 = {0 ≤ Re z ≤ 1, ‖z‖ ≥ 1, ‖z - 1‖ ≥ 1}` (CKMRV (3.13)), and then checks the
finitely many possible matrices by hand.

This file collects the elementary facts about `nbdF` used by the argument:

* `closure_DomainF_subset_nbdF` : `nbdF` really is a neighbourhood of `closure 𝓕`;
* `im_gt_of_mem_nbdF` : every point of `nbdF` has imaginary part `> 3/4` (so that the
  imaginary part of a Möbius image, which is `Im z / ‖c z + d‖²`, is bounded below);
* `sep_nbdF` : a point of `nbdF` is at distance `> 6/5` from every integer `α ∉ {0, 1}`
  (this is what rules out the images `a - 1/z` of the boundary pairings).
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateMpDefs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The open `1/16`-thickening of `closure 𝓕`: the closure of CKMRV's fundamental domain
`𝓕` (3.13) has `0 ≤ Re z ≤ 1`, `‖z‖ ≥ 1`, `‖z - 1‖ ≥ 1`, and `nbdF` relaxes all four
inequalities by `1/16`. -/
def nbdF : Set UpperHalfPlane :=
  {z | -(1 / 16 : ℝ) < z.re ∧ z.re < 1 + 1 / 16 ∧ (15 / 16 : ℝ) < ‖(z : ℂ)‖ ∧
    (15 / 16 : ℝ) < ‖(z : ℂ) - 1‖}

lemma mem_nbdF {z : UpperHalfPlane} :
    z ∈ nbdF ↔ -(1 / 16 : ℝ) < z.re ∧ z.re < 1 + 1 / 16 ∧ (15 / 16 : ℝ) < ‖(z : ℂ)‖ ∧
      (15 / 16 : ℝ) < ‖(z : ℂ) - 1‖ := Iff.rfl

lemma isOpen_nbdF : IsOpen nbdF := by
  have h1 : IsOpen {z : UpperHalfPlane | -(1 / 16 : ℝ) < z.re} :=
    isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have h2 : IsOpen {z : UpperHalfPlane | z.re < 1 + 1 / 16} :=
    isOpen_lt UpperHalfPlane.continuous_re continuous_const
  have h3 : IsOpen {z : UpperHalfPlane | (15 / 16 : ℝ) < ‖(z : ℂ)‖} :=
    isOpen_lt continuous_const continuous_coe.norm
  have h4 : IsOpen {z : UpperHalfPlane | (15 / 16 : ℝ) < ‖(z : ℂ) - 1‖} :=
    isOpen_lt continuous_const (continuous_coe.sub continuous_const).norm
  rw [show nbdF = {z : UpperHalfPlane | -(1 / 16 : ℝ) < z.re} ∩
      {z : UpperHalfPlane | z.re < 1 + 1 / 16} ∩ {z : UpperHalfPlane | (15 / 16 : ℝ) < ‖(z : ℂ)‖} ∩
      {z : UpperHalfPlane | (15 / 16 : ℝ) < ‖(z : ℂ) - 1‖} from by ext z; simp [nbdF, and_assoc]]
  exact ((h1.inter h2).inter h3).inter h4

/-- `closure 𝓕` is contained in the *closed* region cut out by the non-strict versions of the
defining inequalities of `𝓕`. -/
lemma closure_DomainF_subset_closedRegion :
    closure DomainF ⊆
      {z : UpperHalfPlane | 0 ≤ z.re ∧ z.re ≤ 1 ∧ (1 : ℝ) ≤ ‖(z : ℂ)‖ ∧
        1 ≤ ‖(z : ℂ) - 1‖} := by
  refine closure_minimal (fun z hz => ?_) ?_
  · rw [mem_DomainF] at hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  · refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_le continuous_const UpperHalfPlane.continuous_re
    · exact isClosed_le UpperHalfPlane.continuous_re continuous_const
    · exact isClosed_le continuous_const continuous_coe.norm
    · exact isClosed_le continuous_const (continuous_coe.sub continuous_const).norm

/-- `nbdF` is a neighbourhood of `closure 𝓕`. -/
lemma closure_DomainF_subset_nbdF : closure DomainF ⊆ nbdF := by
  refine closure_DomainF_subset_closedRegion.trans (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Points of `nbdF` have imaginary part `> 3/4`. -/
lemma im_gt_of_mem_nbdF {z : UpperHalfPlane} (hz : z ∈ nbdF) : (3 / 4 : ℝ) < z.im := by
  rw [mem_nbdF] at hz
  obtain ⟨hx1, hx2, hn, hn1⟩ := hz
  have hn' : (15 / 16 : ℝ) ^ 2 < ‖(z : ℂ)‖ ^ 2 := by
    have := norm_nonneg (z : ℂ); nlinarith
  have hn1' : (15 / 16 : ℝ) ^ 2 < ‖(z : ℂ) - 1‖ ^ 2 := by
    have := norm_nonneg ((z : ℂ) - 1); nlinarith
  have hz2 : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hz1' : ‖(z : ℂ) - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  by_cases hle : z.re ≤ 1 / 2
  · have hre2 : z.re ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
    have : (161 / 256 : ℝ) < z.im ^ 2 := by rw [hz2] at hn'; linarith
    nlinarith [z.im_pos]
  · have hre : -(1 / 2 : ℝ) ≤ z.re - 1 := by linarith [not_le.mp hle]
    have hre1 : z.re - 1 ≤ (1 / 2 : ℝ) := by linarith [hx2]
    have hre2 : (z.re - 1) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
    have : (161 / 256 : ℝ) < z.im ^ 2 := by rw [hz1'] at hn1'; linarith
    nlinarith [z.im_pos]

/-- A point of `nbdF` is at distance `> 6/5` from every integer `α ∉ {0, 1}`. -/
lemma sep_nbdF {α : ℤ} (h0 : α ≠ 0) (h1 : α ≠ 1) {w : UpperHalfPlane} (hw : w ∈ nbdF) :
    (6 / 5 : ℝ) < ‖(w : ℂ) - (α : ℂ)‖ := by
  rw [mem_nbdF] at hw
  obtain ⟨hu1, hu2, hn, hn1⟩ := hw
  have hn' : (15 / 16 : ℝ) ^ 2 < ‖(w : ℂ)‖ ^ 2 := by
    have := norm_nonneg (w : ℂ); nlinarith
  have hn1' : (15 / 16 : ℝ) ^ 2 < ‖(w : ℂ) - 1‖ ^ 2 := by
    have := norm_nonneg ((w : ℂ) - 1); nlinarith
  have hw2 : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hw1 : ‖(w : ℂ) - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hsq : ‖(w : ℂ) - (α : ℂ)‖ ^ 2 = (w.re - (α : ℝ)) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hb1 : (15 / 16 : ℝ) ^ 2 - w.re ^ 2 < w.im ^ 2 := by
    linarith [hn', hw2]
  have hb2 : (15 / 16 : ℝ) ^ 2 - (w.re - 1) ^ 2 < w.im ^ 2 := by
    linarith [hn1', hw1]
  have him2 : (15 / 16 : ℝ) ^ 2 - 1 / 4 < w.im ^ 2 := by
    rcases le_total w.re (1 / 2) with h | h
    · have h' : w.re ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith [hu1]
      linarith [hb1]
    · have h' : (w.re - 1) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith [hu2, h]
      linarith [hb2]
  have hnum : (6 / 5 : ℝ) ^ 2 < (15 / 16 : ℝ) ^ 2 + (15 / 16 : ℝ) ^ 2 - 1 / 4 := by norm_num
  have hnum2 : (6 / 5 : ℝ) ^ 2 < (15 / 16 : ℝ) ^ 2 + 7 / 8 := by norm_num
  rcases lt_or_gt_of_ne h0 with ha | ha
  · -- `α ≤ -1`
    have hα : (α : ℝ) ≤ -1 := by
      have h2 : α ≤ (-1 : ℤ) := by omega
      exact_mod_cast h2
    have hge' : w.re + 1 ≤ w.re - (α : ℝ) := by linarith
    have hge : (w.re + 1) ^ 2 ≤ (w.re - (α : ℝ)) ^ 2 := by
      have h0' : (0 : ℝ) < w.re - (α : ℝ) := by linarith
      nlinarith [hge', h0']
    have hsplit : w.re ^ 2 + 7 / 8 ≤ (w.re + 1) ^ 2 := by linarith [hu1]
    have h3 : w.re ^ 2 + 7 / 8 ≤ (w.re - (α : ℝ)) ^ 2 := le_trans hsplit hge
    have h2 : (6 / 5 : ℝ) ^ 2 < (w.re - (α : ℝ)) ^ 2 + w.im ^ 2 := by
      linarith [h3, hb1, hnum2]
    rw [← hsq] at h2
    nlinarith [norm_nonneg ((w : ℂ) - (α : ℂ)), h2]
  · -- `2 ≤ α`
    have hα : (2 : ℝ) ≤ (α : ℝ) := by
      have h2 : (2 : ℤ) ≤ α := by omega
      exact_mod_cast h2
    have hlt : w.re - (α : ℝ) ≤ -(15 / 16 : ℝ) := by linarith [hu2, hα]
    have hge : (15 / 16 : ℝ) ^ 2 ≤ (w.re - (α : ℝ)) ^ 2 := by nlinarith [hlt]
    have h3 : (15 / 16 : ℝ) ^ 2 + ((15 / 16 : ℝ) ^ 2 - 1 / 4) <
        (w.re - (α : ℝ)) ^ 2 + w.im ^ 2 := by linarith
    have h2 : (6 / 5 : ℝ) ^ 2 < (w.re - (α : ℝ)) ^ 2 + w.im ^ 2 := by
      linarith [h3, hnum]
    rw [← hsq] at h2
    nlinarith [norm_nonneg ((w : ℂ) - (α : ℂ)), h2]

end Work.Asymptotics
