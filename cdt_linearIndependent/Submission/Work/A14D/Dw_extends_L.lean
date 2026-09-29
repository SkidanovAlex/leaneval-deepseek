import Mathlib
import Submission.Work.A14D.Dw_extends
import Submission.Work.A14D.LC_setup
import Submission.Work.A14.defs

/-!
# `Work.A14D.Dw_extends_L`: the `w`-pullback extends across `1/9` (lower half statement)

This is the mirror image of `Work.A14D.Dw_extends` (`Submission/Work/A14D/Dw_extends.lean`.
There the extension of `z ↦ D (wC z)` was asserted on the *upper* half `halfU δ` of the disc
`ball (1/9) δ`.  Here the same extension `De` is required to reproduce `D ∘ wC` on the *lower*
half `halfL δ = ball (1/9) δ ∩ {Im < 0}`.

The geometry is the mirror image of the one in `Dw_extends`.  The deck involution `wC` swaps the
two half planes, and `wC (halfL δ) ⊆ ball (−1/8) (1/10) ∩ {Im > 0}`.  So instead of taking the
Cauchy data of `D` at a point of the *lower* half of the disc `discW = ball (−1/8) (1/10)` (as in
`Dw_extends`), we take them at the point `−1/8 + i/100` in its *upper* half, continue `D` across
the cut there, and conclude.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- `w` maps the open lower half plane into the open upper half plane: for `z = x + iy` with
`y < 0` one has `Im w(z) = −y/‖z−1‖² > 0`.  (Mirror image of `wC_im_neg_of_pos`.) -/
private lemma wC_im_pos_of_neg {z : ℂ} (hz : z.im < 0) : 0 < (wC z).im := by
  rw [wC, Complex.div_im]
  have h1 : (z - 1).im = z.im := by simp
  have h2 : (z - 1).re = z.re - 1 := by simp
  rw [h1, h2]
  have hN : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]
    intro hc
    have : (z - 1).im = 0 := by rw [hc]; simp
    simp at this
    linarith
  have hnum : z.im * (z.re - 1) - z.re * z.im = -z.im := by ring
  rw [← sub_div, hnum]
  exact div_pos (by linarith) hN

/-- **Extension of the `w`-pullback across the cut, lower-half form.**  Let `D` be a holomorphic
solution of `LZ y = 0` on the slit plane `Om1 = ℂ ∖ (−∞,1]`.  Then for every `0 < δ ≤ 1/20` the
function `z ↦ D (wC z)`, which is holomorphic on the lower half `halfL δ` of the disc
`ball (1/9) δ` (since `wC` sends the lower half plane into the upper half plane, where `D` is
defined), extends holomorphically to the whole disc `ball (1/9) δ`. -/
theorem Dw_extends_L {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1)
    (hDL : ∀ z ∈ Om1, LZ D z = 0) {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    ∃ De : ℂ → ℂ, DifferentiableOn ℂ De (Metric.ball ninth δ) ∧
      ∀ z ∈ halfL δ, De z = D (wC z) := by
  have hΩo : IsOpen discW := by rw [discW]; exact Metric.isOpen_ball
  have hΩc : Convex ℝ discW := by rw [discW]; exact convex_ball (-(1 / 8) : ℂ) (1 / 10)
  have hPZ : ∀ z ∈ discW, PZ z ≠ 0 := by
    intro z hz
    rw [discW] at hz
    exact PZ_ne_zero_near_neg_eighth hz
  -- the base point `z₀ = −1/8 + i/100` lies in the *upper* half of `discW`
  have hz₀W : ((-(1 / 8) : ℂ) + (1 / 100 : ℝ) * Complex.I) ∈ discW := by
    rw [discW, Metric.mem_ball, Complex.dist_eq]
    norm_num [Complex.normSq_apply, Complex.norm_def]
  have hz₀im : 0 < ((-(1 / 8) : ℂ) + (1 / 100 : ℝ) * Complex.I).im := by simp
  -- Cauchy data at `z₀` of `D` (which is defined on `Om1 ∋ z₀` since `Im z₀ > 0`)
  obtain ⟨E, hEdiff, hEz₀, hEd, -, hEL⟩ :=
    exists_sol_LZ_convex hΩo hΩc hPZ hz₀W
      (D ((-(1 / 8) : ℂ) + (1 / 100 : ℝ) * Complex.I))
      (deriv D ((-(1 / 8) : ℂ) + (1 / 100 : ℝ) * Complex.I))
  -- `D` and `E` agree on the (open, convex, hence preconnected) upper half of `discW`
  have hUo : IsOpen (discW ∩ {z : ℂ | 0 < z.im}) := by
    rw [discW]
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hUpc : IsPreconnected (discW ∩ {z : ℂ | 0 < z.im}) := by
    rw [discW]
    exact ((convex_ball (-(1 / 8) : ℂ) (1 / 10)).inter
      (convex_halfSpace_im_gt 0)).isPreconnected
  have hUOm1 : (discW ∩ {z : ℂ | 0 < z.im}) ⊆ Om1 := fun z hz => Or.inl (ne_of_gt hz.2)
  have hz₀U : ((-(1 / 8) : ℂ) + (1 / 100 : ℝ) * Complex.I) ∈ discW ∩ {z : ℂ | 0 < z.im} :=
    ⟨hz₀W, hz₀im⟩
  have hEqUD : Set.EqOn E D (discW ∩ {z : ℂ | 0 < z.im}) :=
    eqOn_of_sol_LZ hUo hUpc (fun z hz => hPZ z hz.1)
      (hEdiff.mono Set.inter_subset_left) (hD.mono hUOm1)
      (fun z hz => hEL z hz.1) (fun z hz => hDL z (hUOm1 hz))
      hz₀U hEz₀ hEd
  -- assembly: the extension is the `w`-pullback of `E`
  have hmaps : Set.MapsTo wC (Metric.ball ninth δ) discW := by
    intro z hz
    rw [discW, Metric.mem_ball, Complex.dist_eq]
    have hdist : wC z - (-(1 / 8) : ℂ) = wC z + 1 / 8 := by ring
    rw [hdist]
    exact norm_wC_add_eighth_lt hδ20 hz
  refine ⟨fun z => E (wC z), hEdiff.comp (differentiableOn_wC_ball hδ20) hmaps, ?_⟩
  intro z hz
  exact hEqUD ⟨hmaps hz.1, wC_im_pos_of_neg hz.2⟩

end

end Work.A14D
