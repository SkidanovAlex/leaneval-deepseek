import Mathlib
import Submission.Work.Pert.Ksub2.orbit_region_uniform
import Submission.Work.Pert.Ksub2.Xc_strip_nhd_bounds
import Submission.Work.Pert.phi_ne_zero_far
import Submission.Work.Pert.exhaust_level_bound
import Submission.Work.PertCrux.phi_norm_le_of_far

/-!
# `Work.Pert.Ksub2.tau0_phi_band_norm_le`

A uniform bound for the Fatou coordinate `φ = φ₀` of a §4.1-datum on the **band**
`{|Im w| ≥ y₁, Re w ≤ 1}` for any `y₁ > η₀`, and with it the statement that every backward
translate `w - m` (`m ≥ 1`) of a point of the band lies in the maximal domain `Dφ`.

The band `B = {|Im w| ≥ y₁, Re w ≤ 1}` is unbounded, but it is controlled by the datum's
asymptotics `φ_asymp` (`τ₀ (φ w) = w + a log(-w) + b + o(1)` on the repelling sector
`QLeft ξ₀ = {π/3 < |arg (w + ξ₀)|}`):

* `B \ QLeft ξ₀` is **bounded**, by the completely elementary estimate
  `‖w‖ ≤ max ξ₀ 1 + 2 (1 + ξ₀)` (`norm_le_max_of_not_mem_QLeft`): off the sector one has
  `2 Re (w + ξ₀) ≥ ‖w + ξ₀‖` (`Work.Parab.QLeft_iff`), hence `Re (w + ξ₀) ≤ 1 + ξ₀` forces
  `|Im w| ≤ √3 (Re w + ξ₀) ≤ 2 (1 + ξ₀)` and `-ξ₀ ≤ Re w ≤ 1`;
* on `B ∩ {‖w‖ ≥ R₁}` inside the sector, `‖φ w‖ ≤ 1` for `R₁` large
  (`Work.PertCrux.phi_norm_le_of_far`);
* on the bounded rest `B ∩ {‖w‖ ≤ R}`, `φ` is continuous at every point (all points of `B` have
  `|Im| ≥ y₁ > η₀`, so `B ⊆ Dφ` by `ParabData.ends_sub`, and `Dφ` is open), hence bounded by
  compactness (`norm_phi_le_of_mem_band_ball`).
-/

namespace Work.Pert.Ksub2

open MandelDim

/-- **The band is bounded off the repelling sector.**  If `u` lies in the band (`Re u ≤ 1`; the
height condition on `u.im` is not needed) and outside Shishikura's sector `QLeft ξ`, then
`‖u‖ ≤ max ξ 1 + 2 (1 + ξ)`.  Indeed `u ∉ QLeft ξ` means `2 Re (u + ξ) ≥ ‖u + ξ‖`
(`Work.Parab.QLeft_iff`), which bounds `Im u` by `√3 (Re u + ξ) ≤ 2 (1 + ξ)` and `Re u` below
by `-ξ`. -/
lemma norm_le_max_of_not_mem_QLeft {ξ : ℝ} {u : ℂ} (hre : u.re ≤ 1)
    (hQ : u ∉ MandelDim.QLeft ξ) : ‖u‖ ≤ max ξ 1 + 2 * (1 + ξ) := by
  have h2 : ‖u + (ξ : ℂ)‖ ≤ 2 * (u + (ξ : ℂ)).re := by
    have hlt : ¬ (2 * (u + (ξ : ℂ)).re < ‖u + (ξ : ℂ)‖) :=
      fun h => hQ ((Work.Parab.QLeft_iff ξ u).mpr h)
    exact not_lt.mp hlt
  have hzre : 0 ≤ (u + (ξ : ℂ)).re := by
    have := norm_nonneg (u + (ξ : ℂ)); linarith
  have hzre' : 0 ≤ u.re + ξ := by
    rw [Complex.add_re, Complex.ofReal_re] at hzre; exact hzre
  have hsum : (u + (ξ : ℂ)).re ≤ 1 + ξ := by
    rw [Complex.add_re, Complex.ofReal_re]; linarith
  have hsq : u.im ^ 2 ≤ 3 * (u.re + ξ) ^ 2 := by
    have h2sq : ‖u + (ξ : ℂ)‖ ^ 2 ≤ (2 * (u + (ξ : ℂ)).re) ^ 2 := by
      nlinarith [h2, norm_nonneg (u + (ξ : ℂ))]
    have h1 : ‖u + (ξ : ℂ)‖ ^ 2 = (u + (ξ : ℂ)).re ^ 2 + (u + (ξ : ℂ)).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h3 : (u + (ξ : ℂ)).im = u.im := by simp
    have h4 : (u + (ξ : ℂ)).re = u.re + ξ := by simp
    rw [h1, h3, h4] at h2sq
    nlinarith [h2sq]
  have him : |u.im| ≤ 2 * (1 + ξ) := by
    have h2' : u.im ^ 2 ≤ (2 * (1 + ξ)) ^ 2 := by
      have h5 : (u.re + ξ) ^ 2 ≤ (1 + ξ) ^ 2 := pow_le_pow_left₀ hzre' hsum 2
      nlinarith [hsq, h5]
    rw [sq_le_sq] at h2'
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + ξ))] at h2'
  have hreabs : |u.re| ≤ max ξ 1 := by
    have h1 : -ξ ≤ u.re := by linarith [hzre']
    rw [abs_le]
    constructor
    · have h2 : -(max ξ 1) ≤ -ξ := by
        have : ξ ≤ max ξ 1 := le_max_left _ _
        linarith
      linarith
    · have h2 : (1 : ℝ) ≤ max ξ 1 := le_max_right _ _
      linarith
  calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    _ ≤ max ξ 1 + 2 * (1 + ξ) := by linarith

/-- **Boundedness of `φ` on a bounded piece of the band.**  For `y₁ > η₀` and any radius `R`, the
Fatou coordinate `φ` is bounded on `{y₁ ≤ |Im u|} ∩ {Re u ≤ 1} ∩ {‖u‖ ≤ R}`: that set is compact
and contained in the open maximal domain `Dφ` (every point of it has `|Im| ≥ y₁ > η₀`), so `φ` is
continuous there and compactness gives the bound. -/
lemma norm_phi_le_of_mem_band_ball {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y₁ R : ℝ} (hy : d.η₀ < y₁) :
    ∃ C : ℝ, ∀ u : ℂ, y₁ ≤ |u.im| → u.re ≤ 1 → ‖u‖ ≤ R → ‖d.φ u‖ ≤ C := by
  have hset : {u : ℂ | y₁ ≤ |u.im| ∧ u.re ≤ 1 ∧ ‖u‖ ≤ R}
      = {u : ℂ | y₁ ≤ |u.im|} ∩ ({u : ℂ | u.re ≤ 1} ∩ {u : ℂ | ‖u‖ ≤ R}) := by
    ext u; tauto
  have hKc : IsCompact {u : ℂ | y₁ ≤ |u.im| ∧ u.re ≤ 1 ∧ ‖u‖ ≤ R} := by
    rw [hset]
    refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le continuous_norm continuous_const))
    · intro u hu
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hu.2.2
  have hsub : {u : ℂ | y₁ ≤ |u.im| ∧ u.re ≤ 1 ∧ ‖u‖ ≤ R} ⊆ d.Dφ := by
    intro u hu
    exact (d.ends_sub u (lt_of_lt_of_le hy hu.1)).1
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn ((d.φ_holo.mono hsub).continuousOn)
  exact ⟨C, fun u h1 h2 h3 => hC u ⟨h1, h2, h3⟩⟩

theorem tau0_phi_band_norm_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y₁ : ℝ} (hy0 : 0 < y₁) (hy : d.η₀ < y₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, y₁ ≤ |w.im| → w.re ≤ 1 → ∀ m : ℕ, 1 ≤ m →
      w - (m : ℂ) ∈ d.Dφ ∧ ‖d.φ (w - (m : ℂ))‖ ≤ C := by
  -- far out inside the sector the coordinate is small
  obtain ⟨R₁, hR₁pos, hfar⟩ := Work.PertCrux.phi_norm_le_of_far d (c := 1) one_pos
  -- the bounded piece of the band
  obtain ⟨Cfix, hCfix⟩ :=
    norm_phi_le_of_mem_band_ball d hy (y₁ := y₁) (R := max (max d.ξ₀ 1 + 2 * (1 + d.ξ₀)) R₁)
  refine ⟨max 1 Cfix, lt_max_of_lt_left one_pos, ?_⟩
  intro w hwim hwre m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have him : (w - (m : ℂ)).im = w.im := by simp
  have hre : (w - (m : ℂ)).re = w.re - (m : ℝ) := by simp
  have hre1 : (w - (m : ℂ)).re ≤ 1 := by rw [hre]; linarith
  have hmwim : y₁ ≤ |(w - (m : ℂ)).im| := by rw [him]; exact hwim
  refine ⟨(d.ends_sub _ (lt_of_lt_of_le hy hmwim)).1, ?_⟩
  by_cases hQ : (w - (m : ℂ)) ∈ MandelDim.QLeft d.ξ₀
  · by_cases hR₁ : ‖w - (m : ℂ)‖ ≤ R₁
    · refine le_trans (hCfix _ hmwim hre1 ?_) (le_max_right _ _)
      exact le_trans hR₁ (le_max_right _ _)
    · exact le_trans (hfar _ hQ (le_of_lt (not_le.mp hR₁))) (le_max_left _ _)
  · refine le_trans (hCfix _ hmwim hre1 ?_) (le_max_right _ _)
    exact le_trans (norm_le_max_of_not_mem_QLeft hre1 hQ) (le_max_left _ _)

end Work.Pert.Ksub2
