import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.H2.T1Q.ExpandQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.T3Q.EasyMajorBoundQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Vanishing of the two weights (and of `T1Easy`) on the boundary lines

`T1Easy α f g = H4PairInt α (f·D_θg) g - T1Hard α f g` is a finite sum of terms each of which
carries a factor `Whz²` resp. `Wm²` (in `H4PairInt`) or a factor `w² sin(2θ)^{-q}` (in
`T1Hard`).  Both weights vanish on the two angular boundary lines `θ = 0`, `θ = π/2`
(`sin(2θ) = 0` and the exponents `η/2`, `γ/2` are positive) and on the radial line `z = 0`
(`w 0 = 0`).  Since `HkIntegrand α 4 g` also vanishes where `sin(2θ) = 0`, the pointwise bound
of `EasyTheta` is trivial on the boundary and the Leibniz expansion (which is available on the
open quadrant only) only has to be invoked in the interior. -/

theorem eta_half_ne_zero : Work.Spaces.eta / 2 ≠ 0 := by
  unfold Work.Spaces.eta; norm_num

theorem eta_ne_zero : Work.Spaces.eta ≠ 0 := by
  unfold Work.Spaces.eta; norm_num

theorem sin_two_rpow_eq_zero_of_sin_eq_zero {θ c : ℝ} (h : Real.sin (2 * θ) = 0) (hc : c ≠ 0) :
    (Real.sin (2 * θ)) ^ c = 0 := by
  simp only [h, Real.zero_rpow hc]

theorem Whz_eq_zero_of_sin_eq_zero (z θ : ℝ) (h : Real.sin (2 * θ) = 0) :
    Work.FTS.H2.Whz z θ = 0 := by
  simp only [Work.FTS.H2.Whz, sin_two_rpow_eq_zero_of_sin_eq_zero h eta_half_ne_zero,
    div_zero]

theorem Wm_eq_zero_of_sin_eq_zero (α : ℝ) (hα : 0 < α) (z θ : ℝ)
    (h : Real.sin (2 * θ) = 0) : Work.FTS.H2.Wm α z θ = 0 := by
  have hc : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hh
    have h1 : Work.Spaces.gam α = 0 := by linarith [neg_eq_zero.mp hh]
    exact absurd h1 (ne_of_gt (Work.Spaces.gam_pos hα))
  simp only [Work.FTS.H2.Wm, Work.Spaces.Wt, Work.Spaces.wTheta,
    sin_two_rpow_eq_zero_of_sin_eq_zero h hc, mul_zero]

/-- On the two angular boundary lines the whole integrand `T1Easy` vanishes. -/
theorem T1Easy_eq_zero_of_sin_eq_zero (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.FTS.H2.T1Easy α f g z θ = 0 := by
  have hWhz := Whz_eq_zero_of_sin_eq_zero z θ h
  have hWm := Wm_eq_zero_of_sin_eq_zero α hα z θ h
  have hH4 : Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ = 0 := by
    simp only [Work.FTS.H2.H4PairInt, hWhz, hWm]
    simp
  have hT1H : Work.FTS.H2.T1Hard α f g z θ = 0 := by
    have h1 : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) = 0 :=
      sin_two_rpow_eq_zero_of_sin_eq_zero h (neg_ne_zero.mpr eta_ne_zero)
    have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 :=
      sin_two_rpow_eq_zero_of_sin_eq_zero h
        (neg_ne_zero.mpr (ne_of_gt (Work.Spaces.gam_pos hα)))
    simp only [Work.FTS.H2.T1Hard, h1, h2, mul_zero, add_zero]
  rw [Work.FTS.H2.T1Easy, hH4, hT1H, sub_zero]

theorem Whz_eq_zero_of_z_eq_zero (θ : ℝ) : Work.FTS.H2.Whz 0 θ = 0 := by
  simp only [Work.FTS.H2.Whz, Work.Spaces.w]
  norm_num

theorem Wm_eq_zero_of_z_eq_zero (α θ : ℝ) : Work.FTS.H2.Wm α 0 θ = 0 := by
  simp only [Work.FTS.H2.Wm, Work.Spaces.Wt, Work.Spaces.w]
  norm_num

/-- On the radial boundary line `z = 0` the whole integrand `T1Easy` vanishes. -/
theorem T1Easy_eq_zero_of_z_eq_zero (α : ℝ) (f g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.FTS.H2.T1Easy α f g 0 θ = 0 := by
  have hWhz := Whz_eq_zero_of_z_eq_zero θ
  have hWm := Wm_eq_zero_of_z_eq_zero α θ
  have hw : Work.Spaces.w 0 = 0 := by simp only [Work.Spaces.w]; norm_num
  have hH4 : Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g 0 θ = 0 := by
    simp only [Work.FTS.H2.H4PairInt, hWhz, hWm]
    simp
  have hT1H : Work.FTS.H2.T1Hard α f g 0 θ = 0 := by
    simp only [Work.FTS.H2.T1Hard, hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_mul]
  rw [Work.FTS.H2.T1Easy, hH4, hT1H, sub_zero]

/-- The "easy" part of Elgindi's `Transport3` for the `D_θ`-pairing in the interior class: with
`T1Easy α f g = H4PairInt α (f·D_θg) g - T1Hard α f g` (all Leibniz summands except the five in
which five derivatives fall on `g`), for `f` smooth on the open quadrant with finite
`𝒲^{4,∞}`-norm and `g` smooth on the open quadrant with `g ∈ ℋ⁴`, the integrand is bounded
pointwise by `C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g` and its angular slices are integrable.
Route: expand `H4PairInt` by the Leibniz rules for `SmoothQuad` (`Work.FTS.H2.WPQ.Leibniz`),
remove the five `T1Hard` summands, bound every `f`-factor by `30|f|_𝒲`
(`Work.FTS.H2.WPQ.DzIter_le_WlInf`, `Work.FTS.H2.WPQ.Mixed_le_WlInf`) and apply AM–GM to the
two `g`-blocks (every surviving summand has both `g`-blocks of total order `≤ 4` and, whenever
the weight is `Wm²`, both blocks carry at least one `θ`-derivative). -/
theorem EasyTheta : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.H2.T1Easy α f g z θ| ≤ C * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ) ∧
    (∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.T1Easy α f g z θ) Work.Spaces.Iθ) := by
  obtain ⟨C, hCpos, hC⟩ := EasyMajorBoundQ
  refine ⟨C, hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm
  have hgam : Work.Spaces.gam α ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hα)
  -- the pointwise bound, on the open quadrant from the Leibniz expansion and on the two
  -- angular boundary lines by the vanishing of both sides
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.H2.T1Easy α f g z θ| ≤ C * Work.Spaces.WlInf α 4 f
        * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- `θ = 0`
      subst h0
      rw [T1Easy_eq_zero_of_sin_eq_zero α hα f g (by simp : Real.sin (2 * 0) = 0)]
      rw [Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero hgam
        (by simp : Real.sin (2 * 0) = 0)]
      simp
    · rcases lt_or_eq_of_le hθ.2 with h2 | h2
      · -- interior: `|T1Easy| ≤ EasyMajor ≤ C |f|_𝓦 HkIntegrand`
        exact le_trans (Work.FTS.H2.T1Easy_le_majorQ α hα f g hf hg z hz θ ⟨h0, h2⟩)
          (hC α f g hα hα1 hf hfm z hz θ ⟨h0, h2⟩)
      · -- `θ = π/2`
        subst h2
        have hsin : Real.sin (2 * (π / 2)) = 0 := by
          rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
        rw [T1Easy_eq_zero_of_sin_eq_zero α hα f g hsin]
        rw [Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero hgam hsin]
        simp
  refine ⟨hbound, ?_⟩
  -- integrability of the angular slices
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hzpos
  · subst h0
    have hz0 : (fun θ => Work.FTS.H2.T1Easy α f g 0 θ) = fun _ => (0 : ℝ) :=
      funext fun θ => T1Easy_eq_zero_of_z_eq_zero α f g θ
    rw [hz0]
    exact integrableOn_zero
  · have hdom : MeasureTheory.IntegrableOn
        (fun θ => C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ)
        Work.Spaces.Iθ := (hgm.1 z hz).const_mul _
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.H2.T1Easy α f g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry (Work.FTS.H2.T1Easy α f g))
        (Work.H2.T1Q.continuousOn_T1Easy_qd α f g hf hg) hzpos
    refine hdom.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs]
    exact hbound z hz θ hθ

end Work.FTS.H2.T3Q
