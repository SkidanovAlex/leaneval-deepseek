/-
# Additivity of `L₁₂` and of the angular moment `(·,K)` over `F = F_* + g`, for `z ≥ 0`

`Work.Construction.L12 f z = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds` and
`Work.Construction.FK F z = ∫_0^{π/2} F(z,θ) K(θ) dθ` are *integrals*, so they are additive in
the profile — provided the integrals are honest (integrable).  For the datum class `GalClass α g`
of the a-priori argument the integrability is available exactly on the paper's domain `z ≥ 0`:
`g` is only controlled on the closed quadrant (`RegQ`), so nothing can be said about `z < 0`
(see `Pieces/NOTES_L12FK_add_FALSE.md`: the unrestricted-`z` version is false).

The three integrability inputs are

* the angular slices of `g`: for `s > 0` the slice `θ ↦ K(θ) g(s,θ)/s` is integrable on `Iθ`,
  because `g ∈ ℋ⁴` gives `g(s,·)² ≤ HkIntegrand α 4 g s ·` on the *open* interval (the `D_z⁰`-term
  of the integrand) and `K` is bounded; only a.e. strong measurability of the slice is needed, and
  that follows from `SmoothQuad g` (continuity on the open quadrant);
* the `L₁₂`-density of `g` on `(z,∞)`: `Work.FTS.H2.L12densIntegrable` (integrable on `(0,∞)`);
* the `L₁₂`-density of `F_*`, which is the elementary function `α·F_*(s)/s = 2α/(1+s)²`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FTS.H2.L12densSlice
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.Stability.L12Add
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false

/-! ## Elementary tools -/

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  calc |a * b| = |a| * |b| := abs_mul a b
    _ ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by linarith
    _ = (a ^ 2 + b ^ 2) / 2 := by rw [sq_abs a, sq_abs b]

/-- `SmoothQuad` data are continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
private lemma continuousOn_uncurry_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  refine h.continuousOn.mono (fun p hp => ?_)
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

/-- The angular slice `θ ↦ g(s,θ)` of a `SmoothQuad` datum is a.e. strongly measurable. -/
private lemma aesm_slice_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_uncurry_of_smoothQuad hsm) hs

/-- On the open quadrant, `g(s,θ)² ≤ HkIntegrand α 4 g s θ`: the `D_z⁰`-term of the integrand
is `(g · w/sin(2θ)^{η/2})²`, and `w ≥ 1`, `sin(2θ)^{η/2} ≤ 1` make the weight at least `1`. -/
private lemma sq_le_HkIntegrand_four (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hSpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hSle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one _) (by have := Work.Spaces.eta_pos; linarith)
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  set A : ℝ := Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hA
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hSpos]
    linarith
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  simp only [Work.Spaces.DzIter_zero] at hkey
  rw [← hA] at hkey
  calc (g s θ) ^ 2 = (g s θ) ^ 2 * 1 := by ring
    _ ≤ (g s θ) ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hA1]) (sq_nonneg _)
    _ = (g s θ * A) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hkey

/-! ## The three integrability inputs -/

/-- The angular slice `θ ↦ F_*(s,θ)·K(θ)` is integrable on `Iθ`, for every `s`
(continuity on the compact `Iθ`: `Γ(θ) = (sinθcos²θ)^{α/3}` is continuous there for `α > 0`). -/
private lemma integrableOn_slice_Fstar_mul_K (α : ℝ) (hα : 0 < α) (s : ℝ) :
    MeasureTheory.IntegrableOn (fun θ => Work.Construction.Fstar α s θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  have hGam : ContinuousOn (fun θ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.Gam
    intro θ _
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))).comp_continuousWithinAt
      (by fun_prop)
  have hF : ContinuousOn (fun θ => Work.Construction.Fstar α s θ) Work.Spaces.Iθ := by
    simp only [Work.Construction.Fstar]
    exact ((continuousOn_const.mul (hGam.div_const (Work.Spaces.c α))).mul continuousOn_const)
  have hK : ContinuousOn (fun θ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    unfold Work.Spaces.K; fun_prop
  exact hF.mul hK

/-- For `s > 0` the square slice `θ ↦ g(s,θ)²` is integrable on `Iθ`, from `SmoothQuad g` and
`HkMem α 4 g` alone (no continuity at the angular boundary is available for `SmoothQuad` data). -/
private lemma integrableOn_sq_slice_of_HkMem (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
  refine (hmem.1 s hs.le).mono' ((aesm_slice_of_smoothQuad hsm hs).pow 2) ?_
  filter_upwards [Work.Elliptic.ae_restrict_Iθ_of_Ioo
    (fun θ h0 h1 => sq_le_HkIntegrand_four α g hs h0 h1)] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hθ

/-- For `s > 0` the angular slice `θ ↦ K(θ)·g(s,θ)` is integrable on `Iθ`: `K` is bounded, so
the product is dominated by `(K² + g(s,·)²)/2`. -/
private lemma integrableOn_slice_K_mul_g (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ) Work.Spaces.Iθ := by
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K; fun_prop
  have hKsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ) ^ 2) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hKcont.continuousOn.pow 2)
  have hsq := integrableOn_sq_slice_of_HkMem α g hsm hmem hs
  have hmaj : MeasureTheory.Integrable
      (fun θ => ((Work.Spaces.K θ) ^ 2 + (g s θ) ^ 2) / 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((show MeasureTheory.Integrable
        (fun θ => (Work.Spaces.K θ) ^ 2 + (g s θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from hKsq.add hsq)).div_const 2
  refine hmaj.mono' ?_ ?_
  · exact (hKcont.aestronglyMeasurable.restrict).mul (aesm_slice_of_smoothQuad hsm hs)
  · filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact abs_mul_le_half_sq (Work.Spaces.K θ) (g s θ)

/-- For `s > 0` the slice `θ ↦ K(θ)·g(s,θ)/s` is integrable on `Iθ`. -/
private lemma integrableOn_slice_g (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ :=
  (integrableOn_slice_K_mul_g α g hsm hmem hs).div_const s

/-- `F_*(s)/s = 2 (1+s)^{-2}` for `s > 0` — the elementary form of the model density. -/
private lemma Fstar_div_self_eq (s : ℝ) (hs : 0 < s) :
    Work.FM.Fstar s / s = 2 * (s + 1) ^ (-2 : ℝ) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (s + 1) ^ (-2 : ℝ) = 1 / (s + 1) ^ 2 := by
    simp only [Real.rpow_neg (le_of_lt hs1), Real.rpow_ofNat, one_div]
  rw [h2]
  unfold Work.FM.Fstar
  field_simp
  ring

/-- The `L₁₂`-density of `F_*` is integrable on `(z,∞)` for `z ≥ 0`: pointwise it is
`α·F_*(s)/s = 2α/(1+s)²`, and `s ↦ (1+s)^{-2}` is integrable on `(z,∞)` for `z > -1`. -/
private lemma integrableOn_L12dens_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Fstar α))
      (Set.Ioi z) := by
  have hA : MeasureTheory.IntegrableOn (fun s : ℝ => (s + 1) ^ (-2 : ℝ)) (Set.Ioi z) :=
    integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := z) (m := 1) (by norm_num) (by linarith)
  refine MeasureTheory.IntegrableOn.congr_fun (hA.const_mul (2 * α)) ?_ measurableSet_Ioi
  intro s hs
  rw [Work.Construction.L12dens_Fstar hα hα1 s, Fstar_div_self_eq s (lt_of_le_of_lt hz hs)]
  ring

/-! ## The main theorem -/

theorem L12FK_add_ge0 {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.Nonlin.GalClass α g) :
    (∀ z : ℝ, 0 ≤ z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z) ∧
    (∀ z : ℝ, 0 ≤ z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z) := by
  have hsq : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    (Work.FTS.GalerkinFix.RegQ.regQ_mono hg.reg (by norm_num)).2.1
  have haxis := hg.axis
  constructor
  · -- additivity of `L₁₂`
    intro z hz
    have h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * Work.Construction.Fstar α s θ / s) Work.Spaces.Iθ :=
      fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s
    have h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ :=
      fun s hs => integrableOn_slice_g α g hsq hmem4 (lt_of_le_of_lt hz hs)
    have h3 : MeasureTheory.IntegrableOn
        (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi z) :=
      integrableOn_L12dens_Fstar α hα hα1 hz
    have h4 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z) := by
      have h0 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) := by
        refine (Work.FTS.H2.L12densIntegrable α g hα hα1 hsq hmem4).congr_fun ?_ measurableSet_Ioi
        intro s _
        exact Work.FTS.H2.L12dens_eq_FM_K g s
      exact h0.mono_set (Set.Ioi_subset_Ioi hz)
    have key := (Work.FTS.LocData.L12_add_mul (c := 1) (a := Work.Construction.Fstar α) (b := g)
      (z := z) h1 h2 h3 h4).1
    exact key
  · -- additivity of the angular moment
    intro z hz
    have hFint : MeasureTheory.IntegrableOn
        (fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
      integrableOn_slice_Fstar_mul_K α hα z
    have hgint : MeasureTheory.IntegrableOn (fun θ => g z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
      rcases eq_or_lt_of_le hz with h0 | hpos
      · subst h0
        refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero ?_
          measurableSet_Icc
        intro θ hθ
        show (0 : ℝ) = g 0 θ * Work.Spaces.K θ
        rw [(haxis θ hθ).1]
        ring
      · refine MeasureTheory.IntegrableOn.congr_fun
          (integrableOn_slice_K_mul_g α g hsq hmem4 hpos) ?_ measurableSet_Icc
        intro θ _
        ring
    have key : (∫ θ in Work.Spaces.Iθ,
          (Work.Construction.Fstar α z θ + g z θ) * Work.Spaces.K θ)
        = (∫ θ in Work.Spaces.Iθ, Work.Construction.Fstar α z θ * Work.Spaces.K θ)
          + ∫ θ in Work.Spaces.Iθ, g z θ * Work.Spaces.K θ := by
      have hpt : (fun θ => (Work.Construction.Fstar α z θ + g z θ) * Work.Spaces.K θ)
          = fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ
              + g z θ * Work.Spaces.K θ := by
        funext θ; ring
      rw [hpt]
      exact MeasureTheory.integral_add hFint hgint
    simpa only [Work.Construction.FK, Work.Construction.Ftot] using key

end Work.FTS.Nonlinear.Pieces
