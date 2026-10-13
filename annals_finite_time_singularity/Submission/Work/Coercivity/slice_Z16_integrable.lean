import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.zAux
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Slice integrability of the four terms of the `Z₁₆`-identity

The pointwise identity `slice_Z16` expresses the slice integrand
`Z₁₆ f z θ · D_z f z θ · Weta z θ` as a sum of three terms, each of which is a
*bounded* continuous function of `θ` multiplied by the angular weight
`sin(2θ)^{-η}`.  Since the two endpoint singularities of `sin(2θ)^{-η}` are
integrable (`0 < η < 1`), every one of the four integrands below is integrable
on `Iθ`.

The only structural input is that `f` is smooth on an open neighbourhood of the
closed quadrant, so that for `z > 0` every `θ`-slice of `f`, of `D_z f`, of
`D_θ(D_z f)` and of the auxiliary `z ↦ z (D_z f(z,θ) w(z))²` is continuous (hence
bounded) on the compact interval `Iθ`. -/

/-- The angular factor `sin(2θ)^{-η}` is integrable over `Iθ`: its endpoint
singularities are integrable because `0 < η < 1`. -/
private lemma sin_neg_eta_integrableOn :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ :=
  (Spaces.sin_two_rpow (-Spaces.eta) (by norm_num [Spaces.eta])
    (by norm_num [Spaces.eta])).1

/-- The `θ`-slice `θ ↦ g z θ` of a function smooth on an open neighbourhood of the
closed quadrant is continuous on `Iθ`, for every `z > 0`. -/
private lemma continuousOn_slice_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Spaces.SmoothNbhd g)
    {z : ℝ} (hz : 0 < z) : ContinuousOn (fun θ => g z θ) Spaces.Iθ := by
  have hz' : z ∈ Set.Ioi (-1:ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) Spaces.Iθ Spaces.nbhU := by
    intro θ hθ
    rw [Spaces.nbhU, Set.mem_prod]
    exact ⟨hz', by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hcont : ContinuousOn (Function.uncurry g) Spaces.nbhU := hg.continuousOn
  have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) Spaces.Iθ :=
    (continuous_const.prodMk continuous_id).continuousOn
  simpa [Function.comp_def, Function.uncurry] using hcont.comp hiota hmap

/-- The open set `(0,∞) × (-1, π/2+1)` on which the radial weight `w` is smooth (it
is only singular at `z = 0`). -/
private def Vw : Set (ℝ × ℝ) := Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1:ℝ) (Real.pi / 2 + 1)

private lemma isOpen_Vw : IsOpen Vw := isOpen_Ioi.prod isOpen_Ioo

private lemma Vw_subset_nbhU : Vw ⊆ Spaces.nbhU := by
  intro p hp
  have hp' : p.1 ∈ Set.Ioi (0:ℝ) ∧ p.2 ∈ Set.Ioo (-1:ℝ) (Real.pi/2+1) := hp
  exact ⟨by simp only [Set.mem_Ioi] at hp' ⊢; linarith [hp'.1], hp'.2⟩

/-- `w(z) = (1+z)²/z²` is smooth on `(0,∞) × (-1,π/2+1)`. -/
private lemma contDiffOn_w_Vw :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) Vw := by
  have hnum : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Vw :=
    ((contDiff_const.add contDiff_fst).pow 2).contDiffOn
  have hden : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ 2) Vw :=
    (contDiff_fst.pow 2).contDiffOn
  have hne : ∀ p ∈ Vw, p.1 ^ 2 ≠ 0 := fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  simp [Spaces.w]

/-- The `z`-derivative `θ ↦ ∂_z (z ↦ z (D_z f(z,θ) · w(z))²)(z)` is continuous in `θ`
on `Iθ`: it is the `z`-partial of the smooth function `(z,θ) ↦ z (D_z f(z,θ) w(z))²`,
which is smooth on `Vw` because `D_z f` is smooth on `nbhU ⊇ Vw` and `w` is smooth
on `Vw`. -/
private lemma continuousOn_deriv_zw_Dz_sq (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z)
      Spaces.Iθ := by
  have hB : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2) Vw := by
    convert ContDiffOn.mono (Spaces.SmoothNbhd.Dz hsm) Vw_subset_nbhU using 1
    ext p; rfl
  have hW : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) Vw := contDiffOn_w_Vw
  have hG : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)) Vw := by
    have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.Dz f p.1 p.2 * Spaces.w p.1) Vw :=
      hB.mul hW
    have h2 : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2 * Spaces.w p.1) ^ 2) Vw := h1.pow 2
    have h3 : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => p.1 * (Spaces.Dz f p.1 p.2 * Spaces.w p.1) ^ 2) Vw :=
      (contDiff_fst.contDiffOn).mul h2
    convert h3 using 1
    ext p; rfl
  have hd : ContDiffOn ℝ ⊤
      (Function.uncurry (Spaces.pz (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2))) Vw :=
    Spaces.contDiffOn_uncurry_pz isOpen_Vw hG
  have hcont : ContinuousOn
      (fun θ => Spaces.pz (fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2) z θ)
      Spaces.Iθ := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) Spaces.Iθ Vw := by
      intro θ hθ
      exact ⟨by simp only [Set.mem_Ioi]; exact hz,
        by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) Spaces.Iθ :=
      (continuous_const.prodMk continuous_id).continuousOn
    simpa [Function.comp_def, Function.uncurry] using hd.continuousOn.comp hiota hmap
  simpa [Spaces.pz] using hcont

theorem slice_Z16_integrable (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (Spaces.Dz f z θ) ^ 2 * Weta z θ) Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  have hsin : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := sin_neg_eta_integrableOn
  have hDz : ContinuousOn (fun θ => Spaces.Dz f z θ) Spaces.Iθ :=
    continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dz hsm) hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `𝓛(D_z f) · D_z f · Weta` term
    have hDzDz : ContinuousOn (fun θ => Spaces.Dz (Spaces.Dz f) z θ) Spaces.Iθ :=
      continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dz (Spaces.SmoothNbhd.Dz hsm)) hz
    have hL : ContinuousOn (fun θ => L (Spaces.Dz f) z θ) Spaces.Iθ := by
      unfold L
      exact (hDz.add hDzDz).sub ((hDz.const_mul 2).div_const (1 + z))
    have hcont : ContinuousOn
        (fun θ => L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2) Spaces.Iθ :=
      (hL.mul hDz).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the `D_θ(D_z f) · D_z f · Weta` term
    have hDthDz : ContinuousOn (fun θ => Spaces.Dth (Spaces.Dz f) z θ) Spaces.Iθ :=
      continuousOn_slice_of_smoothNbhd (Spaces.SmoothNbhd.Dth (Spaces.SmoothNbhd.Dz hsm)) hz
    have hcont : ContinuousOn
        (fun θ => Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2) Spaces.Iθ :=
      (hDthDz.mul hDz).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the coercive `(D_z f)² · Weta` term
    have hcont : ContinuousOn (fun θ => (Spaces.Dz f z θ) ^ 2 * Spaces.w z ^ 2) Spaces.Iθ :=
      (hDz.pow 2).mul continuousOn_const
    refine (IntegrableOn.continuousOn_mul hcont hsin isCompact_Icc).congr_fun
      (fun θ _ => ?_) measurableSet_Icc
    rw [Weta]; ring
  · -- the boundary term `∂_z(z (D_z f · w)²) · sin(2θ)^{-η}`
    exact IntegrableOn.continuousOn_mul (continuousOn_deriv_zw_Dz_sq f hsm hz) hsin isCompact_Icc

end Work.Coercivity
