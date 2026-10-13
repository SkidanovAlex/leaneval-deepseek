/-
Copyright: work module for the Elgindi finite-time singularity project.

# The half-strip `C^∞`-calculus of the angular Poincaré estimate

This module ports the smoothness/identity/integrability layer of the angular Poincaré
estimate from the class `Work.Spaces.SmoothNbhd` (smoothness on an open neighbourhood of the
*closed* quadrant, i.e. on `Ioi (-1) ×ˢ Ioo (-1) (π/2+1)`) to the half-strip class
`Work.FTS.EllipticEst.SmoothHalf`, whose second conjunct is smoothness on the *half*-strip

  `U = Ioi 0 ×ˢ Ioo (-1) (π/2 + 1)`

(and whose first conjunct is the smoothness of every angular slice at every `z ∈ [0,∞)`).

Every statement of the layer is used at a level `z > 0` only: at `z = 0` the whole
`HkIntegrand` vanishes (`Work.Spaces.w 0 = 0`, `Work.FTS.EllipticEst.HkIntegrand_zero_left`),
so no smoothness in `z` beyond `z > 0` is ever needed.  At `z > 0` a point of `Iθ × {z}` is an
interior point of the half-strip, which is what makes all the local arguments go through.

The contents are:

* `HalfU.U`, `HalfU.HalfAn` — the half-strip and its smoothness class;
* `HalfU.HalfAn.{pz,pth,Dz,Dth,DzIter,DthIter,pthIter,mixed}` — closure (only the generic
  open-set lemmas `Work.Spaces.contDiffOn_uncurry_pz/_pth` are needed);
* `HalfU.HalfAn.slice`, `…slice_DzIter`, `…slice_mixed` — the angular slices at `z > 0` are
  `SliceSmooth`;
* `HalfU.DzIter_congr_on` and friends — locality on `U`;
* `HalfU.pth_DzIter_eqOn`, `…DthIter_DzIter_comm_eqOn`, `…DthIter_DzIter_eq_mixed`,
  `…LopIter_DzIter_eq_mixed` — the operator identifications;
* `HalfU.deriv_DzIter_nhds`, `…sliceV_DzIter_nhds`, `…sliceV_DzIter`,
  `…LopIter_deriv_DzIter_eq_mixed`, `…LopIter_sliceV_DzIter_eq_mixed` — the slice identities
  (the ports of `Work.FTS.EllipticEst.ThetaSliceIdent`);
* `HalfU.integrableOn_HkIntegrand_terms_half`, `…slice_data_integrable_of_HkIntegrand_half` —
  the integrability layer (the ports of `Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms`
  and `Work.FTS.EllipticEst.Blocks.slice_data_integrable_of_HkIntegrand`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HalfSmooth
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.Blocks.slice_data_integrable_of_HkIntegrand
import Submission.Work.FTS.EllipticEst.ThetaU.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Elliptic.pth_DzIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.HalfU

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## The half-strip and its smoothness class -/

/-- The half-strip `(0,∞) × (-1, π/2+1)` of the smoothness class `SmoothHalf`. -/
def U : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_Ioo

theorem mem_U {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    (z, θ) ∈ U := ⟨hz, hθ⟩

theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Membership of a point of the closed quadrant with `z > 0` in the half-strip. -/
theorem mem_U_of_Iθ {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : (z, θ) ∈ U :=
  mem_U hz (Iθ_subset_Ioo hθ)

/-- **The smoothness class of the half-strip**: `f` is smooth on `U = (0,∞) × (-1, π/2+1)`.

This is the second conjunct of `Work.FTS.EllipticEst.SmoothHalf`; it is separated here
because the per-`z` estimates only use the half-strip smoothness (the smoothness of the
angular slices at `z = 0` recorded by the first conjunct of `SmoothHalf` is not needed for
the *slice* estimates at a fixed level `z > 0`; the iterates `D_z^j f`, `∂_θ^i f` inherit
their slice smoothness at `z > 0` from `HalfAn` alone). -/
def HalfAn (f : ℝ → ℝ → ℝ) : Prop := ContDiffOn ℝ ⊤ (Function.uncurry f) U

/-- The second conjunct of `SmoothHalf` is `HalfAn`. -/
theorem SmoothHalf.halfAn {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) : HalfAn f := h.2

/-- `HalfAn` is `SmoothOpenθ`, the class of the open versions of the slice estimates. -/
theorem HalfAn.smoothOpenθ {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    Work.FTS.EllipticEst.ThetaU.SmoothOpenθ f := fun n => h.of_le le_top

theorem HalfAn.contDiffAt {f : ℝ → ℝ → ℝ} (h : HalfAn f) {z θ : ℝ} (hy : (z, θ) ∈ U) :
    ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
  ContDiffOn.contDiffAt h (isOpen_U.mem_nhds hy)

/-! ## Closure under the partial derivatives -/

theorem HalfAn.pz {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.pz f) :=
  Work.Spaces.contDiffOn_uncurry_pz isOpen_U h

theorem HalfAn.pth {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.pth f) :=
  Work.Spaces.contDiffOn_uncurry_pth isOpen_U h

theorem HalfAn.Dz {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.Dz f) := by
  have hfun : Function.uncurry (Work.Spaces.Dz f)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [HalfAn, hfun]
  exact contDiffOn_fst.mul h.pz

theorem HalfAn.Dth {f : ℝ → ℝ → ℝ} (h : HalfAn f) : HalfAn (Work.Spaces.Dth f) := by
  have hfun : Function.uncurry (Work.Spaces.Dth f)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth f) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [HalfAn, hfun]
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) U :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.mul h.pth

theorem HalfAn.DzIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ j : ℕ, HalfAn (Work.Spaces.DzIter j f)
  | 0 => h
  | j + 1 => (HalfAn.DzIter h j).Dz

theorem HalfAn.DthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ i : ℕ, HalfAn (Work.Spaces.DthIter i f)
  | 0 => h
  | i + 1 => (HalfAn.DthIter h i).Dth

theorem HalfAn.pthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) :
    ∀ m : ℕ, HalfAn (Work.Spaces.pthIter m f)
  | 0 => h
  | m + 1 => (HalfAn.pthIter h m).pth

theorem HalfAn.mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) :
    HalfAn (Work.Spaces.mixed j i f) := (h.DthIter i).DzIter j

/-! ## Smoothness of the angular slices at a level `z > 0` -/

theorem HalfAn.slice {f : ℝ → ℝ → ℝ} (h : HalfAn f) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => f z θ) := by
  have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : Set.MapsTo (fun t : ℝ => (z, t)) (Set.Ioo (-1) (Real.pi / 2 + 1)) U :=
    fun t ht => ⟨hz, ht⟩
  have hcomp := h.comp hp hmap
  simpa [SliceSmooth, Function.comp_def, Function.uncurry] using hcomp

theorem HalfAn.slice_DzIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => Work.Spaces.DzIter j f z θ) := (h.DzIter j).slice hz

theorem HalfAn.slice_DthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => Work.Spaces.DthIter i f z θ) := (h.DthIter i).slice hz

theorem HalfAn.slice_pthIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => Work.Spaces.pthIter m f z θ) := (h.pthIter m).slice hz

theorem HalfAn.slice_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => Work.Spaces.mixed j i f z θ) := (h.mixed j i).slice hz

/-! ## Locality on the half-strip -/

theorem Dz_congr_on {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') U) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) U := by
  intro y hy
  have hp := Work.Spaces.pz_congr_of_isOpen isOpen_U h hy
  show y.1 * Work.Spaces.pz g y.1 y.2 = y.1 * Work.Spaces.pz g' y.1 y.2
  rw [hp]

theorem Dth_congr_on {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') U) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) U := by
  intro y hy
  have hp := Work.Spaces.pth_congr_of_isOpen isOpen_U h hy
  show Real.sin (2 * y.2) * Work.Spaces.pth g y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth g' y.1 y.2
  rw [hp]

theorem DzIter_congr_on {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') U) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) U := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr_on ih

/-! ## Commutation identities on the half-strip -/

/-- One step of the commutation: `∂_θ (D_z g) = D_z (∂_θ g)` at a point of the half-strip. -/
theorem pth_Dz_apply {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ} (hy : y ∈ U) (hg : HalfAn g) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2 = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry g) y := (hg.contDiffAt hy).of_le (by norm_num)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) h2).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

/-- On the half-strip, the angular derivative of the `j`-th `D_z`-iterate of `Φ` is the
`j`-th `D_z`-iterate of its angular derivative. -/
theorem pth_DzIter_eqOn {Φ : ℝ → ℝ → ℝ} (hΦ : HalfAn Φ) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) U := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : HalfAn (Work.Spaces.DzIter j Φ) := hΦ.DzIter j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y :=
      pth_Dz_apply hy hs
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j Φ))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ))) y :=
      Dz_congr_on ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) Φ)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)) y
    rw [show Work.Spaces.DzIter (j+1) Φ = Work.Spaces.Dz (Work.Spaces.DzIter j Φ) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth Φ)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) from rfl]
    exact hstep.trans hcongr

/-- `D_θ` can be moved across any iterate of `D_z`, on the half-strip. -/
theorem Dth_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : HalfAn f) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) U := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (((h.DzIter b).contDiffAt hy).of_le (by norm_num))
      have hpz := Work.Spaces.pz_congr_of_isOpen isOpen_U ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z`, on the half-strip. -/
theorem DthIter_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : HalfAn f) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) U := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_congr_on ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn (h.DthIter i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-- `D_θ^i (D_z^j f) = D_z^j D_θ^i f` at a point of the closed quadrant with `z > 0`. -/
theorem DthIter_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DthIter i (Work.Spaces.DzIter j f) z θ = Work.Spaces.mixed j i f z θ :=
  DthIter_DzIter_comm_eqOn h j i (mem_U_of_Iθ hz hθ)

/-- The `i`-th iterate of `L = D_θ` applied to the `j`-th `D_z`-slice of `f` is the
`(j,i)`-mixed derivative `D_z^j D_θ^i f` at the same point. -/
theorem LopIter_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.mixed j i f z θ := by
  rw [Work.FTS.EllipticEst.LopIter_slice i (Work.Spaces.DzIter j f) z]
  exact DthIter_DzIter_eq_mixed h j i hz hθ

/-! ## The slice identities

These are the ports of `Work.FTS.EllipticEst.ThetaSliceIdent` (and of `SliceAux.sliceV_DzIter`)
to the half-strip, where the identities are available at every level `z > 0`. -/

theorem Euler_pth_DzIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ :=
  pth_DzIter_eqOn h j (mem_U hz hθ)

/-- `D_z^j (∂_θ f)` is the `θ`-derivative of the `D_z^j`-slice, at a point of the closed
interval with `z > 0` (port of `Work.FTS.EllipticEst.DzIter_pth_eq_deriv`). -/
theorem DzIter_pth_eq_deriv {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
  (Euler_pth_DzIter h j hz (Iθ_subset_Ioo hθ)).symm

/-- Near a point of the closed interval, the derivative of the slices of `D_z^j f` is the
slice of `D_z^j (∂_θ f)`. -/
theorem deriv_DzIter_nhds {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
  have hmem : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := Iθ_subset_Ioo hθ
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with θ' hθ'
  exact Euler_pth_DzIter h j hz hθ'

/-- `sliceV` of the slice of `D_z^j f` is the slice of `D_z^j (∂_θ² f)`, on the half-strip. -/
theorem sliceV_DzIter_of_mem_U {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hmem : (z, θ) ∈ U := mem_U hz hθ
  have hU1 : ∀ θ' ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1),
      Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ' :=
    fun θ' hθ' => Euler_pth_DzIter h j hz hθ'
  have hev1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact hU1 θ' hθ'
  have e1 : Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ := rfl
  rw [e1, hev1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [e2]
  have hU2 : Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
    have h2 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
    rw [h2]
    exact Euler_pth_DzIter h.pth j hz hθ
  exact hU2

/-- Near a point of the closed interval, the second derivative of the slices of `D_z^j f` is
the slice of `D_z^j (∂_θ² f)`. -/
theorem sliceV_DzIter_nhds {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (fun θ' => Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') := by
  have hmem : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := Iθ_subset_Ioo hθ
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with θ' hθ'
  exact sliceV_DzIter_of_mem_U h j hz hθ'

/-- `sliceV` of the slice of `D_z^j f` at a point of the closed interval. -/
theorem sliceV_DzIter {f : ℝ → ℝ → ℝ} (h : HalfAn f) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ :=
  sliceV_DzIter_of_mem_U h j hz (Iθ_subset_Ioo hθ)

/-- The `m`-th iterate of `L` applied to the derivative of the slice of `D_z^j f` is the
`(j,m)`-mixed derivative of `∂_θ f`. -/
theorem LopIter_deriv_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f)
    (j m : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.LopIter m (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pth f) z θ := by
  have h1 : Work.FTS.EllipticEst.LopIter m (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.FTS.EllipticEst.LopIter m
          (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ :=
    Work.FTS.EllipticEst.LopIter_congr_nhds (deriv_DzIter_nhds h j hz hθ) m
  rw [h1]
  have h2 : Work.FTS.EllipticEst.LopIter m
        (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.DthIter m (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z θ :=
    congrFun (Work.FTS.EllipticEst.LopIter_slice m
      (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z) θ
  rw [h2]
  have h3 : Work.Spaces.DthIter m (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z' θ') z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [h3]
  exact DthIter_DzIter_eq_mixed h.pth j m hz hθ

/-- The `m`-th iterate of `L` applied to the second derivative of the slice of `D_z^j f` is
the `(j,m)`-mixed derivative of `∂_θ² f`. -/
theorem LopIter_sliceV_DzIter_eq_mixed {f : ℝ → ℝ → ℝ} (h : HalfAn f)
    (j m : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ := by
  have h1 : Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.FTS.EllipticEst.LopIter m
          (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ :=
    Work.FTS.EllipticEst.LopIter_congr_nhds (sliceV_DzIter_nhds h j hz hθ) m
  rw [h1]
  have h2 : Work.FTS.EllipticEst.LopIter m
        (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
      = Work.Spaces.DthIter m
          (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z θ :=
    congrFun (Work.FTS.EllipticEst.LopIter_slice m
      (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z) θ
  rw [h2]
  have h3 : Work.Spaces.DthIter m
        (fun z' θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z' θ') z θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)) z θ := rfl
  rw [h3]
  exact DthIter_DzIter_eq_mixed (h.pthIter 2) j m hz hθ

/-! ## The integrability layer -/

private lemma measurable_wdivsin_right (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this

/-- **Honesty of the individual summands of the `H^k`-integrand, half-strip version.**
Port of `Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms` to the class `HalfAn`, at a
level `z > 0` (the continuity of the slices `θ ↦ D_z^i G z θ`, `θ ↦ D_z^j D_θ^i G z θ` on
`Iθ` comes from the half-strip smoothness of the iterates). -/
theorem integrableOn_HkIntegrand_terms_half (α : ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ)
    (hG : HalfAn G) {z : ℝ} (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k G z θ)
      Work.Spaces.Iθ) :
    (∀ i ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) ∧
      (∀ i j : ℕ, 1 ≤ i → i + j ≤ k → MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hcont_i : ∀ i : ℕ, ContinuousOn (fun θ => Work.Spaces.DzIter i G z θ) Work.Spaces.Iθ :=
    fun i => ((hG.DzIter i).slice hz).continuousOn.mono Iθ_subset_Ioo
  have hcont_m : ∀ j i : ℕ, ContinuousOn (fun θ => Work.Spaces.mixed j i G z θ) Work.Spaces.Iθ :=
    fun j i => ((hG.mixed j i).slice hz).continuousOn.mono Iθ_subset_Ioo
  refine ⟨fun i hi => ?_, fun i j hi hij => ?_⟩
  · have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (hcont_i i).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        (volume.restrict Work.Spaces.Iθ) :=
      (measurable_wdivsin_right z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α k G z θ i hi
  · have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.mixed j i G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (hcont_m j i).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (measurable_Wt_right α z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k G z θ i j hi hij

private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2

private lemma inv_w_sq_mul_zsummand (z θ c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.w_div_sin_sq hθ z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ * (c ^ 2 *
          ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thEta θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

private lemma inv_w_sq_mul_mixed (z θ α c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.Wt_sq hθ α z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * (Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ)) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thGam α θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

/-- **The slice data of `u_j = D_z^j f z ·` is integrable, half-strip version.**  Port of
`Work.FTS.EllipticEst.Blocks.slice_data_integrable_of_HkIntegrand` to the class `HalfAn` at
a level `z > 0`: the integrability of the `H^k`-integrand of `∂_θ² f` makes the slice data
`u_j'' = D_z^j (∂_θ² f) z ·` and its `D_θ`-iterates integrable against the angular weights
`sin(2θ)^{-η}` resp. `sin(2θ)^{-γ}`. -/
theorem slice_data_integrable_of_HkIntegrand_half (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hf : HalfAn f) {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
      (∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) := by
  have hterms := integrableOn_HkIntegrand_terms_half α k (Work.Spaces.pthIter 2 f)
    (hf.pthIter 2) hz hInt
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul (hterms.1 j hj) ((Work.Spaces.w z) ^ 2)⁻¹)
      ?_ measurableSet_Icc
    intro θ hθ
    exact inv_w_sq_mul_zsummand z θ _ hθ hz
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul (hterms.2 m j hm1 (by omega))
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ measurableSet_Icc
    intro θ hθ
    exact inv_w_sq_mul_mixed z θ α _ hθ hz

end Work.FTS.EllipticEst.HalfU

namespace Work.FTS.EllipticEst

/-- The second conjunct of `SmoothHalf` is `HalfU.HalfAn`.

This bridge is declared in the namespace of `SmoothHalf` (not inside `HalfU`) so that the field
notation `hsm.halfAn` resolves for `hsm : SmoothHalf f`. -/
theorem SmoothHalf.halfAn {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) :
    Work.FTS.EllipticEst.HalfU.HalfAn f := h.2

end Work.FTS.EllipticEst
