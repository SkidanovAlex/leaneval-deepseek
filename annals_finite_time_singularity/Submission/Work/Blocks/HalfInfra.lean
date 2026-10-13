/-
Copyright: work module for the Elgindi finite-time singularity project.

# `SmoothHalf`: the slice-level infrastructure of the `sin 2θ`-division

This module ports the parts of the `sin(2θ)`-division chain that are stated for
`Work.Spaces.SmoothNbhd` (smoothness on an open neighbourhood of the *closed* quadrant) to the
weaker class `Work.FTS.EllipticEst.SmoothHalf` (each angular slice smooth on a neighbourhood of
`[0, π/2]`, jointly smooth on the half-strip `z > 0`).

It collects the pieces that `Work.Blocks.divSin_Half` (and its siblings `HalfDtwMixed`,
`HalfHkMemSlice`, `HalfDivSinPerZ`) consume:

* `hslab` — the open half-strip `z > 0`, `θ ∈ (-1, π/2+1)`;
* `contDiffOn_uncurry_Dz/Dth/DzIter/DthIter/mixed` — `⊤`-smoothness is preserved by the
  operators on any open set (the generalisation of `SmoothNbhd.Dz`, … to an arbitrary open `V`);
* the congruence lemmas `pz_congrOn`, `Dz_congrOn`, `Dth_congrOn`, `DthIter_congrOn`;
* `pth_DzIter_eqOn` — `∂_θ` commutes with the iterates of `D_z` on an open set;
* the identities at a fixed `z > 0`
  (`deriv_DzIter_slice_half`, `divSinMixedExpansion_half`, `mixed_div_eq_Dth1Iter_half`,
  `Dth1Iter_deriv_eq_mixed_half`);
* `DivSinSliceFacts_half` — the slice `θ ↦ D_z^j Φ z θ` is smooth and vanishes at both ends,
  for `z > 0`;
* `pz_cont_DzIter_div_half`, `pz_cont_mixed_div_half` — continuity of the slices of the
  quotient `Φ/sin 2θ` on `(0, π/2)`;
* `HkIntegrand_zero_z` — the `H^k`-integrand vanishes identically at `z = 0` (the radial weight
  `w 0 = 0` kills every summand);
* `dtwTermwiseZ_half` — the pure-`D_z` termwise estimate (one-dimensional weighted Hardy);
* `aesm_uncurry_HkIntegrand_SinQ_half` — a.e. strong measurability of the integrand.

Every result here is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HalfSmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinFactor
import Submission.Work.Elliptic.DivSinMixedExpansion
import Submission.Work.Elliptic.DivSinSliceIdent
import Submission.Work.Elliptic.DthIter_slice
import Submission.Work.Elliptic.DivSinSliceFacts
import Submission.Work.Elliptic.DivSinTermwise
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.Half

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Elementary local helpers (replacing lemmas that live in the heavy `DivSinPerZ`) -/

/-- `sin(2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `Dth1` preserves `C^∞` on an open set. -/
theorem contDiffOn_Dth1_of {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1 f) s :=
  ((show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) s by fun_prop)).mul
    (hf.deriv_of_isOpen hs le_top)

/-- Iterates of `Dth1` preserve `C^∞` on an open set. -/
theorem contDiffOn_Dth1Iter_of {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ∀ m : ℕ, ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter m f) s
  | 0 => by simpa using hf
  | (m + 1) => by
      simpa only [Work.Elliptic.Dth1Iter_succ] using
        contDiffOn_Dth1_of hs (contDiffOn_Dth1Iter_of hs hf m)

/-- The angular quotient of a smooth slice is `C^∞` on `(0, π/2)`. -/
theorem contDiffOn_SinQ_of {h : ℝ → ℝ} (hsm : Work.Elliptic.SmoothSlice h) :
    ContDiffOn ℝ ⊤ (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  exact (hsm.mono hsub).div (by fun_prop) (fun x hx => ne_of_gt (sin_two_pos_Ioo hx))


/-! ## The half-strip -/

/-- The open half-strip `z > 0`, `θ ∈ (-1, π/2+1)` on which `SmoothHalf` demands joint
smoothness. -/
def hslab : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)

theorem isOpen_hslab : IsOpen hslab := isOpen_Ioi.prod isOpen_Ioo

theorem mem_hslab {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : (z, θ) ∈ hslab :=
  ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩

/-- The smoothness half of `SmoothHalf`, as a hypothesis on the half-strip. -/
theorem SmoothHalf.contDiffOn_hslab {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothHalf f) :
    ContDiffOn ℝ ⊤ (Function.uncurry f) hslab := h.2

/-! ## `⊤`-smoothness on an open set is preserved by the operators

The proofs are those of `Work.Spaces.SmoothNbhd.Dz`, `.Dth`, `.DzIter`, `.DthIter`, with the
fixed neighbourhood `nbhU` replaced by an arbitrary open set `V`. -/

theorem contDiffOn_uncurry_Dz {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz f)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤
      (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      y.1 * (fderiv ℝ (Function.uncurry f) y) (1, 0)) V :=
    (contDiff_fst.contDiffOn).mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = (fderiv ℝ (Function.uncurry f) y) (1, 0) :=
    Work.Spaces.deriv_slice_fst (Function.uncurry f) y.1 y.2 hdiff
  show y.1 * deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = y.1 * (fderiv ℝ (Function.uncurry f) y) (1, 0)
  rw [hderiv]

theorem contDiffOn_uncurry_Dth {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth f)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤
      (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry f) y) (0, 1)) V := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry f) y) (0, 1) :=
    Work.Spaces.deriv_slice_snd (Function.uncurry f) y.1 y.2 hdiff
  show Real.sin (2 * y.2) * deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry f) y) (0, 1)
  rw [hderiv]

theorem contDiffOn_uncurry_DzIter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n f)) V := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DzIter_succ]; exact contDiffOn_uncurry_Dz hV ih

theorem contDiffOn_uncurry_DthIter {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter n f)) V := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [Work.Spaces.DthIter_succ]; exact contDiffOn_uncurry_Dth hV ih

theorem contDiffOn_uncurry_mixed {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i f)) V :=
  contDiffOn_uncurry_DzIter hV (contDiffOn_uncurry_DthIter hV h i) j

/-! ## Congruence of the operators under equality on an open set -/

theorem pz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pz g p.1 p.2 = Work.Spaces.pz g' p.1 p.2 := by
  have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ V :=
    (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun z' => Function.uncurry g (z', p.2)) =ᶠ[𝓝 p.1]
      (fun z' => Function.uncurry g' (z', p.2)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [Work.Spaces.pz, Function.uncurry] using this

theorem Dz_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro p hp
  have hpz := pz_congrOn hV h hp
  show p.1 * Work.Spaces.pz g p.1 p.2 = p.1 * Work.Spaces.pz g' p.1 p.2
  rw [hpz]

theorem Dth_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro p hp
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => Function.uncurry g (p.1, θ')) =ᶠ[𝓝 p.2]
      (fun θ' => Function.uncurry g' (p.1, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  exact congrArg (fun t => Real.sin (2 * p.2) * t) hd

theorem DthIter_congrOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [Work.Spaces.DthIter_succ] using Dth_congrOn hV ih

/-! ## `∂_θ` commutes with the iterates of `D_z` on an open set -/

/-- `∂_θ (D_z g) = D_z (∂_θ g)` at a point where `g` is `C²`. -/
theorem pth_Dz_apply_of {g : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) y) :
    Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2 = Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2 := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) y.1 y.2
      = y.1 * Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2 := by
    show deriv (fun θ' => y.1 * Work.Spaces.pz g y.1 θ') y.2
      = y.1 * deriv (fun θ' => Work.Spaces.pz g y.1 θ') y.2
    rw [deriv_const_mul_field]
  have h3 : Work.Spaces.pth (Work.Spaces.pz g) y.1 y.2
      = Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 :=
    (Work.Spaces.pz_pth_comm (f := g) hg).symm
  have h4 : Work.Spaces.Dz (Work.Spaces.pth g) y.1 y.2
      = y.1 * Work.Spaces.pz (Work.Spaces.pth g) y.1 y.2 := rfl
  rw [h1, h3, h4]

theorem pth_DzIter_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
    intro y hy
    have hs : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j f)) V :=
      contDiffOn_uncurry_DzIter hV h j
    have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y :=
      pth_Dz_apply_of ((ContDiffOn.contDiffAt hs (hV.mem_nhds hy)).of_le (by norm_num))
    have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y
        = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))) y :=
      Dz_congrOn hV ih hy
    show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) f)) y
        = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)) y
    rw [show Work.Spaces.DzIter (j+1) f = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
        show Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) from rfl]
    exact hstep.trans hcongr

/-! ## `D_θ` commutes with the iterates of `D_z` (the other direction) -/

theorem Dz_Dth_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dth f)))
      (Function.uncurry (Work.Spaces.Dth (Work.Spaces.Dz f))) V := by
  intro y hy
  exact Work.Spaces.Dz_Dth_comm ((ContDiffOn.contDiffAt h (hV.mem_nhds hy)).of_le (by norm_num))

theorem Dth_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Dz_Dth_comm_eqOn hV (contDiffOn_uncurry_DzIter hV h b) hy
      have hpz := pz_congrOn hV ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

theorem DthIter_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_congrOn hV ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn hV (contDiffOn_uncurry_DthIter hV h i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-! ## The slice of an iterated `D_z`-derivative, at `z > 0` -/

/-- The angular slice of `D_z^j Φ` is smooth near `[0, π/2]`, for `z > 0`. -/
theorem SmoothHalf.slice_DzIter {Φ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothHalf Φ)
    {z : ℝ} (hz : 0 < z) (j : ℕ) :
    Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ) := by
  have hg : ContDiffOn ℝ ⊤ (fun θ : ℝ => ((z, θ) : ℝ × ℝ))
      (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    (contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ ⊤ (fun θ : ℝ => θ) (Set.Ioo (-1) (Real.pi / 2 + 1)))
  exact ((contDiffOn_uncurry_DzIter isOpen_hslab (SmoothHalf.contDiffOn_hslab h) j).comp hg
    (fun θ hθ => ⟨hz, hθ⟩)).congr (fun θ _ => rfl)

/-- The slice facts for `D_z^j Φ` at `z > 0`: smoothness and vanishing at the two angular
boundary lines. -/
theorem DivSinSliceFacts_half (Φ : ℝ → ℝ → ℝ) (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ)
    (hv : Work.Spaces.VanishTheta Φ) (j : ℕ) (z : ℝ) (hz : 0 < z) :
    Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ) ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) 0 = 0 ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) (Real.pi / 2) = 0 :=
  ⟨SmoothHalf.slice_DzIter hΦ hz j, (Work.Elliptic.vanish_DzIter hv j).1 z,
    (Work.Elliptic.vanish_DzIter hv j).2 z⟩

/-- `∂_θ (D_z^j Φ) = D_z^j (∂_θ Φ)` at `z > 0`, in the `deriv`-of-the-slice form. -/
theorem deriv_DzIter_slice_half (Φ : ℝ → ℝ → ℝ) (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    deriv (fun θ' => Work.Spaces.DzIter j Φ z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ :=
  pth_DzIter_eqOn isOpen_hslab (SmoothHalf.contDiffOn_hslab hΦ) j (mem_hslab hz hθ)

/-! ## The commutation of `D_z^j` with `D_θ^i` across division by `sin 2θ`, for `z > 0` -/

private def invSin2 : ℝ → ℝ := fun θ => (Real.sin (2 * θ))⁻¹

private def VnbhH : Set (ℝ × ℝ) :=
  Set.Ioi 0 ×ˢ
    (Set.Ioo (-1) (Real.pi / 2 + 1) ∩ (fun t : ℝ => Real.sin (2 * t)) ⁻¹' {y : ℝ | y ≠ 0})

private theorem isOpen_VnbhH : IsOpen VnbhH := by
  rw [VnbhH]
  exact isOpen_Ioi.prod (isOpen_Ioo.inter
    (isOpen_ne.preimage (by continuity : Continuous fun t : ℝ => Real.sin (2 * t))))

private theorem VnbhH_subset : VnbhH ⊆ hslab := by
  intro p hp
  rw [VnbhH, Set.mem_prod] at hp
  rw [hslab, Set.mem_prod]
  exact ⟨hp.1, hp.2.1⟩

/-- `D_z^j` commutes with `D_θ^i` across division by `sin(2θ)`, for `z > 0`. -/
theorem divSinMixedExpansion_half (Φ : ℝ → ℝ → ℝ) (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ)
    (j i : ℕ) (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j
        (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ
      = Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) z θ := by
  have hθ₁ : (-1 : ℝ) < θ := by linarith [hθ.1]
  have hθ₂ : θ < Real.pi / 2 + 1 := by linarith [hθ.2, Real.pi_pos]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hp : (z, θ) ∈ VnbhH := by
    rw [VnbhH, Set.mem_prod, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨hz, ⟨hθ₁, hθ₂⟩, hsin⟩
  have hf : ContDiffOn ℝ ⊤ (Function.uncurry Φ) VnbhH := (SmoothHalf.contDiffOn_hslab hΦ).mono VnbhH_subset
  have hc : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => invSin2 p.2) VnbhH := by
    have hsin_s : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) VnbhH :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hne : ∀ p ∈ VnbhH, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp'
      rw [VnbhH, Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hp'
      exact hp'.2.2
    exact hsin_s.inv hne
  have key := Work.Spaces.mixed_div_comm isOpen_VnbhH hf hc j i hp
  simpa only [invSin2, div_eq_mul_inv, Function.uncurry] using key

/-- The mixed derivative of the quotient `Φ/sin 2θ`, expressed as an angular iterate of the
slice of `D_z^j Φ`, for `z > 0`. -/
theorem mixed_div_eq_Dth1Iter_half (Φ : ℝ → ℝ → ℝ)
    (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ) (j i : ℕ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ (fun θ' => Work.Spaces.DzIter j Φ z θ')) θ := by
  have h1 := divSinMixedExpansion_half Φ hΦ j i z θ hz hθ
  have h2 := Work.Elliptic.dtw_DthIter_slice_at
    (fun z θ => Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) i z θ
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => Φ z θ / Real.sin (2 * θ))) z θ = _
  rw [h1, h2]
  exact Work.Elliptic.DivSinSliceIdent (fun θ' => Work.Spaces.DzIter j Φ z θ') i z θ hθ

/-- The angular iterate of the derivative of the slice of `D_z^j Φ` equals the mixed derivative
of `∂_θΦ`, for `z > 0`. -/
theorem Dth1Iter_deriv_eq_mixed_half (Φ : ℝ → ℝ → ℝ)
    (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ) (j m : ℕ) (z θ : ℝ) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := by
  have hy : (z, θ) ∈ hslab := mem_hslab hz hθ
  have hfun : (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ')
      = fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ' := by
    funext a θ'; rfl
  calc Work.Elliptic.Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
      = Work.Spaces.DthIter m
          (fun (_ : ℝ) θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ :=
        (Work.Elliptic.DthIter_const m
          (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') z θ).symm
    _ = Work.Spaces.DthIter m
          (fun (_ : ℝ) θ' => Work.Spaces.pth (Work.Spaces.DzIter j Φ) z θ') z θ := by rw [hfun]
    _ = Work.Spaces.DthIter m (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) z θ :=
        (Work.Elliptic.dtw_DthIter_slice_at (Work.Spaces.pth (Work.Spaces.DzIter j Φ)) m z θ).symm
    _ = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pth Φ)) z θ :=
        DthIter_congrOn isOpen_hslab
          (pth_DzIter_eqOn isOpen_hslab (SmoothHalf.contDiffOn_hslab hΦ) j) m hy
    _ = Work.Spaces.DzIter j (Work.Spaces.DthIter m (Work.Spaces.pth Φ)) z θ :=
        DthIter_DzIter_comm_eqOn isOpen_hslab
          (Work.Spaces.contDiffOn_uncurry_pth isOpen_hslab
            (SmoothHalf.contDiffOn_hslab hΦ)) j m hy
    _ = Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ := rfl

/-! ## Continuity of the slices of the quotient on `(0, π/2)` -/

/-- The slices `θ ↦ D_z^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`, for `z > 0`. -/
theorem pz_cont_DzIter_div_half (Φ : ℝ → ℝ → ℝ) (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ)
    (hv : Work.Spaces.VanishTheta Φ) (i : ℕ) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨hsm, -, -⟩ := DivSinSliceFacts_half Φ hΦ hv i z hz
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter i Φ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  refine (hcont.div (by fun_prop) (fun x hx => ne_of_gt (sin_two_pos_Ioo hx))).congr ?_
  intro θ hθ
  exact Work.Elliptic.DivSinFactor Φ i z θ hθ

/-- The mixed slices `θ ↦ D_z^j D_θ^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`, for
`z > 0`. -/
theorem pz_cont_mixed_div_half (Φ : ℝ → ℝ → ℝ) (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ)
    (hv : Work.Spaces.VanishTheta Φ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨hsm, -, -⟩ := DivSinSliceFacts_half Φ hΦ hv j z hz
  have hcd : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter i
      (Work.Elliptic.SinQ (fun θ => Work.Spaces.DzIter j Φ z θ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_Dth1Iter_of isOpen_Ioo (contDiffOn_SinQ_of hsm) i
  refine hcd.continuousOn.congr ?_
  intro θ hθ
  exact mixed_div_eq_Dth1Iter_half Φ hΦ j i z θ hz hθ

/-! ## The `H^k`-integrand at `z = 0` -/

@[simp] theorem w_zero : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]

/-- At `z = 0` the radial weight vanishes, and with it every summand of the `H^k`-integrand:
the integrand is identically zero. -/
@[simp] theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, w_zero, zero_div, mul_zero, Work.Spaces.Wt, Work.Spaces.wTheta]
  simp

/-- The same for the weighted mixed summand. -/
@[simp] theorem Wt_zero_z (α : ℝ) (θ : ℝ) : Work.Spaces.Wt α 0 θ = 0 := by
  simp [Work.Spaces.Wt]

/-! ## The pure-`D_z` termwise estimate at `z > 0` -/

private theorem dtwTermwiseZ_integrand_div (Φ : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i Φ z θ / Real.sin (2 * θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Elliptic.DivSinFactor Φ i z θ hθ]

/-- The pure-`D_z` termwise estimate of the division: for `z > 0` the `i`-th `D_z`-summand of
`Φ/sin 2θ` is bounded in weighted `L²(Iθ)` by the corresponding summand of `∂_θΦ`.  This is the
confirmation of the earlier, now removed file `divSin_Hk_gen.lean`. -/
theorem dtwTermwiseZ_half (k : ℕ) : ∃ KH : ℝ, 0 < KH ∧
    ∀ (Φ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothHalf Φ → Work.Spaces.VanishTheta Φ →
      ∀ {z : ℝ}, 0 < z → ∀ i ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ KH * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  obtain ⟨K, hKpos, hHardy⟩ := Work.Elliptic.dtw_hardy
  refine ⟨K, hKpos, ?_⟩
  intro Φ hΦ hv z hz i _
  obtain ⟨hsm, h0, hp⟩ := DivSinSliceFacts_half Φ hΦ hv i z hz
  have hslice := Work.Elliptic.dtw_SliceHardy hHardy (fun θ => Work.Spaces.DzIter i Φ z θ)
    (Work.Spaces.w z) hsm h0 hp
  have hL : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i Φ z θ / Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    integral_congr_ae (Work.Elliptic.dtw_ae_mem.mono (fun θ hθ =>
      dtwTermwiseZ_integrand_div Φ i z θ hθ))
  have hR : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.DzIter i Φ z θ') θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [Work.Elliptic.dtw_ae_mem] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    rw [← deriv_DzIter_slice_half Φ hΦ i hz hθI]
  rw [hL, hR]
  exact hslice

/-! ## A.e. strong measurability of the `H^k`-integrand of the quotient -/

/-- The uncurried `H^k`-integrand of `Φ/sin 2θ` is a.e. strongly measurable w.r.t. the product
of the restrictions of Lebesgue measure to `Iz` and `Iθ`, for `SmoothHalf Φ`. -/
theorem aesm_uncurry_HkIntegrand_SinQ_half (α : ℝ) (k : ℕ) (Φ : ℝ → ℝ → ℝ)
    (hΦ : Work.FTS.EllipticEst.SmoothHalf Φ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => Φ z θ / Real.sin (2 * θ)) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ hslab := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hnum : ContDiffOn ℝ ⊤ (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 :=
    (SmoothHalf.contDiffOn_hslab hΦ).mono hsub
  have hden : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
    rintro ⟨z, θ⟩ ⟨-, hθ0, hθ1⟩
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hdiv : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => Φ z θ / Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0 := by
    have h := hnum.div hden hne
    convert h using 1
    ext p
    rfl
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) :=
    hdiv.of_le le_top
  exact Work.Spaces.aesm_of_continuousOn_Qd _
    (hSO.continuousOn_HkIntegrand α k)

end Work.Blocks.Half
