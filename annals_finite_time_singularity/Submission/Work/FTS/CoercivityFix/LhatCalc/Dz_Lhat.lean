/-
# The `D_z`-commutator of the clean operator `Lhat = 𝓛 − Transport`

For `𝓛(f) = f + D_z f − 2f/(1+z)` and `Transport f = 3 D_θ f/(1+z)` (the paper's
angular transport term), put

  `Lhat f = 𝓛 f − Transport f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)`.

This file proves the **exact** `D_z`-commutator of `Lhat`:

  `D_z (Lhat f) = Lhat (D_z f) + E2hat f`,   `E2hat f = (2 z f + 3 z D_θ f)/(1+z)²`,

at every interior point `z > 0`, `0 < θ < π/2` of the open quadrant, for `f` of class
`Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on `(-1,∞) × (0,π/2)`).

The point of the identity is that the defect `E2hat f` contains **no nonlocal term**: it is
the explicitly bounded function `(2zf + 3z D_θ f)/(1+z)²`
(`Work.FTS.CoercivityFix.E2hat_abs_le`), unlike the paper's `E₂`, whose `D_z` falls on
`(2zΓ/(c(1+z)²)) L₁₂(f)` and produces an `L₁₂`-term.  Together with `Dth_Lhat` (whose
`D_θ`-commutator vanishes identically, so that `D_θ` preserves the class `L₁₂(f)(0) = 0`),
this is the formal content of the fix of node N2 described in `FTS/N45_DESIGN_LEAD.md` §5.

The proof is a direct calculation.  With `∂_z`, `∂_θ` the plain slice derivatives and
Clairaut's theorem `∂_z∂_θ f = ∂_θ∂_z f` (valid on the open quadrant because `f` is `C²`
there),

  `∂_z(𝓛 f)`   `= ∂_z f + (∂_z f + z ∂_z²f) − 2 ∂_z f/(1+z) + 2f/(1+z)²`,
  `∂_z(3D_θf/(1+z))` `= 3 sin(2θ) ∂_z∂_θf/(1+z) − 3 sin(2θ) ∂_θ f/(1+z)²`,

while

  `Lhat(D_z f) = z∂_zf + z(∂_zf + z∂_z²f) − 2z∂_zf/(1+z) − 3 sin(2θ) z ∂_θ∂_zf/(1+z)`,

so the difference of the two sides is exactly
`(2zf + 3z sin(2θ)∂_θf)/(1+z)² = E2hat f`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Basic
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

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false

/-! ## The open quadrant and the smoothness of the plain partials

`Work.FTS.LocData.SmoothQuad f` is smoothness of `Function.uncurry f` **on the open set**
`quadU = (-1,∞) × (0,π/2)`, in the order `Work.Stability.smoothOrder`.  Everything below is
local at an interior point `(z,θ)` of `quadU`, so we re-derive the few smoothness facts we
need from the class directly (rather than importing the heavy `QuadAux` module).
-/

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
private def quadU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private lemma isOpen_quadU : IsOpen quadU := isOpen_Ioi.prod isOpen_Ioo

private lemma mem_quadU_iff {z θ : ℝ} :
    ((z, θ) ∈ quadU) ↔ -1 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  rw [quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private lemma mem_quadU {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (z, θ) ∈ quadU :=
  mem_quadU_iff.mpr ⟨by linarith, hθ, hθ2⟩

private lemma smoothQuad_contDiffAt {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
  (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf).contDiffAt
    (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))

private lemma smoothQuad_contDiffAt_two {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (smoothQuad_contDiffAt hf hz hθ hθ2).of_le (by simp [Work.Stability.smoothOrder])

/-- The `z`-partial of a `C^∞`-on-`quadU` function is `C^∞` on `quadU`. -/
private lemma contDiffOn_uncurry_pz_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) quadU) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) quadU := by
  have hchain : ∀ p ∈ quadU, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_quadU.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) quadU := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_quadU.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_quadU hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) quadU := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a `C^∞`-on-`quadU` function is `C^∞` on `quadU`. -/
private lemma contDiffOn_uncurry_pth_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) quadU) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) quadU := by
  have hchain : ∀ p ∈ quadU, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder)
        (by simp [Work.Stability.smoothOrder])).differentiableAt (isOpen_quadU.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) quadU := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) isOpen_quadU.uniqueDiffOn
      (by simp [Work.Stability.smoothOrder])
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen isOpen_quadU hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) quadU := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

section Slices

variable {f : ℝ → ℝ → ℝ}

/-- The `z`-slices of `∂_z f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_pz (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pz_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `θ`-slices of `∂_z f` are differentiable at an interior point of the quadrant. -/
private lemma diff_th_pz (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
  Work.Spaces.differentiableAt_curry_right
    (((contDiffOn_uncurry_pz_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `z`-slices of `∂_θ f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_pth (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pth_quadU
        (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadU from hf)).contDiffAt
      (isOpen_quadU.mem_nhds (mem_quadU hz hθ hθ2))).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

/-- The `z`-slices of `f` are differentiable at an interior point of the quadrant. -/
private lemma diff_z_self (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    ((smoothQuad_contDiffAt hf hz hθ hθ2).differentiableAt
      (by simp [Work.Stability.smoothOrder]))

end Slices

/-! ## The plain `z`-derivatives of the pieces -/

private lemma deriv_z_self {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    deriv (fun z' => f z' θ) z = Work.Spaces.pz f z θ := rfl

private lemma deriv_z_mul_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h2 : deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z := rfl
  rw [h2, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_z_two_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z) :
    deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = 2 * Work.Spaces.pz f z θ / (1 + z) - 2 * f z θ / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (hfz.hasDerivAt.const_mul (2 : ℝ)).div
    ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z)) (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [deriv_z_self]
  field_simp
  try ring_nf

private lemma deriv_z_three_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (((hasDerivAt_const (x := z) (Real.sin (2 * θ))).mul hpthz.hasDerivAt).const_mul
    (3 : ℝ)).div ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z))
    (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = deriv ((fun y : ℝ => (fun _ : ℝ => (3 : ℝ)) y
            * ((fun _ : ℝ => Real.sin (2 * θ)) * fun z' => Work.Spaces.pth f z' θ) y)
          / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, zero_mul]
  rw [show deriv (fun z' => Work.Spaces.pth f z' θ) z
      = Work.Spaces.pz (Work.Spaces.pth f) z θ from rfl]
  field_simp
  try ring_nf

private lemma deriv_z_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' => Work.Spaces.Dz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h1 : (fun z' => Work.Spaces.Dz f z' θ)
      = (id * fun z' : ℝ => Work.Spaces.pz f z' θ) := by
    funext z'; rfl
  rw [h1, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_th_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ) :
    deriv (fun θ' => Work.Spaces.Dz f z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_const (x := θ) z).mul hpzθ.hasDerivAt
  have h1 : (fun θ' => Work.Spaces.Dz f z θ')
      = ((fun _ : ℝ => z) * fun θ' => Work.Spaces.pz f z θ') := by
    funext θ'; rfl
  rw [h1, hh.deriv]
  simp only [zero_mul, zero_add]
  rfl

/-! ## The `z`-derivatives of the slices of `𝓛 f` and of `Transport f` -/

private lemma pz_L_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.L f) z θ
      = Work.Spaces.pz f z θ + (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - 2 * Work.Spaces.pz f z θ / (1 + z) + 2 * f z θ / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.L f z' θ) z = _
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hid : DifferentiableAt ℝ (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z :=
    differentiableAt_id.mul hpzz
  have hq : DifferentiableAt ℝ
      ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z :=
    (hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden)
  have h1 : (fun z' => Work.Coercivity.L f z' θ)
      = (((fun z' : ℝ => f z' θ) + (id * fun z' : ℝ => Work.Spaces.pz f z' θ))
          - ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ)))) := by
    funext z'; rfl
  rw [h1, deriv_sub (hfz.add hid) hq, deriv_add hfz hid]
  rw [show deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z from rfl]
  rw [show deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z
      = deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z from rfl]
  rw [deriv_z_mul_pz hpzz, deriv_z_two_div hz hfz, deriv_z_self]
  ring

private lemma pz_Transport_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.Transport f) z θ
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.Transport f z' θ) z = _
  have h1 : (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) := by
    funext z'; rfl
  rw [h1, deriv_z_three_div hz hpthz]

private lemma diff_slice_L {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.L f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.L f z' θ)
      = (fun z' => f z' θ + z' * Work.Spaces.pz f z' θ - 2 * f z' θ / (1 + z')) from by
    funext z'; rfl]
  exact (hfz.add (differentiableAt_id.mul hpzz)).sub
    ((hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden))

private lemma diff_slice_Transport {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.Transport f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) from by
    funext z'; rfl]
  exact (((differentiableAt_const (c := Real.sin (2 * θ))).mul hpthz).const_mul 3).div
    ((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id) (by simpa using hden)

/-! ## The commutator identity -/

/-- **The `D_z`-commutator of the clean operator** `𝓛̂ = 𝓛 − Transport`:
`D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`, with the explicit bounded defect
`Ê₂ f = (2zf + 3z D_θ f)/(1+z)²`. -/
theorem Dz_Lhat {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hfz := diff_z_self hf hz hθ hθ2
  have hpzz := diff_z_pz hf hz hθ hθ2
  have hpzθ := diff_th_pz hf hz hθ hθ2
  have hpthz := diff_z_pth hf hz hθ hθ2
  have hLz := diff_slice_L (θ := θ) hz hfz hpzz
  have hTz := diff_slice_Transport (θ := θ) hz hpthz
  -- the plain `z`-derivatives of the two summands of `𝓛̂`
  have hpzL := pz_L_eq (θ := θ) hz hfz hpzz
  have hpzT := pz_Transport_eq (θ := θ) hz hpthz
  have hpzLhat : Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pz (Work.Coercivity.L f) z θ
        - Work.Spaces.pz (Work.Coercivity.Transport f) z θ := by
    show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    have h1 : (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ)
        = ((fun z' => Work.Coercivity.L f z' θ)
            - fun z' => Work.Coercivity.Transport f z' θ) := by
      funext z'; rfl
    rw [h1, deriv_sub hLz hTz]
    rfl
  have hLHS : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz (Work.Coercivity.L f) z θ
          - Work.Spaces.pz (Work.Coercivity.Transport f) z θ) := by
    show z * deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    rw [show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z
        = Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hpzLhat]
  -- the right-hand side
  have hDzDz : Work.Spaces.Dz (Work.Spaces.Dz f) z θ
      = z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) := by
    show z * deriv (fun z' => Work.Spaces.Dz f z' θ) z = _
    rw [deriv_z_Dz hpzz]
  have hDthDz : Work.Spaces.Dth (Work.Spaces.Dz f) z θ
      = Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ) := by
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.Dz f z θ') θ = _
    rw [deriv_th_Dz hpzθ]
  have hRHS : Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ
      = (z * Work.Spaces.pz f z θ
          + z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
          - 2 * (z * Work.Spaces.pz f z θ) / (1 + z)
          - 3 * (Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ)) / (1 + z))
        + (2 * z * f z θ + 3 * z * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) / (1 + z) ^ 2 := by
    rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz f), Work.FTS.CoercivityFix.E2hat_eq]
    rw [hDzDz, hDthDz]
    rw [show Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ from rfl,
      show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  -- Clairaut's theorem finishes the identification `∂_θ∂_z f = ∂_z∂_θ f`
  have hcl := Work.Spaces.pz_pth_comm (smoothQuad_contDiffAt_two hf hz hθ hθ2)
  rw [hLHS, hRHS, hpzL, hpzT, hcl]
  field_simp
  try ring_nf

end Work.FTS.CoercivityFix.LhatCalc
