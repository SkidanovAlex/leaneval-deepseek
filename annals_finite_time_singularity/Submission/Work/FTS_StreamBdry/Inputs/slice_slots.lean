import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Slots.v2_starUop
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffBounds
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `Work.FTS_StreamBdry.Inputs.slice_slots` — the `SlotBd` half of `slice_inputs`

This module assembles the `SlotBd` conjunct of `Work.FTS_StreamBdry.Inputs.slice_inputs` out of

* `residual_slot_jets` (the order-`≤ 2` jets of the `𝒰/sin 2θ`- and `𝒱`-slots of the residual
  `Φ̃ = v2_PhiT a Φs E g τ`), and
* `theta_part_jets` (the same jets for the singular part `Θ a (Ftau a g τ)`),

using the pointwise splitting of the stream function `Ψ = slice (PsiCan Φs E g) τ` into
`Φ̃ + Θ(F)` on the open quadrant (`PhiTil = id - Theta`, plus `v2_slice_PhiR_eq`) and the
linearity of `Uop`, `Vop` and `mixed`.

## The bridge: the sanitised and the canonical objects agree

`v2_slice_PhiR_eq` (`RXT.velVanish2Aux`) gives `slice (ΦR a Φs E g) τ = Φs + E (slice g τ)` on the
open quadrant, i.e. the *slice of the canonical stream function* `PsiCan Φs E g`; and
`Ftau (pExp a) (GR a g) τ = Fstar + slice (GR a g) τ` agrees there with `Ftau (pExp a) g τ`
(because `GR a g = gS a (tauExt g)` agrees with `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`), hence the
`L₁₂`-values — and with them `Theta` — agree (`RXR5.L12_congr_of_agreeOnQ`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- `Ftau` of the sanitised family `GR a g = gS a (tauExt g)` agrees with `Ftau` of `g` on the
open quadrant, for `τ ≥ 0`. -/
theorem agreeOnQ_Ftau_GR {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)
      (Work.Construction.Ftau (pExp a) g τ) := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.RegExportIface.RXT.GR a g z θ τ = g z θ τ := by
    rw [Work.FTS.RegExportIface.RXT.GR]
    exact (Work.FTS_RegExport.RXR5.SG_apply_of_pos (α := a) (g := g) hz hθ.le hθ2.le).trans
      (Work.FTS.FinalV2.tauExt_of_nonneg g hτ)
  simp only [Work.Construction.Ftau, Work.FTS.Galerkin.slice_apply, h1]

/-- The `L₁₂`-values of the two `Ftau`'s agree for `z ≥ 0`. -/
theorem L12_Ftau_GR_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp a) g τ) z :=
  Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ (agreeOnQ_Ftau_GR (a := a) hτ) hz

/-- The singular parts `Θ` of the two `Ftau`'s agree as functions of `θ`, for `z > 0`. -/
theorem Theta_Ftau_GR_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a)
        (Work.FTS.RegExportIface.RXT.GR a g) τ) z
      = Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a) g τ) z := by
  funext θ
  simp only [Work.Construction.Theta]
  rw [L12_Ftau_GR_eq (a := a) hτ hz.le]

/-- The slice of the canonical stream function is, on the open quadrant, the slice of the
sanitised `ΦR` (they are the same function there). -/
theorem slice_PsiCan_eq_slice_PhiR {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
      = slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ z θ := by
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  rw [Work.FTS_RegExport.RXT.v2_slice_PhiR_eq (αG := a) (Φs := Φs) (E := E) (g := g) hτ z θ
    hz hθ hθ2]
  simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply]

/-- On the open quadrant the slice of the sanitised stream function is the residual plus the
singular part: `Ψ = Φ̃ + Θ(F)` (definitional in `PhiTil = id - Theta`). -/
theorem slice_PhiR_eq_resid_add_Theta {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ z θ : ℝ} :
    slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ z θ
      = Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ z θ
        + Work.Construction.Theta (pExp a)
          (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ := by
  simp only [Work.FTS_RegExport.RXT.v2_PhiT, Work.Construction.PhiTil]
  ring

/-- On the open quadrant the slice of the canonical stream function is the residual plus the
singular part. -/
theorem slice_PsiCan_eq_resid_add_Theta {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
      = Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ z θ
        + Work.Construction.Theta (pExp a)
          (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ :=
  (slice_PsiCan_eq_slice_PhiR (a := a) hτ hzθ).trans slice_PhiR_eq_resid_add_Theta

/-! ## The slot functions of the two pieces -/

/-- The `𝒰/sin 2θ`-slot of the residual `Φ̃ = v2_PhiT a Φs E g τ` (= `v2_SlotU a` of it). -/
abbrev Ures (a : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_SlotU a (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)

/-- The `𝒱`-slot of the residual. -/
abbrev Vres (a : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_SlotV a (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)

/-- The `𝒰/sin 2θ`-slot of the singular part `Θ` of the **sanitised** source. -/
abbrev UthS (a : ℝ) (g : Fam) (τ : ℝ) : Fn := fun z θ =>
  Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
    / Real.sin (2 * θ)

/-- The `𝒱`-slot of the singular part `Θ` of the **sanitised** source. -/
abbrev VthS (a : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Vop (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ))

/-- The `𝒰/sin 2θ`-slot of the singular part `Θ` of the **canonical** source. -/
abbrev Uth (a : ℝ) (g : Fam) (τ : ℝ) : Fn := fun z θ =>
  Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) g τ)) z θ / Real.sin (2 * θ)

/-- The `𝒱`-slot of the singular part `Θ` of the **canonical** source. -/
abbrev Vth (a : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Vop (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) g τ))

/-! ## The closed form of `Vop` of the singular part -/

/-- `𝓥(Θ αG F)(z,θ) = L₁₂(F)(z)·c2m(θ)/(2αG)` on the open quadrant. -/
theorem Vop_Theta_closed {αG : ℝ} (F : Fn) {z θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ / (2 * αG) := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    show deriv (fun θ' => Work.Construction.Theta αG F z θ') θ = _
    have h1 : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
        (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
      simpa [mul_comm] using h
    rw [h1, (h2.const_mul _).deriv]
    ring
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  ring

/-! ## The pointwise splitting of the stream function into residual and singular part -/

/-- `Uop` of the singular part is the same for the sanitised and the canonical source. -/
theorem Uop_Theta_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
      = Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ)) z θ := by
  have hev : (fun z' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact congrFun (Theta_Ftau_GR_eq (a := a) (g := g) hτ hz') θ
  have hval : Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ
      = Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a) g τ) z θ :=
    hev.self_of_nhds
  simp only [Work.Construction.Uop, Work.Spaces.pz]
  rw [hev.deriv_eq, hval]

/-- `Vop` of the singular part is the same for the sanitised and the canonical source. -/
theorem Vop_Theta_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Vop (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
      = Work.Construction.Vop (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ)) z θ := by
  have hfun := Theta_Ftau_GR_eq (a := a) (g := g) hτ hz
  have h1 : deriv (fun θ' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ') θ
      = deriv (fun θ' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ) z θ') θ := by
    rw [hfun]
  have h2 := congrFun hfun θ
  simp only [Work.Construction.Vop, Work.Spaces.pth, h1, h2]

/-- The `Θ`-slots of the sanitised and the canonical source agree on `z > 0`. -/
theorem eqOn_UthS_Uth {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Set.EqOn (Function.uncurry (UthS a g τ)) (Function.uncurry (Uth a g τ))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz0 : 0 < z := hp.1
  simp only [Function.uncurry, UthS, Uth]
  rw [Uop_Theta_eq (a := a) (g := g) hτ hz0]

/-- The `Θ`-slots of the sanitised and the canonical source agree on `z > 0`. -/
theorem eqOn_VthS_Vth {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Set.EqOn (Function.uncurry (VthS a g τ)) (Function.uncurry (Vth a g τ))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz0 : 0 < z := hp.1
  simp only [Function.uncurry, VthS, Vth]
  rw [Vop_Theta_eq (a := a) (g := g) hτ hz0]

/-- The `𝒰/sin 2θ`-slot of the slice of `ΦR` splits as residual plus singular part. -/
theorem eqOn_Uprime_split {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hSΨ : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0) :
    Set.EqOn
      (Function.uncurry (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)))
      (Function.uncurry (Ures a Φs E g τ + UthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hzθ
  have h1 := Work.FTS_RegExport.RXT.Sys.uop_split_theta (α := a) (Φs := Φs) (E := E) (g := g)
    (τ := τ) hzθ hSΨ hSΘ
  simp only [Function.uncurry, Pi.add_apply, Work.FTS.StreamBdryIface.Uprime, Ures, UthS,
    Work.FTS_RegExport.RXT.v2_SlotU, Work.Construction.s2, h1]
  ring

/-- The `𝒱`-slot of the slice of `ΦR` splits as residual plus singular part. -/
theorem eqOn_Vop_split {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hSΨ : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0) :
    Set.EqOn
      (Function.uncurry (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)))
      (Function.uncurry (Vres a Φs E g τ + VthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hzθ
  have h1 := Work.FTS_RegExport.RXT.v2_vop_add_at (f := Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)
    (g := Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) hSΨ hSΘ hzθ
  have hfun : slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ
      = fun z θ => Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ z θ
          + Work.Construction.Theta (pExp a)
            (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ :=
    funext fun z => funext fun θ => slice_PhiR_eq_resid_add_Theta
  simp only [Function.uncurry, Pi.add_apply, Vres, VthS,
    Work.FTS_RegExport.RXT.v2_SlotV, hfun, h1]

/-- Additivity of `mixed` for a sum of two `C²`-functions on the open quadrant (the `Pi.add`
form of `RXT.Sys.mixed_add_lam`). -/
theorem mixed_add_of {f h : Fn} (hf : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Work.FTS.EllipticEst.Q0) {j i : ℕ}
    (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (f + h) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i h z θ :=
  Work.FTS_RegExport.RXT.Sys.mixed_add_lam hf hh hji hzθ

