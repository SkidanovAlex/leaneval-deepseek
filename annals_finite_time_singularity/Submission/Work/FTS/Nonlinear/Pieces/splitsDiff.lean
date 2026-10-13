/-
# `splitsDiff` — the split of `N₀`, `N` and `N_*`, with the missing differentiability hypothesis

**Why this file exists.**  The requested lemma `Work.FTS.Nonlinear.Pieces.splits` states the three
splits (`N₀ = N₀^{F_*} + Σ …`, the four-way split of `N`, the collapse of `N_*` with
`λ = lamfun μ`) under `SmoothQuad`-hypotheses plus the two *algebraic* integrability inputs `hL`
and `hFK`.  As written it is **false**: the four-way split of `N` needs the additivity of
`∂_z` on the two straightened stream functions

  `Φ̃_* = PhiTil α (Fstar α) Φs`,   `Φ̃_g = PhiTil α g Φg`,

i.e. `deriv_add` for the `z`-slices `z' ↦ Φs z' θ - (1/(4α)) sin(2θ) L₁₂(F_*)(z')` and
`z' ↦ Φg z' θ - (1/(4α)) sin(2θ) L₁₂(g)(z')`, whence in particular
`DifferentiableAt ℝ (fun z => L₁₂(g)(z)) z`.  `SmoothQuad g` (which only says that `g` is `C^∞`
on the *open* quadrant `z > -1, 0 < θ < π/2`) does not provide this: it gives no control of `g`
at the angular endpoints, hence neither integrability nor continuity of the `L₁₂`-density
`L12dens g`, and `hL`/`hFK` are statements about *values* of `L₁₂`/`FK` only.  Concretely one can
take (`z₀ = 1`)

  `g z θ = θ⁻² H((z - z₀)/θ) - η(θ) φ(z)`,

with `H ∈ C_c^∞((0,1))` of the form `H(u) = u·bump(u)`, `η ∈ C_c^∞((0,π/2))` supported near
`θ = π/8` and `φ ∈ C_c^∞((2,3))`, the scale of `η` being chosen so that
`∫_{-1}^∞ L12dens g = 0`: then `g` is `C^∞` on the open quadrant, `L12dens g` vanishes on
`(-∞, z₀]` and jumps to `3∫_0^1 H(u)/u du / z₀ ≠ 0` at `z₀⁺` (the `θ`-support
`0.1θ < z - z₀ < 0.9θ` shrinks as `z ↓ z₀` while the values grow like `1/(z-z₀)²`), so that
`z ↦ L₁₂(g)(z)` is *constant* on `(-∞, z₀]` with right derivative `-3∫H(u)/u du / z₀ ≠ 0` — not
differentiable at `z₀`.  This `g` satisfies `hL` (for every real `z`, including the junk values at
`z ≤ -1` where `L12dens (Fstar α)` has its pole at `s = -1`) and `hFK`, so
`Work.FTS.Nonlinear.Pieces.splits` fails; the failure is *exactly* the term
`2 α z · a · (tan θ · F_tot + ∂_θF_tot)` with `a = ∂_zΨ - ∂_zΨ₁ - ∂_zΨ₂`.

This module contains the **corrected** statement: the same three splits, with the additional
hypotheses `0 < α ≤ 1` and

  `∀ z, 0 < z → DifferentiableAt ℝ (fun z => L₁₂(g)(z)) z`

(the only extra analytic input needed; under the classes of the design it is what
`L12densFacts`-type arguments supply, e.g. `IntegrableOn (L12dens g) (Ioi 0)` together with
`∀ z > 0, ContinuousAt (L12dens g) z` give it via `Work.FM.hasDerivAt_L12`).  It is `sorry`-free,
so it can be imported directly.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

/-! ## Differentiability of the slices of a `SmoothQuad` function -/

/-- The `z`-slice of a `SmoothQuad` function is differentiable at every `z > -1`, at every
`θ ∈ (0, π/2)`. -/
theorem differentiableAt_slice_z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z :=
  (((hf.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz))

/-- The `θ`-slice of a `SmoothQuad` function is differentiable at every `θ ∈ (0, π/2)`, at every
`z > -1`. -/
theorem differentiableAt_slice_θ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ :=
  (((hf.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioo.mem_nhds hθ))

/-- `∂_θ` is additive on the sum of two functions whose `θ`-slices are differentiable. -/
theorem pth_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hh : DifferentiableAt ℝ (fun θ' => h z θ') θ) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => f z θ' + h z θ') = (fun θ' => f z θ') + (fun θ' => h z θ') from rfl,
    deriv_add hf hh]

/-- `∂_z` is additive on the sum of two functions whose `z`-slices are differentiable. -/
theorem pz_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hh : DifferentiableAt ℝ (fun z' => h z' θ) z) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => f z' θ + h z' θ) = (fun z' => f z' θ) + (fun z' => h z' θ) from rfl,
    deriv_add hf hh]

/-- `∂_θ` is additive on a sum of `SmoothQuad` functions (on the quadrant). -/
theorem pth_add_of_smoothQuad {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hh : Work.FTS.LocData.SmoothQuad h) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1 : ℝ))
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pth (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth h z θ :=
  pth_add_of_diff (differentiableAt_slice_θ hf hz hθ) (differentiableAt_slice_θ hh hz hθ)

/-- `∂_z` is additive on a sum of `SmoothQuad` functions (on the quadrant). -/
theorem pz_add_of_smoothQuad {f h : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hh : Work.FTS.LocData.SmoothQuad h) {z θ : ℝ} (hz : z ∈ Set.Ioi (-1 : ℝ))
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ :=
  pz_add_of_diff (differentiableAt_slice_z hf hz hθ) (differentiableAt_slice_z hh hz hθ)

/-- `D_z = z ∂_z` is additive as soon as `∂_z` is. -/
theorem Dz_add_of_diff {f h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz h z θ) :
    Work.Spaces.Dz (fun z θ => f z θ + h z θ) z θ
      = Work.Spaces.Dz f z θ + Work.Spaces.Dz h z θ := by
  simp only [Work.Spaces.Dz, hpz]; ring

/-- `D_θ f = s2 θ · ∂_θ f` (the `sin (2θ)` of `Construction.s2`). -/
theorem Dth_eq_s2_mul (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dth f z θ = Work.Construction.s2 θ * Work.Spaces.pth f z θ := rfl

/-! ## The derivative of `z ↦ L₁₂(F_*)` -/

/-- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` is differentiable at every `z > 0`. -/
theorem differentiableAt_L12_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z := by
  have hev : (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z')
      =ᶠ[𝓝 z] (fun z' => 2 * α / (1 + z')) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.Construction.L12_Fstar_eq hα hα1 hz'.le
  exact (Filter.EventuallyEq.differentiableAt_iff hev).mpr
    ((differentiableAt_const (2 * α)).div
      ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) (by intro h; linarith))

/-! ## Additivity of `ℛ`, `U`, `V` in their argument -/

/-- `ℛ` is additive in its argument, provided `∂_z` and `∂_θ` are additive for the pair. -/
theorem Rop_add_of_diff {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ)
    (hpth : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ) :
    Work.Construction.Rop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Rop α Ψ₁ z θ + Work.Construction.Rop α Ψ₂ z θ := by
  simp only [Work.Construction.Rop, hpz, hpth]
  ring

/-- `U` is additive in its argument. -/
theorem Uop_add_of_diff {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ) :
    Work.Construction.Uop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Uop α Ψ₁ z θ + Work.Construction.Uop α Ψ₂ z θ := by
  simp only [Work.Construction.Uop, hpz]
  ring

/-- `V` is additive in its argument. -/
theorem Vop_add_of_diff {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpth : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ) :
    Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ := by
  simp only [Work.Construction.Vop, hpth]
  ring

/-! ## The corrected splits -/

theorem splits_of_diff {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.LocData.SmoothQuad g) (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α))
    (hL : ∀ z : ℝ, Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hFK : ∀ z : ℝ, Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ
            + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ
            + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ
            + Work.FTS.Nonlin.N06F α g z θ)) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ)) ∧
    (∀ μ : ℝ, μ ≠ -1 → ∀ z θ : ℝ,
      Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
        = Work.FTS.Nonlin.NstarLam μ g z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## the split of `N₀`
    intro z θ hq
    have hz : z ∈ Set.Ioi (-1 : ℝ) := by
      rw [Set.mem_Ioi]; exact lt_trans (by norm_num) hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      pth_add_of_smoothQuad hF hreg hz hθ
    have hDz : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
      Dz_add_of_diff (pz_add_of_smoothQuad hF hreg hz hθ)
    simp only [Work.Construction.N0, Work.FTS.Nonlin.N0fix, Work.FTS.Nonlin.N03g,
      Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF, Work.FTS.Nonlin.N05aF,
      Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F, Work.Construction.N01,
      Work.Construction.N02, Work.Construction.N03, Work.Construction.N04a,
      Work.Construction.N04b, Work.Construction.N05a, Work.Construction.N05b,
      Work.Construction.N06]
    rw [hpth, hDz]
    ring
  · -- ## the four-way split of `N`
    intro z θ hq
    have hz : z ∈ Set.Ioi (-1 : ℝ) := by
      rw [Set.mem_Ioi]; exact lt_trans (by norm_num) hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
    have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      pth_add_of_smoothQuad hF hreg hz hθ
    have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
      Dz_add_of_diff (pz_add_of_smoothQuad hF hreg hz hθ)
    -- the two straightened stream functions, unfolded on the quadrant
    have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
        = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
            * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
    have hPsi2 : Work.Construction.PhiTil α g Φg
        = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
            * Work.Construction.L12 g z' := rfl
    have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
      have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
      rw [h]
      exact Real.differentiableAt_sin.comp θ
        ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
    have hzs1 : DifferentiableAt ℝ
        (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z := by
      rw [hPsi1]
      exact (differentiableAt_slice_z hΦs hz hθ).sub
        ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
          (differentiableAt_L12_Fstar hα hα1 hq.1))
    have hzs2 : DifferentiableAt ℝ
        (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
      rw [hPsi2]
      exact (differentiableAt_slice_z hΦg hz hθ).sub
        ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
          (hL12 z hq.1))
    have hts1 : DifferentiableAt ℝ
        (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
      rw [hPsi1]
      exact (differentiableAt_slice_θ hΦs hz hθ).sub
        (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
          (differentiableAt_const _))
    have hts2 : DifferentiableAt ℝ
        (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
      rw [hPsi2]
      exact (differentiableAt_slice_θ hΦg hz hθ).sub
        (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
          (differentiableAt_const _))
    have hpz : Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ :=
      pz_add_of_diff hzs1 hzs2
    have hpth : Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
      pth_add_of_diff hts1 hts2
    -- the straightened stream function of `F_tot` is the sum of the two
    have hPhiSum : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
          + Work.Construction.PhiTil α g Φg := by
      funext z' θ'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Pi.add_apply]
      rw [hL z']
      ring
    have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ := by
      rw [hPhiSum]
      exact Rop_add_of_diff hpz hpth
    have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
      rw [hPhiSum]
      exact Uop_add_of_diff hpz
    have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
      rw [hPhiSum]
      exact Vop_add_of_diff hpth
    -- the five groups of the right-hand side
    have hN1 : Work.Construction.N1 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ := by
      simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
        Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.FTS.Nonlin.PhiTg,
        Work.FTS.Nonlin.PhiTs, Work.Construction.Ftot]
      rw [hRop]
      ring
    have hN2 : Work.Construction.N2 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ := by
      simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
        Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
        Work.FTS.Nonlin.PhiTs]
      rw [hUop, hpthF]
      ring
    have hN3 : Work.Construction.N3 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ := by
      simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
        Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
        Work.FTS.Nonlin.PhiTs]
      rw [hVop, hDzF]
      ring
    have hN4 : Work.Construction.N4 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
          + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) := by
      simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
        Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Work.Construction.Ftot]
      simp only [Dth_eq_s2_mul]
      rw [hFK z, hpthF]
      ring
    have hN5 : Work.Construction.N5 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
          + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
      simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
        Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
      rw [hFK z]
      ring
    rw [Work.Construction.N_eq_sum]
    simp only [Pi.add_apply, hN1, hN2, hN3, hN4, hN5]
    ring
  · -- ## the collapse of `N_*`
    intro μ hμ z θ
    have hμ' : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
    have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
      rw [Work.Construction.lamfun]
      field_simp
      ring
    simp only [Work.Construction.Nstar, Work.FTS.Nonlin.NstarLam, Work.Spaces.Dz]
    rw [hcoef]
    field_simp
    ring

/-! ## What the split really needs

The three lemmas below compute the *difference* between an operator applied to the sum `Ψ` of the
two straightened stream functions and the sum of the operators applied to the two pieces.  They
are pure algebra (no additivity is assumed!), and they are what shows that the four-way split of
`N` is equivalent to the additivity of `∂_z` on `Φ̃_*` and `Φ̃_g`. -/

/-- The difference of `ℛ` at a sum, in terms of the differences of `∂_z` and `∂_θ`, with the
coefficient `α z tan θ` (no division left). -/
theorem Rop_split_of_diff {α : ℝ} {Ψ Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hcos : Real.cos θ ≠ 0) (hΨ : Ψ z θ = Ψ₁ z θ + Ψ₂ z θ) :
    Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ₁ z θ
      + Work.Construction.Rop α Ψ₂ z θ
      + (α * Real.tan θ * z
            * (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ₁ z θ - Work.Spaces.pz Ψ₂ z θ)
          + (Work.Spaces.pth Ψ z θ - Work.Spaces.pth Ψ₁ z θ - Work.Spaces.pth Ψ₂ z θ)) := by
  simp only [Work.Construction.Rop]
  rw [hΨ, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The difference of `U` at a sum, in terms of the difference of `∂_z`. -/
theorem Uop_split_of_diff {α : ℝ} {Ψ Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨ : Ψ z θ = Ψ₁ z θ + Ψ₂ z θ) :
    Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ₁ z θ
      + Work.Construction.Uop α Ψ₂ z θ
      - α * z * (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ₁ z θ - Work.Spaces.pz Ψ₂ z θ) := by
  simp only [Work.Construction.Uop]
  rw [hΨ]
  ring

/-- The difference of `V` at a sum, in terms of the difference of `∂_θ`. -/
theorem Vop_split_of_diff {Ψ Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨ : Ψ z θ = Ψ₁ z θ + Ψ₂ z θ) :
    Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ₁ z θ
      + Work.Construction.Vop Ψ₂ z θ
      + (Work.Spaces.pth Ψ z θ - Work.Spaces.pth Ψ₁ z θ - Work.Spaces.pth Ψ₂ z θ) := by
  simp only [Work.Construction.Vop]
  rw [hΨ]
  ring

/-- **The split forces the additivity of `∂_z` on `Φ̃_*` and `Φ̃_g`.**  If the four-way split of
`N` holds at `(z,θ)` and the coefficient `tan θ · F_tot + ∂_θF_tot` is non-zero (and `α ≠ 0`),
then `∂_z` must be additive on the two straightened stream functions.  This is the precise sense
in which the requested statement `Work.FTS.Nonlinear.Pieces.splits` needs the (absent)
differentiability of `z ↦ L₁₂(g)(z)`. -/
theorem splits_implies_pz_add {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hreg : Work.FTS.LocData.SmoothQuad g) (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α))
    (hL : ∀ z : ℝ, Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hFK : ∀ z : ℝ, Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z)
    (hSplit : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ))
    {z θ : ℝ} (hq : (z, θ) ∈ Work.Construction.Qd) (hα : α ≠ 0)
    (hbracket : Real.tan θ * Work.Construction.Ftot α g z θ
        + Work.Spaces.pth (Work.Construction.Ftot α g) z θ ≠ 0) :
    Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ := by
  have hz : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Set.mem_Ioi]; exact lt_trans (by norm_num) hq.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hz0 : z ≠ 0 := ne_of_gt hq.1
  have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    pth_add_of_smoothQuad hF hreg hz hθ
  have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Dz_add_of_diff (pz_add_of_smoothQuad hF hreg hz hθ)
  have hpzF : Work.Spaces.pz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz g z θ :=
    pz_add_of_smoothQuad hF hreg hz hθ
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
  have hPhiSum : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
        + Work.Construction.PhiTil α g Φg := by
    funext z' θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Pi.add_apply]
    rw [hL z']
    ring
  have hsumpt : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ :=
    congrFun (congrFun hPhiSum z) θ
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (differentiableAt_slice_θ hΦs hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (differentiableAt_slice_θ hΦg hz hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul (differentiableAt_const _))
  have hpthPsi : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
        + Work.Construction.PhiTil α g Φg) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
    pth_add_of_diff hts1 hts2
  -- the `∂_θ`-difference vanishes
  have hB0 : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      - Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      - Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ = 0 := by
    rw [hPhiSum]
    rw [hpthPsi]
    ring
  -- the three operator differences
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hRsplit : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ
        + (α * Real.tan θ * z
              * (Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
                    (fun z θ => Φs z θ + Φg z θ)) z θ
                  - Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
                  - Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ)
            + (Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
                    (fun z θ => Φs z θ + Φg z θ)) z θ
                  - Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
                  - Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ)) :=
    Rop_split_of_diff hcos hsumpt
  have hUsplit : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
        - α * z * (Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ) :=
    Uop_split_of_diff hsumpt
  have hVsplit : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ
        + (Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ) :=
    Vop_split_of_diff hsumpt
  -- the group-by-group differences
  have hd1 : Work.Construction.N1 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      - (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
      = 2 * (Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ)
          * Work.Construction.Ftot α g z θ := by
    simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
      Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs, Work.Construction.Ftot]
    ring
  have hd2 : Work.Construction.N2 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      - (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
      = -2 * (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ)
          * Work.Spaces.pth (Work.Construction.Ftot α g) z θ := by
    simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
      Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hpthF]
    ring
  have hd3 : Work.Construction.N3 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      - (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
      = -2 * α * (Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftot α g) z θ := by
    simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
      Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hDzF]
    ring
  have hd4 : Work.Construction.N4 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      - ((Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
          + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)) = 0 := by
    simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
      Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Dth_eq_s2_mul, Work.Construction.Ftot]
    rw [hFK z, hpthF]
    ring
  have hd5 : Work.Construction.N5 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      - ((Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
          + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ)) = 0 := by
    simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
      Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
    rw [hFK z]
    ring
  -- the difference of the two sides
  have key : (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ)
      - ((Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ))
      = 2 * α * z * (Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ)
          * (Real.tan θ * Work.Construction.Ftot α g z θ
            + Work.Spaces.pth (Work.Construction.Ftot α g) z θ)
        + 2 * (Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
                (fun z θ => Φs z θ + Φg z θ)) z θ
              - Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
              - Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ)
          * (Work.Construction.Ftot α g z θ
            - α * z * Work.Spaces.pz (Work.Construction.Ftot α g) z θ) := by
    have hN := Work.Construction.N_eq_sum α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)
    have h1 : Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.N1 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.N2 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.N3 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.N4 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.N5 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ := by
      rw [hN]
      simp only [Pi.add_apply]
    have hrearr : Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
        - ((Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
              + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
            + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
              + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
            + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
              + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
            + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
              + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
            + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
              + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ))
        = (Work.Construction.N1 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
              - (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
                  + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ))
          + (Work.Construction.N2 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
              - (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
                  + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ))
          + (Work.Construction.N3 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
              - (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
                  + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ))
          + (Work.Construction.N4 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
              - ((Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
                  + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)))
          + (Work.Construction.N5 α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
              - ((Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
                  + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ))) := by
      rw [h1]
      ring
    rw [hrearr, hd1, hd2, hd3, hd4, hd5]
    rw [hRsplit, hUsplit, hVsplit]
    simp only [Work.Spaces.Dz]
    rw [hpthF, hpzF]
    simp only [Work.Construction.Ftot]
    ring
  -- combine with the assumed split
  have hzero : 2 * α * z * (Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        - Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        - Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ)
        * (Real.tan θ * Work.Construction.Ftot α g z θ
          + Work.Spaces.pth (Work.Construction.Ftot α g) z θ)
      + 2 * (Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) z θ
            - Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
            - Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ)
        * (Work.Construction.Ftot α g z θ
          - α * z * Work.Spaces.pz (Work.Construction.Ftot α g) z θ) = 0 := by
    have h1 := hSplit z θ hq
    linarith [key]
  simp only [hB0, mul_zero, zero_mul, add_zero] at hzero
  have hcoef : 2 * α * z * (Real.tan θ * Work.Construction.Ftot α g z θ
      + Work.Spaces.pth (Work.Construction.Ftot α g) z θ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hα) hz0) hbracket
  have hA0 : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      - Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      - Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (mul_ne_zero (mul_ne_zero (by norm_num) hα) hz0)
      · exact h'
    · exact absurd h hbracket
  linarith [hA0]

end Work.FTS.Nonlinear.Pieces
