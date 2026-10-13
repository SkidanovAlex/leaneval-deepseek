/-
# `splits_of_ctx` — the three splits of `N₀`, `N` and `N_*` under `RowCtx`

This file proves `Work.FTS.Nonlinear.Pieces.splits_of_ctx`, the lemma the N4 assembly
(`Pieces/rowInputs_of_parts`) consumes as its three split hypotheses `hspl0`, `hspl`, `hNs`.

**What the splits need.**  The first (`N₀`) and the third (`N_*`) conjunct are algebra; the
second (the four-way split of `N`) is not: it compares `ℛ, U, V` evaluated at the *sum*
`Φ̃ = Φ̃_* + Φ̃_g` of the two straightened stream functions with the sum of the operators evaluated
at the pieces.  Purely algebraically (see `splitsDiff.lean`) the difference is

  `2αz·(∂_zΦ̃ - ∂_zΦ̃_* - ∂_zΦ̃_g)·(tan θ·F + ∂_θF) + 2·(∂_θΦ̃ - ∂_θΦ̃_* - ∂_θΦ̃_g)·(F - αz∂_zF)`,

so the split is *equivalent* to the additivity of `∂_z` and `∂_θ` on the two straightened stream
functions.  At a point of the open quadrant `Qd` (`z > 0`) the pointwise identity

  `Φ̃(z,θ) = Φ̃_*(z,θ) + Φ̃_g(z,θ)`     (`PhiTil_add_ge0`, below)

holds — it is `L₁₂`-additivity on the profile `F = F_* + g`, which is available on `z ≥ 0`
(`L12FK_add_ge0`) — and it holds for *all* `θ'` resp. *all* `z' ≥ 0`, which is exactly what the
derivative additivity needs: `deriv_add` for the `θ`-slices, and, for the `z`-slices, the
eventual-equalities congruence `Filter.EventuallyEq.deriv_eq` on a neighbourhood of `z > 0`.
The differentiability of `z ↦ L₁₂(g)(z)` on `(0,∞)` is the field `l12diff` of the interface
`N4Norm` carried by `RowCtx` (it is the analytic input `Work.FM.hasDerivAt_L12` supplies).

**Why `z ≥ 0` and not all of `ℝ`.**  The additivity of `L₁₂` and of `FK` over `F = F_* + g` is false for
`z < 0` (`Pieces/NOTES_L12FK_add_FALSE.md`: the `L₁₂`-density of `F_*` has a non-integrable pole
at `s = -1`, and `GalClass` constrains `g` only on the paper's domain `z ≥ 0`).  Every split
identity here is evaluated on the open quadrant, so the restricted additivity `L12FK_add_ge0` is
exactly what is needed.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0

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

/-! ## Pointwise congruence of the operators `ℛ`, `U`, `V`

These are the elementary fact that the three operators depend on their argument only through the
value and the two first partials at the point.  They let one replace the argument by an
expression that agrees with it *at the point in question* for `ℛ, U, V` (the derivative
congruences are supplied by the caller). -/

theorem Rop_congr_pt {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Ψ z θ = Ψ' z θ) (hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ)
    (hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ) :
    Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ' z θ := by
  simp only [Work.Construction.Rop, h, hpz, hpth]

theorem Uop_congr_pt {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Ψ z θ = Ψ' z θ) (hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ) :
    Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ' z θ := by
  simp only [Work.Construction.Uop, h, hpz]

theorem Vop_congr_pt {Ψ Ψ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Ψ z θ = Ψ' z θ) (hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ) :
    Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ' z θ := by
  simp only [Work.Construction.Vop, h, hpth]

/-! ## The straightened stream function of `F = F_* + g` splits, on `z ≥ 0` -/

theorem PhiTil_add_ge0 {α : ℝ} {g Φs Φg : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.Nonlin.GalClass α g) :
    ∀ z θ, 0 ≤ z →
      Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ := by
  intro z θ hz
  have hL := (L12FK_add_ge0 hα hα1 hg).1 z hz
  simp only [Work.Construction.PhiTil, Work.Construction.Theta]
  rw [hL]
  ring

/-! ## The three splits -/

theorem splits_of_ctx {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ} {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} (h : Work.FTS.Nonlin.RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : (∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ + Work.FTS.Nonlin.N06F α g z θ)) ∧ (∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ) + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ) + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ) + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ)) ∧ (∀ μ : ℝ, μ ≠ -1 → ∀ z θ, Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = Work.FTS.Nonlin.NstarLam μ g z θ) := by
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hg : Work.FTS.Nonlin.GalClass α g := h.hg
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := h.reg4
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg4.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg4.2.1
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  have hΦs : Work.FTS.LocData.SmoothQuad Φs := h.hs.smooth
  have hΦg : Work.FTS.LocData.SmoothQuad Φg := h.hell.smooth
  have hadd := L12FK_add_ge0 hα hα1 hg
  have hFK : ∀ z : ℝ, 0 ≤ z → Work.Construction.FK (Work.Construction.Ftot α g) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z :=
    hadd.2
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => h.hN.l12diff α ⟨hα, h.hαα₂⟩ g hsq hmem z hz
  refine ⟨?_, ?_, ?_⟩
  · -- ## the split of `N₀`
    intro z θ hq
    have hz : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; exact lt_trans (by norm_num) hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      pth_add_of_smoothQuad hF hsq hz hθ
    have hDz : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
      Dz_add_of_diff (pz_add_of_smoothQuad hF hsq hz hθ)
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
    have hz0 : (0 : ℝ) < z := hq.1
    have hz : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
    have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
      pth_add_of_smoothQuad hF hsq hz hθ
    have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
      Dz_add_of_diff (pz_add_of_smoothQuad hF hsq hz hθ)
    -- the structural identity of the two straightened stream functions, on `z ≥ 0`
    have hpt : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ :=
      PhiTil_add_ge0 hα hα1 hg z θ hz0.le
    have hslice : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ')
        = fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ' :=
      funext fun θ' => PhiTil_add_ge0 hα hα1 hg z θ' hz0.le
    have hzslice : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z' θ)
        =ᶠ[𝓝 z] fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
      exact PhiTil_add_ge0 hα hα1 hg z' θ hz'.le
    -- the explicit form of the two pieces
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
          (differentiableAt_L12_Fstar hα hα1 hz0))
    have hzs2 : DifferentiableAt ℝ
        (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
      rw [hPsi2]
      exact (differentiableAt_slice_z hΦg hz hθ).sub
        ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
          (hL12 z hz0))
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
    -- additivity of `∂_z` and `∂_θ` on the sum of the two pieces
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
    -- the same partials of the `F_tot`-piece agree with those of the sum
    have hpzPsi : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
            + Work.Construction.PhiTil α g Φg z θ) z θ := by
      simp only [Work.Spaces.pz]
      exact Filter.EventuallyEq.deriv_eq hzslice
    have hpthPsi : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
            + Work.Construction.PhiTil α g Φg z θ) z θ := by
      simp only [Work.Spaces.pth]
      rw [hslice]
    -- the three operator identities
    have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ := by
      rw [show Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ)) z θ
          = Work.Construction.Rop α (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g Φg z θ) z θ
          from Rop_congr_pt hpt hpzPsi hpthPsi]
      exact Rop_add_of_diff (α := α) hpz hpth
    have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
      rw [show Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ)) z θ
          = Work.Construction.Uop α (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g Φg z θ) z θ
          from Uop_congr_pt hpt hpzPsi]
      exact Uop_add_of_diff hpz
    have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
      rw [show Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ)) z θ
          = Work.Construction.Vop (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
              + Work.Construction.PhiTil α g Φg z θ) z θ
          from Vop_congr_pt hpt hpthPsi]
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
      rw [hFK z hz0.le, hpthF]
      ring
    have hN5 : Work.Construction.N5 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
          + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
      simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
        Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
      rw [hFK z hz0.le]
      ring
    rw [Work.Construction.N_eq_sum]
    simp only [Pi.add_apply, hN1, hN2, hN3, hN4, hN5]
    ring
  · -- ## the collapse of `N_*`
    intro μ hμ z θ
    have hμ' : (1 : ℝ) + μ ≠ 0 := by intro hh; exact hμ (by linarith)
    have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
      rw [Work.Construction.lamfun]
      field_simp
      ring
    simp only [Work.Construction.Nstar, Work.FTS.Nonlin.NstarLam, Work.Spaces.Dz]
    rw [hcoef]
    field_simp
    ring

end Work.FTS.Nonlinear.Pieces
