import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.L12_Fstar_add_c4
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_EllLimOK.Locality
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The split of the target's stream function (part of `velVanish2`)

On the open quadrant the target's residual `Φ̃ = PhiTil (Ftau (GR g) τ) (slice (ΦR Φs E g) τ)`
splits as the star residual `Φ̃_*` plus the perturbation residual `Φ̃_pert`, and the three
transport slots `Rop`, `Vop`, `Uop/sin 2θ` are additive to first order; this module carries the
identifications (`RXR5.Basic`), the `L₁₂`-linearity step (`L12_Fstar_add_c4`), the `D_z`/`D_θ`
additivity (`deriv_add`) and the generic closing step `v2_slot_bound_of_split`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The three stream functions and the three slots, as transparent abbreviations -/

/-- The residual of the modulated stream function (the object of the target). -/
abbrev v2_PhiT (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ)
    (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ

/-- The star residual `Φ̃_*`. -/
abbrev v2_PhiStar (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
    (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs z θ

/-- The perturbation residual `Φ̃_pert`. -/
abbrev v2_PhiPert (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
    (E (slice g τ)) z θ

/-- The `ℛ`-slot. -/
abbrev v2_SlotR (α : ℝ) (Ψ : Fn) : Fn := Work.Construction.Rop (Work.FTS.Regularity.pExp α) Ψ

/-- The `𝒱`-slot. -/
abbrev v2_SlotV (α : ℝ) (Ψ : Fn) : Fn := Work.Construction.Vop Ψ

/-- The `𝒰/sin 2θ`-slot. -/
abbrev v2_SlotU (α : ℝ) (Ψ : Fn) : Fn := fun z θ =>
  Work.Construction.Uop (Work.FTS.Regularity.pExp α) Ψ z θ / Real.sin (2 * θ)



/-! ## The split of the target's stream function

On the open quadrant the target's residual `PhiTil (Ftau (GR g) τ) (slice (ΦR Φs E g) τ)` is the
star residual plus the perturbation residual.  The only non-trivial ingredient is the linearity of
`L₁₂` over `F_* + u` (`L12_Fstar_add_c4`, from the child module), the rest is the identification of
the sanitised objects with the canonical ones (`RXR5.Basic`). -/

theorem v2_slice_PhiR_eq {αG : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice (Work.FTS.RegExportIface.RXT.ΦR αG Φs E g) τ z θ
        = Φs z θ + E (slice g τ) z θ := by
  intro z θ hz hθ hθ2
  have h1 : slice (Work.FTS.RegExportIface.RXT.ΦR αG Φs E g) τ z θ
      = slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g)) τ z θ :=
    Work.FTS_RegExport.RXR5.SΨ_slice_agreeOnQ αG Φs E g τ z θ hz hθ hθ2
  rw [h1, Work.FTS.Galerkin.slice_apply, Work.FTS.Nonlin.PsiCan,
    Work.FTS.FinalV2.slice_tauExt g hτ]

theorem v2_L12_Ftau_eq {α C₀ : ℝ} (hα : 0 < α)
    (hα1 : Work.FTS.Regularity.pExp α ≤ 1) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    {g : Fam} (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z
      = Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        + Work.Construction.L12 (slice g τ) z := by
  have hmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  have hag : Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice g τ z θ) := by
    intro z θ hz hθ hθ2
    show Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
      = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice g τ z θ
    rw [show slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ = slice g τ z θ from by
      rw [Work.FTS.Galerkin.slice_apply, Work.FTS.Galerkin.slice_apply]
      exact Work.FTS_RegExport.RXR5.SG_apply_of_pos (α := α) (g := g) hz hθ.le hθ2.le |>.trans
        (Work.FTS.FinalV2.tauExt_of_nonneg g hτ)]
  rw [Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ hag hz]
  exact Work.FTS_RegExport.RXT.L12_Fstar_add_c4 (α := Work.FTS.Regularity.pExp α)
    (Work.FTS.Regularity.pExp_pos hα) hα1 h4 hmem hz

theorem v2_phiTil_split {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}
    {g : Fam} (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ z θ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ)
          (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ
        = Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) Φs z θ
          + Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
              (E (slice g τ)) z θ := by
  intro z θ hzθ
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hpE : Work.FTS.Regularity.pExp α ≤ 1 := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hL := v2_L12_Ftau_eq hα hpE hOK hτ hz.le
  have hΦ := v2_slice_PhiR_eq (αG := α) (Φs := Φs) (E := E) (g := g) hτ z θ hz hθ hθ2
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, hL, hΦ]
  ring_nf

/-! ## Additivity of the three slots at a point of the quadrant -/

theorem v2_slice_diff_z {f : Fn} (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun z' => f z' θ) z := by
  have h1 : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
      (by norm_num)
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  exact h1.comp z h2

theorem v2_slice_diff_θ {f : Fn} (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have h1 : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt
      (by norm_num)
  have h2 : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact h1.comp θ h2

theorem v2_pz_add_at {f g : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pz (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pz f z θ + Work.Spaces.pz g z θ := by
  show deriv (fun z' => f z' θ + g z' θ) z
      = deriv (fun z' => f z' θ) z + deriv (fun z' => g z' θ) z
  rw [show (fun z' => f z' θ + g z' θ)
      = ((fun z' => f z' θ) + (fun z' => g z' θ)) from rfl,
    deriv_add (v2_slice_diff_z hf hzθ) (v2_slice_diff_z hg hzθ)]

theorem v2_pth_add_at {f g : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  show deriv (fun θ' => f z θ' + g z θ') θ
      = deriv (fun θ' => f z θ') θ + deriv (fun θ' => g z θ') θ
  rw [show (fun θ' => f z θ' + g z θ')
      = ((fun θ' => f z θ') + (fun θ' => g z θ')) from rfl,
    deriv_add (v2_slice_diff_θ hf hzθ) (v2_slice_diff_θ hg hzθ)]

theorem v2_rop_add_at {αG : ℝ} {f g : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Construction.Rop αG (fun z θ => f z θ + g z θ) z θ
      = Work.Construction.Rop αG f z θ + Work.Construction.Rop αG g z θ := by
  simp only [Work.Construction.Rop, v2_pz_add_at hf hg hzθ, v2_pth_add_at hf hg hzθ]
  ring

theorem v2_vop_add_at {f g : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Construction.Vop (fun z θ => f z θ + g z θ) z θ
      = Work.Construction.Vop f z θ + Work.Construction.Vop g z θ := by
  simp only [Work.Construction.Vop, v2_pth_add_at hf hg hzθ]
  ring

theorem v2_uop_div_add_at {αG : ℝ} {f g : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    (Work.Construction.Uop αG (fun z θ => f z θ + g z θ) z θ / Real.sin (2 * θ))
      = (Work.Construction.Uop αG f z θ / Real.sin (2 * θ))
        + (Work.Construction.Uop αG g z θ / Real.sin (2 * θ)) := by
  simp only [Work.Construction.Uop, v2_pz_add_at hf hg hzθ]
  ring

/-- The generic splitting tool: a slot that decomposes on `Q0` into two `C²` pieces has its
mixed derivatives split. -/
theorem v2_mixed_slot_split {A A₁ A₂ : Fn}
    (heq : Set.EqOn (Function.uncurry A) (Function.uncurry (A₁ + A₂))
      Work.FTS.EllipticEst.Q0)
    (h₁ : ContDiffOn ℝ 2 (Function.uncurry A₁) Work.FTS.EllipticEst.Q0)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry A₂) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) (j i : ℕ) (hji : j + i ≤ 2) :
    |Work.Spaces.mixed j i A z θ|
      ≤ |Work.Spaces.mixed j i A₁ z θ| + |Work.Spaces.mixed j i A₂ z θ| := by
  rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 heq hzθ j i,
    Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn (n := 2)
      Work.FTS.EllipticEst.isOpen_Q0 h₁ h₂ i j (by omega) ⟨z, θ⟩ hzθ]
  exact abs_add_le _ _

/-! ## The assembly -/

/-- The generic closing step: a slot that splits on `Q0` into two `C²` pieces, each satisfying a
`min z 1`-bound, satisfies the sum of the two bounds. -/
theorem v2_slot_bound_of_split {A A₁ A₂ : Fn} {M₁ M₂ : ℝ}
    (heq : Set.EqOn (Function.uncurry A) (Function.uncurry (A₁ + A₂))
      Work.FTS.EllipticEst.Q0)
    (h₁ : ContDiffOn ℝ 2 (Function.uncurry A₁) Work.FTS.EllipticEst.Q0)
    (h₂ : ContDiffOn ℝ 2 (Function.uncurry A₂) Work.FTS.EllipticEst.Q0)
    (hb₁ : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A₁ z θ| ≤ M₁ * min z 1)
    (hb₂ : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A₂ z θ| ≤ M₂ * min z 1) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ (M₁ + M₂) * min z 1 := by
  intro j i hji z θ hz hθ hθ2
  have h := v2_mixed_slot_split heq h₁ h₂ ⟨hz, hθ, hθ2⟩ j i hji
  have hsum := add_le_add (hb₁ j i hji z θ hz hθ hθ2) (hb₂ j i hji z θ hz hθ hθ2)
  calc |Work.Spaces.mixed j i A z θ|
      ≤ |Work.Spaces.mixed j i A₁ z θ| + |Work.Spaces.mixed j i A₂ z θ| := h
    _ ≤ M₁ * min z 1 + M₂ * min z 1 := hsum
    _ = (M₁ + M₂) * min z 1 := by ring


end Work.FTS_RegExport.RXT
