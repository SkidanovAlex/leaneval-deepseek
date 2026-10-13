/-
# `Work.FTS_RegExport.RXR5L.DthFtau_C1Jet` — the `D_θ`-slot of the `F(τ) = F_* + g̃(τ)` family

The target is the `D_θ`-constituent of the R5 package at the fake-time family
`F(τ) = F_* + g̃(τ)`, `g̃ = gS α (tauExt g) = SG α g`:

`C1Jet α S N₅ (fun z θ τ => D_θ (F(τ)) z θ)`,

from the already available slots `C1Jet α S N₃ (D_θ g̃)` (`hO1`, the requester's hypothesis,
which additionally carries the `D_z g̃`-slot) and the *static* slot
`C1Jet α S Nf (D_θ F_*)` (`RXR5.C1Jet_Dth_Fstar`).

The whole content is the split

`D_θ(F_* + g̃(τ)) = D_θ F_* + D_θ g̃(τ)`,

which is `D_θ`-additivity at the point `(z,θ)`.  Since `D_θ f = sin(2θ)·∂_θ f`, the identity is
trivial whenever `sin(2θ) = 0` (both sides are `0`), and on the open quadrant `Q0` it is
`deriv_add` applied to the two `θ`-slices, which are differentiable there:

* `θ' ↦ F_*(z,θ')` = `α·(Γ(θ')/c)·z/(1+z)²` is differentiable because
  `Γ(θ') = (sin θ' cos²θ')^{β/3}` is (`HasDerivAt.rpow_const`, the base `sin θ' cos²θ'` being
  strictly positive in the open interval) — `differentiableAt_Gam`, `differentiableAt_Fstar_slice`;
* `θ' ↦ g̃(τ)(z,θ')` agrees near `θ` with the slice `θ' ↦ slice g τ z θ'`, which is
  differentiable at `(z,θ) ∈ Q0` by `RegPkgMin.c4` (`differentiableAt_SG_slice`).

The remaining cases `z = 0` (both slices vanish identically) and `sin(2θ) = 0` are handled
directly.  The transport of `C1Jet` along the resulting pointwise identity is
`RegPkgGal.C1Jet.congr` and the addition is `RegPkgGal.C1Jet.add`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §1  Differentiability of the two `θ`-slices on the open quadrant -/

/-- `Γ(θ') = (sin θ' · cos²θ')^{β/3}` is differentiable at every interior point of the angular
interval (no constraint on the exponent `β`: only the strict positivity of the base is used). -/
theorem differentiableAt_Gam {β θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam β θ') θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hpos : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hφ : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  simpa only [Work.Spaces.Gam] using
    (hφ.rpow_const (p := β / 3) (Or.inl hpos)).differentiableAt

/-- The `θ`-slice of the static profile `F_*` is differentiable on the open angular interval. -/
theorem differentiableAt_Fstar_slice {β z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar β z θ') θ := by
  have hG : DifferentiableAt ℝ
      (fun θ' : ℝ => β * (Work.Spaces.Gam β θ' / Work.Spaces.c β) * Work.FM.Fstar z) θ :=
    (((differentiableAt_Gam (β := β) hθ0 hθ2).div_const (Work.Spaces.c β)).const_mul β).mul_const
      (Work.FM.Fstar z)
  simpa only [Work.Construction.Fstar] using hG

/-- The `θ`-slice of `SG α g (·,·,τ)` is differentiable at every point of the open quadrant, as
soon as the `τ`-slice `slice g τ` is `C⁴` there.  Near `θ` the sanitised family `SG α g` agrees
with `tauExt g`, which for `τ ≥ 0` agrees with `g`, i.e. with the slice. -/
theorem differentiableAt_SG_slice {α τ z θ : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hc4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    (hτ : 0 ≤ τ) (hz : 0 < z) (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.FTS_RegExport.RXR5.SG α g z θ' τ) θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ0, hθ2⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, θ) :=
    (hc4.differentiableOn (by norm_num)).differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hslice : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ :=
    Work.Spaces.differentiableAt_curry_right hdiff
  refine hslice.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ2⟩] with θ' hθ'
  simp only [Work.FTS.Galerkin.slice]
  rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ'.1.le hθ'.2.le,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- `deriv` of a function that is pointwise zero vanishes. -/
theorem deriv_of_eq_zero {f : ℝ → ℝ} (h : f = fun _ => (0 : ℝ)) (x : ℝ) : deriv f x = 0 := by
  rw [h]; exact deriv_const x 0

/-! ## §2  The pointwise split `D_θ(F_* + g̃) = D_θF_* + D_θg̃` on the strip -/

/-- **The `D_θ`-split on the strip.**  For `z ≥ 0`, `θ ∈ [0,π/2]`, `τ ∈ [0,S]`,

`D_θ F_* z θ + D_θ(g̃(τ)) z θ = D_θ(F_* + g̃(τ)) z θ`,

where `g̃ = SG α g`.  Off the open quadrant (`z = 0`, or `sin(2θ) = 0`) all three `D_θ`'s vanish;
on the open quadrant this is `deriv_add` for the two `θ`-slices. -/
theorem Dth_Ftau_eq_strip {α S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0)
    {z θ τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      + Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ
    = Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS_RegExport.RXR5.SG α g) τ z θ) z θ := by
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.Ftau]
  rcases eq_or_lt_of_le hz with hz0 | hzp
  · -- `z = 0`: both slices vanish identically, hence all three `D_θ`'s vanish
    subst hz0
    have hF : ∀ θ' : ℝ, Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ' = 0 :=
      fun θ' => by simp [Work.Construction.Fstar, Work.FM.Fstar]
    have hH : ∀ θ' : ℝ, Work.FTS_RegExport.RXR5.SG α g 0 θ' τ = 0 :=
      fun θ' => Work.FTS_RegExport.RXR5.SG_apply_of_nonpos le_rfl
    rw [show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ')
          = fun _ => (0 : ℝ) from funext hF,
      show (fun θ' : ℝ => Work.FTS_RegExport.RXR5.SG α g 0 θ' τ) = fun _ => (0 : ℝ)
          from funext hH,
      show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) 0 θ'
            + Work.FTS_RegExport.RXR5.SG α g 0 θ' τ) = fun _ => (0 : ℝ) from
        funext (fun θ' => by rw [hF θ', hH θ', zero_add])]
    simp
  · by_cases hs : Real.sin (2 * θ) = 0
    · -- `sin(2θ) = 0`: all three `D_θ`'s vanish
      rw [hs]
      ring
    · -- the open quadrant: `deriv_add` on the two slices
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact absurd (by rw [← h]; simp) hs
        · exact h
      have hθ2 : θ < π / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exact absurd (by
            rw [h]
            have h2 : 2 * (π / 2) = π := by ring
            rw [h2, Real.sin_pi]) hs
      have hdF : DifferentiableAt ℝ
          (fun θ' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ') θ :=
        differentiableAt_Fstar_slice hθ0 hθ2
      have hdH : DifferentiableAt ℝ
          (fun θ' => Work.FTS_RegExport.RXR5.SG α g z θ' τ) θ :=
        differentiableAt_SG_slice (hc4 τ hτ.1) hτ.1 hzp hθ0 hθ2
      rw [show (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ'
            + Work.FTS_RegExport.RXR5.SG α g z θ' τ)
          = (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ')
            + (fun θ' : ℝ => Work.FTS_RegExport.RXR5.SG α g z θ' τ) from rfl,
        deriv_add hdF hdH]
      ring

/-! ## §3  The target -/

theorem DthFtau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₅ : ℝ, 0 ≤ N₅ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₅
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) := by
  obtain ⟨N₂, N₃, hN₂0, hN₃0, _hDzSG, hDthSG⟩ := hO1
  obtain ⟨Nf, hNf0, hDthFstar⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_Dth_Fstar (α := α) (S := S) hα hα13
  refine ⟨Nf + N₃, add_nonneg hNf0 hN₃0, ?_⟩
  refine Work.FTS.RegPkgGal.C1Jet.congr
    (Work.FTS.RegPkgGal.C1Jet.add hDthFstar hDthSG) ?_
  intro z θ τ hz hθ hτ
  exact Dth_Ftau_eq_strip (α := α) (S := S) (g := g)
    (fun τ hτ => hOK.1.1.c4 τ hτ) hτ hz hθ

end Work.FTS_RegExport.RXR5L
