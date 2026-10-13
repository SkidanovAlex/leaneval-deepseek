import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.HomClsSlotsZero
import Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_sub
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The slots of the packages depend only on the source** — the assembled form of the comparison
that the `EpsLocal` reduction (`EComparison.E_slots_diff_eq`) consumes.

`EComparison.EllPkgCls α Ce F Ψ` is the membership half of the packages `EllPkgGo`/`EllPkgK`
(`SmoothOpen Ψ`, `IsBslSol α F Ψ`, and `HQo α 6` of the three slots `SlotR/SlotU/SlotV` — the
modifications `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ)/sin 2θ`, `Vop (PhiTil α F Ψ)`).  The
assertion is that two elements of the class with the *same* source have the same slots **on the open
quadrant** `0 < z`, `θ ∈ (0, π/2)`.

The quadrant restriction is essential and was required by two reviews: `SmoothOpen` is smoothness on
`Q0 = (0,∞) × (0,π/2)` only, `IsBslSol` constrains the law only there, and `HkMem` integrates only
over `Iz × Iθ = [0,∞) × [0,π/2]`, so `EllPkgCls` is blind to the values of `Ψ` outside the closed
quadrant (a bump supported in `θ > π/2` is invisible to every hypothesis yet changes the slots).
Nothing is lost downstream: the slots are consumed only through `HkSq`/`HkMem`, whose integrands see
`z > 0`, `θ ∈ (0,π/2)` a.e. and vanish at `z = 0`.

Both ingredients are already proved in this workspace, `sorry`-free:
* `Work.FTS.StrongEps.EComparison.EllPkgCls_sub` — the class is closed under differences, so
  `(fun z θ => F z θ - F z θ, fun z θ => Ψ₁ z θ - Ψ₂ z θ)` is in the class (its `hΘ` hypothesis is
  discharged by `Theta α (fun z θ => F z θ - F z θ) = Theta α 0`, which follows from
  `L12dens`-congruence of the identically zero integrand plus
  `MeasureTheory.setIntegral_congr_fun`);
* `Work.FTS.StrongEps.EComparison.HomClsSlotsZero` — a *homogeneous* element of the class
  (`IsBslSol α 0 w`, `SmoothOpen w`, `HkMem α 6` of the three slots of `w`) has all three slots
  vanishing on the open quadrant.

The remaining formal step is the identification of the degenerate source `fun z θ => F z θ - F z θ`
with `fun _ _ => 0`: the pointwise law becomes `bslOp α (Ψ₁ - Ψ₂) = 0` by `sub_self`, the Dirichlet
and decay conjuncts are source-free, and `PhiTil α (F - F) (Ψ₁ - Ψ₂)` agrees with
`PhiTil α 0 (Ψ₁ - Ψ₂)` because `PhiTil α F' Ψ = Ψ - Theta α F'` and the two `Theta`s are equal. -/
theorem Slot_eq_of_source {α Ce : ℝ} {F Ψ₁ Ψ₂ : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (h₁ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F Ψ₁)
    (h₂ : Work.FTS.StrongEps.EComparison.EllPkgCls α Ce F Ψ₂) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotR α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotR α F Ψ₂ z θ) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotU α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotU α F Ψ₂ z θ) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
        Work.FTS.StrongEps.EComparison.SlotV α F Ψ₁ z θ
          = Work.FTS.StrongEps.EComparison.SlotV α F Ψ₂ z θ) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  -- ## The degenerate source `F - F` has vanishing `L₁₂` and `Θ`
  have hL12z : ∀ z, Work.Construction.L12 (fun z θ => F z θ - F z θ) z = 0 := by
    intro z
    have hfun : (fun z θ => F z θ - F z θ) = (fun _ _ => (0 : ℝ)) := by
      funext z θ
      ring
    rw [hfun]
    simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]
  have hThetaG : Work.Construction.Theta α (fun z θ => F z θ - F z θ) = fun _ _ => (0 : ℝ) := by
    funext z θ
    simp only [Work.Construction.Theta]
    rw [hL12z z]
    ring
  have hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F z θ - F z θ) z θ
        = Work.Construction.Theta α F z θ - Work.Construction.Theta α F z θ := by
    intro z _ θ
    rw [hThetaG]
    simp
  -- ## The difference lies in the class
  have hsub : EllPkgCls α Ce (fun z θ => F z θ - F z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) :=
    EllPkgCls_sub h₁ h₂ hΘ
  have hPhiTilG : Work.Construction.PhiTil α (fun z θ => F z θ - F z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) = fun z θ => Ψ₁ z θ - Ψ₂ z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, hThetaG, sub_zero]
  -- ## the hypotheses of `HomClsSlotsZero` for the stream function difference
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := hsub.1
  have hsol : Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
    refine ⟨?_, hsub.2.1.2.1, hsub.2.1.2.2.1, hsub.2.1.2.2.2⟩
    intro z hz θ h0 h1
    simpa using hsub.2.1.1 z hz θ h0 h1
  have hR : Work.Spaces.HkMem α 6
      (Work.Construction.Rop α (fun z θ => Ψ₁ z θ - Ψ₂ z θ)) := by
    simpa only [hPhiTilG] using hsub.2.2.1.2
  have hU : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.Uop α (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        / Work.Construction.s2 θ) := by
    simpa only [hPhiTilG] using hsub.2.2.2.1.2
  have hV : Work.Spaces.HkMem α 6
      (Work.Construction.Vop (fun z θ => Ψ₁ z θ - Ψ₂ z θ)) := by
    simpa only [hPhiTilG] using hsub.2.2.2.2.2
  -- ## all three slots of the difference vanish on the open quadrant
  obtain ⟨hRz, hUz, hVz⟩ :=
    HomClsSlotsZero (w := fun z θ => Ψ₁ z θ - Ψ₂ z θ) hα hα1 hsm hsol hR hU hV
  -- ## the slots of the two elements differ by the slots of the difference
  have hu : ∀ z, 0 < z → DifferentiableAt ℝ
      (fun z' => (1 / (4 * α)) * Work.Construction.L12 F z') z :=
    fun z hz => (differentiableAt_L12_of_Vop hαne h₁.1 h₁.2.2.2.2.1 hz).const_mul (1 / (4 * α))
  have hpz_sub : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α F Ψ₁) z θ
          - Work.Spaces.pz (Work.Construction.PhiTil α F Ψ₂) z θ := by
    intro z θ hz h0 h1
    rw [pz_sub h₁.1 h₂.1 hz h0 h1,
      pz_PhiTil_eq (F := F) (Ψ := Ψ₁) h₁.1 (hu z hz) hz h0 h1,
      pz_PhiTil_eq (F := F) (Ψ := Ψ₂) h₂.1 (hu z hz) hz h0 h1]
    ring
  have hpth_sub : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α F Ψ₁) z θ
          - Work.Spaces.pth (Work.Construction.PhiTil α F Ψ₂) z θ := by
    intro z θ hz h0 h1
    rw [pth_sub h₁.1 h₂.1 hz h0 h1,
      pth_PhiTil_eq (F := F) (Ψ := Ψ₁) h₁.1 hz h0 h1,
      pth_PhiTil_eq (F := F) (Ψ := Ψ₂) h₂.1 hz h0 h1]
    ring
  have hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Construction.PhiTil α F Ψ₁ z θ - Work.Construction.PhiTil α F Ψ₂ z θ := by
    intro z θ _ _ _
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    ring
  obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := α)
    (A := fun z θ => Ψ₁ z θ - Ψ₂ z θ)
    (P₁ := Work.Construction.PhiTil α F Ψ₁)
    (P₂ := Work.Construction.PhiTil α F Ψ₂) hval hpz_sub hpth_sub
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    have h := hsR z θ hz hθ.1 hθ.2
    have h0 := hRz z hz θ hθ
    simp only [SlotR]
    linarith
  · intro z hz θ hθ
    have h := hsU z θ hz hθ.1 hθ.2
    have h0 := hUz z hz θ hθ
    have hUeq : Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ₁) z θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ₂) z θ := by linarith
    simp only [SlotU]
    rw [hUeq]
  · intro z hz θ hθ
    have h := hsV z θ hz hθ.1 hθ.2
    have h0 := hVz z hz θ hθ
    simp only [SlotV]
    linarith

end Work.FTS.StrongEps.EComparison
