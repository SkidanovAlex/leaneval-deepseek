import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Pullback` — the pulled-back equation for `φ = u/ω`

In the logarithmic coordinates of `RXT.Defs`, the weight ratio `φ` satisfies

  `∂_τ φ = f − (a·∂_sφ + b·∂_ψφ + c·φ)`,

with `a = Vz`, `b = 2Vθ/sin 2θ`, `c = cs + 2Vz/(1+z) + α·c2m(θ)·b`, `f = σ/ω` — the content of
`phi_hasDerivAt_τ` below.  The ingredients are the two chain rules `phi_hasDerivAt_s`,
`phi_hasDerivAt_ψ` and the two algebraic relations `dz_relation`, `pth_relation` between the
partial derivatives of `u` and the components `dphi_s`, `dphi_ψ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false


/-- The `z`-slice of a `C¹` function on `dom S` is differentiable, with derivative `pz`. -/
theorem hasDerivAt_zslice {S : ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
    {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    HasDerivAt (fun z' : ℝ => U z' θ τ) (Work.Spaces.pz (fun z θ => U z θ τ) z θ) z := by
  have hslice : ContDiffOn ℝ 1 (fun z : ℝ => U z θ τ) (Set.Ioi (0:ℝ)) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ, τ)) (Set.Ioi (0:ℝ)) := by fun_prop
    have h2 : Set.MapsTo (fun z : ℝ => (z, θ, τ)) (Set.Ioi (0:ℝ)) (dom S) := by
      intro z hz
      exact ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩
    have := hU.comp h1 h2
    simpa [dom, Function.comp_def] using this
  have hd : DifferentiableWithinAt ℝ (fun z : ℝ => U z θ τ) (Set.Ioi (0:ℝ)) z :=
    hslice.differentiableOn one_ne_zero z hz
  have hd' : DifferentiableAt ℝ (fun z : ℝ => U z θ τ) z :=
    hd.differentiableAt (isOpen_Ioi.mem_nhds hz)
  simpa only [Work.Spaces.pz] using hd'.hasDerivAt

/-- The `θ`-slice of a `C¹` function on `dom S` is differentiable, with derivative `pth`. -/
theorem hasDerivAt_θslice {S : ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
    {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    HasDerivAt (fun θ' : ℝ => U z θ' τ) (Work.Spaces.pth (fun z θ => U z θ τ) z θ) θ := by
  have hslice : ContDiffOn ℝ 1 (fun θ' : ℝ => U z θ' τ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (fun θ' : ℝ => (z, θ', τ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
      fun_prop
    have h2 : Set.MapsTo (fun θ' : ℝ => (z, θ', τ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) (dom S) := by
      intro θ' hθ'
      exact ⟨hz, ⟨hθ'.1, hθ'.2⟩, hτ⟩
    have := hU.comp h1 h2
    simpa [dom, Function.comp_def] using this
  have hd : DifferentiableWithinAt ℝ (fun θ' : ℝ => U z θ' τ) (Set.Ioo (0:ℝ) (Real.pi / 2)) θ :=
    hslice.differentiableOn one_ne_zero θ ⟨hθ0, hθπ⟩
  have hd' : DifferentiableAt ℝ (fun θ' : ℝ => U z θ' τ) θ :=
    hd.differentiableAt (isOpen_Ioo.mem_nhds ⟨hθ0, hθπ⟩)
  simpa only [Work.Spaces.pth] using hd'.hasDerivAt

/-! ### The three derivative identities for `φ = u/ω` -/

/-- `D_z u = ω·(∂_sφ + 2φ/(1+z))` — the definition of `dphi_s` solved for `D_zu`. -/
theorem dz_relation {α : ℝ} {u : ℝ → ℝ → ℝ → ℝ} {s ψ τ : ℝ} (hω : om α s ψ ≠ 0) :
    cz s * Work.Spaces.pz (fun z θ => u z θ τ) (cz s) (cth ψ)
      = om α s ψ * (dphi_s α u s ψ τ + 2 * phi α u s ψ τ / (1 + cz s)) := by
  simp only [dphi_s, phi]
  field_simp
  ring

/-- `∂_θu = ω·((2/sin 2θ)·∂_ψφ + φ·2α·c2m θ/sin 2θ)` — the definition of `dphi_ψ` solved
for `∂_θu`. -/
theorem pth_relation {α : ℝ} {u : ℝ → ℝ → ℝ → ℝ} {s ψ τ : ℝ} (hω : om α s ψ ≠ 0)
    (hs : Real.sin (2 * cth ψ) ≠ 0) :
    Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ)
      = om α s ψ * (2 / Real.sin (2 * cth ψ) * dphi_ψ α u s ψ τ
          + phi α u s ψ τ * (2 * α * Work.Construction.c2m (cth ψ) / Real.sin (2 * cth ψ))) := by
  simp only [dphi_ψ, phi]
  field_simp
  ring

/-- **The `s`-derivative of the pulled-back unknown.** -/
theorem phi_hasDerivAt_s {α S : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S))
    (s ψ τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    HasDerivAt (fun s' => phi α u s' ψ τ) (dphi_s α u s ψ τ) s := by
  have hz : 0 < cz s := cz_pos s
  have hθ0 : 0 < cth ψ := cth_pos ψ
  have hθπ : cth ψ < Real.pi / 2 := cth_lt ψ
  have hslice := hasDerivAt_zslice (S := S) hu hz hθ0 hθπ hτ
  have hcomp : HasDerivAt (fun s' => u (cz s') (cth ψ) τ)
      (Work.Spaces.pz (fun z θ => u z θ τ) (cz s) (cth ψ) * cz s) s :=
    hslice.comp s (hasDerivAt_cz s)
  have hωz := (omega_facts α hα).2.1 (cz s) (cth ψ) hz hθ0 hθπ
  have hω : HasDerivAt (fun s' => om α s' ψ)
      (om α s ψ * (2 / (cz s * (1 + cz s))) * cz s) s := by
    have := hωz.comp s (hasDerivAt_cz s)
    simpa only [om, Function.comp_def] using this
  have hquot := hcomp.div hω (ne_of_gt (om_pos (α := α) hα))
  have key : (Work.Spaces.pz (fun z θ => u z θ τ) (cz s) (cth ψ) * cz s * om α s ψ
        - u (cz s) (cth ψ) τ * (om α s ψ * (2 / (cz s * (1 + cz s))) * cz s))
        / om α s ψ ^ 2 = dphi_s α u s ψ τ := by
    simp only [dphi_s, phi]
    field_simp
  exact hquot.congr_deriv key

/-- **The `ψ`-derivative of the pulled-back unknown.** -/
theorem phi_hasDerivAt_ψ {α S : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S))
    (s ψ τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    HasDerivAt (fun ψ' => phi α u s ψ' τ) (dphi_ψ α u s ψ τ) ψ := by
  have hz : 0 < cz s := cz_pos s
  have hθ0 : 0 < cth ψ := cth_pos ψ
  have hθπ : cth ψ < Real.pi / 2 := cth_lt ψ
  have hslice := hasDerivAt_θslice (S := S) hu hz hθ0 hθπ hτ
  have hcomp : HasDerivAt (fun ψ' => u (cz s) (cth ψ') τ)
      (Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ) * (Real.sin (2 * cth ψ) / 2)) ψ :=
    hslice.comp ψ (hasDerivAt_cth ψ)
  have hωθ := (omega_facts α hα).2.2 (cz s) (cth ψ) hz hθ0 hθπ
  have hω : HasDerivAt (fun ψ' => om α s ψ')
      (om α s ψ * (2 * α * Work.Construction.c2m (cth ψ) / Real.sin (2 * cth ψ))
        * (Real.sin (2 * cth ψ) / 2)) ψ := by
    have := hωθ.comp ψ (hasDerivAt_cth ψ)
    simpa only [om, Function.comp_def] using this
  have hquot := hcomp.div hω (ne_of_gt (om_pos (α := α) hα))
  have key : (Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ)
          * (Real.sin (2 * cth ψ) / 2) * om α s ψ
        - u (cz s) (cth ψ) τ * (om α s ψ * (2 * α * Work.Construction.c2m (cth ψ)
            / Real.sin (2 * cth ψ)) * (Real.sin (2 * cth ψ) / 2)))
        / om α s ψ ^ 2 = dphi_ψ α u s ψ τ := by
    have hs2 : Real.sin (2 * cth ψ) ≠ 0 := ne_of_gt (cth_sin_two_pos ψ)
    simp only [dphi_ψ, phi]
    field_simp
  exact hquot.congr_deriv key

/-- **The pulled-back equation.**  `∂_τφ = f − (a·∂_sφ + b·∂_ψφ + c·φ)`. -/
theorem phi_hasDerivAt_τ {α S : ℝ} (hα : 0 < α) {u Vz Vθ cs σ : ℝ → ℝ → ℝ → ℝ}
    (hEq : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => u z θ s)
        (σ z θ τ - (Vz z θ τ * Work.Spaces.Dz (fun z θ => u z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => u z θ τ) z θ + cs z θ τ * u z θ τ)) τ)
    (s ψ τ : ℝ) (hτ0 : 0 < τ) (hτS : τ ≤ S) :
    HasDerivAt (fun σ' => phi α u s ψ σ')
      (trF α σ s ψ τ - (trA Vz s ψ τ * dphi_s α u s ψ τ + trB Vθ s ψ τ * dphi_ψ α u s ψ τ
        + trC α Vz Vθ cs s ψ τ * phi α u s ψ τ)) τ := by
  have hz : 0 < cz s := cz_pos s
  have hθ0 : 0 < cth ψ := cth_pos ψ
  have hθπ : cth ψ < Real.pi / 2 := cth_lt ψ
  have hω : om α s ψ ≠ 0 := ne_of_gt (om_pos (α := α) hα)
  have hs2 : Real.sin (2 * cth ψ) ≠ 0 := ne_of_gt (cth_sin_two_pos ψ)
  have hraw := hEq (cz s) (cth ψ) τ hz hθ0 hθπ hτ0 hτS
  have hscale : HasDerivAt (fun σ' => u (cz s) (cth ψ) σ' / om α s ψ)
      ((σ (cz s) (cth ψ) τ - (Vz (cz s) (cth ψ) τ
            * Work.Spaces.Dz (fun z θ => u z θ τ) (cz s) (cth ψ)
          + Vθ (cz s) (cth ψ) τ * Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ)
          + cs (cz s) (cth ψ) τ * u (cz s) (cth ψ) τ)) / om α s ψ) τ :=
    hraw.div_const _
  have key : (σ (cz s) (cth ψ) τ - (Vz (cz s) (cth ψ) τ
          * Work.Spaces.Dz (fun z θ => u z θ τ) (cz s) (cth ψ)
        + Vθ (cz s) (cth ψ) τ * Work.Spaces.pth (fun z θ => u z θ τ) (cz s) (cth ψ)
        + cs (cz s) (cth ψ) τ * u (cz s) (cth ψ) τ)) / om α s ψ
      = trF α σ s ψ τ - (trA Vz s ψ τ * dphi_s α u s ψ τ + trB Vθ s ψ τ * dphi_ψ α u s ψ τ
        + trC α Vz Vθ cs s ψ τ * phi α u s ψ τ) := by
    rw [div_eq_iff hω]
    simp only [Work.Spaces.Dz]
    rw [dz_relation (α := α) hω, pth_relation (α := α) hω hs2]
    simp only [trA, trB, trC, trF, phi, dphi_s, dphi_ψ]
    field_simp
    ring
  have hfin := hscale.congr_deriv key
  have hfun : (fun σ' => phi α u s ψ σ') = fun σ' => u (cz s) (cth ψ) σ' / om α s ψ := rfl
  rw [hfun]
  exact hfin


end Work.FTS_RegExport.RXT
