import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.Defs
import Submission.Work.FTS_RegExport.RXT.Pullback

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Continuity` — joint continuity of `φ` and of its spatial derivatives

The cone maximum principle consumes `φ`, `∂_sφ`, `∂_ψφ` as continuous functions on the slab
`ℝ² × [0,S]`.  Since `u` is only assumed `C¹` on `(0,∞) × (0,π/2) × [0,S]` (a set which is
open in the first two variables but *closed* in `τ`), the joint continuity of the partial
derivatives is extracted from `ContDiffOn` through the bundled Fréchet derivative
`fderivWithin` on the slab (`fderivWithin_eq_pz`, `fderivWithin_eq_pth`), which is continuous
on a `UniqueDiffOn` set.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

theorem continuous_cz : Continuous cz := Real.continuous_exp

theorem continuous_cth : Continuous cth := Real.continuous_arctan.comp Real.continuous_exp

/-- The identification of the Fréchet derivative of the uncurried slab function with the
`z`-partial derivative. -/
theorem fderivWithin_eq_pz {S : ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
    {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) (z, θ, τ) (1, (0, 0))
      = Work.Spaces.pz (fun z θ => U z θ τ) z θ := by
  have hp : (z, θ, τ) ∈ dom S := ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩
  have hdiff : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2)
      (dom S) (z, θ, τ) := hU.differentiableOn one_ne_zero (z, θ, τ) hp
  have hfd := hdiff.hasFDerivWithinAt
  have hγ : HasFDerivWithinAt (fun z' : ℝ => (z', (θ, τ)))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] (ℝ × ℝ))) (Set.Ioi (0:ℝ)) z :=
    (hasFDerivWithinAt_id z _).prodMk (hasFDerivWithinAt_const (θ, τ) z _)
  have hmaps : Set.MapsTo (fun z' : ℝ => (z', (θ, τ))) (Set.Ioi (0:ℝ)) (dom S) := by
    intro z' hz'
    exact ⟨hz', ⟨hθ0, hθπ⟩, hτ⟩
  have hcomp := hfd.comp_hasDerivWithinAt z hγ.hasDerivWithinAt hmaps
  have h2 := hcomp.hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hval : ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] (ℝ × ℝ))) 1 = (1, (0, 0)) := by
    rw [ContinuousLinearMap.prod_apply]
    rfl
  rw [hval] at h2
  have hderiv : deriv (fun z' : ℝ => U z' θ τ) z
      = fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) (z, θ, τ) (1, (0, 0)) :=
    h2.deriv
  rw [← hderiv]
  rfl

/-- The identification of the Fréchet derivative of the uncurried slab function with the
`θ`-partial derivative. -/
theorem fderivWithin_eq_pth {S : ℝ} {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
    {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) :
    fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) (z, θ, τ) (0, (1, 0))
      = Work.Spaces.pth (fun z θ => U z θ τ) z θ := by
  have hp : (z, θ, τ) ∈ dom S := ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩
  have hdiff : DifferentiableWithinAt ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2)
      (dom S) (z, θ, τ) := hU.differentiableOn one_ne_zero (z, θ, τ) hp
  have hfd := hdiff.hasFDerivWithinAt
  have hγ : HasFDerivWithinAt (fun θ' : ℝ => (z, (θ', τ)))
      ((0 : ℝ →L[ℝ] ℝ).prod ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)))
      (Set.Ioo (0:ℝ) (Real.pi / 2)) θ :=
    (hasFDerivWithinAt_const z θ _).prodMk
      ((hasFDerivWithinAt_id θ _).prodMk (hasFDerivWithinAt_const τ θ _))
  have hmaps : Set.MapsTo (fun θ' : ℝ => (z, (θ', τ))) (Set.Ioo (0:ℝ) (Real.pi / 2)) (dom S) := by
    intro θ' hθ'
    exact ⟨hz, ⟨hθ'.1, hθ'.2⟩, hτ⟩
  have hcomp := hfd.comp_hasDerivWithinAt θ hγ.hasDerivWithinAt hmaps
  have h2 := hcomp.hasDerivAt (isOpen_Ioo.mem_nhds ⟨hθ0, hθπ⟩)
  have hval : ((0 : ℝ →L[ℝ] ℝ).prod ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) 1 = (0, (1, 0)) := by
    rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply]
    rfl
  rw [hval] at h2
  have hderiv : deriv (fun θ' : ℝ => U z θ' τ) θ
      = fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) (z, θ, τ) (0, (1, 0)) :=
    h2.deriv
  rw [← hderiv]
  rfl

/-- Joint continuity of the `z`-partial derivative on the slab. -/
theorem pz_continuousOn {S : ℝ} (hS : 0 < S) {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.pz (fun z θ => U z θ p.2.2) p.1 p.2.1)
      (dom S) := by
  have hD : UniqueDiffOn ℝ (dom S) := by
    rw [dom]
    exact UniqueDiffOn.prod (uniqueDiffOn_Ioi 0)
      (UniqueDiffOn.prod (uniqueDiffOn_Ioo 0 (Real.pi / 2)) (uniqueDiffOn_Icc hS))
  have h1 : ContinuousOn (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
      (dom S) := hU.continuousOn_fderivWithin hD (by norm_num)
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) p (1, (0, 0))) (dom S) :=
    h1.clm_apply continuousOn_const
  refine h2.congr ?_
  intro p hp
  obtain ⟨z, θ, τ⟩ := p
  obtain ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩ := hp
  exact (fderivWithin_eq_pz hU hz hθ0 hθπ hτ).symm

/-- Joint continuity of the `θ`-partial derivative on the slab. -/
theorem pth_continuousOn {S : ℝ} (hS : 0 < S) {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.pth (fun z θ => U z θ p.2.2) p.1 p.2.1)
      (dom S) := by
  have hD : UniqueDiffOn ℝ (dom S) := by
    rw [dom]
    exact UniqueDiffOn.prod (uniqueDiffOn_Ioi 0)
      (UniqueDiffOn.prod (uniqueDiffOn_Ioo 0 (Real.pi / 2)) (uniqueDiffOn_Icc hS))
  have h1 : ContinuousOn (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S))
      (dom S) := hU.continuousOn_fderivWithin hD (by norm_num)
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => U p.1 p.2.1 p.2.2) (dom S) p (0, (1, 0))) (dom S) :=
    h1.clm_apply continuousOn_const
  refine h2.congr ?_
  intro p hp
  obtain ⟨z, θ, τ⟩ := p
  obtain ⟨hz, ⟨hθ0, hθπ⟩, hτ⟩ := hp
  exact (fderivWithin_eq_pth hU hz hθ0 hθπ hτ).symm

/-! ### Joint continuity of the pulled-back quantities -/

/-- The coordinate map `(s,ψ,τ) ↦ (eˢ, arctan e^ψ, τ)` lands in the slab. -/
theorem mapsTo_coords {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) (dom S) := by
  intro p hp
  obtain ⟨s, ψ, τ⟩ := p
  obtain ⟨-, ⟨-, hτ⟩⟩ := hp
  exact ⟨cz_pos s, ⟨cth_pos ψ, cth_lt ψ⟩, hτ⟩

theorem continuousOn_coords {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  ((continuous_cz.comp continuous_fst).continuousOn).prodMk
    (((continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn).prodMk
      (continuous_snd.comp continuous_snd).continuousOn)

/-- `p ↦ u (e^{p.1}) (arctan e^{p.2.1}) p.2.2` is continuous on the slab. -/
theorem continuousOn_u_comp {S : ℝ} {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => u (cz p.1) (cth p.2.1) p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h := hu.continuousOn.comp continuousOn_coords mapsTo_coords
  simpa [Function.comp_def] using h

theorem continuousOn_omega {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.RegExportIface.ω α q.1 q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
  have hz : ContinuousOn (fun q : ℝ × ℝ => q.1) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    continuous_fst.continuousOn
  have hθ : ContinuousOn (fun q : ℝ × ℝ => q.2) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    continuous_snd.continuousOn
  have hbase : ContinuousOn (fun q : ℝ × ℝ => Real.sin q.2 * Real.cos q.2 ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) :=
    ((Real.continuous_sin.comp continuous_snd).continuousOn).mul
      (((Real.continuous_cos.comp continuous_snd).continuousOn).pow 2)
  have hΓ : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.Regularity.Gamma α q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    have h := hbase.rpow_const (fun q _ => Or.inr hα.le)
    simpa [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma] using h
  have hnum : ContinuousOn
      (fun q : ℝ × ℝ => q.1 ^ 2 * Work.FTS.Regularity.Gamma α q.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := (hz.pow 2).mul hΓ
  have hden : ContinuousOn (fun q : ℝ × ℝ => (1 + q.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := (continuousOn_const.add hz).pow 2
  refine (hnum.div hden (fun q hq => by
    have h1 : (0:ℝ) < q.1 := hq.1
    exact ne_of_gt (pow_pos (by linarith) 2))).congr ?_
  intro q hq
  simp only [Work.FTS.RegExportIface.ω, Pi.div_apply, div_eq_mul_inv]

theorem continuousOn_om {α S : ℝ} (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => om α p.1 p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have hcoords : ContinuousOn (fun p : ℝ × ℝ × ℝ => (cz p.1, cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    ((continuous_cz.comp continuous_fst).continuousOn).prodMk
      ((continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn)
  have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (cz p.1, cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    intro p hp
    exact ⟨cz_pos _, cth_pos _⟩
  have h := (continuousOn_omega hα).comp hcoords hmap
  simpa [om, Function.comp_def] using h

theorem phi_continuous {α S : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => phi α u p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  refine (continuousOn_u_comp hu).div (continuousOn_om (S := S) hα) ?_
  intro p hp
  obtain ⟨s, ψ, τ⟩ := p
  exact ne_of_gt (om_pos (α := α) hα)

/-- Joint continuity of `p ↦ pz (u · · p.2.2) (e^{p.1}) (arctan e^{p.2.1})`. -/
theorem pz_comp_continuous {S : ℝ} (hS : 0 < S) {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pz (fun z θ => u z θ p.2.2) (cz p.1) (cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h := (pz_continuousOn hS hu).comp (continuousOn_coords (S := S)) (mapsTo_coords (S := S))
  simpa [dom, Function.comp_def] using h

/-- Joint continuity of `p ↦ pth (u · · p.2.2) (e^{p.1}) (arctan e^{p.2.1})`. -/
theorem pth_comp_continuous {S : ℝ} (hS : 0 < S) {u : ℝ → ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => u z θ p.2.2) (cz p.1) (cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h := (pth_continuousOn hS hu).comp (continuousOn_coords (S := S)) (mapsTo_coords (S := S))
  simpa [dom, Function.comp_def] using h

theorem continuousOn_cz {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => cz p.1) (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  (continuous_cz.comp continuous_fst).continuousOn

theorem continuousOn_cth {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => cth p.2.1) (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  (continuous_cth.comp (continuous_fst.comp continuous_snd)).continuousOn

theorem continuousOn_c2m_comp {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Construction.c2m (cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h2θ : ContinuousOn (fun p : ℝ × ℝ × ℝ => 2 * cth p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ × ℝ => (2:ℝ)) _).mul (continuousOn_cth (S := S))
  have hcos := Real.continuous_cos.comp_continuousOn h2θ
  have hsin := Real.continuous_sin.comp_continuousOn (continuousOn_cth (S := S))
  have h := hcos.sub (hsin.pow 2)
  convert h using 1
  ext p
  simp only [Pi.sub_apply, Pi.pow_apply, Function.comp_def, Work.Construction.c2m]

theorem continuousOn_sin_two_cth {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Real.sin (2 * cth p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
  Real.continuous_sin.comp_continuousOn
    ((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ × ℝ => (2:ℝ)) _).mul (continuousOn_cth (S := S)))

/-- Joint continuity of the `s`-derivative of the pulled-back unknown. -/
theorem dphi_s_continuous {α S : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (hS : 0 < S) (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => dphi_s α u p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      cz p.1 * Work.Spaces.pz (fun z θ => u z θ p.2.2) (cz p.1) (cth p.2.1) / om α p.1 p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    ((continuousOn_cz (S := S)).mul (pz_comp_continuous hS hu)).div
      (continuousOn_om (S := S) hα) (fun p hp => ne_of_gt (om_pos (α := α) hα))
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      2 * phi α u p.1 p.2.1 p.2.2 / (1 + cz p.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    (continuousOn_const.mul (phi_continuous hα hu)).div
      (continuousOn_const.add (continuousOn_cz (S := S)))
      (fun p hp => by
        have hc : (0:ℝ) < 1 + cz p.1 := by have := cz_pos p.1; linarith
        exact ne_of_gt hc)
  have h := h1.sub h2
  convert h using 1
  ext p
  simp only [Pi.sub_apply, dphi_s]

/-- Joint continuity of the `ψ`-derivative of the pulled-back unknown. -/
theorem dphi_ψ_continuous {α S : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ → ℝ}
    (hS : 0 < S) (hu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2) (dom S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => dphi_ψ α u p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Real.sin (2 * cth p.2.1) / 2)
        * (Work.Spaces.pth (fun z θ => u z θ p.2.2) (cz p.1) (cth p.2.1) / om α p.1 p.2.1))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    ((continuousOn_sin_two_cth (S := S)).div_const 2).mul
      ((pth_comp_continuous hS hu).div (continuousOn_om (S := S) hα)
        (fun p hp => ne_of_gt (om_pos (α := α) hα)))
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      phi α u p.1 p.2.1 p.2.2 * (α * Work.Construction.c2m (cth p.2.1)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    (phi_continuous hα hu).mul (continuousOn_const.mul (continuousOn_c2m_comp (S := S)))
  have h := h1.sub h2
  convert h using 1
  ext p
  simp only [Pi.sub_apply, dphi_ψ]

end Work.FTS_RegExport.RXT
