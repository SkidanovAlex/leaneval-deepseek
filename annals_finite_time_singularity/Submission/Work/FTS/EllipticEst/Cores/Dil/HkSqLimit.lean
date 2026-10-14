import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DilSlots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `z`-derivatives of `D_z g` -/

/-- `∂_z (z ∂_z g) = ∂_z g + z ∂_z²g`. -/
theorem pz_Dz_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.Dz g) z θ
        = Work.Spaces.pz g z θ + z * Work.Spaces.pzIter 2 g z θ := by
  intro z θ hz hθ
  have h2 := (hg.pz).hasDerivAt_slice hθ hz
  have hgoal : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz g z' θ)
      (Work.Spaces.pz g z θ + z * Work.Spaces.pzIter 2 g z θ) z := by
    have h := (hasDerivAt_id z).mul h2
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz g z' θ)
        = id * (fun z' : ℝ => Work.Spaces.pz g z' θ) := by
      funext z'; simp
    rw [hfun]
    simpa using h
  rw [show Work.Spaces.pz (Work.Spaces.Dz g) z θ
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz g z' θ) z from rfl]
  exact hgoal.deriv

/-- `∂_z²(z ∂_z g) = 2 ∂_z²g + z ∂_z³g`. -/
theorem pzIter_two_Dz_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
        = 2 * Work.Spaces.pzIter 2 g z θ + z * Work.Spaces.pzIter 3 g z θ := by
  intro z θ hz hθ
  have h1 := (hg.pz).hasDerivAt_slice hθ hz
  have h2 := (hg.pzIter 2).hasDerivAt_slice hθ hz
  have hprod : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 2 g z' θ)
      (Work.Spaces.pzIter 2 g z θ + z * Work.Spaces.pzIter 3 g z θ) z := by
    have h := (hasDerivAt_id z).mul h2
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pzIter 2 g z' θ)
        = id * (fun z' : ℝ => Work.Spaces.pzIter 2 g z' θ) := by
      funext z'; simp
    rw [hfun]
    simpa using h
  have hsum : HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz g z' θ + z' * Work.Spaces.pzIter 2 g z' θ)
      (Work.Spaces.pzIter 2 g z θ + (Work.Spaces.pzIter 2 g z θ
        + z * Work.Spaces.pzIter 3 g z θ)) z := h1.add hprod
  have hev : (fun z' : ℝ => Work.Spaces.pz (Work.Spaces.Dz g) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.pz g z' θ + z' * Work.Spaces.pzIter 2 g z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_Dz_eq hg z' θ hz' hθ
  rw [show Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
      = deriv (fun z' : ℝ => Work.Spaces.pz (Work.Spaces.Dz g) z' θ) z from rfl]
  rw [hev.deriv_eq, hsum.deriv]
  ring

/-- `∂_z(z² ∂_z²g) = 2 z ∂_z²g + z² ∂_z³g`. -/
theorem pz_zsq_pzIter_two_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
        = 2 * z * Work.Spaces.pzIter 2 g z θ + z ^ 2 * Work.Spaces.pzIter 3 g z θ := by
  intro z θ hz hθ
  have h2 := (hg.pzIter 2).hasDerivAt_slice hθ hz
  have hsq : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hgoal : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ)
      (2 * z * Work.Spaces.pzIter 2 g z θ + z ^ 2 * Work.Spaces.pzIter 3 g z θ) z := by
    have h := hsq.mul h2
    have hfun : (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ)
        = (fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => Work.Spaces.pzIter 2 g z' θ) := by
      funext z'; simp
    rw [hfun]
    exact h
  rw [show Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
      = deriv (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ) z from rfl]
  exact hgoal.deriv

/-- **The first slot identity**: `z²∂_z²(D_z g) = D_z(z² ∂_z²g)` on the open quadrant. -/
theorem zsq_pzIter_two_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ)
      (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ)) := by
  intro z θ hz hθ hlt
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  show z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
  rw [pzIter_two_Dz_eq hg z θ hz hθ']
  simp only [Work.Spaces.Dz]
  rw [pz_zsq_pzIter_two_eq hg z θ hz hθ']
  ring

/-! ## The `θ`-derivatives of `D_z g` -/

/-- `∂_θ(D_z g) = D_z(∂_θ g)` on the open quadrant (Clairaut). -/
theorem pth_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (Work.Spaces.pth (Work.Spaces.Dz g)) (Work.Spaces.Dz (Work.Spaces.pth g)) := by
  intro z θ hz hθ hlt
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    ((smoothOpen_iff_forall g).mp hg 2).contDiffAt (isOpen_Q0.mem_nhds hp)
  have hclair : Work.Spaces.pz (Work.Spaces.pth g) z θ
      = Work.Spaces.pth (Work.Spaces.pz g) z θ :=
    Work.Spaces.pz_pth_comm (f := g) hcd
  show deriv (fun θ' : ℝ => z * Work.Spaces.pz g z θ') θ
      = Work.Spaces.Dz (Work.Spaces.pth g) z θ
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz g) z θ
      = Work.Spaces.Dz (Work.Spaces.pth g) z θ
  rw [← hclair]
  rfl

/-- **The second slot identity**: `∂_θ²(D_z g) = D_z(∂_θ²g)` on the open quadrant. -/
theorem pthIter_two_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (Work.Spaces.pthIter 2 (Work.Spaces.Dz g))
      (Work.Spaces.Dz (Work.Spaces.pthIter 2 g)) := by
  have h1 := pth_Dz_AgreeOnQ hg
  have h2 := pth_Dz_AgreeOnQ (hg.pth)
  intro z θ hz hθ hlt
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd' : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) (z, θ) :=
    ((smoothOpen_iff_forall (Work.Spaces.pth g)).mp (hg.pth) 2).contDiffAt
      (isOpen_Q0.mem_nhds hp)
  have hclair : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth g) hcd'
  rw [Work.Spaces.pthIter_succ]
  show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.Dz g) z θ') θ = _
  have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.Dz g) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.Dz (Work.Spaces.pth g) z θ') := by
    filter_upwards [Ioo_mem_nhds hθ'.1 hθ'.2] with θ'' hθ''
    exact h1 z θ'' hz hθ''.1 hθ''.2
  rw [hev.deriv_eq]
  show deriv (fun θ' : ℝ => z * Work.Spaces.pz (Work.Spaces.pth g) z θ') θ = _
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
  rw [← hclair]
  show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
  rw [show Work.Spaces.pth (Work.Spaces.pth g) = Work.Spaces.pthIter 2 g from rfl]
  rfl

end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.DqTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false


end Work.FTS.EllipticEst.Cores.Dil
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The level-`0` `ℋ`-integrand is the single squared weighted slot. -/
theorem HkIntegrand_zero_apply (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- The product measure of the quadrant `Iz ×ˢ Iθ`. -/
abbrev quadMeasure : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- **A.e. strong measurability of the level-`0` integrand of a function continuous on `Q0`.**
The integrand is continuous on the open quadrant, which differs from the closed quadrant
`Iz ×ˢ Iθ` by the null set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`. -/
theorem aemeasurable_ofReal_HkIntegrand_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2) Q0) :
    AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f p.1 p.2))
      quadMeasure := by
  have hQ0 : MeasurableSet Q0 := isOpen_Q0.measurableSet
  have hsub : Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ ⟨hz, hθ0, hθ1⟩
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℝ) ≤ z
      exact le_of_lt hz
    · show (0 : ℝ) ≤ θ
      exact le_of_lt hθ0
    · show θ ≤ Real.pi / 2
      exact le_of_lt hθ1
  have hnull1 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      (Q0 \ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) = 0 := by
    rw [Set.sdiff_eq_empty.mpr hsub, MeasureTheory.measure_empty]
  have hnull2 : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ Q0) = 0 := by
    have hsub2 : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ Q0
        ⊆ (({0} : Set ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0} : Set ℝ))
          ∪ (Set.univ ×ˢ ({Real.pi / 2} : Set ℝ)) := by
      rintro ⟨z, θ⟩ ⟨⟨hzI, hθI⟩, hQ⟩
      rw [Work.Spaces.Iz, Set.mem_Ici] at hzI
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθI
      by_cases hz0 : z = 0
      · exact Or.inl (Or.inl ⟨hz0, Set.mem_univ _⟩)
      · have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
        have hnp : ¬ (0 < θ ∧ θ < Real.pi / 2) := fun hcon =>
          hQ (mem_Q0.mpr ⟨hzpos, hcon.1, hcon.2⟩)
        by_cases hθ0 : θ = 0
        · exact Or.inl (Or.inr ⟨Set.mem_univ _, hθ0⟩)
        · refine Or.inr ⟨Set.mem_univ _, ?_⟩
          have hθpos : 0 < θ := lt_of_le_of_ne hθI.1 (Ne.symm hθ0)
          have hge : ¬ (θ < Real.pi / 2) := fun hlt => hnp ⟨hθpos, hlt⟩
          exact le_antisymm hθI.2 (not_lt.mp hge)
    refine MeasureTheory.measure_mono_null hsub2 ?_
    rw [MeasureTheory.measure_union_null_iff, MeasureTheory.measure_union_null_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [MeasureTheory.Measure.prod_prod]; simp
    · rw [MeasureTheory.Measure.prod_prod]; simp
    · rw [MeasureTheory.Measure.prod_prod]; simp
  have hrc : quadMeasure
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict Q0 := by
    show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.ae_eq_set.mpr ⟨hnull2, hnull1⟩)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict Q0) :=
    hf.aestronglyMeasurable hQ0
  rw [hrc]
  exact ENNReal.measurable_ofReal.comp_aemeasurable haesm.aemeasurable

/-- **The bridge**: for a function in `ℋ⁰`, the `ofReal` of its iterated `ℋ⁰`-integral is the
product-measure lintegral of the `ofReal` of its integrand. -/
theorem ofReal_HkSq_zero {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 0 g)
    (hmeas : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2)) quadMeasure) :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 g)
      = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g p.1 p.2) ∂quadMeasure := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 g z θ) := fun z hz =>
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  have houter := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.2)
    (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  show ENNReal.ofReal (Work.Spaces.HkSq α 0 g) = _
  rw [Work.Spaces.HkSq]
  rw [show quadMeasure
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) from rfl,
    MeasureTheory.lintegral_prod _ hmeas]
  rw [houter]
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
  exact hinner z hz

/-- **Fatou for the `ℋ⁰`-functional.**  If `u n` converges pointwise a.e. to `v`, each `u n` is in
`ℋ⁰` (honestly), `v` is in `ℋ⁰`, the integrands are a.e. measurable, and the `ℋ⁰`-norms of the
`u n` are eventually bounded by `y`, then the `ℋ⁰`-norm of `v` is at most `y`. -/
theorem HkSq_zero_le_of_eventually_le {α : ℝ} {u : ℕ → ℝ → ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    (hmeasn : ∀ n : ℕ, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2)) quadMeasure)
    (hmeasv : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2)) quadMeasure)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 0 (u n))
    (hmemv : Work.Spaces.HkMem α 0 v)
    (hae : ∀ᵐ p ∂quadMeasure,
      Filter.Tendsto (fun n : ℕ => u n p.1 p.2) Filter.atTop (nhds (v p.1 p.2)))
    {y : ℝ} (hy : ∀ᶠ n : ℕ in Filter.atTop, Work.Spaces.HkSq α 0 (u n) ≤ y) :
    Work.Spaces.HkSq α 0 v ≤ y := by
  -- the pointwise convergence of the integrands
  have hpoint : ∀ᵐ p ∂quadMeasure,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2)
        = Filter.liminf
            (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2))
            Filter.atTop := by
    filter_upwards [hae] with p hp
    rw [HkIntegrand_zero_apply α v p.1 p.2,
      show (fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2))
        = fun n : ℕ => ENNReal.ofReal
            ((u n p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2)
        from funext fun n => by rw [HkIntegrand_zero_apply]]
    have hstep : Filter.Tendsto
        (fun n : ℕ => u n p.1 p.2
          * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)))
        Filter.atTop (nhds (v p.1 p.2
          * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2)))) :=
      hp.mul tendsto_const_nhds
    have hsq := hstep.pow 2
    have hoF : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal
          ((u n p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2))
        Filter.atTop (nhds (ENNReal.ofReal
          ((v p.1 p.2 * (Work.Spaces.w p.1 / Real.sin (2 * p.2) ^ (Work.Spaces.eta / 2))) ^ 2))) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hsq
    exact hoF.liminf_eq.symm
  -- Fatou
  have hfatou : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2) ∂quadMeasure
      ≤ Filter.liminf (fun n : ℕ =>
          ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
          Filter.atTop := by
    calc ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 v p.1 p.2) ∂quadMeasure
        = ∫⁻ p, Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2)) Filter.atTop
            ∂quadMeasure := MeasureTheory.lintegral_congr_ae hpoint
      _ ≤ Filter.liminf (fun n : ℕ =>
            ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
            Filter.atTop := MeasureTheory.lintegral_liminf_le' hmeasn
  -- the bridges
  have hbridge : ∀ n : ℕ,
      ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure
        = ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) :=
    fun n => (ofReal_HkSq_zero (hmem n) (hmeasn n)).symm
  -- assemble
  have hle : ENNReal.ofReal (Work.Spaces.HkSq α 0 v) ≤ ENNReal.ofReal y := by
    rw [ofReal_HkSq_zero hmemv hmeasv]
    refine hfatou.trans ?_
    rw [show (fun n : ℕ =>
        ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (u n) p.1 p.2) ∂quadMeasure)
        = fun n : ℕ => ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) from funext hbridge]
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · filter_upwards with n
      exact bot_le
    · intro b hb
      have hy' : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (Work.Spaces.HkSq α 0 (u n)) ≤ ENNReal.ofReal y :=
        hy.mono fun n hn => ENNReal.ofReal_le_ofReal hn
      obtain ⟨n, hn⟩ := (hb.and hy').exists
      exact hn.1.trans hn.2
  by_cases hy0 : 0 ≤ y
  · exact (ENNReal.ofReal_le_ofReal_iff hy0).mp hle
  · exfalso
    obtain ⟨n, hn⟩ := hy.exists
    have := Work.Spaces.HkSq_nonneg α 0 (u n)
    linarith

end Work.FTS.EllipticEst.Cores.Dil
end
end
