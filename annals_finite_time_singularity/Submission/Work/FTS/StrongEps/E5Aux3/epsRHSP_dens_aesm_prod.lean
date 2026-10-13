import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false

/-! ## The measure-theoretic toolbox for the triple product measure

The measure carried by the fake-time box is
`(dτ)|_{[0,T]} ⊗ (dz)|_{(0,∞)} ⊗ (dθ)|_{[0,π/2]}` on `ℝ × (ℝ × ℝ)` with the coordinate
order `(τ, (z, θ))`.  It is the restriction of the product Lebesgue measure to the *open*
box `(0,T) × (0,∞) × (0,π/2)`: the three factors `[0,T]`, `(0,∞)`, `[0,π/2]` differ from
`(0,T)`, `(0,∞)`, `(0,π/2)` only by null sets (`{0,T}`, `∅`, `{0,π/2}`). -/

/-- The product of the three restricted Lebesgue measures is the restriction of the product
Lebesgue measure to the open box `(0,T) × (0,∞) × (0,π/2)`. -/
private lemma restrict_prod_eq (T : ℝ) :
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
          (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
  have hA : (Set.Icc (0 : ℝ) T) =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) T :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))
      (a := (0 : ℝ)) (b := T)).symm
  have hB : ((Set.Ioi (0 : ℝ)) : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
    Filter.EventuallyEq.rfl
  have hC : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))
      (a := (0 : ℝ)) (b := π / 2)).symm
  have hBC : ((Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hB hC
  have hprod : ((Set.Icc (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ)) :
        Set (ℝ × (ℝ × ℝ)))
      =ᵐ[MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)]
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    MeasureTheory.Measure.set_prod_ae_eq hA hBC
  have hmain : (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
        (Set.Icc (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ))
      = (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    MeasureTheory.Measure.restrict_congr_set hprod
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
  exact hmain

/-- The open box `(0,T) × (0,∞) × (0,π/2)` is measurable. -/
private lemma measurableSet_box (T : ℝ) :
    MeasurableSet (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
  (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)).measurableSet

/-- A function continuous on the open box is a.e. strongly measurable for the triple product
measure of the fake-time box. -/
private lemma aesm_prod3_of_continuousOn {T : ℝ} {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))) :
    MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  rw [restrict_prod_eq T]
  exact hf.aestronglyMeasurable (measurableSet_box T)

/-- Two functions agreeing on the open box agree a.e. for the triple product measure. -/
private lemma ae_eq_of_eqOn_box {T : ℝ} {f h : ℝ × (ℝ × ℝ) → ℝ}
    (hfh : Set.EqOn f h
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))) :
    f =ᵐ[(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))] h := by
  rw [restrict_prod_eq T]
  exact hfh.aeEq_restrict (measurableSet_box T)

/-- The one-variable time derivative of a function on `ℝ × ℝ × ℝ` is the Fréchet derivative
in the direction of its third coordinate. -/
private lemma deriv_slice_eq_fderiv {G : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ}
    (h : DifferentiableAt ℝ G p) :
    deriv (fun s : ℝ => G (p.1, (p.2.1, s))) p.2.2 = fderiv ℝ G p (0, (0, 1)) := by
  have hL : HasDerivAt (fun s : ℝ => (p.1, (p.2.1, s))) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) p.2.2 := by
    simpa using (hasDerivAt_const (x := p.2.2) (c := p.1)).prodMk
      ((hasDerivAt_const (x := p.2.2) (c := p.2.1)).prodMk (hasDerivAt_id p.2.2))
  simpa only [Function.comp_def] using (h.hasFDerivAt.comp_hasDerivAt p.2.2 hL).deriv

/-! ## The lemma -/

/-- **A.e. strong measurability of the angular density of the projected scheme.**

`epsRHSP` is a convolution, so its measurability is *not* hereditary in the parameters: `E` is
an arbitrary map.  What makes the statement true is the scheme equation `hsol`: at every point
of the open box `(0,T) × (0,∞) × (0,π/2)` the right-hand side `epsRHSP … τ z θ` *equals* the
time derivative of the datum, and that derivative is continuous there because `g` is jointly
`C¹` on the box (`hcont`).  So the density agrees a.e. with a continuous function, and the
three restrictions of Lebesgue measure see the box up to a null set. -/
theorem epsRHSP_dens_aesm_prod {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2 / q.2.1)
      ((MeasureTheory.volume.restrict (Set.Icc 0 T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- On the open box the right-hand side is the time derivative of the datum.
  have hbox : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2
        = deriv (fun s => g q.2.1 q.2.2 s) q.1 := by
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨hτ, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    obtain ⟨hz, hθ⟩ := hq2
    exact ((hsol.2 q.2.1 q.2.2 q.1 hz hθ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩).hasDerivAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hτ) Set.Ioo_subset_Icc_self)).deriv.symm
  -- On the open box the datum is differentiable, so the time derivative is the Fréchet
  -- derivative in the time direction.
  have hdiff : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
      DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (q.2.1, (q.2.2, q.1)) := by
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨hτ, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    obtain ⟨hz, hθ⟩ := hq2
    have hmem : (q.2.1, (q.2.2, q.1)) ∈
        interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T)) := by
      rw [interior_prod_eq, interior_prod_eq, isOpen_Ioi.interior_eq, isOpen_Ioo.interior_eq,
        interior_Icc]
      exact ⟨hz, hθ, hτ⟩
    exact (hcont.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset)
  -- The Fréchet derivative in the time direction is continuous on the open box: `g` is `C¹`
  -- on an open neighbourhood of every point of the box, and the Fréchet derivative of a `C¹`
  -- function is continuous.
  have hcont_fderiv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (q.2.1, (q.2.2, q.1)) (0, (0, 1)))
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    have hVopen : IsOpen
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      isOpen_interior
    have hFV : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      hcont.mono interior_subset
    have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) p)
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) := by
      have h := hFV.fderivWithin (m := 0) (hVopen.uniqueDiffOn (𝕜 := ℝ)) (by simp)
      refine h.congr ?_
      intro p hp
      rw [fderivWithin_of_isOpen hVopen hp]
    have hfd2 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) p (0, (0, 1)))
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      hfd.clm_apply (contDiffOn_const (c := ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
    have hmap : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by fun_prop
    have hmaps : MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) := by
      intro q hq
      rw [Set.mem_prod] at hq
      obtain ⟨hτ, hq2⟩ := hq
      rw [Set.mem_prod] at hq2
      obtain ⟨hz, hθ⟩ := hq2
      rw [interior_prod_eq, interior_prod_eq, isOpen_Ioi.interior_eq, isOpen_Ioo.interior_eq,
        interior_Icc]
      exact ⟨hz, hθ, hτ⟩
    exact hfd2.continuousOn.comp hmap hmaps
  -- hence the time derivative itself is continuous on the open box
  have hcont_deriv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun s => g q.2.1 q.2.2 s) q.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont_fderiv.congr (fun q hq => deriv_slice_eq_fderiv (hdiff q hq))
  -- and so is the whole density with `epsRHSP` replaced by that derivative
  have hcont_repl : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.K q.2.2 * deriv (fun s => g q.2.1 q.2.2 s) q.1 / q.2.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    have hK : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2)
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
      have hKc : Continuous (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2) := by
        unfold Work.Spaces.K
        fun_prop
      exact hKc.continuousOn
    have hden : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.2.1)
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by fun_prop
    refine (hK.mul hcont_deriv).div hden ?_
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨-, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    exact ne_of_gt hq2.1
  -- the two densities agree on the open box
  have heq : Set.EqOn
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2 / q.2.1)
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        deriv (fun s => g q.2.1 q.2.2 s) q.1 / q.2.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    intro q hq
    simp only [hbox q hq]
  exact (aesm_prod3_of_continuousOn hcont_repl).congr (ae_eq_of_eqOn_box heq).symm

end Work.FTS.StrongEps.E5Aux3
