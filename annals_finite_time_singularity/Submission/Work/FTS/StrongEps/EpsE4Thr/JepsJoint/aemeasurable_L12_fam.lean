/-
Copyright: work module for the Elgindi finite-time singularity project.

# Joint a.e. measurability of the family `s ↦ L₁₂ (F s ·)(0)`

`Work.Construction.L12 f 0` is the iterated integral

  `∫_{z>0} ∫_{θ ∈ [0,π/2]} K θ · f z θ / z`

(`K θ = 3 sin θ cos²θ`), i.e. the operator `L₁₂` of the fundamental model evaluated at `ρ = 0`.
The lemma below says that if the three-variable family `F` is *jointly continuous* on
`[0,T] × (0,∞) × (0,π/2)` then `s ↦ L₁₂ (F s ·)(0)` is a.e. (strongly) measurable for the
Lebesgue measure restricted to `[0,T]`.

The proof has exactly the shape announced in the statement review:

* **Joint measurability of the integrand.**
  `(s,z,θ) ↦ K θ · F s z θ / z` is continuous on the open box
  `(Icc 0 T × Ioi 0) × Ioo 0 (π/2)`, hence a.e. strongly measurable w.r.t.
  `volume.restrict` of that box; the box agrees up to a null set with the closed box on which
  `(volume.restrict (Icc 0 T)).prod ((volume.restrict (Ioi 0)).prod (volume.restrict (Icc 0 (π/2))))`
  is concentrated (`Measure.prod_restrict` twice, `Measure.restrict_congr_set` and
  `Measure.set_prod_ae_eq`).  No integrability is needed, and none is available: continuity on
  the *open* quadrant gives no bound near `z = 0`.
* **Two Fubini–measurability steps**
  (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`, which needs only `SFinite ν`, not
  integrability): first integrate out `θ`, then `z`.
* **Identification with `L₁₂`** by unfolding `Work.Construction.L12`, `Work.FM.L12` and
  `Work.FM.L12dens` (the set-integral notation is *definitionally* an integral against
  `Measure.restrict`).
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-- **Joint a.e. measurability of `s ↦ L₁₂ (F s ·)(0)`.**  If `F` is jointly continuous on
`[0,T] × (0,∞) × (0,π/2)`, then `s ↦ Work.Construction.L12 (F s ·) 0` is a.e. strongly
measurable for `volume.restrict (Icc 0 T)`. -/
theorem aemeasurable_L12_fam {F : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hF : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2.1 q.2.2)
      (Set.Icc (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    AEMeasurable (fun s : ℝ => Work.Construction.L12 (fun z θ => F s z θ) 0)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  -- ### Step 1: joint a.e. strong measurability of the integrand
  have hjoint : AEStronglyMeasurable
      (fun r : (ℝ × ℝ) × ℝ => Work.Spaces.K r.2 * F r.1.1 r.1.2 r.2 / r.1.2)
      (((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))).prod
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))) := by
    -- the `F`-factor: continuous on the open box
    have hA : AEStronglyMeasurable (fun r : (ℝ × ℝ) × ℝ => F r.1.1 r.1.2 r.2)
        (((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))).prod
          (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))) := by
      have hSmeas : MeasurableSet
          (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
        ((measurableSet_Icc.prod measurableSet_Ioi).prod measurableSet_Ioo)
      have hcont : ContinuousOn (fun r : (ℝ × ℝ) × ℝ => F r.1.1 r.1.2 r.2)
          (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
        have h : ContinuousOn ((fun q : ℝ × (ℝ × ℝ) => F q.1 q.2.1 q.2.2) ∘
            (fun r : (ℝ × ℝ) × ℝ => ((r.1.1, (r.1.2, r.2)) : ℝ × (ℝ × ℝ))))
            (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
          refine hF.comp ?_ ?_
          · exact (continuous_fst.fst.prodMk
              (continuous_fst.snd.prodMk continuous_snd)).continuousOn
          · intro r hr
            simp only [Work.FTS.StrongEps.Quad, Set.mem_prod, Set.mem_Icc, Set.mem_Ioi,
              Set.mem_Ioo] at hr ⊢
            exact ⟨hr.1.1, hr.1.2, hr.2⟩
        simpa only [Function.comp_def] using h
      have hAc : AEStronglyMeasurable (fun r : (ℝ × ℝ) × ℝ => F r.1.1 r.1.2 r.2)
          (volume.restrict
            (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2)))) :=
        hcont.aestronglyMeasurable hSmeas
      -- the closed box differs from the open box only by the null set `θ ∈ {0, π/2}`
      have hae : ((((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ
            (Set.Icc (0 : ℝ) (Real.pi / 2)) : Set ((ℝ × ℝ) × ℝ))
          =ᵐ[volume] (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ
            (Set.Ioo (0 : ℝ) (Real.pi / 2)))) :=
        MeasureTheory.Measure.set_prod_ae_eq (ae_eq_refl _)
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
      -- and the target product of restricted measures is the restriction to the closed box
      have hM : (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Ioi 0))).prod
            (volume.restrict (Set.Icc 0 (Real.pi / 2)))) =
          volume.restrict
            (((Set.Icc (0 : ℝ) T) ×ˢ (Set.Ioi (0 : ℝ))) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
        rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
        exact MeasureTheory.Measure.restrict_congr_set hae
      rw [hM]
      exact hAc
    -- the angular–radial factor `K θ / z`
    have hK : Measurable
        (fun r : (ℝ × ℝ) × ℝ => Work.Spaces.K r.2 * (r.1.2)⁻¹) := by
      have hKc : Continuous Work.Spaces.K := by unfold Work.Spaces.K; fun_prop
      exact (hKc.measurable.comp measurable_snd).mul (measurable_inv.comp measurable_fst.snd)
    refine (hK.aestronglyMeasurable.mul hA).congr (Filter.Eventually.of_forall (fun r => ?_))
    show Work.Spaces.K r.2 * (r.1.2)⁻¹ * F r.1.1 r.1.2 r.2
      = Work.Spaces.K r.2 * F r.1.1 r.1.2 r.2 / r.1.2
    ring
  -- ### Step 2: the two Fubini–measurability steps (`θ` first, then `z`)
  have hinner : AEStronglyMeasurable
      (fun x : ℝ × ℝ => ∫ θ, Work.Spaces.K θ * F x.1 x.2 θ / x.2
        ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))))
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hjoint.integral_prod_right'
  have houter : AEStronglyMeasurable
      (fun s : ℝ => ∫ z, (∫ θ, Work.Spaces.K θ * F s z θ / z
        ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))))
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    hinner.integral_prod_right'
  -- ### Step 3: identify the integral with `L₁₂ (F s ·)(0)`
  have hfun : (fun s : ℝ => Work.Construction.L12 (fun z θ => F s z θ) 0)
      = (fun s : ℝ => ∫ z, (∫ θ, Work.Spaces.K θ * F s z θ / z
        ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) := by
    funext s
    simp only [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]
  rw [hfun]
  exact houter.aemeasurable

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
