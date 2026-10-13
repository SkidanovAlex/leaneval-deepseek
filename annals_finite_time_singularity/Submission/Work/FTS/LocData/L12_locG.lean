import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.LocData.L12_hLoc
import Submission.Work.FTS.LocData.integrableOn_bumpZ_div
import Submission.Work.FTS.LocData.integrableOn_L12dens_zfar
import Submission.Work.Stability.L12Add
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

open MeasureTheory Set Filter
open scoped Real Topology

/-! ### Wrappers of the fundamental-model linearity in `Construction.L12` -/

/-- `L₁₂` is homogeneous in a constant, in the vocabulary of `Work.Construction`. -/
theorem L12_const_mul_C (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.L12 (fun z θ => c * f z θ) z = c * Work.Construction.L12 f z :=
  Work.FM.L12_const_mul

/-- `L₁₂` is additive, in the vocabulary of `Work.Construction`. -/
theorem L12_add_C {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (hf : ∀ s, MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (hg : ∀ s, MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * g s θ / s) Work.Spaces.Iθ)
    (hF : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi z))
    (hG : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => f z θ + g z θ) z
      = Work.Construction.L12 f z + Work.Construction.L12 g z :=
  Work.FM.L12_add hf hg hF hG

/-! ### The `L₁₂`-value of the localised perturbation `locG`

`locG α L β h` is the difference between the localised profile `locData = F_*·χ(·/L) + βh`
and the profile `F_*` itself; pointwise (`locG_eq_zfar`)

  `locG α L β h = - zfar L F_* + β h`,

so the value of the *linear* functional `L₁₂(·)(0)` splits — provided the two summands have
integrable angular slices (they do: both are constant multiples of the slice of `F_*`, resp. of
`Γ·K`) and integrable densities on `(0,∞)`.  The latter two are the hypotheses `hzfar`, `hbump`
of the lemma below; they are discharged for `h = hLoc α` in `L12_locG`. -/
theorem L12_locG_of_integrable (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    (hzfar : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Stability.zfar L (Work.Construction.Fstar α)))
      (Set.Ioi (0 : ℝ)))
    (hbump : MeasureTheory.IntegrableOn (fun s : ℝ => bumpZ s / s) (Set.Ioi (0 : ℝ))) :
    Work.Construction.L12 (locG α L β (hLoc α)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 := by
  -- the pointwise decomposition of `locG` into its two summands
  have hfun : locG α L β (hLoc α)
      = fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
          + β * hLoc α z θ := by
    funext z θ
    exact locG_eq_zfar α L β (hLoc α) z θ
  -- the angular slice of the negated far part: a constant multiple of the slice of `F_*`
  have hslice_neg : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (-(Work.Stability.zfar L (Work.Construction.Fstar α) s θ)) / s)
      Work.Spaces.Iθ := by
    intro s
    have hc : MeasureTheory.IntegrableOn
        (fun θ => (-(1 - Work.Stability.chi (s / L))) *
          (Work.Spaces.K θ * Work.Construction.Fstar α s θ / s)) Work.Spaces.Iθ :=
      (Work.Stability.integrableOn_slice_Fstar α hα s).const_mul _
    refine hc.congr_fun (fun θ _ => ?_) measurableSet_Icc
    rw [Work.Stability.zfar_apply]
    ring
  -- the angular slice of `β h`: a constant multiple of `Γ·K`
  have hslice_beta : ∀ s : ℝ, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (β * hLoc α s θ) / s) Work.Spaces.Iθ := by
    intro s
    have hc : MeasureTheory.IntegrableOn
        (fun θ => (β * bumpZ s / s) * (Work.Spaces.Gam α θ * Work.Spaces.K θ)) Work.Spaces.Iθ :=
      (Work.Spaces.CAux.integrableOn_GamK α hα).const_mul _
    refine hc.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hLoc_apply]
    ring
  -- the density of the negated far part is the negated density
  have hdens_neg_pt : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) s
      = -(Work.FM.L12dens Work.Spaces.K
        (Work.Stability.zfar L (Work.Construction.Fstar α)) s) := by
    intro s
    simp only [Work.FM.L12dens]
    rw [show (∫ θ in Set.Icc 0 (π / 2),
          Work.Spaces.K θ * (-(Work.Stability.zfar L (Work.Construction.Fstar α) s θ)) / s)
        = ∫ θ in Set.Icc 0 (π / 2), -(Work.Spaces.K θ *
            Work.Stability.zfar L (Work.Construction.Fstar α) s θ / s) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_neg]
  have hdens_neg : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)))
      (Set.Ioi (0 : ℝ)) := by
    refine hzfar.neg.congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact (hdens_neg_pt s).symm
  -- the density of `β h` is `(β c) · (bumpZ s / s)`
  have hdens_beta_pt : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (fun z θ => β * hLoc α z θ) s
      = (β * Work.Spaces.c α) * (bumpZ s / s) := by
    intro s
    rw [L12dens_const_mul Work.Spaces.K β (hLoc α) s, L12dens_hLoc α s]
    ring
  have hdens_beta : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun z θ => β * hLoc α z θ)) (Set.Ioi (0 : ℝ)) := by
    have hc : MeasureTheory.IntegrableOn (fun s : ℝ => (β * Work.Spaces.c α) * (bumpZ s / s))
        (Set.Ioi (0 : ℝ)) := hbump.const_mul _
    refine hc.congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact (hdens_beta_pt s).symm
  -- additivity of `L₁₂` on the two summands
  have hadd : Work.Construction.L12
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
          + β * hLoc α z θ) 0
      = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
        + Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0 :=
    L12_add_C (f := fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ))
      (g := fun z θ => β * hLoc α z θ) (z := 0)
      hslice_neg hslice_beta hdens_neg hdens_beta
  -- the two homogeneous pieces
  have hneg_eq : Work.Construction.L12
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0) := by
    have hfun2 : (fun r => Work.FM.L12dens Work.Spaces.K
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) r)
        = fun r => -(Work.FM.L12dens Work.Spaces.K
          (Work.Stability.zfar L (Work.Construction.Fstar α)) r) :=
      funext fun r => hdens_neg_pt r
    simp only [Work.Construction.L12, Work.FM.L12]
    rw [hfun2, MeasureTheory.integral_neg]
  have hbeta_eq : Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0
      = β * Work.Construction.L12 (hLoc α) 0 :=
    L12_const_mul_C β (hLoc α) 0
  calc Work.Construction.L12 (locG α L β (hLoc α)) 0
      = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)
            + β * hLoc α z θ) 0 := by rw [hfun]
    _ = Work.Construction.L12
          (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α) z θ)) 0
        + Work.Construction.L12 (fun z θ => β * hLoc α z θ) 0 := hadd
    _ = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 := by rw [hneg_eq, hbeta_eq]

theorem L12_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.Construction.L12 (locG α L β (hLoc α)) 0
      = -(Work.Construction.L12 (Work.Stability.zfar L (Work.Construction.Fstar α)) 0)
        + β * Work.Construction.L12 (hLoc α) 0 :=
  L12_locG_of_integrable α L β hα hα1 hL
    (integrableOn_L12dens_zfar α L hα hα1 hL) integrableOn_bumpZ_div

end Work.FTS.LocData
