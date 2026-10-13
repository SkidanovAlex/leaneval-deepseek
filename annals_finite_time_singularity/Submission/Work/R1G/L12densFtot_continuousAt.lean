import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.Defs
import Submission.Work.Coercivity.L12_facts_n
import Submission.Work.Coercivity.L12dens_integrableOn
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Stability.L12Add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **Angular additivity of the `L₁₂`-density over `F = F_* + g`.**  For `s > 0` the angular
slice of `F_*` and the angular slice of a modulation `g` smooth on a neighbourhood of the
closed quadrant are both integrable on `Iθ = [0,π/2]`, so the density of the sum splits:

  `L12dens (F_* + g) s = L12dens (F_*) s + L12dens g s`.

This is the *pointwise* (angular) half of `Work.R1G.L12densFtot_add`; no radial
integrability is needed. -/
theorem L12densFtot_add_pointwise {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (fun z θ => Work.Construction.Fstar p z θ + g z θ) s
      = Work.Construction.L12dens (Work.Construction.Fstar p) s
        + Work.Construction.L12dens g s := by
  have hs1 : s ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hF : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.Construction.Fstar p s θ / s)
      (Set.Icc 0 (Real.pi / 2)) :=
    Work.Stability.integrableOn_slice_Fstar p hp s
  have hg : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * g s θ / s) (Set.Icc 0 (Real.pi / 2)) := by
    have hK : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) (Set.Icc 0 (Real.pi / 2)) := by
      unfold Work.Spaces.K; fun_prop
    have hsl : ContinuousOn (fun θ : ℝ => g s θ) (Set.Icc 0 (Real.pi / 2)) :=
      Work.Elliptic.continuousOn_slice_theta_Iθ g hsm hs1
    exact ((hK.mul hsl).div_const s).integrableOn_compact isCompact_Icc
  simp only [Work.Construction.L12dens, Work.FM.L12dens]
  have hcongr : (∫ θ in Set.Icc 0 (Real.pi / 2),
        Work.Spaces.K θ * (Work.Construction.Fstar p s θ + g s θ) / s)
      = ∫ θ in Set.Icc 0 (Real.pi / 2),
          (Work.Spaces.K θ * Work.Construction.Fstar p s θ / s
            + Work.Spaces.K θ * g s θ / s) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [hcongr, MeasureTheory.integral_add hF hg]

/-- **The density `L₁₂(F_*)` is continuous at every `z > 0`**: its closed form
`L12dens (F_*) s = α · F_*(s)/s` (`Work.Construction.L12dens_Fstar`) is the elementary
function `2α/(1+s)²` away from `s = 0`. -/
theorem L12densFstar_continuousAt {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {z : ℝ} (hz : 0 < z) :
    ContinuousAt (Work.Construction.L12dens (Work.Construction.Fstar p)) z := by
  have h1 : ContinuousAt (fun s : ℝ => Work.FM.Fstar s / s) z :=
    (Work.FM.hasDerivAt_Fstar z (by linarith)).continuousAt.div continuousAt_id (ne_of_gt hz)
  have h2 : ContinuousAt (fun s : ℝ => p * (Work.FM.Fstar s / s)) z := h1.const_mul p
  refine h2.congr ?_
  filter_upwards with s
  exact (Work.Construction.L12dens_Fstar (α := p) hp hp1 s).symm

theorem L12densFtot_continuousAt {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {z : ℝ} (hz : 0 < z) :
    ContinuousAt
      (Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar (Work.ConstructionInstance.profExp α) z θ + P.g z θ)) z := by
  have hp : 0 < Work.ConstructionInstance.profExp α := Work.ConstructionInstance.profExp_pos P.hα
  have hFc : ContinuousAt
      (Work.Construction.L12dens (Work.Construction.Fstar (Work.ConstructionInstance.profExp α))) z :=
    L12densFstar_continuousAt hp (profExp_le_one P) hz
  have hgc : ContinuousAt (Work.Construction.L12dens P.g) z :=
    Work.Coercivity.L12dens_continuousAt_K P.g P.hsmooth z hz
  refine (hFc.add hgc).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
  exact (L12densFtot_add_pointwise hp P.hsmooth hs).symm

end Work.R1G
