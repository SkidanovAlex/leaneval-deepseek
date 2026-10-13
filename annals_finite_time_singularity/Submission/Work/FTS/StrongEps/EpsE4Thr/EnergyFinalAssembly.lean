/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/EnergyFinalAssembly.lean` — the level-four energy identity
of the `P₀`-scheme from the per-slot `L²`-bundles

This is the end of the chain opened in session 3 and repaired in session 4:

  slot data (`mixed j i`, order `≤ 3`)
    → `DiagCurveI` bundles (the `L²`-route data, `EnergyDiagAssemblyIoo`)
    → `EnergyDeriv (H1IP α)` (`EnergyDeriv_H1IP_of_diag_data_I`)
    → `EnergyDeriv (IP4 …)` (`WordTransfer.energyDeriv_IP4_of_mixed`),

i.e. exactly the `hderiv` input of `EpsE4Thr.apriori_fourth_of_barrier` (with
`E4' τ = 2 · IP4 … (ẋ τ) (x τ)`).

Also recorded: the **uniform `L²` bound** `hK` on a slot of the derivative family, from
`SlotL2LeHkSq.integral_slot_sq_rpow_le_HkSq` and a uniform `ℋ⁴`-size bound.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssemblyIoo
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordTransfer
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotL2LeHkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The uniform `L²` bound on the slots of the derivative family.**  If the derivative family has
a uniform `ℋ⁴`-size `R`, every slot of order `≤ 4` has weighted square-integral `≤ R²` uniformly in
the fake time, for every weight `w²σ^c` with `c ≥ -η`. -/
theorem slot_L2_uniform_le {α c : ℝ} {j i : ℕ} {xd : ℝ → Fn} {T : ℝ}
    (hα : 0 < α) (hc : -(Work.Spaces.eta) ≤ c) (hji : j + i ≤ 4)
    (hsm : ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (xd σ))
    (hmem : ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4 (xd σ))
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 4 (xd σ) ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ K := by
  obtain ⟨R, hR0, hRb⟩ := hR
  refine ⟨R ^ 2, sq_nonneg R, fun σ hσ => ?_⟩
  have h1 := integral_slot_sq_rpow_le_HkSq (α := α) (g := xd σ) (c := c) (j := j) (i := i)
    hα hc hji (hsm σ hσ) (hmem σ hσ)
  have h2 : Work.Spaces.HkSq α 4 (xd σ) = (Work.Spaces.HkNorm α 4 (xd σ)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
  have h3 : (∫ p : ℝ × ℝ, (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ p : ℝ × ℝ, (Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
          * (Work.Spaces.mixed j i (xd σ) p.1 p.2) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [h3]
  refine le_trans h1 ?_
  rw [h2]
  exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) (hRb σ hσ) 2

/-- **The level-four energy identity of the projected mollified family from the per-slot `L²`
bundles.**  This is the `hderiv` input of `apriori_fourth_of_barrier` with
`E4' τ = 2 · IP4 … (ẋ τ) (x τ)`. -/
theorem EnergyDeriv_IP4_of_DiagCurveI {α : ℝ} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) {x xd : ℝ → Fn}
    {τ T : ℝ} (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (x s))
    (hsmd : Work.FTS.EllipticEst.SmoothOpen (xd τ))
    (hdata : ∀ j i : ℕ, j + i ≤ 3 →
      DiagCurveI Work.FTS.StrongPersist.rhoEta
          (fun s => Work.Spaces.mixed j i (x s)) (fun s => Work.Spaces.mixed j i (xd s)) τ T ∧
      DiagCurveI Work.FTS.StrongPersist.rhoW
          (fun s => Work.Spaces.mixed j i (x s)) (fun s => Work.Spaces.mixed j i (xd s)) τ T ∧
      DiagCurveI Work.FTS.StrongPersist.rhoEta
          (fun s => Work.Spaces.Dz (Work.Spaces.mixed j i (x s)))
          (fun s => Work.Spaces.Dz (Work.Spaces.mixed j i (xd s))) τ T ∧
      DiagCurveI (Work.FTS.StrongPersist.rhoGam α)
          (fun s => Work.Spaces.Dth (Work.Spaces.mixed j i (x s)))
          (fun s => Work.Spaces.Dth (Work.Spaces.mixed j i (xd s))) τ T) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) x (xd τ) τ :=
  energyDeriv_IP4_of_mixed c₁ c₂ c₁' c₂' c₁'' c₂'' hτIoo hsm hsmd
    (fun j i hji => EnergyDeriv_H1IP_of_diag_data_I (α := α)
      (u := fun s => Work.Spaces.mixed j i (x s))
      (udot := fun s => Work.Spaces.mixed j i (xd s)) (τ := τ) (T := T)
      (by linarith [hτIoo.1, hτIoo.2]) hτIoo
      (hdata j i hji).1 (hdata j i hji).2.1 (hdata j i hji).2.2.1 (hdata j i hji).2.2.2)

/-- **The level-six energy identity of the projected mollified family from the per-slot `L²`
bundles.**  The same statement as `EnergyDeriv_IP4_of_DiagCurveI` with `IP4` replaced by `IP6` and
slots of order `≤ 5` (the words of length `≤ 5` that `IP6 = IPiter 5` needs). -/
theorem EnergyDeriv_IP6_of_DiagCurveI {α : ℝ} (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ)
    {x xd : ℝ → Fn} {τ T : ℝ} (hτIoo : τ ∈ Set.Ioo (0 : ℝ) T)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (x s))
    (hsmd : Work.FTS.EllipticEst.SmoothOpen (xd τ))
    (hdata : ∀ j i : ℕ, j + i ≤ 5 →
      DiagCurveI Work.FTS.StrongPersist.rhoEta
          (fun s => Work.Spaces.mixed j i (x s)) (fun s => Work.Spaces.mixed j i (xd s)) τ T ∧
      DiagCurveI Work.FTS.StrongPersist.rhoW
          (fun s => Work.Spaces.mixed j i (x s)) (fun s => Work.Spaces.mixed j i (xd s)) τ T ∧
      DiagCurveI Work.FTS.StrongPersist.rhoEta
          (fun s => Work.Spaces.Dz (Work.Spaces.mixed j i (x s)))
          (fun s => Work.Spaces.Dz (Work.Spaces.mixed j i (xd s))) τ T ∧
      DiagCurveI (Work.FTS.StrongPersist.rhoGam α)
          (fun s => Work.Spaces.Dth (Work.Spaces.mixed j i (x s)))
          (fun s => Work.Spaces.Dth (Work.Spaces.mixed j i (xd s))) τ T) :
    Work.FTS.StrongPersist.EnergyDeriv
      (Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α) x (xd τ) τ :=
  energyDeriv_IP6_of_mixed e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' hτIoo hsm hsmd
    (fun j i hji => EnergyDeriv_H1IP_of_diag_data_I (α := α)
      (u := fun s => Work.Spaces.mixed j i (x s))
      (udot := fun s => Work.Spaces.mixed j i (xd s)) (τ := τ) (T := T)
      (by linarith [hτIoo.1, hτIoo.2]) hτIoo
      (hdata j i hji).1 (hdata j i hji).2.1 (hdata j i hji).2.2.1 (hdata j i hji).2.2.2)

end Work.FTS.StrongEps.EpsE4Thr
