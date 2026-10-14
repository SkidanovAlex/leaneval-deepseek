import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.GalFields.Norm.Xn_LGammaT_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two one-dimensional objects of the separated product -/

/-- The level-four radial slot sum `Σ_{j<5}(D_z^j B)²w²` of a `z`-only profile `B`. -/
def slot5 (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, (Work.Elliptic.DzdIter j B z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem slot5_nonneg (B : ℝ → ℝ) (z : ℝ) : 0 ≤ slot5 B z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The angular factor of the level-four separated product `Γ(θ)·r(z)`: the light weight
`smE θ = sin(2θ)^{-η}` plus the heavy slot with the sharp `α²`-coefficient and the combined
exponent `2α/5 - γ = 3α/10 - 1 ∈ (-1,0)`. -/
def afac4 (α : ℝ) (θ : ℝ) : ℝ :=
  Work.FTS.Nonlinear.RadialProd.smE θ
    + 4 * (100000 * α) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)

/-! ## The pointwise separation of `Corr α g = Γ(θ)·radA α g z` -/

/-- **The pointwise `ℋ⁴`-integrand bound for the transfer correction.**  For `θ ∈ Iθ` the
`ℋ⁴`-integrand of `Corr α g = Γ(θ)·radA α g z` is dominated by the product of the level-four
radial slot sum of `radA α g` and the angular factor `afac4 α`.

Proof: `E2norm.HkIntegrand_ang_rad_le_n` at `n = 4`, with angular profile `a = Γ`, `B0 = 1`
(`Γ ≤ 1`), `B1 = 10⁵α`, `G θ = sin(2θ)^{α/5}`: `|D_θ^iΓ| ≤ 10⁵α·Γ` for `1 ≤ i ≤ 4`
(`E2norm.DthIter_Gam_abs_le_alpha`) and `Γ ≤ sin(2θ)^{α/5}` (`LocData.Gam_le_sin_two_rpow`);
the heavy slot is then folded with `(sin(2θ)^{α/5})²·smG = sin(2θ)^{2α/5-γ}`
(`E2norm.rpow_sq_smG_eq`). -/
theorem HkIntegrand_Corr_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (g : Fn) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (Work.FTS.CoercivityFix.Corr α g) z θ
      ≤ slot5 (Work.FTS.CoercivityFix.Transfer.radA α g) z * afac4 α θ := by
  have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ (1 : ℝ) := fun θ hθ => by
    obtain ⟨h1, h2⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    rwa [abs_of_nonneg h1]
  have hB1pos : (0 : ℝ) < 100000 * α := by positivity
  have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (100000 * α) * (fun θ' => (Real.sin (2 * θ')) ^ (α / 5)) θ := by
    intro i hi hi4 θ hθ
    refine (Work.FTS.CoercivityFix.Transfer.E2norm.DthIter_Gam_abs_le_alpha i hi hi4 α hα
      hα1 hθ).trans ?_
    exact mul_le_mul_of_nonneg_left (Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθ) hB1pos.le
  have hfun : Work.FTS.CoercivityFix.Corr α g
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α g z := by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α g z θ
  rw [hfun]
  have hsep := Work.FTS.CoercivityFix.Transfer.E2norm.HkIntegrand_ang_rad_le_n (n := 4) (le_refl 4)
    (α := α) (a := fun θ => Work.Spaces.Gam α θ)
    (r := fun z => Work.FTS.CoercivityFix.Transfer.radA α g z)
    (G := fun θ => (Real.sin (2 * θ)) ^ (α / 5)) (B0 := 1) (B1 := 100000 * α)
    (z := z) (θ := θ) ha0 ha1 hθ
  refine hsep.trans (le_of_eq ?_)
  have hang : (1 : ℝ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + 4 * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ = afac4 α θ := by
    rw [one_pow, one_mul]
    rw [show (4 : ℝ) * (100000 * α) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        = 4 * (100000 * α) ^ 2
          * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        from by ring]
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.rpow_sq_smG_eq α hα hα1 hθ]
    rfl
  rw [hang]
  rfl

/-! ## The `ℋ⁴`-bound for the transfer correction -/


/-! ## The main theorem -/


end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyDiagAssembly =====
section

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

/-- **The `L²`-route data of a curve and its derivative family**, for a fixed weight `ρ` and a fixed
fake time `τ ∈ (0,T)`. -/
structure DiagCurve (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Fn) (τ T : ℝ) : Prop where
  ρmeas : AEMeasurable (Function.uncurry ρ) mup
  ρnn : ∀ᵐ p ∂mup, 0 ≤ ρ p.1 p.2
  int_diag : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  int_diagd : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) mup
  aesm : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  aesmd : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod mup)
  deriv : ∀ᵐ p ∂mup, ∀ s ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s
  cont : ∀ᵐ p ∂mup, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T)
  bdd : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup ≤ K
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂mup) (nhds τ) (nhds 0)
  int_cross : MeasureTheory.Integrable
    (fun p : ℝ × ℝ => udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2) mup




end Work.FTS.StrongEps.EpsE4Thr
end
end
