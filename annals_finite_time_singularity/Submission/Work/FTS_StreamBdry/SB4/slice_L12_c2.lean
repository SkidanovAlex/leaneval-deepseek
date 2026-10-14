import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.NHonest
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXR1.slice_diff_weighted
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.landau_1d
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.L12_slice_jets_le
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharp_modulation_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.GalFields.RHS.sharp_modulation_diff`

The **difference (Lipschitz) estimate for the two modulation constants**

  `μ  = mufunS α (N₀ α (F_tot α g) g) (N α (F_tot α g) (Φ_s + EllSol g)) g`,
  `μ̄  = mubar (N₀ α (F_tot α g) g) (N α (F_tot α g) (Φ_s + EllSol g))`

of the modulation problem (Elgindi, Annals **194** (3) 2021, §Modulation, tex 1366/1380), in the
*sharp* (linear-in-the-difference) form consumed by the `RHSData.lip` clause of
`Submission/Work/FTS/GalFields/Defs.lean`.

Both constants are, by definition (`Construction/Defs.lean`, `Construction/MufunS.lean`),

  `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,
  `μ  = (1/(2α))·(L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3 D_θ g/(1+z))(0))`,

so the difference of the two modulation constants is the explicit linear combination

  `μ(g) − μ(g') = (1/(2α))·(ΔN₀ + ΔN + ΔT)`,   `μ̄(g) − μ̄(g') = ΔN₀ + ΔN`

of the three `L₁₂`-differences

  `ΔN₀ = L₁₂(N₀ α (F_tot α g) g)(0) − L₁₂(N₀ α (F_tot α g') g')(0)`,
  `ΔN  = L₁₂(N α (F_tot α g) (Φ_s+EllSol g))(0) − L₁₂(N α (F_tot α g') (Φ_s+EllSol g'))(0)`,
  `ΔT  = L₁₂(3 D_θ g/(1+z))(0) − L₁₂(3 D_θ g'/(1+z))(0)`,

each bounded by `K·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|g−g'|_{ℋ⁵}` by the three pieces
`SharpMod.N0_L12_diff`, `SharpMod.N_L12_diff` and `SharpMod.transport_L12_diff`.  The proof below
is the assembly: unfold the two definitions with `simp only`, `ring`, and apply the triangle
inequality to the three available bounds.

The `ℋ⁵`-pricing of the difference is not a defect: `ℋ⁴` of `D_z g`, `D_θ g` is only controlled by
`ℋ⁵` of `g` (`GalFields/Defs.lean`, `Norm/Basic.lean`).
-/

namespace Work.FTS.GalFields.RHS


end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Chapters =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Chapters.lean` — the corrected E4 chapters and their assembly (PROVED)

curric-46 install 2026-10-12 (`cbc/fts_e5swap_e4chapters.md` §B, REVIEW
`cbc/fts_e5swap_e4chapters_REVIEW.md`).  `EpsDecay` was edited **in place** (`StrongEps/EpsMem.lean`:
cap `Maj ≤ 1`, the three elliptic blocks bounded by `3` on the open quadrant), so the corrected
target `EpsE4R3Stmt` of the design *is* the statement of `StrongEps.EpsE4R`, verbatim, and the
decay chapter is `EpsE4Thr.DecayChapter` itself (its `AprioriDecayB` reads the new `EpsDecay`).
Changed against `EpsE4Thr.EpsE4RAsm`:

* `LocalStepChapter3`: only `ε ∈ (0,1]`;
* `AprioriChapter3`: `M ≥ K` and `ε₂ ∈ (0,1]` chosen after `T` (at `M = K` the old chapter is
  false: `g₀ = 0`, `K = 0`, the forcing moves the solution);
* the assembly `EpsE4R3_of_chapters` takes `∃ C, ∀ C₀ ≥ C, chapter` for each chapter, and
  `C★ := max (max 2 CL) (max CP CD)`.

Everything here is `sorry`-free.  Of the three chapters, **`DecayChapter3` is proved**
(`E4R3/Decay3.lean := E4R3/Decay3_leaf.lean`, session 22); the two still open leaves are
`E4R3/LocalStep3` (needs the pinning of the elliptic image + the raw-slice traces) and
`E4R3/Apriori3` (needs the raw-slice `ℋ⁷` datum for its `ℋ⁶` half and the coercive pairing
`Nonlin.UnifIP` for its level-`4` half) — see `StrongEps/NOTES_session22.md` §3 and
`StrongEps/REQUEST_LEAD_session22.md` (3).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R3

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps

set_option autoImplicit false



/-- **Decay chapter** (= `EpsE4Thr.DecayChapter`, now over the bounded-block `EpsDecay`). -/
def DecayChapter3 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α' ρ T Φs E g₀ C₀ Maj



end Work.FTS.StrongEps.EpsE4Thr.E4R3
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds`

The angular derivative `D_θ = sin(2θ)·∂_θ` of the slices `slice g τ` of a `LimApprox` family `g`
is uniformly bounded, and is Lipschitz in the fake time `τ`, with the radial weight
`Rwt z = z^{3/2}/(1+z)²`:

  `|D_θ (slice g τ) z θ| ≤ C₁ · Rwt z`
  `|D_θ (slice g τ) z θ − D_θ (slice g τ') z θ| ≤ C₁ · Rwt z · |τ − τ'|`

for `τ, τ' ∈ [0,S]`, `z > 0`, `θ ∈ Iθ = [0,π/2]`.

Both clauses are immediate from the two standing estimates for `LimApprox` families, on the
*open* angle range `0 < θ < π/2`:

* `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` — the weighted slotwise bound
  `|mixed b a (slice g τ) z θ| ≤ C·Rwt z` for `a + b ≤ 2`, obtained from the uniform `ℋ⁴`-bound of
  the class-`C` approximants (the constant `C₀·α²` of the `LimApprox` clause) and the interior
  `L^∞`–`ℋ⁴` trade-off `abs_mixed_le_HkNorm_C4_w_proved`;
* `Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus` — the same slots differ between two
  times by `L·Rwt z·|τ − τ'|`, obtained by applying the trade-off to the class-`C` difference
  `slice (gn n) τ - slice (gn n) τ'` and passing to the limit along the `C⁴`-jet convergence.

`D_θ f` is definitionally `mixed 0 1 f`, so these are exactly the required estimates on the open
range.  The two boundary angles `θ = 0` and `θ = π/2` are handled separately: there `sin(2θ) = 0`,
so `D_θ` vanishes identically *whatever* the (possibly junk) value of `∂_θ f`, and both clauses
are trivial.  This is why the statement needs no restriction to the open angular interval.
-/

namespace Work.FTS_RegExport.RXR5L.Auxiliary

theorem Dth_slice_bounds {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hLim : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C1 * Work.FTS_RegExport.RXT.L12Iter.Rwt z) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z →
        θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ') z θ|
          ≤ C1 * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'|) := by
  have hαG0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the two standing estimates for the limit family, on the open angular range
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) hαG0 hαG1 hLim S hS
  obtain ⟨L, hL0, hL⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) hLim hαG0 hαG1 S hS
  -- `D_θ` vanishes at both boundary angles, whatever the angular slice does there
  have key0 : ∀ (F : ℝ → ℝ → ℝ) (z θ : ℝ), (θ = 0 ∨ θ = Real.pi / 2) →
      Work.Spaces.Dth F z θ = 0 := by
    rintro F z θ (rfl | rfl)
    · simp [Work.Spaces.Dth]
    · simp only [Work.Spaces.Dth]
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
  have hC1 : 0 ≤ max C L := le_trans hC0 (le_max_left _ _)
  refine ⟨max C L, hC1, ?_, ?_⟩
  · intro τ hτ z θ hz hθ
    have hR : 0 ≤ Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
      (Work.FTS_RegExport.RXT.L12Iter.Rwt_pos hz).le
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    by_cases hdeg : θ = 0 ∨ θ = Real.pi / 2
    · rw [key0 (Work.FTS.Galerkin.slice g τ) z θ hdeg, abs_zero]
      exact mul_nonneg hC1 hR
    · rw [not_or] at hdeg
      have hθ0' : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hdeg.1)
      have hθ1' : θ < Real.pi / 2 := lt_of_le_of_ne hθ1 hdeg.2
      have h := hC τ hτ 0 1 (by norm_num) z θ hz hθ0' hθ1'
      calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ|
          = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ| := rfl
        _ ≤ C * Work.FTS_RegExport.RXT.L12Iter.Rwt z := h
        _ ≤ max C L * Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  · intro τ hτ τ' hτ' z θ hz hθ
    have hR : 0 ≤ Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
      (Work.FTS_RegExport.RXT.L12Iter.Rwt_pos hz).le
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    by_cases hdeg : θ = 0 ∨ θ = Real.pi / 2
    · rw [key0 (Work.FTS.Galerkin.slice g τ) z θ hdeg,
        key0 (Work.FTS.Galerkin.slice g τ') z θ hdeg, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hC1 hR) (abs_nonneg _)
    · rw [not_or] at hdeg
      have hθ0' : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hdeg.1)
      have hθ1' : θ < Real.pi / 2 := lt_of_le_of_ne hθ1 hdeg.2
      have h := hL τ hτ τ' hτ' 0 1 (by norm_num) z θ hz hθ0' hθ1'
      calc |Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ') z θ|
          = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ
              - Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ') z θ| := rfl
        _ ≤ L * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'| := h
        _ ≤ max C L * Work.FTS_RegExport.RXT.L12Iter.Rwt z * |τ - τ'| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
              (abs_nonneg _)

end Work.FTS_RegExport.RXR5L.Auxiliary
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.MubarRows =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn)
open Work.FTS_MuLipC
open Work.FTS_MuLipC.RowN0
open Work.FTS_MuLipC.RowN

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "L12" => Work.Construction.L12
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

theorem diffRow0_noSmall {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_MuLipC.DiffRow0 α C₀ := by
  refine ⟨3 * Real.sqrt (Mconst C₀ α) + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hC₀ : 0 ≤ C₀ := by
    have h0 : 0 ≤ Xn α f' := Work.Spaces.HkNorm_nonneg α 4 f'
    have h1 : 0 < α ^ 2 := pow_pos hα 2
    nlinarith [hXf', h0, h1]
  have hmemf : Work.Spaces.HkMem α 4 f := Work.FTS.ClassC.classC_hkMem_four hf
  have hmemf' : Work.Spaces.HkMem α 4 f' := Work.FTS.ClassC.classC_hkMem_four hf'
  have hCsub : Work.FTS.ClassC.ClassC α (f - f') := classC_sub hf hf'
  have hmemD : Work.Spaces.HkMem α 4 (f - f') := Work.FTS.ClassC.classC_hkMem_four hCsub
  have hddefD : ∀ z θ, (f - f') z θ = f z θ - f' z θ := fun z θ => rfl
  set Xd : ℝ := Xn α (f - f') with hXddef
  have hXd : Xn α (f - f') = Xd := rfl
  have hXdnn : 0 ≤ Xd := by
    rw [← hXd]; exact Work.Spaces.HkNorm_nonneg α 4 (f - f')
  -- continuity of the difference field on the open quadrant
  have hcontf : ContinuousOn (Function.uncurry (Sn0 α f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf.reg hmemf
  have hcontf' : ContinuousOn (Function.uncurry (Sn0 α f'))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.contN0_open hα hα1 hf'.reg hmemf'
  have hcontD : ContinuousOn (Function.uncurry (fun z θ => Sn0 α f z θ - Sn0 α f' z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hcontf.sub hcontf'
  -- a.e. strong measurability of the weighted angular energy
  have hmeasD : MeasureTheory.AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Work.FTS.OpenPkg.l12zero_energy_aesm hcontD
  -- slice integrability of the squared difference
  have hslD : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
    have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
    have hDM : DiffMaj α C₀ Xd (f - f') f' r
        = fun θ => 3 * (A1const C₀ α * Hk α 4 (f - f') r θ
            + A2const Xd α * Hk α 4 f' r θ
            + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
      funext θ
      rw [DiffMaj, A1const, A2const]
    have h3c : MeasureTheory.IntegrableOn
        (fun _ : ℝ => 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
    have hmaj : MeasureTheory.IntegrableOn (fun θ => DiffMaj α C₀ Xd (f - f') f' r θ)
        Work.Spaces.Iθ := by
      rw [hDM]
      exact (((hmemD.1 r hzr).const_mul (A1const C₀ α)).add
        ((hmemf'.1 r hzr).const_mul (A2const Xd α))).add h3c |>.const_mul 3
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Sn0 α f p.1 p.2 - Sn0 α f' p.1 p.2) ^ 2) (hcontD.pow 2) hr
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hpt := diff_pointwise_le hα hα1 hC₀ hXd hf.reg hf'.reg hCsub.reg hmemf hmemf' hmemD
      hddefD hXf hr hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        ≤ (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r := by nlinarith [hw1]
      _ ≤ DiffMaj α C₀ Xd (f - f') f' r θ := hpt
  -- the energy bound with the explicit majorant
  have hbdE : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ PhiC α C₀ Xd (f - f') f' r := by
    filter_upwards [diff_energy_le hα hα1 hC₀ hXdnn hXf hXd hf.reg hf'.reg hCsub.reg hmemf
      hmemf' hmemD hddefD] with r hr
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hw] at hr
    exact hr
  have hΦint : MeasureTheory.IntegrableOn (PhiC α C₀ Xd (f - f') f') (Set.Ioi (0 : ℝ)) :=
    integrableOn_PhiC hmemD hmemf'
  have hL12bound := Work.FTS.OpenPkg.l12zero_of_weight_bound
    (f := fun z θ => Sn0 α f z θ - Sn0 α f' z θ) hslD hmeasD hΦint hbdE
  have hint : (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) ≤ Mconst C₀ α * Xd ^ 2 :=
    int_PhiC_le hXdnn hmemD hmemf' hXd hXf' hC₀ hα
  -- the density integrability of the two single fields
  have hslf : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf.reg hmemf
  have hslf' : ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2)
      Work.Spaces.Iθ :=
    N0_slice_sq_integrable hα hα1 hf'.reg hmemf'
  have hEf : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf.reg hmemf] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f r θ) ^ 2) := rfl
    have hR : Phi1 α f r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f)
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f)
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hEf' : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Phi1 α f' r := by
    filter_upwards [N0_weighted_energy_le hα hα1 hf'.reg hmemf'] with r hr
    have hL : (∫ θ in Work.Spaces.Iθ, (Sn0 α f' r θ) ^ 2)
        = (∫ θ in Work.Spaces.Iθ,
            (Work.Construction.N0 α (Work.Construction.Ftot α f') f' r θ) ^ 2) := rfl
    have hR : Phi1 α f' r = 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Xn α f')
          * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + (Real.pi / 2) * Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Xn α f')
          * (1 / (1 + r)) ^ 2) := rfl
    have hw : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
    rw [hL, hR] at *
    exact hr
  have hslf_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf r hr)
  have hslf'_ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Sn0 α f' r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => hslf' r hr)
  have hdensf : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f) hcontf)
      (integrableOn_Phi1 hmemf) (Phi1_nonneg f) hEf
  have hdensf' : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Sn0 α f'))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_energy hslf'_ae
      (aesm_L12dens_of_continuousOn (F := Sn0 α f') hcontf')
      (integrableOn_Phi1 hmemf') (Phi1_nonneg f') hEf'
  have hSaf : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f p.1 p.2) hcontf hr)
      (hslf r hr)
  have hSaf' : ∀ r ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Sn0 α f' r θ / r) Work.Spaces.Iθ :=
    fun r hr => integrableOn_K_mul_div hr
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Sn0 α f' p.1 p.2) hcontf' hr)
      (hslf' r hr)
  have hsub := L12_sub_of_integrable (a := Sn0 α f) (b := Sn0 α f') hdensf hdensf' hSaf hSaf'
  have hM0 : 0 ≤ Mconst C₀ α := Mconst_nonneg C₀ α
  rw [hsub]
  calc |L12 (fun z θ => Sn0 α f z θ - Sn0 α f' z θ) 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd (f - f') f' r) := hL12bound
    _ ≤ 3 * Real.sqrt (Mconst C₀ α * Xd ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hint) (by norm_num)
    _ = 3 * Real.sqrt (Mconst C₀ α) * Xd := by
        rw [Real.sqrt_mul hM0, Real.sqrt_sq hXdnn]
        ring
    _ ≤ (3 * Real.sqrt (Mconst C₀ α) + 1) * Xd := by
        have hs : 0 ≤ Real.sqrt (Mconst C₀ α) := Real.sqrt_nonneg _
        nlinarith [hs, hXdnn]


theorem diffRow1_noSmall {α C₀ Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    Work.FTS_MuLipC.DiffRow1 α C₀ Φs E := by
  classical
  -- ### the constants
  set K₁ : ℝ := Work.FTS_MuLamOK.KMu1 Ce Cs with hK₁
  have hK₁pos : 0 < K₁ := Work.FTS_MuLamOK.KMu1_pos Ce Cs
  have hK₁0 : 0 ≤ K₁ := hK₁pos.le
  set c : ℝ := max C₀ 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hcC : C₀ ≤ c := le_max_left _ _
  set B₁ : ℝ := Real.sqrt 2 * (2 * Real.sqrt 2 * c + 1) with hB₁
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  set B₂ : ℝ := 1 + B₁ + B₁ ^ 2 with hB₂
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  refine ⟨K₁ * B₂ + 1, by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hXc : Work.FTS.Nonlin.Xn α f ≤ c * α ^ 2 :=
    le_trans hXf (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  have hXc' : Work.FTS.Nonlin.Xn α f' ≤ c * α ^ 2 :=
    le_trans hXf' (mul_le_mul_of_nonneg_right hcC (sq_nonneg α))
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hX0 : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  rcases lt_or_eq_of_le hX0 with hXpos | hXzero
  · -- ### the main case `|f - f'|_{ℋ⁴} > 0`
    set t : ℝ := α ^ 2 / X with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have htX : t * X = α ^ 2 := by
      rw [ht]
      field_simp
    have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
    rw [← hX, htX] at hle
    have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + α ^ 2) = B₁ * α ^ 2 := by
      rw [hB₁]
      ring
    rw [hV] at hle
    have hEnv : Work.FTS_MuLipC.Env α (B₁ * α ^ 2) ≤ B₂ * α ^ 2 := by
      rw [hB₂]
      exact Env_scaled hα hα1 hB₁0
    have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α (B₁ * α ^ 2) :=
      Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
    have htinv : K₁ / t = K₁ * X / α ^ 2 := by
      rw [ht]
      field_simp
    calc |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
        ≤ (K₁ / t) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := hle
      _ = (K₁ * X / α ^ 2) * Work.FTS_MuLipC.Env α (B₁ * α ^ 2) := by rw [htinv]
      _ ≤ (K₁ * X / α ^ 2) * (B₂ * α ^ 2) := by
          refine mul_le_mul_of_nonneg_left hEnv ?_
          positivity
      _ = K₁ * B₂ * X := by
          field_simp
      _ ≤ (K₁ * B₂ + 1) * X := by nlinarith [hX0, hB₂0, hK₁0]
  · -- ### the degenerate case `|f - f'|_{ℋ⁴} = 0`
    have hzero : |Work.Construction.L12 (Sn α Φs E f) 0
        - Work.Construction.L12 (Sn α Φs E f') 0| = 0 := by
      refine le_antisymm ?_ (abs_nonneg _)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      set t : ℝ := K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1 with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have hle := l12_diff_le hα hα1 hc0 hEadd hEsmul hstar hell hf hf' hXc hXc' htpos
      rw [← hX, hXzero.symm] at hle
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← pow_two]
        exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hV : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2 + t * 0) = (4 * c) * α ^ 2 := by
        have hmid : Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2) = (4 * c) * α ^ 2 := by
          calc Real.sqrt 2 * (2 * Real.sqrt 2 * c * α ^ 2)
              = (Real.sqrt 2 * Real.sqrt 2) * (2 * c * α ^ 2) := by ring
            _ = 2 * (2 * c * α ^ 2) := by rw [hsq2]
            _ = (4 * c) * α ^ 2 := by ring
        rw [mul_zero, add_zero, hmid]
      rw [hV] at hle
      have hEnv : Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 :=
        Env_scaled hα hα1 (by positivity)
      have hEnv0 : 0 ≤ Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) :=
        Work.FTS_MuLipC.Env_nonneg hα.le (by positivity)
      have hnum0 : 0 ≤ K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 := by positivity
      have hfin : (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2) ≤ ε := by
        calc (K₁ / t) * Work.FTS_MuLipC.Env α ((4 * c) * α ^ 2)
            ≤ (K₁ / t) * ((1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) := by
              refine mul_le_mul_of_nonneg_left hEnv ?_
              positivity
          _ = (K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2) / t := by
              field_simp
          _ ≤ ε := by
              rw [ht]
              rw [div_le_iff₀ (by positivity : 0 < K₁ * (1 + (4 * c) + (4 * c) ^ 2) * α ^ 2 / ε + 1)]
              field_simp
              nlinarith [hε.le, hnum0]
      linarith [hle, hfin]
    rw [hzero]
    exact mul_nonneg (by positivity) hX0


end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.NoHdat.vz0_of_vopLower_noHdat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.NoHdat.vz0_of_vopLower`

The `vz0` clause of `Work.FTS_RegExport.VelPkgOpen` at the sanitised family
`(gS α (tauExt g), psiR α Φs E (tauExt g))`, reduced to the *lower bound*

  `hVop : -(1 - maxMu τ) ≤ 2 α·V(Φ)(z,θ)`   (`Φ = slice (psiR α Φs E (tauExt g)) τ`)

on the `V`-slot of the stream function itself.

On the open quadrant `RXDiag.closedFormOpen` writes the coefficient as

  `Vz7 = (1 - μ τ) + L₁₂(F)·c2m(θ) + 2α·V(Φ̃)`,   `Φ̃ = Φ − Θ(F)`,  `F = Ftau αG G τ`,

and the `Θ`-identity `2α·V(Θ αG F) = L₁₂(F)·c2m(θ)` (whose proof needs only the *value* of
`∂_θΘ`, i.e. `Construction.pth_Theta_eq`) collapses this to

  `Vz7 = (1 - μ τ) + 2α·V(Φ)`.

The `Θ`-identity only asks for the differentiability of the `θ`-slice of `Φ` at the point,
which is supplied here by `RXT.contDiffOn_slice_PhiR_Q0` (`slice (psiR …) τ` is `C³` on the
open quadrant, from `EllLimOK3`, `StarPkgo2`, `DynOK'`).  Hence

  `0 ≤ Vz7  ⟺  -(1 - μ τ) ≤ 2α·V(Φ)`,   which is exactly `hVop`.
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXVP.NoHdat

set_option autoImplicit false

/-- The `θ`-slice of a function which is `C^n` on the open quadrant is `C^n` on `(0, π/2)`. -/
theorem vz7_contDiffOn_thslice {f : ℝ → ℝ → ℝ} {n : ℕ} {z : ℝ} (hz : 0 < z)
    (hf : ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
  (hf.comp (((contDiffOn_const (c := z) :
      ContDiffOn ℝ n (fun _ : ℝ => z) (Set.Ioo 0 (π / 2)))).prodMk
    (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2))))
    (fun _ hθ => ⟨hz, hθ⟩)).congr (fun _ _ => rfl)

/-- The `θ`-slice of a function which is `C³` on the open quadrant is differentiable at every
interior point of the quadrant. -/
theorem vz7_differentiableAt_tslice {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 3 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have h1c : ContDiffOn ℝ 1 (fun θ' : ℝ => f z θ') (Set.Ioo 0 (π / 2)) :=
    vz7_contDiffOn_thslice (n := 1) hz (hf.of_le (by norm_num))
  exact (h1c.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Ioo.mem_nhds ⟨h0, h1⟩)

/-- **The closed form of `V(Θ)`**: `2 α·V(Θ α F) = L₁₂(F)·c2m(θ)` on the open quadrant
(no differentiability of `F` is needed: only the explicit `∂_θ`-derivative of `sin 2θ`).  This
is the `V`-half of `RXDiag.closedFormOpen`'s `two_mul_Vop_Theta`, extracted so that it can be
used with a mere `DifferentiableAt` hypothesis on the `θ`-slice. -/
theorem vz7_two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hpth := Work.Construction.pth_Theta_eq (α := αG) (F := F) hαG z θ
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-- **The `Θ`-split of `V`**: `V(Φ̃) = V(Φ) − V(Θ α F)` for `Φ̃ = Φ − Θ α F`, at any point where
the `θ`-slice of `Φ` is differentiable (`V` is `∂_θ − tan θ`, and the `θ`-dependence of `Θ` is
the explicit factor `sin 2θ`). -/
theorem vz7_vop_phiTil_eq {αG : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨ : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ) :
    Work.Construction.Vop (Work.Construction.PhiTil αG F Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        - Work.Construction.Vop (Work.Construction.Theta αG F) z θ := by
  have hΘ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta αG F z θ') θ := by
    have hfun : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    rw [hfun]
    fun_prop
  have hpth : Work.Spaces.pth (Work.Construction.PhiTil αG F Ψ) z θ
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth (Work.Construction.Theta αG F) z θ := by
    simp only [Work.Spaces.pth]
    rw [show (fun θ' => Work.Construction.PhiTil αG F Ψ z θ')
          = (fun θ' => Ψ z θ') - (fun θ' => Work.Construction.Theta αG F z θ') from by
        funext θ'; rfl,
      deriv_sub hΨ hΘ]
  have hval : Work.Construction.PhiTil αG F Ψ z θ
      = Ψ z θ - Work.Construction.Theta αG F z θ := rfl
  simp only [Work.Construction.Vop]
  rw [hpth, hval]
  ring

/-- **The closed form of `Vz7` on the open quadrant.**  For any families `G`, `Φ` and any clock
`μ`, at a point of the open quadrant where the `θ`-slice of `Φ` (at time `τ`) is differentiable,

  `Vz7 αG μ G Φ z θ τ = (1 - μ τ) + 2 αG·V (slice Φ τ) z θ`.

So the `Θ`-part of the coefficient contributes exactly `L₁₂(F)·c2m(θ) = 2αG·V(Θ)`. -/
theorem vz7_eq_of_vop {αG : ℝ} (hαG : 0 < αG) {μ : ℝ → ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    {z θ τ : ℝ} (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hd : DifferentiableAt ℝ (fun θ' => Work.FTS.Galerkin.slice Φ τ z θ') θ) :
    Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (Work.FTS.Galerkin.slice Φ τ) z θ := by
  have hsub : Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
      = Work.Construction.Vop (Work.FTS.Galerkin.slice Φ τ) z θ
        - Work.Construction.Vop
            (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ :=
    vz7_vop_phiTil_eq (αG := αG) (F := Work.Construction.Ftau αG G τ) hd
  have hΘ : 2 * αG * Work.Construction.Vop
        (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) z θ
      = Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ :=
    vz7_two_mul_Vop_Theta (αG := αG) hαG hθ hθ2
  simp only [Work.FTS.RegExportIface.Vz7]
  rw [hsub, mul_sub, hΘ]
  ring


end Work.FTS_RegExport.RXVP.NoHdat
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DthG_theta_mod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DthG_theta_mod` — the `θ`-modulus of `D_θ g̃` (leaf **B2** of O1)

The family `DthG α g z θ τ = D_θ (gS α (tauExt g)) (z,θ,τ) = sin(2θ)·∂_θ (gS α (tauExt g))` is
`α`-Hölder in `θ`, uniformly on `τ ∈ [0,S]` and on `z ≥ 0`, with a constant depending only on the
six weighted slot bounds `WSys α S K g`.

Route (the sibling of `RXT.st1_hhθ`, one order up).

* On `z > 0, θ ∈ (0,π/2), τ ≥ 0` the sanitiser and the right-Taylor extension are invisible
  (`gS α h z θ τ = h z θ τ` for `0 < z`, `θ ∈ Iθ`; `tauExt g = g` for `τ ≥ 0`), so
  `DthG α g z θ τ = mixed 0 1 (slice g τ) z θ` (the `(0,1)`-slot of `WSys`).
* The engine `RXT.theta_modulus_uniform_fb` only needs, for the `θ`-slice
  `u = fun x => DthG α g z x τ`,
  * `|u x| ≤ K·Γ(θ)` on `Iθ` — the `(0,1)`-slot plus `ω ≤ Γ`, and `u = 0` at both endpoints
    because of the factor `sin 2θ`;
  * `|u'| ≤ K·Γ/sin(2θ)` on `(0,π/2)` with `u' x = mixed 0 2 (slice g τ) z x / sin(2x)` — the
    `(0,2)`-slot plus `ω ≤ Γ`; this is the only place where two slots (`k = 2, 5` of `idx`) are
    consumed.
* The `HasDerivAt` of `u` is the `θ`-slice derivative of the mixed jet `mixed 0 1 (slice g τ)`
  (`RXT.hasDerivAt_slice_snd_of_contDiffOn` + `E2pkg.contDiffOn_uncurry_mixed_le`, at order `4`
  from `RegPkgMin.c4`), moved over to `gS α (tauExt g)` by eventual equality, and its value
  `pth (mixed 0 1 …)` rewritten as `mixed 0 2 … / sin 2θ` (definitional, `mixed 0 2 = D_θ(mixed 0 1)`).
* At `z = 0` everything vanishes (`gS` is `0` for `z ≤ 0`), so the bound is trivial.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

set_option autoImplicit false

/-- The sanitiser is invisible on `z > 0`, `θ ∈ Iθ`. -/
private lemma gS_apply_of_mem (α : ℝ) {h : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.FinalV2.gS α h z θ τ = h z θ τ := by
  simp [Work.FTS.FinalV2.gS, hz, hθ.1, hθ.2]

/-- **The `(0,1)`-slot**: on the open quadrant at a nonnegative fake time, the `O1` family
`DthG` is the mixed jet `D_θ (slice g τ)`. -/
private lemma DthG_eq_mixed_prv {α : ℝ} (g : Work.FTS.Galerkin.Fam) {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (π / 2)) :
    Work.FTS_RegExport.THL.DthG α g z θ τ
      = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ := by
  have hev : (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ)
      =ᶠ[𝓝 θ] (fun θ' => Work.FTS.Galerkin.slice g τ z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [gS_apply_of_mem α hz ⟨hθ'.1.le, hθ'.2.le⟩,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    rfl
  change Real.sin (2 * θ)
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) θ
    = Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
  rw [hev.deriv_eq]

/-- The family vanishes on the left angular edge `θ = 0` (the factor `sin 2θ`). -/
private lemma DthG_zero_theta {α : ℝ} (g : Work.FTS.Galerkin.Fam) (z τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g z 0 τ = 0 := by
  change Real.sin (2 * (0:ℝ))
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) 0 = 0
  rw [show (2:ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul]

/-- The family vanishes on the right angular edge `θ = π/2`. -/
private lemma DthG_zero_pi_div_two {α : ℝ} (g : Work.FTS.Galerkin.Fam) (z τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g z (π / 2) τ = 0 := by
  change Real.sin (2 * (π / 2))
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ' τ) (π / 2) = 0
  rw [show (2:ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]

/-- The family vanishes for `z = 0` (the sanitiser is `0` there). -/
private lemma DthG_zero_rad {α : ℝ} (g : Work.FTS.Galerkin.Fam) (θ τ : ℝ) :
    Work.FTS_RegExport.THL.DthG α g 0 θ τ = 0 := by
  have hfun : (fun θ' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ)
      = fun _ => (0:ℝ) := by
    funext θ'; simp only [Work.FTS.FinalV2.gS, lt_irrefl, ite_false]
  change Real.sin (2 * θ)
      * deriv (fun θ' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ) θ = 0
  rw [hfun, deriv_const, mul_zero]

theorem DthG_theta_mod {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S) (hK0 : 0 ≤ K)
    (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DthG α g z θ τ - Work.FTS_RegExport.THL.DthG α g z θ' τ|
          ≤ L * |θ - θ'| ^ α := by
  obtain ⟨L, hL0, hL⟩ := Work.FTS_RegExport.RXT.theta_modulus_uniform_fb
    (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: both values vanish
    subst hz0
    rw [DthG_zero_rad g θ τ, DthG_zero_rad g θ' τ, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · -- `z > 0`: the uniform `θ`-modulus engine on the slice `x ↦ DthG α g z x τ`
    refine hL (u := fun x => Work.FTS_RegExport.THL.DthG α g z x τ)
      (u' := fun x => Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x / Real.sin (2 * x))
      ?_ ?_ ?_ θ hθ θ' hθ'
    · -- the derivative: `θ`-slice derivative of the mixed jet `D_θ (slice g τ)`
      intro x hx
      have hsin : Real.sin (2 * x) ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))
      have hW1 : ContDiffOn ℝ 1
          (Function.uncurry (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ)))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
          Work.FTS.EllipticEst.isOpen_Q0 1 0 1 (by norm_num) (hmin.c4 τ hτ.1)
      have hbase := Work.FTS_RegExport.RXT.hasDerivAt_slice_snd_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hW1 (z := z) (θ := x) ⟨hzpos, hx⟩
      have hval : Work.Spaces.pth (Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ)) z x
          = Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x / Real.sin (2 * x) := by
        rw [eq_div_iff hsin, mul_comm]
        rfl
      rw [hval] at hbase
      have hev : (fun x' => Work.FTS_RegExport.THL.DthG α g z x' τ)
          =ᶠ[𝓝 x] (fun θ' => Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with θ' hθ'
        exact DthG_eq_mixed_prv g hτ.1 hzpos hθ'
      exact hbase.congr_of_eventuallyEq hev
    · -- the derivative bound `|u'| ≤ K·Γ/sin 2θ` from the `(0,2)`-slot
      intro x hx
      have hsin : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
      have h := hw 5 τ hτ z x hzpos hx.1 hx.2
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h
      have hKΓ : |Work.Spaces.mixed 0 2 (Work.FTS.Galerkin.slice g τ) z x|
          ≤ K * Work.FTS.Regularity.Gamma α x :=
        le_trans h (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le ⟨hx.1.le, hx.2.le⟩) hK0)
      rw [abs_div, abs_of_pos hsin, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hKΓ hsin.le
    · -- the value bound `|u| ≤ K·Γ` on the closed interval
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
      · subst hx0
        rw [DthG_zero_theta g z τ, Work.FTS_RegExport.RXT.Gamma_zero_left hα, mul_zero, abs_zero]
      · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
        · subst hxπ
          rw [DthG_zero_pi_div_two g z τ, Work.FTS_RegExport.RXT.Gamma_zero_right hα, mul_zero,
            abs_zero]
        · -- the interior: the `(0,1)`-slot and `ω ≤ Γ`
          rw [DthG_eq_mixed_prv g hτ.1 hzpos ⟨hxpos, hxlt⟩]
          have h := hw 2 τ hτ z x hzpos hxpos hxlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h
          exact le_trans h (mul_le_mul_of_nonneg_left
            (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le hx) hK0)

end Work.FTS_RegExport.THL.L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DzG_theta_mod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzG_theta_mod` (B1 of `fts_thlip_o1_plans.md`)

The z-uniform `θ`-modulus of the second slot `g̃ ↦ z∂_z g̃ = D_z g̃` of the family
`g̃ = gS α (tauExt g)`.

The family `DzG α g z · τ = D_z (g̃(·,·,τ))(z,·)` is `α`-Hölder on `Iθ` with a constant uniform in
`z ≥ 0` and `τ ∈ [0,S]`.  Route (exactly the plan's):

* the value bound `|D_z g̃(z,θ,τ)| = |mixed 1 0 g̃| ≤ K·ω ≤ K·Γ(θ)` uses the `(1,0)`-slot of `hw`
  on the open interval and the two boundary vanishing facts at `θ = 0, π/2` (`hmin.vanish`);
* the derivative bound `|∂_θ(D_z g̃)| = |mixed 1 1 g̃|/sin 2θ ≤ K·Γ(θ)/sin 2θ` uses the `(1,1)`
  slot (`mixed_one_one_eq`), with the `z²/(1+z)²` factor absorbed by `ω ≤ Γ`;
* the engine `RXT.theta_modulus_uniform_fb` turns the two into `L·|Δθ|^α`.

The bridge between `DzG` (built from the *sanitised* family `gS α (tauExt g)`, extended to `z ≤ 0`
by `0`) and the family `GG α g = extG (gS α (tauExt g))` used by `st1_prelim` is
`DzG_eq_mul_pz_GG` below: `DzG α g z x τ = z · ∂_z (GG α g)` for `z > 0`, `τ ≥ 0`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

/-- **The bridge**: on `z > 0` and `τ ≥ 0`, `DzG α g z x τ` is `z` times the `∂_z`-slice of the
extended family `GG α g = extG (gS α (tauExt g))`. -/
theorem DzG_eq_mul_pz_GG {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ z : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (x : ℝ) :
    Work.FTS_RegExport.THL.DzG α g z x τ
      = z * Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXT.GG α g) τ) z x := by
  show z * deriv (fun z' => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' x τ) z
    = z * deriv (fun z' => Work.FTS_RegExport.RXT.GG α g z' x τ) z
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact (Work.FTS.RegPkgGal.extG_of_pos
    (g := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) hz' hτ).symm

/-- `DzG α g 0 x τ = 0`. -/
theorem DzG_zero_left (α : ℝ) (g : Work.FTS.Galerkin.Fam) (x τ : ℝ) :
    Work.FTS_RegExport.THL.DzG α g 0 x τ = 0 := by
  simp only [Work.FTS_RegExport.THL.DzG, Work.Spaces.Dz, zero_mul]

theorem DzG_theta_mod {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S) (hK0 : 0 ≤ K)
    (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DzG α g z θ τ - Work.FTS_RegExport.THL.DzG α g z θ' τ|
          ≤ L * |θ - θ'| ^ α := by
  obtain ⟨L, hL0, hL⟩ := Work.FTS_RegExport.RXT.theta_modulus_uniform_fb (α := α) (C := K) (K := K)
    hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [DzG_zero_left α g θ τ, DzG_zero_left α g θ' τ, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · refine hL (u := fun x => Work.FTS_RegExport.THL.DzG α g z x τ)
      (u' := fun x => z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x)
      ?_ ?_ ?_ θ hθ θ' hθ'
    · -- differentiability of the `θ`-slice
      intro x hx
      have hc4 : ContDiffAt ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (z, x) :=
        ((hmin.c4 τ hτ.1).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (z, x) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) from ⟨hzpos, hx.1, hx.2⟩))).of_le
          (by norm_num)
      have hd : HasDerivAt
          (fun x' => Work.Spaces.pz
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXT.GG α g) τ) z x')
          (Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) x :=
        (Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta hc4).congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
          exact Work.FTS_RegExport.RXT.pz_GG_eq α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩)
      exact (hd.const_mul z).congr_of_eventuallyEq (by
        filter_upwards with x'
        exact (DzG_eq_mul_pz_GG hτ.1 hzpos x'))
    · -- the derivative bound `|∂_θ(D_z g̃)| ≤ K·Γ/sin 2θ`
      intro x hx
      have hsin : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
      have h4 := hw (4 : Fin 6) τ hτ z x hzpos hx.1 hx.2
      norm_num [Work.FTS.RegExportIface.RXT.idx] at h4
      have hid : Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x
          = z * (Real.sin (2 * x)
              * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) :=
        Work.FTS_RegExport.RXT.mixed_one_one_eq _ z x
      have hkey : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
            * Real.sin (2 * x)) * z ≤ K * Work.FTS.Regularity.Gamma α x := by
        have h1 : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z
            = |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x| := by
          rw [hid]
          simp only [abs_mul, abs_of_pos hzpos, abs_of_pos hsin]
          ring
        rw [h1]
        exact le_trans h4 (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le ⟨hx.1.le, hx.2.le⟩) hK0)
      have hkey' : (z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|)
            * Real.sin (2 * x) ≤ K * Work.FTS.Regularity.Gamma α x := by
        have e : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z
            = (z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|)
              * Real.sin (2 * x) := by ring
        rw [← e]; exact hkey
      calc |z * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
          = z * |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x| := by
            rw [abs_mul, abs_of_pos hzpos]
        _ ≤ K * (Work.FTS.Regularity.Gamma α x / Real.sin (2 * x)) := by
            rw [← mul_div_assoc]
            exact (le_div_iff₀ hsin).mpr hkey'
    · -- the value bound `|D_z g̃| ≤ K·Γ`
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
      · subst hx0
        rw [DzG_eq_mul_pz_GG hτ.1 hzpos 0,
          Work.FTS_RegExport.RXT.pz_GG_eq_zero_left α hτ.1 hzpos hv, mul_zero, abs_zero]
        exact mul_nonneg hK0 (Work.ConstructionInstance.Gamma_nonneg hx)
      · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
        · subst hxπ
          rw [DzG_eq_mul_pz_GG hτ.1 hzpos (π / 2),
            Work.FTS_RegExport.RXT.pz_GG_eq_zero_right α hτ.1 hzpos hv, mul_zero, abs_zero]
          exact mul_nonneg hK0 (Work.ConstructionInstance.Gamma_nonneg hx)
        · rw [DzG_eq_mul_pz_GG hτ.1 hzpos x, Work.FTS_RegExport.RXT.pz_GG_eq α hτ.1 hzpos hx]
          have h1 := hw (1 : Fin 6) τ hτ z x hzpos hxpos hxlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
          have h1' : |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
              ≤ K * Work.FTS.RegExportIface.ω α z x := by
            simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
              Work.Spaces.DthIter_zero, Work.Spaces.Dz] using h1
          exact le_trans h1' (mul_le_mul_of_nonneg_left
            (Work.FTS_RegExport.RXT.omega_le_Gamma α z x hzpos.le hx) hK0)

end Work.FTS_RegExport.THL.L
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_l12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

/-- **The `D_z`-jets of `L₁₂(F_τ)` and of `𝔽K(F_τ)` for the profile `F_τ = F_* + slice g τ`.**

For a family `g` of the strong route (`DynOK'`) and every fake time `τ ≥ 0` there is a constant
`CL > 0` such that

* `|D_z^k (L₁₂ F_τ)(z)| ≤ CL` for `k ≤ 3` and `z > 0`,
* `|D_z^j (𝔽K F_τ)(z)| ≤ CL` for `j ≤ 2` and `z > 0`,
* the iterates `D_z^c (L₁₂ F_τ)` (`c ≤ 2`) and `D_z^b (𝔽K F_τ)` (`b ≤ 1`) are differentiable on
  `(0,∞)`, and
* the level-one identity `z ∂_z (L₁₂ F_τ)(z) = -(𝔽K F_τ)(z)` holds for `z > 0`. -/
theorem theta_part_l12 {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ CL : ℝ, 0 < CL ∧
      (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z| ≤ CL) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z| ≤ CL) ∧
      (∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp a) g τ) z)) z) ∧
      (∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z => Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp a) g τ) z)) z) ∧
      (∀ z : ℝ, 0 < z → z * deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z') z
          = -Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) := by
  intro τ hτ
  set α : ℝ := Work.FTS.Regularity.pExp a with hαdef
  have hαG : 0 < α := by rw [hαdef]; exact Work.FTS.Regularity.pExp_pos ha
  have hαG1 : α ≤ 1 := by rw [hαdef]; exact Work.FTS.Regularity.pExp_le_one ha13
  set h : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ with hh
  have h4 : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0 := by
    rw [hh]; exact hOK.1.1.c4 τ hτ
  have hHk : Work.Spaces.HkMem α 4 h := by rw [hh]; exact hOK.1.1.mem4 τ hτ
  ---------------------------------------------------------------------------------------------
  -- the weighted jet bound for the slice
  ---------------------------------------------------------------------------------------------
  obtain ⟨Cw, hCw0, hCw⟩ := Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved hαG hαG1
    hOK.2 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  have hJet : Work.FTS_RegExport.RXT.Slots.JetBnd Cw h :=
    fun b a hab z θ hz hθ0 hθ1 => hCw τ hτT b a hab z θ hz hθ0 hθ1
  have hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k h z θ| ≤ Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
    fun k hk z θ hz hθ0 hθ1 => hJet k 0 (by omega) z θ hz hθ0 hθ1
  ---------------------------------------------------------------------------------------------
  -- the two `Qang`-derivatives and the tower for the slice
  ---------------------------------------------------------------------------------------------
  have hQA0 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang h 0) (Work.Elliptic.Qang h 1 w / w) w :=
    fun w hw => Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hCw0 h4 hJet hw
  have hQA1 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang h 1) (Work.Elliptic.Qang h 2 w / w) w :=
    fun w hw => Work.FTS_RegExport.RXT.Slots.QangOneDeriv_jet hCw0 h4 hJet hw
  have hTower_h : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 h z) z
        = -Work.Elliptic.Qang h (j - 1) z := by
    intro j hj1 hj3 z hz
    refine Work.FTS_RegExport.RXT.L12Iter.DzdIter_L12_eq_neg_Qang hCw0 h4 hbd ?_ hj1 hj3 hz
    exact fun {k : ℕ} hk {w : ℝ} hw => by
      interval_cases k
      · exact hQA0 w hw
      · exact hQA1 w hw
  have hL12h_level1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) z
        = -Work.Elliptic.Qang h 0 z := fun z hz => hTower_h 1 le_rfl (by norm_num) z hz
  ---------------------------------------------------------------------------------------------
  -- value additivity of `L₁₂` and the `F_*`-identity
  ---------------------------------------------------------------------------------------------
  have hval : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftau α g τ) w
        = Work.Construction.L12 (Work.Construction.Fstar α) w + Work.Construction.L12 h w := by
    intro w hw
    rw [hh]
    exact Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hαG hαG1 h4 hHk hw.le
  have hFstar_eq : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Fstar α) w = 2 * α / (1 + w) :=
    fun w hw => Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
  ---------------------------------------------------------------------------------------------
  -- differentiability of the iterates of the two pieces
  ---------------------------------------------------------------------------------------------
  have hcdFstar : ContDiffOn ℝ 3
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have hinv : ContDiffOn ℝ 3 (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi 0) := by
      refine ContDiffOn.inv (by fun_prop) ?_
      intro z hz
      simp only [Set.mem_Ioi] at hz
      positivity
    have hmain : ContDiffOn ℝ 3 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
      refine ((contDiffOn_const (c := 2 * α)).mul hinv).congr (fun z _ => ?_)
      rw [div_eq_mul_inv]
    exact hmain.congr (fun z hz => hFstar_eq z hz)
  have hFstar_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)) z := by
    intro c hc z hz
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter c]
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
      (hcdFstar.of_le (Nat.cast_le.mpr (by omega : c + 1 ≤ 3))) hz
  have hL12h_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 h z)) z := by
    intro c hc z hz
    interval_cases c
    · exact (Work.FTS_RegExport.RXT.L12Iter.Construction_L12_hasDerivAt hCw0 h4 hbd hz).differentiableAt
    · have hev : (fun w => Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) w)
          =ᶠ[𝓝 z] fun w => -(Work.Elliptic.Qang h 0 w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        simpa using hL12h_level1 w hw
      rw [hev.differentiableAt_iff]
      exact (hQA0 z hz).differentiableAt.neg
    · have hev : (fun w => Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 h z) w)
          =ᶠ[𝓝 z] fun w => -(Work.Elliptic.Qang h 1 w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        simpa using hTower_h 2 (by norm_num) (by norm_num) w hw
      rw [hev.differentiableAt_iff]
      exact (hQA1 z hz).differentiableAt.neg
  have hL12F_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)) z := by
    intro c hc z hz
    have hev1 : (fun w => Work.Elliptic.DzdIter c
          (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) w)
        =ᶠ[𝓝 z] fun w => Work.Elliptic.DzdIter c ((fun z => Work.Construction.L12
            (Work.Construction.Fstar α) z) + (fun z => Work.Construction.L12 h z)) w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval c w hw
    have hev2 : (fun w => Work.Elliptic.DzdIter c ((fun z => Work.Construction.L12
            (Work.Construction.Fstar α) z) + (fun z => Work.Construction.L12 h z)) w)
        =ᶠ[𝓝 z] fun w => Work.Elliptic.DzdIter c (fun z => Work.Construction.L12
              (Work.Construction.Fstar α) z) w
            + Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 h z) w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff c _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') w hw
    rw [hev1.differentiableAt_iff, hev2.differentiableAt_iff]
    exact (hFstar_diff c (by omega) z hz).add (hL12h_diff c hc z hz)
  ---------------------------------------------------------------------------------------------
  -- the jet bounds
  ---------------------------------------------------------------------------------------------
  obtain ⟨Cfs, hCfs0, hCfs⟩ := L12Fstar_jets'
  obtain ⟨Cmaj, hCmajpos, hmajall⟩ := majorant_sqrt_tail'
  have hmaj : ∀ z : ℝ, 0 < z →
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ Cmaj :=
    fun z hz => (hmajall z hz).2
  obtain ⟨Ch, hCh0, hCh⟩ := L12_slice_jets_le (Cw := Cw) (Cmaj := Cmaj) hCw0 hCmajpos.le h4 hJet hmaj
  set CL : ℝ := Cfs * α + Ch with hCL
  have hCLpos : 0 < CL := by rw [hCL]; have := mul_pos hCfs0 hαG; linarith
  have hFstar_jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
        ≤ Cfs * α := by
    intro k hk z hz
    have hj := hCfs α hαG hαG1 k hk z hz
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) k z 0] at hj
    exact hj
  have hh_jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z| ≤ Ch := by
    intro k hk z hz
    have hj := hCh k hk z hz
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 h z) k z 0] at hj
    exact hj
  have hL12F_jetD : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z|
        ≤ CL := by
    intro k hk z hz
    have h1 : Work.Elliptic.DzdIter k (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) z
        = Work.Elliptic.DzdIter k ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval k z hz
    have h2 : Work.Elliptic.DzdIter k ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) z
        = Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          + Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff k _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') z hz
    rw [h1, h2]
    calc |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          + Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z|
        ≤ |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
          + |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z| := abs_add_le _ _
      _ ≤ CL := by rw [hCL]; linarith [hFstar_jet k hk z hz, hh_jet k hk z hz]
  ---------------------------------------------------------------------------------------------
  -- the level-one identity for the full profile and the `𝔽K`-jets
  ---------------------------------------------------------------------------------------------
  have hL12Fstar_level1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
        = -(2 * α) * z / (1 + z) ^ 2 := by
    intro z hz
    have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar α) w)
        =ᶠ[𝓝 z] fun w => 2 * α / (1 + w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact hFstar_eq w hw
    show z * deriv (fun w => Work.Construction.L12 (Work.Construction.Fstar α) w) z
      = -(2 * α) * z / (1 + z) ^ 2
    rw [hev.deriv_eq, deriv_const_div_one_add (2 * α) z (by
      have hz' : (0 : ℝ) < z := hz
      linarith)]
    ring
  have hFK_split : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.FK (Work.Construction.Ftau α g τ) w
        = Work.Construction.FK (Work.Construction.Fstar α) w + Work.Construction.FK h w := by
    intro w hw
    rw [hh]
    refine Work.FTS.GalFields.Tail.FK_Fstar_add (α := α) (u := Work.FTS.Galerkin.slice g τ) ?_ hw
    intro z hz
    have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * h z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.FTS_RegExport.RXT.L12Iter.integrable_Ktheta_mul_DzIter hCw0 h4 hbd (k := 0)
        (by norm_num) hz
    have h2 : Integrable (fun θ => h z θ * Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) :=
      hint.congr (Filter.Eventually.of_forall (fun θ => by
        rw [Work.Elliptic.Ktheta_eq_K]; ring))
    rw [hh] at h2
    exact h2
  have hFK_eq_neg : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.FK (Work.Construction.Ftau α g τ) w
        = -(Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) w) := by
    intro w hw
    have h1 : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) w
        = Work.Elliptic.DzdIter 1 ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) w :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval 1 w hw
    have h2 : Work.Elliptic.DzdIter 1 ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) w
        = Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) w
          + Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) w :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff 1 _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') w hw
    rw [h1, h2, hL12Fstar_level1 w hw, hL12h_level1 w hw, hFK_split w hw,
      Work.FTS.Nonlinear.FstarPkg.FK_Fstar hαG hαG1, Qang_zero_eq_FK h w]
    ring
  have hL12d : ∀ z : ℝ, 0 < z → z * deriv (fun z' => Work.Construction.L12
      (Work.Construction.Ftau α g τ) z') z = -Work.Construction.FK
        (Work.Construction.Ftau α g τ) z := by
    intro z hz
    have h := hFK_eq_neg z hz
    rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
        (Work.Construction.Ftau α g τ) z) z
      = z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α g τ) z') z from rfl] at h
    linarith [h]
  have hFK_jet : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
        (Work.Construction.Ftau α g τ) z) z| ≤ CL := by
    intro j hj z hz
    have h1 : Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
          (Work.Construction.Ftau α g τ) z) z
        = Work.Elliptic.DzdIter j (fun z => -(Work.Elliptic.DzdIter 1
            (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hFK_eq_neg j z hz
    rw [h1, DzdIter_neg j (fun z => Work.Elliptic.DzdIter 1
      (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)]
    rw [← DzdIter_succ_eq j (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)]
    rw [abs_neg]
    exact hL12F_jetD (j + 1) (by omega) z hz
  have hFK_diff : ∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
        (Work.Construction.Ftau α g τ) z)) z := by
    intro b hb z hz
    have hev : (fun w => Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
          (Work.Construction.Ftau α g τ) z) w)
        =ᶠ[𝓝 z] fun w => -(Work.Elliptic.DzdIter (b + 1)
            (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have h1 : Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
            (Work.Construction.Ftau α g τ) z) w
          = Work.Elliptic.DzdIter b (fun z => -(Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hFK_eq_neg b w hw
      have h2 : Work.Elliptic.DzdIter b (fun z => -(Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w
          = -(Work.Elliptic.DzdIter b (Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)) w) :=
        congrFun (DzdIter_neg b (fun z => Work.Elliptic.DzdIter 1
          (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w
      rw [h1, h2]
      exact congrArg Neg.neg (congrFun (DzdIter_succ_eq b (fun z => Work.Construction.L12
        (Work.Construction.Ftau α g τ) z)) w).symm
    rw [hev.differentiableAt_iff]
    exact (hL12F_diff (b + 1) (by omega) z hz).neg
  exact ⟨CL, hCLpos, hL12F_jetD, hFK_jet, hL12F_diff, hFK_diff, hL12d⟩

end

end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.Epart_dz_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Epart_dz_bound` — the near-`0` bound for the `U`-slot of the elliptic part

Target: for `α = 3a ∈ (0,1]`, a horizon datum `slice g τ` of a `DynOK'`-family and the elliptic
solution `E (slice g τ)`, the `z`-derivative of the `U`-slot
`Uop α (PhiTil α (slice g τ) (E (slice g τ))) / sin 2θ` is of size `O(z)` on the open quadrant
for `z ≤ 1`.

The route is the weighted `ℋ⁴ → L^∞` trade-off `RXT.v2_hkMem_pointwise_min` applied to the
class-`C` approximants `slice (gn n) τ` of the approximation scheme `LimApprox` (a conjunct of
`DynOK'`), followed by a limit.  The limit needs the *identification* of the `z`-derivative of
the `U`-slot at a point in terms of the mixed jets of the elliptic solution and the angular
moments `Qang` of the datum (the file `SB4/Aux/Dz_Epart_eq.lean`), together with the pointwise
convergence of the mixed jets (`EllLimOK3`) and of the angular moments
(`RXT.Slots.QangTendsto_conv`).
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The `U`-slot of a datum: `Uop α (PhiTil α F Φ) / sin 2θ`. -/
def Uslot (α : ℝ) (F Φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ / Work.Construction.s2 θ

/-- **The general form of `Epart_dz_bound`**, with the profile exponent as a free parameter
`α ∈ (0,1]` (the target is the instance `α = pExp a = 3a`). -/
theorem Epart_dz_bound_gen {α C₀ Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 α E)
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ))) z θ| ≤ K * z := by
  intro τ hτ
  -- the approximation scheme at the horizon `τ + 1`
  obtain ⟨gn, B, Lc, hC, hLip, hjet, hmu⟩ := hOK.2 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  -- the weighted `ℋ⁴ → L^∞` transfer constant
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved (β := α) hα hα1
  -- the ℋ⁴-bound of the scheme is nonnegative, hence so is the jet constant
  have hX0 : 0 ≤ Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn 0) τ) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  have hC0sq : 0 ≤ C₀ * α ^ 2 := le_trans hX0 (hC 0 τ hτT).2.1
  have hC0nn : 0 ≤ Cw * (C₀ * α ^ 2) := mul_nonneg hCw0 hC0sq
  -- regularity of the approximants and of the limit
  have hF4n : ∀ n : ℕ, ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ)) Work.FTS.EllipticEst.Q0 :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hC n τ hτT).1.reg 4
  have hF4L : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  -- the pointwise jet bound `JetBnd`, with a constant uniform in `n` and for the limit
  have hJetN : ∀ n : ℕ, Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2))
      (Work.FTS.Galerkin.slice (gn n) τ) := by
    intro n b a hab z θ hz h0 h1
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open (hC n τ hτT).1.reg 4 (by norm_num) (hC n τ hτT).1.mem
    have htr : Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) (hC n τ hτT).1.tr
    have h1' := hCw _ (hF4n n) hmem htr b a hab z θ hz h0 h1
    have h2 : Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * α ^ 2 :=
      (hC n τ hτT).2.1
    have hw : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
      div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1'
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * α ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw)
      _ = (Cw * (C₀ * α ^ 2)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hJetL : Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2))
      (Work.FTS.Galerkin.slice g τ) :=
    Work.FTS_RegExport.RXT.Slots.JetBnd.of_tendsto hJetN
      (fun b a hab z θ hz h0 h1 => hjet τ hτT b a (by omega) z θ ⟨hz, h0, h1⟩)
  -- the elliptic limit closure along the scheme
  obtain ⟨-, hEdiff, hEconv⟩ := hEL (fun n => Work.FTS.Galerkin.slice (gn n) τ)
    (Work.FTS.Galerkin.slice g τ) B (fun n => (hC n τ hτT).1) (fun n => (hC n τ hτT).2.2)
    hF4L (fun j i hji z θ hzθ => hjet τ hτT j i hji z θ hzθ)
  -- the angular density of any datum of the class is continuous, so the `L₁₂`-tower and the
  -- `z`-derivative of `Qang · 0` are available
  have hcontD : ∀ F : ℝ → ℝ → ℝ, ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0 →
      Work.FTS_RegExport.RXT.Slots.JetBnd (Cw * (C₀ * α ^ 2)) F →
        ContinuousOn (fun s => Work.Elliptic.L12dens F s) (Set.Ioi 0) := by
    intro F h4 hb
    refine ContinuousOn.congr (s := Set.Ioi 0)
      (f := fun s => Work.Elliptic.Qang F 0 s / s)
      (g := fun s => Work.Elliptic.L12dens F s) ?_ ?_
    · intro s hs
      exact ((Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn h4 hb hs).continuousAt.div
        continuousAt_id (ne_of_gt hs)).continuousWithinAt
    · intro s _
      exact Work.Elliptic.L12dens_eq_Qang_div F s
  -- the pointwise transfer constant
  obtain ⟨Cpt, hCpt0, hCpt⟩ :=
    Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min (α := α) hα hα1
  let M : ℝ := max (Ce * (C₀ * α ^ 2)) 0
  let K : ℝ := max (Cpt * M) 0
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK0, ?_⟩
  intro z θ hzθ hz1
  obtain ⟨hz, h0, h1⟩ :=
    Work.FTS.EllipticEst.mem_Q0.mp (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from hzθ)
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, h1⟩
  -- (1) the pointwise bound, uniformly in `n`
  have hbound : ∀ n : ℕ, |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ| ≤ K * z := by
    intro n
    obtain ⟨hGo, -⟩ := hEll (Work.FTS.Galerkin.slice (gn n) τ) (hC n τ hτT).1
    have hsm : Work.FTS.EllipticEst.SmoothOpen (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := hGo.U.1.1
    have hmem4 : Work.Spaces.HkMem α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := hGo.U.1.2
    have hM : Work.Spaces.HkNorm α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) ≤ M := by
      have h1 := hGo.U.2
      have h2 : Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * α ^ 2 :=
        (hC n τ hτT).2.1
      rcases le_or_gt 0 Ce with hCe | hCe
      · exact le_trans (le_trans h1 (mul_le_mul_of_nonneg_left h2 hCe)) (le_max_left _ _)
      · have h3 : Ce * Work.Spaces.HkNorm α 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hCe.le (Work.Spaces.HkNorm_nonneg α 4 _)
        exact le_trans (le_trans h1 h3) (le_max_right _ _)
    have hpt := hCpt (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)))
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4) hmem4 1 0 (by norm_num) z θ
      hz h0 h1
    have hpt' : |Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ|
        ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) := by
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using hpt
    have hmin : min z 1 = z := min_eq_left hz1
    have hstep : Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ))) ≤ Cpt * z * M := by
      rw [hmin]
      exact mul_le_mul_of_nonneg_left hM (mul_nonneg hCpt0 hz.le)
    have hK' : Cpt * z * M ≤ K * z := by
      have h : Cpt * M ≤ K := le_max_left _ _
      have heq : Cpt * z * M = (Cpt * M) * z := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right h hz.le
    exact le_trans (le_trans hpt' hstep) hK'
  -- (2) the identification of the `z`-derivative at a point, for every approximant and in the limit
  have keyN : ∀ n : ℕ, Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ
      = (-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
          - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z := by
    intro n
    have hsm : Work.FTS.EllipticEst.SmoothOpen (E (Work.FTS.Galerkin.slice (gn n) τ)) :=
      (hEll (Work.FTS.Galerkin.slice (gn n) τ) (hC n τ hτT).1).1.smooth
    have hC2 : ContDiffOn ℝ 2 (Function.uncurry (E (Work.FTS.Galerkin.slice (gn n) τ)))
        Work.FTS.EllipticEst.Q0 := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 2
    have hcont := hcontD (Work.FTS.Galerkin.slice (gn n) τ) (hF4n n) (hJetN n)
    refine Dz_Epart_eq (α := α) (ne_of_gt hα)
      (F := Work.FTS.Galerkin.slice (gn n) τ)
      (Φ := E (Work.FTS.Galerkin.slice (gn n) τ)) hz hθmem hC2 ?_ ?_
    · intro z' hz'
      exact Work.FTS_RegExport.RXT.Slots.Construction_L12_hasDerivAt_jet hC0nn (hJetN n) hcont hz'
    · exact Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn (hF4n n) (hJetN n) hz
  have keyL : Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ))) z θ
      = (-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
          - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z := by
    have hC2 : ContDiffOn ℝ 2 (Function.uncurry (E (Work.FTS.Galerkin.slice g τ)))
        Work.FTS.EllipticEst.Q0 := hEdiff.of_le (by norm_num)
    have hcont := hcontD (Work.FTS.Galerkin.slice g τ) hF4L hJetL
    refine Dz_Epart_eq (α := α) (ne_of_gt hα) hz hθmem hC2 ?_ ?_
    · intro z' hz'
      exact Work.FTS_RegExport.RXT.Slots.Construction_L12_hasDerivAt_jet hC0nn hJetL hcont hz'
    · exact Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0nn hF4L hJetL hz
  -- (3) convergence of the identified expression
  have hq0 : Tendsto (fun n : ℕ => Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z)
      atTop (𝓝 (Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z)) :=
    Work.FTS_RegExport.RXT.Slots.QangTendsto_conv (C0 := Cw * (C₀ * α ^ 2)) hC0nn hF4n hJetN hJetL
      (fun b a hab z' θ' hz' h0' h1' => hjet τ hτT b a (by omega) z' θ' ⟨hz', h0', h1'⟩)
      (k := 0) (by norm_num) hz
  have hq1 : Tendsto (fun n : ℕ => Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z)
      atTop (𝓝 (Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z)) :=
    Work.FTS_RegExport.RXT.Slots.QangTendsto_conv (C0 := Cw * (C₀ * α ^ 2)) hC0nn hF4n hJetN hJetL
      (fun b a hab z' θ' hz' h0' h1' => hjet τ hτT b a (by omega) z' θ' ⟨hz', h0', h1'⟩)
      (k := 1) (by norm_num) hz
  have hAB : Tendsto (fun n : ℕ => (-3 * Work.Spaces.mixed 1 0
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
        / Work.Construction.s2 θ) atTop
      (𝓝 ((-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
        / Work.Construction.s2 θ)) :=
    (((hEconv 1 0 (by norm_num) z θ hzθ).const_mul (-3)).sub
      ((hEconv 2 0 (by norm_num) z θ hzθ).const_mul α)).div_const (Work.Construction.s2 θ)
  have hexpr : Tendsto (fun n : ℕ => (-3 * Work.Spaces.mixed 1 0
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)
        / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice (gn n) τ) 1 z) atTop
      (𝓝 ((-3 * Work.Spaces.mixed 1 0 (E (Work.FTS.Galerkin.slice g τ)) z θ
        - α * Work.Spaces.mixed 2 0 (E (Work.FTS.Galerkin.slice g τ)) z θ)
        / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 z
        - (1 / 4) * Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 1 z)) :=
    (hAB.sub (hq0.const_mul (3 / (4 * α)))).sub (hq1.const_mul (1 / 4))
  have hconv : Tendsto (fun n : ℕ => Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice (gn n) τ)
      (E (Work.FTS.Galerkin.slice (gn n) τ))) z θ) atTop
      (𝓝 (Work.Spaces.Dz (Uslot α (Work.FTS.Galerkin.slice g τ)
        (E (Work.FTS.Galerkin.slice g τ))) z θ)) := by
    rw [keyL]
    exact hexpr.congr' (Eventually.of_forall (fun n => (keyN n).symm))
  exact le_of_tendsto (hconv.abs) (Eventually.of_forall (fun n => hbound n))

theorem Epart_dz_bound {a C₀ Ce : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ))) z θ / Work.Construction.s2 θ) z θ| ≤ K * z := by
  intro τ hτ
  exact Epart_dz_bound_gen (Work.FTS.Regularity.pExp_pos ha)
    (Work.FTS.Regularity.pExp_le_one ha13) hEll hEL hOK τ hτ

end Work.FTS_StreamBdry.SB4
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

/-- The pointwise bound on the low-order jets of the slices of `g`, in the exact shape of
`Work.FTS_RegExport.RXT.Slots.JetBnd`: for every fake time `τ ≥ 0`,
`|D_z^b D_θ^a (slice g τ)(z,θ)| ≤ C · z^{3/2}/(1+z)²` on the open quadrant, whenever
`a + b ≤ 2`.

This is the `LimApprox`-clause of `DynOK'` fed through the weighted limit transfer
`RXA2w.lim_mixed_weighted_proved`; the constant depends on the horizon `τ + 1` only, which is
harmless because the target statement is a pointwise differentiability statement. -/
theorem slice_jetBnd {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 ≤ C ∧ Work.FTS_RegExport.RXT.Slots.JetBnd C (Work.FTS.Galerkin.slice g τ) := by
  have hα : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : Work.FTS.Regularity.pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  obtain ⟨C, hC0, hCb⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved hα hα1 hOK.2 (τ + 1) (by linarith)
  exact ⟨C, hC0, fun b a hab z θ hz h0 h1 =>
    hCb τ ⟨hτ, by linarith⟩ b a hab z θ hz h0 h1⟩

/-- The angular density `s ↦ L₁₂dens (slice g τ) s` of a slice of `g` is continuous on `(0,∞)`.

It is `Qang (slice g τ) 0 s / s` (`Elliptic.L12dens_eq_Qang_div`), and `Qang (slice g τ) 0` is
differentiable on `(0,∞)` with derivative `Qang (slice g τ) 1 s / s`
(`RXT.Slots.QangZeroDeriv_jet`, differentiation under the angular integral). -/
theorem slice_L12dens_continuousOn {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ContinuousOn (fun s => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) s) (Ioi 0) := by
  obtain ⟨C, hC0, hJet⟩ := slice_jetBnd ha ha13 hOK τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  refine ContinuousOn.congr (s := Ioi 0)
    (f := fun s => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 s / s)
    (g := fun s => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) s) ?_ ?_
  · intro s hs
    exact ((Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0 h4 hJet hs).continuousAt.div
      continuousAt_id (ne_of_gt hs)).continuousWithinAt
  · intro s _
    exact Work.Elliptic.L12dens_eq_Qang_div (Work.FTS.Galerkin.slice g τ) s

theorem slice_L12_c2 {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) w)
        (-(Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) z)) z ∧
      DifferentiableAt ℝ (fun w => Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) w) z := by
  intro τ hτ z hz
  obtain ⟨C, hC0, hJet⟩ := slice_jetBnd ha ha13 hOK τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 τ hτ
  have hcont := slice_L12dens_continuousOn ha ha13 hOK τ hτ
  -- the fundamental theorem of calculus for the tail integral `z ↦ ∫_z^∞ L₁₂dens`
  have hint : IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) s)
      (Ioi (z / 2)) :=
    hJet.dens_integrable hC0 hcont (by linarith)
  have hderiv : HasDerivAt
      (fun σ => Work.FM.L12 Work.Spaces.K (Work.FTS.Galerkin.slice g τ) σ)
      (-(Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) z)) z :=
    Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K)
      (f := Work.FTS.Galerkin.slice g τ) (a := z / 2) (ρ := z) hint
      (fun s _ => hcont.continuousAt (isOpen_Ioi.mem_nhds (show (0 : ℝ) < s by linarith)))
      (by linarith)
  refine ⟨?_, ?_⟩
  · -- `L₁₂` is the fundamental-model operator with `K = 3 sin θ cos²θ`
    simpa only [Work.Construction.L12, Work.Construction.L12dens] using hderiv
  · -- the density is `Qang · 0 / s`, and `Qang · 0` is differentiable on `(0,∞)`
    have hd : DifferentiableAt ℝ
        (fun w => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 w / w) z :=
      (Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hC0 h4 hJet hz).differentiableAt.div
        differentiableAt_id (ne_of_gt hz)
    have hcongr : (fun w => Work.Elliptic.L12dens (Work.FTS.Galerkin.slice g τ) w)
        =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang (Work.FTS.Galerkin.slice g τ) 0 w / w) :=
      Eventually.of_forall fun w =>
        Work.Elliptic.L12dens_eq_Qang_div (Work.FTS.Galerkin.slice g τ) w
    have h'' : DifferentiableAt ℝ
        (fun w => Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g τ) w) z :=
      hd.congr_of_eventuallyEq hcongr
    exact h''

end Work.FTS_StreamBdry.SB4
end
