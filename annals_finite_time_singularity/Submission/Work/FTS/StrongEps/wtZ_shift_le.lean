import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_mixed_mul_le_4
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ddDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz pz)

local notation "Iθ" => Work.Spaces.Iθ

set_option maxHeartbeats 4000000

/-- The three-image kernel of the doubly odd extension is dominated by the all-plus kernel. -/
theorem Kern_le_KJ {ε θ s : ℝ} (hε : 0 < ε) :
    ‖Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s‖ ≤ Work.FTS.EllSol.EllPkgAux.KJ ε θ s := by
  have h1 : (0 : ℝ) ≤ sKer ε (θ - s) := sKer_nonneg hε _
  have h2 : (0 : ℝ) ≤ sKer ε (θ + s) := sKer_nonneg hε _
  have h3 : (0 : ℝ) ≤ sKer ε (θ + s - Real.pi) := sKer_nonneg hε _
  have h4 : ‖sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)‖
      ≤ ‖sKer ε (θ - s) - sKer ε (θ + s)‖ + ‖sKer ε (θ + s - Real.pi)‖ :=
    norm_sub_le _ _
  have h5 : ‖sKer ε (θ - s) - sKer ε (θ + s)‖ ≤ sKer ε (θ - s) + sKer ε (θ + s) := by
    have h := norm_sub_le (sKer ε (θ - s)) (sKer ε (θ + s))
    simpa only [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] using h
  have h6 : ‖sKer ε (θ + s - Real.pi)‖ = sKer ε (θ + s - Real.pi) :=
    Real.norm_of_nonneg h3
  have hKJ : Work.FTS.EllSol.EllPkgAux.KJ ε θ s
      = sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := rfl
  have hKn : Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s
      = sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi) := rfl
  rw [hKJ, hKn]
  linarith [h4, h5, h6]

/-- The `Kern`-integral of a fixed slice is dominated by the `KJ`-kernel against its modulus. -/
theorem Kern_integral_le {X : ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε) (hX : IntegrableOn X Iθ) :
    ‖∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s * X s‖
      ≤ ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖X s‖ := by
  have hKJcont : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s) := by
    have hker : Continuous (sKer ε) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
    have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
      hker.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
      hker.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
      hker.comp ((continuous_const.add continuous_id).sub continuous_const)
    have hsum : Continuous (fun s : ℝ =>
        sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := (h1.add h2).add h3
    simpa only [Work.FTS.EllSol.EllPkgAux.KJ] using hsum
  have hXint : IntegrableOn (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖X s‖) Iθ :=
    IntegrableOn.continuousOn_mul hKJcont.continuousOn hX.norm isCompact_Icc
  have hKcont : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s) := by
    have hker : Continuous (sKer ε) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).continuous
    exact ((hker.comp (continuous_const.sub continuous_id)).sub
      (hker.comp (continuous_const.add continuous_id))).sub
      (hker.comp ((continuous_const.add continuous_id).sub continuous_const))
  have hKint : IntegrableOn (fun s : ℝ => ‖Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s
      * X s‖) Iθ := by
    refine (IntegrableOn.continuousOn_mul hKcont.norm.continuousOn hX.norm
      isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro s _
    exact (norm_mul _ _).symm
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on hKint hXint measurableSet_Icc (fun s _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (Kern_le_KJ hε) (norm_nonneg _)

/-- The log-convolution of a function dominated by `Φ` is dominated by the log-convolution
of `Φ`. -/
theorem znorm_le {Ψ Φ : ℝ → ℝ} {δ z : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ t : ℝ, ‖Ψ t‖ ≤ Φ t)
    (hΦ : Integrable (fun t : ℝ => sKer δ (Real.log z - t) * Φ t) volume) :
    ‖∫ t : ℝ, sKer δ (Real.log z - t) * Ψ t‖
      ≤ ∫ t : ℝ, sKer δ (Real.log z - t) * Φ t := by
  calc ‖∫ t : ℝ, sKer δ (Real.log z - t) * Ψ t‖
      ≤ ∫ t : ℝ, ‖sKer δ (Real.log z - t) * Ψ t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, sKer δ (Real.log z - t) * ‖Ψ t‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [norm_mul, Real.norm_of_nonneg (sKer_nonneg hδ _)]
    _ ≤ ∫ t : ℝ, sKer δ (Real.log z - t) * Φ t := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t =>
            mul_nonneg (sKer_nonneg hδ _) (norm_nonneg _)) hΦ
          (Filter.Eventually.of_forall fun t =>
            mul_le_mul_of_nonneg_left (hΨ t) (sKer_nonneg hδ _))

/-- **Pointwise domination of the `D_z²`-slot of the log-mollified datum.**

For `G` in the trace class (`TraceClass`) with honest functionals (`FourInts`), `δ, ε ∈ (0,1/2]`,
put `Φ := zmoll G δ ε`.  Then for a.e. `z > 0` and every `θ ∈ Iθ` the second `D_z`-derivative of
`Φ` is dominated by the doubly-odd-mollified `D_z²G`:

  `|D_z²Φ(z,θ)| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |D_z²G (e^t) s| ds) dt`,

where `KJ ε θ s = sKer ε (θ-s) + sKer ε (θ+s) + sKer ε (θ+s-π)`.

Intended route.  (i) *θ-fold*, a.e. in `w`:
`D_z^j (thMoll G ε) w θ = ∫_{Iθ} km ε θ s · D_z^j G w s ds` for `j ≤ 2`, where
`km ε θ s = sKer ε (θ-s) - sKer ε (θ+s) - sKer ε (θ+s-π)` (this is `D_z^j` of the folded
representation `thMoll G ε w θ = ∫_{Iθ} km ε θ s G w s ds`; the joint integrability needed for
the Fubini argument, `∫_{a}^{b}∫_{Iθ}|D_z^j G| < ∞` for `0 < a ≤ b`, follows from `SliceHonestOpen G`
and `FourInts G` by Cauchy–Schwarz in `θ` against `σ^{-1} = sin(2·)^{2η} ∈ L¹(Iθ)`).
(ii) *log-mollification commutation*, a.e. in `z`:
`D_z^j (zmoll G δ ε) z θ = ∫_t sKer δ (log z - t) · D_z^j (thMoll G ε) (e^t) θ dt` for `j ≤ 2`
(substitute `t = log z - u` and integrate by parts in `u`; all boundary terms vanish because
`sKer δ` has compact support).
(iii) *glue*: the failure set of (i) is null, and the `t`-kernel has compact support, so the two
`t`-integrals agree for a.e. `z`; `|km| ≤ KJ` gives the stated bound.  Every `t`- and
`s`-integral is finite for every `z > 0` because the window `[z e^{-δ}, z e^{δ}]` is compact in
`(0,∞)` and the box integrability of (i) applies there.

Sources to reuse: `Work.FTS.EllSol.EllPkgAux.thMoll_abs_le` (the `j = 0` fold), `KJ`,
`KJ_nonneg`, `KJ_le`, `KJ_mass`, `integrableOn_sq_of_integrableOn`. -/
theorem zmoll_ddDom (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ|
          ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
              (∫ s in Work.Spaces.Iθ,
                Work.FTS.EllSol.EllPkgAux.KJ ε θ s *
                |Work.Spaces.Dz (Work.Spaces.Dz G) (Real.exp t) s|) := by
  have hε0 : (0 : ℝ) < ε := hP.1
  have hδ0 : (0 : ℝ) < δ := hP.2.2.1
  obtain ⟨-, -, -, -, -, -, hsd7⟩ := slice_data hT
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun z hz => ?_
  intro θ hθ
  have hid := zmoll_dz2_eq G hT hF δ ε hP z hz θ hθ
  have hmain := znorm_le (Ψ := fun t : ℝ => ∫ s in Iθ,
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ s * Dz (Dz G) (Real.exp t) s)
    (Φ := fun t : ℝ => ∫ s in Iθ,
        Work.FTS.EllSol.EllPkgAux.KJ ε θ s * ‖Dz (Dz G) (Real.exp t) s‖) hδ0
    (fun t => Kern_integral_le hε0 (hsd7 (Real.exp t) (Real.exp_pos t)))
    (KJ_ddG_integrable_mine hT hF hδ0 hP.2.2.2 hε0 hP.2.1 hz)
  rw [hid]
  exact hmain

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.trunc_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/trunc_identity` — the truncated `I₁` chain identity

The target is the paper's `I₁` chain identity (Step 2 of `prop:H2` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021))

in the weak class `H2W.Ae.AeData`, in the form in which the *radial* cut-off `χ_k = cut k`
and the *angular* cut-off `χ_ε = SliceMixedAux.cut ε` (with `ε = 1/(k+1)`) are kept, and
written as a `z`-outer iterated integral whose inner `θ`-integrand still carries the radial
cut-off.  With `U = z∂_zu`, `V = z∂_z∂_θu`, `Hh = z∂_z∂_θθu`, `AA = z²∂_zzu`,
`BB = ∂_θθu`, `cw z = 2(z-1)/(1+z)`, `w z = (1+z)²/z²`, `σ = sigE = sin(2θ)^{-η}`,
`σ₁ = sig1 = sin(2θ)^{-1-η}`, `Fp u = AA·BB + cw·U·BB + U·Hh` and
`Fd u = z·(z∂_zu)·∂_θθu·w²` (the two `z`-integrands of the pointwise identity
`∂_z Fd = w² Fp`), the identity is

```
∫_z χ_k w² ∫_θ σ χ_ε (AA·BB + cw·U·BB)
  = -∫_z (z χ_k') w² ∫_θ σ χ_ε (U·BB)      -- radial IBP
    + ∫_z χ_k w² ∫_θ σ χ_ε V²               -- angular IBP
    - 2η ∫_z χ_k w² ∫_θ σ₁ χ_ε (U V cos 2θ) -- angular IBP
    + ∫_z χ_k w² ∫_θ σ χ_ε' (U V)           -- angular IBP
```

## Route

* `I1Ae.zibpChain` (proved elsewhere) is the radial integration by parts of
  `∂_z Fd = w² Fp` against `χ_k` in *double*-integral form, with the angular weight
  `σ χ_ε` inserted;
* `I1Ae.thetaChain` (proved elsewhere) is the angular integration by parts of
  `∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η U·V cos 2θ σ₁` against `χ_ε`, again in double form;
* on the compact box `[1/(2(k+1)), 4(k+1)] × [ε/2, π/2 - ε/2]` both the `Fp u`- and the
  `U u·Hh u`-integrand are continuous and compactly supported, hence summable for
  `dz dθ`; this is what allows the double integral of
  `w²σ χ_k χ_ε (AA·BB + cw·U·BB) = w²σ χ_k χ_ε (Fp u - U u·Hh u)` to be split;
* finally every double integral is converted back to the `z`-outer form of the statement
  by the (unconditional) pull-out of the `z`-dependent constant out of the `θ`-integral.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Integrability helpers -/



/-! ## Joint continuity of the elementary factors on the open quadrant -/








/-! ## The two elementary integrability facts -/




/-! ## Splitting the truncated integrand along `Fp u = (AA·BB + cw·U·BB) + U·Hh` -/


/-! ## Converting between the `z`-outer form and the double-integral form -/







/-! ## The target -/


end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.PzJepsEndpointTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- `bump` vanishes in an angular neighbourhood of the endpoint `θ = 0`: its angular cut-off
`thCut` is supported on `[π/4, 3π/8]`. -/
theorem bump_eq_zero_of_lt_pi_div_four (z θ : ℝ) (hθ : θ < Real.pi / 4) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump, Work.FTS.StrongEps.thCut,
    Real.smoothTransition.zero_of_nonpos (show θ - Real.pi / 4 ≤ 0 by linarith),
    zero_mul, mul_zero]

/-- `bump` vanishes in an angular neighbourhood of the endpoint `θ = π/2`. -/
theorem bump_eq_zero_of_lt_pi_three_eighths (z θ : ℝ) (hθ : 3 * Real.pi / 8 < θ) :
    Work.FTS.StrongEps.bump z θ = 0 := by
  rw [Work.FTS.StrongEps.bump, Work.FTS.StrongEps.thCut,
    Real.smoothTransition.zero_of_nonpos (show 3 * Real.pi / 8 - θ ≤ 0 by linarith),
    mul_zero, mul_zero]

/-- The projection `Pz` differs from the identity by a multiple of `bump`, which is supported
away from the angular endpoints, so it does not change the angular traces at `θ = 0` and
`θ = π/2`. -/
theorem Pz_eq_self_near_angular_endpoints {f : Work.FTS.Galerkin.Fn} {z : ℝ} :
    (∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.FTS.StrongEps.Pz f z θ = f z θ) ∧
    (∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.FTS.StrongEps.Pz f z θ = f z θ) := by
  constructor
  · filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
        (show (0 : ℝ) < Real.pi / 4 by linarith [Real.pi_pos]))] with θ hθ
    rw [Work.FTS.StrongEps.Pz_apply, bump_eq_zero_of_lt_pi_div_four z θ hθ, mul_zero, sub_zero]
  · filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (3 : ℝ) * Real.pi / 8 < Real.pi / 2 by linarith [Real.pi_pos]))] with θ hθ
    rw [Work.FTS.StrongEps.Pz_apply, bump_eq_zero_of_lt_pi_three_eighths z θ hθ, mul_zero,
      sub_zero]

theorem PzJepsEndpointTrace {α : ℝ} (hα : 0 < α) {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {δ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ))) :
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hγ : 1 < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  -- the `BdryTraces` clause of the class, at the slot `(a, b) = (0, 0)`
  have hbdry := hg.tr 0 0 (by norm_num)
  constructor
  · intro z hz
    have hPz : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ) z θ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        using (hbdry.2 z hz).1
    have hJ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε δ z θ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.Tendsto.congr' (Pz_eq_self_near_angular_endpoints (f := Work.FTS.StrongEps.Jeps ρ ε δ)
        |>.1.mono fun θ hθ => by rw [hθ]) hPz
    exact Work.FTS.ClassC.tendsto_of_sin_rpow_sq hγ
      (Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])) hJ
  · intro z hz
    have hPz : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ) z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        using (hbdry.2 z hz).2
    have hJ : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.FTS.StrongEps.Jeps ρ ε δ z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      Filter.Tendsto.congr' (Pz_eq_self_near_angular_endpoints (f := Work.FTS.StrongEps.Jeps ρ ε δ)
        |>.2.mono fun θ hθ => by rw [hθ]) hPz
    exact Work.FTS.ClassC.tendsto_of_sin_rpow_sq hγ
      (Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])) hJ

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Positivity of `pzNorm = L₁₂(bump)(0)`

`pzNorm = ∫_{0}^{∞} ∫_{0}^{π/2} K(θ) bump(s,θ)/s dθ ds`.  The angular integrand `K θ · bump s θ / s`
is nonnegative everywhere (the profile `bump` is nonnegative and the weight `K = 3 sin θ cos²θ` is
nonnegative on the support window `(π/4, 3π/8)` of `bump` in `θ`), and it is *strictly* positive on
the rectangle `(5/8, 7/8) × (π/4, 3π/8)`, a set of positive measure contained in the domain of
integration.  Hence the double integral is strictly positive.

The only analytic ingredient is the continuity of the *parameter* integral
`s ↦ ∫_θ K θ · bump s θ / s` on `(0,∞)`, which follows from the parametric-continuity lemma
`continuousOn_integral_of_compact_support` (the integrand is jointly continuous where `s ≠ 0`,
vanishes for `θ` outside the compact support window `[0, π/2]` of `bump` in `θ`, and the parameter
`s > 0` keeps the division regular).
-/

namespace PzNormAux

/-! ### Elementary nonnegativity of the angular weight -/

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on `[0, π/2]`. -/
theorem K_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  nlinarith [h1, h2]

/-- `K(θ) = 3 sin θ cos²θ > 0` on `(0, π/2)`. -/
theorem K_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-! ### The angular integrand of `L₁₂dens K bump` -/

/-- The angular integrand `(s,θ) ↦ K θ · bump s θ / s` of `L₁₂dens K bump`. -/
def KB (s θ : ℝ) : ℝ := Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s

/-- `KB` vanishes for `θ` outside the angular window `Iθ = [0, π/2]` (the support of `bump` in `θ`
is `[π/4, 3π/8] ⊂ Iθ`). -/
theorem KB_eq_zero_of_not_mem_Iθ {s θ : ℝ} (hθ : θ ∉ Work.Spaces.Iθ) : KB s θ = 0 := by
  have hth : Work.FTS.StrongEps.bump s θ = 0 := by
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    rw [Work.Spaces.Iθ, Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with h | h
    · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
    · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
  rw [KB, hth, mul_zero, zero_div]

/-- `KB` is nonnegative everywhere: off the support of `bump` it vanishes, and on the support
`K θ > 0`, `bump s θ > 0` and `s > 0`. -/
theorem KB_nonneg (s θ : ℝ) : 0 ≤ KB s θ := by
  rcases eq_or_ne (Work.FTS.StrongEps.bump s θ) 0 with hb | hb
  · rw [KB, hb, mul_zero, zero_div]
  · have hbpos : 0 < Work.FTS.StrongEps.bump s θ :=
      lt_of_le_of_ne (Work.FTS.StrongEps.bump_nonneg s θ) (Ne.symm hb)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.bump_ne_zero_iff.mp hb
    have hK : 0 < Work.Spaces.K θ :=
      K_pos ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    rw [KB]
    exact le_of_lt (div_pos (mul_pos hK hbpos) (by linarith [hz.1]))

/-! ### The angular density as a parameter integral -/

/-- `L₁₂dens K bump s` is the full-line parameter integral of `KB s`. -/
theorem L12dens_eq (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = ∫ θ, KB s θ := by
  rw [Work.FM.L12dens]
  rw [show (fun θ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      = (fun θ => KB s θ) from rfl]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun θ hθ => KB_eq_zero_of_not_mem_Iθ hθ)

/-- Continuity of the parameter integral `s ↦ ∫_θ K θ · bump s θ / s` on `(0, ∞)`. -/
theorem continuousOn_Kbump_integral :
    ContinuousOn (fun s => ∫ θ, KB s θ) (Set.Ioi 0) := by
  refine continuousOn_integral_of_compact_support (μ := volume) (s := Set.Ioi 0)
    (k := Work.Spaces.Iθ) isCompact_Icc ?_ ?_
  · have hKcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      simp only [Work.Spaces.K]; fun_prop
    have hBcont : Continuous (fun p : ℝ × ℝ => Work.FTS.StrongEps.bump p.1 p.2) :=
      (Work.FTS.StrongEps.contDiff_bump 1).continuous
    exact ((hKcont.mul hBcont).continuousOn).div continuous_fst.continuousOn
      (fun p hp => ne_of_gt hp.1)
  · intro p x _ hx
    exact KB_eq_zero_of_not_mem_Iθ hx

/-- `L₁₂dens K bump` is continuous on `(0, ∞)`. -/
theorem continuousOn_L12dens :
    ContinuousOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Ioi 0) :=
  continuousOn_Kbump_integral.congr (fun s _ => L12dens_eq s)

/-! ### Nonnegativity and vanishing -/

/-- `L₁₂dens K bump` is nonnegative. -/
theorem L12dens_nonneg (s : ℝ) :
    0 ≤ Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
  rw [L12dens_eq s]
  exact integral_nonneg (fun θ => KB_nonneg s θ)

/-- `L₁₂dens K bump` vanishes where the radial cut-off `zCut` does (i.e. off `(1/2, 1)`). -/
theorem L12dens_eq_zero_of_zCut_zero {s : ℝ}
    (hs : Work.FTS.StrongEps.zCut s = 0) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 := by
  rw [L12dens_eq s]
  have h : (fun θ => KB s θ) = fun _ => (0 : ℝ) := by
    funext θ
    have : Work.FTS.StrongEps.bump s θ = 0 := by
      rw [Work.FTS.StrongEps.bump, hs, zero_mul]
    rw [KB, this, mul_zero, zero_div]
  rw [h, integral_zero]

theorem L12dens_eq_zero_of_le {s : ℝ} (hs : s ≤ 1 / 2) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 :=
  L12dens_eq_zero_of_zCut_zero (Work.FTS.StrongEps.zCut_eq_zero_iff.mpr (Or.inl hs))

theorem L12dens_eq_zero_of_ge {s : ℝ} (hs : 1 ≤ s) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 :=
  L12dens_eq_zero_of_zCut_zero (Work.FTS.StrongEps.zCut_eq_zero_iff.mpr (Or.inr hs))

/-! ### Strict positivity on the inner box -/

/-- `L₁₂dens K bump s > 0` for `s ∈ (5/8, 7/8)`: the angular integrand is nonnegative, integrable on
`Iθ`, and strictly positive on the angular box `(π/4, 3π/8)`, a set of positive measure. -/
theorem L12dens_pos_of_inner {s : ℝ} (hs : s ∈ Set.Ioo ((5 : ℝ) / 8) (7 / 8)) :
    0 < Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
  rw [L12dens_eq s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Work.Spaces.Iθ) (fun θ hθ => KB_eq_zero_of_not_mem_Iθ hθ)]
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun θ => KB_nonneg s θ)) ?_).mpr ?_
  · have hKs : Continuous (fun θ => Work.Spaces.K θ) := by
      simp only [Work.Spaces.K]; fun_prop
    have hbs : Continuous (fun θ => Work.FTS.StrongEps.bump s θ) :=
      (Work.FTS.StrongEps.contDiff_bump 1).continuous.comp
        (continuous_const.prodMk continuous_id)
    exact ((hKs.mul hbs).div_const s).integrableOn_Icc
  · have hsub : Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) ⊆
        Function.support (fun θ => KB s θ) ∩ Work.Spaces.Iθ := by
      intro θ hθ
      refine ⟨?_, ?_⟩
      · rw [Function.mem_support]
        have hbpos : 0 < Work.FTS.StrongEps.bump s θ :=
          Work.FTS.StrongEps.bump_pos_iff.mpr
            ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hθ⟩
        have hK : 0 < Work.Spaces.K θ :=
          K_pos ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
        have hspos : 0 < s := by linarith [hs.1]
        intro hzero
        rw [KB] at hzero
        have : 0 < Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s :=
          div_pos (mul_pos hK hbpos) hspos
        linarith
      · rw [Work.Spaces.Iθ, Set.mem_Icc]
        exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hpos : 0 < (volume : Measure ℝ) (Set.Ioo (Real.pi / 4) (3 * Real.pi / 8)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    exact lt_of_lt_of_le hpos (measure_mono hsub)

/-! ### Integrability on `(0, ∞)` and positivity of the supporting set -/

/-- `L₁₂dens K bump` is integrable on `(0, ∞)`: it is continuous there and supported in the compact
interval `[1/2, 1]`. -/
theorem integrableOn_L12dens :
    IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Ioi 0) := by
  have hIcc : IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Icc ((1 : ℝ) / 2) 1) :=
    (continuousOn_L12dens.mono
      (fun s hs => lt_of_lt_of_le (by norm_num) hs.1)).integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc ((1 : ℝ) / 2) 1).indicator
      (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hIcc
  have hEq : (Set.Icc ((1 : ℝ) / 2) 1).indicator
        (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      =ᵐ[volume] (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s) := by
    refine Eventually.of_forall (fun s => ?_)
    by_cases hs : s ∈ Set.Icc ((1 : ℝ) / 2) 1
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h | h
      · exact (L12dens_eq_zero_of_le (le_of_lt h)).symm
      · exact (L12dens_eq_zero_of_ge (le_of_lt h)).symm
  exact (hind.congr hEq).integrableOn

/-- The supporting set of `L₁₂dens K bump` inside `(0, ∞)` has positive measure: it contains the
interval `(5/8, 7/8)` on which the function is strictly positive. -/
theorem support_L12dens_pos :
    0 < (volume : Measure ℝ)
      (Function.support (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
        ∩ Set.Ioi 0) := by
  have hsub : Set.Ioo ((5 : ℝ) / 8) (7 / 8) ⊆
      Function.support (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
        ∩ Set.Ioi 0 := by
    intro s hs
    exact ⟨by rw [Function.mem_support]; exact ne_of_gt (L12dens_pos_of_inner hs),
      by rw [Set.mem_Ioi]; linarith [hs.1]⟩
  have hpos : 0 < (volume : Measure ℝ) (Set.Ioo ((5 : ℝ) / 8) (7 / 8)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  exact lt_of_lt_of_le hpos (measure_mono hsub)

end PzNormAux

theorem pzNorm_pos : 0 < Work.FTS.StrongEps.pzNorm := by
  have hpz : Work.FTS.StrongEps.pzNorm =
      ∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
    rw [Work.FTS.StrongEps.pzNorm, Work.Construction.L12, Work.FM.L12]
  rw [hpz]
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun s => PzNormAux.L12dens_nonneg s))
    PzNormAux.integrableOn_L12dens).mpr PzNormAux.support_L12dens_pos

end Work.FTS.StrongEps.PZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-! ## Elementary trigonometric and algebraic helpers

The whole statement reduces to the classical identity `sin (2 arctan x) = 2x / (1 + x²)` together
with the (elementary, but sign-sensitive) inequality

`q · 2t/(1+t²) ≤ 2tq/(1+t²q²) ≤ q⁻¹ · 2t/(1+t²)` for `0 < q ≤ 1` (and its reverse for `q ≥ 1`),

which is `q² ≤ 1` in disguise. -/

/-- **`sin (2·)` at an arctangent**: `sin (2 arctan x) = 2x / (1 + x²)`. -/
theorem sin_two_arctan (x : ℝ) : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hsin : Real.sin (Real.arctan x) = x * Real.cos (Real.arctan x) := by
    have h := Real.tan_arctan x
    rw [Real.tan_eq_sin_div_cos] at h
    field_simp at h
    rw [h, mul_comm]
  rw [Real.sin_two_mul, hsin,
    show (2 : ℝ) * (x * Real.cos (Real.arctan x)) * Real.cos (Real.arctan x)
      = 2 * x * Real.cos (Real.arctan x) ^ 2 from by ring, Real.cos_sq_arctan]
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  field_simp

/-- The algebraic core for the *lower* case `0 < q ≤ 1`: multiplication by `2t/(1+t²) > 0` sends
the factor `min q q⁻¹ = q` to the factor `q · (1+t²)/(1+t²q²)`, which lies between `q` and `q⁻¹`. -/
theorem tan_shift_bounds_le {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (h1 : q ≤ 1) :
    q * (2 * t / (1 + t ^ 2)) ≤ 2 * t * q / (1 + t ^ 2 * q ^ 2) ∧
      2 * t * q / (1 + t ^ 2 * q ^ 2) ≤ q⁻¹ * (2 * t / (1 + t ^ 2)) := by
  have hsq : q ^ 2 ≤ 1 := by nlinarith
  constructor
  · field_simp
    nlinarith [sq_nonneg t]
  · field_simp
    nlinarith [sq_nonneg t]

/-- The algebraic core for the *upper* case `1 ≤ q` (the mirror of `tan_shift_bounds_le`). -/
theorem tan_shift_bounds_ge {t q : ℝ} (ht : 0 < t) (hq : 0 < q) (h1 : 1 ≤ q) :
    q⁻¹ * (2 * t / (1 + t ^ 2)) ≤ 2 * t * q / (1 + t ^ 2 * q ^ 2) ∧
      2 * t * q / (1 + t ^ 2 * q ^ 2) ≤ q * (2 * t / (1 + t ^ 2)) := by
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  constructor
  · field_simp
    nlinarith [sq_nonneg t]
  · field_simp
    nlinarith [sq_nonneg t]

/-- **`sin (2·)` changes by a bounded factor under the `θ`-shift.**  For `θ ∈ (0, π/2)` and every
`p : ℝ`, the shifted angle `thShift θ p = arctan (tan θ * Real.exp (-p))` satisfies
`e^{-|p|} sin (2 θ) ≤ sin (2 (thShift θ p)) ≤ e^{|p|} sin (2 θ)`.
Equivalently `sin (2 (thShift θ p)) / sin (2 θ) = e^{-p} (1 + tan²θ) / (1 + tan²θ · e^{-2p})`.
This is the `p₂`-half of the weight-shift bound for the angular weight `sin (2θ)^{-γ}` of the
weighted spaces `ℋ^k` of the Elgindi project. -/
theorem sinTwo_thShift_bounds {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.exp (-|p|) * Real.sin (2 * θ) ≤ Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ∧
      Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ≤ Real.exp |p| * Real.sin (2 * θ) := by
  have htp : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have hqp : 0 < Real.exp (-p) := Real.exp_pos _
  have hsinφ : Real.sin (2 * Work.FTS.StrongEps.thShift θ p)
      = 2 * Real.tan θ * Real.exp (-p) / (1 + Real.tan θ ^ 2 * Real.exp (-p) ^ 2) := by
    simp only [Work.FTS.StrongEps.thShift]
    rw [sin_two_arctan]
    ring
  have hsinθ : Real.sin (2 * θ) = 2 * Real.tan θ / (1 + Real.tan θ ^ 2) := by
    have hθar : θ = Real.arctan (Real.tan θ) :=
      (Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2).symm
    conv_lhs => rw [hθar]
    exact sin_two_arctan _
  have hexp : Real.exp p = (Real.exp (-p))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [hsinφ, hsinθ]
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    have hq1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    obtain ⟨hlo, hhi⟩ := tan_shift_bounds_le htp hqp hq1
    exact ⟨hlo, by rw [hexp]; exact hhi⟩
  · rw [abs_of_nonpos hp, neg_neg, hexp]
    have hq1 : 1 ≤ Real.exp (-p) := Real.one_le_exp_iff.mpr (by linarith)
    obtain ⟨hlo, hhi⟩ := tan_shift_bounds_ge htp hqp hq1
    exact ⟨hlo, hhi⟩

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.wtZ_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-! ## The elementary `z`-algebra

`w z = (1 + z)²/z² = (1 + 1/z)²`, so under `z ↦ z e^{-p}` we have
`w (z e^{-p}) = (1 + (1/z) e^{p})²`: the whole shift bound is the statement that
`1 + (1/z) e^{p} ≤ e^{|p|} (1 + 1/z)`, which holds because `e^{p} ≤ e^{|p|}` and `1 ≤ e^{|p|}`. -/



end Work.FTS.StrongEps
end
