import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.LeafShiftCSLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

/- Cauchy–Schwarz for the `k ≥ 5` group of the `L₁₂·D_θ` slot expansion.

Context: `IsLeafW α a ρ` says `ρ` is one of the three leaf weights
`w(z)²sin(2θ)^{-η}`, `w(z)²`, `w(z)²sin(2θ)^{-γ}` (the last only when `a ≥ 1`);
`HkNorm α k f = √(HkSq α k f)`; `HkSq α k` is the weighted ℋ^k energy
(`HkIntegrand α k` contains, for every slot `(i,j)` with `1 ≤ i`, `i + j ≤ k`, the term
`(D_z^jD_θ^if·Wt α z θ)²` with `(Wt α z θ)² = w(z)²sin(2θ)^{-γ}`, and for every `i ≤ k` the
term `(D_z^if·w(z)/sin(2θ)^{η/2})²`).

Claim: for `f` smooth on the open quadrant with honest `ℋ⁶`-integral, `a + b ≤ 6`,
`5 ≤ k ≤ b` and a leaf weight `ρ` of the slot `a`, the `ρ`-weighted pairing of the two slots
`D_z^{b-k}D_θ^{a+1}f` and `D_z^bD_θ^a f` is bounded by `C·|f|_{ℋ⁴}·|f|_{ℋ⁶}`.

Route: the two slots have orders `(b-k)+(a+1) ≤ a+b-4 ≤ 2` and `a+b ≤ 6`, and
`ρ ≤ slotW α aᵢ` for both slot indices `aᵢ ∈ {a, a+1}` (the `γ`-leaf only occurs with
`1 ≤ a`, and `a ≤ aᵢ`).  Hence `ρ·(D_z^{i}D_θ^{j}f)² ≤ HkIntegrand α m f` for the two slots, so
`∫∫ρU² ≤ HkSq α 2 f` and `∫∫ρV² ≤ HkSq α 6 f`; two Cauchy–Schwarz applications
(`Work.Blocks.IMC.cs_integral_mul_le` for the product measure, or the iterated form via
`abs_integral_le_integral_abs` + `integral_mono_of_nonneg`) give
`∫_z|∫_θ ρUV| ≤ ∫∫ρ|U||V| ≤ √(HkSq α 2 f)·√(HkSq α 6 f) ≤ HkNorm α 4 f·HkNorm α 6 f`
(monotonicity `HkSq α 2 ≤ HkSq α 4`).  a.e. strong measurability comes from continuity on the
open quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), and the measure is
`(volume.restrict Iz).prod (volume.restrict Iθ)` (`Measure.prod_restrict`).

**Implementation note (the constant is `1`).**  The proof runs the two-level
Cauchy–Schwarz argument of `slotCS_z` (whose `cs_sqrt_le_fts`, `leaf_prod_sqrt_le`,
`leaf_nonneg_Iθ`, `leaf_sq_le4`, `leaf_sq_le6` are reused verbatim), with the first slot
shifted: because the two slots here are `U = D_z^{b-k}D_θ^{a+1}f` and `V = D_z^bD_θ^af`,
the first one is dominated by `HkIntegrand α 4 f` through `leaf_sq_le4` applied to the slot
index `a+1` — which is legitimate since `IsLeafW α a ρ` implies `IsLeafW α (a+1) ρ` (the
`γ`-leaf is the only `a`-dependent case, and `1 ≤ a → 1 ≤ a+1`) — and the second one by
`HkIntegrand α 6 f` through `leaf_sq_le6`.  Both square-root factors are then combined in
the angular slice and, after a second Cauchy–Schwarz, in `z`, giving
`√(HkSq α 4 f)·√(HkSq α 6 f) = HkNorm α 4 f·HkNorm α 6 f`.  The a.e. estimability is
supplied by `ae_restrict_Iθ_of_Ioo`/`ae_restrict_of_forall_mem` throughout, and no
monotonicity of `HkSq` is needed. -/
theorem LeafShiftCSLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b k : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.TransportS.IsLeafW α a ρ → 5 ≤ k → k ≤ b → a + b ≤ 6 →
      (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ|)
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α hαI f a b k ρ hso hmem hleaf hk hkb hab
  obtain ⟨hα, _hα1⟩ := hαI
  -- the level-four honesty of `f`, which the shifted slot needs
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hmem
  -- `ρ` is also a leaf weight of the (*shifted*) slot index `a + 1`
  have hleaf' : Work.FTS.TransportS.IsLeafW α (a + 1) ρ := by
    rcases hleaf with h | h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Nat.le_succ_of_le h1, h2⟩)
  have habk : a + 1 + (b - k) ≤ 4 := by omega
  let U : ℝ → ℝ → ℝ := Work.Spaces.mixed (b - k) (a + 1) f
  let V : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f
  let A : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 4 f z θ
  let B : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ
  change (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
    ≤ 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have h4nn : ∀ z θ, 0 ≤ A z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have h6nn : ∀ z θ, 0 ≤ B z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hAslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => A z θ) Work.Spaces.Iθ := hmem4.1
  have hBslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ := hmem.1
  have hAint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, A z θ) Work.Spaces.Iz := hmem4.2
  have hBint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz := hmem.2
  have hAnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, A z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h4nn z θ))
  have hBnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, B z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h6nn z θ))
  -- ## the angular slice estimate: the two slots are dominated by `A` resp. `B`
  have hsliceAll : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- at `z = 0` every leaf weight vanishes
      subst h0
      have hρ0 : ∀ θ : ℝ, ρ 0 θ = 0 := fun θ => by
        rcases hleaf with rfl | rfl | ⟨-, rfl⟩ <;>
          simp [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafOne,
            Work.FTS.TransportS.leafGam, Work.Spaces.w]
      have hzero : (fun θ : ℝ => ρ 0 θ * U 0 θ * V 0 θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hρ0 θ]; ring
      rw [hzero, integral_zero, abs_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · -- the open quadrant: pointwise domination and Cauchy–Schwarz on the slice
      have hstep1 : |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
          ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict Work.Spaces.Iθ) (fun θ : ℝ => ρ z θ * U z θ * V z θ))
      have hcongr : (∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ|)
          = ∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ| := by
        refine integral_congr_ae (ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_))
        simp only [abs_mul, abs_of_nonneg (leaf_nonneg_Iθ hleaf z θ hθ)]
      have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          ρ z θ * |U z θ| * |V z θ| ≤ Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
        Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => by
          refine leaf_prod_sqrt_le (leaf_nonneg_Iθ hleaf z θ ⟨le_of_lt h1, le_of_lt h2⟩) ?_ ?_
          · exact leaf_sq_le4 hα hleaf' habk hz0 ⟨h1, h2⟩
          · exact leaf_sq_le6 hα hleaf hab hz0 ⟨h1, h2⟩)
      have h4_meas : AEStronglyMeasurable (fun θ => Real.sqrt (A z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hAslice z hz).aestronglyMeasurable
      have h6_meas : AEStronglyMeasurable (fun θ => Real.sqrt (B z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hBslice z hz).aestronglyMeasurable
      have h4_sq : Integrable (fun θ => Real.sqrt (A z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
        (hAslice z hz).congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (h4nn z θ)).symm))
      have h6_sq : Integrable (fun θ => Real.sqrt (B z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
        (hBslice z hz).congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (h6nn z θ)).symm))
      have h4_lp : MemLp (fun θ => Real.sqrt (A z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h4_meas).mpr h4_sq
      have h6_lp : MemLp (fun θ => Real.sqrt (B z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h6_meas).mpr h6_sq
      have hprod : Integrable (fun θ => Real.sqrt (A z θ) * Real.sqrt (B z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        memLp_one_iff_integrable.mp (h4_lp.mul h6_lp)
      have hstep3 : (∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθm (fun θ hθ => mul_nonneg
            (mul_nonneg (leaf_nonneg_Iθ hleaf z θ hθ) (abs_nonneg _)) (abs_nonneg _)))
          hprod hpt
      have hstep4 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ))
          ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
        cs_sqrt_le_fts (hAslice z hz) (hBslice z hz)
          (fun θ => h4nn z θ) (fun θ => h6nn z θ)
      calc |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|
          ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * U z θ * V z θ| := hstep1
        _ = ∫ θ in Work.Spaces.Iθ, ρ z θ * |U z θ| * |V z θ| := hcongr
        _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) := hstep3
        _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := hstep4
  -- ## the radial Cauchy–Schwarz
  have houter_int : IntegrableOn (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable
    have h1sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hAint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hAnn z)).symm))
    have h2sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hBint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hBnn z)).symm))
    have h1lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have houter : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => abs_nonneg _)
      houter_int (ae_restrict_of_forall_mem hIzm hsliceAll)
  have hCS : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) :=
    cs_sqrt_le_fts hAint hBint hAnn hBnn
  calc (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ * U z θ * V z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) := hCS
    _ = 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq, one_mul]
        rfl

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

noncomputable section

/-- **The `k = 0` top term of the `T5b` row.** -/
theorem T5bZeroTerm_core {α : ℝ} {f : ℝ → ℝ → ℝ} {CL : ℝ} (hCLpos : 0 < CL)
    (hCL : ∀ k ≤ 4, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ CL * Work.Spaces.HkNorm α 4 f)
    (hψsm : ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0))
    (a b : ℕ) {σ : ℝ → ℝ}
    (hσcont : ContinuousOn (fun p : ℝ × ℝ => σ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hσnn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ σ θ)
    (hσcap : ∀ θ ∈ Set.Ioo 0 (π / 2),
      σ θ ≤ (Real.sin (2 * θ)) ^ (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α)))
    (hα : 0 < α) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
      ≤ 8 * CL * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
  set V : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed b a f z θ with hVdef
  set ψ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hψdef
  set θw : ℝ → ℝ := fun θ => σ θ * Work.Construction.c2m θ with hθwdef
  set q : ℝ := (if a = 0 then Work.Spaces.eta else Work.Spaces.gam α) with hqdef
  set Xn : ℝ := Work.Spaces.HkNorm α 4 f with hXndef
  set A : ℝ := CL * Xn with hAdef
  have hXn0 : 0 ≤ Xn := by rw [hXndef]; exact Work.Spaces.HkNorm_nonneg α 4 f
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hHk0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the ψ-bounds
  have hψA : ∀ z ∈ Set.Ioi (0:ℝ), |ψ z| ≤ A := by
    intro z hz
    have h := hCL 0 (by norm_num) z hz
    simpa using h
  have hψB : ∀ z ∈ Set.Ioi (0:ℝ), |z * deriv ψ z| ≤ A := by
    intro z hz
    have h := hCL 1 (by norm_num) z hz
    have h1 : Work.Elliptic.DzdIter 1 ψ z = z * deriv ψ z := rfl
    rw [h1] at h
    exact h
  have hψsm' : ContDiffOn ℝ 1 ψ (Set.Ioi 0) := by
    rw [hψdef]; exact hψsm
  have hψcOn : ContinuousOn ψ (Set.Ioi 0) := hψsm'.continuousOn
  have h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
        ≤ (3 * A + A) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    fun Y hY hF hD =>
      dzSelf1dW (ψ := ψ) (Y := Y) (A := A) (B := A) hA0 hA0 hψsm' hψA hψB hY hF hD
  -- ## measurability and slices
  have hσθm : AEMeasurable σ (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hc : ContinuousOn (fun θ : ℝ => σ θ) (Set.Ioo 0 (π / 2)) := by
      have h2 : ContinuousOn (fun θ : ℝ => ((1:ℝ), θ)) (Set.Ioo 0 (π / 2)) :=
        continuousOn_const.prodMk continuousOn_id
      exact (hσcont.comp h2 (fun θ hθ => ⟨by norm_num, hθ⟩)).congr (fun θ _ => rfl)
    rw [MeasureTheory.Measure.restrict_congr_set
      (Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Ith_ae)]
    exact hc.aemeasurable measurableSet_Ioo
  have hθwm : AEMeasurable θw (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have he : θw = fun θ => σ θ * Work.Construction.c2m θ := by rw [hθwdef]
    rw [he]
    exact hσθm.mul aemeasurable_c2m_Iθ
  have hqV : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), σ θ ≤ (Real.sin (2*θ)) ^ (-q) := by
    intro θ hθ
    rw [hqdef]
    exact hσcap θ hθ
  have hVc : ContinuousOn (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h2 : Function.uncurry V = Function.uncurry (Work.Spaces.mixed b a f) := by
      funext p; simp only [Function.uncurry, hVdef]
    rw [h2]
    exact (hsm.mixed b a).continuousOn
  have hWc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed (b+1) a f z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsm.mixed (b+1) a).continuousOn
  have hVslice : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0) := by
    intro θ hθ
    have h := Work.FTS.StrongPersist.H6Pair6Aux.SmoothOpen.slice (hsm.mixed b a) hθ 1
    have he : (fun z : ℝ => Work.Spaces.mixed b a f z θ) = fun z : ℝ => V z θ := by
      funext z; simp only [hVdef]
    rw [he] at h
    exact h
  have hVae : AEMeasurable (Function.uncurry V) Lprod :=
    (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry V) hVc).aemeasurable
  -- ## the ae-strongly-measurable factors
  have hwae : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
  have hσae : AEStronglyMeasurable (fun p : ℝ × ℝ => σ p.2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hσcont
  have hc2ae : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ continuousOn_c2m_Q0
  have hVae2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (V p.1 p.2)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hVc.pow 2)
  have hWae2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hWc.pow 2)
  have hψae : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.1) Lprod := by
    have hcon : ContinuousOn (fun p : ℝ × ℝ => ψ p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
      (hψcOn.comp continuousOn_fst (fun p hp => hp.1)).congr (fun p _ => rfl)
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcon
  have hθwae : AEStronglyMeasurable (fun p : ℝ × ℝ => |θw p.2|) Lprod := by
    have hcon : ContinuousOn (fun p : ℝ × ℝ => |θw p.2|)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
      have he : (fun p : ℝ × ℝ => |θw p.2|)
          = fun p : ℝ × ℝ => |σ p.2 * Work.Construction.c2m p.2| := by
        funext p; rw [hθwdef]
      rw [he]
      exact (hσcont.mul continuousOn_c2m_Q0).abs
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcon
  have hθw2 : AEStronglyMeasurable (fun p : ℝ × ℝ => θw p.2) Lprod := by
    have he : (fun p : ℝ × ℝ => θw p.2)
        = fun p : ℝ × ℝ => σ p.2 * Work.Construction.c2m p.2 := by
      funext p; rw [hθwdef]
    rw [he]
    exact hσae.mul hc2ae
  -- ## the slot majorants
  have hbigV : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q) * (V p.1 p.2)^2) Lprod := by
    rw [hqdef]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl]
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hsm hm6).1 b (by omega)
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hVdef, Work.Spaces.mixed_zero_right]
    · rw [if_neg ha0]
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 6 hsm hm6).2 b a ha1 hab
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hVdef]
  have hbigW : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q)
        * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod := by
    rw [hqdef]
    by_cases ha0 : a = 0
    · subst ha0
      rw [if_pos rfl]
      have h := (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hsm hm7).1 (b+1) (by omega)
      show MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter (b+1) f p.1 p.2)^2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      exact h
    · rw [if_neg ha0]
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      exact (Work.FTS.StrongPersist.H6Pair6Aux.slotProd α 7 hsm hm7).2 (b+1) a ha1 (by omega)
  have hσVint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (V p.1 p.2)^2) Lprod :=
    slot_sigma_integrable (X := V) hσcont hσnn hqV hVc hbigV
  have hσWint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) Lprod :=
    slot_sigma_integrable (X := fun z θ => Work.Spaces.mixed (b+1) a f z θ)
      hσcont hσnn hqV hWc hbigW
  have hZop : ∀ z θ, z * Work.Spaces.pz V z θ = Work.Spaces.mixed (b+1) a f z θ := by
    intro z θ
    simp only [hVdef, Work.Spaces.pz, Work.Spaces.mixed, Work.Spaces.DzIter_succ,
      Work.Spaces.Dz]
  -- ## the three integrability inputs of `dzSelf2dW`
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * |θw p.2| * (V p.1 p.2)^2) Lprod := by
    refine (hσVint.const_mul 2).mono' ?_ ?_
    · have he2 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2| * (V p.1 p.2)^2)
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => |θw p.2|)
            * (fun p : ℝ × ℝ => (V p.1 p.2)^2) := by
        funext p; rfl
      rw [he2]
      exact (hwae.mul hθwae).mul hVae2
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * |θw θ| * (V z θ)^2‖
            ≤ 2 * ((Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hθwa : |θw θ| ≤ 2 * σ θ := by
          rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
          (abs_nonneg _)) (sq_nonneg _))]
        calc (Work.Spaces.w z)^2 * |θw θ| * (V z θ)^2
            ≤ (Work.Spaces.w z)^2 * (2 * σ θ) * (V z θ)^2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hθwa (sq_nonneg _)) (sq_nonneg _)
          _ = 2 * ((Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  have hD2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * |θw p.2| * (p.1 * Work.Spaces.pz V p.1 p.2)^2) Lprod := by
    have he0 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
          * (p.1 * Work.Spaces.pz V p.1 p.2)^2)
        = fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
          * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2 := by
      funext p; rw [hZop p.1 p.2]
    rw [he0]
    refine (hσWint.const_mul 2).mono' ?_ ?_
    · have he2 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * |θw p.2|
            * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2)
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => |θw p.2|)
            * (fun p : ℝ × ℝ => (Work.Spaces.mixed (b+1) a f p.1 p.2)^2) := by
        funext p; rfl
      rw [he2]
      exact (hwae.mul hθwae).mul hWae2
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * |θw θ|
              * (Work.Spaces.mixed (b+1) a f z θ)^2‖
            ≤ 2 * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hθwa : |θw θ| ≤ 2 * σ θ := by
          rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
          (abs_nonneg _)) (sq_nonneg _))]
        calc (Work.Spaces.w z)^2 * |θw θ| * (Work.Spaces.mixed (b+1) a f z θ)^2
            ≤ (Work.Spaces.w z)^2 * (2 * σ θ) * (Work.Spaces.mixed (b+1) a f z θ)^2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hθwa (sq_nonneg _)) (sq_nonneg _)
          _ = 2 * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  have hcross : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * θw p.2 * ψ p.1
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)) Lprod := by
    have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => A *
        ((Work.Spaces.w p.1)^2 * σ p.2 * (Work.Spaces.mixed (b+1) a f p.1 p.2)^2
         + (Work.Spaces.w p.1)^2 * σ p.2 * (V p.1 p.2)^2)) Lprod :=
      (hσWint.add hσVint).const_mul A
    refine hmaj.mono' ?_ ?_
    · have hZae : AEStronglyMeasurable
          (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2) Lprod := by
        have he : (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2)
            = fun p : ℝ × ℝ => Work.Spaces.mixed (b+1) a f p.1 p.2 := by
          funext p; exact hZop p.1 p.2
        rw [he]
        exact Work.Spaces.aesm_of_continuousOn_Qd _ hWc
      have he3 : (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2 * θw p.2 * ψ p.1
            * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
          = (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) * (fun p : ℝ × ℝ => θw p.2)
            * (fun p : ℝ × ℝ => ψ p.1)
            * ((fun p : ℝ × ℝ => p.1 * Work.Spaces.pz V p.1 p.2)
              * (fun p : ℝ × ℝ => V p.1 p.2)) := by
        funext p; rfl
      rw [he3]
      exact ((hwae.mul hθw2).mul hψae).mul
        (hZae.mul (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry V) hVc))
    · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
          ‖(Work.Spaces.w z)^2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)‖
            ≤ A * ((Work.Spaces.w z)^2 * σ θ * (Work.Spaces.mixed (b+1) a f z θ)^2
              + (Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by
        intro θ hθ z hz
        have hσ0 : 0 ≤ σ θ := hσnn θ hθ
        have hψa : |ψ z| ≤ A := hψA z hz
        have hw : 0 ≤ (Work.Spaces.w z)^2 := sq_nonneg _
        set Z : ℝ := Work.Spaces.mixed (b+1) a f z θ with hZdef
        have hZe : |z * Work.Spaces.pz V z θ| = |Z| := by rw [hZop z θ, hZdef]
        have habs : ‖(Work.Spaces.w z)^2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)‖
            = (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
              * (|Z| * |V z θ|) := by
          have hθwu : θw θ = σ θ * Work.Construction.c2m θ := by rw [hθwdef]
          rw [Real.norm_eq_abs, hθwu]
          simp only [abs_mul, abs_of_nonneg hw, hZe]
          ring
        rw [habs]
        have hAM : 2 * (|Z| * |V z θ|) ≤ Z ^ 2 + (V z θ) ^ 2 := by
          nlinarith [sq_nonneg (|Z| - |V z θ|), sq_abs Z, sq_abs (V z θ)]
        have h1 : (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
            ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A := by
          have hσabs : |σ θ| = σ θ := abs_of_nonneg hσ0
          rw [hσabs]
          calc (Work.Spaces.w z)^2 * σ θ * |Work.Construction.c2m θ| * |ψ z|
              ≤ (Work.Spaces.w z)^2 * σ θ * 2 * |ψ z| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (abs_c2m_le_two θ) (by positivity))
                  (abs_nonneg _)
            _ ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A :=
                mul_le_mul_of_nonneg_left hψa (by positivity)
        calc (Work.Spaces.w z)^2 * |σ θ| * |Work.Construction.c2m θ| * |ψ z|
              * (|Z| * |V z θ|)
            ≤ (Work.Spaces.w z)^2 * σ θ * 2 * A * (|Z| * |V z θ|) :=
              mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = A * σ θ * ((Work.Spaces.w z)^2 * (2 * (|Z| * |V z θ|))) := by ring
          _ ≤ A * σ θ * ((Work.Spaces.w z)^2 * (Z ^ 2 + (V z θ) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAM hw) (by positivity)
          _ = A * ((Work.Spaces.w z)^2 * σ θ * Z ^ 2
              + (Work.Spaces.w z)^2 * σ θ * (V z θ)^2) := by ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt
  -- ## the two-dimensional Hardy input
  have hibp := dzSelf2dW (θw := θw) (ψ := ψ) (V := V) (D := 3 * A + A)
    (by linarith) h1d hθwm hVslice hVae hF hD2 hcross
  -- ## the target integral in the `IBP` form
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => integral_congr_ae
      (Filter.Eventually.of_forall fun θ => ?_))
    rw [hθwdef, hψdef, hVdef]
    simp only [Work.Spaces.pz, Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    ring
  -- ## the RHS bound
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2) ≤ 2 * Work.Spaces.HkSq α 6 f := by
    have hcap' : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), |θw θ| / 2
        ≤ (Real.sin (2*θ)) ^ (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α)) := by
      intro θ hθ
      have hσ0 : 0 ≤ σ θ := hσnn θ hθ
      have hθwa : |θw θ| ≤ 2 * σ θ := by
        rw [hθwdef]; exact thetaW_abs_le σ θ hσ0
      linarith [hσcap θ hθ]
    have hnn' : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 ≤ |θw θ| / 2 :=
      fun θ _ => by positivity
    have hkey : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := by
      by_cases ha0 : a = 0
      · subst ha0
        have hcap0 : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
            |θw θ| / 2 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) :=
          fun θ hθ => by simpa using hcap' θ hθ
        have h := (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).1 b (by omega)
          (fun θ => |θw θ| / 2) hnn' hcap0
        simpa only [hVdef, Work.Spaces.mixed_zero_right] using h
      · have hcapg : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
            |θw θ| / 2 ≤ (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
          intro θ hθ
          have h := hcap' θ hθ
          rwa [if_neg ha0] at h
        have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        exact (Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq α hm6).2 b a ha1 hab
          (fun θ => |θw θ| / 2) hnn' hcapg
    have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        2 * ((Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2))
        = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2) := by
      simp only [MeasureTheory.integral_const_mul]
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
        = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          2 * ((Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => integral_congr_ae
            (Filter.Eventually.of_forall fun θ => by ring))
      _ = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (|θw θ| / 2) * (V z θ) ^ 2) := hmain
      _ ≤ 2 * Work.Spaces.HkSq α 6 f := by linarith [hkey]
  -- ## assembly
  have hpow : Xn ≤ (1 + Xn) ^ 4 := by
    have h1 : (1:ℝ) ≤ 1 + Xn := by linarith
    calc Xn ≤ 1 + Xn := by linarith
      _ = (1 + Xn) ^ 1 := by ring
      _ ≤ (1 + Xn) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
          * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
      = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| := by
        rw [hgoal]
    _ ≤ (3 * A + A) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2) := hibp
    _ ≤ (3 * A + A) * (2 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hval (by linarith)
    _ = 8 * CL * Xn * Work.Spaces.HkSq α 6 f := by rw [hAdef]; ring
    _ ≤ 8 * CL * (1 + Xn) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        have h8H : 0 ≤ 8 * CL * Work.Spaces.HkSq α 6 f := by positivity
        have h8P : 0 ≤ 8 * CL * (1 + Xn) ^ 4 := by positivity
        have h1 := mul_le_mul_of_nonneg_left hpow h8H
        have h2 := mul_le_mul_of_nonneg_left
          (by linarith : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f) h8P
        nlinarith [h1, h2]
    _ = 8 * CL * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        rw [hXndef]


end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.slotCrossLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000


end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZCS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1600000

set_option quotPrecheck false in
local notation "PMq" => (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- **The weighted Cauchy–Schwarz inequality in `L²`** for the product measure. -/
lemma leafGamPureZ_cs {ρ A B : ℝ → ℝ → ℝ}
    (hρ : ∀ᵐ p ∂PMq, 0 ≤ ρ p.1 p.2)
    (hA2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (A p.1 p.2) ^ 2) PMq)
    (hB2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) PMq)
    (hA : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) PMq)
    (hB : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => B p.1 p.2) PMq)
    (hρs : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Real.sqrt (ρ p.1 p.2)) PMq) :
    (∫ p, ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2| ∂PMq)
      ≤ Real.sqrt (∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq)
        * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq) := by
  set f : ℝ × ℝ → ℝ := fun p => Real.sqrt (ρ p.1 p.2) * A p.1 p.2 with hf
  set g : ℝ × ℝ → ℝ := fun p => Real.sqrt (ρ p.1 p.2) * B p.1 p.2 with hg
  have hfm : MeasureTheory.AEStronglyMeasurable f PMq := hρs.mul hA
  have hgm : MeasureTheory.AEStronglyMeasurable g PMq := hρs.mul hB
  have hfsq : (fun p : ℝ × ℝ => f p ^ 2) =ᵐ[PMq] fun p => ρ p.1 p.2 * (A p.1 p.2) ^ 2 := by
    filter_upwards [hρ] with p hp
    show (Real.sqrt (ρ p.1 p.2) * A p.1 p.2) ^ 2 = ρ p.1 p.2 * (A p.1 p.2) ^ 2
    rw [mul_pow, Real.sq_sqrt hp]
  have hgsq : (fun p : ℝ × ℝ => g p ^ 2) =ᵐ[PMq] fun p => ρ p.1 p.2 * (B p.1 p.2) ^ 2 := by
    filter_upwards [hρ] with p hp
    show (Real.sqrt (ρ p.1 p.2) * B p.1 p.2) ^ 2 = ρ p.1 p.2 * (B p.1 p.2) ^ 2
    rw [mul_pow, Real.sq_sqrt hp]
  have hfint : MeasureTheory.Integrable (fun p : ℝ × ℝ => f p ^ 2) PMq := hA2.congr hfsq.symm
  have hgint : MeasureTheory.Integrable (fun p : ℝ × ℝ => g p ^ 2) PMq := hB2.congr hgsq.symm
  have hfmem : MeasureTheory.MemLp f 2 PMq :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfm).mpr hfint
  have hgmem : MeasureTheory.MemLp g 2 PMq :=
    (MeasureTheory.memLp_two_iff_integrable_sq hgm).mpr hgint
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := PMq) (p := 2) (q := 2)
    (f := f) (g := g) Real.HolderConjugate.two_two
    (by rw [ENNReal.ofReal_ofNat]; exact hfmem)
    (by rw [ENNReal.ofReal_ofNat]; exact hgmem)
  have hnorm : (fun p : ℝ × ℝ => ‖f p‖ * ‖g p‖)
      =ᵐ[PMq] (fun p => ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2|) := by
    filter_upwards [hρ] with p hp
    have hs : 0 ≤ Real.sqrt (ρ p.1 p.2) := Real.sqrt_nonneg _
    have h2 : Real.sqrt (ρ p.1 p.2) * Real.sqrt (ρ p.1 p.2) = ρ p.1 p.2 := by
      rw [← sq, Real.sq_sqrt hp]
    show |Real.sqrt (ρ p.1 p.2) * A p.1 p.2| * |Real.sqrt (ρ p.1 p.2) * B p.1 p.2|
      = ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2|
    simp only [abs_mul, abs_of_nonneg hs]
    rw [show (Real.sqrt (ρ p.1 p.2) * |A p.1 p.2|) * (Real.sqrt (ρ p.1 p.2) * |B p.1 p.2|)
        = (Real.sqrt (ρ p.1 p.2) * Real.sqrt (ρ p.1 p.2)) * (|A p.1 p.2| * |B p.1 p.2|)
        from by ring, h2]
    ring
  have hsqA : (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq := by
    calc (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, f p ^ 2 ∂PMq := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      _ = ∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq := MeasureTheory.integral_congr_ae hfsq
  have hsqB : (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq := by
    calc (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, g p ^ 2 ∂PMq := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      _ = ∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq := MeasureTheory.integral_congr_ae hgsq
  calc (∫ p, ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2| ∂PMq)
      = ∫ p, ‖f p‖ * ‖g p‖ ∂PMq := (MeasureTheory.integral_congr_ae hnorm).symm
    _ ≤ (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) ^ (1 / (2 : ℝ))
          * (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt (∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq) := by
        rw [hsqA, hsqB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-! ## Tools for the `b₁ ≤ 4` case of `leafGamPureZ`

For `b₁ ≤ 4` the coefficient slot `D_z^{b₁}A` has order at most `4`, hence a *pointwise* bound
(`N6.PwAny6`, priced by `HkNorm α 6 A ≤ K6`).  The two `f`-slots `mixed (b - b₁) a f` and
`mixed b a f` are both *mixed* (`1 ≤ a`) of order at most `4` resp. `6`, so the matched-weight
Cauchy–Schwarz (`Npair6Aux.weightedCS_ae`) prices their pair by
`|f|_{ℋ⁴}·|f|_{ℋ⁶} ≤ M·|f|_{ℋ⁶}`. -/


/-- The `γ`-leaf weight is continuous on the open quadrant. -/
lemma leafGamPureZ_cont (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      = fun p : ℝ × ℝ =>
          (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := rfl
  rw [h]
  exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0).mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))

/-- The `γ`-weighted density of a mixed slot is continuous on the open quadrant. -/
lemma leafGamPureZ_densCont {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))).mul
    ((hsm.mixed j i).continuousOn.pow 2)

/-- **Product-measure integrability and value bound for a `γ`-weighted mixed slot.** -/
lemma leafGamPureZ_mixedSlotLe {α : ℝ} (hα0 : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ Work.Spaces.HkSq α k f := by
  have hbase := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := k) hsm hmem
  have hpt : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα0 hθI]
      ring
    rw [hid]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
  have hnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' hbase.1
      (Work.Spaces.aesm_of_continuousOn_Qd _ (leafGamPureZ_densCont hsm j i)) ?_
    filter_upwards [hpt, hnn] with p hp hpn
    rw [Real.norm_eq_abs, abs_of_nonneg hpn]
    exact hp
  refine ⟨hint, ?_⟩
  rw [← hbase.2]
  exact MeasureTheory.integral_mono_ae hint hbase.1 hpt
end
end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulTermLargeAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The pointwise domination of a leaf-weighted pair of slots by the two square roots of the
level-`l` and level-`6` integrands, in the weight-comparison form. -/
theorem pairDom {α : ℝ} (hα : 0 < α) {A f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ}
    {b₁ a₁ b a l : ℕ}
    (hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ)
    (hρA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
      → ρ z θ ≤ Work.FTS.TransportS.slotW α a₁ z θ)
    (hρf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2
      → ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ)
    (hA : (l = 6 ∧ a₁ + b₁ ≤ 6) ∨ (l = 4 ∧ a₁ + b₁ ≤ 4))
    (hf : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed b₁ a₁ A z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α l A z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have h1 : ρ z θ * (Work.Spaces.mixed b₁ a₁ A z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α l A z θ := by
    refine le_trans (mul_le_mul_of_nonneg_right (hρA z θ hz hθ0 hθ1) (sq_nonneg _)) ?_
    rcases hA with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le6 α hα A hθ h
    · exact Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le4 α hα A hθ h
  have h2 : ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    le_trans (mul_le_mul_of_nonneg_right (hρf z θ hz hθ0 hθ1) (sq_nonneg _))
      (Work.FTS.StrongPersist.H6Pair6Aux.slotW_mul_le6 α hα f hθ hf)
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le (hρnn z θ hz hθ0 hθ1) h1 h2

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzRem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Leibniz remainder of the `A · D_z f` flat row

The expansion of `D_z^bD_θ^a(A·D_zf)` with the transport summand deleted, its (a.e.) strong
measurability, and its pointwise bound against the `ℋ⁶`-integrand plus the angular Hardy slot.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

/-- **The Leibniz expansion with the transport term deleted.** -/
theorem rowDz_leib {A f : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        - A z θ * Work.Spaces.mixed (b + 1) a f z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)) := by
  intro z θ hz hθ hθ2
  have h := Work.FTS.TransportS.mixed_mul_Dz_open b a A f hA hf z θ hz hθ hθ2
  have h00 : (a.choose 0 : ℝ) * (b.choose 0 : ℝ)
      * (Work.Spaces.mixed 0 0 A z θ * Work.Spaces.mixed (b - 0 + 1) (a - 0) f z θ)
      = A z θ * Work.Spaces.mixed (b + 1) a f z θ := by
    simp only [Nat.choose_zero_right, Nat.sub_zero, Work.Spaces.mixed_zero_left,
      Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero]
    ring
  have hkey : Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
      = A z θ * Work.Spaces.mixed (b + 1) a f z θ
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then (0 : ℝ)
              else (a.choose i : ℝ) * (b.choose j : ℝ)
                * (Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)) := by
    rw [h]
    rw [rowDz_dsum_split a b (fun i j => (a.choose i : ℝ) * (b.choose j : ℝ)
      * (Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j + 1) (a - i) f z θ))]
    rw [h00]
  linarith [hkey]

/-- A.e. strong measurability of the mixed derivative of `A·D_zf`. -/
theorem rowDz_Uf_aesm {A f : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hScont : ContinuousOn (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (a + 1),
      ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ)
          else (a.choose i : ℝ) * (b.choose j : ℝ)
            * (Work.Spaces.mixed j i A p.1 p.2
                * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2)))
      Work.FTS.EllipticEst.Q0 := by
    refine continuousOn_finsetSum _ fun i hi => continuousOn_finsetSum _ fun j hj => ?_
    by_cases h00 : i = 0 ∧ j = 0
    · refine ContinuousOn.congr
        (continuousOn_const (c := (0 : ℝ)) :
          ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0) fun p hp => ?_
      rw [if_pos h00]
    · refine ContinuousOn.congr (ContinuousOn.const_mul
        ((Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hA j i).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf (b - j + 1) (a - i)))
        ((a.choose i : ℝ) * (b.choose j : ℝ))) fun p hp => ?_
      rw [if_neg h00]
      rfl
  set pm : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hpm
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2
      * Work.Spaces.mixed (b + 1) a f p.1 p.2) pm := by
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hA.continuousOn
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (b + 1) a f p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hf (b + 1) a)
    exact h2.mul h3
  have hsum : AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2
      * Work.Spaces.mixed (b + 1) a f p.1 p.2
      + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2))) pm :=
    h1.add (Work.Spaces.aesm_of_continuousOn_Qd _ hScont)
  refine hsum.congr ?_
  filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
  have h := rowDz_leib hA hf b a p.1 p.2 hp.1 hp.2.1 hp.2.2
  show A p.1 p.2 * Work.Spaces.mixed (b + 1) a f p.1 p.2
      + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A p.1 p.2
                  * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2))
      = Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
  linarith [h]

/-- The pointwise bound of the Leibniz remainder. -/
theorem rowDz_rem_pt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K Kf : ℝ) (a b : ℕ) (q : ℝ) (HH : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K → 0 ≤ Kf →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      Work.FTS.EllipticEst.SmoothOpen f →
      a + b ≤ 6 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
        canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |canonW q z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            - A z θ * Work.Spaces.mixed (b + 1) a f z θ) * Work.Spaces.mixed b a f z θ|
          ≤ C * (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
  obtain ⟨Ct, hCtpos, hterm⟩ := rowDz_term_bound
  refine ⟨64 * Ct + 1, by linarith [hCtpos], ?_⟩
  intro α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hfsm hab hq0 hqγ hqη0
    hqcases hHH hHHnn z θ hz hθ hθ2
  have hKnn : 0 ≤ K :=
    le_trans (Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hAwl) hAK
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHHz : 0 ≤ HH z θ := hHHnn z θ hz hθ hθ2
  have hleib := rowDz_leib hAsm hfsm b a z θ hz hθ hθ2
  have hsplit : canonW q z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        - A z θ * Work.Spaces.mixed (b + 1) a f z θ) * Work.Spaces.mixed b a f z θ
      = canonW q z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j + 1) (a - i) f z θ)))
        * Work.Spaces.mixed b a f z θ := by
    rw [hleib]
  rw [hsplit, abs_mul, abs_mul, abs_of_nonneg hcw]
  have htri : |∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ)
          else (a.choose i : ℝ) * (b.choose j : ℝ)
            * (Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j + 1) (a - i) f z θ))|
      ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases h00 : i = 0 ∧ j = 0
    · rw [if_pos h00, if_pos h00, abs_zero]
    · rw [if_neg h00, if_neg h00]
      simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose i : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose j : ℝ))]
      exact le_of_eq (by ring)
  have hcoef : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      ((a.choose i : ℝ) * (b.choose j : ℝ))) ≤ 64 := by
    have h1 : (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ))) = 2 ^ a := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_num
    have h2 : (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℝ))) = 2 ^ b := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; norm_num
    have h3 : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ)))
        = (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ)))
          * (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℝ))) :=
      (Finset.sum_mul_sum (Finset.range (a + 1)) (Finset.range (b + 1))
        (fun i => (a.choose i : ℝ)) (fun j => (b.choose j : ℝ))).symm
    rw [h3, h1, h2, ← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  have hmove : canonW q z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
        * |Work.Spaces.mixed b a f z θ|
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          canonW q z θ * ((if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
            * |Work.Spaces.mixed b a f z θ| := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    ring
  refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htri hcw) (abs_nonneg _)) ?_
  rw [hmove]
  have hX : 0 ≤ Ct * (1 + K + Kf)
      * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) :=
    mul_nonneg (mul_nonneg hCtpos.le (by linarith [hKnn, hKfnn]))
      (by linarith [hHknn, hHHz])
  have hper : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
      canonW q z θ * ((if i = 0 ∧ j = 0 then (0 : ℝ)
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|))
          * |Work.Spaces.mixed b a f z θ|
        ≤ ((a.choose i : ℝ) * (b.choose j : ℝ))
          * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) := by
    intro i hi j hj
    have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hjb : j ≤ b := by have := Finset.mem_range.mp hj; omega
    by_cases h00 : i = 0 ∧ j = 0
    · rw [if_pos h00, mul_zero, zero_mul]
      exact mul_nonneg (by positivity) hX
    · rw [if_neg h00]
      have hh : canonW q z θ * |Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) :=
        hterm α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hab hq0 hqγ hqη0
          hqcases hHH hHHnn i j hia hjb (by omega) z θ hz hθ hθ2
      calc canonW q z θ * (((a.choose i : ℝ) * (b.choose j : ℝ))
            * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|)
            * |Work.Spaces.mixed b a f z θ|
          = ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (canonW q z θ * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ ((a.choose i : ℝ) * (b.choose j : ℝ))
            * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
  refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj) ?_
  simp only [← Finset.sum_mul]
  calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        (a.choose i : ℝ) * (b.choose j : ℝ))
        * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ))
      ≤ 64 * (Ct * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)) :=
        mul_le_mul_of_nonneg_right hcoef hX
    _ ≤ (64 * Ct + 1) * (1 + K + Kf)
        * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
        have h1 : 0 ≤ (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
          refine mul_nonneg (by linarith) ?_
          linarith [hHknn, hHHz]
        nlinarith [h1, hCtpos.le, hKfnn, hKnn]

/-- The `ℋ⁶`-domination of the datum slot `D_z^bD_θ^a f`. -/
theorem rowDz_Z_maj {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hqη0 : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  rcases Nat.eq_zero_or_pos a with ha0 | ha
  · subst ha0
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := q)
        (h := f) (hqη0 rfl) hθI b (by omega)
  · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q)
      (h := f) hqγ hθI b a ha (by omega)

/-- The `ℋ⁷`-domination of the top datum slot `D_z^{b+1}D_θ^a f`. -/
theorem rowDz_DZ_maj {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q : ℝ}
    (hqγ : q ≤ Work.Spaces.gam α) (hqη0 : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos hθI
  rcases Nat.eq_zero_or_pos a with ha0 | ha
  · subst ha0
    rw [Work.Spaces.mixed_zero_right]
    have hqη : q ≤ Work.Spaces.eta := hqη0 rfl
    have h := Work.Spaces.sq_le_HkIntegrand_z α 7 f z θ (b + 1) (by omega)
    have h1 : canonW q z θ
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      have h2 : canonW q z θ ≤ canonW Work.Spaces.eta z θ :=
        Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_le_int hqη hθI
      have h3 : canonW Work.Spaces.eta z θ
          = (Work.FTS.H2.Whz z θ) ^ 2 :=
        Work.FTS.TransportS.SlotT2.canonW_eta_eq z θ ⟨le_of_lt hθ, le_of_lt hθ2⟩
      exact le_trans h2 (le_of_eq h3)
    calc canonW q z θ * (Work.Spaces.DzIter (b + 1) f z θ) ^ 2
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter (b + 1) f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (Work.Spaces.DzIter (b + 1) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 7 f z θ := h
  · have h := Work.FTS.StrongPersist.N6Trans.T1SixAux.mixed_sq_w_rpow_le_HkIntegrand_gen
      α 7 f (z := z) (θ := θ) (c := q) hσp hqγ a (b + 1) ha (by omega)
    rw [rowDz_canonW_eq]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.Flat6Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `θ`-derivative of a function of `θ` alone -/

/-- For a function which depends on `θ` only, `∂_θ` is the plain derivative. -/
theorem pth_thetaOnly (φ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun _ θ' => φ θ') z θ = deriv φ θ := rfl

/-! ## Two elementary transfers -/

/-- **Monotonicity of `FlatW` in its constant.** -/
theorem FlatW_mono6 {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') : Work.FTS.VocabO2.FlatW l f K' :=
  Work.FTS.PhiStar.FlatWApi.flatW_mono h hle

/-- **`FlatW 6` from the two `F0` components**: the first clause is the `i = 0` slot of
`F0 6`, the second is exactly `F0 5 (∂_θ f)`. -/
theorem flatW6_of_F0 {K : ℝ} {f : ℝ → ℝ → ℝ} (h1 : Work.FTS.PhiStar.F0 6 K f)
    (h2 : Work.FTS.PhiStar.F0 5 K (Work.Spaces.pth f)) :
    Work.FTS.VocabO2.FlatW 6 f K := by
  intro z θ hz hθ hθ'
  refine ⟨fun k hk => ?_, fun k i hki => h2 k i (by omega) z θ hz hθ hθ'⟩
  simpa using h1 k 0 (by omega) z θ hz hθ hθ'

/-- `∂_θ` respects agreement on the open quadrant (locality of `deriv`). -/
theorem pth_congr6 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ :=
  Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h

/-! ## The ten coefficient functions and their bundle -/

/-- The ten coefficient functions of the order-six flat calculus: the four angular coefficients
`sin²θ`, `cos²θ - 2 sin²θ`, `sin 2θ`, `cos 2θ`; their four `θ`-derivatives; and the two radial
coefficients `z/(1+z)`, `(1+z)⁻¹`. -/
def coefFun : List (ℝ → ℝ → ℝ) :=
  [ fun _ θ => Real.sin θ ^ 2,
    fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2,
    fun _ θ => Real.sin (2 * θ),
    fun _ θ => Real.cos (2 * θ),
    fun _ θ => deriv (fun θ' => Real.sin θ' ^ 2) θ,
    fun _ θ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ,
    fun _ θ => deriv (fun θ' => Real.sin (2 * θ')) θ,
    fun _ θ => deriv (fun θ' => Real.cos (2 * θ')) θ,
    fun z _ => z / (1 + z),
    fun z _ => (1 + z)⁻¹ ]

/-- `∂_θ(sin²θ) = 2 sinθcosθ`. -/
theorem deriv_sin_sq (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  simpa using h.deriv

/-- `∂_θ(cos²θ - 2 sin²θ) = -6 sinθcosθ`. -/
theorem deriv_cos_sq_sub (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = -(6 * Real.sin θ * Real.cos θ) := by
  have h1 := (Real.hasDerivAt_cos θ).pow 2
  have h2 := ((Real.hasDerivAt_sin θ).pow 2).const_mul 2
  have h := h1.sub h2
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = deriv ((Real.cos ^ 2) - fun y => 2 * (Real.sin ^ 2) y) θ := rfl
  rw [e, hd]
  ring_nf

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = deriv (Real.sin ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- `∂_θ(cos 2θ) = -2 sin 2θ`. -/
theorem deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -(2 * Real.sin (2 * θ)) := by
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = deriv (Real.cos ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- **The coefficient bundle.**  There is a single constant `A ≥ 1` such that each of the ten
coefficient functions is `C^∞` on the open quadrant and lies in `F0 6 A`.

`F0 6 A c` gives in particular `|(z+1)^k ∂_z^k D_θ^i c| ≤ A` for `k + i ≤ 6` and hence, at
`k = 0`, `|D_θ^i c| ≤ A` — the form in which the coefficients are consumed pointwise. -/
theorem CoefBundle6s : ∃ A : ℝ, 1 ≤ A ∧ ∀ c ∈ coefFun,
    Work.FTS.PhiStar.F0 6 A c ∧ Work.FTS.EllipticEst.SmoothOpen c := by
  obtain ⟨A₀, hA₀1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := CoefBundle6
  -- smoothness of the four `θ`-derivative coefficients, via the explicit identities
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_ph1
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.FlatWApi.smoothOpen_congr
      (Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular
        (fun n => by fun_prop))
      (fun _ θ _ _ _ => rfl)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_sin2
  have s4 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos (2 * θ)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_cos2
  have e5 : (fun θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ)
      = fun θ => 2 * Real.sin θ * Real.cos θ := by
    funext θ; exact deriv_sin_sq θ
  have e6 : (fun θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      = fun θ => -(6 * Real.sin θ * Real.cos θ) := by
    funext θ; exact deriv_cos_sq_sub θ
  have e7 : (fun θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
      = fun θ => 2 * Real.cos (2 * θ) := by
    funext θ; exact deriv_sin_two θ
  have e8 : (fun θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ)
      = fun θ => -(2 * Real.sin (2 * θ)) := by
    funext θ; exact deriv_cos_two θ
  have s5 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ)
        = fun _ θ => 2 * Real.sin θ * Real.cos θ from by funext z θ; exact deriv_sin_sq θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s6 : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
        = fun _ θ => -(6 * Real.sin θ * Real.cos θ) from by funext z θ; exact deriv_cos_sq_sub θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s7 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
        = fun _ θ => 2 * Real.cos (2 * θ) from by funext z θ; exact deriv_sin_two θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s8 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ)
        = fun _ θ => -(2 * Real.sin (2 * θ)) from by funext z θ; exact deriv_cos_two θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s9 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_rho
  have s10 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_rhoinv
  refine ⟨A₀, hA₀1, ?_⟩
  intro c hc
  simp only [coefFun, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h1, s1⟩
  · exact ⟨h2, s2⟩
  · exact ⟨h3, s3⟩
  · exact ⟨h4, s4⟩
  · exact ⟨h5, s5⟩
  · exact ⟨h6, s6⟩
  · exact ⟨h7, s7⟩
  · exact ⟨h8, s8⟩
  · exact ⟨h9, s9⟩
  · exact ⟨h10, s10⟩

/-! ## The block bounds (the `atomData` bundle) -/

/-- **The block data.**  From the four hypotheses of the target (`FlatW 7 Y K`, `Fb 6 KY Y`,
`F0 6 KD (Yblk Y)`, `SmoothOpen Y`) one gets the bounds

* `F0 6 KY Y`, `F0 6 (K + KY) (pth Y)`, `F0 6 KD (Yblk Y)` — the three blocks;
* `F0 5 (6(K+KY)) (Yblk (pth Y))` — from `F0_zpz` applied to `F0 6 (K+KY) (pth Y)`;
* `F0 5 (K+KY) (D_θ(pth Y))` — from `F0_Dth` applied to `F0 6 (K+KY) (pth Y)`.

These are exactly the `F0`-facts used by the per-field estimates. -/
theorem atomData {K KY KD : ℝ} {Y : ℝ → ℝ → ℝ}
    (hK : 0 ≤ K) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD) (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hW : Work.FTS.VocabO2.FlatW 7 Y K) (hFb : Work.FTS.PhiStar.Fb 6 KY Y)
    (hD : Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y)) :
    Work.FTS.PhiStar.F0 6 KY Y ∧
    Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) ∧
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) ∧
    Work.FTS.PhiStar.F0 5 (6 * (K + KY)) (Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y)) ∧
    Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.Dth (Work.Spaces.pth Y)) := by
  have hK0 : (0 : ℝ) ≤ K + KY := by linarith
  have hP : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by linarith)
  have hZp : Work.FTS.PhiStar.F0 5 (6 * (K + KY))
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth Y) z θ) :=
    (Work.FTS.PhiStar.CoreAux.F0_zpz (n := 5) hK0 hsm.pth hP).mono le_rfl (by norm_num)
  refine ⟨hFb.f0, hP, hD, ?_, ?_⟩
  · exact Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => rfl) hZp
  · exact Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hP

/-! ## The arithmetic of the constant -/


/-! ## The five fields: reassociated expressions and their `θ`-derivative expressions -/




/-- `EVz Y = 2(cos²θ - 2 sin²θ)·Y + D_θY`, reassociated. -/
def EVzR (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ
    + Real.sin (2 * θ) * Work.Spaces.pth Y z θ

/-- The candidate `∂_θ`-derivative of `EVzR`. -/
def EVzD (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
    + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ
    + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ
    + Work.Spaces.Dth (Work.Spaces.pth Y) z θ

/-- **`EVzR` is `EVz`**. -/
theorem evzEVzR_eq (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EVz Y z θ = EVzR Y z θ := by
  simp only [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, EVzR, Work.Construction.s2]
  try ring

/-- `EV Y = (z/(z+1))·EVz Y`. -/
def EVR (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EVzR Y z θ


/-- **`EVR` is `EV`**. -/
theorem evEVR_eq (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EV Y z θ = EVR Y z θ := by
  simp only [Work.FTS.PhiStar.EV, EVR]
  rw [evzEVzR_eq Y z θ, show z / (z + 1) = z / (1 + z) by rw [add_comm]]

/-- `EUz α Y = -(3Y + α(Y/(z+1) + D_zY))`, reassociated. -/
def EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Work.FTS.PhiStar.Yblk Y z θ)

/-- The candidate `∂_θ`-derivative of `EUzR`. -/
def EUzD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
    + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ)

/-- **`EUzR` is `EUz`**. -/
theorem euzEUzR_eq (α : ℝ) (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EUz α Y z θ = EUzR α Y z θ := by
  simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, EUzR,
    div_eq_mul_inv]
  try ring

/-- `EU α Y = (z/(z+1))·EUz α Y`. -/
def EUR (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EUzR α Y z θ

/-- The candidate `∂_θ`-derivative of `EUR`. -/
def EUD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EUzD α Y z θ

/-- **`EUR` is `EU`**. -/
theorem euEUR_eq (α : ℝ) (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EU α Y z θ = EUR α Y z θ := by
  simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, EUR, EUzR,
    div_eq_mul_inv]
  try ring_nf

end Work.FTS.StrongPersist.SP6
end
end
