/-
# `Work.FTS.PhiStar.RouteB.bslSolExists_psiSeries_of_node_hyp`

The **existence half** of the elliptic node together with the *identification of the witness*
with the mode series: from the node's hypotheses (source `F` `C^∞` on the open quadrant, `ℋ^k`,
vanishing angular moment on `z > 0`, pointwise decay in `z`) there is `Ψ` with

* `SmoothOpen Ψ`,
* `IsBslSol α F Ψ` (the equation on the open quadrant, the two Dirichlet values, decay at `∞`),
* `F_*Ψ ≡ 0` on `z > 0`,
* `Ψ z θ = psiSeries α F z θ` on the whole open quadrant `z > 0`, `0 < θ < π/2`.

## Route

This is `Honesty.bslSolExists_moment_of_node_hyp` (the modal witness
`Psis α (clampQ F)` of the clamped source `G = clampQ F`, cut off at `θ ∉ (0,π/2)` so that the
two Dirichlet values hold literally) with the moment conjunct *replaced* by the mode-series
identity, the moment now being a consequence of it:

* `Φ =ᵐ Psis α G` on the quadrant (interior regularity + continuity), and on the quadrant the
  modal solution is the sum of its partial sums, `Psis α G = psiSeries α G`
  (`psiTrunc_tendsto_Psi` against `psiTrunc_tendsto_psiSeries`);
* `F_*Ψ = F_*(psiSeries α F)` by the pointwise identity (the disagreement set of `Ψ` and
  `psiSeries α F` on `Iθ` is contained in the two endpoints, a null set), and
  `F_*(psiSeries α F) ≡ 0` on `z > 0` by `Fstar_psiSeries_eq_zero_of_hkMem`.

The one extra ingredient is the locality of the mode series in the source: `radGreen` only sees
its source on the open half-line `(0,∞)`, so the clamped source has the same mode coefficients
as `F` on `z > 0` (`cmode_clampQ`, `acoeff_clampQ`, `psiSeries_clampQ`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.bslSolExists_moment_of_node_hyp
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.EllExistHalf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-! ## Two angle functions agreeing on the open interval agree a.e. on `Iθ` -/

private lemma ae_imp_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    ∀ᵐ θ ∂volume, θ ∈ Iθ → f θ = g θ := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.ae_restrict_iff' (s := Iθ)
    (show MeasurableSet Iθ from measurableSet_Icc), ← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

/-! ## Locality of the mode series in the source -/

/-- `radGreen` only sees the values of its source on the open half-line `(0,∞)`: for `z > 0`
both integrals range over positive arguments only. -/
private lemma radGreen_congr_Ioi {α : ℝ} (m : ℕ) {f g : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → f t = g t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m f z
      = Work.FTS.PhiStar.Radial.radGreen α m g z := by
  have h1 : (∫ t in (0 : ℝ)..z, f t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = (∫ t in (0 : ℝ)..z, g t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, f t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = (∫ t in Set.Ioi z, g t * t ^ (-(2 * (m : ℝ) / α) - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- The clamped source `clampQ F` has, at `z > 0`, the same mode coefficients as `F`. -/
private lemma cmode_clampQ (m : ℕ) {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.clampQ F) z
      = Work.FTS.PhiStar.Series.cmode m F z := by
  have hn : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        (Work.FTS.PhiStar.clampQ F) z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Work.FTS.PhiStar.clampQ, if_pos hz]
  rw [Work.FTS.PhiStar.Series.cmode, Work.FTS.PhiStar.Series.cmode, hn]

/-- The mode-`m` radial coefficient is the same for `clampQ F` and `F` at `z > 0`. -/
private lemma acoeff_clampQ (α : ℝ) (m : ℕ) {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.clampQ F) z
      = Work.FTS.PhiStar.Series.acoeff α m F z := by
  rw [Work.FTS.PhiStar.Series.acoeff, Work.FTS.PhiStar.Series.acoeff]
  exact radGreen_congr_Ioi m (fun t ht => cmode_clampQ m ht) hz

/-- **The mode series only sees its source on `z > 0`**: the clamped source has the same series
as `F` in the open half-plane `z > 0`. -/
private lemma psiSeries_clampQ (α : ℝ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.clampQ F) z θ
      = Work.FTS.PhiStar.Series.psiSeries α F z θ := by
  refine tsum_congr (fun m => ?_)
  rw [acoeff_clampQ α m hz]

/-! ## The theorem -/

theorem bslSolExists_psiSeries_of_node_hyp (k : ℕ) :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α k F →
      (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ ∧
          (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Ψ z = 0) ∧
          (∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
            Ψ z θ = Work.FTS.PhiStar.Series.psiSeries α F z θ) := by
  intro α F hα hα4 hsm hk horth hdec
  have hα1 : α ≤ 1 := by linarith
  -- ## the clamped source `G = clampQ F` and its `ℋ^0`-data
  have h0F : Work.Spaces.HkMem α 0 F :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 0 (Nat.zero_le k) hk
  have hsmG : Work.FTS.EllipticEst.SmoothOpen (clampQ F) := smoothOpen_clampQ hsm
  have horthG : Work.Elliptic.OrthCond (clampQ F) := orthCond_clampQ horth
  have h0G : Work.Spaces.HkMem α 0 (clampQ F) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h0F
      (fun z hz θ hθ => by simp only [clampQ]; rw [if_pos (show (0 : ℝ) < z from hz)])
  have hL2F : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0 :=
    integrableOn_sq_Q0_of_HkMem h0F hsm
  have hL2G : IntegrableOn (fun p : ℝ × ℝ => (clampQ F) p.1 p.2 ^ 2) Q0 := by
    refine hL2F.congr_fun ?_ Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    intro p hp
    obtain ⟨hz, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (F p.1 p.2) ^ 2 = ((if 0 < p.1 then F p.1 p.2 else 0)) ^ 2
    rw [if_pos hz]
  have hfstG : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (clampQ F) z = 0 := by
    intro z hz
    rw [fstar_clampQ, if_pos hz]
    exact horth z hz
  -- ## the modal weak solution `Ψ` and its properties (all clean statements)
  have hcontΨ : ContinuousOn (Function.uncurry (Psis α (clampQ F))) Q0 :=
    Honesty.NodeAux.continuousOn_uncurry_Psi_mod α hα hα1 horthG hsmG hL2G
  have hΨli : LocallyIntegrableOn (Function.uncurry (Psis α (clampQ F))) Q0 :=
    hcontΨ.locallyIntegrableOn Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hΨdec : ∀ θ ∈ Iθ, Tendsto (fun z => Psis α (clampQ F) z θ) atTop (nhds 0) :=
    Honesty.NodeAux.Psi_tendsto_atTop_zero_mod α hα hα1 horthG hsmG hL2G
  have hΨslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Psis α (clampQ F) z θ) (Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun z hz =>
      Work.FTS.H2.ModalSolR.Psi_slice_continuous α hα hα1 horthG hsmG hL2G hz)
  -- ## interior regularity: the smooth representative `Φ`
  obtain ⟨Φ, hΦsm, hΦae⟩ :=
    Work.EllipticEst.InteriorRegularity.Q0.interiorSmoothQ0_fts hα hsmG hΨli
      (fun φ hφ hcφ hsub =>
        Work.FTS.H2.ModalSolR.psi_weak_identity α hα hα1 horthG hsmG hL2G hφ hcφ hsub)
  -- ## the pointwise equation for `Φ`
  have hΦeq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α Φ z θ = clampQ F z θ := by
    refine Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth hα hΦsm hsmG ?_
    intro φ hφ hcφ hsub
    rw [← Work.FTS.H2.ModalSolR.psi_weak_identity α hα hα1 horthG hsmG hL2G hφ hcφ hsub]
    refine MeasureTheory.setIntegral_congr_ae Work.FTS.EllipticEst.isOpen_Q0.measurableSet ?_
    rw [← MeasureTheory.ae_restrict_iff' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
    refine hΦae.symm.mono (fun p hp => ?_)
    have hp' : Φ p.1 p.2 = Psis α (clampQ F) p.1 p.2 := hp
    show Φ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
       = Psis α (clampQ F) p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
         * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    rw [hp']
  -- ## `Φ = Ψ` on the open quadrant (both continuous there, equal a.e.)
  have hcontΦ : ContinuousOn (Function.uncurry Φ) Q0 := hΦsm.continuousOn
  have hEqOn : Set.EqOn (Function.uncurry Φ) (Function.uncurry (Psis α (clampQ F))) Q0 :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hΦae.symm Work.FTS.EllipticEst.isOpen_Q0
      hcontΦ hcontΨ
  have hΦΨ : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → Φ z θ = Psis α (clampQ F) z θ :=
    fun z θ hz hθ hθ2 => hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩)
  -- ## the decay of `Φ`
  have hΦdec : ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => Φ z θ) atTop (nhds 0) :=
    Work.FTS.H2.PhiStarE5.smoothRep_decay hΦsm hΦae.symm hΨslice hΨdec
  -- ## on the quadrant, `Ψ` is the mode series of `G`
  have hPsiSeries : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Psis α (clampQ F) z θ = Work.FTS.PhiStar.Series.psiSeries α (clampQ F) z θ := by
    intro z θ hz hθ
    exact tendsto_nhds_unique
      (Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horthG hsmG hL2G hz hθ)
      (Honesty.psiTrunc_tendsto_psiSeries hα hα1 hfstG hsmG hL2G hz hθ)
  -- ## the witness
  refine ⟨fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0, ?_, ?_, ?_, ?_⟩
  · -- `SmoothOpen`
    refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
    refine (hΦsm.forall n).congr (fun p hp => ?_)
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (if p.2 ∈ Set.Ioo 0 (π / 2) then Φ p.1 p.2 else 0) = Φ p.1 p.2
    rw [if_pos ⟨h1, h2⟩]
  · -- `IsBslSol α F`
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ hθ0 hθ2
      have hev : ∀ᶠ q in 𝓝 (z, θ),
          (if q.2 ∈ Set.Ioo 0 (π / 2) then Φ q.1 q.2 else 0) = Φ q.1 q.2 := by
        have hnb : ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (π / 2)) ∈ 𝓝 (z, θ) :=
          (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ0, hθ2⟩
        exact Filter.mem_of_superset hnb (fun q hq => if_pos hq.2)
      rw [Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq α hev, hΦeq z hz θ hθ0 hθ2]
      show (if 0 < z then F z θ else 0) = F z θ
      rw [if_pos hz]
    · intro z; exact if_neg (by simp)
    · intro z; exact if_neg (by simp [Real.pi_pos])
    · intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h | h
      · subst h
        have hz : (fun z : ℝ => (if (0 : ℝ) ∈ Set.Ioo 0 (π / 2) then Φ z 0 else 0))
            = fun _ => 0 := by
          funext z; exact if_neg (by simp)
        rw [hz]; exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · subst h2
          have hz : (fun z : ℝ =>
                (if Real.pi / 2 ∈ Set.Ioo 0 (Real.pi / 2) then Φ z (π / 2) else 0))
              = fun _ => 0 := by
            funext z; exact if_neg (by simp [Real.pi_pos])
          rw [hz]; exact tendsto_const_nhds
        · have hif : ∀ z : ℝ, (if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0) = Φ z θ :=
            fun z => if_pos ⟨h, h2⟩
          exact Tendsto.congr' (Eventually.of_forall (fun z => (hif z).symm))
            (hΦdec θ ⟨h, h2⟩)
  · -- the angular moment, from the mode series
    intro z hz
    have heq : Work.Elliptic.Fstar
          (fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0) z
        = Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      refine ae_imp_eq_of_eqOn_Ioo (fun θ hθ => ?_)
      rw [if_pos hθ, hΦΨ z θ hz hθ.1 hθ.2, hPsiSeries z θ hz hθ, psiSeries_clampQ α hz]
    rw [heq]
    exact Honesty.Fstar_psiSeries_eq_zero_of_hkMem hα hα4 hsm h0F horth z hz
  · -- the mode-series identity on the open quadrant
    intro z hz θ hθ0 hθ1
    show (if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0)
      = Work.FTS.PhiStar.Series.psiSeries α F z θ
    rw [if_pos ⟨hθ0, hθ1⟩, hΦΨ z θ hz hθ0 hθ1, hPsiSeries z θ hz ⟨hθ0, hθ1⟩,
      psiSeries_clampQ α hz]

end Work.FTS.PhiStar.RouteB
