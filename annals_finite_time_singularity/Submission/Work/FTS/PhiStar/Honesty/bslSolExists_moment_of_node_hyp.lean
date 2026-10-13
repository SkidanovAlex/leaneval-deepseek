/-
# `Work.FTS.PhiStar.Honesty.bslSolExists_moment_of_node_hyp`

The **existence half *plus* the solution's moment**: from the node's hypotheses (source `F`
`C^∞` on the open quadrant, `ℋ^k`, vanishing angular moment on `z > 0`, pointwise decay in `z`)
there is a solution `Ψ` of `bslOp α Ψ = F` on the open quadrant, `C^∞` there, with the two
Dirichlet values, decaying at `z → ∞`, **and with vanishing angular moment `F_*Ψ ≡ 0` on `z > 0`**.

## Why the extra conjunct is not a consequence of `IsBslSol`

`IsBslSol α F Ψ` is linear in `(F, Ψ)`, and the homogeneous problem has the decaying kernel
directions `z^{-(2m+5)/α} e_m(θ)` (`e_0 ∝ sin 2θ`): adding `c·z^{-5/α} sin 2θ` to a solution
changes its moment by `c·const·z^{-5/α}` while preserving every conjunct of `IsBslSol`.  Hence the
moment has to be proved for **the witness one exhibits**, not deduced from the class.  The witness
used here is the modal one (`ModalSol.Psi α (clampQ F)`, the limit of the partial sums of the mode
series `Σ_m acoeff α m F z · eFam m θ`), for which the `m = 0` coefficient vanishes identically:
the source's moment on `z > 0` is exactly `cmode 0 F ≡ 0` there, and `radGreen α 0` only integrates
over `t > 0`, so `acoeff α 0 F ≡ 0`; every other mode is orthogonal to `sin θ cos²θ`.

## Route

1. `h0 : HkMem α 0 F` (descent from `HkMem α k F`, `OpenPkg.HkMem_mono_open`), the clamped source
   `G := clampQ F` (`G = F` on `z > 0`, `G = 0` on `z ≤ 0`) with `HkMem α 0 G`
   (`Cert.GbarSin.HkMem_congr_Q0`), global `OrthCond G` (`orthCond_clampQ`), `SmoothOpen G`,
   `L²`-integrability of `G` on the quadrant, and `F_*G ≡ 0` on `z > 0`.
2. The modal weak solution `Ψ := ModalSol.Psi α G` of `bslOp α Ψ = G`: locally integrable,
   continuous on the quadrant, with the weak identity (`ModalSolR.psi_weak_identity`), the
   Dirichlet values (`ModalSol.Psi_apply_zero/pi_half`), the decay, and a.e.-continuous angular
   slices (`ModalSolR.Psi_slice_continuous`).  The continuity, the pointwise bound and the decay
   are the clean reproofs `NodeAux.continuousOn_uncurry_Psi_mod` /
   `NodeAux.Psi_bound_mod` / `NodeAux.Psi_tendsto_atTop_zero_mod`; the versions in
   `FTS/H2/ModalSol/Basic.lean` rest on the statement-only `sorry` of
   `ModalSol/TailBound/psiTrunc_tail.lean` (see the header of `NodeAux`).
3. Interior regularity (`interiorSmoothQ0_fts`) gives `Φ`, `C^∞` on the quadrant and a.e. equal to
   `Ψ` on `Q0`.  Since both are continuous on the open quadrant, the a.e.-equality is an equality
   (`MeasureTheory.Measure.eqOn_open_of_ae_eq`), so the slices of `Φ` and `Ψ` agree pointwise,
   whence `F_*Φ = F_*Ψ` on `z > 0`.  The weak identity also upgrades to the pointwise equation
   `bslOp α Φ = G` on `Q0` (`Assembly.bslOp_eq_of_weak_of_smooth`), and the decay of `Ψ`
   transfers to `Φ` (`PhiStarE5.smoothRep_decay`).
4. On the quadrant, `Ψ = psiSeries α G` (both are limits of the same partial sums
   `psiTrunc α G N z θ`: `psiTrunc_tendsto_Psi` and `psiTrunc_tendsto_psiSeries`), so
   `F_*Ψ = F_*(psiSeries α G)`, and the latter vanishes on `z > 0` by
   `Fstar_psiSeries_eq_zero_of_hkMem` (the `m = 0` coefficient of `psiSeries α G` is `0`).
5. The final witness is `1_{θ ∈ (0,π/2)}·Φ` (the redefinition of `Φ` off the open quadrant forces
   the two Dirichlet values); `SmoothOpen` and `IsBslSol α F` are then as in
   `EllExistHalf.bslSolExists_of_node_hyp`, and `F_*Ψ = F_*Φ` on `z > 0` because the indicator
   differs from `1` only on a null set of angles.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero_of_hkMem
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.Honesty.NodeAux2
import Submission.Work.FTS.EllipticEst.Final.InteriorSmoothQ0_fts
import Submission.Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth
import Submission.Work.FTS.H2.PhiStarE5.Decay
import Submission.Work.FTS.H2.PhiStarE5.Locality
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-- Two angle functions which agree on the *open* interval `(0,π/2)` agree a.e. on
`Iθ = [0,π/2]` (the two endpoints are a null set). -/
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

theorem bslSolExists_moment_of_node_hyp (k : ℕ) :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α k F →
      (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ ∧
          (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar Ψ z = 0) := by
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
    NodeAux.continuousOn_uncurry_Psi_mod α hα hα1 horthG hsmG hL2G
  have hΨli : LocallyIntegrableOn (Function.uncurry (Psis α (clampQ F))) Q0 :=
    hcontΨ.locallyIntegrableOn Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hΨdec : ∀ θ ∈ Iθ, Tendsto (fun z => Psis α (clampQ F) z θ) atTop (nhds 0) :=
    NodeAux.Psi_tendsto_atTop_zero_mod α hα hα1 horthG hsmG hL2G
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
      (psiTrunc_tendsto_psiSeries hα hα1 hfstG hsmG hL2G hz hθ)
  -- ## the witness
  refine ⟨fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0, ?_, ?_, ?_⟩
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
  · -- the angular moment of the witness
    intro z hz
    have h1 : Work.Elliptic.Fstar (fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then Φ z θ else 0) z
        = Work.Elliptic.Fstar Φ z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      refine ae_imp_eq_of_eqOn_Ioo (fun θ hθ => ?_)
      rw [if_pos hθ]
    have h2 : Work.Elliptic.Fstar Φ z = Work.Elliptic.Fstar (Psis α (clampQ F)) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      refine ae_imp_eq_of_eqOn_Ioo (fun θ hθ => ?_)
      rw [hΦΨ z θ hz hθ.1 hθ.2]
    have h3 : Work.Elliptic.Fstar (Psis α (clampQ F)) z
        = Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α (clampQ F)) z := by
      rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      refine ae_imp_eq_of_eqOn_Ioo (fun θ hθ => ?_)
      rw [hPsiSeries z θ hz hθ]
    have h4 : Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α (clampQ F)) z = 0 :=
      Fstar_psiSeries_eq_zero_of_hkMem hα hα4 hsmG h0G hfstG z hz
    rw [h1, h2, h3, h4]

end Work.FTS.PhiStar.Honesty
