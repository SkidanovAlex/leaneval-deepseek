import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.Main
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_split
import Submission.Work.FTS.EllipticEst.TT.ESW.source_le
import Submission.Work.FTS.EllipticEst.TT.ESW.U_le_of_1d
import Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots
import Submission.Work.FTS.EllipticEst.remov.slice_ang_asm
import Submission.Work.FTS.EllipticEst.remov.slice_ang_v_outer
import Submission.Work.FTS.EllipticEst.remov.EllFarTop
import Submission.Work.FTS.EllipticEst.remov.EllFarTopDiv
import Submission.Work.FTS.EllipticEst.AngGainFinal.AngGainFinal
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EllUnifBslot`: the `B`-slot of the induction step, on the live `ESW` route

`remov/EllEstUnif_step.lean` (the frozen target of this workspace area) needs, as the last
missing input, the top angular slot estimate

  `√(Tk α k (∂_θθΨ)) ≤ C(D,k) |F|_k`

(`Tk α k f = ∫∫(D_θ^k f · Wt α)²`), under `TT.EllWeakPos α k F Ψ` and the two level-`(k-1)`
bounds with constant `D`, for `k ≥ 3`.

Two routes to it existed in the workspace:

* `remov/B_top_slot_bound` — via `remov.Rtilde_Tk_bound` (`R̃ = ∂_θθΨ + α²z²∂_zzΨ`).  The lead's
  design note `Submission/Work/FTS/ELL_H2_LEAD.md` (§0, item 1) has since declared the `Rtilde`
  route **off-route** ("the top angular slot needs *no* coercive sign, no flux, no
  anti-degeneracy and no `Rtilde`"), so that route is dead;
* `TT/ESW/Assembly.lean`, `ESW.B_slot_bound`, proving the same thing from the one-dimensional
  estimate `remov.slice_ang_gen` + the source slot `TT/ESW.source_le`.  This is the live route.

This module reproduces the live route **independently of `remov/slice_ang_gen.lean`**, whose
source does not currently compile (a one-token type ascription in the `hV` it builds — see
`remov/NOTE_slice_ang_gen_broken.md`; without its `.olean` the whole `TT/ESW/Assembly.lean` is
unimportable).  Concretely:

* `slice_ang_gen_live` is the same 30-line assembly, with the ascription written correctly, so
  that it produces `OneD k` (the type `TT/ESW/U_le_of_1d` consumes);
* `BSlotBound` is the `B`-slot, assembled exactly as `TT/ESW/Assembly.lean` does but from
  `slice_ang_gen_live`.

Nothing here is new mathematics: the two lemmas are transcriptions of
`remov/slice_ang_gen.lean` and `TT/ESW/Assembly.lean` with the (unbuildable) file
`remov/slice_ang_gen.lean` replaced by the local copy.  The remaining inputs
(`remov.slice_ang_v_far`, `remov.slice_ang_gen_final`, `TT/ESW.source_le`, and the pieces they
rest on) are unchanged.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.EllUnifBslot

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The one-dimensional angular estimate of the paper's §"General `ℋ^k` case"**, assembled
from the outer window bound `remov.slice_ang_v_outer` and the far window bound
`remov.slice_ang_v_far` through `remov.slice_ang_gen_final`.  This is `remov.slice_ang_gen`
with the type ascription of its internal `hV` corrected (the enclosing `∃ C` was unused there). -/
theorem slice_ang_gen_live (k : ℕ) (hk : 2 ≤ k) : Work.FTS.EllipticEst.TT.ESW.OneD k := by
  obtain ⟨Co, hCo, hvout⟩ := Work.FTS.EllipticEst.remov.slice_ang_v_outer k hk
  -- the far window: `EllFarTopDiv.sinWeight_xDivX_top_le'` supplies the top (`i = k+1`)
  -- slot, `EllFarTop.farTopXAuxLive_of_top` assembles the reflected bound and
  -- `EllFarTop.slice_ang_v_far_live_of_top` is the copy of `remov.slice_ang_v_far`
  -- with that gap filled
  obtain ⟨Cf, hCf, hvfar⟩ := Work.FTS.EllipticEst.remov.slice_ang_v_far_live_of_top k hk
    (Work.FTS.EllipticEst.remov.farTopXAuxLive_of_top k hk
      (Work.FTS.EllipticEst.remov.EllFarTopDiv.sinWeight_xDivX_top_le' k hk))
  have hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    refine ⟨Co + Cf, by linarith, ?_⟩
    intro γ u g h m hm
    obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩ := h
    obtain ⟨ho1, ho2⟩ :=
      hvout γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    obtain ⟨hf1, hf2⟩ :=
      hvfar γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
        = Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.Icc_union_Icc_eq_Icc (by positivity)
        (by linarith [Real.pi_pos])]
    constructor
    · have hunion := ho1.union hf1
      rwa [hU] at hunion
    · rw [Work.FTS.EllipticEst.remov.integral_split_Iθ
          (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) ho1 hf1]
      linarith
  obtain ⟨C, hC, hfin⟩ := Work.FTS.EllipticEst.AngGainFinal.AngGainFinal k hk hV
  exact ⟨C, hC, fun γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 =>
    hfin γ u g ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩⟩

/-! ## The slot sums of the `B`-assembly (transcribed from `TT/ESW/Assembly.lean`) -/

/-- The lower angular chain sum of `B = ∂_θθΨ`. -/
abbrev Esumr (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)

/-- The top plain angular slot of `Ψ`. -/
abbrev Usl (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- The high angular slots of `Ψ`. -/
abbrev Ejsum (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)

/-- The `η`-weighted slot of `∂_θθΨ`. -/
abbrev Etasl (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The low order terms `∫∫(Ψ')² w²` and `∫∫Ψ² w²`, as two separate integrals. -/
abbrev Losl (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
    + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

/-- The source slot. -/
abbrev Gsum (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- **The `B`-half of the induction step of `prop:Hk`**: the top angular slot of `∂_θθΨ` is
controlled by `|F|_k`.  This is `TT/ESW/Assembly.B_slot_bound`, with `remov.slice_ang_gen`
replaced by the local `slice_ang_gen_live` (the only difference). -/
theorem BSlotBound (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl Ψ)
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (Work.FTS.EllipticEst.TT.ESW.Asl (Work.Spaces.DzIter 1 Ψ))
          + Work.Spaces.HkNorm α (k - 1)
            (Work.FTS.EllipticEst.TT.ESW.Bsl (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
          (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨Cc, hCcpos, hchain⟩ := Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform k (by omega)
  obtain ⟨CE, hCEpos, hE⟩ := Work.FTS.EllipticEst.TT.ESW.E_le_HkSq k (by omega)
  obtain ⟨Cj, hCjpos, hJ⟩ :=
    Work.FTS.EllipticEst.remov.high_slice_chain_slots D hD k (by omega)
  obtain ⟨Cs, hCspos, hsrc⟩ := Work.FTS.EllipticEst.TT.ESW.source_le D hD k hk
  obtain ⟨CU, hCUpos, hU⟩ :=
    Work.FTS.EllipticEst.TT.ESW.U_le_of_1d D hD k hk (slice_ang_gen_live k (by omega))
  refine ⟨Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1,
    by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsmB : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) :=
    (hsm.pth).pth
  have memB : Work.Spaces.HkMem α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) := hwk.memB
  have memB' : Work.Spaces.HkMem α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
      (by omega) (Work.FTS.EllipticEst.SmoothOpen.forall hsmB) memB
  have hb : Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
      ≤ D * Work.Spaces.HkNorm α k F := by
    have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
        (Work.FTS.EllipticEst.TT.ESW.Asl Ψ) :=
      mul_nonneg (sq_nonneg α)
        (Work.Spaces.HkNorm_nonneg α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl Ψ))
    linarith [h1]
  have hE' : Esumr α k Ψ ≤ CE * Work.Spaces.HkSq α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) :=
    hE α Ψ hα hsm memB'
  have hJ' : Ejsum α k Ψ ≤ Cj * Work.Spaces.HkSq α k F := hJ α F Ψ hα hα4 hwk hb h2
  have hsrc' : Gsum α k F Ψ ≤ Cs * Work.Spaces.HkSq α k F := hsrc α F Ψ hα hα4 hwk h1 h2
  have hη : Etasl α Ψ ≤ Work.Spaces.HkSq α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) :=
    Work.FTS.EllipticEst.TT.ESW.eta_slot_le memB'
  have hsplit : Losl α Ψ ≤ 20 * Etasl α Ψ := Work.FTS.EllipticEst.TT.ESW.low_order_split hwk
  have hU' : Usl α k Ψ ≤ CU * (Gsum α k F Ψ + Ejsum α k Ψ + Etasl α Ψ + Losl α Ψ) := by
    convert hU α F Ψ hα hα4 hwk h1 h2 using 2 <;> ring
  have hchain' : Work.FTS.EllipticEst.remov.Step.Tk α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) ≤
      Cc * (Esumr α k Ψ + Usl α k Ψ) := hchain α Ψ hsm memB
  have hcase : Work.Spaces.HkSq α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
      ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hsq : Work.Spaces.HkSq α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
        = (Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)) ^ 2 := by
      rw [Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ))]
    have hsq2 : Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
    rw [hsq, hsq2]
    calc (Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)) ^ 2
        ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1)
            (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)) hb 2
      _ = D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by ring
  have hkey : Work.FTS.EllipticEst.remov.Step.Tk α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) ≤
      (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) * Work.Spaces.HkSq α k F := by
    have hE2 : Esumr α k Ψ ≤ CE * (D ^ 2 * Work.Spaces.HkSq α k F) :=
      le_trans hE' (mul_le_mul_of_nonneg_left hcase hCEpos.le)
    have hU2 : Usl α k Ψ ≤ CU * (Cs * Work.Spaces.HkSq α k F
        + Cj * Work.Spaces.HkSq α k F
        + 21 * (Work.Spaces.HkSq α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ))) := by
      refine le_trans hU' ?_
      refine mul_le_mul_of_nonneg_left ?_ hCUpos.le
      linarith [hsrc', hJ', hη, hsplit]
    have hU3 : Usl α k Ψ ≤ CU * (Cs * Work.Spaces.HkSq α k F
        + Cj * Work.Spaces.HkSq α k F + 21 * (D ^ 2 * Work.Spaces.HkSq α k F)) := by
      refine le_trans hU2 ?_
      refine mul_le_mul_of_nonneg_left ?_ hCUpos.le
      linarith [hcase]
    refine le_trans hchain' ?_
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hE2 hU3) hCcpos.le) (le_of_eq ?_)
    ring
  have hfin : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
        (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hkey) ?_
    rw [Real.sqrt_mul (by positivity)]
  have hnn : 0 ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) :=
    Real.sqrt_nonneg _
  calc Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
        (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := hfin
    _ ≤ (Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1)
        * Work.Spaces.HkNorm α k F := by
        have := Work.Spaces.HkNorm_nonneg α k F
        nlinarith [hnn, this]

end Work.FTS.EllipticEst.remov.EllUnifBslot

end

