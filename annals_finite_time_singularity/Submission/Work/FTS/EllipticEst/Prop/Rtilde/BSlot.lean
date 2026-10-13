import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.Main
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_split
import Submission.Work.FTS.EllipticEst.TT.ESW.U_le_of_1d
import Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Prop.Rtilde.OneD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.BSlot`: the top angular slot of `∂_θθΨ`

This is `TT.ESW.Assembly.B_slot_bound` with the two unproved inputs (`TT.ESW.source_le` and
`remov.slice_ang_gen`) replaced by explicit hypotheses:
`hSrc` (the source slot, proved in parallel as `Prop.Rtilde.SourceLe`) and `hOneD` (the
one-dimensional angular estimate, produced by `Prop.Rtilde.oneD_of_far` from the far-window
bound).  Assembling the pieces — the sharp angular chain, the lower angular slots, the
one-dimensional far-region estimate applied slicewise, the source domination, the high angular
slots of `Ψ` and the low-order terms — gives `√(Tk α k (∂_θθΨ)) ≤ C(D,k) |F|_k`: the `B`-half of
the induction step of `prop:Hk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The lower angular chain sum of `B = ∂_θθΨ`. -/
abbrev Esumr (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
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

/-- The low order terms `∫∫(Ψ')² w²` and `∫∫Ψ² w²`, as two separate integrals (the shape of the
right-hand side of the one-dimensional estimate). -/
abbrev Losl (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
    + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

/-- The source slot. -/
abbrev Gsum (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- **The `B`-half of the induction step of `prop:Hk`**: the top angular slot of `∂_θθΨ` is
controlled by `|F|_k`. -/
theorem bSlot_bound (D : ℝ) (hD : 0 < D)
    (hSrc : ∀ (k : ℕ), 3 ≤ k → ∃ Cs : ℝ, 0 < Cs ∧
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
        (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ Cs * Work.Spaces.HkSq α k F)
    (hOneD : ∀ (k : ℕ), 3 ≤ k → Work.FTS.EllipticEst.TT.ESW.OneD k) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Asl Ψ)
          + Work.Spaces.HkNorm α (k - 1) (Bsl Ψ) ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Asl (Work.Spaces.DzIter 1 Ψ))
          + Work.Spaces.HkNorm α (k - 1) (Bsl (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨Cc, hCcpos, hchain⟩ := Tk_B_le_chain_uniform k (by omega)
  obtain ⟨CE, hCEpos, hE⟩ := E_le_HkSq k (by omega)
  obtain ⟨Cj, hCjpos, hJ⟩ :=
    Work.FTS.EllipticEst.remov.high_slice_chain_slots D hD k (by omega)
  obtain ⟨Cs, hCspos, hsrc⟩ := hSrc k hk
  obtain ⟨CU, hCUpos, hU⟩ :=
    U_le_of_1d D hD k hk (hOneD k (by omega))
  refine ⟨Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1,
    by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsmB : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := (hsm.pth).pth
  have memB : Work.Spaces.HkMem α k (Bsl Ψ) := hwk.memB
  have memB' : Work.Spaces.HkMem α (k - 1) (Bsl Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := k - 1) (l := k)
      (by omega) (SmoothOpen.forall hsmB) memB
  have hb : Work.Spaces.HkNorm α (k - 1) (Bsl Ψ) ≤ D * Work.Spaces.HkNorm α k F := by
    have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Asl Ψ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α (k - 1) (Asl Ψ))
    linarith [h1]
  -- the pieces
  have hE' : Esumr α k Ψ ≤ CE * Work.Spaces.HkSq α (k - 1) (Bsl Ψ) :=
    hE α Ψ hα hsm memB'
  have hJ' : Ejsum α k Ψ ≤ Cj * Work.Spaces.HkSq α k F :=
    hJ α F Ψ hα hα4 hwk hb h2
  have hsrc' : Gsum α k F Ψ ≤ Cs * Work.Spaces.HkSq α k F :=
    hsrc α F Ψ hα hα4 hwk h1 h2
  have hη : Etasl α Ψ ≤ Work.Spaces.HkSq α (k - 1) (Bsl Ψ) := eta_slot_le memB'
  have hsplit : Losl α Ψ ≤ 20 * Etasl α Ψ := low_order_split hwk
  have hU' : Usl α k Ψ ≤ CU * (Gsum α k F Ψ + Ejsum α k Ψ + Etasl α Ψ + Losl α Ψ) := by
    convert hU α F Ψ hα hα4 hwk h1 h2 using 2 <;> ring
  have hchain' : Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ) ≤
      Cc * (Esumr α k Ψ + Usl α k Ψ) := hchain α Ψ hsm memB
  -- the level-(k-1) bound
  have hcase : Work.Spaces.HkSq α (k - 1) (Bsl Ψ) ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hsq : Work.Spaces.HkSq α (k - 1) (Bsl Ψ)
        = (Work.Spaces.HkNorm α (k - 1) (Bsl Ψ)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) (Bsl Ψ))]
    have hsq2 : Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]
    rw [hsq, hsq2]
    calc (Work.Spaces.HkNorm α (k - 1) (Bsl Ψ)) ^ 2
        ≤ (D * Work.Spaces.HkNorm α k F) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α (k - 1) (Bsl Ψ)) hb 2
      _ = D ^ 2 * (Work.Spaces.HkNorm α k F) ^ 2 := by ring
  -- arithmetic
  have hkey : Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ) ≤
      (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) * Work.Spaces.HkSq α k F := by
    have hE2 : Esumr α k Ψ ≤ CE * (D ^ 2 * Work.Spaces.HkSq α k F) :=
      le_trans hE' (mul_le_mul_of_nonneg_left hcase hCEpos.le)
    have hU2 : Usl α k Ψ ≤ CU * (Cs * Work.Spaces.HkSq α k F
        + Cj * Work.Spaces.HkSq α k F + 21 * (Work.Spaces.HkSq α (k - 1) (Bsl Ψ))) := by
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
  have hfin : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := by
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hkey) ?_
    rw [Real.sqrt_mul (by positivity)]
  have hnn : 0 ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) :=
    Real.sqrt_nonneg _
  calc Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ))
      ≤ Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2)))
        * Work.Spaces.HkNorm α k F := hfin
    _ ≤ (Real.sqrt (Cc * (CE * D ^ 2 + CU * (Cs + Cj + D ^ 2 + 20 * D ^ 2))) + 1)
        * Work.Spaces.HkNorm α k F := by
        have := Work.Spaces.HkNorm_nonneg α k F
        nlinarith [hnn, this]

end Work.FTS.EllipticEst.TT.ESW
