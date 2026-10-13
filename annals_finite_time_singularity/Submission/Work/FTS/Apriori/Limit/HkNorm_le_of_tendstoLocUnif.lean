/-
# Lower semicontinuity of the `ℋ⁴`-norm under locally uniform convergence

`Work.FTS.Apriori.Limit.HkNorm_le_of_tendstoLocUnif`: if `G n` is a sequence of profiles in the
interior regularity class `RegQ α 4` whose `ℋ⁴`-sizes are bounded by `B`, and `G n → f`
uniformly on the compact subsets of the open quadrant `Qd = (0,∞) × (0,π/2)`, then
`|f|_{ℋ⁴} ≤ B` as well.

The proof is the a-priori argument of the Elgindi route (N5, L-N5.9):

* the `ℋ⁴`-integrand is the sum of the squares of the finitely many weighted slots
  `mixed j i f · ρ` (`HkIntegrand_eq_sum_slot`, `SlotCalc`);
* for a compactly supported smooth test function `ψ` one has, by integration by parts
  (`integral_mixed_mul_adjMixed`),
  `∫ (mixed j i g) ψ = ∫ g · adjMixed (j,i) ψ`; combined with the locally uniform convergence
  (`tendsto_integral_mul_of_tendstoLocUnif`) this gives the weak convergence of the slots:
  for every slot `ji` and every cut-off `η`,
  `∫ (slot_ji (G n)) (slot_ji f) η → ∫ (slot_ji f)² η`;
* the elementary inequality `a b s ≤ (a² s + b² s)/2` (for `s ≥ 0`), summed over the slots and
  integrated, bounds the pairing of the limit with the sequence by
  `(1/2) |G n|²_{ℋ⁴,η} + (1/2) |f|²_{ℋ⁴,η} ≤ (1/2) B² + (1/2) |f|²_{ℋ⁴,η}`, whence
  `|f|²_{ℋ⁴,η} ≤ B²` for every cut-off;
* taking the supremum over an exhausting family of cut-offs (`lintegral_..._iSup_...`) and
  comparing with the iterated integral of the `ℋ⁴`-integrand (`ofReal_HkSq_le_lintegral`) gives
  `HkSq α 4 f ≤ B²`, hence `|f|_{ℋ⁴} = √(HkSq) ≤ B`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.Apriori.Limit.TestQClosure
import Submission.Work.FTS.Apriori.Limit.integral_mixed_mul_adjMixed
import Submission.Work.FTS.Apriori.Limit.tendsto_integral_mul_of_tendstoLocUnif
import Submission.Work.FTS.Apriori.Limit.exists_test_cutoff
import Submission.Work.FTS.Apriori.Limit.ofReal_HkSq_le_lintegral
import Submission.Work.FTS.Apriori.Limit.HksqCut_le_HkSq
import Submission.Work.FTS.Apriori.Limit.lintegral_HkIntegrand_le_iSup_HksqCut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

theorem HkNorm_le_of_tendstoLocUnif {α B : ℝ} {G : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α)
    (hG : ∀ n, Work.FTS.Nonlin.RegQ α 4 (G n)) (hB : ∀ n, Work.FTS.Nonlin.Xn α (G n) ≤ B)
    (hf : Work.FTS.LocData.SmoothQuad f)
    (hconv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.Construction.Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) atTop K) :
    Work.FTS.Nonlin.Xn α f ≤ B := by
  classical
  have hGsm : ∀ n, SmoothQuad (G n) := fun n => (hG n).1
  have hGmem : ∀ n, Work.Spaces.HkMem α 4 (G n) := fun n => (hG n).2.1
  have hconvQ : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Qd →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G n p.1 p.2) (fun p => f p.1 p.2) atTop K :=
    fun K hK hKQ => hconv K hK hKQ
  have hBnn : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 4 (G 0)) (hB 0)
  have hGsq : ∀ n, Work.Spaces.HkSq α 4 (G n) ≤ B ^ 2 := by
    intro n
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (G n)) ≤ B := hB n
    have h2 : 0 ≤ Work.Spaces.HkSq α 4 (G n) := Work.Spaces.HkSq_nonneg α 4 (G n)
    have h3 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 4 (G n)) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt h2]
  obtain ⟨η, hηT, hη01, hηtend⟩ := exists_test_cutoff
  -- ### the bound at each cut-off
  have hkey : ∀ k, HksqCut α f (η k) ≤ B ^ 2 := by
    intro k
    have hcut_n : ∀ n, HksqCut α (G n) (η k) ≤ B ^ 2 := fun n =>
      le_trans (HksqCut_le_HkSq (hGsm n) (hGmem n) (hηT k) (fun z θ => (hη01 k z θ).1)
        (fun z θ => (hη01 k z θ).2)) (hGsq n)
    -- ### weak convergence of each slot
    have hslot : ∀ ji ∈ activeSlots, Filter.Tendsto
        (fun n => ∫ p, slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        Filter.atTop (nhds (∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)) := by
      intro ji _
      set Ψ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed ji.1 ji.2 f z θ
        * (slotWeight α ji z θ) ^ 2 * η k z θ with hΨdef
      have hΨT : TestQ Ψ := by
        have hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z θ =>
            Work.Spaces.mixed ji.1 ji.2 f z θ * (slotWeight α ji z θ) ^ 2)) Qd :=
          ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf ji.1 ji.2).mono
            Qd_subset_quadU).mul (contDiffOn_slotWeight_sq α ji.1 ji.2)
        simpa [hΨdef] using (TestQ_mul_adjMixed (hηT k)).1 _ hg
      have hΨadjT : TestQ (adjMixed ji Ψ) := (TestQ_mul_adjMixed hΨT).2 ji.1 ji.2
      have hmain : Filter.Tendsto (fun n => ∫ p,
            Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
          Filter.atTop (nhds (∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ)) := by
        have hibp : ∀ n, (∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
            = ∫ p, G n p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ := fun n =>
          integral_mixed_mul_adjMixed (hGsm n) hΨT ji.1 ji.2
        rw [show (fun n => ∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ)
            = fun n => ∫ p, G n p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ from funext hibp]
        exact tendsto_integral_mul_of_tendstoLocUnif hGsm hf hΨadjT hconvQ
      have hgoal : (∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ)
          = ∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ := by
        rw [← integral_mixed_mul_adjMixed hf hΨT ji.1 ji.2]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show Work.Spaces.mixed ji.1 ji.2 f p.1 p.2 * Ψ p.1 p.2
          = (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2
        rw [hΨdef]
        simp only [slot]
        ring
      rw [show (fun n => ∫ p, slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
          = fun n => ∫ p, Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2 ∂Qμ from
        funext (fun n => by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          show slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2
            = Work.Spaces.mixed ji.1 ji.2 (G n) p.1 p.2 * Ψ p.1 p.2
          rw [hΨdef]
          simp only [slot]
          ring),
        show (∫ p, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)
          = ∫ p, f p.1 p.2 * adjMixed ji Ψ p.1 p.2 ∂Qμ from hgoal.symm]
      exact hmain
    have hsum_lim : Filter.Tendsto
        (fun n => ∑ ji ∈ activeSlots, ∫ p,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        Filter.atTop (nhds (∑ ji ∈ activeSlots, ∫ p,
          (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)) :=
      tendsto_finsetSum _ hslot
    rw [← HksqCut_eq_sum_slot hf (hηT k)] at hsum_lim
    -- ### the elementary bound for each `n`
    have hsupp_gen : ∀ (F : ℝ × ℝ → ℝ), (∀ p, η k p.1 p.2 = 0 → F p = 0) →
        Function.support F ⊆ tsupport (Function.uncurry (η k)) := by
      intro F hF p hp
      exact subset_tsupport _ (fun h => hp (hF p h))
    have hprodint : ∀ (g : ℝ → ℝ → ℝ), SmoothQuad g → ∀ ji : ℕ × ℕ,
        Integrable (fun p : ℝ × ℝ => slot α ji g p.1 p.2 * slot α ji f p.1 p.2
          * η k p.1 p.2) Qμ := by
      intro g hgsm ji
      refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
      · exact ((continuousOn_slot hgsm α ji).mul (continuousOn_slot hf α ji)).mul
          (hηT k).1.continuousOn
      · exact hsupp_gen _ (fun p h => by simp [h])
    have hsqint : ∀ (g : ℝ → ℝ → ℝ), SmoothQuad g → ∀ ji : ℕ × ℕ,
        Integrable (fun p : ℝ × ℝ => (slot α ji g p.1 p.2) ^ 2 * η k p.1 p.2) Qμ := by
      intro g hgsm ji
      refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
      · exact ((continuousOn_slot hgsm α ji).pow 2).mul (hηT k).1.continuousOn
      · exact hsupp_gen _ (fun p h => by simp [h])
    have hsqsum : ∀ (g : ℝ → ℝ → ℝ), SmoothQuad g →
        (∫ p, ∑ ji ∈ activeSlots, (slot α ji g p.1 p.2) ^ 2 * η k p.1 p.2 ∂Qμ)
          = HksqCut α g (η k) := by
      intro g hgsm
      rw [MeasureTheory.integral_finsetSum _ (fun ji _ => hsqint g hgsm ji),
        HksqCut_eq_sum_slot hgsm (hηT k)]
    have hbnd : ∀ n, (∑ ji ∈ activeSlots, ∫ p,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
        ≤ (1 / 2) * HksqCut α (G n) (η k) + (1 / 2) * HksqCut α f (η k) := by
      intro n
      have hint1 : Integrable (fun p : ℝ × ℝ => ∑ ji ∈ activeSlots,
          slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact continuousOn_finsetSum _ (fun ji _ => ((continuousOn_slot (hGsm n) α ji).mul
            (continuousOn_slot hf α ji)).mul (hηT k).1.continuousOn)
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hint2a : Integrable (fun p : ℝ × ℝ => (1 / 2) *
          (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _
            (fun ji _ => ((continuousOn_slot (hGsm n) α ji).pow 2).mul
              (hηT k).1.continuousOn))
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hint2b : Integrable (fun p : ℝ × ℝ => (1 / 2) *
          (∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) Qμ := by
        refine integrable_of_continuousOn_of_support ?_ (hηT k).2.1 (hηT k).2.2 ?_
        · exact ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _
            (fun ji _ => ((continuousOn_slot hf α ji).pow 2).mul (hηT k).1.continuousOn))
        · exact hsupp_gen _ (fun p h => by simp [h])
      have hsum_eq : (∑ ji ∈ activeSlots, ∫ p,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2 ∂Qμ)
          = ∫ p, ∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2
              * η k p.1 p.2) ∂Qμ :=
        (MeasureTheory.integral_finsetSum _ (fun ji _ => hprodint (G n) (hGsm n) ji)).symm
      rw [hsum_eq]
      have hamgm : ∀ᵐ p ∂Qμ, (∑ ji ∈ activeSlots,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2)
          ≤ (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
            + (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        have hs : 0 ≤ η k p.1 p.2 := (hη01 k p.1 p.2).1
        have hterm : ∀ ji ∈ activeSlots,
            slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2
              ≤ (1 / 2) * ((slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * ((slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
          intro ji _
          nlinarith [sq_nonneg (slot α ji (G n) p.1 p.2 - slot α ji f p.1 p.2), hs]
        calc (∑ ji ∈ activeSlots,
              slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2 * η k p.1 p.2)
            ≤ ∑ ji ∈ activeSlots, ((1 / 2) * ((slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * ((slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) :=
              Finset.sum_le_sum hterm
          _ = (1 / 2) * (∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
                + (1 / 2) * (∑ ji ∈ activeSlots,
                    (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hmono : (∫ p, ∑ ji ∈ activeSlots, (slot α ji (G n) p.1 p.2 * slot α ji f p.1 p.2
              * η k p.1 p.2) ∂Qμ)
          ≤ ∫ p, ((1 / 2) * (∑ ji ∈ activeSlots,
                (slot α ji (G n) p.1 p.2) ^ 2 * η k p.1 p.2)
              + (1 / 2) * (∑ ji ∈ activeSlots,
                (slot α ji f p.1 p.2) ^ 2 * η k p.1 p.2)) ∂Qμ :=
        integral_mono_ae hint1 (Integrable.add hint2a hint2b) hamgm
      refine le_trans hmono ?_
      rw [MeasureTheory.integral_add hint2a hint2b, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, hsqsum (G n) (hGsm n), hsqsum f hf]
    have hlim_bound : HksqCut α f (η k) ≤ (1 / 2) * B ^ 2 + (1 / 2) * HksqCut α f (η k) :=
      le_of_tendsto' hsum_lim (fun n => le_trans (hbnd n) (by linarith [hcut_n n]))
    linarith
  -- ### pass to the limit in the cut-off
  have hlin : (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2) ∂Qμ)
      ≤ ENNReal.ofReal (B ^ 2) := by
    refine le_trans (lintegral_HkIntegrand_le_iSup_HksqCut hf hηT
      (fun k z θ => (hη01 k z θ).1) hηtend) ?_
    refine iSup_le (fun k => ?_)
    exact ENNReal.ofReal_le_ofReal (hkey k)
  have hsq : Work.Spaces.HkSq α 4 f ≤ B ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)).mp
      (le_trans (ofReal_HkSq_le_lintegral f hf) hlin)
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B := Real.sqrt_sq hBnn

end Work.FTS.Apriori.Limit
