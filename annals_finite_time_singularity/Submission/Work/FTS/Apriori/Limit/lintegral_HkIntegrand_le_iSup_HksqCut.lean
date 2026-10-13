/-
# `lintegral_HkIntegrand_le_iSup_HksqCut` — Fatou for an exhausting family of cut-offs

The `ℋ⁴`-energy of the lower semicontinuity argument is the *`lintegral`*
`∫⁻_p ofReal (HkIntegrand α 4 f p.1 p.2) ∂Qμ` of the nonnegative integrand, while the
quantities that an approximating sequence of profiles controls are the *cut-off energies*
`HksqCut α f η_k = ∫_p HkIntegrand α 4 f p.1 p.2 · η_k p.1 p.2 ∂Qμ`.

The link is Fatou's lemma: the cut-offs `η_k` are `TestQ` (smooth on the open quadrant
`Qd = (0,∞) × (0,π/2)`, compact support inside it), nonnegative, and tend to `1` pointwise on
`Qd`.  Since `HkIntegrand α 4 f ≥ 0` and the product measure `Qμ = dz dθ |_{Iz ×ˢ Iθ}` is
concentrated on the closed quadrant `Iz ×ˢ Iθ = [0,∞) × [0,π/2]`, the pointwise limit
`HkIntegrand · η_k → HkIntegrand` holds almost everywhere (`Qμ` gives null measure to
`{z = 0}`, `{θ = 0}` and `{θ = π/2}`, and `HkIntegrand` vanishes identically on `{z = 0}` anyway,
so only the *angular* endpoints need the a.e. argument).  Fatou then gives

`∫⁻ ofReal (HkIntegrand) ≤ liminf_k ∫⁻ ofReal (HkIntegrand · η_k)`

and each term on the right is `ofReal (HksqCut α f η_k)` because `HkIntegrand · η_k` is
integrable (continuous on `Qd`, compactly supported inside it).

No boundedness of the cut-offs is needed: Fatou requires no domination.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

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

/-! ## Elementary helpers -/

/-- The `liminf` of a sequence in `ℝ≥0∞` is at most its supremum: `liminf u ≤ ⨆ n, u n`. -/
theorem liminf_le_iSup_nat (u : ℕ → ℝ≥0∞) : Filter.liminf u Filter.atTop ≤ ⨆ n, u n := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun n => ?_
  exact le_trans (le_trans (iInf_le _ n) (iInf_le _ le_rfl)) (le_iSup _ n)

/-- The horizontal line `{θ = c}` is `Qμ`-null. -/
theorem measure_Qmu_snd_eq (c : ℝ) : Qμ {p : ℝ × ℝ | p.2 = c} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 = c} :=
    (measurableSet_singleton c).preimage measurable_snd
  rw [Qμ_eq_restrict, Measure.restrict_apply hmeas]
  have hsub : ({p : ℝ × ℝ | p.2 = c} ∩ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
      ⊆ Set.univ ×ˢ ({c} : Set ℝ) := fun p hp => ⟨Set.mem_univ _, hp.1⟩
  refine measure_mono_null hsub ?_
  rw [Measure.prod_prod]
  simp

/-- The product measure `Qμ` is concentrated on the closed quadrant `Iz ×ˢ Iθ`. -/
theorem ae_Qmu_mem_Dom : ∀ᵐ p ∂Qμ, p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  rw [Qμ_eq_restrict]
  exact ae_restrict_of_forall_mem (measurableSet_Ici.prod measurableSet_Icc) fun _ hp => hp

/-- Almost every point of the closed quadrant has angular coordinate away from the two
endpoints `0` and `π/2`. -/
theorem ae_Qmu_snd_ne : ∀ᵐ p ∂Qμ, p.2 ≠ 0 ∧ p.2 ≠ π / 2 := by
  have h1 : ∀ᵐ p ∂Qμ, p.2 ≠ 0 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬p.2 ≠ 0} = {p : ℝ × ℝ | p.2 = 0} := by ext p; simp
    rw [hset]; exact measure_Qmu_snd_eq 0
  have h2 : ∀ᵐ p ∂Qμ, p.2 ≠ π / 2 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬p.2 ≠ π / 2} = {p : ℝ × ℝ | p.2 = π / 2} := by ext p; simp
    rw [hset]; exact measure_Qmu_snd_eq (π / 2)
  exact h1.and h2

/-! ## Fatou's lemma for an exhausting family of cut-offs -/

/-- **Fatou for an exhausting family of cut-offs.**  Let `G` be nonnegative, continuous on the
open quadrant and vanishing on the axis `z = 0`, and let `η_k` be test functions of the open
quadrant (`TestQ`), nonnegative, tending to `1` pointwise there.  If every product
`G · η_k` is integrable for `Qμ`, then

`∫⁻ ofReal (G) ≤ ⨆ k, ofReal (∫ G · η_k)`.

This is Fatou's lemma combined with the a.e. convergence `G · η_k → G` on `Qμ`: the pointwise
`liminf` of `ofReal (G · η_k)` is `ofReal (G)` a.e. because the axis `z = 0` (where `G` vanishes)
and the two angular endpoints together form a null set, while on the open quadrant `η_k → 1`. -/
theorem lintegral_le_iSup_integral_mul_of_tendsto_one {G : ℝ × ℝ → ℝ}
    (hG : ContinuousOn G Qd) (hGnn : ∀ p, 0 ≤ G p)
    {η : ℕ → ℝ → ℝ → ℝ} (hη : ∀ k, TestQ (η k)) (h0 : ∀ k (p : ℝ × ℝ), 0 ≤ η k p.1 p.2)
    (htend : ∀ p ∈ Qd, Tendsto (fun k => η k p.1 p.2) atTop (nhds 1))
    (hz0 : ∀ p, p.1 = 0 → G p = 0)
    (hint : ∀ k, Integrable (fun p : ℝ × ℝ => G p * η k p.1 p.2) Qμ) :
    (∫⁻ p, ENNReal.ofReal (G p) ∂Qμ)
      ≤ ⨆ k, ENNReal.ofReal (∫ p, G p * η k p.1 p.2 ∂Qμ) := by
  -- Measurability of the approximating functions, from continuity on the open quadrant.
  have hmeas : ∀ k, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (G p * η k p.1 p.2)) Qμ := by
    intro k
    have hcont := hG.mul (hη k).1.continuousOn
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable
  -- Fatou.
  have hfatou := MeasureTheory.lintegral_liminf_le' (μ := Qμ)
    (f := fun k p => ENNReal.ofReal (G p * η k p.1 p.2)) (u := Filter.atTop) hmeas
  -- The pointwise `liminf` is `ofReal G` almost everywhere.
  have hae : (fun p : ℝ × ℝ => ENNReal.ofReal (G p))
      =ᵐ[Qμ] (fun p => Filter.liminf
        (fun k => ENNReal.ofReal (G p * η k p.1 p.2)) Filter.atTop) := by
    filter_upwards [ae_Qmu_mem_Dom, ae_Qmu_snd_ne] with p hp hθ
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with hz | hz
    · -- `p` lies in the open quadrant, where `η_k p → 1`
      have hpos : 0 < p.2 := lt_of_le_of_ne' hp.2.1 hθ.1
      have hlt : p.2 < π / 2 := lt_of_le_of_ne hp.2.2 hθ.2
      have hpQ : p ∈ Qd := ⟨hz, hpos, hlt⟩
      have h1 : Tendsto (fun k => η k p.1 p.2) Filter.atTop (nhds 1) := htend p hpQ
      have h2 : Tendsto (fun k : ℕ => G p * η k p.1 p.2) Filter.atTop (nhds (G p)) := by
        simpa using (tendsto_const_nhds.mul h1)
      exact (Filter.Tendsto.liminf_eq
        ((ENNReal.continuous_ofReal.tendsto (G p)).comp h2)).symm
    · -- `p.1 = 0`, where `G` vanishes and every `η_k` is `0` outside the quadrant
      have hG0 : G p = 0 := hz0 p hz.symm
      have hconst : (fun k : ℕ => ENNReal.ofReal (G p * η k p.1 p.2))
          = fun _ : ℕ => ENNReal.ofReal (G p) := by
        funext k
        rw [hG0, ← hz]
        simp
      rw [hconst]
      exact (Filter.Tendsto.liminf_eq tendsto_const_nhds).symm
  -- Each `lintegral` is `ofReal` of the corresponding Bochner integral.
  have hlin : (fun k => ∫⁻ p, ENNReal.ofReal (G p * η k p.1 p.2) ∂Qμ)
      = fun k => ENNReal.ofReal (∫ p, G p * η k p.1 p.2 ∂Qμ) := by
    funext k
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint k)
      (Filter.Eventually.of_forall fun p => mul_nonneg (hGnn p) (h0 k p))).symm
  calc (∫⁻ p, ENNReal.ofReal (G p) ∂Qμ)
      = ∫⁻ p, Filter.liminf (fun k => ENNReal.ofReal (G p * η k p.1 p.2))
          Filter.atTop ∂Qμ := MeasureTheory.lintegral_congr_ae hae
    _ ≤ Filter.liminf (fun k => ∫⁻ p, ENNReal.ofReal (G p * η k p.1 p.2) ∂Qμ)
          Filter.atTop := hfatou
    _ = Filter.liminf (fun k => ENNReal.ofReal (∫ p, G p * η k p.1 p.2 ∂Qμ))
          Filter.atTop := by rw [hlin]
    _ ≤ ⨆ k, ENNReal.ofReal (∫ p, G p * η k p.1 p.2 ∂Qμ) :=
        liminf_le_iSup_nat _

/-! ## The target -/

theorem lintegral_HkIntegrand_le_iSup_HksqCut {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) {η : ℕ → ℝ → ℝ → ℝ}
    (hη : ∀ k, Work.FTS.Apriori.Limit.TestQ (η k)) (h0 : ∀ k z θ, 0 ≤ η k z θ)
    (htend : ∀ z θ, (z, θ) ∈ Work.FTS.Apriori.Limit.Qd →
      Filter.Tendsto (fun k => η k z θ) Filter.atTop (nhds 1)) :
    MeasureTheory.lintegral Work.FTS.Apriori.Limit.Qμ
        (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      ≤ ⨆ k, ENNReal.ofReal (Work.FTS.Apriori.Limit.HksqCut α f (η k)) := by
  -- The `ℋ⁴`-integrand is continuous on the open quadrant and nonnegative.
  have hG : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) Qd :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hf
  have hGnn : ∀ p : ℝ × ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2 :=
    fun p => Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2
  -- The cut-offs are continuous on the open quadrant.
  have hηcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ => η k p.1 p.2) Qd :=
    fun k => (hη k).1.continuousOn
  -- Each product is integrable: continuous on `Qd`, compactly supported inside it.
  have hint : ∀ k, Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 4 f p.1 p.2 * η k p.1 p.2) Qμ := fun k =>
    integrable_of_continuousOn_of_support (hG.mul (hηcont k)) (hη k).2.1 (hη k).2.2
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport _))
  have hmain := lintegral_le_iSup_integral_mul_of_tendsto_one
    (G := fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
    hG hGnn hη (fun k p => h0 k p.1 p.2)
    (fun p hp => htend p.1 p.2 hp)
    (fun p hp => by rw [hp]; exact Work.Spaces.HkIntegrand_zero_z α 4 f p.2)
    hint
  simpa only [HksqCut] using hmain

end Work.FTS.Apriori.Limit
