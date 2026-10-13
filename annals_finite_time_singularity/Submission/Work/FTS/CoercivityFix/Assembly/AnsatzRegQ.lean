/-
# `Assembly/AnsatzRegQ.lean` — membership of the counterexample in `RegQ`

`RegQ α k f` is (smoothness on the open quadrant) ∧ (`ℋ^k`-membership) ∧ (the boundary
traces of `Submission/Work/FTS/Vocab.lean`).  For the product ansatz `f = ψ·g` with `ψ = psiA`
and `g = hA δ`:

* smoothness is `ContDiff` of the product of the two `C^∞` bumps;
* `ℋ^k`-membership is `HkMem_prod`, whose side conditions are the term-wise integrability
  facts `integrableOn_vzIter_sq` / `integrableOn_vthIter_sq` (the slots are compactly
  supported inside the quadrant);
* the boundary traces hold because every `mixed b a (psiA ⊗ hA δ)` is supported inside
  `[1/2, 9/2] × [θ₀-2δ, θ₀+2δ]`, a compact subset of the open quadrant.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzEval
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsymB
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Positivity of the first radial slot -/

theorem Zc_psiA_zero_pos : 0 < Zc psiA 0 := by
  have hpt : ∀ z ∈ Set.Icc (3 / 2 : ℝ) (7 / 2), (1 : ℝ) ≤ (psiA z * Work.Spaces.w z) ^ 2 := by
    intro z hz
    rw [Set.mem_Icc] at hz
    have hchi : psiA z = 1 := by
      rw [psiA, Work.Stability.chi_eq_one]
      rw [abs_le]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [hchi, one_mul]
    have hz0 : 0 < z := by linarith [hz.1]
    have hw : (1 : ℝ) ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith [hw]
  have hInt1 : IntegrableOn (fun z => (psiA z * Work.Spaces.w z) ^ 2)
      (Set.Icc (3 / 2 : ℝ) (7 / 2)) := by
    have hcont : ContinuousOn (fun z => (psiA z * Work.Spaces.w z) ^ 2)
        (Set.Icc (3 / 2 : ℝ) (7 / 2)) := by
      refine (((contDiff_psiA.continuous.continuousOn).mul ?_).pow 2)
      change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc (3 / 2 : ℝ) (7 / 2))
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => ?_)
      rw [Set.mem_Icc] at hz
      exact pow_ne_zero 2 (by linarith [hz.1])
    exact hcont.integrableOn_compact isCompact_Icc
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (3 / 2 : ℝ) (7 / 2)) :=
    integrableOn_const (μ := volume) (s := Set.Icc (3 / 2 : ℝ) (7 / 2)) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hmono : (∫ z in Set.Icc (3 / 2 : ℝ) (7 / 2), (1 : ℝ))
      ≤ ∫ z in Set.Icc (3 / 2 : ℝ) (7 / 2), (psiA z * Work.Spaces.w z) ^ 2 := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => zero_le_one)
      hInt1 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => hpt z hz
  have hval : (∫ z in Set.Icc (3 / 2 : ℝ) (7 / 2), (1 : ℝ)) = 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, mul_one]
    norm_num
  have hle : (∫ z in Set.Icc (3 / 2 : ℝ) (7 / 2), (psiA z * Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, (psiA z * Work.Spaces.w z) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_vzIter_sq 0)
      (Filter.Eventually.of_forall fun z => sq_nonneg _) ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    simp only [Set.mem_Icc] at hz
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith [hz.1]
  have : (2 : ℝ) ≤ Zc psiA 0 := by
    rw [Zc]
    have h2 : (2 : ℝ) ≤ ∫ z in Set.Icc (3 / 2 : ℝ) (7 / 2), (psiA z * Work.Spaces.w z) ^ 2 := by
      linarith [hval, hmono]
    exact h2.trans hle
  linarith

/-! ## `ℋ^k`-membership of a product -/

/-- **`ℋ^k`-membership of a product**, from the term-wise integrability of its slots. -/
theorem HkMem_prod (α : ℝ) (k : ℕ) (ψ g : ℝ → ℝ)
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ)
    (hg : ContDiff ℝ Work.Stability.smoothOrder g)
    (hU : ∀ p ∈ SlotS k, IntegrableOn (SlotU ψ k p) Work.Spaces.Iz)
    (hV : ∀ p ∈ SlotS k, IntegrableOn (SlotV α g p) Work.Spaces.Iθ) :
    Work.Spaces.HkMem α k (fun z θ => ψ z * g θ) := by
  constructor
  · intro z _
    have hcongr : ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => ψ z * g θ) z θ
          = ∑ p ∈ SlotS k, SlotU ψ k p z * SlotV α g p θ :=
      fun θ hθ => HkIntegrand_slots α k ψ g hψ hg hθ
    have hsum : IntegrableOn (fun θ => ∑ p ∈ SlotS k, SlotU ψ k p z * SlotV α g p θ)
        Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum (SlotS k) (fun p hp => (hV p hp).const_mul _)
    exact hsum.congr_fun (fun θ hθ => (hcongr θ hθ).symm) measurableSet_Icc
  · have hIθ : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hpt : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => ψ z * g θ) z θ)
          = ∑ p ∈ SlotS k, SlotU ψ k p z * (∫ θ in Work.Spaces.Iθ, SlotV α g p θ) := by
      intro z
      rw [MeasureTheory.setIntegral_congr_fun hIθ
        (fun θ hθ => HkIntegrand_slots α k ψ g hψ hg hθ)]
      rw [MeasureTheory.integral_finsetSum]
      · exact Finset.sum_congr rfl fun p _ => by rw [MeasureTheory.integral_const_mul]
      · intro p hp
        exact (hV p hp).const_mul _
    have hfin : IntegrableOn (fun z => ∑ p ∈ SlotS k,
        SlotU ψ k p z * (∫ θ in Work.Spaces.Iθ, SlotV α g p θ)) Work.Spaces.Iz :=
      MeasureTheory.integrable_finsetSum (SlotS k)
        (fun p hp => (hU p hp).mul_const _)
    refine hfin.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (hpt z).symm

/-! ## The two slot-integrability instantiations for the ansatz -/

theorem slotU_integrable (k : ℕ) :
    ∀ p ∈ SlotS k, IntegrableOn (SlotU psiA k p) Work.Spaces.Iz := by
  intro p _
  rcases p with i | ⟨i, j⟩
  · have hfun : SlotU psiA k (Sum.inl i)
        = fun z => (vzIter i psiA z * Work.Spaces.w z) ^ 2 := by
      funext z; rw [SlotU_inl]
    rw [hfun]
    exact integrableOn_vzIter_sq i
  · by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hfun : SlotU psiA k (Sum.inr (i, j))
          = fun z => (vzIter j psiA z * Work.Spaces.w z) ^ 2 := by
        funext z; rw [SlotU_inr, if_pos hc]
      rw [hfun]
      exact integrableOn_vzIter_sq j
    · have hfun : SlotU psiA k (Sum.inr (i, j)) = fun _ => (0 : ℝ) := by
        funext z; rw [SlotU_inr, if_neg hc]
      rw [hfun]
      exact integrableOn_zero

theorem slotV_integrable (α : ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (i : ℕ) :
    IntegrableOn (fun θ => (vthIter i (hA δ) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
  integrableOn_vthIter_sq δ hδ0 hδ1 i Work.Spaces.eta

theorem slotV_integrable_hA (α : ℝ) (k : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ∀ p ∈ SlotS k, IntegrableOn (SlotV α (hA δ) p) Work.Spaces.Iθ := by
  intro p _
  rcases p with i | ⟨i, j⟩
  · have hfun : SlotV α (hA δ) (Sum.inl i)
        = fun θ => (vthIter 0 (hA δ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      funext θ; rw [SlotV_inl, vthIter_zero]
    rw [hfun]
    exact integrableOn_vthIter_sq δ hδ0 hδ1 0 Work.Spaces.eta
  · have hfun : SlotV α (hA δ) (Sum.inr (i, j))
        = fun θ => (vthIter i (hA δ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      funext θ; rw [SlotV_inr]
    rw [hfun]
    exact integrableOn_vthIter_sq δ hδ0 hδ1 i (Work.Spaces.gam α)

theorem slotV_integrable_vth (α : ℝ) (k : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ∀ p ∈ SlotS k, IntegrableOn (SlotV α (vthIter 1 (hA δ)) p) Work.Spaces.Iθ := by
  intro p _
  rcases p with i | ⟨i, j⟩
  · have hfun : SlotV α (vthIter 1 (hA δ)) (Sum.inl i)
        = fun θ => (vthIter 1 (hA δ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      funext θ; rw [SlotV_inl]
    rw [hfun]
    exact integrableOn_vthIter_sq δ hδ0 hδ1 1 Work.Spaces.eta
  · have hfun : SlotV α (vthIter 1 (hA δ)) (Sum.inr (i, j))
        = fun θ => (vthIter (i + 1) (hA δ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      funext θ
      rw [SlotV_inr, vthIter_add i 1 (hA δ)]
    rw [hfun]
    exact integrableOn_vthIter_sq δ hδ0 hδ1 (i + 1) (Work.Spaces.gam α)

/-! ## The boundary traces -/

theorem tendsto_zero_of_eventually_eq_zero {l : Filter ℝ} {f : ℝ → ℝ}
    (h : ∀ᶠ x in l, f x = 0) : Filter.Tendsto f l (𝓝 0) := by
  have h' : f =ᶠ[l] fun _ => (0 : ℝ) := h
  exact Filter.Tendsto.congr' h'.symm tendsto_const_nhds

theorem BdryTraces_ansatz (α : ℝ) (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Work.FTS.Nonlin.BdryTraces α (n + 2) (ansatz δ) := by
  intro a b _
  have hmix : ∀ z θ : ℝ, Work.Spaces.mixed b a (ansatz δ) z θ
      = vzIter b psiA z * vthIter a (hA δ) θ := by
    intro z θ
    have h := congrFun (congrFun
      (mixed_prod b a psiA (hA δ) contDiff_psiA (contDiff_hA δ)) z) θ
    have h2 : (fun z θ => psiA z * hA δ θ) = ansatz δ := rfl
    rw [h2] at h
    exact h
  have hz_lt : (0 : ℝ) < 1 / 2 := by norm_num
  have hz_gt : th0 + 2 * δ < Real.pi / 2 := by
    rw [th0]; have := Real.pi_gt_three; linarith
  have hθ_lt : (0 : ℝ) < th0 - 2 * δ := by
    rw [th0]; linarith
  constructor
  · intro θ _
    constructor
    · refine tendsto_zero_of_eventually_eq_zero ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hz_lt] with z hz _
      simp only [Set.mem_Iio] at hz
      rw [hmix, vzIter_psiA_eq_zero (j := b) (by
        rw [Set.mem_Icc, not_and_or]
        exact Or.inl (by intro h; linarith [hz, h]))]
      simp
    · refine tendsto_zero_of_eventually_eq_zero ?_
      filter_upwards [eventually_gt_atTop ((9 : ℝ) / 2)] with z hz
      rw [hmix, vzIter_psiA_eq_zero (j := b) (by
        rw [Set.mem_Icc, not_and_or]
        exact Or.inr (by intro h; linarith [hz, h]))]
      simp
  · intro z _
    constructor
    · refine tendsto_zero_of_eventually_eq_zero ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hθ_lt] with θ hθ _
      simp only [Set.mem_Iio] at hθ
      rw [hmix, vthIter_hA_eq_zero hδ0 (i := a) (by
        rw [Set.mem_Icc, not_and_or]
        exact Or.inl (by intro h; linarith [hθ, h]))]
      simp
    · refine tendsto_zero_of_eventually_eq_zero ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds hz_gt] with θ hθ _
      simp only [Set.mem_Ioi] at hθ
      rw [hmix, vthIter_hA_eq_zero hδ0 (i := a) (by
        rw [Set.mem_Icc, not_and_or]
        exact Or.inr (by intro h; linarith [hθ, h]))]
      simp

/-! ## Membership in `RegQ` -/

theorem SmoothQuad_ansatz (δ : ℝ) : Work.FTS.LocData.SmoothQuad (ansatz δ) := by
  have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => psiA p.1) :=
    contDiff_psiA.comp contDiff_fst
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => hA δ p.2) :=
    (contDiff_hA δ).comp contDiff_snd
  have h3 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => psiA p.1 * hA δ p.2) :=
    h1.mul h2
  have h4 : Function.uncurry (ansatz δ) = fun p : ℝ × ℝ => psiA p.1 * hA δ p.2 := rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (ansatz δ))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
  rw [h4]
  exact h3.contDiffOn

theorem HkMem_ansatz (α : ℝ) (k : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Work.Spaces.HkMem α k (ansatz δ) := by
  have h := HkMem_prod α k psiA (hA δ) contDiff_psiA (contDiff_hA δ)
    (slotU_integrable k) (slotV_integrable_hA α k δ hδ0 hδ1)
  have h2 : (fun z θ => psiA z * hA δ θ) = ansatz δ := rfl
  rw [h2] at h
  exact h

/-- **The counterexample lies in `RegQ α k`** for every `k` and every `δ ≤ 1/8`. -/
theorem RegQ_ansatz (α : ℝ) (k : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Work.FTS.Nonlin.RegQ α (k + 2) (ansatz δ) :=
  ⟨SmoothQuad_ansatz δ, HkMem_ansatz α (k + 2) δ hδ0 hδ1,
    BdryTraces_ansatz α k δ hδ0 hδ1⟩

end Work.FTS.CoercivityFix.Assembly
