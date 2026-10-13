/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/PerzNoTraces.lean` — the per-`z` energy bound of the level-`4`
# `ℋ`-integrand, with NO trace hypothesis

**Finding.**  `Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le` declares the hypothesis
`BdryTraces α 6 f`, but **its proof never uses it** (`intro α hα f hF hmem htr i hi z hz`; the body
only touches `hF`, `hmem`, `hzpos`, `hR`, `hσθ`, `hσint` — the per-`σ` window bound is the purely
radial inequality `Work.FTS.StrongEps.E5Aux.zslot_window_perz`, which has no trace input).  The same
hypothesis is therefore spurious all the way up: the per-`z` bound
`HkIntegrand_perz_le_of_traces`, and hence the whole `(H4)` chapter
(`EpsEngine/NOTES_HkMemIterAll.md`) which reported the trace data
`BdryTraces α 6 (Feps u)` as its single remaining input, does not need it at all.

This module records the correct (strictly stronger) statements:

* `HkIntegrand_zslot_perz_le_noTraces` — the `z`-slots, without `BdryTraces`;
* `HkIntegrand_perz_le_noTraces` — the level-4 per-`z` bound, without `BdryTraces`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.E5Aux.zslot_window_perz
import Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_four_perz_le
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum_nt {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

private lemma integrableOn_if_mixed_nt (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 4
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The `z`-slots, without traces -/

/-- **The `z`-slots of the level-`4` integrand, per `z`, with no boundary-trace hypothesis.** -/
theorem HkIntegrand_zslot_perz_le_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα f hF hmem i hi z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hzero : (fun θ : ℝ => (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hw0, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hzero]
    have h1 : (∫ _θ in Work.Spaces.Iθ, (0 : ℝ)) = 0 := by simp
    rw [h1]
    have h2 : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (1 : ℝ) + (Work.Spaces.w 0) ^ 2 := by rw [hw0]; norm_num
    nlinarith [h2, h3]
  · -- ### `z > 0`: the window bound at every angle, then integrate in `θ`
    have hR : z ≤ max z 2 := le_max_left z 2
    have hRpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : (2 : ℝ) ≤ max z 2 := le_max_right z 2
    obtain ⟨hswap, hGint, hGslice⟩ :=
      Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
    -- almost every angle is interior
    have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)] with σ h
      exact fun hmem' => h.mpr hmem'
    -- the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ)) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 6 i (by omega) hzpos hR hσθ hσint
    -- integrability of the two sides
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_zSummand α 6 hF hmem i (by omega)
        (Set.mem_Ici.mpr hzpos.le)
    have hRI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 6 f s σ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hGint.const_mul ((Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2))
    -- the integral bound
    have hmain : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := by
      have h1 := MeasureTheory.integral_mono_ae hLI hRI hle
      rw [MeasureTheory.integral_const_mul, hswap] at h1
      exact h1
    -- the coefficient is at most `3`
    have hcoef : 2 + 2 / max z 2 ≤ 3 := by
      have h : 2 / max z 2 ≤ 1 := by
        rw [div_le_one hRpos]
        exact h2max
      linarith
    have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hXsq : Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
      have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
      rw [h4]
      nlinarith [Real.sq_sqrt hHknn, hXnn, hHknn]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 6 f := hmain
      _ ≤ (Work.Spaces.w z) ^ 2 * 3 * Work.Spaces.HkSq α 6 f := by
          have h := mul_le_mul_of_nonneg_right hcoef hHknn
          nlinarith [h, sq_nonneg (Work.Spaces.w z)]
      _ ≤ 3 * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
          have hstep : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 6 f
              ≤ (1 + (Work.Spaces.w z) ^ 2)
                * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
            mul_le_mul (by linarith [sq_nonneg (Work.Spaces.w z)]) hXsq hHknn
              (by linarith [sq_nonneg (Work.Spaces.w z)])
          nlinarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 3)]

/-! ## The level-`4` per-`z` bound, without traces -/

/-- **The per-`z` bound of the level-`4` `ℋ`-integrand, with no boundary-trace hypothesis.** -/
theorem HkIntegrand_perz_le_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zslot_perz_le_noTraces
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.StrongEps.E5Aux.mixed_slot_perz_le
  refine ⟨5 * Cz + 25 * Cm, by positivity, ?_⟩
  intro α f hα hreg hmem6 z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem6
  have hXsq : Work.Spaces.HkSq α 6 f ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
    have h2 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have h3 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
    rw [h4]
    nlinarith [Real.sq_sqrt h2, h3, h2]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 4 f θ]
      simp
    rw [hzero]
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hcoef : 0 < 5 * Cz + 25 * Cm := by positivity
    nlinarith [hX0]
  · -- the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_nt _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg
        hmem4 i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_nt _
        (fun i _ => integrable_finsetSum_nt _
          (fun j _ => integrableOn_if_mixed_nt α hreg hmem4 i j hzpos))
    have hdef : (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ; rw [Work.Spaces.HkIntegrand]
    rw [hdef, MeasureTheory.integral_add hPint hMint]
    -- the bound for the pure-`z` part
    have hPbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg hmem4 i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) :=
            Finset.sum_le_sum fun i hi => hCz α hαI hreg hmem6 i
              (by rw [Finset.mem_range] at hi; omega) z hz
        _ = 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    -- the bound for the mixed part
    have hMbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i _ =>
        integrable_finsetSum_nt _ (fun j _ => integrableOn_if_mixed_nt α hreg hmem4 i j hzpos))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 5, (5 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α 6 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun j _ =>
              integrableOn_if_mixed_nt α hreg hmem4 i j hzpos)]
            calc ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ 4
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range 5, (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α 6 f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ 4
                  · simp only [if_pos hij]
                    exact hCm α hαI hreg hmem6 i j hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
                      have := Work.Spaces.HkSq_nonneg α 6 f
                      positivity
                    simpa using h1
              _ = 5 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine le_trans (add_le_add hPbound hMbound) ?_
    have hPnn : 0 ≤ (1 : ℝ) + (Work.Spaces.w z) ^ 2 := by positivity
    have hX2nn : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have hkey : 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f)
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      have h1 : Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f
          ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
        mul_le_mul_of_nonneg_left hXsq (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hsum : 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2)
        + 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2)
        = (5 * Cz + 25 * Cm) * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by ring
    exact le_trans (add_le_add le_rfl hkey) (le_of_eq hsum)

end Work.FTS.EpsEngine
