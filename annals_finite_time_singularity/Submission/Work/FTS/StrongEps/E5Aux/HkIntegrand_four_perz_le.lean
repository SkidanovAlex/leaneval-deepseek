/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-`z` bound for the level-`4` `ℋ`-integrand of a class-`C` profile

`Work.FTS.StrongEps.E5Aux.HkIntegrand_four_perz_le`: there is a universal constant `C` with

  `∫_{Iθ} HkIntegrand α 4 f z θ ≤ C * (1 + w z ^ 2) * (1 + |f|_{ℋ⁶}) ^ 2`

for every `α ∈ (0,1]`, every `f` of class `C` (`Work.FTS.ClassC.ClassC α f`) and every
`z ∈ Iz = [0,∞)`.

## Proof

The `ℋ⁴`-integrand is the sum of its `z`-slots and its mixed slots, and the two families are
estimated separately at the fixed `z`:

* **mixed slots** (`(D_z^jD_θ^i f · W)²`, `1 ≤ i`, `i+j ≤ 4`): `W = w z · sin(2θ)^{-γ/2}`, so
  the slot is `(w z)² · (D_z^jD_θ^if)² · sin(2θ)^{-γ}`, and
  `Work.FTS.StrongPersist.N6.sliceAng_le6` bounds its `θ`-integral by `C · |f|²_{ℋ⁶}` with a
  universal constant (`mixed_slot_perz_le` below);
* **`z`-slots** (`(D_z^if · w z/sin(2θ)^{η/2})²`, `i ≤ 4`): here `sin(2θ)^{-η}` is *integrable*
  (η = 99/100 < 1) and no `θ`-Hardy inequality is available (it would cost a factor `1/(γ-1)`,
  which is *not* uniform in `α`); instead one uses the window Agmon inequality
  `Work.FTS.StrongEps.E5Aux.agmon_window` in the radial variable on the window `[z/2,3z/2]`,
  which pays a factor `1/z`, absorbed by `1 + w z ^ 2`.  This is the delegated lemma
  `Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le`.

Since both pieces are bounded by `C·(1 + w z ^ 2)·(1 + |f|_{ℋ⁶})²` (using `HkSq α 6 f = |f|²_{ℋ⁶}`
and `HkSq α 6 f ≤ (1 + |f|_{ℋ⁶})²`), the finite sum of the slots gives the claim.

The `z = 0` case is degenerate (`w 0 = 0` kills every slot, `HkIntegrand_zero_z`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.StrongPersist.N6.sliceAng_le6
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.GalBasis.cc.intervalIntegrable_mixed_div_sin
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
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

/-! ## The per-`z` bound for a mixed slot -/

theorem mixed_slot_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨CB, hCBpos, hCB⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  refine ⟨CB, hCBpos, ?_⟩
  intro α hα f hF hmem i j hi hij z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hcongr :
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hs]
    ring
  rw [hcongr]
  have hb := hCB α f j i hα0 hα1 hF hmem hi (by omega) z hz
  have hHk := Work.Spaces.HkSq_nonneg α 6 f
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (CB * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ CB * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
        nlinarith [hCBpos, hHk, sq_nonneg (Work.Spaces.w z)]

/-! ## Integrability of the individual summands of the level-4 integrand -/

private lemma integrableOn_if_mixed (α : ℝ) {f : ℝ → ℝ → ℝ}
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

/-! ## The target -/

theorem HkIntegrand_four_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.ClassC.ClassC α f → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le
  obtain ⟨Cm, hCmpos, hCm⟩ := mixed_slot_perz_le
  refine ⟨5 * Cz + 25 * Cm, by positivity, ?_⟩
  intro α hα f hf z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hreg : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem7 : Work.Spaces.HkMem α 7 f := hf.mem
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hmem7
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
  have htr : Work.FTS.Nonlin.BdryTraces α 6 f := hf.tr
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
      integrable_finsetSum _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg
        hmem4 i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _
        (fun i _ => integrable_finsetSum _
          (fun j _ => integrableOn_if_mixed α hreg hmem4 i j hzpos))
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
            Finset.sum_le_sum fun i hi => hCz α hαI hreg hmem6 htr i
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
        integrable_finsetSum _ (fun j _ => integrableOn_if_mixed α hreg hmem4 i j hzpos))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 5, (5 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α 6 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun j _ =>
              integrableOn_if_mixed α hreg hmem4 i j hzpos)]
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
    nlinarith [hkey, hPbound, hMbound, hPnn, hX2nn, hXsq, hCzpos, hCmpos,
      Work.Spaces.HkSq_nonneg α 6 f, Work.Spaces.HkNorm_nonneg α 6 f]

end Work.FTS.StrongEps.E5Aux
