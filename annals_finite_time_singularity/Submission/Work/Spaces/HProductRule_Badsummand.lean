import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_g_bound
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.AesmSqProdSmooth
import Submission.Work.Spaces.GoodTermSqBound
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.MixedSqPointwiseBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Private scaffolding -/

private def lT (f g : ℝ → ℝ → ℝ) (p : ℕ × ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => mixed p.2 p.1 f z θ * mixed (3 - p.2) (1 - p.1) g z θ

private def lY (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℕ × ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => lT f g p z θ * Wt α z θ

private def lC (p : ℕ × ℕ) : ℝ := (Nat.choose 1 p.1 : ℝ) * (Nat.choose 3 p.2 : ℝ)

private def lP : Finset (ℕ × ℕ) := Finset.range 2 ×ˢ Finset.range 4

private lemma lP_card : lP.card = 8 := by
  simp [lP, Finset.card_product]

private lemma lC_sq_le : ∀ p ∈ lP, (lC p) ^ 2 ≤ 9 := by
  intro p hp
  obtain ⟨a, b⟩ := p
  simp only [lP, Finset.mem_product, Finset.mem_range] at hp
  obtain ⟨ha, hb⟩ := hp
  interval_cases a <;> interval_cases b <;> simp only [lC] <;> norm_num

private lemma SmoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothNbhd f) (hg : SmoothNbhd g) :
    SmoothNbhd (fun z θ => f z θ * g z θ) := hf.mul hg

private lemma SmoothInt_of_SmoothNbhd {g : ℝ → ℝ → ℝ} (h : SmoothNbhd g) : SmoothInt g := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

private lemma Integrable_congr_fun' {F G : ℝ → ℝ} {μ : Measure ℝ} (h : ∀ x, F x = G x)
    (hF : Integrable F μ) : Integrable G μ :=
  hF.congr (Filter.Eventually.of_forall h)

private lemma integral_congr_fun' {F G : ℝ → ℝ} {μ : Measure ℝ} (h : ∀ x, F x = G x) :
    ∫ x, F x ∂μ = ∫ x, G x ∂μ :=
  MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h)

/-! ## The main lemma -/

theorem HProductRule_Badsummand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsimg : Work.Spaces.SmoothNbhd g)
    (hvtf : Work.Spaces.VanishTheta f) (hvtg : Work.Spaces.VanishTheta g)
    (hdecf : Work.Spaces.DecayAll 4 f) (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.mixed 3 1 (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ)
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 3 1 (fun z θ => f z θ * g z θ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ (10 ^ 12 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hdecMf : DecayMixed 2 f := fun a b hab θ hθ => hdecf.2 a b (by omega) θ hθ
  have hdecMg : DecayMixed 2 g := fun a b hab θ hθ => hdecg.2 a b (by omega) θ hθ
  have hfg_sm : SmoothNbhd (fun z θ => f z θ * g z θ) := SmoothNbhd_mul hsmf hsimg
  have hfI : SmoothInt f := SmoothInt_of_SmoothNbhd hsmf
  have hgI : SmoothInt g := SmoothInt_of_SmoothNbhd hsimg
  -- the Leibniz expansion
  have hleib : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      mixed 3 1 (fun z θ => f z θ * g z θ) z θ = ∑ p ∈ lP, lC p * lT f g p z θ := by
    intro z hz θ hθ
    rw [mixed_mul_eq 3 1 f g hfI hgI z hz θ hθ]
    simp only [lP, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    simp only [lC, lT]
  -- the pointwise square bound
  have hYsq : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 72 * ∑ p ∈ lP, (lY α f g p z θ) ^ 2 := by
    intro z hz θ hθ
    have hexp : mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ
        = ∑ p ∈ lP, lC p * lY α f g p z θ := by
      rw [hleib z hz θ hθ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p hp => by simp only [lY]; ring
    rw [hexp]
    have h1 := sq_sum_le_card_mul_sum_sq (s := lP) (f := fun p => lC p * lY α f g p z θ)
    calc (∑ p ∈ lP, lC p * lY α f g p z θ) ^ 2
        ≤ (lP.card : ℝ) * ∑ p ∈ lP, (lC p * lY α f g p z θ) ^ 2 := h1
      _ = 8 * ∑ p ∈ lP, (lC p * lY α f g p z θ) ^ 2 := by rw [lP_card]; norm_num
      _ ≤ 8 * ∑ p ∈ lP, 9 * (lY α f g p z θ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          refine Finset.sum_le_sum fun p hp => ?_
          calc (lC p * lY α f g p z θ) ^ 2 = (lC p) ^ 2 * (lY α f g p z θ) ^ 2 := by ring
            _ ≤ 9 * (lY α f g p z θ) ^ 2 :=
                mul_le_mul_of_nonneg_right (lC_sq_le p hp) (sq_nonneg _)
      _ = 72 * ∑ p ∈ lP, (lY α f g p z θ) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]; ring_nf
  -- numerical steps
  have hstep_fg : ∀ X : ℝ, X ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g →
      X ≤ 10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine le_trans hX ?_
    have hcoef : (100:ℝ) / (gam α - 1) ≤ 10 ^ 6 / (gam α - 1) :=
      div_le_div_of_nonneg_right (by norm_num) hγ.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
  have hstep_gf : ∀ X : ℝ, X ≤ 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f →
      X ≤ 10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro X hX
    refine le_trans hX ?_
    have hcoef : (100:ℝ) / (gam α - 1) ≤ 10 ^ 6 / (gam α - 1) :=
      div_le_div_of_nonneg_right (by norm_num) hγ.le
    calc 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
        = 100 / (gam α - 1) * (HkSq α 4 g * HkSq α 4 f) := by ring
      _ ≤ 10 ^ 6 / (gam α - 1) * (HkSq α 4 g * HkSq α 4 f) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (HkSq_nonneg α 4 g) (HkSq_nonneg α 4 f))
      _ = 10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
  -- the generic good-term application
  have goodCase : ∀ (A Bv h : ℝ → ℝ → ℝ) (hsA : SmoothNbhd A) (hsBv : SmoothNbhd Bv) (M : ℝ),
      (∀ z ∈ Iz, ∀ θ ∈ Iθ, (A z θ) ^ 2 ≤ M) → HkMem α 4 h →
      (∀ z ∈ Iz, ∀ θ ∈ Iθ, (Bv z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 h z θ) →
      (∀ z ∈ Iz, IntegrableOn (fun θ => (A z θ * Bv z θ * Wt α z θ) ^ 2) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (A z θ * Bv z θ * Wt α z θ) ^ 2) Iz ∧
      ∫ z in Iz, ∫ θ in Iθ, (A z θ * Bv z θ * Wt α z θ) ^ 2 ≤ M * HkSq α 4 h := by
    intro A Bv h hsA hsBv M hAb hhm hBsq
    exact GoodTermSqBound α A Bv h M hhm hAb hBsq
      (fun z hz => (AesmSqProdSmooth α hsA hsBv).2 z hz)
      (AesmSqProdSmooth α hsA hsBv).1
  have goodCaseSw : ∀ (A Bv h : ℝ → ℝ → ℝ) (hsA : SmoothNbhd A) (hsBv : SmoothNbhd Bv) (M : ℝ),
      (∀ z ∈ Iz, ∀ θ ∈ Iθ, (A z θ) ^ 2 ≤ M) → HkMem α 4 h →
      (∀ z ∈ Iz, ∀ θ ∈ Iθ, (Bv z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 h z θ) →
      (∀ z ∈ Iz, IntegrableOn (fun θ => (Bv z θ * A z θ * Wt α z θ) ^ 2) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (Bv z θ * A z θ * Wt α z θ) ^ 2) Iz ∧
      ∫ z in Iz, ∫ θ in Iθ, (Bv z θ * A z θ * Wt α z θ) ^ 2 ≤ M * HkSq α 4 h := by
    intro A Bv h hsA hsBv M hAb hhm hBsq
    have hres := goodCase A Bv h hsA hsBv M hAb hhm hBsq
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact Integrable_congr_fun' (fun θ => by ring) (hres.1 z hz)
    · exact Integrable_congr_fun' (fun z => integral_congr_fun' (fun θ => by ring)) hres.2.1
    · rw [show (∫ z in Iz, ∫ θ in Iθ, (Bv z θ * A z θ * Wt α z θ) ^ 2)
            = ∫ z in Iz, ∫ θ in Iθ, (A z θ * Bv z θ * Wt α z θ) ^ 2 from
          integral_congr_fun' (fun z => integral_congr_fun' (fun θ => by ring))]
      exact hres.2.2
  -- per-term bounds
  have hTerm : ∀ p ∈ lP,
      (∀ z ∈ Iz, IntegrableOn (fun θ => (lY α f g p z θ) ^ 2) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (lY α f g p z θ) ^ 2) Iz ∧
      ∫ z in Iz, ∫ θ in Iθ, (lY α f g p z θ) ^ 2
        ≤ 10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    intro p hp
    obtain ⟨a, b⟩ := p
    simp only [lP, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨ha, hb⟩ := hp
    interval_cases a <;> interval_cases b
    · -- (0,0)
      have hlY : lY α f g (0,0) = fun z θ => (mixed 0 0 f z θ * mixed 3 1 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCase (fun z θ => mixed 0 0 f z θ) (fun z θ => mixed 3 1 g z θ) g
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 0) 0)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 1) 3)
        (100 / (gam α - 1) * HkSq α 4 f)
        (MixedSqPointwiseBound α hα hα1 f hsmf hvtf hdecMf hmemf 0 0 (by norm_num))
        hmemg
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 g z θ 1 3 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_fg _ hres.2.2⟩
    · -- (0,1)
      have hlY : lY α f g (0,1) = fun z θ => (mixed 1 0 f z θ * mixed 2 1 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCase (fun z θ => mixed 1 0 f z θ) (fun z θ => mixed 2 1 g z θ) g
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 0) 1)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 1) 2)
        (100 / (gam α - 1) * HkSq α 4 f)
        (MixedSqPointwiseBound α hα hα1 f hsmf hvtf hdecMf hmemf 1 0 (by norm_num))
        hmemg
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 g z θ 1 2 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_fg _ hres.2.2⟩
    · -- (0,2)
      have hlY : lY α f g (0,2) = fun z θ => (mixed 2 0 f z θ * mixed 1 1 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCase (fun z θ => mixed 2 0 f z θ) (fun z θ => mixed 1 1 g z θ) g
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 0) 2)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 1) 1)
        (100 / (gam α - 1) * HkSq α 4 f)
        (MixedSqPointwiseBound α hα hα1 f hsmf hvtf hdecMf hmemf 2 0 (by norm_num))
        hmemg
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 g z θ 1 1 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_fg _ hres.2.2⟩
    · -- (0,3) : bad term
      have hlY : lY α f g (0,3)
          = fun z θ => (DzIter 3 f z θ * Dth g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have h3 := BadTermSqBound α hα hα1 f g hsmf hvtf hmemf hsimg hdecg.1 hmemg
        (fun z hz => (AesmSqProdSmooth α (SmoothNbhd.DzIter hsmf 3) (SmoothNbhd.Dth hsimg)).2 z hz)
        (AesmSqProdSmooth α (SmoothNbhd.DzIter hsmf 3) (SmoothNbhd.Dth hsimg)).1
      exact ⟨h3.1, h3.2.1, hstep_fg _ h3.2.2⟩
    · -- (1,0) : bad term, roles swapped
      have hlY : lY α f g (1,0)
          = fun z θ => (Dth f z θ * DzIter 3 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have h3 := BadTermSqBound α hα hα1 g f hsimg hvtg hmemg hsmf hdecf.1 hmemf
        (fun z hz => (AesmSqProdSmooth α (SmoothNbhd.DzIter hsimg 3) (SmoothNbhd.Dth hsmf)).2 z hz)
        (AesmSqProdSmooth α (SmoothNbhd.DzIter hsimg 3) (SmoothNbhd.Dth hsmf)).1
      have hEq : (∫ z in Iz, ∫ θ in Iθ, ((Dth f z θ * DzIter 3 g z θ) * Wt α z θ) ^ 2)
          = ∫ z in Iz, ∫ θ in Iθ, ((DzIter 3 g z θ * Dth f z θ) * Wt α z θ) ^ 2 :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z =>
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring))
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        exact Integrable_congr_fun' (fun θ => by ring) (h3.1 z hz)
      · exact Integrable_congr_fun' (fun z =>
          integral_congr_fun' (fun θ => by ring)) h3.2.1
      · rw [hEq]
        exact hstep_gf _ h3.2.2
    · -- (1,1)
      have hlY : lY α f g (1,1) = fun z θ => (mixed 1 1 f z θ * mixed 2 0 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCaseSw (fun z θ => mixed 2 0 g z θ) (fun z θ => mixed 1 1 f z θ) f
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 0) 2)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 1) 1)
        (100 / (gam α - 1) * HkSq α 4 g)
        (MixedSqPointwiseBound α hα hα1 g hsimg hvtg hdecMg hmemg 2 0 (by norm_num))
        hmemf
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 f z θ 1 1 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_gf _ hres.2.2⟩
    · -- (1,2)
      have hlY : lY α f g (1,2) = fun z θ => (mixed 2 1 f z θ * mixed 1 0 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCaseSw (fun z θ => mixed 1 0 g z θ) (fun z θ => mixed 2 1 f z θ) f
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 0) 1)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 1) 2)
        (100 / (gam α - 1) * HkSq α 4 g)
        (MixedSqPointwiseBound α hα hα1 g hsimg hvtg hdecMg hmemg 1 0 (by norm_num))
        hmemf
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 f z θ 1 2 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_gf _ hres.2.2⟩
    · -- (1,3)
      have hlY : lY α f g (1,3) = fun z θ => (mixed 3 1 f z θ * mixed 0 0 g z θ) * Wt α z θ := by funext z θ; rfl
      rw [hlY]
      have hres := goodCaseSw (fun z θ => mixed 0 0 g z θ) (fun z θ => mixed 3 1 f z θ) f
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsimg 0) 0)
        (SmoothNbhd.DzIter (SmoothNbhd.DthIter hsmf 1) 3)
        (100 / (gam α - 1) * HkSq α 4 g)
        (MixedSqPointwiseBound α hα hα1 g hsimg hvtg hdecMg hmemg 0 0 (by norm_num))
        hmemf
        (fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 f z θ 1 3 (by norm_num) (by norm_num))
      exact ⟨hres.1, hres.2.1, hstep_gf _ hres.2.2⟩
  -- assembling
  have hGslice : ∀ z ∈ Iz, IntegrableOn (fun θ => 72 * ∑ p ∈ lP, (lY α f g p z θ) ^ 2) Iθ :=
    fun z hz => (integrable_finsetSum lP (fun p hp => (hTerm p hp).1 z hz)).const_mul 72
  have hGhat_int : IntegrableOn
      (fun z => 72 * ∑ p ∈ lP, ∫ θ in Iθ, (lY α f g p z θ) ^ 2) Iz :=
    (integrable_finsetSum lP (fun p hp => (hTerm p hp).2.1)).const_mul 72
  have hslice_le : ∀ z ∈ Iz,
      ∫ θ in Iθ, (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ 72 * ∑ p ∈ lP, ∫ θ in Iθ, (lY α f g p z θ) ^ 2 := by
    intro z hz
    have h1 : ∫ θ in Iθ, (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, 72 * ∑ p ∈ lP, (lY α f g p z θ) ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        (hGslice z hz)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hYsq z hz θ hθ))
    have h2 : ∫ θ in Iθ, 72 * ∑ p ∈ lP, (lY α f g p z θ) ^ 2
        = 72 * ∑ p ∈ lP, ∫ θ in Iθ, (lY α f g p z θ) ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact integral_finsetSum lP (fun p hp => (hTerm p hp).1 z hz)
    rwa [h2] at h1
  have hF_slice_meas : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ => (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := by
    intro z hz
    have hsmA : SmoothNbhd (fun z θ => mixed 3 1 (fun z θ => f z θ * g z θ) z θ) :=
      SmoothNbhd.DzIter (SmoothNbhd.DthIter hfg_sm 1) 3
    have hsmB : SmoothNbhd (fun _ _ : ℝ => (1 : ℝ)) := contDiffOn_const
    have h := (AesmSqProdSmooth α hsmA hsmB).2 z hz
    simpa only [mul_one] using h
  refine ⟨?_, ?_⟩
  · constructor
    · intro z hz
      refine MeasureTheory.Integrable.mono' (hGslice z hz) (hF_slice_meas z hz) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hYsq z hz θ hθ
    · refine MeasureTheory.Integrable.mono' hGhat_int ?_ ?_
      · exact (aesm_mixed_Wt_sq_prod α (fun z θ => f z θ * g z θ) hfg_sm 3 1).integral_prod_right'
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
        exact hslice_le z hz
  · calc L2Sq (fun z θ => mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
        = ∫ z in Iz, ∫ θ in Iθ, (mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 :=
          rfl
      _ ≤ ∫ z in Iz, 72 * ∑ p ∈ lP, ∫ θ in Iθ, (lY α f g p z θ) ^ 2 := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
            hGhat_int ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
          exact hslice_le z hz
      _ = 72 * ∑ p ∈ lP, ∫ z in Iz, ∫ θ in Iθ, (lY α f g p z θ) ^ 2 := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          exact integral_finsetSum lP (fun p hp => (hTerm p hp).2.1)
      _ ≤ 72 * ∑ p ∈ lP, (10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun p hp => (hTerm p hp).2.2
      _ = 72 * (8 * (10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) := by
          congr 1
          rw [Finset.sum_const, lP_card, nsmul_eq_mul]
          norm_num
      _ ≤ 10 ^ 12 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          have hcoef : (72 : ℝ) * (8 * (10 ^ 6 / (gam α - 1))) ≤ 10 ^ 12 / (gam α - 1) := by
            rw [show (72 : ℝ) * (8 * (10 ^ 6 / (gam α - 1))) = 72 * 8 * 10 ^ 6 / (gam α - 1) by
              ring]
            exact div_le_div_of_nonneg_right (by norm_num) hγ.le
          calc 72 * (8 * (10 ^ 6 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g))
              = (72 * (8 * (10 ^ 6 / (gam α - 1)))) * (HkSq α 4 f * HkSq α 4 g) := by ring
            _ ≤ (10 ^ 12 / (gam α - 1)) * (HkSq α 4 f * HkSq α 4 g) :=
                mul_le_mul_of_nonneg_right hcoef
                  (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
            _ = 10 ^ 12 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.Spaces
