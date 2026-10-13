import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.Slots.Wt
import Submission.Work.FTS.PhiStar.Honesty.Slots.Series
import Submission.Work.FTS.PhiStar.Honesty.Slots.SeriesDeriv
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.ClassCHon.CmpSupp.source_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- At level `0` the honest integrand is the weighted square. -/
theorem HkIntegrand_zero_eq_weighted (α : ℝ) (f : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ
        = (f z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  intro z θ hθ
  have h1 : Work.Spaces.HkIntegrand α 0 f z θ = (f z θ) ^ 2
      * (Work.Spaces.w z ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [Work.FTS.ClassCHon.CmpSupp.sf_HkIntegrand_zero_eq, mul_pow,
      Work.FTS.ClassCHon.CmpSupp.sf_Whz_sq_Iθ hθ]
  have h2 : (f z θ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (f z θ) ^ 2 * (Work.Spaces.w z ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [mul_pow, mul_assoc]
    simp only [Work.FTS.EllipticEst.sEta]
  rw [h1, h2]

/-- The level-`0` integrand vanishes at `z = 0` and at `θ = 0`, `θ = π/2`. -/
theorem HkIntegrand_zero_eq_zero_of (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) :
    Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [Work.FTS.ClassCHon.CmpSupp.sf_HkIntegrand_zero_eq]
  have hη : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  rcases h with h | h | h
  · subst h
    simp [Work.Spaces.w]
  · subst h
    rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, Real.zero_rpow hη]
    ring
  · subst h
    rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hη]
    ring

/-- **`H^0`-membership transports across an equality on the open quadrant.** -/
theorem HkMem_zero_of_eq {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) → f z θ = g z θ)
    (hf : Work.Spaces.HkMem α 0 f) : Work.Spaces.HkMem α 0 g := by
  have hkey : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ = Work.Spaces.HkIntegrand α 0 g z θ := by
    intro z θ hz hθ
    by_cases hio : θ ∈ Set.Ioo 0 (π/2)
    · rw [HkIntegrand_zero_eq_weighted α f z θ hθ,
        HkIntegrand_zero_eq_weighted α g z θ hθ, h z θ hz hio]
    · have hθ' : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · exact Or.inl h0.symm
        · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt fun hlt => hio ⟨h0, hlt⟩))
      rw [HkIntegrand_zero_eq_zero_of α f (Or.inr hθ'),
        HkIntegrand_zero_eq_zero_of α g (Or.inr hθ')]
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
    · subst hz0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g 0 θ) = fun _ => (0:ℝ) := by
        funext θ
        exact HkIntegrand_zero_eq_zero_of α g (Or.inl rfl)
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · refine (hf.1 z hz).congr_fun ?_ measurableSet_Icc
      intro θ hθ
      exact hkey z θ hz0 hθ
  · refine hf.2.congr_fun ?_ measurableSet_Ici
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
    · subst hz0
      change (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f 0 θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g 0 θ
      have h0 : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 f 0 θ)
          = fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g 0 θ := by
        funext θ
        rw [HkIntegrand_zero_eq_zero_of α f (Or.inl rfl),
          HkIntegrand_zero_eq_zero_of α g (Or.inl rfl)]
      rw [h0]
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hkey z θ hz0 hθ)] with θ hθ
      exact hθ

theorem slots_psiSeries_of_cptQ (K : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    (∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 → Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter l (Work.Spaces.pthIter m (Work.FTS.PhiStar.Series.psiSeries α G)))) ∧
    (∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α G)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α G)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) := by
  obtain ⟨a, b, c, d, ha, hab', hc, hcd, hd, hsupp_box⟩ := hG.cpt
  have hab : a ≤ b := le_of_lt hab'
  have hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → G z θ = 0 := by
    intro z θ hz
    by_contra h
    exact hz (hsupp_box z θ h).1
  have hφint := integrableOn_phiWt_mul_w_sq hα hα4
  have hneg : -1 < -(Work.Spaces.eta) := by
    rw [Work.Spaces.eta]; norm_num
  have hetapos : (0:ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  constructor
  · intro l m _ _
    obtain ⟨K', hK'pos, hK'bd⟩ := dzS_abs_le hα hα4 hG ha hab hsupp hFs l m
    have hcont := dzS_continuousOn hα hα4 hG ha hab hsupp hFs l m
    obtain ⟨h1, h2⟩ := integrableOn_sq_mul_sin_rpow_of_bound (F := dzS α G l m)
      (φ := phiWt α) (K := K') (e := -(Work.Spaces.eta)) hcont hK'pos.le
      (fun z hz => phiWt_nonneg hz) (fun z hz θ hθ => hK'bd z θ hz hθ) hφint hneg
    have hmemS : Work.Spaces.HkMem α 0 (dzS α G l m) := by
      constructor
      · intro z hz
        rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
        · subst hz0
          have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 (dzS α G l m) 0 θ)
              = fun _ => (0:ℝ) := by
            funext θ
            exact HkIntegrand_zero_eq_zero_of α (dzS α G l m) (Or.inl rfl)
          rw [hzero]
          exact MeasureTheory.integrableOn_zero
        · refine (h1 z hz).congr_fun ?_ measurableSet_Icc
          intro θ hθ
          exact (HkIntegrand_zero_eq_weighted α (dzS α G l m) z θ hθ).symm
      · refine h2.congr_fun ?_ measurableSet_Ici
        intro z hz
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (HkIntegrand_zero_eq_weighted α (dzS α G l m) z θ hθ).symm)]
          with θ hθ
        exact hθ
    exact HkMem_zero_of_eq
      (fun z θ hz hθ => (DzIter_psiSeries_eq_dzS hα hα4 hG ha hab hsupp hFs m l z θ hz hθ).symm)
      hmemS
  · intro t l ht _ _
    obtain ⟨K', hK'pos, hK'bd⟩ := dzS_abs_le hα hα4 hG ha hab hsupp hFs l t
    have hcont := dzS_continuousOn hα hα4 hG ha hab hsupp hFs l t
    have hexp : -1 < 2 * (t : ℝ) - 4 - Work.Spaces.gam α := by
      rw [Work.Spaces.gam]
      have : (3:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    have hne : (2 * (t : ℝ) - 4 - Work.Spaces.gam α) ≠ 0 := by
      have ht' : (3:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have hgam : Work.Spaces.gam α ≤ 3 / 2 := by
        rw [Work.Spaces.gam]
        linarith [hα4]
      exact ne_of_gt (by linarith)
    obtain ⟨h1, h2⟩ := integrableOn_sq_mul_sin_rpow_of_bound (F := dzS α G l t)
      (φ := phiWt α) (K := K') (e := 2 * (t : ℝ) - 4 - Work.Spaces.gam α) hcont hK'pos.le
      (fun z hz => phiWt_nonneg hz) (fun z hz θ hθ => hK'bd z θ hz hθ) hφint hexp
    have hpt : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
        Work.Spaces.DzIter l (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G))
            z θ = dzS α G l t z θ :=
      fun z θ hz hθ => DzIter_psiSeries_eq_dzS hα hα4 hG ha hab hsupp hFs t l z θ hz hθ
    have hzeroexp : ∀ θ : ℝ, θ = 0 ∨ θ = Real.pi / 2 →
        (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) = 0 := by
      intro θ hθ
      rcases hθ with h | h
      · subst h
        rw [show Real.sin (2 * (0:ℝ)) = 0 by norm_num, Real.zero_rpow hne]
      · subst h
        rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi], Real.zero_rpow hne]
    have hkey : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        (Work.Spaces.DzIter l (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G))
            z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)
        = (dzS α G l t z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) := by
      intro z θ hz hθ
      by_cases hio : θ ∈ Set.Ioo 0 (π/2)
      · rw [hpt z θ hz hio]
      · have hθ' : θ = 0 ∨ θ = Real.pi / 2 := by
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · exact Or.inl h0.symm
          · exact Or.inr (le_antisymm hθ.2 (le_of_not_gt fun hlt => hio ⟨h0, hlt⟩))
        rw [hzeroexp θ hθ']
        ring
    constructor
    · intro z hz
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
      · subst hz0
        have hz0' : (fun θ : ℝ => (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
            = fun _ => (0:ℝ) := by
          funext θ
          simp [Work.Spaces.w]
        rw [hz0']
        exact MeasureTheory.integrableOn_zero
      · refine (h1 z hz).congr_fun ?_ measurableSet_Icc
        intro θ hθ
        exact (hkey z θ hz0 hθ).symm
    · refine h2.congr_fun ?_ measurableSet_Ici
      intro z hz
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hz0
      · subst hz0
        change (∫ θ in Work.Spaces.Iθ, (dzS α G l t 0 θ * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)
        have h0 : (fun θ : ℝ => (dzS α G l t 0 θ * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α))
            = fun θ : ℝ => (Work.Spaces.DzIter l
              (Work.Spaces.pthIter t (Work.FTS.PhiStar.Series.psiSeries α G)) 0 θ
                * Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α) := by
          funext θ
          simp [Work.Spaces.w]
        rw [h0]
      · refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (hkey z θ hz0 hθ).symm)] with θ hθ
        exact hθ

end Work.FTS.PhiStar.Honesty
