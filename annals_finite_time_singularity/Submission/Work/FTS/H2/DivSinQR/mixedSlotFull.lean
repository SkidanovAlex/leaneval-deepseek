import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.FTS.H2.DivQ.nearRegionLHS_i
import Submission.Work.FTS.H2.DivQ.middleRegionLHS_i
import Submission.Work.FTS.H2.DivQ.farRegionLHS
import Submission.Work.FTS.H2.DivQ.nearRegionIntegrable
import Submission.Work.FTS.H2.DivQ.reflSlice_facts
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.H2.DivSinQR.zSlotHardy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivSinQR

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Measure-theoretic bookkeeping on the angular interval -/

/-- The measure of `Iθ` only sees the open interval. -/
private lemma restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)).symm

/-- A property holding on the open interval holds a.e. on `Iθ`. -/
private lemma ae_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ

/-- If `f` is integrable on the three pieces `(0,π/8]`, `[π/8,3π/8]`, `(3π/8,π/2)`, then it is
integrable on `Iθ`. -/
private lemma integrableOn_Iθ_of_regions {f : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn f (Set.Ioc 0 (Real.pi / 8)))
    (h2 : MeasureTheory.IntegrableOn f (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)))
    (h3 : MeasureTheory.IntegrableOn f (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
  have hs1 : MeasureTheory.IntegrableOn f (Set.Icc 0 (Real.pi / 8)) :=
    IntegrableOn.congr_set_ae h1
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 8)).symm
  have hs3 : MeasureTheory.IntegrableOn f (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) :=
    IntegrableOn.congr_set_ae h3
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := 3 * Real.pi / 8)
        (b := Real.pi / 2)).symm
  have hset : Set.Icc (0 : ℝ) (Real.pi / 8) ∪ Set.Icc (Real.pi / 8) (3 * Real.pi / 8)
      ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2) = Work.Spaces.Iθ := by
    ext x
    simp only [Work.Spaces.Iθ, Set.mem_union, Set.mem_Icc]
    constructor
    · rintro ((⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩)
      · exact ⟨ha, by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], hb⟩
    · rintro ⟨ha, hb⟩
      rcases le_total x (Real.pi / 8) with hle | hle
      · exact Or.inl (Or.inl ⟨ha, hle⟩)
      rcases le_total x (3 * Real.pi / 8) with hle' | hle'
      · exact Or.inl (Or.inr ⟨hle, hle'⟩)
      · exact Or.inr ⟨hle', hb⟩
  rw [← hset]
  exact (hs1.union h2).union hs3

/-- Reflection transfers integrability from the near region to the far region. -/
private lemma integrableOn_far_iff_near (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 8))
      ↔ MeasureTheory.IntegrableOn F (Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)) := by
  have hset : (fun θ : ℝ => Real.pi / 2 - θ) ⁻¹' Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)
      = Set.Ioo 0 (Real.pi / 8) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have h := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (Work.FTS.H2.DivQ.far_measurePreserving_reflθ)
    (Work.FTS.H2.DivQ.far_measurableEmbedding_reflθ) (f := F)
    (s := Set.Ioo (3 * Real.pi / 8) (Real.pi / 2))
  rwa [hset] at h

/-! ## The whole-interval bound and honesty for a level-`i` mixed slot -/

/-- **The full-interval bound and integrability for the level-`i` angular slot of
`h / sin(2θ)`.**  Combining `nearRegionLHS_i` (near region), `middleRegionLHS_i` (middle) and
`farRegionLHS` (far region, by reflection) gives, on the whole of `Iθ`, the weighted bound
`∫_{Iθ}(D_θ^i(h/sin2θ))² sin(2θ)^{-γ} ≤ C (Denη + Σ_{1≤m≤i} Denγ m)` in terms of the honest data
`Denη = ∫(∂_θh)²sin(2θ)^{-η}`, `Denγ m = ∫(D_θ^m(∂_θh))²sin(2θ)^{-γ}`, and the near-region
integrability `nearRegionIntegrable` (together with its reflection and compactness in the middle)
gives the integrability of the integrand on `Iθ`. -/
theorem mixedSlotBoundIθ :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 →
        (∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  obtain ⟨Cn, hCnpos, hN⟩ := Work.FTS.H2.DivQ.nearRegionLHS_i
  obtain ⟨Cm, hCmpos, hM⟩ := Work.FTS.H2.DivQ.middleRegionLHS_i
  obtain ⟨Cf, hCfpos, hF⟩ := Work.FTS.H2.DivQ.farRegionLHS
  refine ⟨Cn + Cm + Cf, by positivity, ?_⟩
  intro α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  set F : ℝ → ℝ := fun θ =>
    (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hFdef
  set SS : ℝ := (∫ θ in Work.Spaces.Iθ,
        (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) with hSS
  have hSSnn : 0 ≤ SS := by
    rw [hSS]
    refine add_nonneg ?_ (Finset.sum_nonneg fun m _ => ?_)
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
    · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  -- the three region bounds
  have hNb : (∫ θ in (0 : ℝ)..(Real.pi / 8), F θ) ≤ Cn * SS := by
    rw [hFdef, hSS]
    exact hN α h hα hα1 hsm ht0 hDenη i hi hDenγ
  have hMb : (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), F θ) ≤ Cm * SS := by
    rw [hFdef, hSS]
    exact hM α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  have hFb : (∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), F θ) ≤ Cf * SS := by
    rw [hFdef, hSS]
    exact hF α h hα hα1 hsm ht0 ht1 hDenη i hi hDenγ
  -- the three integrability statements
  have hIntNear : MeasureTheory.IntegrableOn F (Set.Ioc 0 (Real.pi / 8)) := by
    rw [hFdef]
    exact Work.FTS.H2.DivQ.nearRegionIntegrable α h hα hα1 hsm ht0 hDenη i hi hDenγ
  have hIntMid : MeasureTheory.IntegrableOn F (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
    rw [hFdef]
    have hcont : ContinuousOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :=
      (((Work.FTS.H2.DivQ.continuousOn_Dth1Iter_div hsm i).pow 2).mul
        (Work.FTS.H2.DivQ.continuousOn_rpow_neg_sin_two (Work.Spaces.gam α)))
    exact hcont.integrableOn_compact isCompact_Icc
  have hIntFarIoo : MeasureTheory.IntegrableOn F (Set.Ioo (3 * Real.pi / 8) (Real.pi / 2)) := by
    have hgsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => h (Real.pi / 2 - θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.pi / 2 - θ)
          (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const.sub contDiffOn_id
      refine (hsm.comp h2 ?_)
      intro θ hθ
      exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hg0 : Filter.Tendsto (fun θ : ℝ => h (Real.pi / 2 - θ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0) (𝓝 (Real.pi / 2)) := by
            have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 0)
                (𝓝 (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
            simpa using h3
          exact h2.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with θ hθ
          simp only [Set.mem_Ioi] at hθ
          exact sub_lt_self _ hθ
      simpa [Function.comp_def] using ht1.comp h1
    have hgDenη : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      Work.FTS.H2.DivQ.far_data_eta_integrable hsm hDenη
    have hgDenγ : ∀ m : ℕ, m ∈ Finset.Icc 1 i → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv (fun θ' : ℝ => h (Real.pi / 2 - θ'))) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      fun m hm => Work.FTS.H2.DivQ.far_data_gam_integrable m α hsm (hDenγ m hm)
    have hgNear : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i
            (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioc 0 (Real.pi / 8)) :=
      Work.FTS.H2.DivQ.nearRegionIntegrable α (fun θ : ℝ => h (Real.pi / 2 - θ))
        hα hα1 hgsm hg0 hgDenη i hi hgDenγ
    have hgNearIoo : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter i
            (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo 0 (Real.pi / 8)) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp hgNear
    -- transfer to the far region
    have hrefl : MeasureTheory.IntegrableOn (fun θ : ℝ => F (Real.pi / 2 - θ))
        (Set.Ioo 0 (Real.pi / 8)) := by
      refine hgNearIoo.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hθ2 : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      show (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = F (Real.pi / 2 - θ)
      rw [hFdef]
      change (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h (Real.pi / 2 - θ') / Real.sin (2 * θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Elliptic.Dth1Iter i (fun θ' : ℝ => h θ' / Real.sin (2 * θ')) (Real.pi / 2 - θ)) ^ 2
          * (Real.sin (2 * (Real.pi / 2 - θ))) ^ (-(Work.Spaces.gam α))
      rw [Work.FTS.H2.DivQ.sin_two_reflSlice θ,
        ← Work.FTS.H2.DivQ.far_sq_Dth1Iter_divSin_reflSlice_eq i hsm θ hθ2]
    exact (integrableOn_far_iff_near F).mp hrefl
  have hIntFar : MeasureTheory.IntegrableOn F (Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hIntFarIoo
  have hIntAll : MeasureTheory.IntegrableOn F Work.Spaces.Iθ :=
    integrableOn_Iθ_of_regions hIntNear hIntMid hIntFar
  -- integrability on the middle+far half
  have hIntMidFar : MeasureTheory.IntegrableOn F (Set.Ioc (Real.pi / 8) (Real.pi / 2)) := by
    have hunion : MeasureTheory.IntegrableOn F
        (Set.Ioc (Real.pi / 8) (3 * Real.pi / 8) ∪ Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)) :=
      (hIntMid.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)).union hIntFar
    rwa [show Set.Ioc (Real.pi / 8) (3 * Real.pi / 8) ∪ Set.Ioc (3 * Real.pi / 8) (Real.pi / 2)
        = Set.Ioc (Real.pi / 8) (Real.pi / 2) from by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 (by linarith [Real.pi_pos])⟩
        · exact ⟨by linarith [Real.pi_pos], h2⟩
      · rintro ⟨h1, h2⟩
        rcases lt_or_ge (3 * Real.pi / 8) x with hlt | hge
        · exact Or.inr ⟨hlt, h2⟩
        · exact Or.inl ⟨h1, hge⟩] at hunion
  -- split the integral
  have hiN : IntervalIntegrable F volume (0 : ℝ) (Real.pi / 8) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)]
    exact hIntNear
  have hiMF : IntervalIntegrable F volume (Real.pi / 8) (Real.pi / 2) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 8 ≤ Real.pi / 2)]
    exact hIntMidFar
  have hiM : IntervalIntegrable F volume (Real.pi / 8) (3 * Real.pi / 8) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : Real.pi / 8 ≤ 3 * Real.pi / 8)]
    exact hIntMid.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hiF : IntervalIntegrable F volume (3 * Real.pi / 8) (Real.pi / 2) := by
    rw [intervalIntegrable_iff,
      Set.uIoc_of_le (by linarith [Real.pi_pos] : 3 * Real.pi / 8 ≤ Real.pi / 2)]
    exact hIntFar
  have hsplit1 : (∫ θ in Work.Spaces.Iθ, F θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have hsplit2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), F θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 8), F θ) + ∫ θ in (Real.pi / 8)..(Real.pi / 2), F θ :=
    (intervalIntegral.integral_add_adjacent_intervals hiN hiMF).symm
  have hsplit3 : (∫ θ in (Real.pi / 8)..(Real.pi / 2), F θ)
      = (∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), F θ)
        + ∫ θ in (3 * Real.pi / 8)..(Real.pi / 2), F θ :=
    (intervalIntegral.integral_add_adjacent_intervals hiM hiF).symm
  refine ⟨hIntAll, ?_⟩
  rw [hsplit1, hsplit2, hsplit3]
  have harith : (Cn + Cm + Cf) * SS = Cn * SS + Cm * SS + Cf * SS := by ring
  linarith [hNb, hMb, hFb, harith]

end Work.FTS.H2.DivSinQR
