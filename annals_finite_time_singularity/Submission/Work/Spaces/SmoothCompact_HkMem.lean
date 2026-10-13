/-
Copyright: work module for the Elgindi finite-time singularity project.

Measurability and integrability of the `ℋ^k`-integrand, and the proof that a smooth
compactly supported function belongs to `ℋ^k`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.BoxBounds
import Submission.Work.Spaces.SinMinBounds
import Submission.Work.Spaces.SupportZ
import Submission.Work.Spaces.SmoothCompact_Aux

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

theorem null_pair : (volume : Measure ℝ) ({0, π / 2} : Set ℝ) = 0 :=
  Set.Finite.measure_zero (Set.toFinite _) volume

theorem null_pair' {R : ℝ} : (volume : Measure ℝ) ({0, R} : Set ℝ) = 0 :=
  Set.Finite.measure_zero (Set.toFinite _) volume

theorem Iθ_ae_eq_Ioo : Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : Iθ \ Set.Ioo 0 (π / 2) ⊆ ({0, π / 2} : Set ℝ) := by
      intro x hx
      rw [Set.mem_diff, Iθ, Set.mem_Icc, Set.mem_Ioo] at hx
      obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
      have hcase : x = 0 ∨ x = π / 2 := by
        by_cases h : 0 < x
        · by_cases h' : x < π / 2
          · exact absurd ⟨h, h'⟩ hx3
          · exact Or.inr (le_antisymm hx2 (not_lt.mp h'))
        · exact Or.inl (le_antisymm (not_lt.mp h) hx1)
      rcases hcase with h | h
      · rw [Set.mem_insert_iff]; exact Or.inl h
      · rw [Set.mem_insert_iff]; exact Or.inr (Set.mem_singleton_iff.mpr h)
    exact measure_mono_null hsub null_pair
  · have hsub : Set.Ioo 0 (π / 2) \ Iθ ⊆ (∅ : Set ℝ) := by
      intro x hx
      rw [Set.mem_diff, Set.mem_Ioo, Iθ, Set.mem_Icc] at hx
      exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
    exact measure_mono_null hsub (by simp)

theorem box_ae_eq (R : ℝ) :
    (Set.Icc 0 R ×ˢ Iθ) =ᵐ[((volume : Measure ℝ).prod volume)]
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : (Set.Icc 0 R ×ˢ Iθ) \ (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
        ⊆ (({0, R} : Set ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ ({0, π / 2} : Set ℝ)) := by
      intro p hp
      rw [Set.mem_diff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Set.mem_prod] at hp1
      rw [Set.mem_prod] at hp2
      rw [Iθ, Set.mem_Icc] at hp1
      rw [Set.mem_Ioo, Set.mem_Ioo] at hp2
      obtain ⟨hp1a, hp1b⟩ := hp1
      have hcase : p.1 = 0 ∨ p.1 = R ∨ p.2 = 0 ∨ p.2 = π / 2 := by
        by_contra h
        push_neg at h
        exact hp2 ⟨⟨lt_of_le_of_ne hp1a.1 (Ne.symm h.1), lt_of_le_of_ne hp1a.2 h.2.1⟩,
          ⟨lt_of_le_of_ne hp1b.1 (Ne.symm h.2.2.1), lt_of_le_of_ne hp1b.2 h.2.2.2⟩⟩
      rw [Set.mem_union]
      rcases hcase with h | h | h | h
      · exact Or.inl (Set.mem_prod.mpr ⟨Set.mem_insert_iff.mpr (Or.inl h), Set.mem_univ _⟩)
      · exact Or.inl (Set.mem_prod.mpr
          ⟨Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)), Set.mem_univ _⟩)
      · exact Or.inr (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_insert_iff.mpr (Or.inl h)⟩)
      · exact Or.inr (Set.mem_prod.mpr
          ⟨Set.mem_univ _, Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))⟩)
    refine measure_mono_null hsub ?_
    refine measure_union_null_iff.mpr ⟨?_, ?_⟩
    · rw [Measure.prod_prod]; rw [null_pair', zero_mul]
    · rw [Measure.prod_prod]; rw [null_pair, mul_zero]
  · have hsub : (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) \ (Set.Icc 0 R ×ˢ Iθ) ⊆ (∅ : Set (ℝ × ℝ)) := by
      intro p hp
      rw [Set.mem_diff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Set.mem_prod] at hp1
      rw [Set.mem_prod] at hp2
      rw [Set.mem_Ioo, Set.mem_Ioo] at hp1
      rw [Iθ, Set.mem_Icc] at hp2
      exact absurd ⟨⟨le_of_lt hp1.1.1, le_of_lt hp1.1.2⟩,
        ⟨le_of_lt hp1.2.1, le_of_lt hp1.2.2⟩⟩ hp2
    exact measure_mono_null hsub (by simp)

/-- Continuity of the uncurried integrand on the open box. -/
theorem continuousOn_uncurry_HkIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R : ℝ)
    (hsm : SmoothNbhd f) :
    ContinuousOn (Function.uncurry (HkIntegrand α k f)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : Function.uncurry (HkIntegrand α k f)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (DzIter i f p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0 := by
    funext p
    rfl
  rw [hfun]
  set box := Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2) with hbox
  have hsinpos : ∀ p ∈ box, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2])
  have hcont : ∀ G : ℝ → ℝ → ℝ, ContDiffOn ℝ ⊤ (Function.uncurry G) U →
      ContinuousOn (Function.uncurry G) box := fun G hG =>
    hG.continuousOn.mono fun p hp =>
      mem_U (by linarith [hp.1.1]) (by linarith [hp.2.1]) (by linarith [hp.2.2])
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) box := by
    rw [show (fun p : ℝ × ℝ => w p.1) = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) fun p hp => pow_ne_zero 2 (ne_of_gt hp.1.1)
  have hsinC : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) box := by
    fun_prop
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (eta / 2)) box :=
    ContinuousOn.rpow_const hsinC fun p hp => Or.inl (ne_of_gt (hsinpos p hp))
  have hsin' : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(gam α / 2))) box :=
    ContinuousOn.rpow_const hsinC fun p hp => Or.inl (ne_of_gt (hsinpos p hp))
  have hzterm : ∀ i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      (DzIter i f p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2) box := by
    intro i
    refine (((hcont _ (smoothNbhd_DzIter hsm i)).mul ?_).pow 2)
    exact hw.div hsin fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _)
  have hmterm : ∀ j i : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2) box := by
    intro j i
    refine (((hcont _ (smoothNbhd_mixed hsm j i)).mul ?_).pow 2)
    rw [show (fun p : ℝ × ℝ => Wt α p.1 p.2)
      = fun p => w p.1 * (Real.sin (2 * p.2)) ^ (-(gam α / 2)) from rfl]
    exact hw.mul hsin'
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_finsetSum _ fun i _ => hzterm i
  · refine continuousOn_finsetSum _ fun i _ => ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hiff : (fun p : ℝ × ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0)
          = fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 := by
        funext p
        exact if_pos hc
      rw [hiff]
      exact hmterm j i
    · have hiff : (fun p : ℝ × ℝ =>
          if 1 ≤ i ∧ i + j ≤ k then (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0)
          = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext p
        exact if_neg hc
      rw [hiff]
      exact continuousOn_const

/-- Continuity of the `θ`-slice of the integrand for fixed `z`. -/
theorem continuousOn_HkIntegrand_slice (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R z : ℝ)
    (hsm : SmoothNbhd f) (hz : z ∈ Set.Ioo 0 R) :
    ContinuousOn (fun θ => HkIntegrand α k f z θ) (Set.Ioo 0 (π / 2)) := by
  have h1 : ContinuousOn (Function.uncurry (HkIntegrand α k f))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_uncurry_HkIntegrand α k f R hsm
  have h2 : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) :=
    continuousOn_const.prodMk continuousOn_id
  have h3 := h1.comp h2 (fun θ hθ => ⟨hz, hθ⟩)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h3

/-- Membership of a smooth compactly supported function in `ℋ^k`. -/
theorem HkMemSmoothCompact (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hsm : SmoothNbhd f) (hf_gt : ∀ z θ : ℝ, R < z → f z θ = 0)
    (hvan : VanishTheta f) (hz0 : ∀ θ ∈ Iθ, f 0 θ = 0 ∧ pz f 0 θ = 0) :
    HkMem α k f := by
  obtain ⟨M, hMnn, hM⟩ := HkIntegrand_bound α hα hα1 k f R hR hsm hf_gt hvan hz0
  have hzero_gt : ∀ z θ, R < z → HkIntegrand α k f z θ = 0 :=
    fun z θ hz => HkIntegrand_eq_zero_of_gt α k f R z θ hf_gt hz
  have hinner : ∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α k f z θ) Iθ := by
    intro z hz
    have hz0le : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz0le with hz0' | hzpos
    · rw [← hz0']
      exact IntegrableOn.congr_fun integrableOn_zero
        (fun θ _ => (HkIntegrand_apply_zero α k f θ).symm) measurableSet_Icc
    · by_cases hzR : z ≤ R
      · refine IntegrableOn.of_bound volume_Iθ_lt_top ?_ M ?_
        · rw [Measure.restrict_congr_set Iθ_ae_eq_Ioo]
          exact (continuousOn_HkIntegrand_slice α k f (R + 1) z hsm ⟨hzpos, by linarith⟩).aestronglyMeasurable
            measurableSet_Ioo
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [HkIntegrand_nonneg α k f z θ, hMnn],
            hM z hz θ hθ⟩
      · rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
          funext fun θ => hzero_gt z θ (not_le.mp hzR)]
        exact integrableOn_zero
  refine ⟨hinner, ?_⟩
  have hbound : ∀ z ∈ Set.Icc 0 R, ‖∫ θ in Iθ, HkIntegrand α k f z θ‖ ≤ M * (π / 2) := by
    intro z hz
    rw [← volume_real_Iθ]
    refine norm_setIntegral_le_of_norm_le_const volume_Iθ_lt_top fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [HkIntegrand_nonneg α k f z θ, hMnn], hM z hz.1 θ hθ⟩
  have hIcc : IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) (Set.Icc 0 R) := by
    refine IntegrableOn.of_bound ?_ ?_ (M * (π / 2)) ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · have hjoint : AEStronglyMeasurable (Function.uncurry (HkIntegrand α k f))
          ((volume.restrict (Set.Icc 0 R)).prod (volume.restrict Iθ)) := by
        have hμ : (volume.restrict (Set.Icc 0 R)).prod (volume.restrict Iθ)
            = (volume.prod volume).restrict (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
          rw [Measure.prod_restrict, Measure.restrict_congr_set (box_ae_eq R)]
        rw [hμ]
        exact (continuousOn_uncurry_HkIntegrand α k f R hsm).aestronglyMeasurable
          (measurableSet_Ioo.prod measurableSet_Ioo)
      exact hjoint.integral_prod_right'
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
      exact hbound z hz
  have hIoi : IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) (Set.Ioi R) := by
    refine IntegrableOn.congr_fun integrableOn_zero (fun z hz => ?_) measurableSet_Ioi
    show (0 : ℝ) = ∫ θ in Iθ, HkIntegrand α k f z θ
    rw [show (fun θ => HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from
      funext fun θ => hzero_gt z θ hz]
    simp
  refine IntegrableOn.mono_set (IntegrableOn.union hIcc hIoi) ?_
  intro z hz
  by_cases h : z ≤ R
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr (not_le.mp h)

end Work.Spaces
