/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/Measurable.lean`

The a.e. measurability of the shifted `EpsSq`-integrand with respect to `μq ⊗ volume`, needed for
Tonelli's theorem in the final assembly.  This is the only place where the a.e. measurability
contained in `EpsMem` is used.
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The shift map with a fixed parameter is measurable. -/
theorem measurable_shift_slice_map (p : ℝ × ℝ) :
    Measurable fun q : ℝ × ℝ => (zShift q.1 p.1, thShift q.2 p.2) := by
  have htan : Measurable fun θ : ℝ => Real.tan θ := by
    convert (Real.measurable_sin.div Real.measurable_cos :
      Measurable fun θ : ℝ => Real.sin θ / Real.cos θ) using 1
    funext θ
    exact Real.tan_eq_sin_div_cos θ
  refine Measurable.prodMk ?_ ?_
  · show Measurable fun q : ℝ × ℝ => q.1 * Real.exp (-p.1)
    exact measurable_fst.mul (measurable_const : Measurable fun _ : ℝ × ℝ => Real.exp (-p.1))
  · show Measurable fun q : ℝ × ℝ => Real.arctan (Real.tan q.2 * Real.exp (-p.2))
    exact Real.measurable_arctan.comp
      ((htan.comp measurable_snd).mul
        (measurable_const : Measurable fun _ : ℝ × ℝ => Real.exp (-p.2)))

/-- The shift map with a fixed *base point* is measurable (the argument is the shift). -/
theorem measurable_shift_arg_map (z θ : ℝ) :
    Measurable fun p : ℝ × ℝ => (zShift z p.1, thShift θ p.2) := by
  have htan : Measurable fun ζ : ℝ => Real.tan ζ := by
    convert (Real.measurable_sin.div Real.measurable_cos :
      Measurable fun ζ : ℝ => Real.sin ζ / Real.cos ζ) using 1
    funext ζ
    exact Real.tan_eq_sin_div_cos ζ
  refine Measurable.prodMk ?_ ?_
  · show Measurable fun p : ℝ × ℝ => z * Real.exp (-p.1)
    exact (measurable_const : Measurable fun _ : ℝ × ℝ => z).mul
      (Real.measurable_exp.comp measurable_fst.neg)
  · show Measurable fun p : ℝ × ℝ => Real.arctan (Real.tan θ * Real.exp (-p.2))
    exact Real.measurable_arctan.comp
      ((measurable_const : Measurable fun _ : ℝ × ℝ => Real.tan θ).mul
        (Real.measurable_exp.comp measurable_snd.neg))

/-- The shift map of a base point and a parameter is measurable. -/
theorem measurable_shift_pair_map :
    Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) := by
  have htan : Measurable fun θ : ℝ => Real.tan θ := by
    convert (Real.measurable_sin.div Real.measurable_cos :
      Measurable fun θ : ℝ => Real.sin θ / Real.cos θ) using 1
    funext θ
    exact Real.tan_eq_sin_div_cos θ
  refine Measurable.prodMk ?_ ?_
  · show Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 * Real.exp (-z.2.1)
    exact (measurable_fst.comp measurable_fst).mul
      (Real.measurable_exp.comp (measurable_fst.comp measurable_snd).neg)
  · show Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.arctan (Real.tan z.1.2 * Real.exp (-z.2.2))
    exact Real.measurable_arctan.comp
      (((htan.comp (measurable_snd.comp measurable_fst)).mul
        (Real.measurable_exp.comp (measurable_snd.comp measurable_snd).neg)))

/-- `logJac` is measurable. -/
theorem measurable_logJac : Measurable fun u : ℝ × ℝ => HkSqAux.logJac u.1 u.2 := by
  have hk : Measurable fun ζ : ℝ => HkSqAux.kappa ζ := by
    simp only [HkSqAux.kappa]
    exact Real.measurable_exp.div
      (measurable_const.add (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  simp only [HkSqAux.logJac]
  exact (Real.measurable_exp.comp measurable_fst).mul (hk.comp measurable_snd)

/-- The log-coordinate pull-back of a set of the plane. -/
def logPre (B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {u : ℝ × ℝ | (Real.exp u.1, Real.arctan (Real.exp u.2)) ∈ B}

theorem measurableSet_logPre {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    MeasurableSet (logPre B) :=
  hB.preimage (Measurable.prodMk (Real.measurable_exp.comp measurable_fst)
    (Real.measurable_arctan.comp (Real.measurable_exp.comp measurable_snd)))

/-- **The log-coordinate pull-back of a Lebesgue-null set is Lebesgue-null.** -/
theorem volume_logPreimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) :
    (MeasureTheory.volume : Measure (ℝ × ℝ)) (logPre B) = 0 := by
  classical
  have hBlog_meas : MeasurableSet (logPre B) := measurableSet_logPre hB
  have hmeasB : Measurable fun q : ℝ × ℝ => B.indicator 1 q :=
    (measurable_const : Measurable fun _ : ℝ × ℝ => (1 : ENNReal)).indicator hB
  have hmeasLog : Measurable fun q : ℝ × ℝ => (logPre B).indicator 1 q :=
    (measurable_const : Measurable fun _ : ℝ × ℝ => (1 : ENNReal)).indicator hBlog_meas
  -- (a) the `logJac`-weighted integral of `1_{logPre B}` vanishes
  have hJac : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
      * (logPre B).indicator 1 (s, ζ)) = 0 := by
    have hid : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
          * (B.indicator 1) (Real.exp s, Real.arctan (Real.exp ζ)))
        = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ)
            * (logPre B).indicator 1 (s, ζ) := by
      refine lintegral_congr (fun s => lintegral_congr (fun ζ => ?_))
      congr 1
    rw [← hid, ← Work.FTS.StrongEps.EpsSrc.lintegral_logSubst (fun z θ => B.indicator 1 (z, θ))]
    have h2 : ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) B = 0 := by
      rw [MeasureTheory.Measure.restrict_apply hB]
      exact le_antisymm (MeasureTheory.measure_mono Set.inter_subset_left |>.trans_eq hB0) zero_le
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, B.indicator 1 (z, θ)) = 0 := by
      have h := MeasureTheory.setLIntegral_prod (μ := MeasureTheory.volume)
        (ν := MeasureTheory.volume) (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ)
        (f := fun q : ℝ × ℝ => B.indicator 1 q) hmeasB.aemeasurable
      rw [← h, MeasureTheory.lintegral_indicator_one hB]
      exact h2
    rw [hL]
  -- (b) hence `1_{logPre B}` vanishes a.e.
  have hprod0 : (∫⁻ u : ℝ × ℝ, ENNReal.ofReal (HkSqAux.logJac u.1 u.2)
      * (logPre B).indicator 1 u) = 0 :=
    le_antisymm (MeasureTheory.lintegral_prod_le (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)
      (fun u : ℝ × ℝ => ENNReal.ofReal (HkSqAux.logJac u.1 u.2)
        * (logPre B).indicator 1 u) |>.trans_eq hJac) zero_le
  have hmeas_int : Measurable fun u : ℝ × ℝ =>
      ENNReal.ofReal (HkSqAux.logJac u.1 u.2) * (logPre B).indicator 1 u :=
    (ENNReal.measurable_ofReal.comp measurable_logJac).mul hmeasLog
  have hone0 : (logPre B).indicator 1 =ᵐ[(MeasureTheory.volume : Measure (ℝ × ℝ))] (0 : ℝ × ℝ → ENNReal) := by
    have hf := (MeasureTheory.lintegral_eq_zero_iff hmeas_int).mp hprod0
    filter_upwards [hf] with u hu
    simp only [Pi.zero_apply] at hu ⊢
    rcases mul_eq_zero.mp hu with h | h
    · exact absurd h (ne_of_gt (ENNReal.ofReal_pos.mpr (HkSqAux.logJac_pos u.1 u.2)))
    · exact h
  -- (c) conclude
  have hz : (∫⁻ u : ℝ × ℝ, (logPre B).indicator 1 u) = 0 := by
    rw [MeasureTheory.lintegral_congr_ae hone0]
    simp
  rwa [MeasureTheory.lintegral_indicator_one hBlog_meas] at hz

/-- **Translation invariance of the Lebesgue measure under `p ↦ (s - p₁, ζ - p₂)`.** -/
theorem volume_preimage_sub_eq (s ζ : ℝ) {Blog : Set (ℝ × ℝ)} (hBlog : MeasurableSet Blog) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
      {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ Blog} = MeasureTheory.volume Blog := by
  set A : Set (ℝ × ℝ) := (fun q : ℝ × ℝ => ((s, ζ) : ℝ × ℝ) + q) ⁻¹' Blog with hA
  have hAmeas : MeasurableSet A := hBlog.preimage (measurable_const.add measurable_id)
  have hset : {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ Blog} = Neg.neg ⁻¹' A := by
    ext p
    have hp : ((s, ζ) : ℝ × ℝ) + (-p) = (s - p.1, ζ - p.2) := by
      refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg]
    simp only [hA, Set.mem_setOf_eq, Set.mem_preimage]
    rw [hp]
  have hneg : (MeasureTheory.volume : Measure (ℝ × ℝ)) (Neg.neg ⁻¹' A) = MeasureTheory.volume A := by
    have h1 : (∫⁻ p : ℝ × ℝ, (Neg.neg ⁻¹' A).indicator 1 p)
        = ∫⁻ p : ℝ × ℝ, A.indicator 1 p := by
      rw [← MeasureTheory.lintegral_neg_eq_self (fun p : ℝ × ℝ => A.indicator 1 p)]
      exact MeasureTheory.lintegral_congr (fun p => rfl)
    rw [← MeasureTheory.lintegral_indicator_one (hAmeas.preimage measurable_neg), h1,
      MeasureTheory.lintegral_indicator_one hAmeas]
  rw [hset, hneg]
  exact MeasureTheory.measure_preimage_add MeasureTheory.volume (s, ζ) Blog

/-- **One slice of the pull-back of a null set is null.** -/
theorem volume_shift_preimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (MeasureTheory.volume : Measure (ℝ × ℝ))
      {p : ℝ × ℝ | (zShift z p.1, thShift θ p.2) ∈ B} = 0 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℝ, Real.exp s = z := ⟨Real.log z, Real.exp_log hz⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, Real.arctan (Real.exp ζ) = θ := by
    refine ⟨Real.log (Real.tan θ), ?_⟩
    rw [Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2)]
    exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2
  have hset : {p : ℝ × ℝ | (zShift z p.1, thShift θ p.2) ∈ B}
      = {p : ℝ × ℝ | (s - p.1, ζ - p.2) ∈ logPre B} := by
    ext p
    simp only [logPre, Set.mem_setOf_eq]
    rw [← hs, ← hζ, zShift_exp', thShift_arctan_exp']
  rw [hset, volume_preimage_sub_eq s ζ (measurableSet_logPre hB)]
  exact volume_logPreimage_null hB hB0

/-- `Quad` is conull for the measure `μq = volume∣_{Iz ×ˢ Iθ}`. -/
theorem ae_mem_quad :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), q ∈ Quad := by
  rw [MeasureTheory.ae_iff]
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioi.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
      Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton 0) (MeasureTheory.measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h' | h'
      · exact absurd ⟨h, h'⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h')
    · exact Or.inl (le_antisymm h hxI.1)
  have hsub : {a : ℝ × ℝ | a ∉ Quad} ⊆
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
        ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) := by
    intro q hq
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and, Set.mem_setOf_eq] at hq ⊢
    tauto
  refine MeasureTheory.measure_mono_null hsub (MeasureTheory.measure_union_null ?_ ?_)
  · rw [MeasureTheory.Measure.prod_prod, h1, zero_mul]
  · rw [MeasureTheory.Measure.prod_prod, h2, mul_zero]

/-- **The pull-back of a null set under the shift map is null** (for the product measure). -/
theorem measure_shift_pair_preimage_null {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hB0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) B = 0) :
    (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume)
      {z : (ℝ × ℝ) × (ℝ × ℝ) | (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ B} = 0 := by
  classical
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    {z | (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ B} with hS
  have hSmeas : MeasurableSet S := hB.preimage measurable_shift_pair_map
  have hSind : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => S.indicator 1 z :=
    (measurable_const : Measurable fun _ : (ℝ × ℝ) × (ℝ × ℝ) => (1 : ENNReal)).indicator hSmeas
  rw [← MeasureTheory.lintegral_indicator_one hSmeas]
  rw [show (∫⁻ z : (ℝ × ℝ) × (ℝ × ℝ), S.indicator 1 z
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume)
        = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, S.indicator 1 (q, p) ∂MeasureTheory.volume
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
        MeasureTheory.lintegral_prod
          (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (ν := MeasureTheory.volume) _ hSind.aemeasurable]
  have hcongr : (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ, S.indicator 1 (q, p))
      = fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
          ({p' : ℝ × ℝ | (zShift q.1 p'.1, thShift q.2 p'.2) ∈ B}).indicator 1 p := by
    funext q
    refine MeasureTheory.lintegral_congr (fun p => ?_)
    simp only [hS, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [hcongr]
  have hzero : ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (∫⁻ p : ℝ × ℝ,
        ({p' : ℝ × ℝ | (zShift q.1 p'.1, thShift q.2 p'.2) ∈ B}).indicator 1 p) = 0 := by
    filter_upwards [ae_mem_quad] with q hq
    have hmeasq : MeasurableSet {p : ℝ × ℝ | (zShift q.1 p.1, thShift q.2 p.2) ∈ B} :=
      hB.preimage (measurable_shift_arg_map q.1 q.2)
    rw [MeasureTheory.lintegral_indicator_one hmeasq]
    exact volume_shift_preimage_null hB hB0 hq.1 hq.2
  rw [MeasureTheory.lintegral_congr_ae hzero, MeasureTheory.lintegral_zero]

/-- `Quad` is conull for the measure `μq = volume∣_{Iz ×ˢ Iθ}` (the null set is computed
directly). -/
theorem measure_quad_compl :
    (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))) Quadᶜ = 0 := by
  have h1 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioi.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
      Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton 0) (MeasureTheory.measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
      Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h' | h'
      · exact absurd ⟨h, h'⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h')
    · exact Or.inl (le_antisymm h hxI.1)
  have hsub : Quadᶜ ⊆ ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ)) ∪
      ((Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) := by
    intro q hq
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hq ⊢
    tauto
  refine MeasureTheory.measure_mono_null hsub (MeasureTheory.measure_union_null ?_ ?_)
  · rw [MeasureTheory.Measure.prod_prod, h1, zero_mul]
  · rw [MeasureTheory.Measure.prod_prod, h2, mul_zero]

/-- **The shifted integrand is a.e. measurable.** -/
theorem aemeasurable_shift_comp {Γ : ℝ × ℝ → ENNReal}
    (hΓ : AEMeasurable Γ (MeasureTheory.volume : Measure (ℝ × ℝ))) :
    AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        Γ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  obtain ⟨Γ₁, hΓ₁_meas, hΓ₁_eq⟩ := hΓ
  have hN0 : (MeasureTheory.volume : Measure (ℝ × ℝ)) {u : ℝ × ℝ | Γ u ≠ Γ₁ u} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hΓ₁_eq
  obtain ⟨B, hNB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hN0
  refine ⟨fun z => Γ₁ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2), ?_, ?_⟩
  · exact hΓ₁_meas.comp measurable_shift_pair_map
  · show ∀ᵐ z : (ℝ × ℝ) × (ℝ × ℝ) ∂(((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume),
      Γ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) = Γ₁ (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2)
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (measure_shift_pair_preimage_null hBmeas hB0)
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    exact hNB hz

/-- The a.e. measurability of the shifted integrand, with the measurability hypothesis in the
form in which `EpsMem` provides it (with respect to the *restricted* measure). -/
theorem aemeasurable_shift_comp' {F : ℝ × ℝ → ENNReal}
    (hF : AEMeasurable F (MeasureTheory.volume.restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        F (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  classical
  have hquadmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hFa : AEMeasurable ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F) MeasureTheory.volume :=
    (aemeasurable_indicator_iff hquadmeas).mpr hF
  obtain ⟨g, hg, hg1⟩ := aemeasurable_shift_comp hFa
  refine ⟨g, hg, ?_⟩
  have hquad : ∀ᵐ z : (ℝ × ℝ) × (ℝ × ℝ)
      ∂(((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume), z.1 ∈ Quad := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : (ℝ × ℝ) × (ℝ × ℝ) | ¬ z.1 ∈ Quad}
        = Quadᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true]
    rw [hset, MeasureTheory.Measure.prod_prod, measure_quad_compl, zero_mul]
  have hae : (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator F
          (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2))
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume]
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        F (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2)) := by
    filter_upwards [hquad] with z hz
    have hmem : (zShift z.1.1 z.2.1, thShift z.1.2 z.2.2) ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
      ⟨(zShift_pos hz.1).le, ⟨(thShift_mem hz.2).1.le, (thShift_mem hz.2).2.le⟩⟩
    exact Set.indicator_of_mem hmem F
  exact hae.symm.trans hg1


end Work.FTS.StrongEps.EpsSqTools
