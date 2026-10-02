import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.QC.CompHolo.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- **Local injectivity of a holomorphic function at a point with non-zero derivative.**
A complex differentiable function is strictly differentiable, and a strict derivative that is
invertible (non-zero in dimension one) admits a local left inverse, which forces injectivity on
a neighbourhood. -/
theorem exists_injOn_ball_of_deriv_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z : ℂ}
    (hz : deriv F z ≠ 0) : ∃ ε : ℝ, 0 < ε ∧ Set.InjOn F (Metric.ball z ε) := by
  have hstrict : HasStrictDerivAt F (deriv F z) z := (hF.analyticAt z).hasStrictDerivAt
  have hev : ∀ᶠ x in 𝓝 z,
      HasStrictDerivAt.localInverse F (deriv F z) z hstrict hz (F x) = x :=
    hstrict.eventually_left_inverse hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  have hx' : HasStrictDerivAt.localInverse F (deriv F z) z hstrict hz (F x) = x := hsub hx
  have hy' : HasStrictDerivAt.localInverse F (deriv F z) z hstrict hz (F y) = y := hsub hy
  rw [hxy] at hx'
  exact hx'.symm.trans hy'

/-- A finite-union form of the subadditivity of the lower integral, valid for arbitrary (not
necessarily measurable) integrands. -/
private lemma lintegral_biUnion_finset_le {ι : Type*} (t : Finset ι) (W : ι → Set ℂ)
    (f : ℂ → ENNReal) :
    ∫⁻ z in ⋃ i ∈ t, W i, f z ≤ ∑ i ∈ t, ∫⁻ z in W i, f z := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h1 : ∫⁻ z in W a ∪ ⋃ i ∈ s, W i, f z
        ≤ (∫⁻ z in W a, f z) + (∫⁻ z in ⋃ i ∈ s, W i, f z) :=
      MeasureTheory.lintegral_union_le f (W a) (⋃ i ∈ s, W i)
    have h2 : (∫⁻ z in ⋃ i ∈ s, W i, f z) ≤ ∑ i ∈ s, ∫⁻ z in W i, f z := ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact le_trans h1 (add_le_add_right h2 (∫⁻ z in W a, f z))

/-- **Local `L²` change-of-variables bound.**  If `F` is complex differentiable and injective on
a measurable set `s`, and `‖deriv F‖ ≥ m > 0` on `s`, then for every `H : ℂ → ℝ≥0∞`
`∫⁻_{s} H (F z) ≤ (m²)⁻¹ ∫⁻_{F '' s} H`.

The proof is the change-of-variables formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
together with the pointwise identity `|det D F z| = ‖deriv F z‖²` (the Jacobian of a conformal
map), which converts the area integral `∫⁻_{s} |det D F| · H (F z)` into `∫⁻_{F '' s} H`. -/
theorem lintegral_comp_le_of_injOn {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : Set ℂ}
    (hs : MeasurableSet s) (hinj : Set.InjOn F s) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ z ∈ s, m ≤ ‖deriv F z‖) (H : ℂ → ENNReal) :
    ∫⁻ z in s, H (F z) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' s, H w := by
  set K0 : ENNReal := ENNReal.ofReal ((m ^ 2)⁻¹) with hK0
  have hm2pos : 0 < m ^ 2 := pow_pos hm 2
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F (fderiv ℝ F x) s x := fun x _ =>
    (hF.real_of_complex.differentiableAt (x := x)).hasFDerivAt.hasFDerivWithinAt
  have hcov : ∫⁻ w in F '' s, H w
      = ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ F z).det| * H (F z) :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj H
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ s →
      H (F z) ≤ K0 * (ENNReal.ofReal |(fderiv ℝ F z).det| * H (F z)) := by
    refine Eventually.of_forall fun z hz => ?_
    have hdet : |(fderiv ℝ F z).det| = ‖deriv F z‖ ^ 2 :=
      Work.MRMT.QC.abs_det_fderiv_eq (hF.differentiableAt (x := z))
    have hmle : m ≤ ‖deriv F z‖ := hbound z hz
    have hm2 : ENNReal.ofReal (m ^ 2) ≤ ENNReal.ofReal |(fderiv ℝ F z).det| := by
      rw [hdet]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [hm.le])
    have hone : K0 * ENNReal.ofReal (m ^ 2) = 1 := by
      rw [hK0, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (ne_of_gt hm2pos),
        ENNReal.ofReal_one]
    have hkey : 1 ≤ K0 * ENNReal.ofReal |(fderiv ℝ F z).det| := by
      rw [← hone]
      exact mul_le_mul_right hm2 K0
    calc H (F z) = 1 * H (F z) := (one_mul _).symm
      _ ≤ (K0 * ENNReal.ofReal |(fderiv ℝ F z).det|) * H (F z) :=
          mul_le_mul_left hkey (H (F z))
      _ = K0 * (ENNReal.ofReal |(fderiv ℝ F z).det| * H (F z)) := mul_assoc _ _ _
  calc ∫⁻ z in s, H (F z)
      ≤ ∫⁻ z in s, K0 * (ENNReal.ofReal |(fderiv ℝ F z).det| * H (F z)) :=
        MeasureTheory.setLIntegral_mono_ae' hs hpt
    _ = K0 * ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ F z).det| * H (F z) :=
        MeasureTheory.lintegral_const_mul' K0 _ ENNReal.ofReal_ne_top
    _ = K0 * ∫⁻ w in F '' s, H w := by rw [hcov]

theorem comp_l2_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {K : Set ℂ}
    (hK : IsCompact K) (hK' : ∀ z ∈ K, deriv F z ≠ 0) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ u : ℂ → ℂ,
      ∫⁻ z in K, ENNReal.ofReal (‖u (F z)‖ ^ 2)
        ≤ C * ∫⁻ w in F '' K, ENNReal.ofReal (‖u w‖ ^ 2) := by
  classical
  -- Step 1: a uniform positive lower bound for `‖deriv F‖` on the compact set `K`.
  obtain ⟨m, hmpos, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K, m ≤ ‖deriv F z‖ := by
    by_cases hne : K.Nonempty
    · have hcont : ContinuousOn (fun z : ℂ => ‖deriv F z‖) K :=
        (hF.deriv.continuous.norm).continuousOn
      obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hcont
      exact ⟨‖deriv F z₀‖, norm_pos_iff.mpr (hK' z₀ hz₀), fun z hz => hmin hz⟩
    · exact ⟨1, one_pos, fun z hz => (hne ⟨z, hz⟩).elim⟩
  -- Step 2: cover `K` by finitely many open sets on which `F` is injective.
  have hball : ∀ z : K, ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ Set.InjOn F U := fun z =>
    let ⟨ε, hε, hinj⟩ := exists_injOn_ball_of_deriv_ne_zero hF (hK' z z.2)
    ⟨Metric.ball (z : ℂ) ε, Metric.isOpen_ball, Metric.mem_ball_self hε, hinj⟩
  choose U hUo hUz hUi using hball
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun z => hUo z)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hUz ⟨z, hz⟩⟩)
  -- Step 3: the bound on each piece `U i ∩ K`.
  have hpiece : ∀ i ∈ t, ∀ H : ℂ → ENNReal,
      ∫⁻ z in U i ∩ K, H (F z) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' K, H w := by
    intro i _ H
    have hs : MeasurableSet (U i ∩ K) := (hUo i).measurableSet.inter hK.isClosed.measurableSet
    have hinj : Set.InjOn F (U i ∩ K) := (hUi i).mono Set.inter_subset_left
    have hb : ∀ z ∈ U i ∩ K, m ≤ ‖deriv F z‖ := fun z hz => hm z hz.2
    calc ∫⁻ z in U i ∩ K, H (F z)
        ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' (U i ∩ K), H w :=
          lintegral_comp_le_of_injOn hF hs hinj hmpos hb H
      _ ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' K, H w :=
          mul_le_mul_right (MeasureTheory.lintegral_mono_set
            (Set.image_mono Set.inter_subset_right)) _
  refine ⟨(t.card : ENNReal) * ENNReal.ofReal ((m ^ 2)⁻¹), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  · intro u
    let H : ℂ → ENNReal := fun w => ENNReal.ofReal (‖u w‖ ^ 2)
    have hcover : ⋃ i ∈ t, (U i ∩ K) = K := by
      apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨i, _, hzi⟩ := Set.mem_iUnion₂.mp hz
        exact hzi.2
      · intro z hz
        obtain ⟨i, hit, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
        exact Set.mem_iUnion₂.mpr ⟨i, hit, hzi, hz⟩
    have hstep2 : ∫⁻ z in ⋃ i ∈ t, (U i ∩ K), H (F z)
        ≤ ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (F z) :=
      lintegral_biUnion_finset_le t (fun i => U i ∩ K) (fun z => H (F z))
    have hstep3 : ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (F z)
        ≤ ∑ i ∈ t, ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' K, H w :=
      Finset.sum_le_sum fun i hi => hpiece i hi H
    have hstep4 : ∑ i ∈ t, ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' K, H w
        = ((t.card : ENNReal) * ENNReal.ofReal ((m ^ 2)⁻¹)) * ∫⁻ w in F '' K, H w := by
      rw [Finset.sum_const, nsmul_eq_mul, (mul_assoc _ _ _).symm]
    calc ∫⁻ z in K, H (F z)
        = ∫⁻ z in ⋃ i ∈ t, (U i ∩ K), H (F z) := by rw [hcover]
      _ ≤ ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (F z) := hstep2
      _ ≤ ∑ i ∈ t, ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in F '' K, H w := hstep3
      _ = ((t.card : ENNReal) * ENNReal.ofReal ((m ^ 2)⁻¹)) * ∫⁻ w in F '' K, H w := hstep4

end Work.MRMT.Found
