import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

noncomputable section

/-!
## The pull-back (area) inequality for an orientation-reversing `C¹` map

We prove that an orientation-reversing `C¹` map `f : ℂ → ℂ` (in the weak sense
`‖∂f z‖ < ‖∂̄f z‖` off a set `S`) satisfies the change-of-variables inequality

`∫⁻_{z ∈ K} H (f z) ≤ C · ∫⁻_{w ∈ f '' K} H w`

on every compact `K` disjoint from `S`, with a constant `C > 0` depending only on `f` and `K`.

The proof follows the same route as `Work.MRMT.QC.pullbackAreaBound`:

* on `K` the Jacobian `det (fderiv ℝ f z) = ‖∂f z‖² - ‖∂̄f z‖²` is negative
  (`Work.MRMT.Sobolev.det_fderiv_eq`), hence non-zero, and `z ↦ |det (fderiv ℝ f z)|` is
  continuous, so it is bounded below by some `m > 0` on `K`;
* a non-zero derivative makes `f` a local homeomorphism (inverse function theorem for the
  *strict* derivative `hasStrictFDerivAt`, available for `C¹` maps), so `K` is covered by
  finitely many open sets on which `f` is injective;
* on each piece Mathlib's change-of-variables formula
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` together with the lower bound `|det| ≥ m`
  gives `∫⁻ H (f z) ≤ m⁻¹ ∫⁻_{f '' piece} H`;
* a finite sum over the covering pieces bounds the overlap, giving the constant `card · m⁻¹`.
-/

/-- **Local injectivity at a point with invertible real derivative.**  If `f` is `C¹` and
`(fderiv ℝ f z).det ≠ 0`, then `f` is injective on some ball around `z`.  The derivative being
invertible, the inverse function theorem (in the strict form, which holds for `C¹` maps) provides
a local left inverse of `f` near `z`, which forces injectivity. -/
private lemma exists_injOn_ball_of_det_ne_zero {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {z : ℂ}
    (hdet : (fderiv ℝ f z).det ≠ 0) : ∃ δ : ℝ, 0 < δ ∧ Set.InjOn f (Metric.ball z δ) := by
  have hunit_lin : IsUnit ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) := by
    rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hunit : IsUnit (fderiv ℝ f z : ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr hunit_lin
  have hbij : Function.Bijective (fderiv ℝ f z : ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hker : ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbij.1
  have hrange : ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ).range = ⊤ :=
    LinearMap.range_eq_top.mpr hbij.2
  set e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ f z) hker hrange with hedef
  have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hsd := hf.hasStrictFDerivAt (x := z) (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← he] at hsd
  have hev := hsd.eventually_left_inverse
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have hx' := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
  have hy' := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
  rw [← hx', ← hy', hxy]

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

/-- **Single-sheet change-of-variables bound.**  If `f` is injective on a measurable set `s`, is
differentiable there, and `|det (fderiv ℝ f z)| ≥ m > 0` on `s`, then for every `H : ℂ → ℝ≥0∞`

`∫⁻_{z ∈ s} H (f z) ≤ m⁻¹ · ∫⁻_{w ∈ f '' s} H w`.

The proof is Mathlib's change of variables formula together with the pointwise inequality
`H (f z) ≤ m⁻¹ |det (fderiv ℝ f z)| H (f z)`. -/
private lemma lintegral_comp_le_of_injOn_abs_det {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hdiff : ∀ z ∈ s, HasFDerivWithinAt f (fderiv ℝ f z) s z) (hinj : Set.InjOn f s) {m : ℝ}
    (hm : 0 < m) (hbound : ∀ z ∈ s, m ≤ |(fderiv ℝ f z).det|) (H : ℂ → ENNReal) :
    ∫⁻ z in s, H (f z) ≤ ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' s, H w := by
  have hcov : ∫⁻ w in f '' s, H w
      = ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ f z).det| * H (f z) :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hdiff hinj H
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ s →
      H (f z) ≤ ENNReal.ofReal m⁻¹ * (ENNReal.ofReal |(fderiv ℝ f z).det| * H (f z)) := by
    refine Eventually.of_forall fun z hz => ?_
    have hmle : m ≤ |(fderiv ℝ f z).det| := hbound z hz
    have hinv : 0 < m⁻¹ := inv_pos.mpr hm
    have hone : (1 : ℝ) ≤ m⁻¹ * |(fderiv ℝ f z).det| := by
      calc (1 : ℝ) = m⁻¹ * m := (inv_mul_cancel₀ (ne_of_gt hm)).symm
        _ ≤ m⁻¹ * |(fderiv ℝ f z).det| := mul_le_mul_of_nonneg_left hmle hinv.le
    have hkey : (1 : ENNReal)
        ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal |(fderiv ℝ f z).det| := by
      rw [← ENNReal.ofReal_mul hinv.le, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hone
    calc H (f z) = 1 * H (f z) := (one_mul _).symm
      _ ≤ (ENNReal.ofReal m⁻¹ * ENNReal.ofReal |(fderiv ℝ f z).det|) * H (f z) :=
          mul_le_mul_left hkey (H (f z))
      _ = ENNReal.ofReal m⁻¹ * (ENNReal.ofReal |(fderiv ℝ f z).det| * H (f z)) :=
          mul_assoc _ _ _
  calc ∫⁻ z in s, H (f z)
      ≤ ∫⁻ z in s, ENNReal.ofReal m⁻¹ * (ENNReal.ofReal |(fderiv ℝ f z).det| * H (f z)) :=
        MeasureTheory.setLIntegral_mono_ae' hs hpt
    _ = ENNReal.ofReal m⁻¹ * ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ f z).det| * H (f z) :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' s, H w := by rw [hcov]

-- i.e. ∫⁻ z in K, H (f z) ≤ ofReal C * ∫⁻ w in f '' K, H w
theorem lintegral_comp_le_of_isCompact_disjoint {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖)
    {K : Set ℂ} (hK : IsCompact K) (hKS : Disjoint K S) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℂ → ENNReal,
      MeasureTheory.lintegral (MeasureTheory.Measure.restrict MeasureTheory.volume K) (fun z => H (f z))
        ≤ ENNReal.ofReal C * MeasureTheory.lintegral
            (MeasureTheory.Measure.restrict MeasureTheory.volume (f '' K)) H := by
  classical
  by_cases hKne : K.Nonempty
  · -- on `K` the Jacobian is negative, hence non-zero
    have hdetK : ∀ z ∈ K, (fderiv ℝ f z).det ≠ 0 := by
      intro z hz h0
      have hzS : z ∉ S := fun hc => (Set.disjoint_left.mp hKS hz) hc
      have hlt : ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖ := hrev z hzS
      have hdet := Work.MRMT.Sobolev.det_fderiv_eq f z
      rw [hdet, sub_eq_zero] at h0
      have habs : ‖Work.MRMT.dz f z‖ = ‖Work.MRMT.dzbar f z‖ := by
        have h2 := congrArg Real.sqrt h0
        rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (norm_nonneg _)] at h2
      linarith
    -- `z ↦ |det (fderiv ℝ f z)|` is continuous
    have hcont : Continuous (fun z : ℂ => |(fderiv ℝ f z).det|) := by
      have hc : Continuous fun p : ℂ × ℂ => (fderiv ℝ f p.1) p.2 :=
        hf.continuous_fderiv_apply (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      have h1 : Continuous fun z : ℂ => fderiv ℝ f z (1 : ℂ) :=
        hc.comp (continuous_id.prodMk continuous_const)
      have hI : Continuous fun z : ℂ => fderiv ℝ f z Complex.I :=
        hc.comp (continuous_id.prodMk continuous_const)
      have hdz : Continuous fun z : ℂ => ‖Work.MRMT.dz f z‖ := by
        have h : Continuous fun z : ℂ => Work.MRMT.dz f z := by
          simp only [Work.MRMT.dz]
          exact (h1.sub (continuous_const.mul hI)).div_const 2
        exact h.norm
      have hdzb : Continuous fun z : ℂ => ‖Work.MRMT.dzbar f z‖ := by
        have h : Continuous fun z : ℂ => Work.MRMT.dzbar f z := by
          simp only [Work.MRMT.dzbar]
          exact (h1.add (continuous_const.mul hI)).div_const 2
        exact h.norm
      have : (fun z : ℂ => |(fderiv ℝ f z).det|)
          = fun z => |‖Work.MRMT.dz f z‖ ^ 2 - ‖Work.MRMT.dzbar f z‖ ^ 2| := by
        funext z; rw [Work.MRMT.Sobolev.det_fderiv_eq]
      rw [this]
      exact ((hdz.pow 2).sub (hdzb.pow 2)).abs
    -- a uniform positive lower bound for `|det|` on `K`
    obtain ⟨m, hmpos, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K, m ≤ |(fderiv ℝ f z).det| := by
      obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
      exact ⟨|(fderiv ℝ f z₀).det|, abs_pos.mpr (hdetK z₀ hz₀), fun z hz => hmin hz⟩
    -- cover `K` by finitely many open sets on which `f` is injective
    have hball : ∀ z : K, ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ Set.InjOn f U := fun z =>
      let ⟨δ, hδ, hinj⟩ := exists_injOn_ball_of_det_ne_zero hf (hdetK z z.2)
      ⟨Metric.ball (z : ℂ) δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, hinj⟩
    choose U hUo hUz hUi using hball
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun z => hUo z)
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hUz ⟨z, hz⟩⟩)
    -- the bound on each piece of the cover
    have hpiece : ∀ i : K, ∀ H : ℂ → ENNReal,
        ∫⁻ z in U i ∩ K, H (f z) ≤ ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' K, H w := by
      intro i H
      have hs : MeasurableSet (U i ∩ K) := (hUo i).measurableSet.inter hK.isClosed.measurableSet
      have hinj : Set.InjOn f (U i ∩ K) := (hUi i).mono Set.inter_subset_left
      have hdiff : ∀ z ∈ U i ∩ K, HasFDerivWithinAt f (fderiv ℝ f z) (U i ∩ K) z := fun z _ =>
        ((hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) z).hasFDerivAt).hasFDerivWithinAt
      have hb : ∀ z ∈ U i ∩ K, m ≤ |(fderiv ℝ f z).det| := fun z hz => hm z hz.2
      calc ∫⁻ z in U i ∩ K, H (f z)
          ≤ ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' (U i ∩ K), H w :=
            lintegral_comp_le_of_injOn_abs_det hs hdiff hinj hmpos hb H
        _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' K, H w :=
            mul_le_mul_right (MeasureTheory.lintegral_mono_set
              (Set.image_mono Set.inter_subset_right)) _
    refine ⟨(t.card : ℝ) * m⁻¹, ?_, ?_⟩
    · have htne : t.Nonempty := by
        obtain ⟨z, hz⟩ := hKne
        obtain ⟨i, hit, -⟩ := Set.mem_iUnion₂.mp (ht hz)
        exact ⟨i, hit⟩
      have hcard : (0 : ℝ) < (t.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr htne
      positivity
    · intro H
      have hcover : ⋃ i ∈ t, (U i ∩ K) = K := by
        apply Set.Subset.antisymm
        · intro z hz
          obtain ⟨i, -, hzi⟩ := Set.mem_iUnion₂.mp hz
          exact hzi.2
        · intro z hz
          obtain ⟨i, hit, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
          exact Set.mem_iUnion₂.mpr ⟨i, hit, hzi, hz⟩
      have hstep2 : ∫⁻ z in ⋃ i ∈ t, (U i ∩ K), H (f z)
          ≤ ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (f z) :=
        lintegral_biUnion_finset_le t (fun i => U i ∩ K) (fun z => H (f z))
      have hstep3 : ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (f z)
          ≤ ∑ i ∈ t, ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' K, H w :=
        Finset.sum_le_sum fun i _ => hpiece i H
      have hstep4 : ∑ i ∈ t, ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' K, H w
          = ((t.card : ENNReal) * ENNReal.ofReal m⁻¹) * ∫⁻ w in f '' K, H w := by
        rw [Finset.sum_const, nsmul_eq_mul, (mul_assoc _ _ _).symm]
      have hC : ENNReal.ofReal ((t.card : ℝ) * m⁻¹)
          = (t.card : ENNReal) * ENNReal.ofReal m⁻¹ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (t.card : ℝ)), ENNReal.ofReal_natCast]
      calc ∫⁻ z in K, H (f z)
          = ∫⁻ z in ⋃ i ∈ t, (U i ∩ K), H (f z) := by rw [hcover]
        _ ≤ ∑ i ∈ t, ∫⁻ z in U i ∩ K, H (f z) := hstep2
        _ ≤ ∑ i ∈ t, ENNReal.ofReal m⁻¹ * ∫⁻ w in f '' K, H w := hstep3
        _ = ((t.card : ENNReal) * ENNReal.ofReal m⁻¹) * ∫⁻ w in f '' K, H w := hstep4
        _ = ENNReal.ofReal ((t.card : ℝ) * m⁻¹) * ∫⁻ w in f '' K, H w := by rw [hC]
  · -- `K = ∅`: any positive constant works
    refine ⟨1, one_pos, fun H => ?_⟩
    have hK0 : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simp [hK0]

end

end Work.MRMT.Found
