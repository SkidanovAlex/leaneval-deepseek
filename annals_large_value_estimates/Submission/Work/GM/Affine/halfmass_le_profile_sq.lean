import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.integrable_Fhat_sq

/-!
# The half-period mass of `Fhat h` is at most the `L²`-mass of `h`

For `h : ℝ → ℝ` continuous with compact support and `g x = ‖Fhat h x‖²`,

`∫_0^{1/2} ∑'_ℓ g (ℓ + u) du ≤ ∫ h²`.

This is the "upper half" of the periodization/Plancherel identity
`∫_0^1 ∑'_ℓ g (ℓ + u) du = ∫ g = ∫ h²`: the integrand `u ↦ ∑'_ℓ g (ℓ+u)` is nonnegative, so the
integral over the half interval `(0, 1/2)` is at most the integral over the unit interval, which
equals `∫ g` by periodization (unfolding the `ℤ`-orbit of `(0,1]`), and `∫ g = ∫ h²` by Plancherel.

The proof below does not need measurability of the periodization itself: it uses
`integral_tsum` to unfold the integral of the series into the series of the integrals of the
individual shifts, compares each shift integral with the corresponding unit-interval integral, and
finishes with the `HasSum` decomposition of `∫ g` over the unit intervals.

The finiteness hypothesis of `integral_tsum` is supplied by the `ENNReal` (Tonelli) computation
`∑'_ℓ ∫⁻_{[0,1/2]} ‖g (ℓ+u)‖ₑ ≤ ∑'_ℓ ∫⁻_{[ℓ,ℓ+1]} ofReal (g) = ofReal (∫ g) < ⊤`.
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Translation of integrals over intervals -/

private lemma image_const_add_Ioc' (a c : ℝ) :
    (fun x : ℝ => a + x) '' Set.Ioc (0 : ℝ) c = Set.Ioc a (a + c) := by
  rw [Set.image_const_add_Ioc a 0 c]
  simp

private lemma setLIntegral_comp_add_left_Ioc' (f : ℝ → ℝ≥0∞) (a c : ℝ) :
    ∫⁻ u in Set.Ioc (0 : ℝ) c, f (a + u) = ∫⁻ x in Set.Ioc a (a + c), f x := by
  have h := MeasurePreserving.setLIntegral_comp_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding f (Set.Ioc (0 : ℝ) c)
  rw [image_const_add_Ioc'] at h
  exact h

private lemma setIntegral_comp_add_left_Ioc' {F : ℝ → ℝ} (a c : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) c, F (a + u) = ∫ x in Set.Ioc a (a + c), F x := by
  have h := (MeasurePreserving.setIntegral_image_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding F (Set.Ioc (0 : ℝ) c)).symm
  rw [image_const_add_Ioc'] at h
  exact h

/-! ## The unit intervals decompose the Lebesgue integral -/

private lemma disjoint_Ioc_intCast_unit (m n : ℤ) (hmn : m ≠ n) :
    Disjoint (Set.Ioc (m : ℝ) ((m : ℝ) + 1)) (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [Set.disjoint_left]
  intro x hmx hnx
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (by omega : m + 1 ≤ n)
    have hx1 : x ≤ (m : ℝ) + 1 := hmx.2
    have hx2 : (n : ℝ) < x := hnx.1
    linarith
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ m)
    have hx1 : x ≤ (n : ℝ) + 1 := hnx.2
    have hx2 : (m : ℝ) < x := hmx.1
    linarith

private lemma lintegral_intCast_Ioc_tsum' (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F x := by
  have hd : Pairwise (Function.onFun Disjoint (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) :=
    fun m n hmn => disjoint_Ioc_intCast_unit m n hmn
  have h := lintegral_iUnion (μ := volume) (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))
      (fun n => measurableSet_Ioc) hd F
  rw [iUnion_Ioc_intCast ℝ, Measure.restrict_univ] at h
  exact h

/-! ## Elementary facts about `ℂ`-valued norms of reals -/

private lemma norm_ofReal_sq' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

private lemma continuous_Fhat_of_continuous_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Continuous (Fhat f) := by
  rw [show Fhat f = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) from rfl]
  exact VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun u : ℝ => (f u : ℂ)) Real.continuous_fourierChar (by fun_prop)
    ((hf.integrable_of_hasCompactSupport hcs).ofReal)

/-! ## The main theorem -/

theorem halfmass_le_profile_sq {h : ℝ → ℝ} (hh : Continuous h) (hcs : HasCompactSupport h) :
    ∫ u in (0 : ℝ)..(1/2), (∑' ℓ : ℤ, ‖Work.GM.Affine.Fhat h ((ℓ : ℝ) + u)‖ ^ 2)
      ≤ ∫ x, (h x) ^ 2 := by
  set g : ℝ → ℝ := fun x => ‖Fhat h x‖ ^ 2 with hgdef
  have hFcont : Continuous (Fhat h) := continuous_Fhat_of_continuous_hasCompactSupport hh hcs
  have hgcont : Continuous g := by
    rw [hgdef]
    exact (hFcont.norm).pow 2
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    simp only [hgdef]
    positivity
  have hgc : Continuous (fun x : ℝ => ((h x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hh
  have hcsC : HasCompactSupport (fun x : ℝ => ((h x : ℝ) : ℂ)) :=
    hcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hgint : Integrable g := by
    rw [hgdef]
    simpa only [Fhat] using integrable_fourier_sq_of_continuous_hasCompactSupport hgc hcsC
  -- Plancherel: `∫ g = ∫ h ^ 2`
  have hplan : ∫ x, g x = ∫ x, (h x) ^ 2 := by
    have hp := plancherel_continuous (fun x : ℝ => ((h x : ℝ) : ℂ)) hgc hcsC
    have hL : ∫ x, ‖((h x : ℝ) : ℂ)‖ ^ 2 = ∫ x, (h x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => norm_ofReal_sq' (h x)))
    have hR : ∫ ξ, ‖FourierTransform.fourier (fun x : ℝ => ((h x : ℝ) : ℂ)) ξ‖ ^ 2
        = ∫ x, g x := by
      rw [hgdef]
      rfl
    rw [← hL, hp, hR]
  set S : ℝ → ℝ := fun u => ∑' ℓ : ℤ, g ((ℓ : ℝ) + u) with hSdef
  -- Finiteness of the sum of the `lintegrals`, which is the hypothesis of `integral_tsum`.
  have hfin : (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ‖g ((ℓ : ℝ) + u)‖ₑ) ≠ ⊤ := by
    have hstep : ∀ ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ‖g ((ℓ : ℝ) + u)‖ₑ
        ≤ ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ENNReal.ofReal (g x) := by
      intro ℓ
      calc ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ‖g ((ℓ : ℝ) + u)‖ₑ
          = ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (g ((ℓ : ℝ) + u)) :=
            lintegral_congr (fun u => Real.enorm_of_nonneg (hgnn _))
        _ = ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1 / 2), ENNReal.ofReal (g x) :=
            setLIntegral_comp_add_left_Ioc' (fun x => ENNReal.ofReal (g x)) (ℓ : ℝ) (1 / 2)
        _ ≤ ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ENNReal.ofReal (g x) :=
            lintegral_mono_set (Set.Ioc_subset_Ioc le_rfl (by norm_num))
    have hle' : (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ‖g ((ℓ : ℝ) + u)‖ₑ)
        ≤ ENNReal.ofReal (∫ x, g x) := by
      calc (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) (1 / 2), ‖g ((ℓ : ℝ) + u)‖ₑ)
          ≤ ∑' ℓ : ℤ, ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ENNReal.ofReal (g x) :=
            ENNReal.tsum_le_tsum hstep
        _ = ∫⁻ x, ENNReal.ofReal (g x) :=
            (lintegral_intCast_Ioc_tsum' (fun x => ENNReal.ofReal (g x))).symm
        _ = ENNReal.ofReal (∫ x, g x) :=
            (ofReal_integral_eq_lintegral_ofReal hgint
              (Filter.Eventually.of_forall hgnn)).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle'
  have hmeas : ∀ ℓ : ℤ, AEStronglyMeasurable (fun u : ℝ => g ((ℓ : ℝ) + u))
      (volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))) := fun ℓ =>
    ((hgcont.comp (continuous_const.add continuous_id)).measurable).aestronglyMeasurable
  have hA : ∫ u in (0 : ℝ)..(1 / 2), S u
      = ∑' ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u) := by
    rw [hSdef, intervalIntegral.integral_of_le (by norm_num)]
    exact integral_tsum hmeas hfin
  have ha_le : ∀ ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u)
      ≤ ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x := by
    intro ℓ
    calc ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u)
        = ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1 / 2), g x :=
          setIntegral_comp_add_left_Ioc' (ℓ : ℝ) (1 / 2)
      _ ≤ ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x := by
          refine setIntegral_mono_set (f := g) (s := Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1 / 2))
            (t := Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1))
            hgint.integrableOn ?_ ?_
          · exact Filter.Eventually.of_forall (fun x => hgnn x)
          · exact (Set.Ioc_subset_Ioc le_rfl (by norm_num)).eventuallyLE
  have ha_nn : ∀ ℓ : ℤ, 0 ≤ ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u) :=
    fun ℓ => integral_nonneg (fun u => hgnn ((ℓ : ℝ) + u))
  -- The unit-interval decomposition of `∫ g`
  have h0 := hgint.hasSum_intervalIntegral (0 : ℝ)
  have hfun : ∀ ℓ : ℤ, ∫ x in (0 : ℝ) + (ℓ : ℝ)..(0 : ℝ) + (ℓ : ℝ) + 1, g x
      = ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x := by
    intro ℓ
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right zero_le_one)]
    simp
  have hsumm : Summable (fun ℓ : ℤ => ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x) :=
    h0.summable.congr hfun
  have htsum : (∑' ℓ : ℤ, ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x) = ∫ x, g x :=
    (tsum_congr hfun).symm.trans h0.tsum_eq
  have hsumm_a : Summable (fun ℓ : ℤ => ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u)) :=
    Summable.of_nonneg_of_le ha_nn ha_le hsumm
  have hle : (∑' ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) (1 / 2), g ((ℓ : ℝ) + u))
      ≤ ∑' ℓ : ℤ, ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), g x :=
    Summable.tsum_le_tsum ha_le hsumm_a hsumm
  have hmain : ∫ u in (0 : ℝ)..(1 / 2), S u ≤ ∫ x, g x :=
    le_trans (le_of_eq hA) (le_trans hle (le_of_eq htsum))
  exact le_trans hmain (le_of_eq hplan)

end

end Work.GM.Affine
