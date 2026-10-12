import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrable_sbMassKernel`

Integrability of the small-box pair-mass kernel

    (p₁, p₂) ↦ χ_{B(u)}(p₁) · |g₀(p₁ − p₂)| · χ_{B(u)}(p₂)

over the restricted product measure `volume.restrict (B(u) ×ˢ B(u))`, where
`B(u) = dlBox ℓ d u` is the sliding small box and `χ_{B(u)} = chiSmallB M ℓ d u`
is its cutoff.

The argument is elementary:

* `chiSmallB` is *uniformly bounded* by the constant `χ∞ · D_M`
  (`chiScale_abs_le_sup` for the big-scale factor, `chiSmall_decay_coord_le_decay`
  for the `ℓd`-scale factor), so the kernel is a.e. dominated by
  `(χ∞·D_M)² · |g₀(x − y)|`;
* `g₀` is integrable (`g0_integrable`) and is a.e. equal to a *measurable*
  representative `w`; the dominating function `|w(x − y)|` is integrable over
  `volume.restrict (B ×ˢ B)` because, by Tonelli and translation invariance of
  Lebesgue measure (`lintegral_prod_sub_le`), its lower integral is at most
  `(∫ |w|) · volume B`, and the small box has finite measure (`B ⊆ acube ℓ`);
* the two kernels agree a.e. (`ae_sub_notMem_of_volume_eq_zero`: the difference
  profile of a null set is null for the restricted product measure), which gives
  both the a.e. strong measurability and the a.e. pointwise domination needed for
  `Integrable.mono'`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The uniform bound of the small-box cutoff `chiSmallB M ℓ d u`. -/
private def sbBoundK (M : ℕ) : ℝ :=
  Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M

/-- **Tonelli/translation bound.**  For a measurable `G : ℝ³ → ℝ≥0∞` and an arbitrary set `B`,
the lower integral of the difference kernel `(x,y) ↦ G (x − y)` over the restricted product
measure `volume.restrict (B ×ˢ B)` is at most `(∫⁻ z, G z) · volume B`.

The restricted product measure is the product of the restricted measures
(`Measure.prod_restrict`, `Measure.volume_eq_prod`); Tonelli's theorem
(`lintegral_prod`) turns the lintegral into the iterated one, and for fixed `x` the inner
integral is bounded by `∫⁻ G` because `volume.restrict B ≤ volume` and `y ↦ x − y` is
measure-preserving (`Measure.measurePreserving_sub_left`). -/
private theorem lintegral_prod_sub_le {B : Set E3} {G : E3 → ENNReal} (hG : Measurable G) :
    (∫⁻ p : E3 × E3, G (p.1 - p.2) ∂(volume.restrict (B ×ˢ B)))
      ≤ (∫⁻ z : E3, G z) * (volume B) := by
  have hμeq : (volume.restrict (B ×ˢ B) : Measure (E3 × E3))
      = (volume.restrict B).prod (volume.restrict B) := by
    rw [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod E3 E3]
  have hsubm : Measurable (fun p : E3 × E3 => p.1 - p.2) := by fun_prop
  have hAEM : AEMeasurable (fun p : E3 × E3 => G (p.1 - p.2))
      ((volume.restrict B).prod (volume.restrict B)) :=
    (hG.comp hsubm).aemeasurable
  have hinner : ∀ x : E3, (∫⁻ y, G (x - y) ∂(volume.restrict B)) ≤ ∫⁻ z : E3, G z := by
    intro x
    calc (∫⁻ y, G (x - y) ∂(volume.restrict B))
        ≤ (∫⁻ y, G (x - y) ∂(volume : Measure E3)) :=
          lintegral_mono' (Measure.restrict_le_self (μ := (volume : Measure E3)) (s := B)) le_rfl
      _ = ∫⁻ z : E3, G z :=
          (Measure.measurePreserving_sub_left (volume : Measure E3) x).lintegral_comp hG
  calc (∫⁻ p : E3 × E3, G (p.1 - p.2) ∂(volume.restrict (B ×ˢ B)))
      = ∫⁻ p : E3 × E3, G (p.1 - p.2)
          ∂((volume.restrict B).prod (volume.restrict B)) := by simp only [hμeq]
    _ = ∫⁻ x : E3, ∫⁻ y : E3, G (x - y) ∂(volume.restrict B) ∂(volume.restrict B) :=
        lintegral_prod (fun p : E3 × E3 => G (p.1 - p.2)) hAEM
    _ ≤ ∫⁻ x : E3, (∫⁻ z : E3, G z) ∂(volume.restrict B) := lintegral_mono (fun x => hinner x)
    _ = (∫⁻ z : E3, G z) * (volume B) := by
        rw [lintegral_const, Measure.restrict_apply_univ]

/-- **Null difference profiles.**  If `t` is measurable and Lebesgue-null then, for the
restricted product measure on `B ×ˢ B`, almost every pair has `p.1 − p.2 ∉ t`. -/
private theorem ae_sub_notMem_of_volume_eq_zero {B t : Set E3}
    (htm : MeasurableSet t) (h0 : (volume : Measure E3) t = 0) :
    ∀ᵐ p : E3 × E3 ∂(volume.restrict (B ×ˢ B)), p.1 - p.2 ∉ t := by
  classical
  rw [MeasureTheory.ae_iff]
  have hsubm : Measurable (fun p : E3 × E3 => p.1 - p.2) := by fun_prop
  have hpre : MeasurableSet ((fun p : E3 × E3 => p.1 - p.2) ⁻¹' t) := htm.preimage hsubm
  have h1 : (volume.restrict (B ×ˢ B)) ((fun p : E3 × E3 => p.1 - p.2) ⁻¹' t)
      = ∫⁻ p : E3 × E3, (t.indicator (1 : E3 → ENNReal)) (p.1 - p.2)
          ∂(volume.restrict (B ×ˢ B)) := by
    rw [← lintegral_indicator_one hpre]
    apply lintegral_congr
    intro p
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  have hset : {p : E3 × E3 | ¬ (p.1 - p.2 ∉ t)} = (fun p : E3 × E3 => p.1 - p.2) ⁻¹' t := by
    ext p
    simp
  rw [hset, h1]
  refine le_antisymm ?_ zero_le
  calc (∫⁻ p : E3 × E3, (t.indicator (1 : E3 → ENNReal)) (p.1 - p.2)
        ∂(volume.restrict (B ×ˢ B)))
      ≤ (∫⁻ z : E3, (t.indicator (1 : E3 → ENNReal)) z) * (volume B) :=
        lintegral_prod_sub_le (B := B) (G := t.indicator (1 : E3 → ENNReal))
          (measurable_const.indicator htm)
    _ = 0 := by
        rw [lintegral_indicator_one htm, h0, zero_mul]

theorem integrable_sbMassKernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)) := by
  classical
  -- the sliding box, its finiteness, and the difference map
  set B : Set E3 := Submission.BoseGases.dlBox ℓ d u with hB
  have hBsub : B ⊆ Submission.BoseGases.acube ℓ := by
    rw [hB]
    exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hBfin : (volume : Measure E3) B < ⊤ :=
    lt_of_le_of_lt (measure_mono hBsub) (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  have hsubm : Measurable (fun p : E3 × E3 => p.1 - p.2) := by fun_prop
  -- uniform bound of the cutoff
  have hK0 : 0 ≤ sbBoundK M := by
    show 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  have hchiB : ∀ x : E3, |Submission.BoseGases.chiSmallB M ℓ d u x| ≤ sbBoundK M := by
    intro x
    show |Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
    rw [abs_mul]
    exact mul_le_mul (Submission.BoseGases.chiScale_abs_le_sup ℓ x)
      (Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u))
      (abs_nonneg _)
      Submission.BoseGases.chiSupAbs_nonneg
  have hchiBc : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) := by
    show Continuous (fun x : E3 => Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  have habs : Measurable (fun t : ℝ => |t|) := by fun_prop
  -- the scattering kernel and a measurable representative
  have hgc : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  let w : E3 → ℝ := AEMeasurable.mk (Submission.BoseGases.g0 v h) hgc.aemeasurable
  have hwm : Measurable w := AEMeasurable.measurable_mk hgc.aemeasurable
  have hwae : (Submission.BoseGases.g0 v h) =ᵐ[volume] w :=
    AEMeasurable.ae_eq_mk hgc.aemeasurable
  have hwInt : MeasureTheory.Integrable w := hgc.congr hwae
  -- the dominating profile `|w|` and its finiteness
  have hGfin : (∫⁻ z : E3, ENNReal.ofReal |w z|) < ⊤ := by
    have h1 := (hasFiniteIntegral_iff_norm w).mp hwInt.hasFiniteIntegral
    simpa only [Real.norm_eq_abs] using h1
  have hGm : Measurable (fun z : E3 => ENNReal.ofReal |w z|) :=
    (habs.comp hwm).ennreal_ofReal
  have hprod_fin :
      (∫⁻ p : E3 × E3, ENNReal.ofReal |w (p.1 - p.2)| ∂(volume.restrict (B ×ˢ B))) < ⊤ :=
    lt_of_le_of_lt
      (lintegral_prod_sub_le (B := B) (G := fun z : E3 => ENNReal.ofReal |w z|) hGm)
      (ENNReal.mul_lt_top hGfin hBfin)
  have hint_w : MeasureTheory.Integrable (fun p : E3 × E3 => |w (p.1 - p.2)|)
      (volume.restrict (B ×ˢ B)) := by
    refine ⟨?_, ?_⟩
    · exact ((habs.comp hwm).comp hsubm).aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_norm]
      have h2 : (fun p : E3 × E3 => ENNReal.ofReal ‖|w (p.1 - p.2)|‖)
          = fun p : E3 × E3 => ENNReal.ofReal |w (p.1 - p.2)| := by
        funext p
        rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      rw [h2]
      exact hprod_fin
  have hgdom : MeasureTheory.Integrable
      (fun p : E3 × E3 => sbBoundK M ^ 2 * |w (p.1 - p.2)|)
      (volume.restrict (B ×ˢ B)) :=
    hint_w.const_mul (sbBoundK M ^ 2)
  -- a.e. agreement of `g₀` and its representative along the difference profile
  have hN : (volume : Measure E3) {z : E3 | Submission.BoseGases.g0 v h z ≠ w z} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hwae
  obtain ⟨t, hNt, htm, ht0⟩ := exists_measurable_superset_of_null hN
  have hsub_t : ∀ᵐ p : E3 × E3 ∂(volume.restrict (B ×ˢ B)), p.1 - p.2 ∉ t :=
    ae_sub_notMem_of_volume_eq_zero (B := B) (t := t) htm ht0
  have hae_eq : ∀ᵐ p : E3 × E3 ∂(volume.restrict (B ×ˢ B)),
      Submission.BoseGases.g0 v h (p.1 - p.2) = w (p.1 - p.2) := by
    filter_upwards [hsub_t] with p hp
    by_contra hc
    exact hp (hNt hc)
  have hae_phi :
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2)
        =ᵐ[volume.restrict (B ×ˢ B)]
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |w (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2) := by
    filter_upwards [hae_eq] with p hp
    simp only [hp]
  -- a.e. strong measurability of the target integrand
  have hAESM : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2)
      (volume.restrict (B ×ˢ B)) := by
    have hm1 : Measurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1) :=
      hchiBc.measurable.comp measurable_fst
    have hm2 : Measurable (fun p : E3 × E3 => |w (p.1 - p.2)|) :=
      (habs.comp hwm).comp hsubm
    have hm3 : Measurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2) :=
      hchiBc.measurable.comp measurable_snd
    exact (((hm1.mul hm2).mul hm3).aestronglyMeasurable).congr hae_phi.symm
  -- the a.e. pointwise domination
  have hle : ∀ᵐ p : E3 × E3 ∂(volume.restrict (B ×ˢ B)),
      ‖Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2‖
        ≤ sbBoundK M ^ 2 * |w (p.1 - p.2)| := by
    filter_upwards [hae_eq] with p hp
    have hφ : Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
        = Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |w (p.1 - p.2)| * Submission.BoseGases.chiSmallB M ℓ d u p.2 := by
      simp only [hp]
    rw [hφ]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg, abs_nonneg]
    have h1 : |Submission.BoseGases.chiSmallB M ℓ d u p.1| ≤ sbBoundK M := hchiB p.1
    have h2 : |Submission.BoseGases.chiSmallB M ℓ d u p.2| ≤ sbBoundK M := hchiB p.2
    have hw0 : 0 ≤ |w (p.1 - p.2)| := abs_nonneg _
    calc |Submission.BoseGases.chiSmallB M ℓ d u p.1| * |w (p.1 - p.2)|
          * |Submission.BoseGases.chiSmallB M ℓ d u p.2|
        ≤ sbBoundK M * |w (p.1 - p.2)| * sbBoundK M :=
          mul_le_mul (mul_le_mul h1 le_rfl hw0 hK0) h2 (abs_nonneg _) (mul_nonneg hK0 hw0)
      _ = sbBoundK M ^ 2 * |w (p.1 - p.2)| := by ring
  exact MeasureTheory.Integrable.mono' hgdom hAESM hle

end Work.BoseFixB1
