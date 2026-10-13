/-
# `hasFDerivAt_of_weakGrad` — a continuous weak gradient is a strong gradient

`Work.FTS.PressureOn.Auxiliary.hasFDerivAt_of_weakGrad`: if `q : ℝ³ → ℝ` is continuous,
`Φ : ℝ³ → ℝ³` is continuous, and for every smooth compactly supported test function `k` and every
coordinate direction `i`

`∫ x, k x * Φ x i = - ∫ x, q x * (fderiv ℝ k x) (e i)`   (i.e. `∂ᵢq = Φᵢ` weakly),

then `q` is differentiable everywhere with gradient `Φ`:
`∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x`.

## Route

1. **Weak gradient ⟹ coordinate FTC** (`fTC_of_weakGradient`).  For a test function `ω` we compare
   the pairing `∫ y, ω y * (q (y + t eᵢ) - q y)` with `∫ y, ω y * ∫₀ᵗ Φ (y + s eᵢ)ᵢ`.
   Translation invariance of Lebesgue measure moves the shift onto `ω`; the one dimensional
   fundamental theorem of calculus rewrites `ω (y - t eᵢ) - ω y = -∫₀ᵗ ∂ᵢω (y - s eᵢ) ds`; Fubini
   (over the compact interval `(0,t)` and `ℝ³`) moves the `s`-integral out; the hypothesis applied
   to the translated test function `y ↦ ω (y - s eᵢ)` identifies the resulting pairings; a second
   change of variables and one more Fubini put the integral back into the desired shape.  Since the
   difference `q (y + t eᵢ) - q y - ∫₀ᵗ Φ (y + s eᵢ)ᵢ` is a *continuous* function pairing to zero
   against every test function, du Bois–Reymond plus `Measure.eq_of_ae_eq` give the pointwise
   identity.
2. **Coordinate FTC ⟹ differentiability** (`Work.FTS.PressureOn.Weyl.hasFDerivAt_of_fTC`, proved
   in the workspace): telescoping the three coordinate increments along the polygonal path.

The integrability input for the two Fubini steps is the auxiliary lemma
`integrable_uncurry_prod_restrict_aux`: a continuous function on `ℝ × ℝ³` vanishing (on the
interval) off a fixed compact set in its second variable is integrable for the product of the
interval-restricted Lebesgue measure with Lebesgue measure.
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Weyl.hasFDerivAt_of_fTC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity MeasureTheory Filter Set
open scoped Topology Pointwise

namespace Work.FTS.PressureOn.Auxiliary

/-- **Integrability of a continuous function vanishing off a compact set in its second
variable.**  For a continuous `φ : ℝ → ℝ³ → ℝ` which vanishes on the interval `uIoc a b` whenever
its second argument lies outside a fixed compact set `K`, the uncurried function is integrable for
the product of Lebesgue measure on the interval `uIoc a b` (restricted) with Lebesgue measure on
`ℝ³`.  This is the Fubini hypothesis needed to swap an interval integral in the first variable
with an integral over `ℝ³` in the second. -/
lemma integrable_uncurry_prod_restrict_aux {a b : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K)
    {φ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : Continuous (Function.uncurry φ))
    (hvan : ∀ σ ∈ Set.uIoc a b, ∀ u, u ∉ K → φ σ u = 0) :
    Integrable (Function.uncurry φ)
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  have hmeas : MeasurableSet (Set.uIcc a b ×ˢ K) :=
    isCompact_uIcc.isClosed.measurableSet.prod hK.isClosed.measurableSet
  have hmeas2 : MeasurableSet (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) :=
    measurableSet_uIoc.prod MeasurableSet.univ
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod hK).exists_bound_of_continuousOn hφ.continuousOn
  have hbox : IntegrableOn (Function.uncurry φ) (Set.uIcc a b ×ˢ K) (volume.prod volume) := by
    refine IntegrableOn.of_bound ?_ ?_ C ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top isCompact_uIcc.measure_lt_top hK.measure_lt_top
    · exact hφ.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' hmeas]
      exact Eventually.of_forall fun p hp => hC p hp
  have hind : Integrable (Set.indicator (Set.uIcc a b ×ˢ K) (Function.uncurry φ))
      (volume.prod volume) := (integrable_indicator_iff hmeas).mpr hbox
  have hsub : Set.uIcc a b \ Set.uIoc a b ⊆ ({a, b} : Set ℝ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Set.mem_uIcc] at hx1
    rw [Set.mem_uIoc] at hx2
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases h : a < x
      · exact absurd (Or.inl ⟨h, h2⟩) hx2
      · left; exact le_antisymm (not_lt.mp h) h1
    · by_cases h : b < x
      · exact absurd (Or.inr ⟨h, h2⟩) hx2
      · right; exact le_antisymm (not_lt.mp h) h1
  have hae : Set.indicator (Set.uIcc a b ×ˢ K) (Function.uncurry φ)
      =ᵐ[volume.prod volume]
      Set.indicator (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))))
        (Function.uncurry φ) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (t := ({a, b} : Set ℝ) ×ˢ K) ?_ ?_
    · intro p hp
      rw [Set.mem_ofPred_eq] at hp
      have hmem1 : p.2 ∈ K := by
        by_contra h2c
        apply hp
        have h1 : (Set.uIcc a b ×ˢ K).indicator (Function.uncurry φ) p = 0 :=
          Set.indicator_of_notMem (fun hc => h2c hc.2) _
        have h2 : (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))).indicator
            (Function.uncurry φ) p = 0 := by
          by_cases h3 : p.1 ∈ Set.uIoc a b
          · rw [Set.indicator_of_mem (show p ∈ Set.uIoc a b ×ˢ Set.univ from
              ⟨h3, Set.mem_univ _⟩)]
            exact hvan p.1 h3 p.2 h2c
          · exact Set.indicator_of_notMem (fun hc => h3 hc.1) _
        rw [h1, h2]
      have hmem2 : p.1 ∈ ({a, b} : Set ℝ) := by
        by_contra h1c
        apply hp
        by_cases h3 : p.1 ∈ Set.uIoc a b
        · rw [Set.indicator_of_mem (show p ∈ Set.uIcc a b ×ˢ K from
                ⟨Set.uIoc_subset_uIcc h3, hmem1⟩),
              Set.indicator_of_mem (show p ∈ Set.uIoc a b ×ˢ Set.univ from
                ⟨h3, Set.mem_univ _⟩)]
        · have h4 : p.1 ∉ Set.uIcc a b := fun hc => h1c (hsub ⟨hc, h3⟩)
          rw [Set.indicator_of_notMem (fun hc => h4 hc.1),
            Set.indicator_of_notMem (fun hc => h3 hc.1)]
      exact Set.mem_prod.mpr ⟨hmem2, hmem1⟩
    · rw [Measure.prod_prod, show (volume : Measure ℝ) ({a, b} : Set ℝ) = 0 from by
        rw [show ({a, b} : Set ℝ) = {a} ∪ {b} from rfl,
          measure_union_null (measure_singleton a) (measure_singleton b)], zero_mul]
  have hind2 : Integrable (Set.indicator (Set.uIoc a b ×ˢ
      (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) (Function.uncurry φ))
      (volume.prod volume) := hind.congr hae
  have h1' : IntegrableOn (Function.uncurry φ)
      (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))))
      (volume.prod volume) := (integrable_indicator_iff hmeas2).mp hind2
  have hEq := Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (Set.uIoc a b) Set.univ
  rw [Measure.restrict_univ] at hEq
  rw [hEq]
  exact h1'

/-- The chain rule for a translate of a function: the derivative of `w ↦ g (w - s • eᵢ)` is the
translated derivative of `g`. -/
lemma hasFDerivAt_sub_smul_comp (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : Differentiable ℝ g)
    (i : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => g (w - s • FiniteTimeSingularity.e i)) y
      = fderiv ℝ g (y - s • FiniteTimeSingularity.e i) := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 3) => w - s • FiniteTimeSingularity.e i)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) y := (hasFDerivAt_id y).sub_const _
  have h2 : HasFDerivAt g (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
      (y - s • FiniteTimeSingularity.e i) := (hg _).hasFDerivAt
  have h3 := h2.comp y h1
  simpa [Function.comp_def] using h3.fderiv

/-- A translate of a compactly supported function is compactly supported. -/
lemma hasCompactSupport_sub_smul (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : HasCompactSupport g) (i : Fin 3) (s : ℝ) :
    HasCompactSupport
      (fun y : EuclideanSpace ℝ (Fin 3) => g (y - s • FiniteTimeSingularity.e i)) := by
  refine HasCompactSupport.intro
    (K := tsupport g + ({s • FiniteTimeSingularity.e i} : Set (EuclideanSpace ℝ (Fin 3))))
    (IsCompact.add hg isCompact_singleton) ?_
  intro y hy
  refine image_eq_zero_of_notMem_tsupport (fun hmem => hy ?_)
  rw [Set.mem_add]
  exact ⟨y - s • FiniteTimeSingularity.e i, hmem, s • FiniteTimeSingularity.e i,
    Set.mem_singleton _, by abel⟩

/-- **Weak gradient ⟹ the coordinate fundamental theorem of calculus.**  If `∂ᵢq = Φᵢ` weakly
(against all smooth compactly supported test functions) with `q` and `Φ` continuous, then the
increment of `q` along every coordinate line is the integral of the corresponding component of
`Φ`. -/
theorem fTC_of_weakGradient (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hgrad : ∀ i : Fin 3, ∀ k : EuclideanSpace ℝ (Fin 3) → ℝ,
      (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
      ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i)) :
    ∀ x : EuclideanSpace ℝ (Fin 3), ∀ t : ℝ, ∀ i : Fin 3,
      q (x + t • FiniteTimeSingularity.e i) - q x
        = ∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i := by
  intro x t i
  have hGcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      (hΦ.comp (continuous_fst.add (continuous_snd.smul continuous_const))))
  -- the pairing identity
  have hpair : ∀ (g : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ n : ℕ, ContDiff ℝ n g) → HasCompactSupport g →
      ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) = 0 := by
    intro g hg hgc
    have hgd : Differentiable ℝ g := (hg 1).differentiable (by norm_num)
    -- ### translation invariance
    have htrans : ∫ y, g y * q (y + t • FiniteTimeSingularity.e i)
        = ∫ y, g (y - t • FiniteTimeSingularity.e i) * q y := by
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun y : EuclideanSpace ℝ (Fin 3) => g y * q (y + t • FiniteTimeSingularity.e i))
        (t • FiniteTimeSingularity.e i)
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [sub_add_cancel]
    -- ### the one dimensional fundamental theorem of calculus along the line
    have hftc : ∀ y : EuclideanSpace ℝ (Fin 3), g y - g (y - t • FiniteTimeSingularity.e i)
        = ∫ s in (0 : ℝ)..t,
            (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) := by
      intro y
      have hderiv : ∀ s : ℝ,
          HasDerivAt (fun s : ℝ => g (y - s • FiniteTimeSingularity.e i))
            (-((fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
              (FiniteTimeSingularity.e i))) s := by
        intro s
        have h1 : HasDerivAt (fun s : ℝ => y - s • FiniteTimeSingularity.e i)
            (-(FiniteTimeSingularity.e i)) s := by
          simpa using ((hasDerivAt_id s).smul_const (FiniteTimeSingularity.e i)).const_sub y
        have h2 : HasFDerivAt g (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (y - s • FiniteTimeSingularity.e i) := (hgd _).hasFDerivAt
        simpa [Function.comp_def] using h2.comp_hasDerivAt s h1
      have hint : IntervalIntegrable
          (fun s : ℝ => -((fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i))) volume (0 : ℝ) t := by
        refine Continuous.intervalIntegrable ?_ 0 t
        exact (((hg 1).continuous_fderiv_apply (by norm_num)).comp
          ((continuous_const.sub (continuous_id.smul continuous_const)).prodMk
            continuous_const)).neg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
      rw [intervalIntegral.integral_neg] at h
      simp only [zero_smul, sub_zero] at h
      linarith [h]
    -- ### the weak identity for the translated test function, for each `s`
    have hweak : ∀ s : ℝ,
        ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) * q y
          = -∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i := by
      intro s
      have hwk := hgrad i (fun y : EuclideanSpace ℝ (Fin 3) =>
          g (y - s • FiniteTimeSingularity.e i))
        (fun n => (hg n).comp (contDiff_id.sub contDiff_const))
        (hasCompactSupport_sub_smul g hgc i s)
      have hfd : ∀ y : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            g (w - s • FiniteTimeSingularity.e i)) y) (FiniteTimeSingularity.e i)
            = (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) :=
        fun y => by rw [hasFDerivAt_sub_smul_comp g hgd i s y]
      have hcongr : (∫ x, q x * (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
              g (w - s • FiniteTimeSingularity.e i)) x) (FiniteTimeSingularity.e i))
            = ∫ x, q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show q x * (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            g (w - s • FiniteTimeSingularity.e i)) x) (FiniteTimeSingularity.e i)
          = q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i)
        rw [hfd x]
      rw [hcongr] at hwk
      rw [show (∫ x, q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
              (FiniteTimeSingularity.e i))
            = ∫ x, (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q x
          from integral_congr_ae (Eventually.of_forall fun x => by ring)] at hwk
      simpa using (congrArg Neg.neg hwk).symm
    -- ### the translated derivative has compact support
    have hcs' : HasCompactSupport
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ g z) (FiniteTimeSingularity.e i)) := by
      refine HasCompactSupport.intro (K := tsupport g) hgc ?_
      intro z hz
      have hopen : IsOpen (tsupport g)ᶜ := (isClosed_tsupport g).isOpen_compl
      have h0 : g =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact image_eq_zero_of_notMem_tsupport hw
      rw [h0.fderiv_eq]
      simp
    -- ### integrability for the first Fubini
    have hInt1 : Integrable (Function.uncurry fun (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) =>
        (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) * q y)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
      refine integrable_uncurry_prod_restrict_aux (K := tsupport
        (fun z : EuclideanSpace ℝ (Fin 3) => (fderiv ℝ g z) (FiniteTimeSingularity.e i))
        + Set.image (fun σ : ℝ => σ • FiniteTimeSingularity.e i) (Set.uIcc (0 : ℝ) t)) ?_ ?_ ?_
      · exact IsCompact.add hcs'
          (isCompact_uIcc.image ((continuous_id : Continuous fun s : ℝ => s).smul
            (continuous_const : Continuous fun _ : ℝ => FiniteTimeSingularity.e i)))
      · refine Continuous.mul ?_ (hq.comp continuous_snd)
        have h1 : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
            p.2 - p.1 • FiniteTimeSingularity.e i :=
          continuous_snd.sub (continuous_fst.smul continuous_const)
        exact (((hg 1).continuous_fderiv_apply (by norm_num)).comp
          (h1.prodMk continuous_const))
      · intro σ hσ y hy
        have hmem : y - σ • FiniteTimeSingularity.e i ∉
            tsupport (fun z : EuclideanSpace ℝ (Fin 3) =>
              (fderiv ℝ g z) (FiniteTimeSingularity.e i)) := by
          intro hcon
          exact hy (by
            rw [Set.mem_add]
            exact ⟨y - σ • FiniteTimeSingularity.e i, hcon, σ • FiniteTimeSingularity.e i,
              Set.mem_image_of_mem _ (Set.uIoc_subset_uIcc hσ), by abel⟩)
        rw [image_eq_zero_of_notMem_tsupport hmem, zero_mul]
    -- ### the first Fubini
    have hFub1 : ∫ y, (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i)) * q y
        = ∫ s in (0 : ℝ)..t, ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i) * q y := by
      rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
              (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i)) * q y)
            = fun y => ∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q y
          from funext fun y => (intervalIntegral.integral_mul_const (q y) _).symm]
      exact (MeasureTheory.intervalIntegral_integral_swap hInt1).symm
    -- ### integrability for the second Fubini
    have hInt2 : Integrable (Function.uncurry fun (s : ℝ) (u : EuclideanSpace ℝ (Fin 3)) =>
        g u * Φ (u + s • FiniteTimeSingularity.e i) i)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
      refine integrable_uncurry_prod_restrict_aux (K := tsupport g) ?_ ?_ ?_
      · exact hgc
      · exact ((hg 0).continuous.comp continuous_snd).mul
          ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
            (hΦ.comp (continuous_snd.add (continuous_fst.smul continuous_const))))
      · intro σ _ u hu
        rw [image_eq_zero_of_notMem_tsupport hu, zero_mul]
    -- ### the second Fubini
    have hFub2 : ∫ s in (0 : ℝ)..t, ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i
        = ∫ u, ∫ s in (0 : ℝ)..t, g u * Φ (u + s • FiniteTimeSingularity.e i) i :=
      MeasureTheory.intervalIntegral_integral_swap hInt2
    -- ### the change of variables in the `s`-integral
    have hshift : ∀ s : ℝ, ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i
        = ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i := by
      intro s
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : EuclideanSpace ℝ (Fin 3) => g u * Φ (u + s • FiniteTimeSingularity.e i) i)
        (s • FiniteTimeSingularity.e i)
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [sub_add_cancel]
    -- ### integrability of the three pieces of the `y`-integral
    have hi1 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * q (y + t • FiniteTimeSingularity.e i)) :=
      Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul (hq.comp (continuous_id.add continuous_const)))
        (HasCompactSupport.intro hgc fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    have hi2 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => g y * q y) :=
      Continuous.integrable_of_hasCompactSupport ((hg 0).continuous.mul hq)
        (HasCompactSupport.intro hgc fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    have hi3 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g (y - t • FiniteTimeSingularity.e i) * q y) :=
      Continuous.integrable_of_hasCompactSupport
        (((hg 0).continuous.comp (continuous_id.sub continuous_const)).mul hq)
        (HasCompactSupport.intro (hasCompactSupport_sub_smul g hgc i t) fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    -- ### the assembly
    have hL : ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
        = ∫ y, g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) := by
      calc ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
          = (∫ y, g (y - t • FiniteTimeSingularity.e i) * q y) - (∫ y, g y * q y) := by
            rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                  g y * (q (y + t • FiniteTimeSingularity.e i) - q y))
                = fun y => g y * q (y + t • FiniteTimeSingularity.e i) - g y * q y
              from funext fun y => by ring]
            rw [integral_sub hi1 hi2, htrans]
        _ = ∫ y, (g (y - t • FiniteTimeSingularity.e i) - g y) * q y := by
            have h1 : (∫ y, (g (y - t • FiniteTimeSingularity.e i) - g y) * q y)
                = (∫ y, g (y - t • FiniteTimeSingularity.e i) * q y) - (∫ y, g y * q y) := by
              rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                    (g (y - t • FiniteTimeSingularity.e i) - g y) * q y)
                  = fun y => g (y - t • FiniteTimeSingularity.e i) * q y - g y * q y
                from funext fun y => by ring]
              exact integral_sub hi3 hi2
            exact h1.symm
        _ = ∫ y, (-(∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i))) * q y := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            simp only [← hftc y]
            ring
        _ = -(∫ y, (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i)) * q y) := by
            rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                  (-(∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i))) * q y)
                = fun y => -((∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i)) * q y)
              from funext fun y => by ring]
            rw [integral_neg]
        _ = -(∫ s in (0 : ℝ)..t, ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q y) := by rw [hFub1]
        _ = -(∫ s in (0 : ℝ)..t,
                (-∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i)) := by
            rw [show (fun s : ℝ => ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i) * q y)
                = fun s => -∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i
              from funext hweak]
        _ = ∫ s in (0 : ℝ)..t, ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i := by
            rw [intervalIntegral.integral_neg, neg_neg]
        _ = ∫ s in (0 : ℝ)..t, ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i := by
            rw [show (fun s : ℝ => ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i)
                = fun s => ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i
              from funext hshift]
        _ = ∫ u, ∫ s in (0 : ℝ)..t, g u * Φ (u + s • FiniteTimeSingularity.e i) i := hFub2
        _ = ∫ u, g u * (∫ s in (0 : ℝ)..t, Φ (u + s • FiniteTimeSingularity.e i) i) := by
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            exact intervalIntegral.integral_const_mul (g u) _
    -- ### conclude
    have hA : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * (q (y + t • FiniteTimeSingularity.e i) - q y)) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul ((hq.comp (continuous_id.add continuous_const)).sub hq)) ?_
      exact HasCompactSupport.intro hgc fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    have hB : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i)) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul hGcont) ?_
      exact HasCompactSupport.intro hgc fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) => g y * (q (y + t • FiniteTimeSingularity.e i)
            - q y - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i))
        = fun y => g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
            - g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i)
      from funext fun y => by ring]
    rw [integral_sub hA hB, hL]
    exact sub_self _
  -- the pointwise conclusion, by du Bois-Reymond + continuity
  have hFcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) :=
    ((hq.comp (continuous_id.add continuous_const)).sub hq).sub hGcont
  have hae : (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hFcont.locallyIntegrable ?_
    intro g hg hgc
    simpa [smul_eq_mul] using hpair g (fun n => hg.of_le (by simp)) hgc
  have heq : (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) = 0 :=
    Measure.eq_of_ae_eq hae hFcont continuous_const
  have hx : q (x + t • FiniteTimeSingularity.e i) - q x
      - (∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i) = 0 := congrFun heq x
  linarith [hx]

/-- **A continuous weak gradient is a strong gradient.**  If `∂ᵢq = Φᵢ` weakly against all smooth
compactly supported test functions, with `q` and `Φ` continuous, then `q` is differentiable
everywhere with gradient `Φ`. -/
theorem hasFDerivAt_of_weakGrad (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hgrad : ∀ i : Fin 3, ∀ k : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n k) →
      HasCompactSupport k →
      ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i)) :
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x :=
  Work.FTS.PressureOn.Weyl.hasFDerivAt_of_fTC q Φ hΦ
    (fTC_of_weakGradient q Φ hq hΦ hgrad)

end Work.FTS.PressureOn.Auxiliary
