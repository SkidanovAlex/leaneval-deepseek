/-
# The `Z4` bound of the `D_z`-coercivity estimate

This file proves `bound_Z4`, the estimate for the fourth term `Z4` in the expansion
`D_z(𝓛_Γ^T f) = Z1 + ⋯ + Z7` of `Dz_LGammaT_decomp`, namely

`wip Weta (Z4 α f) (D_z f) ≥ -(1/32) EDz f - 10^7 Ef f`

together with the joint integrability of the integrand.

Since `Z4 α f z θ = -κ(z,θ)·L₁₂f(z)`, where `κ(z,θ) = 2 z (1-z) Γ(θ)/(c(1+z)^3)`, the
argument is the AM-GM inequality `|a b| ≤ 8a² + b²/32` with `a = κ·L₁₂f`, `b = D_z f`,
followed by

* `κ²·Weta = 4 ((1-z)/(1+z))² (Γ/c)² sin(2θ)^{-η} / z² ≤ 4 (Γ/c)² sin(2θ)^{-η} / z²` (`z ≥ 0`),
* `∫_θ (Γ/c)² sin(2θ)^{-η} ≤ 18900` (`Gam_div_c_sq_eta_integral_le`),
* `∫_z (L₁₂f z / z)² = EL12z f ≤ 16 Ef f` (`EL12z_le`).

The subtle point is the *joint integrability* of the integrand: the hypotheses
`HardyHyp`/`CoerciveData` do not assume `f` (or `D_z f`) to be a.e. strongly measurable,
only that certain *quadratic* products are integrable.  The missing ingredient is supplied
by `ae_pz_eq_zero_of_aesm_sq`: if `f²` and `(D_z f)²` are a.e. strongly measurable, then
`∂_z f = 0` a.e. on the zero set of `f`, because every point of the zero set at which
`∂_z f ≠ 0` is an *isolated* point of the corresponding `z`-slice's zero set, and the
isolated points of a subset of `ℝ` are countable (`countable_isolated_points`), hence null.

The result is the paper's estimate for the term `I₄` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.f_sq_w_sq_integrable
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.EfEta_eq_wip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The product measure of the two restricted Lebesgue measures -/

/-- The product of the restrictions of Lebesgue measure to `Iz` and `Iθ`. -/
def muzθ : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)

theorem restrict_prod_eq_muzθ : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) = muzθ :=
  (prod_restrict_eq _ _).symm

/-- The uncurried form of a curried function, evaluated at an explicit pair. -/
theorem uncurry_apply_pair' (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Function.uncurry g p = g p.1 p.2 := rfl

/-! ## Auxiliary measure-theoretic lemmas -/

/-- The set of isolated points of a subset of `ℝ` is countable.  (A point `x ∈ S` is
isolated in `S` if `S ∩ Ioo (x - ε) (x + ε) = {x}` for some `ε > 0`.) -/
theorem countable_isolated_points (S : Set ℝ) :
    {x ∈ S | ∃ ε > 0, S ∩ Set.Ioo (x - ε) (x + ε) = {x}}.Countable := by
  have hdisc : IsDiscrete {x ∈ S | ∃ ε > 0, S ∩ Set.Ioo (x - ε) (x + ε) = {x}} := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    rintro x ⟨hxS, ε, hε, hεS⟩
    refine ⟨Set.Ioo (x - ε) (x + ε), isOpen_Ioo, ?_⟩
    ext y
    constructor
    · rintro ⟨hyI, hyT⟩
      have hy : y ∈ S ∩ Set.Ioo (x - ε) (x + ε) := ⟨hyT.1, hyI⟩
      rw [hεS] at hy
      exact hy
    · intro hy
      rw [mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨by linarith, by linarith⟩, hxS, ε, hε, hεS⟩
  exact IsLindelof.countable_of_isDiscrete (HereditarilyLindelofSpace.isLindelof _) hdisc

/-- If `g` vanishes at `z` and is eventually nonzero on a punctured neighbourhood of `z`,
then `z` is an isolated point of the zero set of `g`. -/
theorem isolated_zero_set_of_eventually_ne {g : ℝ → ℝ} {z : ℝ} (hz : g z = 0)
    (h : ∀ᶠ y in 𝓝[≠] z, g y ≠ 0) :
    ∃ ε > 0, {y | g y = 0} ∩ Set.Ioo (z - ε) (z + ε) = {z} := by
  obtain ⟨t₁, ht₁, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp h
  have ht₂' : {z}ᶜ ⊆ t₂ := Filter.mem_principal.mp ht₂
  obtain ⟨ε, hε, hball⟩ := (Metric.nhds_basis_ball.mem_iff.mp ht₁)
  refine ⟨ε, hε, ?_⟩
  ext y
  constructor
  · rintro ⟨hy0, hyI⟩
    rcases eq_or_ne y z with hyz | hyne
    · rw [hyz]; simp
    · exfalso
      have hyball : y ∈ Metric.ball z ε := by
        rw [Real.ball_eq_Ioo]; exact hyI
      have hy : y ∈ {x | g x ≠ 0} := by
        rw [heq]
        exact ⟨hball hyball, ht₂' (by simpa using hyne)⟩
      exact hy hy0
  · intro hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact ⟨hz, ⟨by linarith, by linarith⟩⟩

/-- **The key measurability fact.**  If `f²` and `(D_z f)²` are a.e. strongly measurable on
the quadrant, then `∂_z f` vanishes a.e. on the zero set of `f`.

Indeed, at a point where `f = 0` and `∂_z f ≠ 0`, the slice `z ↦ f z θ` cannot frequently
vanish (Mathlib's `deriv_zero_of_frequently_const`), so that point is an isolated point of
the slice's zero set.  Hence, for almost every `θ`, the set of such `z` is countable, hence
null; Fubini finishes. -/
theorem ae_pz_eq_zero_of_aesm_sq (f : ℝ → ℝ → ℝ)
    (hf2 : AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ ^ 2)) muzθ)
    (hDz2 : AEStronglyMeasurable (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2)) muzθ) :
    ∀ᵐ p ∂muzθ, f p.1 p.2 = 0 → Spaces.pz f p.1 p.2 = 0 := by
  set P : Measure (ℝ × ℝ) := muzθ with hP
  set Q : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iθ).prod (volume.restrict Spaces.Iz) with hQ
  set F : ℝ × ℝ → ℝ := hf2.mk (Function.uncurry (fun z θ => f z θ ^ 2)) with hFdef
  set G : ℝ × ℝ → ℝ := hDz2.mk (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2)) with hGdef
  have hFmeas : Measurable F := hf2.stronglyMeasurable_mk.measurable
  have hGmeas : Measurable G := hDz2.stronglyMeasurable_mk.measurable
  have hFae : Function.uncurry (fun z θ => f z θ ^ 2) =ᵐ[P] F := hf2.ae_eq_mk
  have hGae : Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2) =ᵐ[P] G := hDz2.ae_eq_mk
  have hmap : Measure.map Prod.swap Q = P := by
    rw [hQ, hP, muzθ]; exact Measure.prod_swap
  have hqmp : Measure.QuasiMeasurePreserving Prod.swap Q P := ⟨measurable_swap, by rw [hmap]⟩
  have hFslice : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (fun z => f z θ ^ 2) =ᵐ[volume.restrict Spaces.Iz] (fun z => F (z, θ)) := by
    have h' := Measure.ae_ae_eq_curry_of_prod (hqmp.ae_eq_comp hFae)
    filter_upwards [h'] with θ hθ
    have hc1 : Function.curry ((Function.uncurry (fun z θ => f z θ ^ 2)) ∘ Prod.swap) θ
        = (fun z => f z θ ^ 2) := by
      funext z
      simp only [Function.curry_apply, Function.uncurry_apply_pair, Function.comp_apply,
        Prod.swap_prod_mk]
    have hc2 : Function.curry (F ∘ Prod.swap) θ = (fun z => F (z, θ)) := by
      funext z
      simp only [Function.curry_apply, Function.comp_apply, Prod.swap_prod_mk]
    rw [hc1, hc2] at hθ
    exact hθ
  have hGslice : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ),
      (fun z => (Spaces.Dz f z θ) ^ 2) =ᵐ[volume.restrict Spaces.Iz] (fun z => G (z, θ)) := by
    have h' := Measure.ae_ae_eq_curry_of_prod (hqmp.ae_eq_comp hGae)
    filter_upwards [h'] with θ hθ
    have hc1 : Function.curry
        ((Function.uncurry (fun z θ => Spaces.Dz f z θ ^ 2)) ∘ Prod.swap) θ
        = (fun z => Spaces.Dz f z θ ^ 2) := by
      funext z
      simp only [Function.curry_apply, Function.uncurry_apply_pair, Function.comp_apply,
        Prod.swap_prod_mk]
    have hc2 : Function.curry (G ∘ Prod.swap) θ = (fun z => G (z, θ)) := by
      funext z
      simp only [Function.curry_apply, Function.comp_apply, Prod.swap_prod_mk]
    rw [hc1, hc2] at hθ
    exact hθ
  set M : Set (ℝ × ℝ) := {p | F p = 0 ∧ G p ≠ 0} with hMdef
  have hMmeas : MeasurableSet M :=
    (hFmeas (measurableSet_singleton 0)).inter
      ((measurableSet_singleton (0 : ℝ)).compl.preimage hGmeas)
  have hMnull : P M = 0 := by
    rw [hP, muzθ, Measure.prod_apply_symm hMmeas]
    refine (MeasureTheory.lintegral_eq_zero_iff'
      (measurable_measure_prodMk_right hMmeas).aemeasurable).mpr ?_
    filter_upwards [hFslice, hGslice] with θ hFθ hGθ
    have hBad : (volume.restrict Spaces.Iz)
        {z : ℝ | f z θ = 0 ∧ Spaces.pz f z θ ≠ 0} = 0 := by
      have hsub : {z : ℝ | f z θ = 0 ∧ Spaces.pz f z θ ≠ 0} ⊆
          {z ∈ {y : ℝ | f y θ = 0} |
            ∃ ε > 0, {y : ℝ | f y θ = 0} ∩ Set.Ioo (z - ε) (z + ε) = {z}} := by
        rintro z ⟨hz0, hzpz⟩
        refine ⟨hz0, ?_⟩
        refine isolated_zero_set_of_eventually_ne hz0 ?_
        have hfreq : ¬ (∃ᶠ y in 𝓝[≠] z, f y θ = 0) := by
          intro hcon
          have hd : deriv (fun y : ℝ => f y θ) z = 0 := deriv_zero_of_frequently_const hcon
          exact hzpz hd
        exact Filter.not_frequently.mp hfreq
      exact measure_mono_null hsub (Set.Countable.measure_zero
        (countable_isolated_points _) _)
    have hNθ : (volume.restrict Spaces.Iz)
        ({z : ℝ | F (z, θ) ≠ f z θ ^ 2}
          ∪ {z : ℝ | G (z, θ) ≠ (Spaces.Dz f z θ) ^ 2}) = 0 := by
      refine measure_union_null ?_ ?_
      · refine MeasureTheory.ae_iff.mp ?_
        filter_upwards [hFθ] with z hz
        simpa using hz.symm
      · refine MeasureTheory.ae_iff.mp ?_
        filter_upwards [hGθ] with z hz
        simpa using hz.symm
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hBad hNθ)
    by_cases hbad : f z θ = 0 ∧ Spaces.pz f z θ ≠ 0
    · exact Or.inl hbad
    · refine Or.inr ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
      obtain ⟨hFz, hGz⟩ := hcon
      rw [not_ne_iff] at hFz hGz
      refine hbad ⟨?_, ?_⟩
      · exact sq_eq_zero_iff.mp (by rw [← hFz, hz.1])
      · intro hpz
        have hDz : Spaces.Dz f z θ = 0 := by rw [Spaces.Dz, hpz, mul_zero]
        exact hz.2 (by rw [hGz, hDz]; norm_num)
  have hNnull : P ({p : ℝ × ℝ | F p ≠ f p.1 p.2 ^ 2}
      ∪ {p : ℝ × ℝ | G p ≠ (Spaces.Dz f p.1 p.2) ^ 2}) = 0 := by
    refine measure_union_null ?_ ?_
    · refine MeasureTheory.ae_iff.mp ?_
      filter_upwards [hFae] with p hp
      obtain ⟨a, b⟩ := p
      simpa [Function.uncurry_apply_pair] using hp.symm
    · refine MeasureTheory.ae_iff.mp ?_
      filter_upwards [hGae] with p hp
      obtain ⟨a, b⟩ := p
      simpa [Function.uncurry_apply_pair] using hp.symm
  have hZ0 : P {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [hP, muzθ, hset, Measure.prod_prod, measure_singleton]
    simp
  have hBnull : P {p : ℝ × ℝ | f p.1 p.2 = 0 ∧ Spaces.pz f p.1 p.2 ≠ 0} = 0 := by
    refine measure_mono_null (fun p hp => ?_)
      (measure_union_null (measure_union_null hMnull hNnull) hZ0)
    by_contra hcon
    rw [hMdef] at hcon
    simp only [Set.mem_union, Set.mem_setOf_eq] at hcon
    simp only [not_or] at hcon
    obtain ⟨⟨hpM, hpF', hpG'⟩, hpz0⟩ := hcon
    rw [not_ne_iff] at hpF' hpG'
    refine hpM ⟨?_, ?_⟩
    · rw [hpF', hp.1]; norm_num
    · rw [hpG']
      have hDz : Spaces.Dz f p.1 p.2 ≠ 0 := by
        rw [Spaces.Dz, mul_ne_zero_iff]
        exact ⟨hpz0, hp.2⟩
      exact pow_ne_zero 2 hDz
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hBnull
  filter_upwards [hBnull] with p hp hfp
  by_contra hne
  exact hp ⟨hfp, hne⟩


/-! ## Non-vanishing of the weights, a.e. -/

/-- `w(z)²` is nonzero a.e. on the quadrant. -/
theorem w_sq_ne_zero_ae : ∀ᵐ p ∂muzθ, Spaces.w p.1 ^ 2 ≠ 0 := by
  have hmem : ∀ᵐ p ∂muzθ, p.1 ∈ Spaces.Iz := by
    rw [← restrict_prod_eq_muzθ]
    exact (ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)).mono fun p hp => hp.1
  have hz : ∀ᵐ p ∂muzθ, p.1 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [hset, muzθ, Measure.prod_prod,
      measure_singleton (μ := volume.restrict Spaces.Iz) (0 : ℝ)]
    simp
  filter_upwards [hmem, hz] with p hp hne
  have h1 : (1 : ℝ) + p.1 ≠ 0 := by
    have : (0 : ℝ) ≤ p.1 := hp
    linarith
  rw [Spaces.w]
  exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 hne))

/-- The zero set of `θ ↦ sin (2θ)` is countable. -/
theorem countable_sin_two_zero : ({θ : ℝ | Real.sin (2 * θ) = 0} : Set ℝ).Countable :=
  (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi / 2)).mono (fun θ hθ => by
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hθ
    exact ⟨n, by linarith⟩)

/-- `sin (2θ)` is nonzero a.e. on `Iθ`. -/
theorem sin_two_ne_zero_ae_Iθ : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), Real.sin (2 * θ) ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simpa only [ne_eq, not_not] using
    Set.Countable.measure_zero countable_sin_two_zero (volume.restrict Spaces.Iθ)

/-- The zero set of `K` is countable. -/
theorem countable_K_zero : ({θ : ℝ | Spaces.K θ = 0} : Set ℝ).Countable := by
  refine Set.Countable.mono ?_ (Set.Countable.union
    (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi))
    (Set.countable_range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2)))
  intro θ hθ
  simp only [Spaces.K] at hθ
  rcases mul_eq_zero.mp hθ with h | h
  · rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact Or.inl (by obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h1; exact ⟨n, by linarith⟩)
  · exact Or.inr (by
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp (sq_eq_zero_iff.mp h)
      exact ⟨k, by linarith⟩)

/-- `K` is nonzero a.e. on `Iθ`. -/
theorem K_ne_zero_ae_Iθ : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), Spaces.K θ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simpa only [ne_eq, not_not] using
    Set.Countable.measure_zero countable_K_zero (volume.restrict Spaces.Iθ)

/-- `K` is nonzero a.e. on the quadrant (as a function of the second coordinate). -/
theorem K_ne_zero_ae : ∀ᵐ p ∂muzθ, Spaces.K p.2 ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null
    (t := (Set.univ : Set ℝ) ×ˢ {θ : ℝ | Spaces.K θ = 0}) (fun p hp => ?_) ?_
  · refine ⟨Set.mem_univ _, ?_⟩
    have hp' : ¬ (Spaces.K p.2 ≠ 0) := by simpa using hp
    exact not_not.mp hp'
  · rw [muzθ, Measure.prod_prod]
    have h0 : (volume.restrict Spaces.Iθ) {θ : ℝ | Spaces.K θ = 0} = 0 :=
      Set.Countable.measure_zero countable_K_zero _
    rw [h0]
    simp

/-- The weight `w(z)² sin(2θ)^{-η}` is nonzero a.e. on the quadrant. -/
theorem wetaWeight_ne_zero_ae :
    ∀ᵐ p ∂muzθ, Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta) ≠ 0 := by
  have hmemθ : ∀ᵐ p ∂muzθ, p.2 ∈ Spaces.Iθ := by
    rw [← restrict_prod_eq_muzθ]
    exact (ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)).mono fun p hp => hp.2
  have hθ : ∀ᵐ p ∂muzθ, Real.sin (2 * p.2) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null
      (t := (Set.univ : Set ℝ) ×ˢ {θ : ℝ | Real.sin (2 * θ) = 0}) (fun p hp => ?_) ?_
    · refine ⟨Set.mem_univ _, ?_⟩
      have hp' : ¬ (Real.sin (2 * p.2) ≠ 0) := by simpa using hp
      exact not_not.mp hp'
    · rw [muzθ, Measure.prod_prod]
      have h0 : (volume.restrict Spaces.Iθ) {θ : ℝ | Real.sin (2 * θ) = 0} = 0 :=
        Set.Countable.measure_zero countable_sin_two_zero _
      rw [h0]
      simp
  filter_upwards [w_sq_ne_zero_ae, hθ, hmemθ] with p hw hs hI
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hI.1]) (by linarith [hI.2, Real.pi_pos])
  exact mul_ne_zero hw ((Real.rpow_ne_zero hsin (by rw [Spaces.eta]; norm_num)).mpr hs)

/-! ## Almost everywhere strong measurability of the ingredients -/

/-- `f²` is a.e. strongly measurable under `CoerciveData`. -/
theorem aesm_f_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ ^ 2)) muzθ := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      f p.1 p.2 * f p.1 p.2
        * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) muzθ := by
    rw [← restrict_prod_eq_muzθ]
    refine hi.intFeta.aestronglyMeasurable.congr ?_
    filter_upwards with p
    simp only [uncurry_apply_pair']; ring
  have hW : Measurable (fun p : ℝ × ℝ =>
      Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by
    have hw : Measurable fun z : ℝ => Spaces.w z ^ 2 := by
      unfold Spaces.w; fun_prop
    have hs : Measurable fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    exact (hw.comp measurable_fst).mul (hs.comp measurable_snd)
  refine (h1.div₀ hW.aestronglyMeasurable).congr ?_
  filter_upwards [wetaWeight_ne_zero_ae] with p hp
  simp only [uncurry_apply_pair', Pi.div_apply]
  rw [mul_div_assoc, div_self hp, mul_one, sq]

/-- `(D_z f)²` is a.e. strongly measurable under `CoerciveData`. -/
theorem aesm_Dz_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2)) muzθ := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2
        * (Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))) muzθ := by
    rw [← restrict_prod_eq_muzθ]
    refine hi.intDz.aestronglyMeasurable.congr ?_
    filter_upwards with p
    simp only [uncurry_apply_pair']; ring
  have hW : Measurable (fun p : ℝ × ℝ =>
      Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by
    have hw : Measurable fun z : ℝ => Spaces.w z ^ 2 := by
      unfold Spaces.w; fun_prop
    have hs : Measurable fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    exact (hw.comp measurable_fst).mul (hs.comp measurable_snd)
  refine (h1.div₀ hW.aestronglyMeasurable).congr ?_
  filter_upwards [wetaWeight_ne_zero_ae] with p hp
  simp only [uncurry_apply_pair', Pi.div_apply]
  rw [mul_div_assoc, div_self hp, mul_one, sq]

/-- `f · D_z f` is a.e. strongly measurable under `CoerciveData`. -/
theorem aesm_f_mul_Dz (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ * Spaces.Dz f z θ)) muzθ := by
  have hL : AEStronglyMeasurable (fun p : ℝ × ℝ => L f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      muzθ := by
    rw [← restrict_prod_eq_muzθ]
    exact hi.intL.aestronglyMeasurable
  have hF2 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2)
      muzθ := by
    rw [← restrict_prod_eq_muzθ]
    exact (f_sq_w_sq_integrable α f hi).aestronglyMeasurable
  have hc : Measurable (fun p : ℝ × ℝ => 1 - 2 / (1 + p.1)) := by fun_prop
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      f p.1 p.2 * Spaces.Dz f p.1 p.2 * Spaces.w p.1 ^ 2) muzθ := by
    refine (hL.sub (hc.aestronglyMeasurable.mul hF2)).congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Pi.sub_apply, Pi.mul_apply, L, Spaces.Dz]
    ring_nf
  have hW : Measurable (fun p : ℝ × ℝ => Spaces.w p.1 ^ 2) := by
    have hw : Measurable fun z : ℝ => Spaces.w z ^ 2 := by
      unfold Spaces.w; fun_prop
    exact hw.comp measurable_fst
  refine (hprod.div₀ hW.aestronglyMeasurable).congr ?_
  filter_upwards [w_sq_ne_zero_ae] with p hp
  obtain ⟨a, b⟩ := p
  simp only [uncurry_apply_pair', Pi.div_apply]
  rw [mul_div_assoc, div_self hp, mul_one]

/-- `f · L₁₂ f` is a.e. strongly measurable under `CoerciveData` (from `intK`). -/
theorem aesm_f_mul_L12f (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => f z θ * L12f f z)) muzθ := by
  have hK : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Spaces.w p.1 / p.1 * L12f f p.1 * (Spaces.K p.2 * f p.1 p.2)) muzθ := by
    rw [← restrict_prod_eq_muzθ]
    exact hi.intK.aestronglyMeasurable
  have hD : Measurable (fun p : ℝ × ℝ => Spaces.w p.1 / p.1 * Spaces.K p.2) := by
    have h1 : Measurable fun z : ℝ => Spaces.w z / z := by
      unfold Spaces.w; fun_prop
    have h2 : Measurable fun θ : ℝ => Spaces.K θ := by
      unfold Spaces.K; fun_prop
    exact (h1.comp measurable_fst).mul (h2.comp measurable_snd)
  have hz : ∀ᵐ p ∂muzθ, p.1 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p; simp
    rw [hset, muzθ, Measure.prod_prod,
      measure_singleton (μ := volume.restrict Spaces.Iz) (0 : ℝ)]
    simp
  have hDne : ∀ᵐ p ∂muzθ, Spaces.w p.1 / p.1 * Spaces.K p.2 ≠ 0 := by
    have hmem : ∀ᵐ p ∂muzθ, p.1 ∈ Spaces.Iz := by
      rw [← restrict_prod_eq_muzθ]
      exact (ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)).mono fun p hp => hp.1
    filter_upwards [hmem, hz, K_ne_zero_ae] with p hp hne hkp
    have h1 : (1 : ℝ) + p.1 ≠ 0 := by
      have : (0 : ℝ) ≤ p.1 := hp
      linarith
    have hwz : Spaces.w p.1 / p.1 ≠ 0 := by
      rw [Spaces.w]
      exact div_ne_zero (div_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 hne)) hne
    exact mul_ne_zero hwz hkp
  refine (hK.div₀ hD.aestronglyMeasurable).congr ?_
  filter_upwards [hDne] with p hp
  obtain ⟨a, b⟩ := p
  simp only [uncurry_apply_pair', Pi.div_apply, div_eq_mul_inv] at hp ⊢
  have hw : Spaces.w a ≠ 0 := fun h0 => hp (by simp [h0])
  have ha : a ≠ 0 := fun h0 => hp (by simp [h0])
  have hkb : Spaces.K b ≠ 0 := fun h0 => hp (by simp [h0])
  field_simp


/-! ## The pointwise estimate for the `Z4` term -/

/-- The elementary Young/AM-GM inequality `|a b| ≤ 8 a² + b²/32`
(sharp: `8 a² - |a b| + b²/32 = 8(|a| - |b|/16)²`). -/
theorem amgm_8_32 (a b : ℝ) : |a * b| ≤ 8 * a ^ 2 + (1 / 32) * b ^ 2 := by
  have h : 0 ≤ (|a| - |b| / 16) ^ 2 := sq_nonneg _
  have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
  have h2 : |b| ^ 2 = b ^ 2 := sq_abs b
  rw [abs_mul]
  nlinarith [h, h1, h2]

/-- **The pointwise `Z4` bound.**  With `κ(z,θ) = 2 z (1-z) Γ(θ)/(c (1+z)³)`, so that
`Z4 α f z θ = -κ(z,θ) · L₁₂ f z`, one has
`|Z4 · D_z f · Weta| ≤ (1/32) (D_z f)² Weta + 8 κ² (L₁₂ f)² Weta`. -/
theorem Z4_amgm_pt (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Spaces.Iθ) :
    |Z4 α f z θ * Spaces.Dz f z θ * Weta z θ|
      ≤ (1 / 32) * (Spaces.Dz f z θ * Spaces.Dz f z θ * Weta z θ)
        + 8 * ((2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) ^ 2
            * (L12f f z) ^ 2 * Weta z θ) := by
  have hW : 0 ≤ Weta z θ := by
    rw [Weta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hEq : Z4 α f z θ * Spaces.Dz f z θ * Weta z θ
      = -(((2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) * L12f f z)
          * Spaces.Dz f z θ * Weta z θ) := by
    rw [Z4]; ring
  rw [hEq, abs_neg, abs_mul, abs_of_nonneg hW]
  calc |((2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) * L12f f z)
        * Spaces.Dz f z θ| * Weta z θ
      ≤ (8 * ((2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) * L12f f z) ^ 2
          + (1 / 32) * (Spaces.Dz f z θ) ^ 2) * Weta z θ :=
        mul_le_mul_of_nonneg_right (amgm_8_32 _ _) hW
    _ = (1 / 32) * (Spaces.Dz f z θ * Spaces.Dz f z θ * Weta z θ)
        + 8 * ((2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) ^ 2
            * (L12f f z) ^ 2 * Weta z θ) := by ring

/-- **The coefficient identity.**  For `z > 0` and `θ ∈ Iθ`,
`κ² · Weta ≤ 4 (Γ(θ)/c)² sin(2θ)^{-η} / z²`.  (The two sides differ by the factor
`((1-z)/(1+z))² ≤ 1`; both vanish at `z = 0`.) -/
theorem kappa_sq_Weta_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Spaces.Iθ) :
    (2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) ^ 2 * Weta z θ
      ≤ 4 * (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) / z ^ 2 := by
  have hs : 0 ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
    Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hA : (2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) ^ 2 * Weta z θ
      = 4 * (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          * ((1 - z) ^ 2 / (1 + z) ^ 2) / (Spaces.c α) ^ 2 / z ^ 2 := by
    rw [Weta, Spaces.w]
    field_simp
    ring
  rw [hA]
  have hratio : (1 - z) ^ 2 / (1 + z) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hpos : 0 ≤ 4 * (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      / (Spaces.c α) ^ 2 / z ^ 2 := by
    refine div_nonneg (div_nonneg ?_ (by positivity)) (by positivity)
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hs
  calc 4 * (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        * ((1 - z) ^ 2 / (1 + z) ^ 2) / (Spaces.c α) ^ 2 / z ^ 2
      = (4 * (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          / (Spaces.c α) ^ 2 / z ^ 2) * ((1 - z) ^ 2 / (1 + z) ^ 2) := by ring
    _ ≤ (4 * (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
          / (Spaces.c α) ^ 2 / z ^ 2) * 1 := mul_le_mul_of_nonneg_left hratio hpos
    _ = 4 * (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) / z ^ 2 := by
        rw [mul_one, div_pow]
        ring

/-! ## Integrability of the dominating terms -/

/-- `z ↦ (L₁₂ f z / z)²` is integrable on `Iz` (this is `HardyHyp.intA` at `j = 1`). -/
theorem integrableOn_L12f_div_z_sq (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) Spaces.Iz := by
  have h0 := hfH.intA 1 (by norm_num)
  have h1 : IntegrableOn (fun z : ℝ => (L12f f z / z) ^ 2) (Set.Ioi 0) := by
    refine h0.congr_fun ?_ measurableSet_Ioi
    intro z hz
    show L12f f z ^ 2 / z ^ (2 * ((1 : ℕ) : ℝ)) = (L12f f z / z) ^ 2
    rw [div_pow]
    norm_num
  rw [Spaces.Iz]
  have hmeas : volume.restrict (Set.Ici (0 : ℝ)) = volume.restrict (Set.Ioi (0 : ℝ)) :=
    (Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
  change Integrable (fun z : ℝ => (L12f f z / z) ^ 2) (volume.restrict (Set.Ici (0 : ℝ)))
  rw [hmeas]
  exact h1

/-- `θ ↦ (Γ(θ)/c)² sin(2θ)^{-η}` is integrable on `Iθ` (the integral is at most `18900`,
`Gam_div_c_sq_eta_integral_le`). -/
theorem integrableOn_gamDivC_sq_sin (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  have hsinle : ∀ θ ∈ Spaces.Iθ, (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-Spaces.eta) := fun θ hθ =>
    Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hpt : ∀ θ ∈ Spaces.Iθ,
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
    intro θ hθ
    have hb := Gam_div_c_bound hα hα1 hθ
    have hsq : (Spaces.Gam α θ / Spaces.c α) ^ 2 ≤ 100 := by
      rw [← sq_abs (Spaces.Gam α θ / Spaces.c α)]
      nlinarith [abs_nonneg (Spaces.Gam α θ / Spaces.c α)]
    exact mul_le_mul_of_nonneg_right hsq (hsinle θ hθ)
  have hInt2 : IntegrableOn (fun θ : ℝ => 100 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ :=
    ((Work.Spaces.sin_two_rpow (-Spaces.eta) (by rw [Spaces.eta]; norm_num)
      (by rw [Spaces.eta]; norm_num)).1).const_mul 100
  have hmeas : AEStronglyMeasurable (fun θ : ℝ =>
      (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (volume.restrict Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    unfold Spaces.Gam
    fun_prop
  refine Integrable.mono' hInt2 hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hsinle θ hθ))]
  exact hpt θ hθ

/-- **Integrability and the bound for the second dominating term.**  With
`κ(z,θ) = 2 z (1-z) Γ(θ)/(c(1+z)³)`, the function `κ² (L₁₂ f)² Weta` is integrable on the
quadrant and its integral is at most `4 · 18900 · EL12z f`. -/
theorem integrable_kappa_sq_U_sq_Weta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    Integrable (fun p : ℝ × ℝ =>
        (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
          * (L12f f p.1) ^ 2 * Weta p.1 p.2) muzθ
      ∧ ∫ p, (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
          * (L12f f p.1) ^ 2 * Weta p.1 p.2 ∂muzθ ≤ 4 * 18900 * EL12z f := by
  set A : ℝ → ℝ := fun z => (L12f f z / z) ^ 2 with hA
  set B : ℝ → ℝ := fun θ =>
    4 * (Spaces.Gam α θ / Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) with hB
  have hAint : Integrable A (volume.restrict Spaces.Iz) := by
    rw [hA]; exact integrableOn_L12f_div_z_sq f hfH
  have hBnonneg : ∀ θ ∈ Spaces.Iθ, 0 ≤ B θ := by
    intro θ hθ
    simp only [hB]
    refine mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
    exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _
  have hBabs : ∀ θ ∈ Spaces.Iθ, |B θ| = B θ := fun θ hθ => abs_of_nonneg (hBnonneg θ hθ)
  have hBint : Integrable (fun θ => |B θ|) (volume.restrict Spaces.Iθ) := by
    refine ((integrableOn_gamDivC_sq_sin α hα hα1).const_mul 4).abs.congr ?_
    filter_upwards with θ
    simp only [hB, mul_assoc]
  have hG := Work.Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Spaces.Iz) (ν := volume.restrict Spaces.Iθ)
    (G := fun z θ => A z * |B θ|)
    (fun z θ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
    (hAint.aestronglyMeasurable.comp_fst.mul (hBint.aestronglyMeasurable.comp_snd))
    (Filter.Eventually.of_forall fun z => hBint.const_mul (A z))
    ((hAint.mul_const _).congr (Filter.Eventually.of_forall fun z => by
      show A z * (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ))
        = ∫ θ, A z * |B θ| ∂(volume.restrict Spaces.Iθ)
      rw [integral_const_mul]))
  have hmem : ∀ᵐ p ∂muzθ, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
    rw [← restrict_prod_eq_muzθ]
    exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hWnn : ∀ p ∈ Spaces.Iz ×ˢ Spaces.Iθ, 0 ≤ Weta p.1 p.2 := by
    rintro p hp
    rw [Weta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])) _)
  have hpt_le : ∀ᵐ p ∂muzθ,
      (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
          * (L12f f p.1) ^ 2 * Weta p.1 p.2 ≤ A p.1 * |B p.2| := by
    filter_upwards [hmem] with p hp
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with hz | hz
    · have hkey := kappa_sq_Weta_le α hα hα1 hz hp.2
      rw [hBabs p.2 hp.2]
      simp only [hA, hB]
      calc (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2
          = (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * Weta p.1 p.2 * (L12f f p.1) ^ 2 := by ring
        _ ≤ (4 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta)
              / p.1 ^ 2) * (L12f f p.1) ^ 2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
        _ = (L12f f p.1 / p.1) ^ 2 * (4 * (Spaces.Gam α p.2 / Spaces.c α) ^ 2
              * (Real.sin (2 * p.2)) ^ (-Spaces.eta)) := by rw [div_pow]; ring
    · rw [← hz, hA]
      simp only [Weta, Spaces.w, Pi.pow_apply]
      norm_num
  have hU2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (L12f f p.1) ^ 2) muzθ := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => L12f f p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (L12f_continuousOn f hfH).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => L12f f p.1) hcont).pow 2
    refine h.congr ?_
    filter_upwards with p
    simp only [Pi.pow_apply]
  have hmeasT : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
        * (L12f f p.1) ^ 2 * Weta p.1 p.2) muzθ := by
    have hc : Measurable (fun p : ℝ × ℝ =>
        (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
          * Weta p.1 p.2) := by
      apply Measurable.mul
      · have hGam : Measurable fun θ : ℝ => Spaces.Gam α θ := by unfold Spaces.Gam; fun_prop
        have h1 : Measurable (fun p : ℝ × ℝ =>
            2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) := by fun_prop
        exact h1.pow_const 2
      · show Measurable (fun p : ℝ × ℝ =>
          Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
        apply Measurable.mul
        · have hw : Measurable fun z : ℝ => Spaces.w z ^ 2 := by unfold Spaces.w; fun_prop
          exact hw.comp measurable_fst
        · exact (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
    refine (hc.aestronglyMeasurable.mul hU2).congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply]
    ring
  have hint : Integrable (fun p : ℝ × ℝ =>
      (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
        * (L12f f p.1) ^ 2 * Weta p.1 p.2) muzθ := by
    refine Integrable.mono' hG.1 hmeasT ?_
    filter_upwards [hpt_le, hmem] with p hp hpmem
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa only [uncurry_apply_pair'] using hp
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hWnn p hpmem)
  refine ⟨hint, ?_⟩
  have hmono := integral_mono_ae hint hG.1 hpt_le
  have hval : ∫ p, A p.1 * |B p.2| ∂muzθ
      = (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ)) * ∫ z, A z ∂(volume.restrict Spaces.Iz) := by
    have h1 : ∫ p, A p.1 * |B p.2| ∂muzθ
        = ∫ p, (fun z θ => A z * |B θ|) p.1 p.2 ∂muzθ := rfl
    rw [h1, muzθ, hG.2]
    rw [show (∫ z, ∫ θ, A z * |B θ| ∂(volume.restrict Spaces.Iθ) ∂(volume.restrict Spaces.Iz))
        = ∫ z, A z * (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ)) ∂(volume.restrict Spaces.Iz) from
      integral_congr_ae (Filter.Eventually.of_forall fun z =>
        integral_const_mul (A z) (fun θ => |B θ|))]
    rw [integral_mul_const, mul_comm]
  have hAval : (∫ z, A z ∂(volume.restrict Spaces.Iz)) = EL12z f := by
    rw [hA]; rfl
  have hBval : (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ)) ≤ 4 * 18900 := by
    have h1 : (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ))
        = 4 * ∫ θ in Spaces.Iθ, (Spaces.Gam α θ / Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hBabs θ hθ]
      simp only [hB, mul_assoc]
    rw [h1]
    have hle := Gam_div_c_sq_eta_integral_le α hα hα1
    linarith
  have hELnn : 0 ≤ EL12z f := by
    rw [EL12z, L2Sqz]
    exact integral_nonneg fun z => sq_nonneg _
  have hBnn : 0 ≤ ∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ) :=
    integral_nonneg fun θ => abs_nonneg _
  have hmono' : ∫ p, Function.uncurry (fun z θ => A z * |B θ|) p ∂muzθ
      = (∫ θ, |B θ| ∂(volume.restrict Spaces.Iθ)) * ∫ z, A z ∂(volume.restrict Spaces.Iz) := by
    rw [show (∫ p, Function.uncurry (fun z θ => A z * |B θ|) p ∂muzθ)
      = ∫ p, A p.1 * |B p.2| ∂muzθ from rfl]
    exact hval
  rw [hmono', hAval] at hmono
  nlinarith [hmono, hBval, hELnn, hBnn]


/-! ## Almost everywhere strong measurability of the target integrand -/

/-- **The target integrand is a.e. strongly measurable.**  This is where
`ae_pz_eq_zero_of_aesm_sq` is used: a.e. where `f` vanishes also `D_z f` vanishes, so
`Z4·D_z f·Weta = -κ·Weta·(f·D_z f)·(f·L₁₂f)·(f²)^{-1}` a.e., and the right-hand side
involves only functions known to be a.e. strongly measurable from the quadratic
integrability hypotheses of `CoerciveData`. -/
theorem aesm_Z4 (α : ℝ) (f : ℝ → ℝ → ℝ) (hi : CoerciveData α f) :
    AEStronglyMeasurable
      (Function.uncurry (fun z θ => Z4 α f z θ * Spaces.Dz f z θ * Weta z θ)) muzθ := by
  have hf2 := aesm_f_sq α f hi
  have hfV := aesm_f_mul_Dz α f hi
  have hfU := aesm_f_mul_L12f α f hi
  have hDz2 := aesm_Dz_sq α f hi
  -- the reciprocal of `f²`
  have hinv : AEStronglyMeasurable (fun p : ℝ × ℝ => ((f p.1 p.2) ^ 2)⁻¹) muzθ := by
    have hrep : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ((hf2.mk (Function.uncurry (fun z θ => f z θ ^ 2))) p)⁻¹) muzθ :=
      hf2.stronglyMeasurable_mk.measurable.inv.aestronglyMeasurable
    refine hrep.congr ?_
    filter_upwards [hf2.ae_eq_mk] with p hp
    obtain ⟨a, b⟩ := p
    simp only [Function.uncurry_apply_pair] at hp ⊢
    rw [← hp]
  -- the a.e. pointwise identity
  have hred : (fun p : ℝ × ℝ => Z4 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
      =ᵐ[muzθ] fun p =>
        -(2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3))
          * Weta p.1 p.2
          * ((f p.1 p.2 * Spaces.Dz f p.1 p.2) * (f p.1 p.2 * L12f f p.1)
              * ((f p.1 p.2) ^ 2)⁻¹) := by
    filter_upwards [ae_pz_eq_zero_of_aesm_sq f hf2 hDz2] with p hz
    by_cases hf : f p.1 p.2 = 0
    · have hpz : Spaces.pz f p.1 p.2 = 0 := hz hf
      have hDz0 : Spaces.Dz f p.1 p.2 = 0 := by rw [Spaces.Dz, hpz, mul_zero]
      rw [hf, hDz0]
      simp [Z4]
    · rw [Z4]
      have h1 : (f p.1 p.2 * Spaces.Dz f p.1 p.2) * (f p.1 p.2 * L12f f p.1)
          * ((f p.1 p.2) ^ 2)⁻¹ = Spaces.Dz f p.1 p.2 * L12f f p.1 := by
        field_simp
        try ring
      rw [h1]
      ring
  have hredmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      -(2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3))
        * Weta p.1 p.2
        * ((f p.1 p.2 * Spaces.Dz f p.1 p.2) * (f p.1 p.2 * L12f f p.1)
            * ((f p.1 p.2) ^ 2)⁻¹)) muzθ := by
    have hc : Measurable (fun p : ℝ × ℝ =>
        -(2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3))
          * Weta p.1 p.2) := by
      apply Measurable.mul
      · have hGam : Measurable fun θ : ℝ => Spaces.Gam α θ := by unfold Spaces.Gam; fun_prop
        have h1 : Measurable (fun p : ℝ × ℝ =>
            -(2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3))) := by
          fun_prop
        exact h1
      · show Measurable (fun p : ℝ × ℝ =>
          Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Spaces.eta))
        apply Measurable.mul
        · have hw : Measurable fun z : ℝ => Spaces.w z ^ 2 := by unfold Spaces.w; fun_prop
          exact hw.comp measurable_fst
        · exact (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
    exact hc.aestronglyMeasurable.mul ((hfV.mul hfU).mul hinv)
  exact hredmeas.congr hred.symm

/-! ## The main estimate -/

theorem bound_Z4 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hfH : HardyHyp f) (hi : CoerciveData α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z4 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)
    ∧ wip Weta (Z4 α f) (Spaces.Dz f) ≥ -((1 / 32) * EDz f + 10 ^ 7 * Ef f) := by
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (f_sq_w_sq_integrable α f hi).congr_fun (fun p hp => by ring)
      (measurableSet_Ici.prod measurableSet_Icc)
  obtain ⟨hIntK, hIntKbd⟩ := integrable_kappa_sq_U_sq_Weta α hα hα1 f hfH
  have hIntDz : Integrable (fun p : ℝ × ℝ =>
      Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) muzθ := by
    rw [← restrict_prod_eq_muzθ]
    refine hi.intDz.congr (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨a, b⟩ := p
    simp only [Function.uncurry_apply_pair, Weta]
    ring
  have hmem : ∀ᵐ p ∂muzθ, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
    rw [← restrict_prod_eq_muzθ]
    exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  have hdom : ∀ᵐ p ∂muzθ, ‖Z4 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2‖
      ≤ (1 / 32) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        + 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2) := by
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs]
    exact Z4_amgm_pt α f (show (0 : ℝ) ≤ p.1 from hp.1) hp.2
  have hdomint : Integrable (fun p : ℝ × ℝ =>
      (1 / 32) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        + 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2)) muzθ :=
    (hIntDz.const_mul (1 / 32)).add (hIntK.const_mul 8)
  have hInt : Integrable (fun p : ℝ × ℝ =>
      Z4 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2) muzθ :=
    hdomint.mono' (aesm_Z4 α f hi) hdom
  have hIntOn : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Z4 α f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [IntegrableOn, restrict_prod_eq_muzθ]
    exact hInt
  refine ⟨hIntOn, ?_⟩
  rw [wip_eq_integral_prod Weta (Z4 α f) (Spaces.Dz f) hIntOn]
  -- the pointwise lower bound for the integrand
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (-(1 / 32)) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        - 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2)) muzθ :=
    (hIntDz.const_mul (-(1 / 32))).sub (hIntK.const_mul 8)
  have hlow : ∀ᵐ p ∂muzθ,
      (-(1 / 32)) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        - 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2)
        ≤ Z4 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 := by
    filter_upwards [hdom] with p hp
    have h := neg_le_of_abs_le hp
    rw [show (-(1 / 32)) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        - 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2)
        = -(((1 / 32) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2))
          + 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
              * (L12f f p.1) ^ 2 * Weta p.1 p.2)) from by ring]
    exact h
  have hmono := integral_mono_ae hmaj hInt hlow
  have hI₁eq : (∫ p, Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂muzθ)
      = EDz f := by
    have h := wip_eq_integral_prod (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz f) (Spaces.Dz f) ?_
    · rw [EDz_eq_wip f]
      exact h.symm
    · rw [IntegrableOn, restrict_prod_eq_muzθ]
      refine hIntDz.congr (Filter.Eventually.of_forall fun p => ?_)
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry_apply_pair, Weta]
      try ring
  have hval : (∫ p, (-(1 / 32)) * (Spaces.Dz f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2)
        - 8 * ((2 * p.1 * (1 - p.1) * Spaces.Gam α p.2 / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2
            * (L12f f p.1) ^ 2 * Weta p.1 p.2) ∂muzθ)
      = -((1 / 32) * EDz f
          + 8 * (∫ p, (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2
              / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2 * (L12f f p.1) ^ 2 * Weta p.1 p.2 ∂muzθ)) := by
    rw [integral_sub (hIntDz.const_mul (-(1 / 32))) (hIntK.const_mul 8),
      integral_const_mul, integral_const_mul, hI₁eq]
    ring
  have hmono' : -((1 / 32) * EDz f
        + 8 * (∫ p, (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2
            / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2 * (L12f f p.1) ^ 2 * Weta p.1 p.2 ∂muzθ))
      ≤ ∫ p, Z4 α f p.1 p.2 * Spaces.Dz f p.1 p.2 * Weta p.1 p.2 ∂muzθ := by
    rw [← hval]
    exact hmono
  have hEL : EL12z f ≤ 16 * Ef f := EL12z_le f hfH hfw
  have hEf0 : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hIJ : 8 * (∫ p, (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2
        / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2 * (L12f f p.1) ^ 2 * Weta p.1 p.2 ∂muzθ)
      ≤ 10 ^ 7 * Ef f := by
    have h1 : 8 * (∫ p, (2 * p.1 * (1 - p.1) * Spaces.Gam α p.2
        / (Spaces.c α * (1 + p.1) ^ 3)) ^ 2 * (L12f f p.1) ^ 2 * Weta p.1 p.2 ∂muzθ)
        ≤ 8 * (4 * 18900 * EL12z f) := by linarith [hIntKbd]
    have h2 : 8 * (4 * 18900 * EL12z f) ≤ 10 ^ 7 * Ef f := by linarith [hEL, hEf0]
    linarith
  simp only [muzθ] at hmono' hIJ ⊢
  linarith [hmono', hIJ]

end

end Work.Coercivity
