import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.integrable_PsiC`

The mean-free localised state

  `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`

of FS `eq:Q1Qslide` is `L¹` as soon as `ψ` is smooth and compactly supported.

The proof is elementary and uses no Fourier analysis.  Both ingredients are *box-localised
integrals of `ψ` shifted by `x`*,

* `boxFTfun ℓ p ψ x = ∫_{z ∈ acube ℓ} e^{−i⟪p,z⟫} ψ(x+z) dz`,
* `boxMeanR ℓ ψ x = ℓ⁻³ ∫_{z ∈ acube ℓ} ψ(x+z) dz`,

and each of them is

* strongly measurable in `x` (Fubini: the integrand on `ℝ³ × ℝ³` is strongly measurable and
  `x ↦ ∫ z, F (x,z)` of a strongly measurable two-variable function is strongly measurable);
* supported in the compact set `(fun q : ℝ³ × ℝ³ => q.1 - q.2) '' (tsupport ψ ×ˢ acube ℓ)`
  for `ℓ > 0` (a point outside this set has `ψ (x+z) = 0` for every `z ∈ acube ℓ`);
* bounded by `B · C · (volume (acube ℓ)).toReal`, where `B` bounds the weight and `C` bounds
  `ψ` (`norm_setIntegral_le_of_norm_le_const`).

A strongly measurable function with compact support and a uniform bound is integrable, which
gives the two terms; `PsiC` is their difference.  For `ℓ ≤ 0` the cube `acube ℓ` is contained
in `acube 0` and therefore has measure zero, and both terms of `PsiC` vanish identically.

Since the two terms are the same integral with a different weight `c`, the general
shift-integral lemmas are stated for an arbitrary strongly measurable weight `c` bounded by
`B ≥ 0` and an arbitrary compactly supported `g`, and are applied with `c z = e^{−i⟪p,z⟫}`
respectively `c = 1`.

The Fubini step is why `ℝ³ = EuclideanSpace ℝ (Fin 3)` is used consistently: the shift integral
is `∫ z, c z · g (x+z) ∂(volume.restrict (acube ℓ))`, which is literally the `z`-integral of the
strongly measurable function `(x,z) ↦ c z · g (x+z)`.

Note (for the requester): the skeleton module `Momentum.momForm_u_integral` also *declares* an
`integrable_PsiC` (with a `sorry`); a module importing both would see a duplicate declaration,
so import this one instead of that skeleton once the skeleton's copy is removed.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. A bounded, compactly supported, measurable function is integrable -/

/-- A strongly measurable function with compact support and a uniform bound is integrable.
(Both `tsupport f` and — via `ℓ > 0` — every cube have finite measure, so the function is
integrable on its support and vanishes off it.) -/
lemma integrable_of_bound_hasCompactSupport {f : ℝ³ → ℂ} (hf : StronglyMeasurable f)
    (hfs : HasCompactSupport f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f := by
  have hK : volume (tsupport f) < ⊤ := hfs.measure_lt_top
  have hOn : IntegrableOn f (tsupport f) volume :=
    IntegrableOn.of_bound hK (hf.aestronglyMeasurable.restrict) C (Filter.Eventually.of_forall hb)
  exact hOn.integrable_of_forall_notMem_eq_zero fun x hx => image_eq_zero_of_notMem_tsupport hx

/-! ## 2. The box-localised shift integral `x ↦ ∫_{z ∈ acube ℓ} c z · g (x+z)` -/

/-- **Strong measurability.**  The two-variable integrand `(x,z) ↦ c z · g (x+z)` is strongly
measurable and `x ↦ ∫ z, c z · g (x+z)` is an integral of it, so it is strongly measurable
(`StronglyMeasurable.integral_prod_right'` with the measure `volume.restrict (acube ℓ)`, which
is exactly the set integral over `acube ℓ`). -/
lemma stronglyMeasurable_setIntegral_comp_add (ℓ : ℝ) (c g : ℝ³ → ℂ)
    (hc : StronglyMeasurable c) (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun x : ℝ³ => ∫ z in acube ℓ, c z * g (x + z)) := by
  have hmul : StronglyMeasurable (fun q : ℝ³ × ℝ³ => c q.2 * g (q.1 + q.2)) :=
    (hc.comp_measurable measurable_snd).mul (hg.comp_measurable (measurable_fst.add measurable_snd))
  exact StronglyMeasurable.integral_prod_right' (ν := volume.restrict (acube ℓ)) hmul

/-- **Compact support.**  For `ℓ > 0` the shift integral is supported in the compact set
`(fun q : ℝ³ × ℝ³ => q.1 - q.2) '' (tsupport g ×ˢ acube ℓ)`: a point `x` outside it has
`x + z ∉ tsupport g` for every `z ∈ acube ℓ`, hence the integrand vanishes on `acube ℓ`. -/
lemma hasCompactSupport_setIntegral_comp_add {ℓ : ℝ} (hℓ : 0 < ℓ) (c g : ℝ³ → ℂ)
    (hg : HasCompactSupport g) :
    HasCompactSupport (fun x : ℝ³ => ∫ z in acube ℓ, c z * g (x + z)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun q : ℝ³ × ℝ³ => q.1 - q.2) '' (tsupport g ×ˢ acube ℓ)) ?_ ?_
  · exact ((show IsCompact (tsupport g) from hg).prod (acube_compact hℓ)).image continuous_sub
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    have hzero : ∀ z ∈ acube ℓ, c z * g (x + z) = 0 := by
      intro z hz
      have hgz : g (x + z) = 0 := by
        by_contra hne
        exact hmem ⟨(x + z, z), ⟨subset_tsupport g (Function.mem_support.mpr hne), hz⟩, by simp⟩
      rw [hgz, mul_zero]
    rw [setIntegral_congr_fun (acube_measurable ℓ) hzero]
    simp

/-- **Uniform bound.**  If `‖c‖ ≤ B` and `‖g‖ ≤ C` with `B ≥ 0`, then the shift integral is
bounded by `B · C · |acube ℓ|`; the volume is finite for `ℓ > 0`. -/
lemma norm_setIntegral_comp_add_le {ℓ : ℝ} (hℓ : 0 < ℓ) (c g : ℝ³ → ℂ) {B C : ℝ}
    (hB : 0 ≤ B) (hcb : ∀ z, ‖c z‖ ≤ B) (hgb : ∀ y, ‖g y‖ ≤ C) (x : ℝ³) :
    ‖∫ z in acube ℓ, c z * g (x + z)‖ ≤ B * C * (volume (acube ℓ)).toReal := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := acube ℓ)
    (f := fun z => c z * g (x + z)) (C := B * C) (acube_lt_top ℓ hℓ.le) (fun z hz => by
      rw [norm_mul]
      exact mul_le_mul (hcb z) (hgb (x + z)) (norm_nonneg _) hB)
  simpa [Measure.real] using h

/-- **Integrability of the box-localised shift integral** (the core of the proof). -/
lemma integrable_setIntegral_comp_add {ℓ : ℝ} (hℓ : 0 < ℓ) (c g : ℝ³ → ℂ)
    (hc : StronglyMeasurable c) (hg : StronglyMeasurable g) (hgs : HasCompactSupport g)
    {B C : ℝ} (hB : 0 ≤ B) (hcb : ∀ z, ‖c z‖ ≤ B) (hgb : ∀ y, ‖g y‖ ≤ C) :
    Integrable (fun x : ℝ³ => ∫ z in acube ℓ, c z * g (x + z)) :=
  integrable_of_bound_hasCompactSupport
    (stronglyMeasurable_setIntegral_comp_add ℓ c g hc hg)
    (hasCompactSupport_setIntegral_comp_add hℓ c g hgs)
    (fun x => norm_setIntegral_comp_add_le hℓ c g hB hcb hgb x)

/-! ## 3. A smooth compactly supported `ψ` is bounded -/

/-- A continuous function with compact support is bounded. -/
lemma exists_norm_le_of_contDiff_hasCompactSupport {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖ψ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (show IsCompact (tsupport ψ) from hcs).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport ψ
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

/-! ## 4. The two terms of `PsiC` and the theorem -/

/-- `boxFTfun ℓ p ψ` is integrable for `ℓ > 0`: the weight `z ↦ e^{−i⟪p,z⟫}` has modulus `1`
and `z ↦ (ψ z : ℂ)` is compactly supported and bounded. -/
lemma integrable_boxFTfun {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (boxFTfun ℓ p ψ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_contDiff_hasCompactSupport hψ hcs
  have hcsC : HasCompactSupport (fun y : ℝ³ => (ψ y : ℂ)) := by
    have h := hcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
    simpa [Function.comp_def] using h
  have hC' : ∀ y : ℝ³, ‖((ψ y : ℝ) : ℂ)‖ ≤ C := fun y => by simpa using hC y
  have hc : StronglyMeasurable (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) :=
    (Complex.continuous_exp.comp (by fun_prop)).stronglyMeasurable
  have hg : StronglyMeasurable (fun y : ℝ³ => (ψ y : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ.continuous).stronglyMeasurable
  refine integrable_setIntegral_comp_add hℓ (fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
    (fun y => (ψ y : ℂ)) hc hg hcsC (B := 1) (C := C) zero_le_one ?_ hC'
  intro z
  rw [Complex.norm_exp]
  simp

/-- The complexification of `boxMeanR ℓ ψ` is integrable for `ℓ > 0`.  The complex integral
`∫_{z ∈ acube ℓ} (ψ (x+z) : ℂ)` is the complexification of the real one (`integral_ofReal`). -/
lemma integrable_boxMeanR {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_contDiff_hasCompactSupport hψ hcs
  have hcsC : HasCompactSupport (fun y : ℝ³ => (ψ y : ℂ)) := by
    have h := hcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
    simpa [Function.comp_def] using h
  have hC' : ∀ y : ℝ³, ‖((ψ y : ℝ) : ℂ)‖ ≤ C := fun y => by simpa using hC y
  have hg : StronglyMeasurable (fun y : ℝ³ => (ψ y : ℂ)) :=
    (Complex.continuous_ofReal.comp hψ.continuous).stronglyMeasurable
  have hsh : Integrable (fun x : ℝ³ => ∫ z in acube ℓ, ((ψ (x + z) : ℝ) : ℂ)) := by
    have h := integrable_setIntegral_comp_add hℓ (fun _ => (1 : ℂ)) (fun y => (ψ y : ℂ))
      stronglyMeasurable_const hg hcsC (B := 1) (C := C) zero_le_one (fun _ => by simp) hC'
    simpa only [one_mul] using h
  have h := hsh.const_mul ((ℓ ^ 3)⁻¹ : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hkey : (∫ z in acube ℓ, ((ψ (x + z) : ℝ) : ℂ)) = ((∫ z in acube ℓ, ψ (x + z) : ℝ) : ℂ) := by
    norm_cast
  simp only [hkey, boxMeanR, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem integrable_PsiC (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : MeasureTheory.Integrable (Work.BoseKinLoc.Momentum.PsiC ℓ p ψ) := by
  by_cases hℓ : ℓ ≤ 0
  · -- for `ℓ ≤ 0` the cube is contained in `acube 0`, hence null, and `PsiC` vanishes
    have hsub : acube ℓ ⊆ acube 0 := by
      intro y hy m
      have h1 : y m ≤ ℓ / 2 := (hy m).2
      have h2 : -ℓ / 2 ≤ y m := (hy m).1
      have h3 : y m = 0 := by linarith
      simp [h3]
    have hzero : volume (acube ℓ) = 0 := by
      have h : volume (acube 0) = 0 := by
        rw [acube_volume 0 le_rfl]
        simp
      exact measure_mono_null hsub h
    refine Integrable.congr (integrable_zero ℝ³ ℂ volume) ?_
    filter_upwards with x
    simp only [Pi.zero_apply, PsiC, boxFTfun, boxMeanR]
    rw [setIntegral_measure_zero _ hzero, setIntegral_measure_zero _ hzero]
    simp
  · -- for `ℓ > 0`: `PsiC` is the difference of two integrable functions
    have hpos : 0 < ℓ := not_le.mp hℓ
    have h1 := integrable_boxFTfun hpos p ψ hψ hcs
    have h2 := integrable_boxMeanR hpos ψ hψ hcs
    refine (h1.sub (h2.mul_const (Work.OneBodyKin.boxHat ℓ p : ℂ))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [PsiC, Pi.sub_apply]

end Work.BoseKinLoc.Momentum
