import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ChallengeDeps
import Submission.KernelIds
import Submission.RadialEven
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B6 — potential-energy localization (lem:LocPotential)

FS `final_v2.tex` Lemma `lem:LocPotential` (lines ~975--985): with the
cell-`u` translates `w_u(x,y) := χ_u(x)·W(x−y)·χ_u(y)` (`χ_u(x) :=
χ((x−ℓu)/ℓ)`, here `chiU ℓ u x`) and `w_{1,u}` (same with `W₁ := g/(χ⋆χ)`),
the localizations average back to the original kernels:

    ∫_{ℝ³} w_u(x,y) du  = v(x−y)          (per pair)
    ∫_{ℝ³} ∫_{ℝ³} w_{1,u}(xᵢ,y) dy du = ∫_y g(xᵢ−y) dy   (per particle)

so that `Σ_{i<j} v(xᵢ−xⱼ) − μΣᵢ ∫g(xᵢ−y)dy` equals the `u`-average of the
localized potential `Σ_{i<j} w_u(xᵢ,xⱼ) − μΣᵢ∫_y w_{1,u}(xᵢ,y)dy` (the corpus
statement is per-term; the summed form follows by finite `Finset` sums).

## Content

1. `locPotential_pair` — `∫_u χUℓu x·Wℓv(x−y)·χUℓu y du = v(x−y)`
   pointwise, where `Wℓh x := h x / convScale ℓ x` (`wScaled`).  Hypotheses:
   `0 < ℓ`, `v` vanishes outside `ball 0 R` (`R ≤ ‖x‖ → v x = 0`), the
   convolution is `≥ 1/2` on `ball 0 r₀` and `R ≤ ℓ·r₀` (so that on the
   support of `v`, `convScale ℓ (x−y) ≥ 1/2 ≠ 0`).  Proof: pull the
   `u`-independent factor `wScaled ℓ v (x−y)` out of the `u`-integral
   (`KernelIds.chiU_chiU_integral`: `∫_u χUx·χUy du = convScale ℓ (x−y)`),
   then show `(v(t)/C(t))·C(t) = v(t)` for all `t` by case analysis
   (`C(t) ≠ 0`: field law; `C(t) = 0`: then `‖t‖ ≥ R` (contrapositive of
   the regime conditions), so `v t = 0` and `(0/0)·0 = 0`).

2. `locPotential_onebody` — `∫_u ∫_y χUℓu x·Wℓg(x−y)·χUℓu y dy du =
   ∫_y g(x−y) dy` for `g ∈ L¹` vanishing outside `ball 0 R` (same regime).
   Proof: Fubini; integrate `u` first (`chiU_chiU_integral`), cancelling
   `C(t)·(g(t)/C(t)) = g(t)` pointwise as in 1; then `∫_y g(x−y) dy = ∫g`
   (translation).

3. `locPotential_pair_sum`, `locPotential_onebody_sum` — the finite-sum
   (`i < j` pairs / all `i`) versions used in the localization lemma.

## Notes for the child
* Vector scaling is `(ℓ⁻¹)•x` (no vector division).  The volume factor of
  the `u ↦ w` substitution is absorbed by `chiU_chiU_integral` — no further
  change of variables is needed.
* All integrands are continuous (products of `χ`, `v`, `g`) on compact
  supports / `L¹`-integrable; state and use `MeasureTheory.Integrable`
  hypotheses on `g` (`hg`) only where the integral over `y` is taken.
* χ boundedness: `KernelIds.chi_le_sqrt_inv` / `KernelIds.abs_chiScale_le`
  (χ is bounded but not necessarily by `1`).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The one-body localization kernel of FS (`w_{1,u}(x,y)`): `χ_u(x)·
W₁(x−y)·χ_u(y)` with `W₁ := g/(χ⋆χ(·/ℓ))`.  (Two-body: same with `h := v`,
`w_u(x,y)`.) -/
noncomputable def wLoc (ℓ : ℝ) (h : ℝ³ → ℝ) (u : ℝ³) (x : ℝ³) (y : ℝ³) : ℝ :=
  chiU ℓ u x * wScaled ℓ h (x - y) * chiU ℓ u y

-- ======================================================================
-- helpers for locPotential_onebody
-- ======================================================================

/-- `χ_u(x) = χ(u − (ℓ⁻¹)•x)` (evenness of `χ`). -/
lemma chiU_eq_chi_sub (ℓ : ℝ) (u x : ℝ³) : chiU ℓ u x = chi (u - (ℓ⁻¹) • x) := by
  dsimp [chiU]
  calc
    chi ((ℓ⁻¹) • x - u) = chi (-(u - (ℓ⁻¹) • x)) := by congr 1; abel
    _ = chi (u - (ℓ⁻¹) • x) := chi_even (u - (ℓ⁻¹) • x)

/-- `u ↦ χ_u(x)` is continuous. -/
lemma chiU_continuous_u (ℓ : ℝ) (x : ℝ³) : Continuous (fun u : ℝ³ => chiU ℓ u x) := by
  rw [show (fun u : ℝ³ => chiU ℓ u x) = fun u : ℝ³ => chi (u - (ℓ⁻¹) • x) by
    funext u; rw [chiU_eq_chi_sub]]
  exact chi_continuous.comp (continuous_id.sub continuous_const)

/-- `u ↦ χ_u(x)` has compact support. -/
lemma chiU_hasCompactSupport_u (x : ℝ³) (ℓ : ℝ) :
    HasCompactSupport (fun u : ℝ³ => chiU ℓ u x) := by
  rw [show (fun u : ℝ³ => chiU ℓ u x) = fun u : ℝ³ => chi (u - (ℓ⁻¹) • x) by
    funext u; rw [chiU_eq_chi_sub]]
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.addRight (-((ℓ⁻¹) • x))
  have hφ : (fun u : ℝ³ => chi (u - (ℓ⁻¹) • x)) = chi ∘ ⇑φ := by
    funext u
    apply congrArg chi
    dsimp [φ]
    abel
  rw [hφ]
  exact chi_hasCompactSupport.comp_homeomorph φ

/-- `u ↦ χ_u(x)` is integrable over `u`. -/
lemma chiU_integrable_u (x : ℝ³) (ℓ : ℝ) :
    Integrable (fun u : ℝ³ => chiU ℓ u x) :=
  Continuous.integrable_of_hasCompactSupport (chiU_continuous_u ℓ x) (chiU_hasCompactSupport_u x ℓ)

/-- `y ↦ c − y` preserves the Lebesgue measure on `ℝ³`. -/
lemma measurePreserving_sub_left (c : ℝ³) :
    MeasurePreserving (fun y : ℝ³ => c - y) volume volume := by
  have hneg : MeasurePreserving (fun y : ℝ³ => -y) volume volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ³)
  have hadd : MeasurePreserving (fun z : ℝ³ => c + z) volume volume :=
    measurePreserving_add_left (volume : Measure ℝ³) c
  have hfun : (fun y : ℝ³ => c - y) = (fun z : ℝ³ => c + z) ∘ (fun y : ℝ³ => -y) := by
    funext y; rfl
  have h := hadd.comp hneg
  rwa [← hfun] at h

/-- Pointwise bound `|χ| ≤ (∫χ²)⁻¹ᐟ²`. -/
lemma abs_chi_le (z : ℝ³) : |chi z| ≤ (Real.sqrt chiNormSq)⁻¹ := by
  rw [abs_of_nonneg (chi_nonneg z)]
  exact chi_le_sqrt_inv z

/-- Pointwise bound `|wScaled ℓ h z| ≤ 2·|h z|` under the regime conditions. -/
lemma abs_wScaled_le {h : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hhsupp : ∀ x : ℝ³, R ≤ ‖x‖ → h x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (z : ℝ³) :
    |wScaled ℓ h z| ≤ 2 * |h z| := by
  have hk := abs_kRat_le (h := h) hℓ hhsupp hRℓ hC z
  simpa [wScaled, kRat] using hk

/-- For fixed `x`, the `(u,y) ↦ wLoc ℓ g u x y` kernel is integrable on
`ℝ³ × ℝ³`: dominated by `|χ_u(x)| · (2S·|g(x−y)|)` (the `u`-factor has
compact support; `g` is `L¹`). -/
lemma locPotential_integrable {g : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : ℝ³) :
    Integrable (fun p : ℝ³ × ℝ³ => wLoc ℓ g p.1 x p.2) (volume.prod volume) := by
  let μ : Measure ℝ³ := volume
  let S : ℝ := (Real.sqrt chiNormSq)⁻¹
  -- measurability pieces
  have hA : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 x) (μ.prod μ) := by
    have hc : Continuous (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 x) :=
      (chiU_continuous_u ℓ x).comp continuous_fst
    simpa [μ] using hc.aestronglyMeasurable
  have hC3 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 p.2) (μ.prod μ) := by
    have hc : Continuous (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 p.2) := (chiU_contDiff ℓ).continuous
    simpa [μ] using hc.aestronglyMeasurable
  have hgT : AEStronglyMeasurable (fun v : ℝ³ => g (x - v)) volume := by
    have hq : Measure.QuasiMeasurePreserving (fun v : ℝ³ => x - v) volume volume :=
      (measurePreserving_sub_left x).quasiMeasurePreserving
    simpa [Function.comp_def] using hg.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have hgT2 : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => g (x - p.2)) (μ.prod μ) := by
    have h := AEStronglyMeasurable.comp_snd (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³)) hgT
    simpa [μ] using h
  have hinvM : Measurable (fun p : ℝ³ × ℝ³ => (convScale ℓ (x - p.2))⁻¹) := by
    have hc : Continuous (fun p : ℝ³ × ℝ³ => convScale ℓ (x - p.2)) :=
      (convScale_continuous ℓ).comp (continuous_const.sub continuous_snd)
    have hinv : Measurable fun t : ℝ => t⁻¹ := by fun_prop
    exact hinv.comp hc.measurable
  have hB : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => wScaled ℓ g (x - p.2)) (μ.prod μ) := by
    have hEq : (fun p : ℝ³ × ℝ³ => wScaled ℓ g (x - p.2))
             = fun p : ℝ³ × ℝ³ => g (x - p.2) * (convScale ℓ (x - p.2))⁻¹ := by
      funext p
      dsimp [wScaled]
      rw [div_eq_mul_inv]
    rw [hEq]
    exact hgT2.mul hinvM.aestronglyMeasurable
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => wLoc ℓ g p.1 x p.2) (μ.prod μ) := by
    have hprod1 : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 x * wScaled ℓ g (x - p.2)) (μ.prod μ) :=
      hA.mul hB
    have hF : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => chiU ℓ p.1 x * wScaled ℓ g (x - p.2) * chiU ℓ p.1 p.2) (μ.prod μ) :=
      hprod1.mul hC3
    simpa [wLoc] using hF
  -- integrability of the dominating product
  have hf : Integrable (fun u : ℝ³ => |chiU ℓ u x|) μ := by
    simpa [μ] using (chiU_integrable_u x ℓ).abs
  have hgsub : Integrable (fun y : ℝ³ => |g (x - y)|) volume := by
    have hmp : MeasurePreserving (fun y : ℝ³ => x - y) volume volume := measurePreserving_sub_left x
    have hiff := MeasurePreserving.integrable_comp (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³)) hmp (g := fun v : ℝ³ => |g v|) hg.abs.aestronglyMeasurable
    have hfwd : Integrable ((fun v : ℝ³ => |g v|) ∘ fun y : ℝ³ => x - y) volume := hiff.mpr hg.abs
    simpa [Function.comp_def] using hfwd
  have hk : Integrable (fun y : ℝ³ => (2 * S) * |g (x - y)|) volume := by
    simpa [S] using hgsub.const_mul (2 * S)
  have hdom : Integrable
      (fun p : ℝ³ × ℝ³ => |chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|)) (μ.prod μ) := by
    have h := hf.mul_prod hk
    simpa [μ] using h
  -- pointwise domination
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact inv_nonneg.mpr (le_of_lt (Real.sqrt_pos.mpr chiNormSq_pos))
  have hbnd : ∀ p : ℝ³ × ℝ³,
      |wLoc ℓ g p.1 x p.2| ≤ |chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|) := by
    intro p
    let u := p.1
    let y := p.2
    have hw : |wScaled ℓ g (x - y)| ≤ 2 * |g (x - y)| := abs_wScaled_le (h := g) hℓ hgsupp hRℓ hC (x - y)
    have hchi2 : |chiU ℓ u y| ≤ S := by
      dsimp [chiU]
      exact abs_chi_le ((ℓ⁻¹) • y - u)
    calc
      |wLoc ℓ g u x y| = |chiU ℓ u x * wScaled ℓ g (x - y) * chiU ℓ u y| := by rfl
      _ = |chiU ℓ u x| * |wScaled ℓ g (x - y)| * |chiU ℓ u y| := by simp [abs_mul]
      _ ≤ |chiU ℓ u x| * (2 * |g (x - y)|) * |chiU ℓ u y| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (abs_nonneg _)
      _ ≤ |chiU ℓ u x| * (2 * |g (x - y)|) * S := by
        have hA : 0 ≤ |chiU ℓ u x| * (2 * |g (x - y)|) := by
          exact mul_nonneg (abs_nonneg (chiU ℓ u x)) (mul_nonneg (by norm_num) (abs_nonneg (g (x - y))))
        exact mul_le_mul_of_nonneg_left hchi2 hA
      _ = |chiU ℓ u x| * ((2 * S) * |g (x - y)|) := by ring
      _ = |chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|) := by
        simp [u, y]
  refine Integrable.mono hdom hFmeas ?_
  filter_upwards with p
  have hDnn : 0 ≤ |chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|) := by
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hSnonneg) (abs_nonneg _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    |wLoc ℓ g p.1 x p.2| ≤ |chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|) := hbnd p
    _ = |(|chiU ℓ p.1 x| * ((2 * S) * |g (x - p.2)|))| := (abs_of_nonneg hDnn).symm


/-- **lem:LocPotential (pair)**: `∫_u w_u(x,y) du = v(x−y)` pointwise, for
`v` supported in `ball 0 R` and `ℓ` with `(χ⋆χ) ≥ 1/2` on `ball 0 r₀ ⊇
ball(0,R/ℓ)`. -/
theorem locPotential_pair {v : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hv : ∀ x : ℝ³, R ≤ ‖x‖ → v x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    ∀ x y : ℝ³, (∫ u : ℝ³, wLoc ℓ v u x y) = v (x - y) := by
  intro x y
  by_cases hc : convScale ℓ (x - y) ≠ 0
  · -- the denominator `(χ⋆χ)((x−y)/ℓ)` is nonzero: field law
    simpa [wLoc] using (wScaled_integral (h := v) ℓ (ne_of_gt hℓ) x y hc)
  · -- denominator zero: then `v (x − y) = 0` by the support hypothesis and
    -- the integrand vanishes identically
    have hc0 : convScale ℓ (x - y) = 0 := by
      by_contra hcne
      exact hc hcne
    have hv0 : v (x - y) = 0 := by
      by_contra hvn
      have hhalf : 1 / 2 ≤ convScale ℓ (x - y) :=
        convScale_ge_half_of_hnz (h := v) hℓ hv hRℓ hC hvn
      rw [hc0] at hhalf
      norm_num at hhalf
    calc
      (∫ u : ℝ³, wLoc ℓ v u x y) = ∫ u : ℝ³, (0 : ℝ) := by
        apply integral_congr_ae
        exact ae_of_all _ (by intro u; dsimp [wLoc, wScaled]; simp [hv0, hc0])
      _ = 0 := by simp
      _ = v (x - y) := hv0.symm

/-- **lem:LocPotential (one-body)**: `∫_u ∫_y w_{1,u}(x,y) dy du =
∫_y g(x−y) dy`, for `g ∈ L¹` supported in `ball 0 R` and the same regime. -/
theorem locPotential_onebody {g : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) :
    ∀ x : ℝ³,
      (∫ u : ℝ³, ∫ y : ℝ³, wLoc ℓ g u x y) = (∫ y : ℝ³, g (x - y)) := by
  intro x
  -- Fubini: `∫_u∫_y w_u(x,y) = ∫_y∫_u w_u(x,y)` (the kernel is integrable
  -- on the product, dominated by `|χ_u(x)|·(2S·|g(x−y)|)`)
  have hInt : Integrable (fun p : ℝ³ × ℝ³ => wLoc ℓ g p.1 x p.2) (volume.prod volume) :=
    locPotential_integrable hℓ hg hgsupp hRℓ hC x
  calc
    (∫ u : ℝ³, ∫ y : ℝ³, wLoc ℓ g u x y)
        = ∫ y : ℝ³, (∫ u : ℝ³, wLoc ℓ g u x y) := by
          exact integral_integral_swap (f := fun (u : ℝ³) (y : ℝ³) => wLoc ℓ g u x y) hInt
    _ = ∫ y : ℝ³, g (x - y) := by
          apply integral_congr_ae
          exact ae_of_all _ (by intro y; exact locPotential_pair hℓ hgsupp hR hr₀ hRℓ hC x y)

/-- The pair-sum version: `Σ_{i<j} ∫_u w_u(xᵢ,xⱼ) du = Σ_{i<j} v(xᵢ−xⱼ)`. -/
theorem locPotential_pair_sum {N : ℕ} {v : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hv : ∀ x : ℝ³, R ≤ ‖x‖ → v x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : X N) :
    (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
        ∫ u : ℝ³, wLoc ℓ v u (x ij.1.1) (x ij.1.2)) =
      (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) := by
  apply Finset.sum_congr rfl
  intro ij hij
  exact locPotential_pair hℓ hv hR hr₀ hRℓ hC (x ij.1.1) (x ij.1.2)

/-- The one-body-sum version: `Σᵢ ∫_u ∫_y w_{1,u}(xᵢ,y) dy du =
Σᵢ ∫_y g(xᵢ−y) dy`. -/
theorem locPotential_onebody_sum {N : ℕ} {g : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : X N) :
    (∑ i : Fin N, ∫ u : ℝ³, ∫ y : ℝ³, wLoc ℓ g u (x i) y) =
      (∑ i : Fin N, ∫ y : ℝ³, g (x i - y)) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact locPotential_onebody hℓ hg hgsupp hR hr₀ hRℓ hC (x i)



end BoseGases

end Submission
