/-
# `L3RhsL12zero`: `|L₁₂ u 0| ≤ C · |u|_{ℋ⁰_α}`, uniformly for `α ∈ (0,1]`

This is the `k = 0` sibling of the *already proved*
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm` (the `k = 4` case), following the same
Cauchy–Schwarz route and with the same `α`-free constant `BK · √W2 + 1`.

The point of the passage from `k = 4` to `k = 0` is that the `ℋ⁰`-integrand is *exactly*
the square of the weighted datum

  `Gaz u s θ = u s θ · w s / sin(2θ)^{η/2}`:

in `HkIntegrand α 0 f z θ` the first (pure `D_z`) sum has the single term `i = 0`, and the
second (mixed) sum is empty because its guard `1 ≤ i ∧ i + j ≤ 0` is unsatisfiable.  Hence
`HkSq α 0 u = ∫∫ (Gaz u)²`, `HkNorm α 0 u = √(∫∫ (Gaz u)²)`, `HkMem α 0 u` is integrability
of the slice/marginal of this single square — and in particular

  **`HkSq α 0`, `HkNorm α 0`, `HkMem α 0` are independent of `α`**, so the
  `∀ α ∈ Ioc 0 1` quantifier of the statement is inert.

`L₁₂ u 0 = ∫_{s>0} ∫_θ K(θ)·u(s,θ)/s dθ ds` with `K θ = 3 sin θ cos²θ` and, using
`1/(s·w s) = s/(1+s)² = Wlam s`,

  `K θ · u s θ / s = Wlam s · (K θ · Sw θ · Gaz u s θ)`,   `Sw θ = sin(2θ)^{η/2}`,

so the density factorises as (radial weight) × (angular pairing), and two
Cauchy–Schwarz steps — angular, against the `L²`-norm `BK` of `K·Sw`, and radial, against
the `L²`-norm `√W2` of `Wlam` — give the bound with `C = BK·√W2 + 1`.

Everything below is a transcription of the `k = 4` proof with `4 ↦ 0`; the only ingredient
that had to be redone is the pointwise domination of `Gaz` by the square root of the
integrand (`Gaz_sq_le_HkIntegrand_zero`, `abs_Gaz_le_sqrt_HkIntegrand_zero`), which at
`k = 0` is an equality rather than a comparison with the `i = 0` summand.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise domination of the weighted datum by the `ℋ⁰`-integrand -/

/-- At `k = 0` the squared weighted datum is (at most, in fact exactly) the `ℋ⁰`-integrand:
the only surviving summand is the `D_z^0`-term `i = 0`. -/
lemma Gaz_sq_le_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 0 h z θ 0 (by norm_num)

/-- On the domain, `|Gaz|` is dominated by the square root of the `ℋ⁰`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 0 h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand_zero α h z θ)

/-! ## The angular Cauchy–Schwarz step -/

/-- The angular half of the argument, at `k = 0`: the weighted angular profile `K · Sw` is
paired against the weighted datum `Gaz h s` and estimated by Cauchy–Schwarz against the
`ℋ⁰`-integrand.  The only hypothesis is integrability of the slice of the integrand; no
measurability of `h` is needed (the Cauchy–Schwarz step is arranged so that the only
functions whose measurability is used are the continuous profile `K·Sw`, the integrable
square root `√(HkIntegrand α 0 h s ·)`, and `|K·Sw|`). -/
theorem abs_integral_K_S_Gaz_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 h s θ)
      Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      ≤ BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Sw θ with hu
  set v : ℝ → ℝ := fun θ => Gaz h s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 0 h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 0 h s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 0 h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact abs_Gaz_le_sqrt_HkIntegrand_zero α h s θ
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BK := by
    rw [BK]
    congr 1
    simp only [hu]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Sw θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ) := by
        rw [hsqrt_u, hsqrt_w]

/-! ## The pointwise bound on the `L₁₂`-density -/

/-- The `L₁₂`-density as a constant multiple of the angular integral of the weighted datum
(specialisation to `k = 0` of the density factorisation; the factorisation itself is
`α`- and `k`-independent and is proved in `Work.FTS.GalBasis.cc`). -/
lemma abs_L12dens_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 0 h)
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ)) := by
  rw [L12dens_eq_weighted h hs, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_K_S_Gaz_le_zero α h (hmem.1 s hs.le)) (Wlam_nonneg hs.le)

/-! ## The radial Cauchy–Schwarz step -/

/-- **The integrated pointwise bound on the `L₁₂`-density** (`k = 0`).  If
`|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α 0 h s θ))` for every `s > 0` and
`h ∈ ℋ⁰_α`, then the same bound holds after integrating in `s`:

`∫_{s>0} |L12dens h s| ≤ BK · √W2 · √(HkSq α 0 h)`.

This is Cauchy–Schwarz in the radial variable: `Wlam²` is integrable on `(0,∞)` with
`∫ Wlam² = W2`, and `∫_{(0,∞)} (√(∫_θ HkIntegrand α 0 h s θ))² = HkSq α 0 h` (the two sets
`(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`). -/
theorem integral_abs_L12dens_le_zero (α : ℝ) (h : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α 0 h)
    (hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ))) :
    ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- `H` is integrable on `(0,∞)` (hence so is `A²`)
  have hH_int : IntegrableOn H (Set.Ioi 0) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi 0)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi 0)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(0,∞)} A² = HkSq α 0 h`, up to the null set `{0}`
  have hW2eq : ∫ s in Set.Ioi 0, Wlam s ^ 2 = W2 := rfl
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α 0 h := by
    rw [hH]; rfl
  have hA2sq : ∫ s in Set.Ioi 0, A s ^ 2 = Work.Spaces.HkSq α 0 h := by
    have h1 : ∫ s in Set.Ioi 0, A s ^ 2 = ∫ s in Set.Ioi 0, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]; exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    rw [h1, h2, hIz_eq]
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi 0) hWlam_memLp hA_memLp
    rw [hA2sq, hW2eq] at hcs
    have hnn : 0 ≤ ∫ s in Set.Ioi 0, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs =>
        mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s)
    rwa [abs_of_nonneg hnn] at hcs
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ), Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi 0) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi 0) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (le_of_lt hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi 0, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi 0, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi 0, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi 0, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi 0, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi 0, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) := by ring

/-! ## The main theorem -/

/-- **`|L₁₂ u 0|` is bounded by the `ℋ⁰_α`-norm of `u`, uniformly in `α ∈ (0,1]`.**

`L₁₂ u 0 = ∫_{s>0} ∫_θ K θ · u s θ / s`, and with `Gaz u s θ = u s θ · w s / sin(2θ)^{η/2}`
one has the factorisation `K θ u/s = Gaz u · (K θ Sw θ Wlam s)`; two Cauchy–Schwarz steps
(angular against `BK = √(∫_θ (K Sw)²)`, radial against `√W2 = √(∫_s Wlam²)`) give
`|L₁₂ u 0| ≤ BK·√W2 · √(HkSq α 0 u) = BK·√W2 · |u|_{ℋ⁰_α}`.  Both constants are finite,
positive and independent of `α` (and of `u`); the statement's `α` is confined to `(0,1]`
for consistency with the surrounding blocks of `L3Rhs`. -/
theorem L3RhsL12zero : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (u : Work.FTS.Galerkin.Fn),
    Work.Spaces.HkMem α 0 u →
    |Work.Construction.L12 u 0| ≤ C * Work.Spaces.HkNorm α 0 u := by
  refine ⟨BK * Real.sqrt W2 + 1, by nlinarith [BK_nonneg, Real.sqrt_nonneg W2], ?_⟩
  intro α hα h hmem
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h s θ)) :=
    fun s hs => abs_L12dens_le_zero α h hmem hs
  have hL12 : Work.Construction.L12 h 0
      = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s := rfl
  calc |Work.Construction.L12 h 0|
      = |∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s| := by rw [hL12]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens h s))
    _ ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 0 h) :=
        integral_abs_L12dens_le_zero α h hmem hbd
    _ = (BK * Real.sqrt W2) * Work.Spaces.HkNorm α 0 h := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α 0 h := by
        have hx := Work.Spaces.HkNorm_nonneg α 0 h
        nlinarith

end Work.FTS.StrongPersist.L3Rhs
