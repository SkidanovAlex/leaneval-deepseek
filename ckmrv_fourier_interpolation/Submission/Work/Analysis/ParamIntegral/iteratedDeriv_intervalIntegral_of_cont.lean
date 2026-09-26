import Mathlib
import Submission.Work.RadialSpace.Basic

/-!
# Iterated derivatives of a parametric interval integral

Let `k : ℝ → ℝ → ℂ` be a family of functions which is continuous in its second variable, smooth in
its first variable, and whose iterated derivatives in the first variable are uniformly bounded for
`u ∈ [0,1]`.  Then `F r = ∫ u in (0:ℝ)..1, k r u` is smooth, and every iterated derivative of `F`
is obtained by differentiating under the integral sign:

`iteratedDeriv j F r = ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' => k r' u) r`.

The proof differentiates under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
using the uniform bounds of the hypothesis as dominating functions.  Measurability in the
integration variable of the iterated derivatives is obtained by writing the `(j+1)`-st derivative
as a pointwise limit of difference quotients of the `j`-th one and using that a pointwise limit of
measurable functions is measurable (`measurable_of_tendsto_metrizable`).
-/

namespace Work.Analysis.ParamIntegral

open scoped ContDiff
open Filter Topology MeasureTheory Set

variable {k : ℝ → ℝ → ℂ}

/-- In a family `k` smooth in its first variable, the `j`-th iterated derivative in the first
variable is again smooth in the first variable. -/
lemma contDiff_iteratedDeriv_fst
    (hk_smooth : ∀ u, ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => k r u)) (j : ℕ)
    (u : ℝ) :
    ContDiff ℝ Work.RadialSpace.Smooth
      (fun r : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j (hk_smooth u)

/-- If `k` is smooth in its first variable and continuous in its second, then the `j`-th iterated
derivative of `k` in its first variable is Borel measurable in the second variable. -/
lemma measurable_iteratedDeriv_fst
    (hk_cont : ∀ r, Continuous (fun u : ℝ => k r u))
    (hk_smooth : ∀ u, ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => k r u)) :
    ∀ j : ℕ, ∀ r : ℝ, Measurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r) := by
  intro j
  induction j with
  | zero =>
    intro r
    simpa [iteratedDeriv_zero] using (hk_cont r).measurable
  | succ j ih =>
    intro r
    simp only [iteratedDeriv_succ]
    set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
    set φ : ℕ → ℝ → ℂ := fun n u =>
      (t n)⁻¹ * (iteratedDeriv j (fun r' : ℝ => k r' u) (r + t n)
        - iteratedDeriv j (fun r' : ℝ => k r' u) r) with hφ
    have hφ_meas : ∀ n : ℕ, Measurable (φ n) := by
      intro n
      have h1 : Measurable (fun u : ℝ =>
          iteratedDeriv j (fun r' : ℝ => k r' u) (r + t n)
            - iteratedDeriv j (fun r' : ℝ => k r' u) r) := (ih (r + t n)).sub (ih r)
      simpa [hφ] using h1.const_mul ((t n)⁻¹ : ℂ)
    have htend : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa [ht] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      · filter_upwards with n
        rw [ht]
        exact ne_of_gt (one_div_pos.mpr (by positivity))
    have hlim : Tendsto φ atTop
        (𝓝 (fun u : ℝ => deriv (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') r)) := by
      rw [tendsto_pi_nhds]
      intro u
      have hdiff : Differentiable ℝ (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') :=
        (contDiff_iteratedDeriv_fst (k := k) hk_smooth j u).differentiable (by decide)
      have hd_at : DifferentiableAt ℝ (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') r :=
        hdiff.differentiableAt
      have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd_at.hasDerivAt
      have hcomp := hslope.comp htend
      simpa [hφ, Function.comp_def] using hcomp
    exact measurable_of_tendsto_metrizable hφ_meas hlim

/-- Differentiation under the integral sign for the family
`r ↦ iteratedDeriv j (fun r' => k r' u) r`. -/
lemma hasDerivAt_intervalIntegral_iteratedDeriv
    (hk_smooth : ∀ u, ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => k r u))
    (hk_bound : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ B)
    (hmeas : ∀ j : ℕ, ∀ r : ℝ,
      Measurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r))
    (j : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      (∫ u in (0:ℝ)..1, iteratedDeriv (j+1) (fun r' : ℝ => k r' u) r) r := by
  obtain ⟨Bj, -, hBj⟩ := hk_bound j
  obtain ⟨B, -, hB⟩ := hk_bound (j + 1)
  have hconst : ∀ c : ℝ,
      Integrable (fun _ : ℝ => c) (volume.restrict (Set.uIoc (0:ℝ) 1)) := fun c =>
    intervalIntegrable_iff.mp (intervalIntegrable_const (c := c) (a := (0:ℝ)) (b := 1))
  have hIoc : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIoc_subset_uIcc
  have hF_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
        (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    Filter.Eventually.of_forall (fun x => (hmeas j x).aestronglyMeasurable)
  have hF_int : Integrable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (hconst Bj).mono' (hmeas j r).aestronglyMeasurable (by
      rw [ae_restrict_iff' measurableSet_uIoc]
      exact Filter.Eventually.of_forall (fun a ha => hBj a (hIoc ha) r))
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (hmeas (j + 1) r).aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(volume.restrict (Set.uIoc (0:ℝ) 1)),
      ∀ x ∈ (Set.univ : Set ℝ), ‖iteratedDeriv (j + 1) (fun r' : ℝ => k r' a) x‖ ≤ B := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall (fun a ha _ _ => hB a (hIoc ha) _)
  have h_diff : ∀ᵐ a ∂(volume.restrict (Set.uIoc (0:ℝ) 1)),
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x)
          (iteratedDeriv (j + 1) (fun r' : ℝ => k r' a) x) x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun a _ x _ => ?_)
    have hd : Differentiable ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x) :=
      (contDiff_iteratedDeriv_fst (k := k) hk_smooth j a).differentiable (by decide)
    have hd_at : DifferentiableAt ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x) x :=
      hd.differentiableAt
    have h' : HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x)
        (deriv (iteratedDeriv j (fun r' : ℝ => k r' a)) x) x := hd_at.hasDerivAt
    exact h'.congr_deriv (congrFun (iteratedDeriv_succ (n := j) (f := fun r' : ℝ => k r' a)) x).symm
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.uIoc (0:ℝ) 1))
    (F := fun x u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
    (F' := fun x u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) x)
    (x₀ := r) (s := Set.univ) (bound := fun _ : ℝ => B)
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound (hconst B) h_diff
  have hconv : ∀ f : ℝ → ℂ,
      (∫ u : ℝ, f u ∂(volume.restrict (Set.uIoc (0:ℝ) 1))) = ∫ u in (0:ℝ)..1, f u := by
    intro f
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  have hfun : (fun x : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      = fun x : ℝ => ∫ u : ℝ, iteratedDeriv j (fun r' : ℝ => k r' u) x
          ∂(volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    funext (fun x => (hconv (fun u => iteratedDeriv j (fun r' : ℝ => k r' u) x)).symm)
  have hval : (∫ u in (0:ℝ)..1, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      = ∫ u : ℝ, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r
          ∂(volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (hconv (fun u => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)).symm
  rw [hfun, hval]
  exact hmain.2

theorem iteratedDeriv_intervalIntegral_of_cont (k : ℝ → ℝ → ℂ)
    (hk_cont : ∀ r, Continuous (fun u : ℝ => k r u))
    (hk_smooth : ∀ u, ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => k r u))
    (hk_bound : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ B) :
    ContDiff ℝ Work.RadialSpace.Smooth (fun r : ℝ => ∫ u in (0:ℝ)..1, k r u) ∧
    ∀ j : ℕ, ∀ r : ℝ,
      iteratedDeriv j (fun r : ℝ => ∫ u in (0:ℝ)..1, k r u) r
        = ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
  have hmeas := measurable_iteratedDeriv_fst (k := k) hk_cont hk_smooth
  have hstep := fun j (r : ℝ) =>
    hasDerivAt_intervalIntegral_iteratedDeriv (k := k) hk_smooth hk_bound hmeas j r
  have hderiv : ∀ j : ℕ,
      deriv (fun r : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r)
        = fun r : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv (j+1) (fun r' : ℝ => k r' u) r :=
    fun j => funext (fun r => (hstep j r).deriv)
  have hdiff : ∀ j : ℕ, Differentiable ℝ
      (fun r : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r) :=
    fun j => fun r => (hstep j r).differentiableAt
  have hkey : ∀ j : ℕ, iteratedDeriv j (fun r : ℝ => ∫ u in (0:ℝ)..1, k r u)
      = fun r : ℝ => ∫ u in (0:ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
    intro j
    induction j with
    | zero =>
      funext r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      rw [show iteratedDeriv (j + 1) (fun r : ℝ => ∫ u in (0:ℝ)..1, k r u)
          = deriv (iteratedDeriv j (fun r : ℝ => ∫ u in (0:ℝ)..1, k r u))
          from iteratedDeriv_succ, ih]
      exact hderiv j
  refine ⟨?_, fun j r => congrFun (hkey j) r⟩
  exact contDiff_of_differentiable_iteratedDeriv (n := ⊤) (fun m _ => by
    rw [hkey m]
    exact hdiff m)

end Work.Analysis.ParamIntegral
