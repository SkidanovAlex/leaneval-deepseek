import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

/-!
# Radial functions on `R^n` and their profiles

This file sets up the elementary API for the challenge's predicate
`LeanEval.Analysis.CKMRVInterpolation.Radial`: radiality of the constant
functions, closure under the vector space operations, under composition with a
linear isometry, radiality of the norm, radiality is preserved by pointwise
limits of nets, and the characterisation `Radial f ↔ ∀ x, f x = f (realIncl ‖x‖)`
in terms of the coordinate axis.

We also define the **profile** `profile f = f ∘ realIncl` of a function on `R^n`,
the continuous linear map `profileCLM` it induces on the Schwartz space (using
that `realIncl` is an isometry, hence antilipschitz and temperate), and record
the basic facts relating the profile of a radial function to the function
itself: `f x = profile f ‖x‖`, the profile is even, and the derivative of the
profile of a radial function at `0` vanishes.

## Main definitions

* `Work.RadialSpace.realInclCLM`: the coordinate axis inclusion as a continuous
  linear map.
* `Work.RadialSpace.profile`: `profile f r = f (realIncl r)`.
* `Work.RadialSpace.profileCLM`: the induced continuous linear map
  `𝓢(R^n, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)`.
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation
open Work.Sampling

variable {n : ℕ} [NeZero n]

/-- The smoothness exponent `∞ : ℕ∞ω`, so that `ContDiff ℝ Smooth f` means that
`f` is `C^∞` (smooth).  Careful: the *top* element `⊤ : ℕ∞ω` is `ω`, which means
*analyticity*, and is strictly stronger. -/
abbrev Smooth : ℕ∞ω := ∞

/-! ### The axis inclusion is a temperate antilipschitz map -/

/-- The coordinate axis inclusion `realIncl : ℝ → R^n` as a continuous linear map. -/
noncomputable def realInclCLM (n : ℕ) [NeZero n] : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.toSpanSingleton ℝ (realIncl (n := n) 1)

lemma realInclCLM_apply (r : ℝ) : realInclCLM n r = realIncl (n := n) r := by
  rw [realInclCLM, ContinuousLinearMap.toSpanSingleton_apply]
  exact (realIncl_eq_smul (n := n) r).symm

lemma realIncl_eq_realInclCLM : realIncl (n := n) = ⇑(realInclCLM (n := n)) :=
  funext fun r => (realInclCLM_apply (n := n) r).symm

/-- `realIncl` has temperate growth. -/
theorem realIncl_hasTemperateGrowth : Function.HasTemperateGrowth (realIncl (n := n)) := by
  obtain ⟨hcd, hb⟩ := (realInclCLM (n := n)).hasTemperateGrowth
  rw [← realIncl_eq_realInclCLM] at hcd hb
  exact ⟨hcd, hb⟩

/-- `realIncl` is an isometry onto its image, in particular antilipschitz. -/
theorem realIncl_antilipschitz : AntilipschitzWith 1 (realIncl (n := n)) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have hlin : realIncl (n := n) x - realIncl (n := n) y = realIncl (n := n) (x - y) := by
    rw [← realInclCLM_apply (n := n) x, ← realInclCLM_apply (n := n) y,
      ← realInclCLM_apply (n := n) (x - y), map_sub]
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [hlin, realIncl_norm, Real.norm_eq_abs]

/-! ### The profile -/

/-- The profile of a function on `R^n`: its restriction to the first coordinate axis. -/
noncomputable def profile (f : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ → ℂ := f ∘ realIncl

@[simp] lemma profile_apply (f : EuclideanSpace ℝ (Fin n) → ℂ) (r : ℝ) :
    profile f r = f (realIncl (n := n) r) := rfl

/-- Restriction of a Schwartz function on `R^n` to the coordinate axis, as a
continuous linear map of Schwartz spaces. -/
noncomputable def profileCLM {n : ℕ} [NeZero n] :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (realIncl_hasTemperateGrowth (n := n))
    (realIncl_antilipschitz (n := n))

@[simp] lemma profileCLM_apply {n : ℕ} [NeZero n] (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ⇑(profileCLM f) = profile f := by
  rw [profileCLM, SchwartzMap.compCLMOfAntilipschitz_apply]
  rfl

/-- For a radial function, the profile determines the function: `f x = f (‖x‖ e₁)`. -/
theorem profile_eq_of_radial {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f)
    (x : EuclideanSpace ℝ (Fin n)) : f x = profile f ‖x‖ :=
  hf x (realIncl (n := n) ‖x‖) (by
    rw [realIncl_norm, abs_of_nonneg (norm_nonneg x)])

/-- The profile of a radial function is even. -/
theorem profile_neg {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f) (r : ℝ) :
    profile f (-r) = profile f r := by
  refine hf (realIncl (n := n) (-r)) (realIncl (n := n) r) ?_
  rw [realIncl_norm, realIncl_norm, abs_neg]

/-- The profile of a radial function is even. -/
theorem profile_even {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f) :
    Function.Even (profile f) := profile_neg hf

/-- The derivative at `0` of the profile of a radial function vanishes. -/
theorem deriv_profile_zero {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f) :
    deriv (profile f) 0 = 0 := by
  have hcomp : deriv (fun x : ℝ => profile f (-x)) 0 = deriv (profile f) 0 := by
    rw [show (fun x : ℝ => profile f (-x)) = profile f from funext (profile_neg hf)]
  rw [deriv_comp_neg] at hcomp
  simp only [neg_zero] at hcomp
  have h2 : deriv (profile f) 0 = -deriv (profile f) 0 := hcomp.symm
  have h5 : deriv (profile f) 0 + deriv (profile f) 0 = 0 := by
    nth_rewrite 1 [h2]
    exact neg_add_cancel (deriv (profile f) 0)
  have h6 : (2 : ℂ) * deriv (profile f) 0 = 0 := by
    rw [two_mul]
    exact h5
  exact (mul_eq_zero.mp h6).resolve_left two_ne_zero

/-! ### The radiality API -/

section RadialAPI

variable {E : Type*} [Norm E] {F : Type*}

lemma radial_zero [Zero F] : Radial (fun _ : E => (0 : F)) := fun _ _ _ => rfl

lemma radial_const [Zero F] (c : F) : Radial (fun _ : E => c) := fun _ _ _ => rfl

lemma radial_add [Add F] {f g : E → F} (hf : Radial f) (hg : Radial g) :
    Radial (f + g) := fun x y h => by simp only [Pi.add_apply, hf x y h, hg x y h]

lemma radial_neg [Neg F] {f : E → F} (hf : Radial f) : Radial (-f) :=
  fun x y h => by simp only [Pi.neg_apply, hf x y h]

lemma radial_sub [Sub F] {f g : E → F} (hf : Radial f) (hg : Radial g) :
    Radial (f - g) := fun x y h => by simp only [Pi.sub_apply, hf x y h, hg x y h]

lemma radial_smul {𝕜 : Type*} [SMul 𝕜 F] {f : E → F} (hf : Radial f) (c : 𝕜) :
    Radial (c • f) := fun x y h => by simp only [Pi.smul_apply, hf x y h]

lemma radial_finsetSum [AddCommMonoid F] {ι : Type*} {s : Finset ι} {f : ι → E → F}
    (hf : ∀ i ∈ s, Radial (f i)) : Radial (fun x => ∑ i ∈ s, f i x) :=
  fun x y h => Finset.sum_congr rfl fun i hi => hf i hi x y h

/-- The norm is radial. -/
lemma radial_norm : Radial (fun x : E => ‖x‖) := fun _ _ h => h

/-- The norm, as a complex-valued function, is radial. -/
lemma radial_norm_complex : Radial (fun x : E => ((‖x‖ : ℝ) : ℂ)) :=
  fun _ _ h => by simp only [radial_norm _ _ h]

/-- Composition of a radial function with a norm-preserving map is radial. -/
theorem radial_comp_norm_map {G : Type*} [Norm G] {f : G → F} (hf : Radial f) {L : E → G}
    (hL : ∀ x, ‖L x‖ = ‖x‖) : Radial (f ∘ L) :=
  fun x y h => hf (L x) (L y) (by rw [hL, hL, h])

/-- Composition of a radial function with a linear isometry is radial. -/
theorem radial_comp_linearIsometry {𝕜 𝔽 𝔾 H : Type*} [NormedField 𝕜]
    [NormedAddCommGroup 𝔽] [NormedSpace 𝕜 𝔽] [NormedAddCommGroup 𝔾] [NormedSpace 𝕜 𝔾]
    {f : 𝔾 → H} (hf : Radial f) (L : 𝔽 →ₗᵢ[𝕜] 𝔾) : Radial (f ∘ L) :=
  fun x y h => hf (L x) (L y) (by rw [L.norm_map, L.norm_map, h])

lemma radial_mul {f g : E → ℂ} (hf : Radial f) (hg : Radial g) : Radial (f * g) :=
  fun x y h => by simp only [Pi.mul_apply, hf x y h, hg x y h]

/-- Radiality is preserved by pointwise limits of nets. -/
theorem radial_of_tendsto {ι : Type*} {l : Filter ι} [TopologicalSpace F] [T2Space F] [l.NeBot]
    {f : ι → E → F} {g : E → F} (hf : ∀ i, Radial (f i))
    (hg : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) : Radial g := by
  intro x y hxy
  refine tendsto_nhds_unique (hg x) ?_
  rw [show (fun i => f i x) = fun i => f i y from funext fun i => hf i x y hxy]
  exact hg y

/-- Any function of the norm is radial. -/
lemma radial_of_norm {g : ℝ → F} : Radial (fun x : E => g ‖x‖) :=
  fun _ _ h => by simp only [h]

/-- Composition of a radial function with a continuous linear map on the
*codomain* side is radial. -/
theorem radial_comp_clm {𝔼 𝔽 : Type*} [Norm 𝔼] {𝔾 : Type*}
    [NormedAddCommGroup 𝔽] [NormedSpace ℝ 𝔽] [NormedAddCommGroup 𝔾] [NormedSpace ℝ 𝔾]
    {f : 𝔼 → 𝔽} (hf : Radial f) (T : 𝔽 →L[ℝ] 𝔾) : Radial (T ∘ f) :=
  fun x y h => by simp only [Function.comp_apply, hf x y h]

end RadialAPI

/-! ### The characterisation of radiality on `R^n` -/

/-- A function on `R^n`, `n ≥ 1`, is radial iff it is determined by the value at
the point `(‖x‖, 0, …, 0)` of the first coordinate axis. -/
theorem radial_iff_realIncl (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    Radial f ↔ ∀ x, f x = f (realIncl (n := n) ‖x‖) := by
  constructor
  · intro hf x
    exact hf x (realIncl (n := n) ‖x‖) (by
      rw [realIncl_norm, abs_of_nonneg (norm_nonneg x)])
  · intro hf x y hxy
    calc f x = f (realIncl (n := n) ‖x‖) := hf x
      _ = f (realIncl (n := n) ‖y‖) := by rw [hxy]
      _ = f y := (hf y).symm

end Work.RadialSpace
