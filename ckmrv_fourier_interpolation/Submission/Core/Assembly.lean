import ChallengeDeps
import Submission.Work.Core.Basic
import Submission.Work.Sampling.rapidlyDecreasing_coeffs
import Submission.Work.Summability.exists_schwartz_tsum
import Submission.Work.Sampling.coeffs_continuous_linear
import Submission.Work.Sampling.summable_norm_mul_pow
import Submission.Work.Core.Formula

/-!
# Assembling the CKMRV interpolation isomorphism

The target statement `CKMRV n k₀` says that the sampling map
`f ↦ coeffs n k₀ f` is a bijection from radial complex Schwartz functions on
`R^n` onto the four rapidly decreasing sample sequences.  This file records the
elementary half of the assembly:

* `samplingMap`: the forward map, whose second component is the proof that the
  samples of a Schwartz function are rapidly decreasing
  (`Work.Sampling.rapidlyDecreasing_coeffs`);
* `samplingMap_injective`: the interpolation formula forces the sampling map to
  be injective (a radial Schwartz function all of whose samples vanish is zero).
-/

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

namespace Submission

/-- The forward map of the CKMRV sampling isomorphism: a radial Schwartz function is
sent to its four sample sequences, together with the proof that they are rapidly
decreasing. -/
noncomputable def samplingMap (n k₀ : ℕ) [NeZero n] :
    RadialSchwartz n → RapidSampleData k₀ :=
  fun f => ⟨coeffs n k₀ f.1, Work.Sampling.rapidlyDecreasing_coeffs n k₀ f.1⟩

@[simp]
theorem samplingMap_apply (n k₀ : ℕ) [NeZero n] (f : RadialSchwartz n) :
    (samplingMap n k₀ f).1 = coeffs n k₀ f.1 := rfl

/-- A pointwise series of radial functions is radial. -/
theorem radial_tsum {n : ℕ} [NeZero n] {ι : Type*}
    {u : ι → EuclideanSpace ℝ (Fin n) → ℂ} (hu : ∀ i, Radial (u i)) :
    Radial fun x => ∑' i, u i x := by
  intro x y hxy
  exact tsum_congr fun i => hu i x y hxy

/-- If a family of radial Schwartz functions reconstructs every radial Schwartz function
from its samples (the interpolation formula), then the sampling map is injective: a
radial Schwartz function whose four sample sequences all vanish is zero. -/
theorem samplingMap_injective (n k₀ : ℕ) [NeZero n]
    (D : Work.Core.InterpolationBasis n k₀) : Function.Injective (samplingMap n k₀) := by
  intro f g hfg
  have hc : coeffs n k₀ f.1 = coeffs n k₀ g.1 := by
    have h := congrArg Subtype.val hfg
    simpa [samplingMap] using h
  refine Subtype.ext ?_
  ext x
  rw [D.formula f x, D.formula g x]
  exact tsum_congr fun i => by rw [hc]

/-- The polynomially weighted sample sequence `‖a i‖ * (k+1)^N` is summable for every `N`
when the sample sequence `a` is rapidly decreasing. -/
theorem summable_weight_samples (k₀ N : ℕ) (a : Set.Ici k₀ × Fin 4 → ℂ)
    (ha : RapidlyDecreasingSamples a) :
    Summable fun i : Set.Ici k₀ × Fin 4 => ‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1) ^ N := by
  have key : Summable fun p : Fin 4 × Set.Ici k₀ =>
      ‖a (p.2, p.1)‖ * ((((p.2).1 : ℕ) : ℝ) + 1) ^ N := by
    rw [summable_prod_of_nonneg (fun i => by positivity)]
    exact ⟨fun j => Work.Sampling.summable_norm_mul_pow k₀ N (fun k => a (k, j)) (ha j),
      Summable.of_finite⟩
  exact key.prod_symm

/-- Surjectivity of the sampling map, given the two analytic inputs: continuity of the
sampling functionals (a continuous linear map `C` agreeing with `coeffs`) and summability
of the polynomially weighted coefficient sequence.  The reconstruction is the pointwise
series `∑ i, a i • basis i`. -/
theorem samplingMap_surjective_of (n k₀ : ℕ) [NeZero n] (D : Work.Core.InterpolationBasis n k₀)
    (a : Set.Ici k₀ × Fin 4 → ℂ)
    (C : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ((Set.Ici k₀ × Fin 4) → ℂ))
    (hC : ∀ f, C f = coeffs n k₀ f)
    (hW : ∀ N : ℕ, Summable fun i : Set.Ici k₀ × Fin 4 =>
      ‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1) ^ N) :
    ∃ f : RadialSchwartz n, coeffs n k₀ f.1 = a := by
  let u : (Set.Ici k₀ × Fin 4) → 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := fun i => a i • (D.basis i).1
  have hsum : ∀ k l : ℕ, Summable fun i => (SchwartzMap.seminorm ℂ k l) (u i) := by
    intro k l
    obtain ⟨Cc, N, hCnn, hgrow⟩ := D.growth k l
    refine Summable.of_nonneg_of_le
      (fun i => apply_nonneg (SchwartzMap.seminorm ℂ k l) _) (fun i => ?_)
      ((hW N).mul_left Cc)
    calc (SchwartzMap.seminorm ℂ k l) (u i)
        = ‖a i‖ * (SchwartzMap.seminorm ℂ k l) (D.basis i).1 := by
          rw [show u i = a i • (D.basis i).1 from rfl, map_smul_eq_mul]
      _ ≤ ‖a i‖ * (Cc * (((i.1.1 : ℕ) : ℝ) + 1) ^ N) :=
          mul_le_mul_of_nonneg_left (hgrow i) (norm_nonneg _)
      _ = Cc * (‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1) ^ N) := by ring
  obtain ⟨g, hsum_g, hgfun⟩ := Work.Summability.exists_schwartz_tsum n u hsum
  have hrad : Radial g := by
    rw [funext hgfun]
    refine radial_tsum (fun i => ?_)
    have h1 : (fun x => u i x) = fun x => a i * (D.basis i).1 x := by
      funext x; simp [u]
    change Radial (fun x => u i x)
    rw [h1]
    intro x y hxy
    show a i * (D.basis i).1 x = a i * (D.basis i).1 y
    rw [(D.basis i).2 x y hxy]
  have hhas : HasSum (fun i => C (u i)) (C g) := C.hasSum hsum_g
  have htsum : C g = ∑' i, C (u i) := hhas.tsum_eq.symm
  have hCu : ∀ i, C (u i) = a i • coeffs n k₀ (D.basis i).1 := by
    intro i
    rw [show u i = a i • (D.basis i).1 from rfl, map_smul, hC (D.basis i).1]
  refine ⟨⟨g, hrad⟩, funext fun j => ?_⟩
  have h1 : coeffs n k₀ g j = ∑' i, (C (u i)) j := by
    have hproj : HasSum (fun i => (C (u i)) j) ((C g) j) := by
      simpa using (ContinuousLinearMap.hasSum
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Set.Ici k₀ × Fin 4 => ℂ) j) hhas)
    rw [← hC g]
    exact hproj.tsum_eq.symm
  rw [h1]
  have h2 : (fun i => (C (u i)) j) = fun i => a i * (coeffs n k₀ (D.basis i).1 j) := by
    funext i
    rw [hCu i]
    rfl
  rw [h2]
  rw [tsum_eq_single j (fun i hi => by
    have hzero : (fun j' => if j' = i then (1 : ℂ) else 0) j = 0 := by
      show (if j = i then (1 : ℂ) else 0) = 0
      rw [if_neg (Ne.symm hi)]
    rw [D.delta i, hzero, mul_zero])]
  rw [D.delta j]
  show a j * (if j = j then (1 : ℂ) else 0) = a j
  simp

/-- **The CKMRV Fourier interpolation theorem, modulo the construction of the
interpolation basis.**  If a family of radial Schwartz functions indexed by the samples has
Kronecker-delta samples, Schwartz seminorms of at most polynomial growth, and reconstructs
every radial Schwartz function from its samples (the interpolation formula), then the
sampling map is a bijection onto the rapidly decreasing sample sequences. -/
theorem ckmrv_of_interpolationBasis (n k₀ : ℕ) [NeZero n]
    (D : Work.Core.InterpolationBasis n k₀) : CKMRV n k₀ := by
  obtain ⟨C, hC⟩ := Work.Sampling.coeffs_continuous_linear n k₀
  have hinj : Function.Injective (samplingMap n k₀) := samplingMap_injective n k₀ D
  have hsurj : Function.Surjective (samplingMap n k₀) := by
    rintro ⟨a, ha⟩
    obtain ⟨f, hf⟩ := samplingMap_surjective_of n k₀ D a C hC
      (fun N => summable_weight_samples k₀ N a ha)
    exact ⟨f, Subtype.ext hf⟩
  exact ⟨Equiv.ofBijective (samplingMap n k₀) ⟨hinj, hsurj⟩, fun f => rfl⟩

/-- **The CKMRV interpolation theorem from Gaussian-level data.**  It suffices to produce
the interpolation basis, its Kronecker-delta samples, polynomial seminorm growth, and the
interpolation identity evaluated at the complex Gaussians: the density of the Gaussians
(Lemma 2.7 of the paper) upgrades the identity to all radial Schwartz functions. -/
theorem ckmrv_of_gaussian_data (n k₀ : ℕ) [NeZero n]
    (basis : Set.Ici k₀ × Fin 4 → RadialSchwartz n)
    (delta : ∀ i, coeffs n k₀ (basis i).1 = fun j => if j = i then (1 : ℂ) else 0)
    (growth : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ i : Set.Ici k₀ × Fin 4, (SchwartzMap.seminorm ℂ k l) (basis i).1
        ≤ C * ((i.1.1 : ℝ) + 1) ^ N)
    (h : ∀ (τ : ℂ) (hτ : 0 < τ.im), ∀ x : EuclideanSpace ℝ (Fin n),
      Work.Core.gaussianFun n τ x
        = ∑' i : Set.Ici k₀ × Fin 4,
            (coeffs n k₀ (Work.Core.gaussianSchwartz n τ hτ) i) * (basis i).1 x) :
    CKMRV n k₀ :=
  ckmrv_of_interpolationBasis n k₀ (Work.Core.interpolationBasis_of_gaussians n k₀ basis delta growth h)

/-- **The two deep inputs.**  The interpolation theorem is proved by constructing an
interpolation basis, first in the `n₀ = 1` normalisation, in dimensions 8 and 24.  Everything
below is proved; what is missing for the challenge theorem is these two instances. -/
def DeepInterpolation8 : Prop := Nonempty (Work.Core.InterpolationBasis 8 1)

/-- The deep input in dimension 24 (sampling starting at the Leech minimal radius `2`). -/
def DeepInterpolation24 : Prop := Nonempty (Work.Core.InterpolationBasis 24 2)

/-- The CKMRV Fourier interpolation theorem in dimensions 8 and 24, deduced from the
construction of the two interpolation bases. -/
theorem ckmrv_of_deep (h8 : DeepInterpolation8) (h24 : DeepInterpolation24) :
    CKMRV 8 1 ∧ CKMRV 24 2 :=
  ⟨ckmrv_of_interpolationBasis 8 1 h8.some, ckmrv_of_interpolationBasis 24 2 h24.some⟩

end Submission
