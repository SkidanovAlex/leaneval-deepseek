import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.support_add
import Submission.Commons.Geometry.Convex.Hadwiger.eq_of_support_eq
import Submission.Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg
import Submission.Commons.Geometry.Convex.Hadwiger.even_smooth_cosine_decompose

/-!
# `smoothCentred_generalizedZonoid` — smooth origin-symmetric bodies are generalized zonoids

**Statement** (Klain–Rota, *Introduction to Geometric Probability*, Prop. 8.1.2;
requested by the `centred0_zonoidDiff_seq` development): every origin-symmetric
convex body whose support function is `C∞` away from the origin is a
*generalized zonoid*: there are zonoids `Y₁`, `Y₂` (Hausdorff limits of
`[0,1]`-box zonotopes) with `X + Y₂ = Y₁`.

## Proof plan (mathematics)

Let `h(u) := sSup {⟨u, x⟩ | x ∈ X}` be the support function.  Since `X = −X`,
`0 ∈ X` and `h` is even, positively 1-homogeneous, and (by `hSmooth`) `C∞` on
`V ∖ {0}`.  The proof has three parts:

1. **cosine inversion / Funk–Hecke** (`coreA_here`, pending commons
   `Commons.Geometry.Convex.Hadwiger.even_smooth_cosine_decompose`): an even
   `C∞` positively homogeneous function on `V ∖ {0}` is the cosine transform
   of a signed even smooth compactly supported density, hence the difference
   `h = C f₁ − C f₂` of the cosine transforms of two **nonnegative** even
   continuous compactly supported densities `f₁, f₂` (take positive/negative
   parts; continuity and bounded support survive).  This is the analytic heart
   (Funk–Hecke surjectivity of the cosine transform on even smooth functions
   of the unit sphere, transferred to `V` by a smooth radial weight).

2. **zonoid generation** (`coreB_here`, pending commons
   `Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg`):
   for a nonnegative even continuous compactly supported density `f`, the
   function `u ↦ (Cf)(u) := ∫_V |⟨u, x⟩| f(x) dx` is the support function of a
   convex body `Y(f)` which is a Hausdorff limit of `[0,1]`-box zonotopes
   (Riemann sums over a fine grid: `Σⱼ f(xⱼ)·Δⱼ·|⟨·,xⱼ⟩|` is the support
   function of the box zonotope with generators `{f(xⱼ)Δⱼ xⱼ, −f(xⱼ)Δⱼ xⱼ}`,
   and uniform continuity of `(u,x) ↦ |⟨u,x⟩|f(x)` on `S × supp f` gives
   uniform convergence of support functions, hence Hausdorff convergence by
   `ConvexBody` completeness (`convexBody_complete` in the commons) and
   `hausdorffDist_eq_sSup_support`).

3. **assembly** (done in this file): apply (2) to `f₁, f₂` obtaining
   `Y₁ = Y(f₁)`, `Y₂ = Y(f₂)` with their box-zonotope approximation
   sequences; then the support functions satisfy
   `h_{Y₁} − h_{Y₂} = C f₁ − C f₂ = h_X`, so by additivity
   (`support_add`) and injectivity (`eq_of_support_eq`) of support functions,
   `X + Y₂ = Y₁` as convex bodies.

## Status

Both parts are now PROVED and imported from the shared commons:
`Commons.Geometry.Convex.Hadwiger.even_smooth_cosine_decompose` (part 1,
the Funk–Hecke / cosine-transform inversion) and
`Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg`
(part 2, zonoid generation by Riemann sums).  The proof below is the
assembly.
-/

namespace Commons.Geometry.Convex.Hadwiger

open Filter Metric Set MeasureTheory
open scoped Topology BigOperators ENNReal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The main statement: smooth origin-symmetric bodies are generalized zonoids.

Proved from the two delegated cores: `coreA` (cosine inversion /
Funk–Hecke: the smooth even homogeneous support function is the difference of
the cosine transforms of two nonnegative even continuous compactly supported
densities) and `coreB` (zonoid generation: each such density generates a
zonoid, a Hausdorff limit of `[0,1]`-box zonotopes, whose support function is
its cosine transform).  The assembly below only uses additivity and
injectivity of support functions. -/
theorem smoothCentred_generalizedZonoid
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (X : ConvexBody V)
    (hSym : (X : Set V) = -(X : Set V))
    (hSmooth : ContDiffOn ℝ ⊤ (fun u : V => sSup ((fun x : V => inner ℝ u x) '' (X : Set V)))
      {u : V | u ≠ 0}) :
    ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
      (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
      Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
      (∀ n : ℕ, (Z₁ n : Set V) =
        {x : V | ∃ t : Fin (k₁ n) → ℝ, (∀ i : Fin (k₁ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
          x = ∑ i : Fin (k₁ n), t i • w₁ n i}) ∧
      (∀ n : ℕ, (Z₂ n : Set V) =
        {x : V | ∃ t : Fin (k₂ n) → ℝ, (∀ i : Fin (k₂ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
          x = ∑ i : Fin (k₂ n), t i • w₂ n i}) ∧
      X + Y₂ = Y₁ := by
  classical
  borelize V
  rcases even_smooth_cosine_decompose V X hSym hSmooth with
    ⟨f₁, f₂, hf₁₀, hf₂₀, hf₁e, hf₂e, hf₁c, hf₂c, hf₁s, hf₂s, hdec⟩
  rcases zonoidLimit_of_continuous_even_nonneg V f₁ hf₁₀ hf₁e hf₁c hf₁s with
    ⟨Y₁, Z₁, k₁, w₁, hT₁, hbox₁, hsup₁⟩
  rcases zonoidLimit_of_continuous_even_nonneg V f₂ hf₂₀ hf₂e hf₂c hf₂s with
    ⟨Y₂, Z₂, k₂, w₂, hT₂, hbox₂, hsup₂⟩
  refine ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT₁, hT₂, hbox₁, hbox₂, ?_⟩
  -- X + Y₂ = Y₁ : prove equality of support functions everywhere
  apply ConvexBody.ext
  apply eq_of_support_eq V (X + Y₂) Y₁
  intro u
  -- support (X + Y₂) u = support X u + support Y₂ u   (additivity)
  have hXY₂ : sSup ((fun x : V => inner ℝ u x) '' ((X + Y₂ : ConvexBody V) : Set V)) =
        sSup ((fun x : V => inner ℝ u x) '' (X : Set V)) +
          sSup ((fun x : V => inner ℝ u x) '' (Y₂ : Set V)) := by
        rw [ConvexBody.coe_add]
        exact support_add V X Y₂ u
  -- support X u = (C f₁ u) - (C f₂ u), support Yᵢ u = C fᵢ u
  have hX : sSup ((fun x : V => inner ℝ u x) '' (X : Set V)) =
      (∫ x : V, |inner ℝ u x| * f₁ x) - (∫ x : V, |inner ℝ u x| * f₂ x) := hdec u
  have hY₁ : sSup ((fun x : V => inner ℝ u x) '' (Y₁ : Set V)) =
      ∫ x : V, |inner ℝ u x| * f₁ x := hsup₁ u
  have hY₂ : sSup ((fun x : V => inner ℝ u x) '' (Y₂ : Set V)) =
      ∫ x : V, |inner ℝ u x| * f₂ x := hsup₂ u
  calc
    sSup ((fun x : V => inner ℝ u x) '' ((X + Y₂ : ConvexBody V) : Set V))
        = sSup ((fun x : V => inner ℝ u x) '' (X : Set V)) +
            sSup ((fun x : V => inner ℝ u x) '' (Y₂ : Set V)) := hXY₂
    _ = ((∫ x : V, |inner ℝ u x| * f₁ x) - (∫ x : V, |inner ℝ u x| * f₂ x)) +
          (∫ x : V, |inner ℝ u x| * f₂ x) := by rw [hX, hY₂]
    _ = ∫ x : V, |inner ℝ u x| * f₁ x := by ring
    _ = sSup ((fun x : V => inner ℝ u x) '' (Y₁ : Set V)) := hY₁.symm

end

end Commons.Geometry.Convex.Hadwiger
