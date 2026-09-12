import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.zonoidDiff_seq

/-!
# `centred_zonoidDiff_seq` — centred bodies are limits of differences of zonoids

**Statement** (requested by the `klain333_from_cylinders` development; the
geometric content of Klain, *A short proof of Hadwiger's characterization
theorem*, Mathematika 42 (1995) 329–339, Prop. 3.1 (p. 333), together with
Schneider, *Convex Bodies*, Thm 3.4.1): every *centred* convex body `K` (there
is a point `c = v/2` with `K = 2c − K`, i.e.
`(K : Set V) = (fun x => -x + v) '' (K : Set V)`) is a Hausdorff limit of
convex bodies `K_j` each of which is a *generalized zonoid*: there are zonoids
`Y₁`, `Y₂` — spelled out as Hausdorff limits of `[0,1]`-box zonotopes
`Zᵢ(n) = {Σᵢ tᵢ • wᵢ(n,i) : tᵢ ∈ [0,1]}` — with `K_j + Y₂ = Y₁`.

## Mathematical route (as developed in the commons)

* `Commons.Geometry.Convex.Hadwiger.centred0_zonoidDiff_seq` (origin-symmetric
  case, built on
  `Commons.Geometry.Convex.Hadwiger.smoothCentred_dense` — Schneider Thm 3.4.1:
  origin-symmetric bodies with `C∞` support functions are Hausdorff-dense —
  and `Commons.Geometry.Convex.Hadwiger.smoothCentred_generalizedZonoid` — the
  cosine transform / Funk–Hecke inversion
  `cosine_transform_even_smooth_homogeneous`, plus
  `zonoidLimit_of_continuous_even_nonneg`, which realises the cosine transform
  of a nonnegative even continuous density as a limit of `[0,1]`-box
  zonotopes via Riemann sums).
* `Commons.Geometry.Convex.Hadwiger.zonoidDiff_seq` lifts the origin-symmetric
  statement to bodies with an arbitrary centre `c`: translate `K₀ := K − c` to
  the origin, apply the symmetric case, and translate the representation back
  using the elementary set identity `{c} + [0,−c] = [0,c]` (which appends one
  generator to a box-zonotope sequence).

The present file is the requested commons entry: it is exactly the statement
above, obtained from the published commons lemma.
-/

namespace Commons.Geometry.Convex.Hadwiger

open Filter
open scoped Topology BigOperators

theorem centred_zonoidDiff_seq
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (K : ConvexBody V)
    (hK : ∃ v : V, (K : Set V) = (fun x : V => -x + v) '' (K : Set V)) :
    ∃ Kj : ℕ → ConvexBody V,
      Tendsto Kj atTop (𝓝 K) ∧
      ∀ j : ℕ, ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
        (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
        Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
        (∀ n : ℕ, (Z₁ n : Set V) =
          {x : V | ∃ t : Fin (k₁ n) → ℝ, (∀ i : Fin (k₁ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₁ n), t i • w₁ n i}) ∧
        (∀ n : ℕ, (Z₂ n : Set V) =
          {x : V | ∃ t : Fin (k₂ n) → ℝ, (∀ i : Fin (k₂ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₂ n), t i • w₂ n i}) ∧
        Kj j + Y₂ = Y₁ := by
  exact zonoidDiff_seq V K hK

end Commons.Geometry.Convex.Hadwiger
