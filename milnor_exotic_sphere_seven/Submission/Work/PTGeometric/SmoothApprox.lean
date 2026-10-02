import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: G2, smoothing a continuous map that is already smooth near the boundary

The first analytic input of the geometric half of Pontryagin–Thom (G2 of the project lead's
blueprint): a continuous map from a compact smooth `(9+k)`-manifold with boundary into a Euclidean
space, which is already `C^∞` on a neighbourhood of the boundary, can be smoothed while
(i) keeping the boundary values **exactly** (the ends of the null-homotopy are the genuine collapse
maps of the pieces) and (ii) being arbitrarily uniformly close to the original map.

Mathlib's `Continuous.exists_contMDiff_approx_and_eqOn`
(`Mathlib/Geometry/Manifold/SmoothApprox.lean`, derived there from smooth partitions of unity) is
exactly this statement with a precision *function*; specialising the precision to the constant `ε`
gives the form consumed here.  The remaining steps of the smoothing (implementing the approximation
in the target manifold `E = Th(γ_k) ∖ {∞}` through its charts, and retracting the matrix part with
`Work.PTGeometric.grassmannianRetraction`) then only need the approximation error to be at most the
`1/4` of the reach of the Grassmannian.

## Main result

* `Work.PTGeometric.smoothApproximation`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **G2 of the PTGEOMETRIC blueprint: smoothing a continuous map that is already smooth near the
boundary.**

Let `M` be a compact `T2` smooth `(9+k)`-manifold with boundary (modelled on the half-space
`𝓡∂ ((8+k)+1)`), `f : M → ℝ^N` a continuous map which is `C^∞` on an open neighbourhood `V` of `∂M`,
`K ⊆ M` compact and `ε > 0`.  Then there is a `C^∞` map `g : M → ℝ^N` which agrees with `f` on all of
`∂M` and is within `ε` of `f` on `K`.

This is `Continuous.exists_contMDiff_approx_and_eqOn` (Mathlib) with the closed set `S = ∂M` and the
constant precision function `ε`; the extra compact set `K` of the statement is not needed for the
proof — the approximation is uniform on all of `M` — and is kept because it is the form in which the
retraction `Work.PTGeometric.grassmannianRetraction` (which needs an error below `1/4`) consumes it. -/
theorem smoothApproximation (k N : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (f : M → EuclideanSpace ℝ (Fin N)) (hf : Continuous f)
    (V : Set M) (hVopen : IsOpen V) (hbd : (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V)
    (hfV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓡 N) ∞ f V)
    (K : Set M) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → EuclideanSpace ℝ (Fin N),
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 N) ∞ g ∧
      (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, g x = f x) ∧
      (∀ x ∈ K, ‖g x - f x‖ < ε) := by
  obtain ⟨g, hg_approx, hg_eqOn, -⟩ :=
    hf.exists_contMDiff_approx_and_eqOn (𝓡∂ ((8 + k) + 1)) (⊤ : ℕ∞) continuous_const (fun _ => hε)
      ((𝓡∂ ((8 + k) + 1)).isClosed_boundary (n := ∞) (by simp))
      (hVopen.mem_nhdsSet.mpr hbd) hfV
  exact ⟨fun x => g x, g.contMDiff, fun x hx => hg_eqOn hx,
    fun x _ => by simpa [dist_eq_norm] using hg_approx x⟩

/-- **G2 with an arbitrary normed target space** (the form in which the target manifold's coordinates
are smoothed: the pair `(matrix part, vector part)` of the Pontryagin–Thom null-homotopy lives in a
product of normed spaces).  Same statement as `smoothApproximation`, with `EuclideanSpace ℝ (Fin N)`
replaced by an arbitrary real normed space. -/
theorem smoothApproximation_normedSpace {k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (hf : Continuous f)
    (V : Set M) (hVopen : IsOpen V) (hbd : (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V)
    (hfV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → F,
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ g ∧
      (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, g x = f x) ∧
      (∀ x : M, ‖g x - f x‖ < ε) := by
  obtain ⟨g, hg_approx, hg_eqOn, -⟩ :=
    hf.exists_contMDiff_approx_and_eqOn (𝓡∂ ((8 + k) + 1)) (⊤ : ℕ∞) continuous_const
      (fun _ => hε) ((𝓡∂ ((8 + k) + 1)).isClosed_boundary (n := ∞) (by simp))
      (hVopen.mem_nhdsSet.mpr hbd) hfV
  exact ⟨fun x => g x, g.contMDiff, fun x hx => hg_eqOn hx,
    fun x => by simpa [dist_eq_norm] using hg_approx x⟩

end

end Work.PTGeometric
