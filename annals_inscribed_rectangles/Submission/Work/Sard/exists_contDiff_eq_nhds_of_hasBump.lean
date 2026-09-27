import Mathlib

/-!
# Smooth local-to-global extension: the corrected statement

The statement requested as `Work.Sard.exists_contDiff_eq_nhds` (and recorded, with its missing
hypothesis, in `Submission/Work/Sard/exists_contDiff_eq_nhds.lean`) quantifies over an **arbitrary**
normed space `E`.  That statement is not provable: every known construction of a global `C^∞`
representative of a `C^∞` germ multiplies the germ by a smooth *bump function* on `E` (this is also
the construction sketched in the doc-string of the requested lemma), and a general normed space need
not carry one.  In Mathlib

* `ContDiffBump c` — the bundled bump function used by the sketch — can only be used as a function
  when the type class `HasContDiffBump E` is available; its only instances are
  `hasContDiffBump_of_innerProductSpace` (`InnerProduct.lean`) and `[FiniteDimensional ℝ E]`
  (`FiniteDimension.lean`), and `HasContDiffBump E` is *not* synthesizable for a general normed
  space;
* every lemma producing a smooth cut-off / Urysohn function on a normed space
  (`exists_contDiff_tsupport_subset`, `IsOpen.exists_contDiff_support_eq`,
  `Continuous.exists_contDiff_approx_and_eqOn`, the manifold `SmoothBumpCovering`, …) carries the
  hypothesis `[FiniteDimensional ℝ E]`.

Mathematically this is not an accident: smooth bump functions are absent in most
infinite-dimensional Banach spaces (e.g. `ℓ^1`, `C[0,1]`), and the question whether *every* `C^∞`
germ at a point of a Banach space has a global `C^∞` representative is a research question — see
Question 1.1 of G. Belitskii and V. Rayskin, *Extension of local smooth maps of Banach spaces*,
arXiv:1703.06299, where it is settled only for spaces carrying a "`K`-map" (a bounded smooth map
that is the identity near the origin; e.g. `C^q`-smooth spaces, `C(M)`, `C^n(M)`).

This file proves the lemma with the missing hypothesis `[HasContDiffBump E]`.  Note that this
hypothesis is automatic whenever `[FiniteDimensional ℝ E]`, which is the case of the intended
application of the lemma (Sard's theorem for maps that are smooth only on an open subset of
`EuclideanSpace ℝ (Fin (n+1))`, cf. `Work.Sard.weak_interior_empty_open`).
-/

namespace Work.Sard

open Filter Metric Set
open scoped Topology ContDiff

/-- **Smooth local-to-global extension** (corrected statement: `E` carries a smooth bump function).

If `g` is `C^∞` on a neighbourhood `s` of `y₀`, then it agrees with a globally `C^∞` function on a
neighbourhood of `y₀`.  The proof multiplies `g` by a `ContDiffBump` at `y₀` which is `1` on
`closedBall y₀ (ε/4)` and vanishes outside `closedBall y₀ (ε/2) ⊆ s`, where `ball y₀ ε ⊆ s`. -/
theorem exists_contDiff_eq_nhds_of_hasBump {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (y₀ : E) (s : Set E)
    (hs : s ∈ nhds y₀) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ∃ G : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds y₀] g := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  -- a bump function at `y₀`, supported in `ball y₀ ε ⊆ s`
  let β : ContDiffBump y₀ := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hβin : β.rIn = ε / 4 := rfl
  have hβout : β.rOut = ε / 2 := rfl
  -- the closed ball of radius `ε/2` sits in the interior of `s`, where `g` is smooth
  have hball : ball y₀ ε ⊆ interior s := interior_maximal hεs Metric.isOpen_ball
  have hsub : closedBall y₀ (ε / 2) ⊆ interior s := by
    intro x hx
    refine hball ?_
    have hx' : dist x y₀ ≤ ε / 2 := Metric.mem_closedBall.mp hx
    exact Metric.mem_ball.mpr (by linarith)
  refine ⟨fun x => β x • g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ interior s
    · -- inside `s` the product is a product of two smooth functions
      have hgs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g x :=
        (hg x (interior_subset hx)).contDiffAt
          (mem_of_superset (IsOpen.mem_nhds isOpen_interior hx) interior_subset)
      exact β.contDiff.contDiffAt.smul hgs
    · -- outside `interior s` the bump vanishes on a neighbourhood of `x`
      have hx' : x ∉ closedBall y₀ (ε / 2) := fun h => hx (hsub h)
      have hd : ε / 2 < dist x y₀ := not_le.mp (by simpa using hx')
      have hδ : (0 : ℝ) < dist x y₀ - ε / 2 := by linarith
      have hsupp : ∀ᶠ z in nhds x, β z = 0 := by
        refine Filter.eventually_of_mem (Metric.ball_mem_nhds x hδ) ?_
        intro z hz
        refine β.zero_of_le_dist (le_of_lt ?_)
        rw [hβout]
        have hz' : dist x z < dist x y₀ - ε / 2 := Metric.mem_ball'.mp hz
        have h1 : dist x y₀ ≤ dist x z + dist z y₀ := dist_triangle x z y₀
        linarith
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [hsupp] with z hz
      simp [hz]
  · -- near `y₀` the bump is `1`
    filter_upwards [Metric.closedBall_mem_nhds y₀ (show (0 : ℝ) < ε / 4 by linarith)]
      with x hx
    have hx1 : β x = 1 := by
      refine β.one_of_mem_closedBall ?_
      rwa [hβin]
    rw [hx1, one_smul]

/-- **Smooth local-to-global extension**, convenience form for finite dimensional `E`: the required
instance `HasContDiffBump E` is provided by `FiniteDimensional ℝ E`. -/
theorem exists_contDiff_eq_nhds_of_finiteDimensional {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F)
    (y₀ : E) (s : Set E) (hs : s ∈ nhds y₀) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ∃ G : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds y₀] g :=
  exists_contDiff_eq_nhds_of_hasBump g y₀ s hs hg

end Work.Sard
