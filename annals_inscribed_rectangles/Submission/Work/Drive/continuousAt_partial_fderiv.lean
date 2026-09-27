import Mathlib

/-!
# Continuity of the partial `fderiv` of a smooth function

`Work.Drive.continuousAt_partial_fderiv`: if `ρ : P × X → F` is smooth (`C^∞`, indeed analytic,
since the order in the hypothesis is `ω = ((⊤ : ℕ∞) : WithTop ℕ∞)`) on an open set `U` and
`q₀ ∈ U`, then the partial derivative in the second variable,
`q ↦ fderiv ℝ (fun x : X => ρ (q.1, x)) q.2`, is continuous at `q₀`.

The proof is a two-line application of `ContDiffAt.fderiv`:

* the map `(q, x) ↦ ρ (q.1, x)` is `ρ ∘ L` for the continuous linear map
  `L : (P × X) × X →L[ℝ] P × X`, `L (q, x) = (q.1, x)`, hence smooth at `(q₀, q₀.2)`;
* `q ↦ q.2` is smooth, so `ContDiffAt.fderiv` gives the smoothness (in particular the continuity)
  of `q ↦ fderiv ℝ (fun x => ρ (q.1, x)) q.2`.
-/

namespace Work.Drive

theorem continuousAt_partial_fderiv {P X F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (P × X)} (hU : IsOpen U) (ρ : P × X → F)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ U) {q₀ : P × X} (hq₀ : q₀ ∈ U) :
    ContinuousAt (fun q : P × X => fderiv ℝ (fun x : X => ρ (q.1, x)) q.2) q₀ := by
  -- the continuous linear map `(q, x) ↦ (q.1, x)`, whose composite with `ρ` is `uncurry` of the
  -- partial map
  let L : (P × X) × X →L[ℝ] P × X :=
    ((ContinuousLinearMap.fst ℝ P X).comp (ContinuousLinearMap.fst ℝ (P × X) X)).prod
      (ContinuousLinearMap.snd ℝ (P × X) X)
  have hLfun : ∀ p : (P × X) × X, L p = (p.1.1, p.2) := by intro p; rfl
  have hρat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ q₀ := hρ.contDiffAt (hU.mem_nhds hq₀)
  have hL : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ⇑L (q₀, q₀.2) := L.contDiff.contDiffAt
  have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun q : P × X => fun x : X => ρ (q.1, x))) (q₀, q₀.2) := by
    have : Function.uncurry (fun q : P × X => fun x : X => ρ (q.1, x)) = ρ ∘ L := by
      funext p
      show ρ (p.1.1, p.2) = ρ (L p)
      rw [hLfun p]
    rw [this]
    exact hρat.comp (q₀, q₀.2) hL
  have hres : ContDiffAt ℝ 0
      (fun q : P × X => fderiv ℝ (fun x : X => ρ (q.1, x)) q.2) q₀ :=
    ContDiffAt.fderiv (f := fun q : P × X => fun x : X => ρ (q.1, x))
      hf (g := fun q : P × X => q.2) contDiff_snd.contDiffAt (by simp)
  exact hres.continuousAt

end Work.Drive
