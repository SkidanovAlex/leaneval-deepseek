/-
# GATE2 / EXL — the residual-1 dichotomy is a theorem: real crossing, or the tail in the near side

The design's residual 1 (`NOTES_LEAD_mandelbar_residuals.md` §2.2, and this area's
`Submission/Work/GATE2/Access.lean`) is a dichotomy on the real line of the repelling coordinate:

* **case (i)**: some real `x₁` lies on the `α₁`-lift `γ₁` — then `Ψ x₁` is a point of the root
  ray `R(α₁)`, hence *off* the filled Julia set, with `α₁`-deviation exactly `0`.  This is the
  "leak point with angle exactly `α₁`" of the design, and it is the input of the *ray route* to
  `EXL` (`Work.GATE2.EXL.exitLoop_exists`, `exitLoop_of_rayLift`);
* **case (ii)**: the real axis avoids both lifts — then the deep equator tail `Ψ (x)`, `x < -R'`,
  lies in the near side of the `α`-pair.

Both branches were previously available only *under the contradiction hypothesis*
`hE : ∀ x, Ψ x ∈ K c` (`Work.ELRig.htail_of_nest`, `htail_of_analytic`, `equatorTail_mem_near` all
carry it, and it is exactly the hypothesis refuted by `equatorLeak`).  This module removes it:
`Work.GATE2.EXL.htail_of_ne` is the same parity argument with `hE` replaced by the direct
"the lift misses the real axis" (`∀ s, (γ₁ s).im ≠ 0`), and the dichotomy follows by a case split.

The case-(i) branch is stated in the form the ray route needs: a **real** point `y₀` with
`L.γ₁ s = (y₀ : ℂ)` and `Ψ y₀ ∉ K c`, i.e. a genuine leak point in the escaping region which lies
on the `α₁`-ray.
-/
import Submission.Work.GATE2.EXL.htail_of_ne

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The residual-1 dichotomy, with the contradiction hypothesis removed.**

For a `RayCylLift` `L` of the two root rays, the analytic side-flip hypothesis `hflip`
(`Work.ELRig.flipHyp_of_jordan` supplies it from the Jordan curve theorem) and the plane-topology
data `d`, `fl`, `nest`:

* either the real axis meets the `α₁`-lift, and then the crossing point is a **real leak point on
  the `α₁`-ray** — off `K c`, hence in the escaping region, with `α₁`-deviation `0`; this is the
  base point of the ray route to `EXL`;
* or the deep equator tail lies in the near side of the `α`-pair (`htail_of_ne`).

This is the design's §2.2 dichotomy as a *theorem*. -/
theorem exists_real_crossing_or_htail {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 L) :
    (∃ y₀ : ℝ, ∃ s : ℝ, L.γ₁ s = ((y₀ : ℝ) : ℂ) ∧
        fl.Ψ ((y₀ : ℝ) : ℂ) ∉ Work.EL.K c) ∨
      (∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ ((x : ℂ)) ∈ Work.EL.pairSideNear nest.P0) := by
  by_cases h : ∃ s : ℝ, (L.γ₁ s).im = 0
  · obtain ⟨s, hs⟩ := h
    have hγ : L.γ₁ s = (((L.γ₁ s).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hs
    refine Or.inl ⟨(L.γ₁ s).re, s, hγ, ?_⟩
    rw [← hγ]
    exact Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 (L.img₁ s)
  · push_neg at h
    exact Or.inr (htail_of_ne d fl nest L han hflip h)

end Work.GATE2.EXL
