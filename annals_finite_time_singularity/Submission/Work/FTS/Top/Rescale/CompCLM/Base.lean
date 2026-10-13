/-
# `Work.FTS.Top.Rescale.CompCLM.Base` — the reparametrisation of `IsContDiffHolderOn`

Generic, self-contained lemmas behind the time-rescaling of the strip `C^{1,α}` class
(`Work.FTS.Top.Rescale.isContDiffHolderOn_uncurry_timeScale`).

If `g : ℝ³ × ℝ → ℝ³` is `C^{1,α}` on a set `t`, `Φ : (ℝ³ × ℝ) →L[ℝ] (ℝ³ × ℝ)` is a continuous
linear map with `Φ '' s ⊆ t`, and `A : ℝ³ →L[ℝ] ℝ³`, then `z ↦ A (g (Φ z))` is `C^{1,α}` on `s`,
provided `s` is uniquely differentiable within at each of its points (so that the within chain rule
pins down `fderivWithin ℝ (fun z => A (g (Φ z))) s`).

This file contains the two *structural* blocks — the `C¹` block and the **within-derivative
formula** — together with the norm form of `HolderOnWith`, which is stated in `edist` coordinates in
Mathlib.  The two *estimation* blocks (boundedness and Hölder of the composite derivative) are in
the sibling modules `CompCLM.Bounded` and `CompCLM.Holder`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Top.Rescale.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.Top.Rescale

/-- **The `C¹` block.**  Precomposition with a continuous linear map `Φ` (mapping `s` into `t`) and
postcomposition with a continuous linear map `A` preserve `C¹` on the strip. -/
theorem contDiffOn_comp_clm {s t : Set (Work.FTS.Top.R3 × ℝ)}
    {g : Work.FTS.Top.R3 × ℝ → Work.FTS.Top.R3}
    (A : Work.FTS.Top.R3 →L[ℝ] Work.FTS.Top.R3)
    (Φ : (Work.FTS.Top.R3 × ℝ) →L[ℝ] (Work.FTS.Top.R3 × ℝ))
    (hΦ : MapsTo Φ s t) (hg : ContDiffOn ℝ 1 g t) :
    ContDiffOn ℝ 1 (fun z => A (g (Φ z))) s := by
  have h1 : ContDiffOn ℝ 1 (g ∘ Φ) s :=
    hg.comp (Φ.contDiff.contDiffOn (𝕜 := ℝ) (s := s)) hΦ
  have h2 : ContDiffOn ℝ 1 (⇑A) Set.univ := A.contDiff.contDiffOn
  have h3 := h2.comp h1 (fun _ _ => trivial)
  convert h3 using 1
  ext z
  rfl

/-- **The within-derivative formula.**  On a set `s` which is uniquely differentiable within at
each of its points, the within-derivative of `z ↦ A (g (Φ z))` is the composite of the
within-derivative of `g` at `Φ z` with the two fixed linear maps `A` and `Φ`.

This is the within chain rule (`HasFDerivWithinAt.comp`, twice) together with
`HasFDerivWithinAt.fderivWithin`; the hypothesis `huniq` is what pins the within-derivative down. -/
theorem fderivWithin_comp_clm {s t : Set (Work.FTS.Top.R3 × ℝ)}
    {g : Work.FTS.Top.R3 × ℝ → Work.FTS.Top.R3}
    (A : Work.FTS.Top.R3 →L[ℝ] Work.FTS.Top.R3)
    (Φ : (Work.FTS.Top.R3 × ℝ) →L[ℝ] (Work.FTS.Top.R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t) :
    ∀ z ∈ s, fderivWithin ℝ (fun z => A (g (Φ z))) s z
      = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ) := by
  intro z hz
  have hz_t : Φ z ∈ t := hΦ hz
  have hg' : HasFDerivWithinAt g (fderivWithin ℝ g t (Φ z)) t (Φ z) :=
    (hg (Φ z) hz_t).hasFDerivWithinAt
  have hΦ' : HasFDerivWithinAt Φ Φ s z := Φ.hasFDerivAt.hasFDerivWithinAt
  have hcomp1 : HasFDerivWithinAt (g ∘ Φ) (fderivWithin ℝ g t (Φ z) ∘L Φ) s z :=
    HasFDerivWithinAt.comp z hg' hΦ' hΦ
  have hA : HasFDerivWithinAt (⇑A) A Set.univ ((g ∘ Φ) z) :=
    A.hasFDerivAt.hasFDerivWithinAt
  have hcomp2 : HasFDerivWithinAt (⇑A ∘ (g ∘ Φ))
      (A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)) s z :=
    HasFDerivWithinAt.comp z hA hcomp1 (fun _ _ => trivial)
  have := hcomp2.fderivWithin (huniq z hz)
  change fderivWithin ℝ (⇑A ∘ (g ∘ Φ)) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)
  exact this

/-- **The norm form of `HolderOnWith`.**  `HolderOnWith` is stated in `edist` coordinates; every
estimate below is in norm coordinates. -/
theorem norm_le_of_holderOnWith {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X} (h : HolderOnWith C r f s) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ) := by
  intro x hx y hy
  have h1 := h.edist_le hx hy
  rw [edist_dist, edist_dist, dist_eq_norm] at h1
  have hC : ((C : ℝ≥0∞)) = ENNReal.ofReal (C : ℝ) := ENNReal.coe_nnreal_eq _
  rw [hC] at h1
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)] at h1
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

end Work.FTS.Top.Rescale
