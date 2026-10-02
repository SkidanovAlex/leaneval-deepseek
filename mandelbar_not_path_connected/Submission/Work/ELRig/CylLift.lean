/-
# ELRig — the ray-lift data of the parity route (`TailId`), replacing `RayStrand`

`NOTES_LEAD_mandelbar_residuals.md` §3.2: the statement `RayStrand` (“on the strand of `R(αᵢ)`, the
smaller level is the deeper point”) is **false in general** — the lift is an exactly
`1`-periodic-shift curve, its shape does not straighten as `R → ∞`, and the finger counterexample
of `ELRig/NOTES.md` §6 is exactly such a curve.  It is also **not needed**: `reach` and `rigidity`
receive a `LiftSides` argument and never use it, and the only consumer of the lift is R-a3
(`htail`, the equator tail lies in the near side).

This file provides the correct, weaker input — **`TailId`**: in a far-left half plane the
`Ψ`-preimages of the two root rays are *exactly* the two lift curves.  It is true and provable
(§3.2 (a)) from `exists_liftCurvesV3` (`Work.ELRig.exists_liftCurvesV3`: the curves
`γ₁, γ₂ = conj γ₁ + ½`, `Ψ (γ₁ s) = rayPt α₁ (τ s)` with `τ` strictly increasing onto `(1,∞)`, and
the periodicity), from `fl.Ψ_inj`, `fl.Ψ_small` and the continuity of the Green function at `z₁`.

## The design (`NOTES_LEAD_mandelbar_residuals.md` §3.2 (a)–(d))

**(a) `TailId`** (`exists_rayCylLift`, 2–3K): choose `s*` with `γ₁((-∞,s*]) ⊆ H_{R_inj}` (from the
periodicity, `Re γ₁ s ≤ s + K`), `t* = τ s*`.  Ray points of level `≥ t*` have Green value
`≥ log t* > 0`, so they are `≥ δ` away from `z₁` (continuity of the Green function at `z₁`, where
its value is `0`).  Take `R ≥ R_inj` with `Ψ(H_R) ⊆ ball z₁ δ` (`Ψ_small`).  Then `Ψ w = rayPt α₁ t`
forces `t < t*`, so `γ₁(τ⁻¹ t) ∈ H_{R_inj}`, and injectivity of `Ψ` there gives `w = γ₁(τ⁻¹ t)`.

*Deriving the surjectivity of `τ` (which (a) uses): `V3`'s data plus `Work.ELRig.rayPt_level_inj`
(the level of a ray point is determined by it) give the self-similarity `τ (s+1) = (τ s) ^ 1024`
via `γ₁ (s+1) = γ₁ s + 1`, `Ψ_shift` and `rayPt_F_alpha1`; with the tail coverage (`(1,t₀) ⊆ range τ`
because levels below `t₀` lie on `γ₁`) and iterating the self-similarity one gets
`range τ = (1,∞)`.  (`τ` is not required to be continuous.)*

**(b) local flip** (2–3K): at `p = γ₁ s*`, `B := log φ ∘ Ψ` is holomorphic and injective near `p`
with `B(γ₁ s) = log τ s + 2πiα₁`.  A `C¹` path `σ` crossing `γ₁` transversally at `p` has
`Im B − 2πα₁` changing sign, so the points of `σ` just before and after `p` lie on rays of angle
`α₁ ± small`, i.e. in the two sides of the pair (`PairSides.paramRay_far` / `paramRay_near`).

**(c) odd parity ⇒ `htail`** (3–4K): under `hE` the real axis meets neither lift, so WLOG
`γ₁ ⊆ {Im > 0}`, `γ₂ = ιγ₁ ⊆ {Im < 0}`.  For generic `x₀ < -R` the vertical segment
`V = [x₀, x₀ + iY]` (`Y > max(B, R₀)`) meets only `γ₁`, in `#{s : Re γ₁ s = x₀}` points, which is
odd (`h(s) = Re γ₁ s − x₀` has `h(s+1) = h(s) + 1` and simple zeros).  The top of `V` lies in
`Pa ⊆ pairSide` (`Ψ_ends`, `Pa_far`), every crossing flips the side ((b)), and `Ψ(V ∖ γ₁)` avoids
the pair curve (`TailId` + `Ψ_small`).  So `Ψ x₀ ∈ pairSideNear`, and the whole real tail is too
(connected, off the pair curve).

**(d) even parity ⇒ side preservation** (2–3K): for `z = Ψ w` near `z₁`, off the pair curve and not
in `Pa`, the segment `[w, w+1]` meets `γ₁` in `#{zeros of the 1-periodic Im γ₁ − Im w} =: N(w)`
points, even for generic `Im w` (each zero `s` gives exactly one shift `γ₁ s + n ∈ [w, w+1)`), and
`z`, `F z` are the images of the two endpoints; `Pa` is handled by `mapsTo_Pa`.  This is the
`Z1Nest.SP` field, which the ELNest area needs after `NestData.band` is dropped (`§3.3`).

## Consequences

With `TailId`, R-a3 is proved by **crossing parity** (§3.2 (b)–(c)): a vertical segment crosses the
lift an odd number of times, every transversal crossing flips the side, and the top of the segment
lies in the petal — so the real axis lands in the near side.  No monotonicity, no Jordan curve
theorem.  The same argument in its *even* form gives the side preservation `Z1Nest.SP` (§3.2 (d)),
which is what the ELNest area needs after `NestData.band` is dropped (§3.3).
-/
import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The ray-lift data of the parity route.**  The curves of `exists_liftCurvesV3` together with
`TailId`: in the far-left half plane `{Re < -R}` the `Ψ`-preimages of the two root rays are exactly
the two lifts. -/
structure RayCylLift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) where
  /-- the lift of the ray `R(α₁)`. -/
  γ₁ : ℝ → ℂ
  /-- the lift of the ray `R(α₂)`. -/
  γ₂ : ℝ → ℂ
  /-- the level parametrisation: `Ψ (γ₁ s)` is the point of `R(α₁)` of level `τ s`. -/
  τ : ℝ → ℝ
  /-- the half-plane level past which the preimages are the lifts. -/
  R : ℝ
  /-- the level parametrisation is strictly increasing. -/
  hτmono : StrictMono τ
  /-- all levels are `> 1`. -/
  hτ1 : ∀ s : ℝ, 1 < τ s
  /-- the first lift maps onto the ray at the level `τ s`. -/
  hΨ₁ : ∀ s : ℝ, fl.Ψ (γ₁ s) = Work.EL.rayPt d.hN Work.EL.alpha1 (τ s)
  /-- the first lift is continuous. -/
  cont₁ : Continuous γ₁
  /-- the second lift is continuous. -/
  cont₂ : Continuous γ₂
  /-- the first lift is `1`-periodic up to the translation `w ↦ w + 1`. -/
  per₁ : ∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1
  /-- the second lift is `1`-periodic up to the translation `w ↦ w + 1`. -/
  per₂ : ∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1
  /-- the anti-symmetry of the pair: `γ₂` is the reflection-shift of `γ₁`. -/
  anti : ∀ s : ℝ, γ₂ s = star (γ₁ s) + 1 / 2
  /-- **`TailId`, first ray**: a `Ψ`-preimage of a point of `R(α₁)` in the half plane is on `γ₁`. -/
  tailId₁ : ∀ w : ℂ, w.re < -R → fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha1 →
    w ∈ Set.range γ₁
  /-- **`TailId`, second ray**. -/
  tailId₂ : ∀ w : ℂ, w.re < -R → fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha2 →
    w ∈ Set.range γ₂
  /-- in the far left half plane `Ψ` misses the parabolic point (the flower's `Ψ_small`). -/
  hzne : ∀ w : ℂ, w.re < -R → fl.Ψ w ≠ d.z₁
  /-- the flower's `Ψ_ends` level below `R`: the far-left large-`|Im|` region of this half plane
  lies in the attracting petal. -/
  hγtail : ∃ R₀ : ℝ, R₀ < R ∧ ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa
  /-- `Ψ` is injective on the half plane `{Re < -R}` (the flower's `Ψ_inj` at a level below `R`).
  Hence `Ψ` is a local biholomorphism at every point of that half plane
  (`Work.ELRig.exists_localInverseAt_of_inj`, `Work.ELRig.deriv_psi_ne_zero_of_inj`). -/
  hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R}

namespace RayCylLift

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-- The second lift maps onto the ray `R(α₂)` at the level `(τ s) ^ 32` (the antiholomorphic
square root `g = (T_c)^[5]` realises `t ↦ t^32` on the rays). -/
theorem hΨ₂ (L : RayCylLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₂ s) = Work.EL.rayPt d.hN Work.EL.alpha2 ((L.τ s) ^ (32 : ℕ)) := by
  rw [L.anti s, fl.Ψ_anti, L.hΨ₁ s]
  exact Work.ELRig.rayPt_g_alpha1 d (L.hτ1 s)

/-- The first lift maps into the ray `R(α₁)`. -/
theorem img₁ (L : RayCylLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
  rw [L.hΨ₁ s]
  exact Work.EL.rayPt_mem_paramRay d.hN (L.hτ1 s)

/-- The second lift maps into the ray `R(α₂)`. -/
theorem img₂ (L : RayCylLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₂ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
  rw [L.hΨ₂ s]
  exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ (L.hτ1 s) (by norm_num))

/-- Under the contradiction hypothesis `E ⊆ K c`, the real axis below the level `-R` avoids the two
lifts: a real point of a lift would have `Ψ`-image on one of the two rays, hence outside `K c`. -/
theorem hreal_of (L : RayCylLift d fl) (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∀ x : ℝ, x < -L.R → (x : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
  rintro x _ (h | h)
  · obtain ⟨s, hs⟩ := h
    have hmem : fl.Ψ (x : ℂ) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
      rw [← hs]; exact L.img₁ s
    exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 hmem) (hE x)
  · obtain ⟨s, hs⟩ := h
    have hmem : fl.Ψ (x : ℂ) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
      rw [← hs]; exact L.img₂ s
    exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2 hmem) (hE x)

end RayCylLift

end Work.ELRig
