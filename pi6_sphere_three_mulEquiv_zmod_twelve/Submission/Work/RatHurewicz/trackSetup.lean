import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.StemsB.BundlePullback

/-!
# The mapping track of a map, and the fibration giving the truncation transfer

This file fixes the **vocabulary** used by `Work.RatHurewicz.truncationHomologyTransfer_of_serre`.

Given `inc : X → Z` and `x₀ : X`, let `F := homotopyFibre inc x₀` be the homotopy fibre of `inc`
(the space of pairs `(x, γ)` with `γ` a path from `inc x₀` to `inc x`, `Work.RatHurewicz.homotopyFibre`).
The transfer statement is about the map `H_{n+1}(F) → H_{n+1}(X)` induced by the projection
`homotopyFibreFst inc x₀ : F → X`.

The identification of `ker(fst_*)` in the stable range uses the **mapping track** of `inc`,

  `Track inc := {p : X × C(I,Z) // p.2 1 = inc p.1}`

(the space of pairs `(x, γ)` with `γ` a path in `Z` *ending* at `inc x`), together with

* `trackMap inc : Track inc → Z`, `(x,γ) ↦ γ 0`, which is a **Hurewicz fibration** with fibre over
  `z₀ = inc x₀` the space of paths from `z₀` to `inc x`, i.e. — up to reversal — the homotopy fibre
  `F`;
* `trackProj inc : Track inc → X`, `(x,γ) ↦ x`, which is a homotopy equivalence with explicit
  inverse `trackSec inc` and an explicit homotopy `trackProj ∘ trackSec ≃ id`.

The pair `(Track inc, trackFibre inc (inc x₀))` is the model of "the pair `(X, F)`" of the argument:
the long exact sequence of the pair gives `ker(H_{n+1}(F) → H_{n+1}(X))` as the image of
`H_{n+2}(Track inc, Track fibre)`, which Serre's exact sequence in the stable range identifies with
`H_{n+2}(Z, {z₀})`, rationally vanishing for a range model by hypothesis.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

universe u

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

/-- The **mapping track** of `inc : X → Z`: the space of pairs `(x, γ)` with `γ` a path in `Z`
ending at `inc x` (the start of `γ` is free). -/
def Track (inc : C(X, Z)) : Type u := {p : X × C(unitInterval, Z) // p.2 1 = inc p.1}

instance instTopologicalSpaceTrack (inc : C(X, Z)) : TopologicalSpace (Track inc) :=
  inferInstanceAs (TopologicalSpace {p : X × C(unitInterval, Z) // p.2 1 = inc p.1})

/-- The map `q : Track inc → Z`, `(x,γ) ↦ γ(0)`; the "mapping track fibration" of `inc`. -/
def trackMap (inc : C(X, Z)) : C(Track inc, Z) where
  toFun p := p.1.2 0
  continuous_toFun := (continuous_eval_const 0).comp (continuous_snd.comp continuous_subtype_val)

/-- The map `r : Track inc → X`, `(x,γ) ↦ x`. -/
def trackProj (inc : C(X, Z)) : C(Track inc, X) where
  toFun p := p.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The section `X → Track inc`, `x ↦ (x, const path)`. -/
def trackSec (inc : C(X, Z)) : C(X, Track inc) where
  toFun x := ⟨(x, ContinuousMap.const unitInterval (inc x)), by simp⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_id.prodMk ((ContinuousMap.const' (X := unitInterval) (Y := Z)).comp inc).continuous_toFun

/-- The base point of the track: the pair `(x₀, const path)`. -/
def trackBase (inc : C(X, Z)) (x₀ : X) : Track inc := trackSec inc x₀

/-- The **fibre of the track fibration** over `z₀`: the paths from `z₀` to `inc x`.  It is written
as the preimage `trackMap inc ⁻¹' {z₀}` of the singleton, so that it is *syntactically* the set
that `Work.StemsB.relPairMap (trackMap inc) z₀` uses as its source. -/
abbrev trackFibre (inc : C(X, Z)) (z₀ : Z) : Set (Track inc) := trackMap inc ⁻¹' {z₀}

@[simp]
theorem trackMap_apply (inc : C(X, Z)) (p : Track inc) : trackMap inc p = p.1.2 0 := rfl

@[simp]
theorem trackProj_apply (inc : C(X, Z)) (p : Track inc) : trackProj inc p = p.1.1 := rfl

@[simp]
theorem trackSec_apply (inc : C(X, Z)) (x : X) : trackSec inc x = ⟨(x, ContinuousMap.const unitInterval (inc x)), by simp⟩ := rfl

@[simp]
theorem trackProj_trackSec (inc : C(X, Z)) (x : X) : trackProj inc (trackSec inc x) = x := rfl

@[simp]
theorem trackMap_trackBase (inc : C(X, Z)) (x₀ : X) :
    trackMap inc (trackBase inc x₀) = inc x₀ := rfl

@[simp]
theorem trackBase_mem_trackFibre (inc : C(X, Z)) (x₀ : X) :
    trackBase inc x₀ ∈ trackFibre inc (inc x₀) := rfl

/-- The elements of the fibre of the track fibration, unwrapped. -/
theorem mem_trackFibre {inc : C(X, Z)} {z₀ : Z} {p : Track inc} :
    p ∈ trackFibre inc z₀ ↔ p.1.2 0 = z₀ := Iff.rfl

end

end Work.RatHurewicz
