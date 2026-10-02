/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower.exists_phia_pushforward
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Flower.transfer_parabolicFlower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.Model` — the *model* Fatou coordinate of the flower

The delivered flower `Work.FatouCoord.ParabolicFlower` (and the repaired
`Work.FatouCoordFix.ParabolicFlowerFix`) carry their attracting coordinate `φa` as an *opaque*
field: the existence theorem returns `Nonempty (ParabolicFlower …)`, so nothing about *which*
Fatou coordinate was chosen can be recovered from the interface.  For the local comparison with
the perturbed Écalle model (`Work.PARIMP L.MatchData`, items (M-in)/(M-out)) the caller needs
two facts that the interface does not provide:

* **(a) the identification**: the flower's coordinate is the *pushed-forward model coordinate*,
  i.e. the explicit `fatouCoordW` (the Abel coordinate of the parabolic chart) transported along
  the dynamics to the whole petal;
* **(b) the estimate**: consequently, on the petal, `φa = approxCoord + O(1/Re w)` — the
  quantitative form (residuals note §1.2) in which (M-in) and (M-out) read off the Écalle height.

Both are exports of the *construction*, not of the interface; this file re-exports them for the
push-forward construction of `Work.FatouCoord.Flower.exists_phia_pushforward` (which *is* the
construction of the flower) in a form in which a caller can instantiate the flower's `φa`.

## Contents

* `Work.FlowerGlue.modelCoord P Pa sel` — the explicit coordinate
  `φ₀ (f^[n] z) - n` of the push-forward construction (`= FatouCoord.Flower.orbitCoord`);
* `Work.FlowerGlue.modelCoord_eq_of_mem_iterate` / `modelCoord_self` — **the identification**:
  on the petal, the coordinate is `φ₀` read at any orbit time at which the orbit is in the deep
  petal `P`; in particular `modelCoord = φ₀` **on `P`**;
* `Work.FlowerGlue.modelCoord_anti`, `modelCoord_injOn`, `modelCoord_differentiableOn`,
  `modelCoord_shift` — the fields of the flower for this explicit choice;
* `Work.FlowerGlue.fatouCoord_approx_bound` — **the estimate** `fatouCoord = approxCoord + O(1/R)`
  on a right half-plane of the chart (Hubbard–Schleicher's comparison);
* `Work.FlowerGlue.modelCoordTransfer` and its API — the same two facts after an affine transfer
  `u ↦ z₀ + lam * u` of the germ, i.e. in the chart in which the family's flower lives.

## How a caller uses it

To have the identification and the estimate for the flower of the family, build the flower from
this coordinate (or, equivalently, use `Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix`
and *record* `φa := modelCoord …` at the construction site): the two exports above are then
available in the chart of the caller's conjugacy.  See `Submission/Work/FlowerGlue/NOTES.md`,
"the opacity of `φa`", for why no statement about the `Classical.choice`-produced flower can be
proved from the flower interface alone.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FlowerGlue

open Work.FatouCoord Work.FatouCoord.Flower

noncomputable section

variable {f h gU φ₀ : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
  {M : ℝ} {s : ℂ} {z : ℂ}

/-! ## 1. The model coordinate of the push-forward construction -/

/-- **The model coordinate** of the flower: the orbit coordinate of the push-forward
construction `Work.FatouCoord.Flower.exists_phia_pushforward`, i.e.

  `modelCoord P Pa sel z = φ₀ (f^[sel z] z) - sel z`  for `z ∈ Pa`,

where `sel z` is any time at which the orbit of `z` has entered the deep petal `P`.  This is the
explicit function that the delivered flower's (opaque) field `φa` is chosen to be; every field of
the flower that this file uses is proved for it in `FatouCoord.Flower`. -/
def modelCoord (f φ₀ : ℂ → ℂ) (P Pa : Set ℂ) (sel : ℂ → ℕ) : ℂ → ℂ :=
  orbitCoord f φ₀ P Pa sel

@[simp] theorem modelCoord_apply (z : ℂ) :
    modelCoord f φ₀ P Pa sel z = orbitCoord f φ₀ P Pa sel z := rfl

/-- **(a) The identification.**  On the petal, the model coordinate is the model coordinate `φ₀`
evaluated at *any* orbit time `m` at which the orbit has entered the deep petal `P`. -/
theorem modelCoord_eq_of_mem_iterate
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hz : z ∈ Pa) {m : ℕ} (hm : f^[m] z ∈ P) :
    modelCoord f φ₀ P Pa sel z = φ₀ (f^[m] z) - (m : ℂ) :=
  orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hm

/-- The model coordinate on the deep petal `P` itself **is** `φ₀`: this is the exact sense in
which the flower's coordinate is the pushed-forward model coordinate. -/
theorem modelCoord_self (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hsub : P ⊆ Pa) (hz : z ∈ P) : modelCoord f φ₀ P Pa sel z = φ₀ z := by
  have h := modelCoord_eq_of_mem_iterate hsel hPmaps hφ (hsub hz) (m := 0) hz
  simpa using h

/-- The model coordinate satisfies the antiequivariance of the flower (Hubbard–Schleicher
Lemma 2.3). -/
theorem modelCoord_anti (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hanti : IsAntiholomorphicFatouOn gU φ₀ P) (hgg : gU ∘ gU = f)
    (hz : z ∈ Pa) (hz' : gU z ∈ Pa) :
    modelCoord f φ₀ P Pa sel (gU z) = star (modelCoord f φ₀ P Pa sel z) + 1 / 2 :=
  orbitCoord_map_gU hsel hPmaps hφ hanti hgg hz hz'

/-- The model coordinate is holomorphic on the petal. -/
theorem modelCoord_differentiableOn (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hf : Differentiable ℂ f) (hPopen : IsOpen P) (hPmaps : Set.MapsTo f P P)
    (hφ : IsFatouCoordinateOn f φ₀ P) :
    DifferentiableOn ℂ (modelCoord f φ₀ P Pa sel) Pa :=
  differentiableOn_orbitCoord hsel hf hPopen hPmaps hφ

/-- The model coordinate is injective on the petal. -/
theorem modelCoord_injOn (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hφinj : Set.InjOn φ₀ P) (hfPa : Set.InjOn f Pa) (hPamaps : Set.MapsTo f Pa Pa) :
    Set.InjOn (modelCoord f φ₀ P Pa sel) Pa :=
  injOn_orbitCoord hsel hPmaps hφ hφinj hfPa hPamaps

/-! ## 2. The estimate `fatouCoord = approxCoord + O(1/R)` -/

/-- **(b) The estimate.**  On a right half-plane of the parabolic chart `w = -1/z`, the Fatou
coordinate of the germ is the approximate coordinate `approxCoord (1 - a) w = w - (1-a) log w`
plus a remainder of size `O(1 / Re w)`.

This is `Work.FatouCoord.Exist.fatouCoordW_tsum_bound`, restated in the dynamical variable
`z = -1/w` (the form in which (M-in)/(M-out) read the height off the model). -/
theorem fatouCoord_approx_bound (hb : ParabolicBounds f h a r A A') :
    ∃ N K : ℝ, 0 < N ∧ 1 / r < N ∧ 0 ≤ K ∧ ∀ w : ℂ, N < w.re →
      ‖fatouCoord f (1 - a) (-1 / w) - approxCoord (1 - a) w‖ ≤ K / w.re := by
  obtain ⟨N, K, hN, hrN, hK, hbnd⟩ := Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  refine ⟨N, K, hN, hrN, hK, fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0] at hw
    simp at hw
    linarith
  have key : fatouCoord f (1 - a) (-1 / w) = fatouCoordW f (1 - a) w := by
    rw [fatouCoord_eq, chart]
    congr 1
    field_simp
  rw [key]
  exact hbnd w hw

/-- The same estimate for the flower's *model* coordinate: on the deep petal `P = Petal r M`
(where the model coordinate is `φ₀ = fatouCoord + s`), the remainder is `O(1/Re w)` up to the
constant `‖s‖` — the phase normalisation constant, which is a *real* additive constant of the
Fatou coordinate and hence does not affect any Écalle height. -/
theorem modelCoord_approx_bound (hb : ParabolicBounds f h a r A A')
    (hφ₀ : φ₀ = fun z => fatouCoord f (1 - a) z + s)
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P) (hPmaps : Set.MapsTo f P P)
    (hφ : IsFatouCoordinateOn f φ₀ P) (hsub : P ⊆ Pa) {M : ℝ} (hP : P = Petal r M) :
    ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧ ∀ w : ℂ, N < w.re → (-1 / w) ∈ P →
      ‖modelCoord f φ₀ P Pa sel (-1 / w) - approxCoord (1 - a) w - s‖ ≤ K / w.re := by
  obtain ⟨N, K, hN, _hrN, hK, hbnd⟩ := fatouCoord_approx_bound (f := f) (h := h) (a := a) hb
  refine ⟨max N 1, K, lt_of_lt_of_le one_pos (le_max_right _ _), hK, ?_⟩
  intro w hw hwP
  have hwN : N < w.re := lt_of_le_of_lt (le_max_left _ _) hw
  have hmem : modelCoord f φ₀ P Pa sel (-1 / w) = φ₀ (-1 / w) :=
    modelCoord_self hsel hPmaps hφ hsub hwP
  rw [hmem, hφ₀]
  have h1 : fatouCoord f (1 - a) (-1 / w) + s - approxCoord (1 - a) w - s
      = fatouCoord f (1 - a) (-1 / w) - approxCoord (1 - a) w := by ring
  rw [h1]
  exact hbnd w hwN

/-! ## 3. The affine transfer: the same two facts in the chart of the family -/

/-- The model coordinate of the **transferred** flower: with the affine chart
`u ↦ z₀ + lam * u` putting the germ at the flower's centre `z₀`, the transferred coordinate is
`z ↦ modelF ((z - z₀)/lam)`.  This is the coordinate that
`Work.FatouCoord.Flower.transfer_parabolicFlower` (and its repaired copy in `FatouCoordFix`)
assigns to the flower of `(F, g)` at `z₀`. -/
def modelCoordTransfer (z₀ lam : ℂ) (modelF : ℂ → ℂ) : ℂ → ℂ :=
  fun z => modelF ((z - z₀) / lam)

@[simp] theorem modelCoordTransfer_apply (z₀ lam : ℂ) (modelF : ℂ → ℂ) (z : ℂ) :
    modelCoordTransfer z₀ lam modelF z = modelF ((z - z₀) / lam) := rfl

/-- On the transferred petal, the transferred model coordinate is the germ coordinate of the
pre-image — the identification **(a)** in the chart of the family. -/
theorem modelCoordTransfer_trChart {z₀ lam : ℂ} (hlam : lam ≠ 0) (modelF : ℂ → ℂ) (u : ℂ) :
    modelCoordTransfer z₀ lam modelF (z₀ + lam * u) = modelF u := by
  simp only [modelCoordTransfer_apply, add_sub_cancel_left]
  rw [mul_div_cancel_left₀ u hlam]

/-- The estimate **(b)** in the chart of the family: for `w` deep in the chart, the transferred
coordinate differs from the approximate coordinate by `O(1/Re w)`. -/
theorem modelCoordTransfer_approx_bound {z₀ lam : ℂ} (hlam : lam ≠ 0) {modelF : ℂ → ℂ}
    {N K : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hbnd : ∀ u : ℂ, N < u.re → ‖modelF u - approxCoord (1 - a) (-1 / u)‖ ≤ K / u.re)
    {z : ℂ} (hz : N < ((z - z₀) / lam).re) :
    ‖modelCoordTransfer z₀ lam modelF z - approxCoord (1 - a) (-lam / (z - z₀))‖
      ≤ K / ((z - z₀) / lam).re := by
  have h2 : modelCoordTransfer z₀ lam modelF z - approxCoord (1 - a) (-lam / (z - z₀))
      = modelF ((z - z₀) / lam) - approxCoord (1 - a) (-1 / ((z - z₀) / lam)) := by
    rw [modelCoordTransfer_apply]
    congr 1
    rw [neg_div, neg_div, one_div_div]
  rw [h2]
  exact hbnd ((z - z₀) / lam) hz

end

end Work.FlowerGlue
