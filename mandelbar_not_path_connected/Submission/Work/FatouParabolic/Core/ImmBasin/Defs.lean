/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# The immediate basin and the strip regions (design `NOTES_LEAD_mandelbar_gaps2.md` §2.1)

`Work.FatouParabolic.puncturedBasin F z₀` is the **whole** basin of `z₀` — it contains every
preimage component, so it is *not* simply connected in general (at a root-parabolic parameter
`F = T_c^10` has degree `1024` while its degree on the immediate basin is `4`).  The design of
`Submission/Work/FatouParabolic/NOTES.md` §4 therefore has to work on the **immediate basin**

`Work.FatouParabolic.Core.immBasin F z₀ p₀ = connectedComponentIn (puncturedBasin F z₀) p₀`

for a petal point `p₀` (`p₀ ∈ fl.Pa`), and use the lifting property of the coverings
`F^[n] : Ω₀ → Ω₀` (when `Ω₀` is free of critical points) instead of simple connectivity of a
basin.  The simple connectivity needed for the lifting is that of the **horizontal tail strips**
`tailStrip C B = {τ | C < Re τ ∧ |Im τ| < B}`, which are convex and hence contractible.

This file collects the two definitions; the lemmas of the design (`immBasin_basics` (Q1),
`isCoveringMap_iterate_immBasin` (Q2), `exists_petalInverse` (Q3), the lifting and Liouville
steps (Q4–Q6)) live in the sibling files.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter
open Set

namespace Work.FatouParabolic.Core

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- **The immediate basin** of the parabolic fixed point `z₀`: the connected component of the
*interior* of the basin through a point `p₀` of an attracting petal.

Taking the interior of the basin (rather than, say, the punctured basin) is essential: the
punctured basin contains the countable, non-open, non-Fatou set of preimages of `z₀`, so its
connected component through `p₀` need not be open, and nothing controls what accumulates at it.
The interior of the basin is open, hence a union of components, each of which is open (ℂ is
locally connected). -/
def immBasin (F : ℂ → ℂ) (z₀ p₀ : ℂ) : Set ℂ :=
  connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) p₀

/-- The connected component of the *punctured* basin through `p₀` — the set considered by the
first, superseded version of the design.  It need not be open. -/
def immBasinPunct (F : ℂ → ℂ) (z₀ p₀ : ℂ) : Set ℂ :=
  connectedComponentIn (Work.FatouParabolic.puncturedBasin F z₀) p₀

theorem immBasin_subset_basin {F : ℂ → ℂ} {z₀ p₀ : ℂ} :
    immBasin F z₀ p₀ ⊆ Work.FatouParabolic.basin F z₀ :=
  (connectedComponentIn_subset _ _).trans interior_subset

theorem mem_immBasin_self {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hp₀ : p₀ ∈ interior (Work.FatouParabolic.basin F z₀)) : p₀ ∈ immBasin F z₀ p₀ :=
  mem_connectedComponentIn hp₀

/-- The **horizontal tail strip** `{τ | C < Re τ ∧ |Im τ| < B}`. -/
def tailStrip (C B : ℝ) : Set ℂ := {τ : ℂ | C < τ.re ∧ |τ.im| < B}

@[simp] theorem mem_tailStrip {C B : ℝ} {τ : ℂ} :
    τ ∈ tailStrip C B ↔ C < τ.re ∧ |τ.im| < B := Iff.rfl

theorem tailStrip_subset {C C' B : ℝ} (h : C ≤ C') : tailStrip C' B ⊆ tailStrip C B :=
  fun _ hτ => ⟨lt_of_le_of_lt h hτ.1, hτ.2⟩

theorem isOpen_tailStrip (C B : ℝ) : IsOpen (tailStrip C B) :=
  isOpen_lt continuous_const Complex.continuous_re |>.inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem convex_tailStrip (C B : ℝ) : Convex ℝ (tailStrip C B) := by
  intro x hx y hy a b ha hb hab
  simp only [tailStrip, Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [abs_lt] at hx2 hy2
  have hre : a * x.re + b * y.re ∈ Set.Ioi C := by
    have h := (convex_Ioi C : Convex ℝ (Set.Ioi C)) hx1 hy1 ha hb hab
    simpa [smul_eq_mul] using h
  have him : a * x.im + b * y.im ∈ Set.Ioo (-B) B := by
    have h := (convex_Ioo (-B) B : Convex ℝ (Set.Ioo (-B) B)) ⟨hx2.1, hx2.2⟩ ⟨hy2.1, hy2.2⟩
      ha hb hab
    simpa [smul_eq_mul] using h
  constructor
  · have h1 : (a • x + b • y).re = a * x.re + b * y.re := by simp
    rw [h1]; exact hre
  · have h1 : (a • x + b • y).im = a * x.im + b * y.im := by simp
    rw [h1]
    exact abs_lt.mpr him


/-- The `n`-th iterate of `F` as a self-map of an `F`-invariant set `Ω`, as a map of the
subtype `↥Ω` into itself. -/
def immBasinIterate (Ω : Set ℂ) (F : ℂ → ℂ) (hmap : MapsTo F Ω Ω) (n : ℕ) : ↥Ω → ↥Ω :=
  fun x => ⟨(F^[n]) x.1, Work.FatouCoord.mapsTo_iterate_of_mapsTo hmap n x.2⟩

@[simp] theorem immBasinIterate_coe {Ω : Set ℂ} {F : ℂ → ℂ} {hmap : MapsTo F Ω Ω} {n : ℕ}
    (x : ↥Ω) : ((immBasinIterate Ω F hmap n x : ↥Ω) : ℂ) = (F^[n]) x.1 := rfl

end

end Work.FatouParabolic.Core
