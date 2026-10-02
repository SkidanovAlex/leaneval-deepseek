import Mathlib
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero
import Submission.Work.FatouParabolic.Core.finite_fiber_immBasinIterate
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_basinEscape
import Submission.Work.FatouParabolic.Core.isProperMap_of_escapeBound
import Submission.Work.SeedDyn.isLocalHomeomorph_subtypeMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-!
# Coverings of the immediate basin by iterates of `F` (Q2 of the design)

`Work.FatouParabolic.Core.immBasin F z₀ p₀` is the connected component through `p₀` of the
*interior* of the basin of the fixed point `z₀`
(`Submission/Work/FatouParabolic/Core/ImmBasin/Defs.lean`).  This file proves the covering
statement Q2 of `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §2.1:

`IsCoveringMap (immBasinIterate (immBasin F z₀ p₀) F hmap n)`

for a polynomial map `F` of degree `≥ 2` whose immediate basin is `F`-invariant, bounded,
relatively closed in the punctured basin and free of critical points.

Because `immBasin` is a connected component of the *open* set `interior (basin F z₀)`, the
immediate basin `Ω` is itself open (`isOpen_immBasin` below), and the covering argument is the
classical one, with saturation set `P = interior (basin F z₀)`:

* `F^[n]` is closed and proper on `ℂ` (the escape bound of a polynomial of degree `≥ 2` makes `F`
  proper), and the saturation facts `Ω ⊆ P`, `(F^[n])⁻¹ P ⊆ P`, `P ∩ closure Ω ⊆ Ω` descend this
  to closedness of `F^[n] : Ω → Ω` (`isClosedMap_immBasinIterate`);
* its fibres are finite because a polynomial map of degree `≥ 2` is finite-to-one
  (`finite_fiber_immBasinIterate`);
* it is a local homeomorphism on `Ω` — `deriv F ≠ 0` on `Ω` is transported to the subtype `↥Ω`
  by `Work.SeedDyn.isLocalHomeomorph_subtypeMap`, which is where the openness of `Ω` is used.

`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` then finishes.
-/

open Set Filter
open scoped Topology

variable {F : ℂ → ℂ} {z₀ p₀ : ℂ}

/-- **The immediate basin is open**: it is a connected component of the open set
`interior (basin F z₀)` and `ℂ` is locally connected. -/
theorem isOpen_immBasin (F : ℂ → ℂ) (z₀ p₀ : ℂ) :
    IsOpen (immBasin F z₀ p₀) :=
  isOpen_interior.connectedComponentIn

/-- **Backwards invariance of `interior (basin)`**: if `F^[m] x` lies in the interior of the basin
of `z₀`, so does `x`.  Indeed `F^[m] x ∈ basin` forces `x ∈ basin` (shift the orbit), and the
continuity of `F^[m]` then pulls the open set `interior (basin)` back to a neighbourhood of `x`
consisting of basin points. -/
theorem preimage_interior_basin (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F)
    (m : ℕ) : ∀ x : ℂ, (F^[m]) x ∈ interior (basin F z₀) → x ∈ interior (basin F z₀) := by
  have hdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hsub : (F^[m]) ⁻¹' interior (basin F z₀) ⊆ basin F z₀ := by
    intro y hy
    have hyb : (F^[m]) y ∈ basin F z₀ := interior_subset hy
    rw [Work.FatouParabolic.mem_basin] at hyb ⊢
    have hshift : (fun k : ℕ => (F^[k]) ((F^[m]) y)) = fun k : ℕ => (F^[k + m]) y := by
      funext k
      exact (Function.iterate_add_apply F k m y).symm
    rw [hshift] at hyb
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) y) m).mp hyb
  intro x hx
  have hnhds : (F^[m]) ⁻¹' interior (basin F z₀) ∈ 𝓝 x :=
    ((hdiff.continuous.iterate m).continuousAt).preimage_mem_nhds (isOpen_interior.mem_nhds hx)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnhds hsub)

/-- **The immediate basin is relatively closed in `interior (basin)`**: a point of
`interior (basin)` lying in the closure of the component of `p₀` belongs to that component (its
own component is open, so it meets the component of `p₀`, and two components that meet are
equal). -/
theorem immBasin_closed_in_interior (F : ℂ → ℂ) (z₀ p₀ : ℂ) :
    ∀ x ∈ interior (basin F z₀), x ∈ closure (immBasin F z₀ p₀) → x ∈ immBasin F z₀ p₀ := by
  intro x hx hxcl
  by_contra hxnot
  have hCx : IsOpen (connectedComponentIn (interior (basin F z₀)) x) :=
    isOpen_interior.connectedComponentIn
  have hxCx : x ∈ connectedComponentIn (interior (basin F z₀)) x := mem_connectedComponentIn hx
  obtain ⟨y, hyx, hyΩ⟩ := mem_closure_iff.mp hxcl _ hCx hxCx
  have h1 : connectedComponentIn (interior (basin F z₀)) x
      = connectedComponentIn (interior (basin F z₀)) y := connectedComponentIn_eq hyx
  have h2 : connectedComponentIn (interior (basin F z₀)) y = immBasin F z₀ p₀ :=
    (connectedComponentIn_eq hyΩ).symm
  exact hxnot (h1.trans h2 ▸ hxCx)

/-- **`F^[n]` restricted to the immediate basin is a closed map**, from the closedness of `F^[n]`
on `ℂ` and the saturation conditions along a set `P ⊇ Ω`.

Let `Ω ⊆ P`, let `P` be backwards invariant under `F^[n]` and let `Ω` be relatively closed in `P`.
If `C ⊆ Ω` is closed in `↥Ω` and `y ∈ Ω` lies in the closure of `F^[n] '' C`, then `y = F^[n] a`
for some `a ∈ closure C` (continuity, boundedness of `Ω`), and the saturation conditions upgrade
`a ∈ closure Ω` to `a ∈ Ω`, so `a ∈ Ω ∩ closure C = C`. -/
theorem isClosedMap_immBasinIterate_of_saturated {P : Set ℂ} (n : ℕ)
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F)
    (hmap : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀))
    (hΩP : immBasin F z₀ p₀ ⊆ P)
    (hpre : ∀ x : ℂ, (F^[n]) x ∈ P → x ∈ P)
    (hcl : ∀ x ∈ P, x ∈ closure (immBasin F z₀ p₀) → x ∈ immBasin F z₀ p₀)
    (hbdd : Bornology.IsBounded (immBasin F z₀ p₀)) :
    IsClosedMap (immBasinIterate (immBasin F z₀ p₀) F hmap n) := by
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hcont : Continuous (F^[n]) := hFdiff.continuous.iterate n
  intro C hC
  obtain ⟨D, hDcl, hDC⟩ := isClosed_induced_iff.mp hC
  have hCeq : ∀ x : ↥(immBasin F z₀ p₀), x ∈ C ↔ (x : ℂ) ∈ D := by
    intro x
    rw [← hDC]
    exact Iff.rfl
  have hsub : (Subtype.val '' C : Set ℂ) ⊆ D := by
    rintro b ⟨x, hxC, rfl⟩
    exact (hCeq x).mp hxC
  refine isClosed_induced_iff.mpr ⟨(F^[n]) '' closure (Subtype.val '' C : Set ℂ), ?_, ?_⟩
  · have hbddC : Bornology.IsBounded (Subtype.val '' C : Set ℂ) :=
      hbdd.subset (Subtype.coe_image_subset (immBasin F z₀ p₀) C)
    have hK : IsCompact (closure (Subtype.val '' C : Set ℂ)) :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbddC.closure⟩
    exact (hK.image hcont).isClosed
  · ext x
    constructor
    · intro hx
      rw [mem_preimage] at hx
      obtain ⟨a, ha, hax⟩ := hx
      have haP : a ∈ P := hpre a (by rw [hax]; exact hΩP x.2)
      have hacl : a ∈ closure (immBasin F z₀ p₀) :=
        closure_mono (Subtype.coe_image_subset (immBasin F z₀ p₀) C) ha
      have haΩ : a ∈ immBasin F z₀ p₀ := hcl a haP hacl
      have haD : a ∈ D := hDcl.closure_subset_iff.mpr hsub ha
      refine ⟨⟨a, haΩ⟩, (hCeq ⟨a, haΩ⟩).mpr haD, ?_⟩
      exact Subtype.ext hax
    · rintro ⟨y, hy, rfl⟩
      rw [mem_preimage]
      exact ⟨y.1, subset_closure ⟨y, hy, rfl⟩, rfl⟩

theorem isCoveringMap_iterate_immBasin {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hcl : ∀ x ∈ Work.FatouParabolic.puncturedBasin F z₀,
      x ∈ closure (Work.FatouParabolic.Core.immBasin F z₀ p₀) →
      x ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀)
    (hbdd : Bornology.IsBounded (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hnocrit : ∀ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w ≠ 0) (n : ℕ) :
    IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n) := by
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  -- the saturation set is `P = interior (basin F z₀)`
  -- `F^[n]` is a local homeomorphism on `Ω`, hence on the subtype `↥Ω` (using that `Ω` is open)
  have hlocF : IsLocalHomeomorphOn F (immBasin F z₀ p₀) :=
    isLocalHomeomorphOn_of_deriv_ne_zero hFdiff hnocrit
  have hlocFn : IsLocalHomeomorphOn (F^[n]) (immBasin F z₀ p₀) := by
    induction n with
    | zero =>
        simpa [Function.iterate_zero] using
          (Homeomorph.refl ℂ).isLocalHomeomorph.isLocalHomeomorphOn (s := immBasin F z₀ p₀)
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hlocF.comp ih (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmap k)
  have hloc : IsLocalHomeomorph (immBasinIterate (immBasin F z₀ p₀) F hmap n) :=
    Work.SeedDyn.isLocalHomeomorph_subtypeMap (isOpen_immBasin F z₀ p₀)
      (isOpen_immBasin F z₀ p₀) (fun z hz => Work.FatouCoord.mapsTo_iterate_of_mapsTo hmap n hz)
      hlocFn
  have hclosed : IsClosedMap (immBasinIterate (immBasin F z₀ p₀) F hmap n) :=
    isClosedMap_immBasinIterate_of_saturated (P := interior (basin F z₀)) n hF hmap
      (connectedComponentIn_subset _ _) (preimage_interior_basin hF n)
      (immBasin_closed_in_interior F z₀ p₀) hbdd
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hclosed
    (fun y _ => finite_fiber_immBasinIterate hF hfix hmap hcl hbdd hnocrit n y)
    hloc.isLocalHomeomorphOn

end Work.FatouParabolic.Core
