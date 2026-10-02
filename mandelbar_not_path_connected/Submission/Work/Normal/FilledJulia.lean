import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.escapeRadius

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Elementary invariants of the filled Julia set

For a polynomial map `f` of degree `d ≥ 1` the filled Julia set `K = FilledJuliaSet f` (the set of
points with bounded orbit) satisfies:

* `f(K) ⊆ K` and `f⁻¹(K) ⊆ K` (a point has bounded orbit iff its image does, from `Basic`);
* `f(K°) ⊆ K°` and `f⁻¹(K°) ⊆ K°` (here the open mapping property of a nonconstant holomorphic
  map is used, together with `f(K) ⊆ K` and `f⁻¹(K) ⊆ K`).

These are the invariances used to identify the Julia set with the boundary of `K` and to prove that
the Julia set is backward invariant.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- A polynomial map of degree at least one is continuous. -/
theorem continuous_of_isPolynomialMapOfDegree {d : ℕ} {f : ℂ → ℂ}
    (hf : IsPolynomialMapOfDegree d f) : Continuous f := by
  obtain ⟨P, -, hPf⟩ := hf
  rw [show f = fun z => P.eval z from funext fun z => hPf z]
  exact Polynomial.continuous P

/-- A polynomial map of degree at least one is an open map. -/
theorem isOpenMap_of_isPolynomialMapOfDegree {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : IsOpenMap f := by
  obtain ⟨P, hP, hPf⟩ := hf
  rw [show f = fun z => P.eval z from funext fun z => hPf z]
  rcases (AnalyticOnNhd.eval_polynomial P).is_constant_or_isOpenMap with hconst | hmap
  · exfalso
    obtain ⟨w, hw⟩ := hconst
    have hPeq : P = Polynomial.C w := Polynomial.funext fun z => by
      simpa using hw z
    rw [hPeq, Polynomial.natDegree_C] at hP
    omega
  · exact hmap

/-- The interior of the filled Julia set of a polynomial map of degree at least one is forward
invariant. -/
theorem mapsTo_interior_filledJuliaSet {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) :
    MapsTo f (interior (FilledJuliaSet f)) (interior (FilledJuliaSet f)) := by
  intro x hx
  have himg : f '' interior (FilledJuliaSet f) ⊆ FilledJuliaSet f := by
    rintro y ⟨w, hw, rfl⟩
    exact mapsTo_filledJuliaSet f (interior_subset hw)
  have hopen : IsOpen (f '' interior (FilledJuliaSet f)) :=
    isOpenMap_of_isPolynomialMapOfDegree hd hf _ isOpen_interior
  exact interior_maximal himg hopen ⟨x, hx, rfl⟩

/-- The interior of the filled Julia set of a polynomial map of degree at least one is backward
invariant. -/
theorem preimage_interior_filledJuliaSet_subset {d : ℕ} {f : ℂ → ℂ}
    (hf : IsPolynomialMapOfDegree d f) :
    (f ⁻¹' (interior (FilledJuliaSet f))) ⊆ interior (FilledJuliaSet f) := by
  intro x hx
  have hopen : IsOpen (f ⁻¹' (interior (FilledJuliaSet f))) :=
    isOpen_interior.preimage (continuous_of_isPolynomialMapOfDegree hf)
  have hsub : (f ⁻¹' (interior (FilledJuliaSet f))) ⊆ FilledJuliaSet f :=
    fun y hy => preimage_filledJuliaSet_subset f (interior_subset (s := FilledJuliaSet f) hy)
  exact interior_maximal hsub hopen hx

end Work.Normal
