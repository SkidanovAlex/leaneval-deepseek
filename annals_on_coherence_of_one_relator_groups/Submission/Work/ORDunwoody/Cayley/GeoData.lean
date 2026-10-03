/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The geodesic subdivision data of the Dunwoody construction (step (G2))

`Submission.Work.ORDunwoody.Cayley.exists_geoSubdivision` produces, for a `G`-tree `T` with a
basepoint `t₀` and a finite presentation `P`, the lengths and geodesics used to subdivide the
Cayley complex `Λ` of `P` into `Λ'` so that the equivariant map `φ : Λ' → baryGT T` becomes
cellular.

This file bundles that data into a `structure` (`GeoData`) so that the construction of `Λ'` and
`φ` can be carried out relative to a *fixed* datum (thereby avoiding `Classical.choose` in every
definition), together with `Nonempty (GeoData …)` from the existence theorem.

## Conventions

* `L x` is the length of the geodesic from `t₀` to `genE P x • t₀`, so that the edge with
  generator-with-sign `x` is subdivided into `L x` sub-edges and has `L x - 1` internal vertices.
* The reversal relation is stated with the group element on the left,
  `genE P x • geo (swapLetter x) j = geo x i` for `(i : ℕ) + (j : ℕ) = L x`: this says that
  `geo (swapLetter x)`, the geodesic from `t₀` to `(genE P x)⁻¹ • t₀`, is carried by `genE P x`
  onto the *reverse* of `geo x`.  Without the `•` the relation would force `genE P x • t₀ = t₀`
  for every generator, i.e. a global fixed point.
-/
import Mathlib
import Submission.Work.ORDunwoody.Cayley.Basic
import Submission.Work.ORDunwoody.Cayley.exists_geoSubdivision

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Cayley

open CayV

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-- **The geodesic subdivision data** for the Dunwoody construction: lengths `L` and geodesics
`geo` (one for each generator-with-sign), from the basepoint `t₀` to the translate
`genE P x • t₀`, compatible with the reversal `swapLetter`. -/
structure GeoData (T : GTree G V) (t₀ : V) (P : FinPresentation G) where
  /-- The length of the geodesic of the generator-with-sign `x`. -/
  L : Fin P.n × Bool → ℕ
  /-- The geodesic of the generator-with-sign `x`, enumerated. -/
  geo : (x : Fin P.n × Bool) → Fin (L x + 1) → V
  /-- The geodesic starts at the basepoint. -/
  geo_zero : ∀ x, geo x 0 = t₀
  /-- The geodesic ends at the translate of the basepoint. -/
  geo_last : ∀ x, geo x (Fin.last (L x)) = genE P x • t₀
  /-- Consecutive vertices of the geodesic are adjacent. -/
  geo_adj : ∀ (x : Fin P.n × Bool) (i : Fin (L x)), T.Adj (geo x i.castSucc) (geo x i.succ)
  /-- The geodesic is injective. -/
  geo_inj : ∀ x, Function.Injective (geo x)
  /-- The lengths of `x` and `swapLetter x` agree. -/
  L_swap : ∀ x, L (swapLetter x) = L x
  /-- The reversal relation. -/
  rev₁ : ∀ (x : Fin P.n × Bool) (i : Fin (L x + 1)),
    ∃ j : Fin (L (swapLetter x) + 1), (i : ℕ) + (j : ℕ) = L x ∧
      genE P x • geo (swapLetter x) j = geo x i
  /-- The reversal relation, in the other direction. -/
  rev₂ : ∀ (x : Fin P.n × Bool) (j : Fin (L (swapLetter x) + 1)),
    ∃ i : Fin (L x + 1), (i : ℕ) + (j : ℕ) = L x ∧
      genE P x • geo (swapLetter x) j = geo x i

/-- **Existence of the geodesic subdivision data.** -/
theorem geoData_nonempty (T : GTree G V) (t₀ : V) (P : FinPresentation G) :
    Nonempty (GeoData T t₀ P) := by
  obtain ⟨L, geo, h0, hlast, hadj, hinj, hL, hrev₁, hrev₂⟩ := exists_geoSubdivision T t₀ P
  exact ⟨{ L := L, geo := geo, geo_zero := h0, geo_last := hlast, geo_adj := hadj,
            geo_inj := hinj, L_swap := hL, rev₁ := hrev₁, rev₂ := hrev₂ }⟩

end Work.ORDunwoody.Cayley
