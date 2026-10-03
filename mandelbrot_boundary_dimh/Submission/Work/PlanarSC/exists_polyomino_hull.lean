import Mathlib
import Submission.Work.PlanarSC.PolyDefs
import Submission.Work.PlanarSC.HullDefs
import Submission.Work.PlanarSC.exists_compact_preconnected_superset
import Submission.Work.PlanarSC.exists_polyomino_superset_of_preconnected_compact
import Submission.Work.PlanarSC.exists_finset_compHull_eq
import Submission.Work.PlanarSC.isPreconnected_compl_compHull
import Submission.Work.PlanarSC.isPreconnected_compHull
import Submission.Work.PlanarSC.compHull_subset_of_no_bounded_complement

/-!
# A hole-free dyadic polyomino hull of a compact subset of a plane domain without holes

For `U ⊆ ℂ` open, connected, with no bounded complementary component, and `K ⊆ U` compact, there is
a finite union of closed dyadic squares `P = dyadicPolyomino n S` with `K ⊆ P ⊆ U`, `P` nonempty and
preconnected, and with preconnected complement.

The proof is the "join, cover, fill" construction:

* `exists_compact_preconnected_superset` joins the pieces of `K` by paths in `U`, producing a compact
  preconnected `K' ⊆ U`;
* `exists_polyomino_superset_of_preconnected_compact` covers `K'` by the cells of a dyadic polyomino
  `P ⊆ U`, from the canonical exhaustion of `U`; every cell used meets `K'`, which makes `P`
  preconnected;
* `HullDefs.compHull` fills in the bounded components of `Pᶜ`.  `exists_finset_compHull_eq` says the
  result is again a polyomino at the same level, `isPreconnected_compHull` and
  `isPreconnected_compl_compHull` give the two preconnectedness conclusions, and
  `compHull_subset_of_no_bounded_complement` keeps the result inside `U`.
-/

open Set

namespace Work.PlanarSC

theorem exists_polyomino_hull {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hnb : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (S : Finset (ℤ × ℤ)),
      K ⊆ Work.PlanarSC.dyadicPolyomino n S ∧
      Work.PlanarSC.dyadicPolyomino n S ⊆ U ∧
      (Work.PlanarSC.dyadicPolyomino n S).Nonempty ∧
      IsPreconnected (Work.PlanarSC.dyadicPolyomino n S) ∧
      IsPreconnected (Work.PlanarSC.dyadicPolyomino n S)ᶜ := by
  -- Step 1: join the pieces of `K` by paths inside `U`.
  obtain ⟨K', hKK', hK'U, hK'c, hK'ne, hK'pre⟩ :=
    exists_compact_preconnected_superset hUo hUc hK hKU
  -- Step 2: cover `K'` by the cells of a preconnected polyomino `P ⊆ U`.
  obtain ⟨n, S, hK'S, hSU, hSpre⟩ :=
    exists_polyomino_superset_of_preconnected_compact hUo hK'c hK'ne hK'pre hK'U
  -- Step 3: fill in the bounded complementary components, and represent the result as a polyomino.
  obtain ⟨S', hS'⟩ := exists_finset_compHull_eq n S
  obtain ⟨x, hx⟩ := hK'ne
  have hne : (dyadicPolyomino n S).Nonempty := ⟨x, hK'S hx⟩
  refine ⟨n, S', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hS']
    exact hKK'.trans (hK'S.trans subset_compHull)
  · rw [← hS']
    exact compHull_subset_of_no_bounded_complement hnb hSU
  · rw [← hS']
    exact hne.mono subset_compHull
  · rw [← hS']
    exact isPreconnected_compHull n S hne hSpre
  · rw [← hS']
    exact isPreconnected_compl_compHull n S

end Work.PlanarSC
