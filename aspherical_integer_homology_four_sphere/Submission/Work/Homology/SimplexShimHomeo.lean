import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The standard simplex, two ways

Mathlib carries two models of the standard simplex on `Fin (n + 1)`:

* `Convexity.StdSimplex ℝ (Fin (n + 1))`, the finsupp-based structure, whose
  coordinates are `w.weights i`;
* `stdSimplex ℝ (Fin (n + 1))`, the (deprecated) set of functions
  `f : Fin (n + 1) → ℝ` with non-negative coordinates summing to `1`.

This file builds the homeomorphism between them, given by the identity in
coordinates, and shows that it commutes with the `map` operations induced by a
map of index sets.
-/

namespace Work.Homology

open Convexity

/-- The identity in coordinates from the finsupp-based standard simplex to the
set-based (deprecated) standard simplex. -/
noncomputable def toStdSimplex (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    _root_.stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun i => w.weights i, fun i => w.weights_nonneg i, by simpa using w.total_of_fintype⟩

@[simp]
theorem toStdSimplex_coe (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ⇑(toStdSimplex n w) = fun i => w.weights i := rfl

/-- The inverse coordinate map: a function on a finite index type is finitely supported. -/
noncomputable def ofStdSimplex (n : ℕ) (s : _root_.stdSimplex ℝ (Fin (n + 1))) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (s : Fin (n + 1) → ℝ), fun m => by simpa using s.2.1 m,
    by simpa [Finsupp.sum_fintype] using s.2.2⟩

@[simp]
theorem ofStdSimplex_weights (n : ℕ) (s : _root_.stdSimplex ℝ (Fin (n + 1))) :
    (ofStdSimplex n s).weights = Finsupp.equivFunOnFinite.symm (s : Fin (n + 1) → ℝ) := rfl

theorem toStdSimplex_ofStdSimplex (n : ℕ) (s : _root_.stdSimplex ℝ (Fin (n + 1))) :
    toStdSimplex n (ofStdSimplex n s) = s :=
  Subtype.ext (funext (fun _ => rfl))

theorem ofStdSimplex_toStdSimplex (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    ofStdSimplex n (toStdSimplex n w) = w :=
  Convexity.StdSimplex.ext (Finsupp.ext (fun _ => rfl))

theorem continuous_toStdSimplex (n : ℕ) : Continuous (toStdSimplex n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => Convexity.StdSimplex.continuous_weights_apply ℝ i)

theorem continuous_ofStdSimplex (n : ℕ) : Continuous (ofStdSimplex n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  exact continuous_subtype_val

/-- The homeomorphism between the finsupp-based and the set-based standard simplex
on `Fin (n + 1)`, given by the identity on coordinates. -/
noncomputable def simplexHomeo (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ _root_.stdSimplex ℝ (Fin (n + 1)) where
  toFun := toStdSimplex n
  invFun := ofStdSimplex n
  left_inv := ofStdSimplex_toStdSimplex n
  right_inv := toStdSimplex_ofStdSimplex n
  continuous_toFun := continuous_toStdSimplex n
  continuous_invFun := continuous_ofStdSimplex n

@[simp]
theorem simplexHomeo_apply (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ((simplexHomeo n w : _root_.stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) i = w.weights i :=
  rfl

theorem toStdSimplex_map (m n : ℕ) (f : Fin (m + 1) → Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    toStdSimplex n (Convexity.StdSimplex.map f w) = _root_.stdSimplex.map f (toStdSimplex m w) := by
  apply Subtype.ext
  funext j
  change (Convexity.StdSimplex.map f w).weights j =
      ((_root_.stdSimplex.map f (toStdSimplex m w) : _root_.stdSimplex ℝ (Fin (n + 1))) :
        Fin (n + 1) → ℝ) j
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype]
  simp only [_root_.stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, toStdSimplex_coe]

theorem simplexHomeo_map (m n : ℕ) (f : Fin (m + 1) → Fin (n + 1))
    (w : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    simplexHomeo n (Convexity.StdSimplex.map f w) = _root_.stdSimplex.map f (simplexHomeo m w) := by
  show toStdSimplex n (Convexity.StdSimplex.map f w) = _root_.stdSimplex.map f (toStdSimplex m w)
  exact toStdSimplex_map m n f w

theorem SimplexShimHomeo :
    ∃ e : ∀ n : ℕ, Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ _root_.stdSimplex ℝ (Fin (n + 1)),
      (∀ (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)),
        (((e n w : _root_.stdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) → ℝ) i = w.weights i)) ∧
      (∀ (m n : ℕ) (f : Fin (m + 1) → Fin (n + 1))
        (w : Convexity.StdSimplex ℝ (Fin (m + 1))),
        e n (Convexity.StdSimplex.map f w) = _root_.stdSimplex.map f (e m w)) :=
  ⟨fun n => simplexHomeo n, fun n w i => simplexHomeo_apply n w i,
    fun m n f w => simplexHomeo_map m n f w⟩

end Work.Homology
