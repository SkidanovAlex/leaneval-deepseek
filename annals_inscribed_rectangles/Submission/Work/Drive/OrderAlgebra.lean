import Mathlib

/-!
# The `ZMod 2` algebra of the order: transitivity from the triple count

The chain route produces, for the "side" function `e : Zc γ → ZMod 2` of Hugelmeyer's order
(`e u = 1` iff `M ≺ u · M`), three kinds of input:

* **antisymmetry** (Hugelmeyer's Lemma 3): `e u + e (−u) = 1`, from the pair count
  `n_P + n_Q + n₀ ≡ 1` together with the multiplicativity of the intersection form on the cut surface
  (`Work.Drive.surf_intersection_form_line`);
* **the triple identity** (Hugelmeyer's Lemma 4): `n_P + n_Q + n_R ≡ 1` for a pairwise disjoint triple,
  from `Work.Drive.manifold_triple_inter_boundary_parity` together with the bottom-face computation and
  the seam cancellation (`ENDS_AND_SEAMS_NOTES.md`);
* **multiplicativity** (`Surf/ChainForm.lean`): `n_P = e (v−u) · e (w−u)` for the three planes
  `P = P_u, Q = P_v, R = P_w` of the triple, and cyclically — the count `n_P` is the intersection
  number of the two `1`-cycles `A_Q = P ∩ V_Q` and `A_R = P ∩ V_R` on the surface `P ≅ ℝP²`, which
  `(SURF)` computes as the product of the two pairings with the cut.

Putting the last two together for a triple with translation-invariant `e` (which is the rotation
invariance of the count) gives the functional identity

`e a · e (a+c) + e (−a) · e c + e (−(a+c)) · e (−c) = 1`  for `a, c, a + c ∈ Zc`,

and this file records the purely `ZMod 2` consequence: **together with antisymmetry it gives
transitivity**, i.e. `e a = e c = 1 → e (a+c) = 1`.  (Antisymmetry, not the triple identity, is what
rules out the trivial solution `e ≡ 1` of the functional identity.)
-/

namespace Work.Drive

/-- **Transitivity of the side function from the triple count and antisymmetry.**  If `e` is
antisymmetric on `Z` and satisfies the functional identity coming from the triple-intersection count,
then `e` is additive on triples of `Z` (Hugelmeyer's Lemma 4). -/
theorem e_add_of_triple {G : Type*} [AddCommGroup G] {Z : Set G} {e : G → ZMod 2}
    (hanti : ∀ u ∈ Z, e u + e (-u) = 1)
    (hT : ∀ a ∈ Z, ∀ c ∈ Z, a + c ∈ Z →
      e a * e (a + c) + e (-a) * e c + e (-(a + c)) * e (-c) = 1)
    {a c : G} (ha : a ∈ Z) (hc : c ∈ Z) (hac : a + c ∈ Z)
    (ha1 : e a = 1) (hc1 : e c = 1) : e (a + c) = 1 := by
  have h1 : e (-a) = 0 := by
    have h := hanti a ha
    rw [ha1] at h
    exact (add_left_inj 1).mp (by simpa using h)
  have h2 : e (-c) = 0 := by
    have h := hanti c hc
    rw [hc1] at h
    exact (add_left_inj 1).mp (by simpa using h)
  have h := hT a ha c hc hac
  rw [ha1, hc1, h1, h2] at h
  simpa using h

/-- The two consequences of antisymmetry used above: the side function of the negated angle is the
complement of the side function. -/
theorem e_neg_eq {G : Type*} [AddCommGroup G] {Z : Set G} {e : G → ZMod 2}
    (hanti : ∀ u ∈ Z, e u + e (-u) = 1) {u : G} (hu : u ∈ Z) :
    e (-u) = 1 - e u := by
  have h := hanti u hu
  rw [eq_sub_iff_add_eq, add_comm]
  exact h

end Work.Drive
