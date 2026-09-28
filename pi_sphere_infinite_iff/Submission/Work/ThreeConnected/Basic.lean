import Submission.Work.Surgery.SurgicalRoute

/-!
# Step 1 of the dimension-`8` signature theorem: the `3`-connected reduction

This is the first module of the subproject `Submission/Work/ThreeConnected/`, which attacks **Step 1**
of the surgical proof of the dimension-`8` Hirzebruch congruence
(`Submission/NOTES.md` §8.4, §15.8, §15.12): the reduction of an arbitrary closed oriented smooth
`8`-manifold to a `3`-connected one by surgery below the middle dimension.

The chapter is built in the model of `Submission/Work/Bordism/`: a closed oriented `n`-manifold is a
pair `(X, c)` of a space and a fundamental class, and all statements are made about its integral
homology `H_k(X;ℤ)` computed by the singular chain complex of `Submission/Work/Cohomology/`.

## What is in this file

* `Work.ThreeConnected.Hom` — the `k`-th homology of a closed oriented manifold, bundled as a
  `ModuleCat ℤ` (so that `IsZero` can be applied to it, as in `Work.Surgery.IsConnectedUpTo`);
* the API of the connectivity predicate `Work.Surgery.IsConnectedUpTo`:
  `Work.ThreeConnected.isConnectedUpTo_mono` (connectivity is monotone in the degree),
  `Work.ThreeConnected.isConnectedUpTo_zero` (every manifold is `0`-connected),
  `Work.ThreeConnected.isZero_hom_of_isConnectedUpTo` (the definition, unfolded),
  `Work.ThreeConnected.isConnectedUpTo_of_isZero` (the converse, degree by degree), and
  `Work.ThreeConnected.isConnectedUpTo_iff` (the two together);
* `Work.ThreeConnected.isThreeConnected_iff` — `3`-connectivity as the vanishing of `H₁`, `H₂`,
  `H₃`, and its degreewise form.

The notions `Work.Surgery.IsConnectedUpTo` and `Work.Surgery.IsThreeConnected` are *not* redeclared
here: this chapter imports them, so that the conclusions it reaches are conclusions about the same
predicates that `Work.Surgery.Family8.GeometricSurgicalReduction` asks for.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology ContDiff
open CategoryTheory CategoryTheory.Limits

namespace Work.ThreeConnected

open Work.Bordism Work.Surgery Work.SignatureBordism Work.Cohomology

noncomputable section

variable {n : ℕ}

/-- The `k`-th integral homology `H_k(M;ℤ)` of a closed oriented `n`-manifold, as an object of
`ModuleCat ℤ`. -/
abbrev Hom (M : ClosedOriented n) (k : ℕ) : ModuleCat ℤ :=
  (chainC ℤ (TopCat.toSSet.obj M.X)).homology k

/-- **`IsZero` of a homology object is subsingleton-ness of the underlying module**: this is the
bridge between the categorical form in which `Work.Surgery.IsConnectedUpTo` is stated and the
linear-algebraic form in which the surgery effect is stated. -/
theorem isZero_hom_iff (M : ClosedOriented n) (k : ℕ) :
    IsZero (Hom M k) ↔ Subsingleton (M.hom k) :=
  ModuleCat.isZero_iff_subsingleton

theorem isZero_hom_of_subsingleton {M : ClosedOriented n} {k : ℕ} (h : Subsingleton (M.hom k)) :
    IsZero (Hom M k) :=
  (isZero_hom_iff M k).mpr h

theorem subsingleton_of_isZero_hom {M : ClosedOriented n} {k : ℕ} (h : IsZero (Hom M k)) :
    Subsingleton (M.hom k) :=
  (isZero_hom_iff M k).mp h

/-- The **singular simplicial set** of the underlying space of a closed oriented manifold: the
object on which the cohomology of `Submission/Work/Cohomology/` is computed. -/
abbrev singSSet {n : ℕ} (M : ClosedOriented n) : SSet.{0} := TopCat.toSSet.obj M.X

/-- The **rationalised cohomology** `H^k(M;ℤ) ⊗[ℤ] ℚ` of a closed oriented `n`-manifold, as a
`Type` (the carrier of the middle intersection form). -/
abbrev ratCoh {n : ℕ} (M : ClosedOriented n) (k : ℕ) : Type :=
  Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj M.X)

/-- The **middle intersection form** of a closed oriented `2k`-manifold, restated. -/
abbrev MidForm {k : ℕ} (M : ClosedOriented (k + k)) : QuadraticForm ℚ (ratCoh M k) :=
  Work.Bordism.midForm M

/-- **Finite generation of the homology of a closed oriented manifold in every degree.**  For a
genuine closed oriented smooth manifold this is the compactness of the manifold (a compact manifold
has finitely generated homology, by a finite handle decomposition or by the finiteness of the
singular chain complex of a finite triangulation).  It is recorded as a hypothesis here; the
killing iteration of `Work.ThreeConnected` needs it in degree `k`. -/
def FiniteHomology (M : ClosedOriented n) : Prop := ∀ j : ℕ, Module.Finite ℤ (M.hom j)

theorem finiteHomology_of_finite (M : ClosedOriented n)
    (h : ∀ j : ℕ, Module.Finite ℤ (M.hom j)) : FiniteHomology M := h

/-! ## Connectivity -/

/-- The definition of `Work.Surgery.IsConnectedUpTo`, unfolded: connectivity up to degree `k` is the
vanishing of `H₁, …, H_k`. -/
theorem isConnectedUpTo_iff (k : ℕ) (M : ClosedOriented n) :
    IsConnectedUpTo k M ↔ ∀ i, 1 ≤ i → i ≤ k → IsZero (Hom M i) := by
  refine Iff.rfl

/-- **Connectivity is monotone in the degree.** -/
theorem isConnectedUpTo_mono {j k : ℕ} (hjk : j ≤ k) {M : ClosedOriented n}
    (h : IsConnectedUpTo k M) : IsConnectedUpTo j M :=
  fun i hi hij => h i hi (le_trans hij hjk)

/-- **Every manifold is `0`-connected**: the condition is vacuous. -/
theorem isConnectedUpTo_zero (M : ClosedOriented n) : IsConnectedUpTo 0 M :=
  fun i hi h0 => absurd h0 (by omega)

/-- The vanishing form of `k`-connectivity, degree by degree. -/
theorem isZero_hom_of_isConnectedUpTo (k : ℕ) {M : ClosedOriented n}
    (h : IsConnectedUpTo k M) {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) : IsZero (Hom M i) :=
  h i hi hik

/-- **The converse**: a manifold whose homology vanishes in degrees `1, …, k` is `k`-connected. -/
theorem isConnectedUpTo_of_isZero (k : ℕ) {M : ClosedOriented n}
    (h : ∀ i, 1 ≤ i → i ≤ k → IsZero (Hom M i)) : IsConnectedUpTo k M :=
  h

/-- **`3`-connectivity is the vanishing of `H₁`, `H₂`, `H₃`.** -/
theorem isThreeConnected_iff (M : ClosedOriented 8) :
    IsThreeConnected M ↔
      (IsZero (Hom M 1) ∧ IsZero (Hom M 2) ∧ IsZero (Hom M 3)) := by
  constructor
  · intro h
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) le_rfl⟩
  · rintro ⟨h1, h2, h3⟩ i hi hik
    interval_cases i
    · exact h1
    · exact h2
    · exact h3

/-- `3`-connectivity expressed as the vanishing of the three homology groups. -/
theorem isThreeConnected_iff_subsingleton (M : ClosedOriented 8) :
    IsThreeConnected M ↔
      (Subsingleton (M.hom 1) ∧ Subsingleton (M.hom 2) ∧ Subsingleton (M.hom 3)) := by
  rw [isThreeConnected_iff]
  exact and_congr (isZero_hom_iff M 1) (and_congr (isZero_hom_iff M 2) (isZero_hom_iff M 3))

/-- `IsConnectedUpTo` only depends on the manifold as a `ClosedOriented` datum, and hence transports
along an equality of the underlying data. -/
theorem isConnectedUpTo_congr {M M' : ClosedOriented n} (h : M = M') {k : ℕ} :
    IsConnectedUpTo k M ↔ IsConnectedUpTo k M' := by
  rw [h]

end

end Work.ThreeConnected
