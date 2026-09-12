import Mathlib

/-!
# Successive minima of a full-rank `ℤ`-lattice (shared commons)

Successive minima of a discrete full-rank `ℤ`-submodule `L` of a finite-dimensional real
normed space `E`, following the classical definition:

`λᵢ(L) = sInf { r ≥ 0 | ∃ f : Fin i → L, LinearIndependent ℤ (fun j => (f j : E)) ∧
                  ∀ j, ‖(f j : E)‖ ≤ r }`

(the infimum of all radii `r` such that the closed ball of radius `r` around `0` contains `i`
`ℤ`-linearly independent elements of `L`).  This module provides the definition and the
basic API used by the geometry-of-numbers results (Minkowski's first/second theorems, model
successive minima of diagonal flows):

- `successiveMinimumSet` / `successiveMinimum` (the definition, as an `sInf` over radii);
- `bddBelow_successiveMinimumSet`, `nonempty_successiveMinimumSet`,
  `successiveMinimumSet_nonempty_of_exists_linearIndependent` (nonemptyness),
  `successiveMinimum_nonneg`, `successiveMinimum_le_of_exists`, `successiveMinimum_mono`
  (monotonicity in the index);
- realisation: `upwardClosed_successiveMinimumSet`,
  `mem_successiveMinimumSet_of_sInf_lt`,
  `exists_linearIndependent_of_successiveMinimum_lt` (radii strictly above `λᵢ` contain `i`
  independent lattice points), `first_successiveMinimum_le_of_mem`;
- uniform lower bound: `successiveMinimum_ge_of_forall_ne_zero_norm_ge` (if every nonzero
  lattice point has norm `≥ m`, then `m ≤ λᵢ` for every `1 ≤ i`).

All declarations are Mathlib-only.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module
open scoped ENNReal
set_option linter.unusedSectionVars false

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def successiveMinimumSet (L : Submodule ℤ E) (i : ℕ) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧
    ∃ f : Fin i → L, LinearIndependent ℤ (fun j : Fin i => (f j : E)) ∧
      ∀ j : Fin i, ‖(f j : E)‖ ≤ r}

/-- The `i`-th successive minimum of the full-rank discrete lattice `L ≤ E`:
the infimum of all radii `r` such that the ball of radius `r` contains `i`
`ℤ`-linearly independent elements of `L`. -/
def successiveMinimum (L : Submodule ℤ E) (i : ℕ) : ℝ :=
  sInf (successiveMinimumSet L i)

/-- The defining set of `successiveMinimum` is bounded below by `0`. -/
lemma bddBelow_successiveMinimumSet (L : Submodule ℤ E) (i : ℕ) :
    BddBelow (successiveMinimumSet L i) := by
  refine ⟨0, ?_⟩
  rintro r ⟨hr, _⟩
  exact hr

/-- The set used to define the `i`-th successive minimum is nonempty whenever `i` is at most
the rank of the ambient space.  (Any full lattice has rank `finrank ℝ E`.) -/
lemma nonempty_successiveMinimumSet (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ) (hi : i ≤ Module.finrank ℤ L) :
    (successiveMinimumSet L i).Nonempty := by
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let n : ℕ := Module.finrank ℤ L
  let b : Module.Basis (Fin n) ℤ L := Module.finBasis ℤ L
  let v : Fin n → E := fun k => (b k : E)
  have hb : LinearIndependent ℤ v := by
    exact LinearIndependent.map' b.linearIndependent L.subtype (Submodule.ker_subtype L)
  let e : Fin i ↪ Fin n := Fin.castLEEmb hi
  let f : Fin i → L := fun a => b (e a)
  have hnormsum : ∀ k : Fin n, ‖v k‖ ≤ ∑ l : Fin n, ‖v l‖ := by
    intro k
    exact Finset.single_le_sum (s := Finset.univ) (fun l _ => norm_nonneg _)
      (Finset.mem_univ (α := Fin n) k)
  refine ⟨∑ l : Fin n, ‖v l‖, ?_⟩
  constructor
  · exact Finset.sum_nonneg (fun l _ => norm_nonneg _)
  refine ⟨f, ?_, ?_⟩
  · -- the chosen subfamily of the ℤ-basis is still ℤ-linearly independent
    exact (hb.comp e e.injective)
  · intro a
    exact hnormsum (e a)

/-- Successive minima are nonnegative. -/
lemma successiveMinimum_nonneg (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ) (hi : i ≤ Module.finrank ℤ L) : 0 ≤ successiveMinimum L i := by
  unfold successiveMinimum
  exact le_csInf (nonempty_successiveMinimumSet L i hi) (by rintro r ⟨hr, _⟩; exact hr)

/-- If the ball of radius `r` contains `i` linearly independent lattice points, then
`λᵢ ≤ r`. -/
lemma successiveMinimum_le_of_exists (L : Submodule ℤ E) (i : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (f : Fin i → L)
    (hlin : LinearIndependent ℤ (fun j : Fin i => (f j : E)))
    (hnorm : ∀ j : Fin i, ‖(f j : E)‖ ≤ r) :
    successiveMinimum L i ≤ r := by
  unfold successiveMinimum successiveMinimumSet
  exact csInf_le (bddBelow_successiveMinimumSet L i) ⟨hr, f, hlin, hnorm⟩

/-- Successive minima are nondecreasing in the index: if `i ≤ j`, then `λᵢ ≤ λⱼ`.
A family of `j` independent points contains an independent subfamily of size `i`
(the restriction to the first `i` coordinates). -/
lemma successiveMinimum_mono (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Module.finrank ℤ L) :
    successiveMinimum L i ≤ successiveMinimum L j := by
  unfold successiveMinimum
  apply le_csInf (nonempty_successiveMinimumSet L j hj)
  rintro r ⟨hr, f, hlin, hnorm⟩
  let e : Fin i ↪ Fin j := Fin.castLEEmb hij
  exact successiveMinimum_le_of_exists L i hr (fun a => f (e a))
    (by exact hlin.comp e e.injective)
    (fun a => hnorm (e a))

lemma upwardClosed_successiveMinimumSet (L : Submodule ℤ E) (i : ℕ) {r r' : ℝ}
    (hr : r ∈ successiveMinimumSet L i) (hrr' : r ≤ r') :
    r' ∈ successiveMinimumSet L i := by
  rcases hr with ⟨hr0, f, hlin, hnorm⟩
  refine ⟨le_trans hr0 hrr', f, hlin, fun j => le_trans (hnorm j) hrr'⟩

/-- The defining set of the `i`-th successive minimum contains every radius strictly above
the infimum (provided the set is nonempty). -/
lemma mem_successiveMinimumSet_of_sInf_lt (L : Submodule ℤ E) (i : ℕ) {r : ℝ}
    (hr : successiveMinimum L i < r) (hS : (successiveMinimumSet L i).Nonempty) :
    r ∈ successiveMinimumSet L i := by
  -- `r` is not a lower bound of the set (otherwise `sInf ≥ r`), so some `s ∈ S` has `s < r`,
  -- and upward closedness then gives `r ∈ S`.
  by_contra hrS
  have hlb : ∀ s ∈ successiveMinimumSet L i, r ≤ s := by
    intro s hs
    by_contra hlt
    exact hrS (upwardClosed_successiveMinimumSet L i hs (le_of_lt (lt_of_not_ge hlt)))
  have hinf : r ≤ sInf (successiveMinimumSet L i) := le_csInf hS hlb
  exact (not_lt_of_ge hinf) hr

/-- If `r > λᵢ(L)`, then the closed ball of radius `r` contains `i` `ℤ`-linearly independent
elements of `L`. This is the standard "realisation" property of the successive minima. -/
lemma exists_linearIndependent_of_successiveMinimum_lt (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (i : ℕ) (hi : i ≤ Module.finrank ℤ L) {r : ℝ}
    (hr : successiveMinimum L i < r) :
    ∃ f : Fin i → L, LinearIndependent ℤ (fun j : Fin i => (f j : E)) ∧
      ∀ j : Fin i, ‖(f j : E)‖ ≤ r := by
  have hmem : r ∈ successiveMinimumSet L i :=
    mem_successiveMinimumSet_of_sInf_lt L i hr (nonempty_successiveMinimumSet L i hi)
  exact hmem.2

/-- Any nonzero lattice point `v` satisfies `λ₁(L) ≤ ‖v‖`. -/
lemma first_successiveMinimum_le_of_mem {L : Submodule ℤ E} (v : L) (hv : v ≠ 0) :
    successiveMinimum L 1 ≤ ‖(v : E)‖ := by
  have hvE : (v : E) ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    exact h
  haveI : Module.IsTorsionFree ℤ E := by
    refine Module.IsTorsionFree.of_smul_eq_zero (R := ℤ) (M := E) ?_
    intro z m hm
    rw [← Int.cast_smul_eq_zsmul ℝ z m] at hm
    rcases (smul_eq_zero.mp hm) with hz | hm
    · exact Or.inl (Int.cast_eq_zero.mp hz)
    · exact Or.inr hm
  refine successiveMinimum_le_of_exists L 1 (norm_nonneg _) (fun _ : Fin 1 => v) ?_
    (by intro j; simp)
  exact (linearIndependent_subsingleton_index_iff (f := fun _ : Fin 1 => (v : E))).2
    (by intro i; exact hvE)



/-- **Lower bound on `λᵢ` from a uniform lower bound on nonzero lattice points**:
if every nonzero lattice point has norm `≥ m`, then the `i`-th successive minimum satisfies
`m ≤ λᵢ` for every `1 ≤ i` (with `hS` the nonemptyness of the defining set). -/
lemma successiveMinimum_ge_of_forall_ne_zero_norm_ge (L : Submodule ℤ E) (m : ℝ)
    {i : ℕ} (hi1 : 1 ≤ i) (hS : (successiveMinimumSet L i).Nonempty)
    (h : ∀ v : L, v ≠ 0 → m ≤ ‖(v : E)‖) : m ≤ successiveMinimum L i := by
  refine le_csInf hS ?_
  rintro r ⟨hr0, f, hlin, hnorm⟩
  have hi0 : 0 < i := by omega
  let j : Fin i := ⟨0, hi0⟩
  have hnz : (f j : E) ≠ 0 := hlin.ne_zero j
  have hfj : f j ≠ 0 := by
    intro hz
    apply hnz
    exact congrArg Subtype.val hz
  exact le_trans (h (f j) hfj) (hnorm j)

/-- Nonemptyness of the defining set of `λᵢ` from an explicit family of `i` independent
lattice points of bounded norm. -/
lemma successiveMinimumSet_nonempty_of_exists_linearIndependent (L : Submodule ℤ E) (i : ℕ)
    (f : Fin i → L) (hlin : LinearIndependent ℤ (fun j : Fin i => (f j : E))) (R : ℝ)
    (hR : ∀ j : Fin i, ‖(f j : E)‖ ≤ R) (hR0 : 0 ≤ R) :
    (successiveMinimumSet L i).Nonempty := by
  refine ⟨R, hR0, f, hlin, hR⟩

end Commons.Lattice.SuccessiveMinima
