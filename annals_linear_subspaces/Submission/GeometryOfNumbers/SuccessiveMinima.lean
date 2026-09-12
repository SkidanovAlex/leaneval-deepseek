import Mathlib

/-!
# Successive minima of a full-rank `ℤ`-lattice

We define the successive minima `λ₁ ≤ λ₂ ≤ ⋯ ≤ λ_{dim E}` of a full-rank discrete
`ℤ`-submodule of a finite-dimensional real normed space, following the classical
definition:

`λᵢ(L) = inf { r ≥ 0 | L ∩ closedBall 0 r contains i linearly independent vectors }`.

All results in this file are Mathlib-only, so they can later be promoted to the shared
commons.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module
open scoped ENNReal
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of radii appearing in the definition of the `i`-th successive minimum. -/
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


/- TODO (next stretch): Minkowski first theorem corollaries, using
   MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
   with a `Submodule`-to-`AddSubgroup` transport of the fundamental domain. -/

/-- **Sheared successive minima (upper)**: if the ball of radius `R` in `L` contains `i`
`ℤ`-independent points and the linear map `g` expands norms by at most `M`
(`0 ≤ M`), then the image lattice `g(L)` has `i`-th successive minimum at most `M·R`.
Proof: the image of the witness family is still `ℤ`-independent (`LinearIndependent.map'`
through the injective `g`), and its norms are at most `M·R`. -/
lemma successiveMinimum_image_le_of_bound (g : E →ₗ[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ x : E, ‖g x‖ ≤ M * ‖x‖) (hginj : Function.Injective g)
    (L : Submodule ℤ E) (i : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (f : Fin i → L)
    (hlin : LinearIndependent ℤ (fun j : Fin i => (f j : E)))
    (hnorm : ∀ j : Fin i, ‖(f j : E)‖ ≤ R) :
    successiveMinimum (L.map (g.restrictScalars ℤ)) i ≤ M * R := by
  let Lg : Submodule ℤ E := L.map (g.restrictScalars ℤ)
  let fg : Fin i → Lg := fun j => ⟨(g.restrictScalars ℤ) (f j : E),
    Submodule.mem_map.mpr ⟨(f j : E), (f j).2, rfl⟩⟩
  have hlin_g : LinearIndependent ℤ (fun j : Fin i => ((fg j : Lg) : E)) := by
    dsimp [fg]
    have hker : LinearMap.ker (g.restrictScalars ℤ) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      simpa using hginj
    exact LinearIndependent.map' hlin (g.restrictScalars ℤ) hker
  have hnorm_g : ∀ j : Fin i, ‖((fg j : Lg) : E)‖ ≤ M * R := by
    intro j
    calc
      ‖(g.restrictScalars ℤ) ((f j : E))‖ ≤ M * ‖(f j : E)‖ := by
            simpa using hg ((f j : E))
      _ ≤ M * R := mul_le_mul_of_nonneg_left (hnorm j) hM
  exact successiveMinimum_le_of_exists Lg i (mul_nonneg hM hR) fg hlin_g hnorm_g



/-- **Sheared successive minima (lower / pull-back)**: if the image lattice `g(L)` has `i`
`ℤ`-independent points in the ball of radius `R` and `g` distorts norms by no more than
`M` in the sense `‖x‖ ≤ M·‖g x‖`, then `L` has its `i`-th successive minimum at most
`M·R`.  Proof: pull each image point back through `g` (`Submodule.mem_map`), the pulled
family is `ℤ`-independent (`LinearIndependent.of_comp` through `g`), and its norms are at
most `M·R`. -/
lemma successiveMinimum_le_image_of_bound (g : E →ₗ[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ x : E, ‖x‖ ≤ M * ‖g x‖)
    (L : Submodule ℤ E) (i : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (f : Fin i → L.map (g.restrictScalars ℤ))
    (hlin : LinearIndependent ℤ (fun j : Fin i => ((f j : L.map (g.restrictScalars ℤ)) : E)))
    (hnorm : ∀ j : Fin i, ‖((f j : L.map (g.restrictScalars ℤ)) : E)‖ ≤ R) :
    successiveMinimum L i ≤ M * R := by
  classical
  let fp : Fin i → L := fun j =>
    ⟨Classical.choose (Submodule.mem_map.mp (f j).2), (Classical.choose_spec (Submodule.mem_map.mp (f j).2)).1⟩
  have hf_eq : ∀ j : Fin i, (g.restrictScalars ℤ) ((fp j : L) : E) = (f j : E) := by
    intro j
    dsimp [fp]
    exact (Classical.choose_spec (Submodule.mem_map.mp (f j).2)).2
  have hlin_p : LinearIndependent ℤ (fun j : Fin i => ((fp j : L) : E)) := by
    dsimp [fp]
    -- (g ∘ fp) = f as E-valued families, and f is LI, so fp is LI (of_comp)
    apply LinearIndependent.of_comp (g.restrictScalars ℤ)
    -- need: LI (fun j => (g.restrictScalars ℤ) ((fp j : L) : E)): equals LI of (f j : E)
    convert hlin using 1
    funext j
    exact hf_eq j
  have hnorm_p : ∀ j : Fin i, ‖((fp j : L) : E)‖ ≤ M * R := by
    intro j
    calc
      ‖((fp j : L) : E)‖ ≤ M * ‖(g.restrictScalars ℤ) ((fp j : L) : E)‖ := by
            simpa using hg ((fp j : L) : E)
      _ = M * ‖(f j : E)‖ := by rw [hf_eq j]
      _ ≤ M * R := mul_le_mul_of_nonneg_left (hnorm j) hM
  exact successiveMinimum_le_of_exists L i (mul_nonneg hM hR) fp hlin_p hnorm_p

