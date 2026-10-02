import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.CoordGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign of a cell reading

For the pinch (`glue_class_of_collapse`) the reading of a based cube on a box of a grid is a
composition `q ∘ c` where `c : I^n → I^n` changes each coordinate by its own map
`ψ i : I → I`.  This file shows that only the *endpoints* matter:

* `cl_coordUpd` (in `CoordGen.lean`): a coordinate map fixing `0` and `1` does not change the class;
* `cl_coordUpd_swap`: a coordinate map *interchanging* `0` and `1` inverts the class.

Hence for a coordinatewise map whose `i`-th component fixes (resp. swaps) the endpoints the class
is multiplied by `(+1)^{#fixing} (-1)^{#swapping}` — this is the whole sign content of the
arrangement computation, and it needs no degree theory.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The reversal of the unit interval, as a continuous map. -/
def revC : C(unitInterval, unitInterval) :=
  ⟨unitInterval.symm, unitInterval.continuous_symm⟩

@[simp] theorem revC_apply (s : unitInterval) : revC s = unitInterval.symm s := rfl

theorem revC_zero : revC (0 : unitInterval) = 1 := by
  show unitInterval.symm (0 : unitInterval) = 1
  simp

theorem revC_one : revC (1 : unitInterval) = 0 := by
  show unitInterval.symm (1 : unitInterval) = 0
  simp

/-- `coordUpd` preserves the boundary as soon as the coordinate map sends `{0,1}` into `{0,1}`. -/
theorem coordUpd_mem_boundary' {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0 ∨ ψ 0 = 1) (h1 : ψ 1 = 0 ∨ ψ 1 = 1) {u : IC n}
    (hu : u ∈ Cube.boundary (Fin n)) : coordUpd n i ψ u ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj | hj⟩ := hu
  · by_cases hji : j = i
    · subst j
      rcases h0 with h | h
      · exact ⟨i, Or.inl (by rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj, h])⟩
      · exact ⟨i, Or.inr (by rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj, h])⟩
    · exact ⟨j, Or.inl (by rw [coordUpd_apply, Function.update_apply, if_neg hji, hj])⟩
  · by_cases hji : j = i
    · subst j
      rcases h1 with h | h
      · exact ⟨i, Or.inl (by rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj, h])⟩
      · exact ⟨i, Or.inr (by rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj, h])⟩
    · exact ⟨j, Or.inr (by rw [coordUpd_apply, Function.update_apply, if_neg hji, hj])⟩

/-- The based cube obtained from `p` by reversing coordinate `i`. -/
def revCube {n : ℕ} (i : Fin n) (p : GenLoop (Fin n) X x₀) : GenLoop (Fin n) X x₀ :=
  ⟨p.1.comp (coordUpd n i revC),
    fun u hu => p.2 _ (coordUpd_mem_boundary' i revC (Or.inr revC_zero) (Or.inl revC_one) hu)⟩

theorem revCube_eq_symmAt {n : ℕ} (i : Fin n) (p : GenLoop (Fin n) X x₀) :
    revCube i p = GenLoop.symmAt i p := by
  refine Subtype.ext (ContinuousMap.ext fun u => ?_)
  show p.1 (Function.update u i (unitInterval.symm (u i)))
      = p.1 (fun j => if j = i then unitInterval.symm (u i) else u j)
  congr 1
  exact (by ext j; rw [Function.update_apply])

theorem revCube_class {n : ℕ} [NeZero n] (i : Fin n) (p : GenLoop (Fin n) X x₀) :
    cl n X x₀ (revCube i p) = (cl n X x₀ p)⁻¹ := by
  rw [revCube_eq_symmAt, cl_symmAt']

/-- **The swap lemma**: a coordinate map interchanging `0` and `1` inverts the class. -/
theorem cl_coordUpd_swap {n : ℕ} [NeZero n] (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 1) (h1 : ψ 1 = 0) (p : GenLoop (Fin n) X x₀) :
    cl n X x₀ ⟨p.1.comp (coordUpd n i ψ),
        fun u hu => p.2 _ (coordUpd_mem_boundary' i ψ (Or.inr h0) (Or.inl h1) hu)⟩
      = (cl n X x₀ p)⁻¹ := by
  set ψ' : C(unitInterval, unitInterval) := revC.comp ψ with hψ'
  have h0' : ψ' 0 = 0 := by rw [hψ', ContinuousMap.comp_apply, h0, revC_one]
  have h1' : ψ' 1 = 1 := by rw [hψ', ContinuousMap.comp_apply, h1, revC_zero]
  have hcomp : coordUpd n i ψ = (coordUpd n i revC).comp (coordUpd n i ψ') := by
    ext u j
    by_cases hji : j = i
    · subst hji
      rw [coordUpd_apply_self, ContinuousMap.comp_apply, coordUpd_apply_self,
        coordUpd_apply_self, hψ', ContinuousMap.comp_apply]
      simp only [revC_apply, unitInterval.symm_symm]
    · rw [coordUpd_apply_of_ne _ _ _ hji, ContinuousMap.comp_apply,
        coordUpd_apply_of_ne _ _ _ hji, coordUpd_apply_of_ne _ _ _ hji]
  have heq : (⟨p.1.comp (coordUpd n i ψ),
        fun u hu => p.2 _ (coordUpd_mem_boundary' i ψ (Or.inr h0) (Or.inl h1) hu)⟩ :
        GenLoop (Fin n) X x₀)
      = ⟨(revCube i p).1.comp (coordUpd n i ψ'),
          fun u hu => (revCube i p).2 _ (coordUpd_mem_boundary i ψ' h0' h1' hu)⟩ := by
    refine Subtype.ext (ContinuousMap.ext fun u => ?_)
    show p.1 (coordUpd n i ψ u)
        = p.1 ((coordUpd n i revC).comp (coordUpd n i ψ') u)
    rw [← hcomp]
  rw [heq]
  exact (cl_coordUpd (n := n) i ψ' h0' h1' (revCube i p)).trans (revCube_class i p)

end

end Work.RatHurewicz
