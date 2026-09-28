import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# Auxiliary lattice facts for `Work.HP.FM3.transf_extreme`

Basic lemmas about discrete `ℤ`-submodules `L ⊆ ℝ^ι` used by the transference proof:

* `rank_finrank_discrete`: `finrank ℤ L = rkR L` for a discrete `L` (the `ℤ`-rank equals the
  dimension of the real span);
* `secLat_discrete`: the section `L ∩ v^⊥` of a discrete lattice is discrete;
* `dotR_eq_zero_of_forall_mem`: a vector of the real span of `L` that pairs to zero with all of
  `L` must vanish.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

/-- For a discrete `ℤ`-submodule `L ⊆ ℝ^ι`, the `ℤ`-rank of `L` equals the dimension of its real
span. -/
theorem rank_finrank_discrete (L : Submodule ℤ (ι → ℝ)) (h : DiscreteTopology ↥L) :
    Module.finrank ℤ ↥L = rkR L := by
  letI := h
  have h1 := Real.finrank_eq_int_finrank_of_discrete (s := (L : Set (ι → ℝ)))
    (by rw [Submodule.span_eq]; exact h)
  rw [Set.finrank, Set.finrank, Submodule.span_eq] at h1
  exact h1.symm

/-- The section `L ∩ v^⊥` of a discrete lattice is discrete. -/
theorem secLat_discrete (L : Submodule ℤ (ι → ℝ)) (h : DiscreteTopology ↥L) (v : ι → ℝ) :
    DiscreteTopology ↥(secLat v L) := by
  letI := h
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ↥(secLat v L) => (⟨(x : ι → ℝ), x.2.1⟩ : ↥L)) ?_ ?_
  · exact (continuous_subtype_val).subtype_mk _
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z : ↥L => (z : ι → ℝ)) hxy)

/-- A vector of the real span of `L` that pairs to zero with every element of `L` is zero. -/
theorem dotR_eq_zero_of_forall_mem {L : Submodule ℤ (ι → ℝ)} {v : ι → ℝ}
    (h : ∀ z ∈ L, dotR v z = 0) (hv : v ∈ Submodule.span ℝ (L : Set (ι → ℝ))) : v = 0 := by
  have hself : dotR v v = 0 := by
    refine Submodule.span_induction (p := fun x _ => dotR v x = 0) (fun x hx => h x hx) ?_ ?_ ?_ hv
    · simp
    · intro x y _ _ hx hy; rw [dotR_add_right, hx, hy, add_zero]
    · intro c x _ hx; rw [dotR_smul_right, hx, mul_zero]
  exact dotR_self_eq_zero.mp hself

end Work.HP.FM3
