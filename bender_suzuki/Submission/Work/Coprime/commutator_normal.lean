/-
The commutator `[G, A] = FT.commutator A ⊤` of the whole group with the acting group is a
normal subgroup of `G`.

The generating set is `S = {x⁻¹ * (a • x) | a : A, x : G}`.  For a generator
`P = y⁻¹ * (a • y)` and an arbitrary `g : G` one has the identity
`g * (y⁻¹ * (a • y)) * g⁻¹
   = ((y * g⁻¹)⁻¹ * (a • (y * g⁻¹))) * ((g⁻¹)⁻¹ * (a • g⁻¹))⁻¹`,
a product of two generators (with witnesses `y * g⁻¹` and `g⁻¹`).  Hence conjugation by `g`
maps the generating set into `[G, A]`, and therefore maps `[G, A]` into itself, i.e.
`[G, A] ⊴ G`.
-/
import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coprime

open scoped Pointwise

/-- The set of "coprime commutators" generating `[H, A]`. -/
def commutatorGens (A : Type*) {G : Type*} [Group A] [Group G] [MulDistribMulAction A G]
    (H : Subgroup G) : Set G :=
  {y : G | ∃ a : A, ∃ x ∈ H, y = x⁻¹ * (a • x)}

theorem commutator_eq_closure (A : Type*) {G : Type*} [Group A] [Group G]
    [MulDistribMulAction A G] (H : Subgroup G) :
    FT.commutator A H = Subgroup.closure (commutatorGens A H) := rfl

/-- Conjugating a generator `y⁻¹ * (a • y)` by `g` again lies in `[G, A]`. -/
theorem conj_mem_commutatorGens {G : Type*} [Group G] {A : Type*} [Group A]
    [MulDistribMulAction A G] (a : A) (y g : G) :
    g * (y⁻¹ * (a • y)) * g⁻¹ ∈ FT.commutator A (⊤ : Subgroup G) := by
  have h1 : (y * g⁻¹)⁻¹ * (a • (y * g⁻¹)) ∈ FT.commutator A (⊤ : Subgroup G) :=
    FT.le_commutator a (Subgroup.mem_top _)
  have h2 : ((g⁻¹)⁻¹ * (a • g⁻¹))⁻¹ ∈ FT.commutator A (⊤ : Subgroup G) :=
    Subgroup.inv_mem _ (FT.le_commutator a (Subgroup.mem_top _))
  rw [show g * (y⁻¹ * (a • y)) * g⁻¹
      = ((y * g⁻¹)⁻¹ * (a • (y * g⁻¹))) * ((g⁻¹)⁻¹ * (a • g⁻¹))⁻¹ from by
    rw [smul_mul', smul_inv']
    group]
  exact Subgroup.mul_mem _ h1 h2

/-- `[G, A]` is normalised by `G`, i.e. it is a normal subgroup of `G`. -/
theorem commutator_normal (A : Type*) {G : Type*} [Group A] [Group G] [MulDistribMulAction A G] :
    (FT.commutator A (⊤ : Subgroup G)).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  refine Subgroup.closure_induction
    (k := commutatorGens A (⊤ : Subgroup G))
    (p := fun n _ => g * n * g⁻¹ ∈ FT.commutator A (⊤ : Subgroup G)) ?_ ?_ ?_ ?_ hn
  · intro x hx
    obtain ⟨a, y, -, rfl⟩ := hx
    exact conj_mem_commutatorGens a y g
  · simp
  · intro x y hx hy ihx ihy
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) from by group]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x hx ih
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ from by group]
    exact Subgroup.inv_mem _ ih

end Work.Coprime
