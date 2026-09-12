import Mathlib
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# A decomposable exterior vector determines the span of its factors

ROADMAP H1 (finite saturated hulls / covolume-spectrum discreteness) needs the
injectivity of the Plücker map `M ↦ ∧(a ℤ-basis of M)` on saturated rank-`r`
subgroups of a lattice: two `ℝ`-linearly independent families `u, v : Fin r → E`
with equal exterior products `ιMulti ℝ r u = ιMulti ℝ r v` span the same subspace.

The engine is the classical characterisation of the annihilator of a nonzero
decomposable `r`-vector by left exterior multiplication:

    `(ι x) * (ιMulti K r u) = 0  ⟺  x ∈ span (range u)`     (u linearly independent)

Proof route (all elementary, in `ExteriorAlgebra`):
1. `Fin.cons x u` is linearly independent when `u` is and `x ∉ span(range u)`
   (`linearIndependent_finCons`, Mathlib);
2. LI families give nonzero `ExteriorAlgebra.ιMulti`
   (fleet `Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent`
   + the coe/rfl bridge `exteriorPower.ιMulti_apply_coe`);
3. `ιMulti K (r+1) (Fin.cons x u) = (ι x) * ιMulti K r u`
   (`ExteriorAlgebra.ιMulti_succ_apply`);
4. contrapositively: `x ∉ span(range u)` ⟹ `(ι x) * ιMulti K r u ≠ 0`;
5. the converse (`x ∈ span` ⟹ product `= 0`) via `ιMulti_mul_ιMulti`: each
   `(ι (u j)) * ιMulti K r u = ιMulti K (1+r) (append ![(u j)] u) = 0` since the
   family repeats `u j`.

Then the span-equality theorem follows: from `∧u = ∧v`, each `v j` satisfies
`(ι (v j)) * ∧u = (ι (v j)) * ∧v = 0` (own factor), so `v j ∈ span(range u)`;
symmetrically.  All declarations are Mathlib-only apart from the single Commons
import; they live here (not in the Commons) because the exact statement shapes
are pinned by the H1 counting argument.
-/

noncomputable section

open Set Module
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.WedgeDeterminesSpan

open ExteriorAlgebra

/-- A linearly independent family plus a vector outside its span gives a linearly
independent `Fin.cons` family.  (Direct instantiation of Mathlib
`linearIndependent_finCons`; kept here for a stable name.) -/
lemma finCons_linearIndependent {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r : ℕ} (u : Fin r → E) (hu : LinearIndependent K u) (x : E)
    (hx : x ∉ Submodule.span K (Set.range u)) :
    LinearIndependent K (Fin.cons x u : Fin (r + 1) → E) :=
  (linearIndependent_finCons (K := K) (x := x) (v := u)).2 ⟨hu, hx⟩

/-- Linearly independent families give non-zero exterior products in the exterior
ALGEBRA (the ambient ring of the graded pieces). -/
lemma exteriorAlgebra_ιMulti_ne_zero_of_linearIndependent {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ} (v : Fin k → E)
    (hv : LinearIndependent K v) : ExteriorAlgebra.ιMulti K k v ≠ 0 := by
  have hne : exteriorPower.ιMulti K k v ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent v hv
  intro hz
  apply hne
  apply Subtype.ext
  simpa using hz

/-- Exterior product of a `Fin.cons` family = the head vector multiplied by the
product of the tail. -/
lemma ιMulti_finCons_eq_mul {K E : Type*} [CommRing K] [AddCommGroup E] [Module K E]
    {r : ℕ} (x : E) (u : Fin r → E) :
    ExteriorAlgebra.ιMulti K (r + 1) (Fin.cons x u : Fin (r + 1) → E) =
      ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K r u := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail]

/-- A vector outside the span of a linearly independent family multiplies the
corresponding exterior product to a non-zero element. -/
lemma exterior_mul_ιMulti_ne_zero_of_not_mem_span {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {r : ℕ} (u : Fin r → E) (hu : LinearIndependent K u)
    (x : E) (hx : x ∉ Submodule.span K (Set.range u)) :
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K r u ≠ 0 := by
  have hw : LinearIndependent K (Fin.cons x u : Fin (r + 1) → E) :=
    finCons_linearIndependent u hu x hx
  have hwne : ExteriorAlgebra.ιMulti K (r + 1) (Fin.cons x u : Fin (r + 1) → E) ≠ 0 :=
    exteriorAlgebra_ιMulti_ne_zero_of_linearIndependent (Fin.cons x u) hw
  have hid := ιMulti_finCons_eq_mul (K := K) (E := E) (r := r) x u
  -- hid : ιMulti (r+1) (cons x u) = ι x * ιMulti r u; but hwne mentions the cons family
  rw [hid] at hwne
  -- hwne : ι x * ιMulti r u ≠ 0? only after simplifying the tail of hid's LHS matches; done
  exact hwne

/-- The product of the exterior product of a family by one of its members vanishes
(repeated vector). -/
lemma exterior_mul_ιMulti_self_mem_eq_zero {K E : Type*} [CommRing K]
    [AddCommGroup E] [Module K E] {r : ℕ} (u : Fin r → E) (j : Fin r) :
    ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ιMulti K r u = 0 := by
  let a : Fin 1 → E := fun _ => u j
  have hrep : ExteriorAlgebra.ι K (u j) = ExteriorAlgebra.ιMulti K 1 a := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rw [hrep]
  have hm := ExteriorAlgebra.ιMulti_mul_ιMulti (R := K) (m := 1) (n := r) a u
  rw [hm]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hinj
  let i0 : Fin (1 + r) := Fin.castAdd r (0 : Fin 1)
  let i1 : Fin (1 + r) := Fin.natAdd 1 j
  have hval : Fin.append a u i0 = Fin.append a u i1 := by
    simp [a, i0, i1]
  have heq : i0 = i1 := hinj hval
  have hne : i0 ≠ i1 := by
    intro h
    have hv : i0.val = i1.val := congrArg Fin.val h
    simp [i0, i1] at hv
    omega
  exact hne heq

/-- A vector in the span of a family annihilates its exterior product. -/
lemma exterior_mul_ιMulti_eq_zero_of_mem_span {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {r : ℕ} (u : Fin r → E) (x : E)
    (hx : x ∈ Submodule.span K (Set.range u)) :
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K r u = 0 := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hx with ⟨c, hc⟩
  -- hc : ∑ j, c j • u j = x
  have hlin : ExteriorAlgebra.ι K (∑ j : Fin r, c j • u j) =
      ∑ j : Fin r, (c j) • ExteriorAlgebra.ι K (u j) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact map_smul (ExteriorAlgebra.ι K) (c j) (u j)
  calc
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K r u
        = ExteriorAlgebra.ι K (∑ j : Fin r, c j • u j) * ExteriorAlgebra.ιMulti K r u := by
            rw [← hc]
    _ = (∑ j : Fin r, (c j) • ExteriorAlgebra.ι K (u j)) * ExteriorAlgebra.ιMulti K r u := by
            rw [hlin]
    _ = ∑ j : Fin r, ((c j) • ExteriorAlgebra.ι K (u j)) *
            ExteriorAlgebra.ιMulti K r u := by
            rw [Finset.sum_mul]
    _ = ∑ j : Fin r, (c j) • (ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ιMulti K r u) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [smul_mul_assoc]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            simp [exterior_mul_ιMulti_self_mem_eq_zero u j]

/-- A vector lies in the span of a linearly independent family iff multiplying the
exterior product of the family by it gives zero. -/
theorem exterior_mul_ιMulti_eq_zero_iff_mem_span {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {r : ℕ} (u : Fin r → E) (hu : LinearIndependent K u)
    (x : E) :
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K r u = 0 ↔
      x ∈ Submodule.span K (Set.range u) := by
  constructor
  · intro hEq
    by_contra hx
    exact exterior_mul_ιMulti_ne_zero_of_not_mem_span u hu x hx hEq
  · intro hx
    exact exterior_mul_ιMulti_eq_zero_of_mem_span u x hx


/-- Two `K`-independent families with equal exterior products (in the exterior
ALGEBRA) span the same subspace. -/
theorem span_eq_of_ιMulti_eq_exteriorAlgebra {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] {r : ℕ} (u v : Fin r → E) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v)
    (h : ExteriorAlgebra.ιMulti K r u = ExteriorAlgebra.ιMulti K r v) :
    Submodule.span K (Set.range u) = Submodule.span K (Set.range v) := by
  apply le_antisymm
  · -- span(range u) ≤ span(range v): show range u ⊆ span(range v)
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    -- u j ∈ span(range v): use the iff with v: (ι(u j)) * ∧v = 0
    have hprod : ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ιMulti K r v = 0 := by
      -- (ι(u j)) * ∧v = (ι(u j)) * ∧u (by h.symm) = 0 (own factor)
      rw [← h]
      exact exterior_mul_ιMulti_self_mem_eq_zero u j
    exact (exterior_mul_ιMulti_eq_zero_iff_mem_span v hv (u j)).mp hprod
  · -- span(range v) ≤ span(range u)
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    have hprod : ExteriorAlgebra.ι K (v j) * ExteriorAlgebra.ιMulti K r u = 0 := by
      rw [h]
      exact exterior_mul_ιMulti_self_mem_eq_zero v j
    exact (exterior_mul_ιMulti_eq_zero_iff_mem_span u hu (v j)).mp hprod

/-- Two `K`-independent families with equal exterior products (in the exterior
POWER module) span the same subspace. -/
theorem span_eq_of_ιMulti_eq {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {r : ℕ} (u v : Fin r → E) (hu : LinearIndependent K u) (hv : LinearIndependent K v)
    (h : exteriorPower.ιMulti K r u = exteriorPower.ιMulti K r v) :
    Submodule.span K (Set.range u) = Submodule.span K (Set.range v) := by
  apply span_eq_of_ιMulti_eq_exteriorAlgebra u v hu hv
  -- transport the equality from the exterior-power submodule to the ambient
  -- exterior algebra (the subtype embedding is injective)
  have hval : (exteriorPower.ιMulti K r u).1 = (exteriorPower.ιMulti K r v).1 :=
    congrArg Subtype.val h
  simpa using hval

end Submission.WedgeDeterminesSpan
