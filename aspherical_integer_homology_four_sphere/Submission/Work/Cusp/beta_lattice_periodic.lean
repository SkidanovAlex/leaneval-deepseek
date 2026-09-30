import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-!
# `β` is periodic under the cusp lattice

`beta` is the `ℤ³`-periodic ceiling function of the cusp charts (`Basic.lean`): over the unit cube
with centre `c` it is `√(9/4 − ‖x−c‖²)`, written as a single periodic formula through `off`.
Here we record the periodicity, first for a full integer translation (`beta_add_ofInt3`) and then
for the cusp lattice `Λ_v = ⟨κ_{v,1}, κ_{v,2}, κ_{v,3}⟩ ⊂ ℤ³` (`beta_lattice_periodic`).
-/

/-- `off` has every integer as a period (`off t = 1/2 − |frac t − 1/2|`). -/
theorem off_add_int (t : ℝ) (n : ℤ) : off (t + n) = off t := by
  simp [off, Int.fract_add_intCast]

/-- **`β` is periodic under an integer vector**: translating `x` by `ofInt3 m` does not change the
ceiling, because each coordinate `off (x i)` is `1`-periodic. -/
theorem beta_add_ofInt3 (x : E3) (m : Fin 3 → ℤ) : beta (x + ofInt3 m) = beta x := by
  have h : (∑ i, (off ((x + ofInt3 m) i)) ^ 2) = ∑ i, (off (x i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h2 : (x + ofInt3 m) i = x i + (m i : ℝ) := by
      fin_cases i <;> simp [ofInt3]
    rw [h2, off_add_int]
  simp only [beta, h]

/-- The set of periods of `β` is an additive subgroup of `E3`. -/
def betaPeriodSub : AddSubgroup E3 where
  carrier := {d | ∀ x, beta (x + d) = beta x}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb (x + a), ha x]
  neg_mem' := by
    intro a ha x
    have h := ha (x + -a)
    rw [add_assoc, neg_add_cancel, add_zero] at h
    exact h.symm

/-- Every integer vector is a period of `β`. -/
theorem ofInt3_mem_betaPeriodSub (m : Fin 3 → ℤ) : ofInt3 m ∈ betaPeriodSub :=
  fun x => beta_add_ofInt3 x m

/-- The generators `κ_{v,i} = ofInt3 (kappa v i)` of the cusp lattice are periods of `β`. -/
theorem kv_mem_betaPeriodSub (v : Fin 5) : Set.range (kv v) ⊆ (betaPeriodSub : Set E3) := by
  rintro d ⟨i, rfl⟩
  exact ofInt3_mem_betaPeriodSub (kappa v i)

/-- **`β` is invariant under the cusp lattice**: for `l ∈ Λ_v = AddSubgroup.closure (range (kv v))`
we have `beta (x + l) = beta x`. -/
theorem beta_lattice_periodic (v : Fin 5) (x l : E3) (hl : l ∈ lattice v) : beta (x + l) = beta x :=
  (AddSubgroup.closure_le betaPeriodSub |>.mpr (kv_mem_betaPeriodSub v)) hl x

end Work.Cusp
