import Mathlib
import Submission.Work.Thom.realification

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# The linear algebra of "splitting off a line in `ℂⁿ`"

Let `k : Fin (n+1)` and `w : ℂ^{n+1}` with `w k ≠ 0`.  Then `ℂ^{n+1} = ℂ·w ⊕ {coordinates ≠ k}`,
witnessed by

`Θ : ℂ^{n+1} → ℂ × ℂ^n,  u ↦ (u k, quoFun k w u)`,  where
`(quoFun k w u) m = u (k.succAbove m) - (w (k.succAbove m)/w k) · u k`,

which is a linear isomorphism with inverse `(a, z) ↦ fillFun k z + (a/w k) • w`.

These two maps are the local algebra behind `Q = π^*V / ℂ·s`, the tautological quotient of a
complex vector bundle over its punctured total space: over the chart piece where the `k`-th fibre
coordinate of the tautological section is invertible, `Q` is trivialised by `quoFun k w`, and the
splitting `π^*V ≅ ε¹ ⊕ Q` is the map `Θ` above.

Everything here is stated for the *bare* functions; the linearity (and hence the passage to
`ℂ →L[ℂ]`) is `Work.Thom.fill_linear` / `Work.Thom.quo_linear` of the quotient-bundle module.
-/

open scoped RealInnerProductSpace

namespace Work.Thom

noncomputable section

variable {n : ℕ}

/-- The `k`-th coordinate of `u : ℂⁿ`. -/
def coordFun (k : Fin n) (u : EuclideanSpace ℂ (Fin n)) : ℂ := u k

@[simp] theorem coordFun_apply (k : Fin n) (u : EuclideanSpace ℂ (Fin n)) : coordFun k u = u k :=
  rfl

/-- The standard basis vector of `ℂⁿ` at `k` (the `k`-th unit vector). -/
def basisVec (k : Fin n) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Pi.single k 1)

@[simp] theorem basisVec_apply (j i : Fin n) : basisVec j i = if i = j then 1 else 0 := by
  simp [basisVec]

/-- **Forgetting the `k`-th coordinate**, `ℂ^{n+1} → ℂ^n`. -/
def dropFun (k : Fin (n + 1)) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun m => u (k.succAbove m))

@[simp] theorem dropFun_apply (k : Fin (n + 1)) (u : EuclideanSpace ℂ (Fin (n + 1)))
    (m : Fin n) : dropFun k u m = u (k.succAbove m) := by
  simp [dropFun]

theorem dropFun_add (k : Fin (n + 1)) (u v : EuclideanSpace ℂ (Fin (n + 1))) :
    dropFun k (u + v) = dropFun k u + dropFun k v := by
  ext m; simp [dropFun_apply]

theorem dropFun_smul (k : Fin (n + 1)) (c : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    dropFun k (c • u) = c • dropFun k u := by
  ext m; simp [dropFun_apply]

/-- **Filling the `k`-th coordinate with `0`**: the section `ℂ^n → ℂ^{n+1}` of `dropFun k`. -/
def fillFun (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  ∑ m : Fin n, z m • basisVec (k.succAbove m)

theorem fillFun_apply (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) (i : Fin (n + 1)) :
    fillFun k z i = ∑ m : Fin n, if i = k.succAbove m then z m else 0 := by
  have h1 : fillFun k z i = ∑ m : Fin n, (z m • basisVec (k.succAbove m)) i := by
    simp only [fillFun, WithLp.ofLp_sum, Finset.sum_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, basisVec_apply, smul_eq_mul]
  by_cases h : i = k.succAbove m <;> simp [h]

theorem fillFun_apply_succAbove (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) (m : Fin n) :
    fillFun k z (k.succAbove m) = z m := by
  have hinj : Function.Injective (fun m : Fin n => k.succAbove m) := Fin.succAbove_right_injective
  rw [fillFun_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    have hne : k.succAbove m ≠ k.succAbove b := fun h => hb (hinj h).symm
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ m) h

theorem fillFun_apply_self (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    fillFun k z k = 0 := by
  rw [fillFun_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  have hne : k ≠ k.succAbove m := Ne.symm (Fin.succAbove_ne k m)
  simp [hne]

@[simp] theorem dropFun_fillFun (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    dropFun k (fillFun k z) = z := by
  ext m
  simp [dropFun_apply, fillFun_apply_succAbove]

/-- **The quotient projection along `w`**: `u ↦ u - (u k / w k) • w`, read in the coordinates
other than `k`.  Its kernel is the line `ℂ·w` when `w k ≠ 0`. -/
def quoFun (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin n) :=
  dropFun k u - (u k / w k) • dropFun k w

theorem quoFun_apply (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1))) (m : Fin n) :
    quoFun k w u m = u (k.succAbove m) - (u k / w k) * w (k.succAbove m) := by
  rw [quoFun, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, dropFun_apply,
    dropFun_apply, smul_eq_mul]

/-- `quoFun k w (fillFun k z) = z`: the filling is a section of the quotient projection. -/
theorem quoFun_fillFun (k : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1)))
    (z : EuclideanSpace ℂ (Fin n)) (hw : w k ≠ 0) : quoFun k w (fillFun k z) = z := by
  ext m
  rw [quoFun_apply, fillFun_apply_succAbove, fillFun_apply_self, zero_div, zero_mul, sub_zero]

/-- `quoFun k w w = 0`: the quotient projection kills the line it is taken along. -/
theorem quoFun_self (k : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1))) (hw : w k ≠ 0) :
    quoFun k w w = 0 := by
  rw [quoFun, div_self hw, one_smul, sub_self]

@[simp] theorem fillFun_zero (k : Fin (n + 1)) : fillFun k (0 : EuclideanSpace ℂ (Fin n)) = 0 := by
  rw [fillFun]
  simp

/-- **The basic identity**: `u - fillFun k (quoFun k w u) = (u k / w k) • w`, i.e. `u` differs from
the filling of its quotient class by a multiple of `w`. -/
theorem sub_fillFun_quoFun (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (hw : w k ≠ 0) : u - fillFun k (quoFun k w u) = (u k / w k) • w := by
  ext i
  by_cases hi : i = k
  · subst hi
    simp only [WithLp.ofLp_sub, Pi.sub_apply, fillFun_apply_self, sub_zero, WithLp.ofLp_smul,
      Pi.smul_apply, quoFun_apply, dropFun_apply, smul_eq_mul, div_eq_mul_inv]
    rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
  · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [WithLp.ofLp_sub, Pi.sub_apply, fillFun_apply_succAbove, WithLp.ofLp_smul,
      Pi.smul_apply, quoFun_apply, dropFun_apply, smul_eq_mul, div_eq_mul_inv]
    ring

/-- **The kernel of the quotient projection is the line `ℂ·w`** (when `w k ≠ 0`). -/
theorem quoFun_eq_zero_iff (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (hw : w k ≠ 0) : quoFun k w u = 0 ↔ ∃ a : ℂ, u = a • w := by
  constructor
  · intro h
    refine ⟨u k / w k, ?_⟩
    have h2 : u - fillFun k (quoFun k w u) = (u k / w k) • w := sub_fillFun_quoFun k w u hw
    rw [h, fillFun_zero, sub_zero] at h2
    exact h2
  · rintro ⟨a, rfl⟩
    have h2 : (a • w) k / w k = a := by
      rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hw, mul_one]
    rw [quoFun, h2, dropFun_smul, sub_self]

/-- **The coordinate decomposition is injective**: `u ↦ (u k, quoFun k w u)` has trivial kernel. -/
theorem coordFun_quoFun_injective (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (hw : w k ≠ 0) (h : u k = 0) (h' : quoFun k w u = 0) : u = 0 := by
  have h2 := sub_fillFun_quoFun k w u hw
  simpa [h', fillFun_zero, h] using h2

end

end Work.Thom
