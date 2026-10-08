import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.principalChar_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff`

`Q = S × Q₁` (via `prodIso`), and `h.prodChar lam theta a b = lam a * theta b` for the
corresponding decomposition.  The two lemmas below compute `prodChar` on the elements of `Q`
that lie in `Q₁` and record the general fact that an irreducible character which is constant
is the principal character.  The main theorem is then immediate:

for `lam ∈ Irr S` and `theta ∈ Irr Q₁`,
`Q₁ ≤ ker (prodChar h lam theta)` holds if and only if `theta` is the principal character of
`Q₁`.

Indeed, an element of `Q` lying in `Q₁` decomposes as `(1, x)` in `S × Q₁`, so
`prodChar h lam theta x = lam 1 * theta x`, while `prodChar h lam theta 1 = lam 1 * theta 1`;
as `lam 1 ≠ 0` (the degree of an irreducible character is positive), the condition
`prodChar h lam theta x = prodChar h lam theta 1` for all such `x` says exactly that `theta`
is constant, i.e. that `theta` is the principal character of `Q₁`.

## Main results

* `Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1`
* `Work.FeitSibley.CharQ.eq_principal_of_irr_of_constant`
* `Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff`
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

/-- An element `x` of `Q` which lies in `Q₁` corresponds to the pair `(1, x)` under the
isomorphism `Q ≅ S × Q₁`; consequently `prodChar h lam theta x = lam 1 * theta x`. -/
theorem prodChar_apply_of_mem_Q1 {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (lam : ↥h.S → ℂ) (theta : ↥h.Q1 → ℂ)
    (x : ↥h.Q) (hx : (x : G) ∈ h.Q1) :
    h.prodChar lam theta x = lam 1 * theta ⟨(x : G), hx⟩ := by
  -- the `S × Q₁` coordinates of `x` multiply to `x`, and `x = 1 * x` is the decomposition
  -- with second factor in `Q₁`; by uniqueness of the decomposition the first factor is `1`
  obtain ⟨ha1, hb1⟩ := h.mul_eq_of_Q_decomp (h.prodIso.symm x).1.2 (one_mem h.S)
    (h.prodIso.symm x).2.2 hx (by rw [h.prodIso_symm_mul x, one_mul])
  have hS1 : (h.prodIso.symm x).1 = 1 := Subtype.ext ha1
  have hQ1b : (h.prodIso.symm x).2 = ⟨(x : G), hx⟩ := Subtype.ext hb1
  rw [Work.FeitSibley.FSData.prodChar, hS1, hQ1b]

/-- An irreducible complex character which is constant (equal to its value at `1`) is the
principal character.

The two orthogonality relations for `theta` and the principal character give
`theta 1 * conj (theta 1) = cfInner theta theta = 1` and
`theta 1 = cfInner theta 1 ∈ {0, 1}`; since `theta 1 ≠ 0` the value is `1`. -/
theorem eq_principal_of_irr_of_constant {G : Type} [Group G] [Fintype G] {theta : G → ℂ}
    (ht : theta ∈ Work.CharCore.Irr G) (hconst : ∀ x : G, theta x = theta 1) :
    theta = fun _ => 1 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- `cfInner theta theta = 1`, and it is `theta 1 * conj (theta 1)` as `theta` is constant
  have hself : Work.CharCore.cfInner theta theta = 1 := by
    simpa using Work.CharCore.irr_orthonormal theta theta ht ht
  have hsum : (∑ x : G, theta x * starRingEnd ℂ (theta x)) =
      (Fintype.card G : ℂ) * (theta 1 * starRingEnd ℂ (theta 1)) := by
    calc (∑ x : G, theta x * starRingEnd ℂ (theta x))
        = ∑ _x : G, theta 1 * starRingEnd ℂ (theta 1) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hconst x]
      _ = (Fintype.card G) • (theta 1 * starRingEnd ℂ (theta 1)) := Finset.sum_const _
      _ = (Fintype.card G : ℂ) * (theta 1 * starRingEnd ℂ (theta 1)) := by
          rw [nsmul_eq_mul]
  have hprod : theta 1 * starRingEnd ℂ (theta 1) = 1 := by
    have h := hself
    rw [Work.CharCore.cfInner, hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul] at h
    exact h
  have hne : theta 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hprod
    exact one_ne_zero hprod.symm
  -- `cfInner theta 1 = theta 1`, and orthogonality says it is `0` or `1`
  have hcf : Work.CharCore.cfInner theta (fun _ : G => (1 : ℂ)) = theta 1 := by
    rw [Work.CharCore.cfInner]
    have hsum2 : (∑ x : G, theta x * starRingEnd ℂ ((fun _ : G => (1 : ℂ)) x)) =
        (Fintype.card G : ℂ) * theta 1 := by
      calc (∑ x : G, theta x * starRingEnd ℂ ((fun _ : G => (1 : ℂ)) x))
          = ∑ _x : G, theta 1 * 1 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hconst x]
            simp
        _ = (Fintype.card G) • (theta 1 * 1) := Finset.sum_const _
        _ = (Fintype.card G : ℂ) * theta 1 := by
            rw [nsmul_eq_mul]
            ring
    rw [hsum2, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  by_cases h : theta = fun _ : G => 1
  · exact h
  · have hprin := Work.CharCore.irr_orthonormal theta (fun _ : G => (1 : ℂ)) ht
        Work.CharCore.principalChar_mem_Irr
    have hzero : (if theta = (fun _ : G => 1) then (1 : ℂ) else 0) = 0 := by simp [h]
    rw [hcf, hzero] at hprin
    exact absurd hprin hne

/-- `Q₁` is contained in the kernel of `prodChar h lam theta` if and only if `theta` is the
principal character of `Q₁`. -/
theorem prodChar_Q1_kernel_iff {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {lam : ↥h.S → ℂ} {theta : ↥h.Q1 → ℂ}
    (hl : lam ∈ Work.CharCore.Irr ↥h.S) (ht : theta ∈ Work.CharCore.Irr ↥h.Q1) :
    (∀ x : ↥h.Q, (x : G) ∈ h.Q1 → h.prodChar lam theta x = h.prodChar lam theta 1) ↔
      theta = fun _ : ↥h.Q1 => 1 := by
  have hlam : lam 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hl]
    exact Work.CharCore.irrDeg_ne_zero hl
  constructor
  · intro hcond
    refine eq_principal_of_irr_of_constant ht fun b => ?_
    have h1 := hcond ⟨(b : G), h.Q1_le_Q b.2⟩ b.2
    rw [prodChar_apply_of_mem_Q1 h lam theta ⟨(b : G), h.Q1_le_Q b.2⟩ b.2,
      h.prodChar_one] at h1
    exact mul_left_cancel₀ hlam h1
  · intro htheta x hx
    rw [prodChar_apply_of_mem_Q1 h lam theta x hx, h.prodChar_one, htheta]

end Work.FeitSibley.CharQ
