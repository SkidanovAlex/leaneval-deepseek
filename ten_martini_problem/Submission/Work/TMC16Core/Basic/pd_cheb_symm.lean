/-
# Symmetry of the Chebyshev form `Pbiv` of the Dirichlet continuant

`Pbiv α lam E k = cont (listA α lam E k)` is the continuant of the length-`k` window of
potentials `E - 2λ cos(2π(x + jα - ctr))`, written as a bivariate polynomial with
`X = cos 2πx` and `Y = sin 2πx`.  The window is centred, so the reflection `x ↦ -x`
(equivalently `Y ↦ -Y`) permutes the potentials, sending the `j`-th one to the
`(k-1-j)`-th one.  Hence it reverses the list `listA`, and since a continuant is
invariant under reversal of its list (`Cheb.cont_reverse`), `Pbiv` is invariant under
`Y ↦ -Y`, i.e. under `Polynomial.comp (-X)`.

This is the symmetry hypothesis `hsym` consumed by `pd_cheb_red`, which removes the
degree-one `sin` part of `Pbiv` and produces the polynomial `Q` in `cos 2πx` of
`pd_cheb`.
-/
import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_setup

namespace Work.TMC16Core.Basic

open Polynomial
open Work.TMC16Core.Cheb

namespace PdSymm

/-! ## List combinatorics for the reflected range -/

/-- The reflection `j ↦ k - 1 - j` turns `List.range k` into its reverse. -/
lemma range_reverse (k : ℕ) :
    (List.range k).reverse = (List.range k).map (fun j => k - 1 - j) := by
  simpa [List.range_eq_range', Nat.zero_add] using (List.reverse_range' (s := 0) (n := k))

/-- Mapping `g` over the reflected range is the same as reversing the mapped list. -/
lemma map_range_rev_comp {β : Type*} (g : ℕ → β) (k : ℕ) :
    (List.range k).map (fun j => g (k - 1 - j)) = ((List.range k).map g).reverse := by
  rw [← List.map_reverse, range_reverse, List.map_map]
  rfl

/-! ## The pointwise reflection of a single potential -/

/-- For `j < k` the index `k - 1 - j` is an honest natural number index. -/
lemma hcast_sub (k j : ℕ) (hj : j < k) : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
  have h1 : k - 1 - j = k - (j + 1) := by omega
  rw [h1, Nat.cast_sub (by omega : j + 1 ≤ k)]
  push_cast
  ring

/-- Reflection `Y ↦ -Y` (i.e. `x ↦ -x`) sends the `j`-th potential of a centred length-`k`
window to the `(k-1-j)`-th one.  Indeed the centre satisfies `ctr k α = ((k-1)/2)α`, so
`(k-1-j)α - ctr k α = -(jα - ctr k α)`; `cos` is even and `sin` is odd. -/
lemma afun_comp_negX (α lam : ℝ) (E : ℂ) (k : ℕ) {j : ℕ} (hj : j < k) :
    (afun α lam E k j).comp (-Polynomial.X) = afun α lam E k (k - 1 - j) := by
  have hctr : ((k - 1 - j : ℕ) : ℝ) * α - ctr k α = -((j : ℝ) * α - ctr k α) := by
    rw [hcast_sub k j hj, ctr]; ring
  have hcos : Real.cos (2 * Real.pi * (((k - 1 - j : ℕ) : ℝ) * α - ctr k α))
      = Real.cos (2 * Real.pi * ((j : ℝ) * α - ctr k α)) := by
    rw [hctr, mul_neg, Real.cos_neg]
  have hsin : Real.sin (2 * Real.pi * (((k - 1 - j : ℕ) : ℝ) * α - ctr k α))
      = -Real.sin (2 * Real.pi * ((j : ℝ) * α - ctr k α)) := by
    rw [hctr, mul_neg, Real.sin_neg]
  rw [afun, afun, hcos, hsin]
  simp only [cst, cX, sY, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp, Polynomial.C_neg, Complex.ofReal_neg]
  ring

/-! ## The reflection of the whole window -/

/-- Reflecting `Y ↦ -Y` reverses the list of potentials of the centred window. -/
lemma listA_comp (α lam : ℝ) (E : ℂ) (k : ℕ) :
    (listA α lam E k).map (fun p => p.comp (-Polynomial.X)) = (listA α lam E k).reverse := by
  simp only [listA, List.map_map]
  rw [← map_range_rev_comp]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  exact afun_comp_negX α lam E k (List.mem_range.mp hj)

end PdSymm

theorem pd_cheb_symm (α lam : ℝ) (E : ℂ) (k : ℕ) :
    (Work.TMC16Core.Cheb.Pbiv α lam E k).comp (-Polynomial.X) = Work.TMC16Core.Cheb.Pbiv α lam E k := by
  show (cont (listA α lam E k)).comp (-Polynomial.X) = cont (listA α lam E k)
  have hcont := cont_map (Polynomial.compRingHom (-Polynomial.X)) (listA α lam E k)
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom] at hcont
  rw [PdSymm.listA_comp, cont_reverse] at hcont
  exact hcont.symm

end Work.TMC16Core.Basic
