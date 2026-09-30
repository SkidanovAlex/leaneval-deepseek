import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

theorem telescope_coord0 {n : ℕ} (f : (Fin (n + 1) →₀ ℕ) → ℚ)
    (Q : MvPolynomial (Fin (n + 1)) ℚ) (M : ℕ)
    (h : ∀ x : Fin (n + 1) →₀ ℕ, (∀ j, M ≤ x j) →
      f (x + Finsupp.single 0 1) - f x = Q.eval (fun j => (x j : ℚ)))
    (d : Fin (n + 1) →₀ ℕ) (hd : ∀ j, M ≤ d j) :
    f d - f (d - Finsupp.single 0 (d 0) + Finsupp.single 0 M) =
      ∑ k ∈ Finset.range (d 0 - M),
        Q.eval (Function.update (fun j => (d j : ℚ)) 0 ((M + k : ℕ) : ℚ)) := by
  have hd0 : M ≤ d 0 := hd 0
  -- The intermediate points of the telescoping path along coordinate `0`:
  -- `x k` agrees with `d` off coordinate `0`, and has coordinate `0` equal to `M + k`.
  let e : Fin (n + 1) →₀ ℕ := d - Finsupp.single 0 (d 0)
  let x : ℕ → Fin (n + 1) →₀ ℕ := fun k => e + Finsupp.single 0 (M + k)
  have hx0 : ∀ k, x k 0 = M + k := by
    intro k
    simp only [x, e]
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
    simp
  have hxj : ∀ k (j : Fin (n+1)), j ≠ 0 → x k j = d j := by
    intro k j hj
    simp only [x, e]
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj, Finsupp.single_eq_of_ne hj]
    simp
  have hxmem : ∀ k j, M ≤ x k j := by
    intro k j
    by_cases hj : j = 0
    · subst hj; rw [hx0 k]; exact Nat.le_add_right M k
    · rw [hxj k j hj]; exact hd j
  have hstep : ∀ k, x k + Finsupp.single 0 1 = x (k+1) := by
    intro k
    ext j
    rw [Finsupp.add_apply]
    by_cases hj : j = 0
    · subst hj
      rw [hx0 k, hx0 (k+1), Finsupp.single_eq_same]
      omega
    · rw [hxj k j hj, hxj (k+1) j hj, Finsupp.single_eq_of_ne hj]
      simp
  have hxd : x (d 0 - M) = d := by
    ext j
    by_cases hj : j = 0
    · subst hj
      rw [hx0 (d 0 - M)]
      omega
    · rw [hxj _ j hj]
  have hx0' : x 0 = d - Finsupp.single 0 (d 0) + Finsupp.single 0 M := by
    simp only [x, e, Nat.add_zero]
  have hQ : ∀ k, Q.eval (fun j => (x k j : ℚ)) =
      Q.eval (Function.update (fun j => (d j : ℚ)) 0 ((M + k : ℕ) : ℚ)) := by
    intro k
    have hfun : (fun j => (x k j : ℚ)) = Function.update (fun j => (d j : ℚ)) 0 ((M + k : ℕ) : ℚ) := by
      funext j
      by_cases hj : j = 0
      · subst hj; rw [Function.update_self, hx0 k]
      · rw [Function.update_of_ne hj, hxj k j hj]
    rw [hfun]
  have htel := Finset.sum_range_sub (fun k => f (x k)) (d 0 - M)
  have h1 : f d - f (d - Finsupp.single 0 (d 0) + Finsupp.single 0 M) = f d - f (x 0) := by
    rw [hx0']
  have h2 : f (x (d 0 - M)) - f (x 0) = f d - f (x 0) := by
    rw [hxd]
  calc f d - f (d - Finsupp.single 0 (d 0) + Finsupp.single 0 M)
      = f d - f (x 0) := h1
    _ = f (x (d 0 - M)) - f (x 0) := h2.symm
    _ = ∑ k ∈ Finset.range (d 0 - M), (f (x (k+1)) - f (x k)) := htel.symm
    _ = ∑ k ∈ Finset.range (d 0 - M),
          Q.eval (Function.update (fun j => (d j : ℚ)) 0 ((M + k : ℕ) : ℚ)) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [← hstep k, h (x k) (hxmem k), hQ k]

end Work.RB
