import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.Spaces.DerivLikeDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.Spaces

variable {X : Type*}

/-- Closure properties of the class `P` of admissible functions. -/
structure FunClass (P : (X → ℝ) → Prop) : Prop where
  add : ∀ A B : X → ℝ, P A → P B → P (A + B)
  mul : ∀ A B : X → ℝ, P A → P B → P (A * B)
  smul : ∀ (c : ℝ) (A : X → ℝ), P A → P (fun p => c * A p)

/-- An operator satisfying the Leibniz rule and the companion algebraic
properties, all relative to the class `P` and the set `s` on which `EqOn` is
taken. -/
structure DerivLike (s : Set X) (P : (X → ℝ) → Prop) (D : (X → ℝ) → (X → ℝ)) : Prop where
  add : ∀ A B : X → ℝ, P A → P B → Set.EqOn (D (A + B)) (fun p => D A p + D B p) s
  mul : ∀ A B : X → ℝ, P A → P B →
    Set.EqOn (D (A * B)) (fun p => D A p * B p + A p * D B p) s
  congr : ∀ A B : X → ℝ, Set.EqOn A B s → Set.EqOn (D A) (D B) s
  preserve : ∀ A : X → ℝ, P A → P (D A)
  smul : ∀ (c : ℝ) (A : X → ℝ), P A →
    Set.EqOn (D (fun p => c * A p)) (fun p => c * D A p) s

variable {s : Set X} {P : (X → ℝ) → Prop}

/-- `EqOn` is compatible with finite sums (pointwise). -/
theorem eqOn_sum {ι : Type*} (t : Finset ι) {f g : ι → X → ℝ}
    (h : ∀ i ∈ t, Set.EqOn (f i) (g i) s) :
    Set.EqOn (fun p => ∑ i ∈ t, f i p) (fun p => ∑ i ∈ t, g i p) s := fun _ hp =>
  Finset.sum_congr rfl fun i hi => h i hi hp

/-- The Pascal convolution identity behind one step of the iterated Leibniz
rule: the sum of the two shifted binomial convolutions over `range (k+1)` is
the binomial convolution over `range (k+2)` with `k+1` in place of `k`. -/
theorem leibniz_step (k : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (a (i + 1) * b (k - i) + a i * b (k - i + 1)))
      = ∑ j ∈ Finset.range (k + 1 + 1),
          ((k + 1).choose j : ℝ) * (a j * b (k + 1 - j)) := by
  have key : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * (a (i + 1) * b (k - i) + a i * b (k - i + 1))
        = (k.choose i : ℝ) * a (i + 1) * b (k - i)
            + (k.choose i : ℝ) * a i * b (k - i + 1) := by
    intro i _; ring
  have key2 : (∑ j ∈ Finset.range (k + 1 + 1),
        ((k + 1).choose j : ℝ) * a j * b (k + 1 - j))
      = ∑ j ∈ Finset.range (k + 1 + 1),
          ((k + 1).choose j : ℝ) * (a j * b (k + 1 - j)) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← key2]
  exact thD_reindex k a b

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.scoef_sum_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The defining recursion of the Stirling numbers of the second kind, in the
form needed for the reindexing step. -/
private lemma scoef_succ_succ_aux (n k : ℕ) :
    scoef (n + 1) (k + 1) = (k + 1) * scoef n (k + 1) + scoef n k := by
  simp [scoef]

/-- Index shift in a sum: if `g (n+1) = 0` then
`∑_{k≤n} k g(k) = ∑_{j≤n} (j+1) g(j+1)`.  The hypothesis makes the top term of
the right-hand side vanish, so that the shift does not overshoot the range. -/
private lemma sum_range_mul_shift (n : ℕ) (g : ℕ → ℝ) (h : g (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * g k)
      = ∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * g (j + 1) := by
  rw [Finset.sum_range_succ' (f := fun k => (k : ℝ) * g k) n,
      Finset.sum_range_succ (f := fun j => ((j : ℝ) + 1) * g (j + 1)) n]
  simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one, h, add_zero, mul_zero]

/-- The reindexing identity relating the `n`-th and `(n+1)`-st rows of Stirling
numbers of the second kind, as used in the induction step of the operator
expansion of `D_z = z ∂_z`. -/
theorem scoef_sum_shift (n : ℕ) (A : ℕ → ℝ) (z : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = ∑ j ∈ Finset.range (n + 2), (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * A j) := by
  let g : ℕ → ℝ := fun k => (scoef n k : ℝ) * (z ^ k * A k)
  let w : ℕ → ℝ := fun k => (scoef n k : ℝ) * (z ^ (k + 1) * A (k + 1))
  let h : ℕ → ℝ := fun j => (scoef (n + 1) j : ℝ) * (z ^ j * A j)
  have hg0 : g (n + 1) = 0 := by
    simp only [g, scoef_succ_self_eq_zero n, Nat.cast_zero, zero_mul]
  -- split each summand of the left-hand side
  have hL : (∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k)) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [g, w]
    ring
  -- shift the index in the `k`-weighted piece
  have hsum : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k))
      = (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_range_mul_shift n g hg0]
  -- the right-hand side, with the `j = 0` term dropped (it vanishes)
  have h0 : h 0 = 0 := by
    show (scoef (n + 1) 0 : ℝ) * (z ^ 0 * A 0) = 0
    simp [scoef]
  have hR1 : (∑ j ∈ Finset.range (n + 2), h j)
      = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := by
    rw [Finset.sum_range_succ']
    rw [h0, add_zero]
  -- and the `D_z`-recursion applied to the remaining terms
  have hR2 : (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j))
      = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    show (((j : ℝ) + 1) * ((scoef n (j + 1) : ℝ) * (z ^ (j + 1) * A (j + 1)))
        + (scoef n j : ℝ) * (z ^ (j + 1) * A (j + 1)))
      = ((scoef (n + 1) (j + 1) : ℝ) * (z ^ (j + 1) * A (j + 1)))
    rw [scoef_succ_succ_aux]
    push_cast
    ring
  calc (∑ k ∈ Finset.range (n + 1),
        (scoef n k : ℝ) * ((k : ℝ) * z ^ k * A k + z ^ (k + 1) * A (k + 1)))
      = (∑ k ∈ Finset.range (n + 1), ((k : ℝ) * g k + w k)) := hL
    _ = (∑ j ∈ Finset.range (n + 1), (((j : ℝ) + 1) * g (j + 1) + w j)) := hsum
    _ = (∑ j ∈ Finset.range (n + 1), h (j + 1)) := hR2
    _ = (∑ j ∈ Finset.range (n + 2), h j) := hR1.symm
    _ = ∑ j ∈ Finset.range (n + 2), (scoef (n + 1) j : ℝ) * (z ^ j * A j) := rfl

end Work.Spaces
end
