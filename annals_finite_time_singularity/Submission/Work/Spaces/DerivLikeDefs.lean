/-
Copyright: work module for the Elgindi finite-time singularity project.

# Abstract derivation-like operators

This file isolates the algebraic apparatus behind the iterated Leibniz rule
used for the operators `D_z`, `D_θ` of `Submission.Work.Spaces.Defs` and,
more generally, for the two-operator statement of
`Submission.Work.Spaces.twoOp_iterate_mul_eqOn`.

A class `P` of "admissible" functions (closed under `+`, `*` and scalar
multiplication) is fixed, together with an operator `D` which is additive on
`P`-functions, satisfies the Leibniz rule on products of `P`-functions,
commutes with multiplication by a constant, preserves `P` and only depends on
the values of its argument on a fixed set `s` (`EqOn`-locality).
-/
import Mathlib
import Submission.Work.Spaces.thD_reindex

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
