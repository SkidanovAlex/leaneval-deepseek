import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.par_polarisation_hpol`

**The polarisation identity for a `2`-homogeneous solution of the parallelogram law whose
polar form is `ℝ`-homogeneous in the first variable.**

For a function `Q : V → ℝ` on a real vector space satisfying

* the parallelogram law `Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y` (`hpar`),
* `2`-homogeneity `Q (t • x) = t ^ 2 * Q x` (`hhom`), and
* the *polar homogeneity* `Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y))` (`hpol`),

the polar form `polForm Q x y = (Q (x + y) - Q (x - y)) / 4` is `ℝ`-bilinear and therefore

`Q (∑ i, c i • v i) = ∑ i, ∑ j, c i * c j * polForm Q (v i) (v j)`.

## Why the third hypothesis is needed

Sibling module `Work.BoseFixB2.Polar.par_polarisation` records that `hpar` and `hhom` alone do
**not** suffice (the defect `t ↦ Q (t • x + y) - Q (t • x - y) - t * (Q (x + y) - Q (x - y))` is a
derivation of the field `ℝ`, which need not vanish).  The extra hypothesis `hpol` is exactly the
statement that this defect vanishes, and it is the concrete property that the box words of this
development do satisfy.  Hypothesis `hpol` gives `polForm`-homogeneity in the *first* variable;
homogeneity in the second variable, symmetry, and additivity are all consequences of `hpar` and
`hhom` (in particular they do not need `hpol`).

## The proof

`hpar` and `hhom` alone already give:

* `polForm Q x x = Q x` (`polForm_self`), the diagonal property;
* `polForm Q x y = polForm Q y x` (`polForm_comm`) and `polForm Q (-x) y = -polForm Q x y`
  (`polForm_neg`), from `Q (-x) = Q x`, which is `hhom (-1) x`;
* the three-term identity
  `(Q (u+v+w) - Q (u+v-w)) + (Q (u-v+w) - Q (u-v-w)) = 2 * (Q (u+w) - Q (u-w))`,
  obtained by combining the parallelogram law at the pairs `(u, v+w)`, `(u, v-w)`, `((u-w), v)`,
  `(v, w)` and `(u, w)` — this is the only genuinely computational step;
* additivity `polForm Q (x+y) z = polForm Q x z + polForm Q y z`: the three-term identity plus
  symmetry/skew-symmetry gives both
  `polForm Q (x+y) z + polForm Q (x-y) z = 2 * polForm Q x z` and
  `polForm Q (x+y) z - polForm Q (x-y) z = 2 * polForm Q y z`, and adding these two equations
  produces the claim.

Together with `hpol` (`polForm_smul_left`) this makes `polForm` additive and `ℝ`-homogeneous in
both variables — a symmetric `ℝ`-bilinear form — and the identity is then the standard expansion
`polForm (∑ cᵢ•vᵢ) (∑ cⱼ•vⱼ) = ∑ᵢ∑ⱼ cᵢ cⱼ polForm (vᵢ) (vⱼ)` of a bilinear form on a finite sum
(`polForm_sum_left`, `polForm_sum_right`), with the diagonal property converting
`polForm (∑ cᵢ•vᵢ) (∑ cᵢ•vᵢ)` back into `Q (∑ cᵢ•vᵢ)`.
-/

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **polar form** of `Q`, `(Q (x + y) - Q (x - y)) / 4`.  Under the hypotheses of
`par_polarisation_hpol` it is the symmetric `ℝ`-bilinear form whose diagonal is `Q`. -/
private def polForm (Q : V → ℝ) (x y : V) : ℝ :=
  (Q (x + y) - Q (x - y)) / 4

/-- `Q 0 = 0`, from `2`-homogeneity at `t = 0`. -/
private lemma Q_zero (Q : V → ℝ) (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) :
    Q 0 = 0 := by
  have h := hhom 0 (0 : V)
  simpa using h

/-- `Q (-x) = Q x`, from `2`-homogeneity at `t = -1`. -/
private lemma Q_neg (Q : V → ℝ) (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (x : V) : Q (-x) = Q x := by
  have h := hhom (-1) x
  simpa using h

/-- The polar form vanishes when its first argument is `0`. -/
private lemma polForm_zero_left (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (y : V) : polForm Q 0 y = 0 := by
  have h := Q_neg Q hhom y
  unfold polForm
  rw [zero_add, zero_sub, h, sub_self, zero_div]

/-- The polar form is symmetric. -/
private lemma polForm_comm (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (x y : V) :
    polForm Q x y = polForm Q y x := by
  have hneg : Q (-(x - y)) = Q (x - y) := Q_neg Q hhom (x - y)
  unfold polForm
  rw [add_comm x y, show y - x = -(x - y) by abel, hneg]

/-- The polar form is skew-symmetric in its first argument. -/
private lemma polForm_neg (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (x y : V) :
    polForm Q (-x) y = - polForm Q x y := by
  have hneg : ∀ a : V, Q (-a) = Q a := fun a => Q_neg Q hhom a
  unfold polForm
  rw [show -x + y = -(x - y) by abel, show -x - y = -(x + y) by abel, hneg, hneg]
  ring

/-- **The three-term identity.**  For a `2`-homogeneous `Q` with the parallelogram law,
`(Q (u+v+w) - Q (u+v-w)) + (Q (u-v+w) - Q (u-v-w)) = 2 * (Q (u+w) - Q (u-w))`.

It is the parallelogram law at the five pairs `(u, v+w)`, `(u, v-w)`, `((u-w), v)`, `(v, w)`
and `(u, w)`, combined by linear arithmetic. -/
private lemma add_sub_three (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (u v w : V) :
    (Q (u + v + w) - Q (u + v - w)) + (Q (u - v + w) - Q (u - v - w))
      = 2 * (Q (u + w) - Q (u - w)) := by
  have E1 := hpar u (v + w)
  have E2 := hpar u (v - w)
  have E4 := hpar (u - w) v
  have Pvw := hpar v w
  have Puw := hpar u w
  rw [show u + (v + w) = u + v + w by abel, show u - (v + w) = u - v - w by abel] at E1
  rw [show u + (v - w) = u + v - w by abel, show u - (v - w) = u - v + w by abel] at E2
  rw [show (u - w) + v = u + v - w by abel, show (u - w) - v = u - v - w by abel] at E4
  linarith

/-- **Additivity of the polar form in its first argument.**  Only `hpar` and `hhom` are used. -/
private lemma polForm_add_left (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (x y z : V) : polForm Q (x + y) z = polForm Q x z + polForm Q y z := by
  -- The three-term identity in terms of `polForm`
  have hA : ∀ u v w : V, polForm Q (u + v) w + polForm Q (u - v) w = 2 * polForm Q u w := by
    intro u v w
    unfold polForm
    rw [← add_div]
    have := add_sub_three Q hpar u v w
    linarith
  -- the same identity with the roles of `x` and `y` exchanged, using skew-symmetry
  have key : polForm Q (x + y) z - polForm Q (x - y) z = 2 * polForm Q y z := by
    have h := hA y x z
    rw [show y + x = x + y by abel] at h
    have h2 : polForm Q (y - x) z = - polForm Q (x - y) z := by
      rw [show y - x = -(x - y) by abel, polForm_neg Q hhom]
    rw [h2] at h
    linarith
  linarith [hA x y z, key]

/-- **`ℝ`-homogeneity of the polar form in its first argument.**  This is hypothesis `hpol`. -/
private lemma polForm_smul_left (Q : V → ℝ)
    (hpol : ∀ (t : ℝ) (x y : V),
      Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)))
    (t : ℝ) (x y : V) : polForm Q (t • x) y = t * polForm Q x y := by
  unfold polForm
  rw [hpol t x y]
  ring

/-- `ℝ`-homogeneity of the polar form in its second argument (from `hpol` and symmetry). -/
private lemma polForm_smul_right (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (hpol : ∀ (t : ℝ) (x y : V),
      Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)))
    (t : ℝ) (x y : V) : polForm Q x (t • y) = t * polForm Q x y := by
  rw [polForm_comm Q hhom, polForm_smul_left Q hpol, polForm_comm Q hhom]

/-- Additivity of the polar form in its second argument (from `polForm_add_left` and symmetry). -/
private lemma polForm_add_right (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (x y z : V) : polForm Q x (y + z) = polForm Q x y + polForm Q x z := by
  rw [polForm_comm Q hhom x (y + z), polForm_add_left Q hpar hhom y z x,
    polForm_comm Q hhom y x, polForm_comm Q hhom z x]

/-- The polar form vanishes when its second argument is `0`. -/
private lemma polForm_zero_right (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (x : V) : polForm Q x 0 = 0 := by
  rw [polForm_comm Q hhom, polForm_zero_left Q hhom]

/-- **The diagonal property**: `polForm Q x x = Q x`. -/
private lemma polForm_self (Q : V → ℝ)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (x : V) : polForm Q x x = Q x := by
  have h0 : Q (0 : V) = 0 := Q_zero Q hhom
  have h2 : Q (x + x) = 4 * Q x := by
    have h := hhom 2 x
    rw [show (2 : ℝ) • x = x + x by rw [two_smul],
      show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  unfold polForm
  rw [sub_self, h0, h2]
  ring

/-- Expansion of the polar form of a finite sum in its first argument. -/
private lemma polForm_sum_left {ι : Type*} [DecidableEq ι] (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (hpol : ∀ (t : ℝ) (x y : V),
      Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)))
    (s : Finset ι) (c : ι → ℝ) (v : ι → V) (y : V) :
    polForm Q (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * polForm Q (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact polForm_zero_left Q hhom y
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polForm_add_left Q hpar hhom,
        polForm_smul_left Q hpol, ih]

/-- Expansion of the polar form of a finite sum in its second argument. -/
private lemma polForm_sum_right {ι : Type*} [DecidableEq ι] (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (hpol : ∀ (t : ℝ) (x y : V),
      Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)))
    (s : Finset ι) (c : ι → ℝ) (v : ι → V) (x : V) :
    polForm Q x (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * polForm Q x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact polForm_zero_right Q hhom x
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polForm_add_right Q hpar hhom,
        polForm_smul_right Q hhom hpol, ih]

theorem par_polarisation_hpol {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ) (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (hpol : ∀ (t : ℝ) (x y : V), Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y))) {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (v : ι → V) : Q (∑ i, c i • v i) = ∑ i, ∑ j, c i * c j * ((Q (v i + v j) - Q (v i - v j)) / 4) := by
  classical
  -- `polForm` is bilinear, so its value on `∑ cᵢ•vᵢ` expands as a double sum
  have key : polForm Q (∑ i, c i • v i) (∑ j, c j • v j)
      = ∑ i, ∑ j, c i * c j * polForm Q (v i) (v j) := by
    calc polForm Q (∑ i, c i • v i) (∑ j, c j • v j)
        = ∑ j, c j * polForm Q (∑ i, c i • v i) (v j) :=
          polForm_sum_right Q hpar hhom hpol Finset.univ c v _
      _ = ∑ j, c j * (∑ i, c i * polForm Q (v i) (v j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [polForm_sum_left Q hpar hhom hpol Finset.univ c v (v j)]
      _ = ∑ j, ∑ i, c j * (c i * polForm Q (v i) (v j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, c j * (c i * polForm Q (v i) (v j)) := Finset.sum_comm
      _ = ∑ i, ∑ j, c i * c j * polForm Q (v i) (v j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [← polForm_self Q hhom (∑ i, c i • v i), key]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold polForm
  ring

end

end Work.BoseFixB2.Polar
