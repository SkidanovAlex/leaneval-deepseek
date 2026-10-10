import Mathlib
import Submission.Work.MotAS.AsRuleRankDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of the AS Pfaffians `kleinPASm`

`Work.MotAS.kleinPASm a b g k` (`Submission/Work/MotAS/AsRuleRankDefs.lean`) is the `k`-th AS
Pfaffian `p^{AS}_k` written as an element of `MvPolynomial (Fin 5) K`: the five Galois
coordinates `y 0, …, y 4` are replaced by the variables `X 0, …, X 4` and the parameters `a,b,g`
by the constants `C a, C b, C g`.

Each AS Pfaffian is a *quadratic form* in the coordinates: its defining expression
(`Work.MotAS.kleinPAS0`, …, `kleinPAS4` in `Submission/Work/MotAS/ASData.lean`) is a sum of terms
`coefficient · y i · y j` or `coefficient · y i ^ 2` with the coefficient built out of `a, b, g`.
This file records that fact as `IsHomogeneous 2`:

* `kleinPASm_isHomogeneous` — the statement of the node;
* five private lemmas `kleinPAS{k}_homog` — one per Pfaffian, proved uniformly.

## Proof route

After unfolding the definition the goal is `IsHomogeneous 2` of an explicit sum of quadratic
monomials whose coefficients are products of `C _` and numerals.  Three normalisation steps reduce
it to a form in which every summand has the shape `C c * (X i * X j)`:

1. replace the numeral `2` by `C 2` (`MvPolynomial.C (2 : K) = (2 : MvPolynomial _ K)` holds by
   `rfl`), then merge the coefficient factors with the reverse lemmas
   `← MvPolynomial.C_mul`, `← MvPolynomial.C_pow` (this produces a single `C c` per term);
2. replace `X i ^ 2` by `X i * X i` (`pow_two`) and right-associate with `mul_assoc`.

Then `IsHomogeneous.add`/`IsHomogeneous.sub` decompose the sum, and the atom lemma
`isHomogeneous_C_mul_X_mul_X` (`IsHomogeneous.C_mul` applied to a product of two `X`'s, each of
degree `1`) closes every leaf. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotAS.Ker4

open MvPolynomial

/-- A quadratic monomial with an arbitrary coefficient: `C c * (X i * X j)` is homogeneous of
degree `2`. -/
private lemma isHomogeneous_C_mul_X_mul_X {K : Type} [Field K] (c : K) (i j : Fin 5) :
    (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) :
      MvPolynomial (Fin 5) K).IsHomogeneous 2 :=
  (MvPolynomial.isHomogeneous_C (σ := Fin 5) c).mul
    ((MvPolynomial.isHomogeneous_X (R := K) i).mul (MvPolynomial.isHomogeneous_X (R := K) j))

/-- `kleinPAS0` is a quadratic form. -/
private theorem kleinPAS0_homog (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.kleinPAS0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i)).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPAS0]
  have h2 : (2 : MvPolynomial (Fin 5) K) = MvPolynomial.C (2 : K) := rfl
  simp only [h2, ← MvPolynomial.C_mul, ← MvPolynomial.C_pow]
  simp only [pow_two, mul_assoc]
  repeat (first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub)
  all_goals exact isHomogeneous_C_mul_X_mul_X _ _ _

/-- `kleinPAS1` is a quadratic form. -/
private theorem kleinPAS1_homog (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.kleinPAS1 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i)).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPAS1]
  have h2 : (2 : MvPolynomial (Fin 5) K) = MvPolynomial.C (2 : K) := rfl
  simp only [h2, ← MvPolynomial.C_mul, ← MvPolynomial.C_pow]
  simp only [pow_two, mul_assoc]
  repeat (first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub)
  all_goals exact isHomogeneous_C_mul_X_mul_X _ _ _

/-- `kleinPAS2` is a quadratic form. -/
private theorem kleinPAS2_homog (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.kleinPAS2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i)).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPAS2]
  have h2 : (2 : MvPolynomial (Fin 5) K) = MvPolynomial.C (2 : K) := rfl
  simp only [h2, ← MvPolynomial.C_mul, ← MvPolynomial.C_pow]
  simp only [pow_two, mul_assoc]
  repeat (first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub)
  all_goals exact isHomogeneous_C_mul_X_mul_X _ _ _

/-- `kleinPAS3` is a quadratic form. -/
private theorem kleinPAS3_homog (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.kleinPAS3 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i)).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPAS3]
  have h2 : (2 : MvPolynomial (Fin 5) K) = MvPolynomial.C (2 : K) := rfl
  simp only [h2, ← MvPolynomial.C_mul, ← MvPolynomial.C_pow]
  simp only [pow_two, mul_assoc]
  repeat (first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub)
  all_goals exact isHomogeneous_C_mul_X_mul_X _ _ _

/-- `kleinPAS4` is a quadratic form. -/
private theorem kleinPAS4_homog (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotAS.kleinPAS4 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (fun i => MvPolynomial.X i)).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPAS4]
  have h2 : (2 : MvPolynomial (Fin 5) K) = MvPolynomial.C (2 : K) := rfl
  simp only [h2, ← MvPolynomial.C_mul, ← MvPolynomial.C_pow]
  simp only [pow_two, mul_assoc]
  repeat (first | apply MvPolynomial.IsHomogeneous.add | apply MvPolynomial.IsHomogeneous.sub)
  all_goals exact isHomogeneous_C_mul_X_mul_X _ _ _

/-- **Each AS Pfaffian is a quadratic form.**  `kleinPASm a b g k` is the `k`-th Pfaffian
`p^{AS}_k` of the AS (characteristic-`5`) chart, written as a polynomial in the five Galois
coordinates; the defining expression is a sum of monomials of total degree `2`. -/
theorem kleinPASm_isHomogeneous (K : Type) [Field K] [CharP K 5] (a b g : K) (k : Fin 5) :
    (Work.MotAS.kleinPASm a b g k).IsHomogeneous 2 := by
  rw [Work.MotAS.kleinPASm, Work.MotAS.kleinPAS]
  fin_cases k
  · exact kleinPAS0_homog K a b g
  · exact kleinPAS1_homog K a b g
  · exact kleinPAS2_homog K a b g
  · exact kleinPAS3_homog K a b g
  · exact kleinPAS4_homog K a b g

end Work.MotAS.Ker4
