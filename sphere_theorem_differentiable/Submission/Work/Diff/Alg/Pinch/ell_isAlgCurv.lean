import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking transform preserves algebraic curvature tensors

`Work.Diff.Alg.Pinch.ell a b R = R + b • (Ric₀(R) ∧ id) + (a/n · scal R) • (id ∧ id)` is the
linear transformation of Böhm–Wilking (Lemma 3.4) used to build the pinching cones
`Ccone a b p = ell a b '' Dpic p`.

The set of algebraic curvature tensors (`Submission.Diff.Alg.IsAlgCurv`: antisymmetry in the first
pair, symmetry of the two pairs, first Bianchi) is a *linear* subspace of `Curv4 n`, and the
Kulkarni–Nomizu product `A ∧ B` of two **symmetric** `2`-tensors is an algebraic curvature tensor.
Since `ric R`, `ric0 R` and `id2 n` are symmetric whenever `R` is algebraic, `ell a b` maps
algebraic curvature tensors to algebraic curvature tensors.

This is the "curvature-type" bookkeeping behind the Böhm–Wilking cone construction: every cone
`Ccone a b p` consists of algebraic curvature tensors.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Symmetry of the `2`-tensors appearing in `ell` -/

/-- The Ricci tensor of an algebraic curvature tensor is symmetric.  Only the pair symmetry
(the second component of `IsAlgCurv`) is used. -/
lemma ric_symm {R : Curv4 n} (hR : IsAlgCurv R) (i j : Fin n) : ric R i j = ric R j i := by
  simp only [ric]
  exact Finset.sum_congr rfl (fun k _ => hR.2.1 k j k i)

/-- The traceless Ricci tensor of an algebraic curvature tensor is symmetric. -/
lemma ric0_symm {R : Curv4 n} (hR : IsAlgCurv R) (i j : Fin n) : ric0 R i j = ric0 R j i := by
  simp only [ric0]
  rw [ric_symm hR i j, id2_symm i j]

/-! ## The Kulkarni–Nomizu product of symmetric tensors is algebraic -/

/-- The Kulkarni–Nomizu product `A ∧ B` of two symmetric `2`-tensors is an algebraic curvature
tensor.  (Antisymmetry in the first pair needs no symmetry; pair symmetry and the first Bianchi
identity need exactly the symmetry of `A` and `B`.) -/
lemma knProd_isAlgCurv {A B : Fin n → Fin n → ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i) :
    IsAlgCurv (knProd A B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp only [knProd]
    ring
  · intro i j k l
    simp only [knProd]
    rw [hA k i, hA k j, hA l i, hA l j, hB l j, hB l i, hB k j, hB k i]
    ring
  · intro i j k l
    simp only [knProd]
    rw [hA j i, hA k i, hA k j, hB j i, hB k i, hB k j]
    ring

/-! ## `IsAlgCurv` is preserved by linear combinations -/

/-- A sum of algebraic curvature tensors is algebraic. -/
lemma isAlgCurv_add {R S : Curv4 n} (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (R + S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l; simp only [Pi.add_apply]; linarith [hR.1 i j k l, hS.1 i j k l]
  · intro i j k l; simp only [Pi.add_apply]; linarith [hR.2.1 i j k l, hS.2.1 i j k l]
  · intro i j k l
    simp only [Pi.add_apply]
    linear_combination hR.2.2 i j k l + hS.2.2 i j k l

/-- A scalar multiple of an algebraic curvature tensor is algebraic. -/
lemma isAlgCurv_smul (c : ℝ) {R : Curv4 n} (hR : IsAlgCurv R) : IsAlgCurv (c • R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l; simp only [Pi.smul_apply]; linear_combination c * (hR.1 i j k l)
  · intro i j k l; simp only [Pi.smul_apply]; linear_combination c * (hR.2.1 i j k l)
  · intro i j k l; simp only [Pi.smul_apply]; linear_combination c * (hR.2.2 i j k l)

/-! ## The main statement -/

theorem ell_isAlgCurv (n : ℕ) (a b : ℝ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Submission.Diff.Alg.IsAlgCurv (Work.Diff.Alg.Pinch.ell a b R) := by
  have h1 : IsAlgCurv (knProd (ric0 R) (id2 n)) :=
    knProd_isAlgCurv (fun i j => ric0_symm hR i j) (fun i j => id2_symm i j)
  have h2 : IsAlgCurv (knProd (id2 n) (id2 n)) :=
    knProd_isAlgCurv (fun i j => id2_symm i j) (fun i j => id2_symm i j)
  rw [ell]
  exact isAlgCurv_add (isAlgCurv_add hR (isAlgCurv_smul b h1))
    (isAlgCurv_smul (a / (n : ℝ) * scalAlg R) h2)

end Work.Diff.Alg.Pinch
