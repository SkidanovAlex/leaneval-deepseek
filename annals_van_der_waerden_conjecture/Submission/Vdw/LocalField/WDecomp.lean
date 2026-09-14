import Mathlib
import Submission.Vdw.LocalField.CoeffIntegral
import Submission.Vdw.LocalField.OWBasic

open Classical
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, (b2)): power-basis decomposition of `W` (glue input)

This module provides the decomposition machinery to apply the tuple-level
coefficient lemmas L-A/L-B (`CoeffIntegral.coeffs_integral_of_norm_le_one`,
`coeffs_p_divisible_of_norm_lt_one`) to actual elements `w ∈ 𝒪_W`:

* `norm_sum_le_of_le` / `norm_sum_type_le_of_le` — generic ultrametric
  finite-sum norm bound: a finite sum of terms of norm ≤ 1 has norm ≤ 1
  (Finset induction with `IsUltrametricDist.norm_add_le_max`).
* `wPowerBasis p P α hα` — the power basis of `W = ℚ_p(ζ) = Wk p P α` over
  `QpAdic p` (`IntermediateField.adjoin.powerBasis`), with `gen = zetaW`
  (`wPowerBasis_gen`) and `dim = P.inertiaDeg ℤ` (`wPowerBasis_dim`).
* `wBasis p P α hα hgen` — the basis reindexed to `Fin f` (`f :=
  P.inertiaDeg ℤ`) by a value-preserving equivalence (`toFun j :=
  ⟨(j : ℕ), proof⟩`), so the basis vector at `j` is exactly `ζ^j`:
  `wBasis_apply_value`.

NEXT (recorded in Roadmap Session-93): `w_value_eq_wSum` — the value
equality `(w : kpAdic) = wSum p P α (wBasis.repr w)` (from
`Module.Basis.sum_repr` + the ℚ_p-linearity of the Wk→kpAdic embedding +
`wBasis_apply_value`); then the OW closure: for `w ∈ 𝒪_W` with
`resOW w = 0` (`‖(w : kpAdic)‖ < 1` via `OWBasic`-style norm lemma),
L-A/L-B give integrality and `p`-divisibility of the coefficients
`c := wBasis.repr w`; `w' := Σ_j (c j / p) • wBasis j` has norm ≤ 1
(`norm_sum_type_le_of_le` + `norm_div`) and `w = p·w'`, closing
`OW_ker ≤ Ideal.span {pOW}` (e(W)=1).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- generic ultrametric finite-sum norm bound: a finite sum of terms of norm
≤ 1 has norm ≤ 1. -/
lemma norm_sum_le_of_le {S : Type*} [SeminormedAddCommGroup S] [IsUltrametricDist S]
    {ι : Type*} (s : Finset ι) (x : ι → S)
    (h : ∀ i, i ∈ s → ‖x i‖ ≤ 1) : ‖s.sum x‖ ≤ 1 := by
  classical
  have hmain : ∀ s : Finset ι, (∀ i, i ∈ s → ‖x i‖ ≤ 1) → ‖s.sum x‖ ≤ 1 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro h
      simp
    · intro a s has ih h
      rw [Finset.sum_insert has]
      calc
        ‖x a + s.sum x‖ ≤ max ‖x a‖ ‖s.sum x‖ :=
          IsUltrametricDist.norm_add_le_max (x a) (s.sum x)
        _ ≤ max (1 : ℝ) 1 := by
          exact max_le_max (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (by simp [hi])))
        _ = 1 := by norm_num
  exact hmain s h

/-- the type-level version. -/
lemma norm_sum_type_le_of_le {S : Type*} [SeminormedAddCommGroup S] [IsUltrametricDist S]
    {ι : Type*} [Fintype ι] (x : ι → S)
    (h : ∀ i, ‖x i‖ ≤ 1) : ‖∑ i : ι, x i‖ ≤ 1 := by
  simpa using (norm_sum_le_of_le (Finset.univ : Finset ι) x (fun i hi => h i))

/-- power basis of W = ℚ_p(ζ) over QpAdic. -/
noncomputable def wPowerBasis (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0) : PowerBasis (QpAdic p) (Wk p P α) :=
  IntermediateField.adjoin.powerBasis (teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα)

/-- the generator of the power basis is ζ. -/
theorem wPowerBasis_gen (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0) :
    (wPowerBasis p P α hα).gen = zetaW p P α := by
  dsimp [wPowerBasis]
  rw [IntermediateField.adjoin.powerBasis_gen]
  rfl

/-- the dimension is f := P.inertiaDeg ℤ. -/
theorem wPowerBasis_dim (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (wPowerBasis p P α hα).dim = P.inertiaDeg ℤ := by
  classical
  let pb : PowerBasis (QpAdic p) (Wk p P α) := wPowerBasis p P α hα
  have hfr := PowerBasis.finrank pb
  have hW := finrank_QpAdic_Wk_eq_inertiaDeg (p := p) (P := P) (α := α) hα hgen
  rw [← hfr]
  exact hW

/-- the power-basis reindexed to `Fin f` (`f := P.inertiaDeg ℤ`): the basis
vector at `j` is `ζ^j` (the reindexing equiv preserves the natural value). -/
noncomputable def wBasis (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Module.Basis (Fin (P.inertiaDeg ℤ)) (QpAdic p) (Wk p P α) := by
  classical
  let pb := wPowerBasis p P α hα
  let e : Fin (P.inertiaDeg ℤ) ≃ Fin pb.dim := {
    toFun := fun j => ⟨(j : ℕ), by
      have hdim := wPowerBasis_dim p P α hα hgen
      rw [hdim]
      exact j.2⟩
    invFun := fun i => ⟨(i : ℕ), by
      have hdim := wPowerBasis_dim p P α hα hgen
      rw [← hdim]
      exact i.2⟩
    left_inv := by
      intro j
      apply Fin.ext
      rfl
    right_inv := by
      intro i
      apply Fin.ext
      rfl }
  exact pb.basis.reindex e.symm

/-- the basis vector at `j` is `ζ^j` (as a value). -/
theorem wBasis_apply_value (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (j : Fin (P.inertiaDeg ℤ)) :
    ((wBasis p P α hα hgen j : Wk p P α) : kpAdic p P) =
      (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ)) := by
  classical
  let pb := wPowerBasis p P α hα
  let e : Fin (P.inertiaDeg ℤ) ≃ Fin pb.dim := {
    toFun := fun j => ⟨(j : ℕ), by
      have hdim := wPowerBasis_dim p P α hα hgen
      rw [hdim]
      exact j.2⟩
    invFun := fun i => ⟨(i : ℕ), by
      have hdim := wPowerBasis_dim p P α hα hgen
      rw [← hdim]
      exact i.2⟩
    left_inv := by intro j; apply Fin.ext; rfl
    right_inv := by intro i; apply Fin.ext; rfl }
  change (((pb.basis.reindex e.symm) j : Wk p P α) : kpAdic p P)
      = (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ))
  rw [Module.Basis.reindex_apply]
  -- (reindex e.symm) j = pb.basis ((e.symm).symm j) = pb.basis (e j)
  change (((pb.basis (e j) : Wk p P α) : kpAdic p P))
      = (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ))
  rw [PowerBasis.basis_eq_pow]
  have hgenw : pb.gen = zetaW p P α := wPowerBasis_gen p P α hα
  -- exponent: (e j : Fin pb.dim): val = (j : ℕ) by rfl (e j = ⟨(j:ℕ), _⟩):
  calc
    (((pb.gen ^ (((e j : Fin pb.dim) : ℕ)) : Wk p P α) : kpAdic p P))
        = ((pb.gen : kpAdic p P) ^ (((e j : Fin pb.dim) : ℕ))) := by rfl
    _ = ((pb.gen : kpAdic p P) ^ (j : ℕ)) := by rfl
    _ = ((zetaW p P α : kpAdic p P) ^ (j : ℕ)) := by rw [hgenw]
    _ = (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ)) := by rfl

lemma Wk_coe_sum_finset (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (s : Finset (Fin (P.inertiaDeg ℤ)))
    (x : Fin (P.inertiaDeg ℤ) → Wk p P α) :
    (((s.sum x : Wk p P α)) : kpAdic p P) = s.sum (fun j => ((x j : Wk p P α) : kpAdic p P)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has]
    rw [Finset.sum_insert has]
    rw [show ((((x a + s.sum x : Wk p P α))) : kpAdic p P) =
        ((x a : Wk p P α) : kpAdic p P) + (((s.sum x : Wk p P α)) : kpAdic p P) by rfl]
    rw [ih]
lemma Wk_coe_sum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (x : Fin (P.inertiaDeg ℤ) → Wk p P α) :
    (((∑ j : Fin (P.inertiaDeg ℤ), x j : Wk p P α)) : kpAdic p P)
      = ∑ j : Fin (P.inertiaDeg ℤ), ((x j : Wk p P α) : kpAdic p P) := by
  classical
  change ((((Finset.univ : Finset (Fin (P.inertiaDeg ℤ))).sum x : Wk p P α)) : kpAdic p P)
      = (Finset.univ : Finset (Fin (P.inertiaDeg ℤ))).sum (fun j => ((x j : Wk p P α) : kpAdic p P))
  exact Wk_coe_sum_finset p P α Finset.univ x

theorem w_value_eq_wSum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (w : Wk p P α) :
    ((w : Wk p P α) : kpAdic p P) =
      wSum p P α (fun j : Fin (P.inertiaDeg ℤ) => (wBasis p P α hα hgen).repr w j) := by
  classical
  let c : Fin (P.inertiaDeg ℤ) → QpAdic p :=
    fun j : Fin (P.inertiaDeg ℤ) => (wBasis p P α hα hgen).repr w j
  calc
    ((w : Wk p P α) : kpAdic p P)
        = (((∑ j : Fin (P.inertiaDeg ℤ), c j • wBasis p P α hα hgen j : Wk p P α)) : kpAdic p P) := by
          rw [← (wBasis p P α hα hgen).sum_repr w]
    _ = ∑ j : Fin (P.inertiaDeg ℤ),
          (((c j) • (wBasis p P α hα hgen j) : Wk p P α) : kpAdic p P) := by
          exact Wk_coe_sum p P α (fun j : Fin (P.inertiaDeg ℤ) => c j • wBasis p P α hα hgen j)
    _ = ∑ j : Fin (P.inertiaDeg ℤ),
          (algebraMap (QpAdic p) (kpAdic p P) (c j)) *
            (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show (((c j) • (wBasis p P α hα hgen j) : Wk p P α) : kpAdic p P) =
              (algebraMap (QpAdic p) (kpAdic p P) (c j)) *
                (((wBasis p P α hα hgen j : Wk p P α) : kpAdic p P)) by rfl]
          rw [wBasis_apply_value p P α hα hgen j]
    _ = wSum p P α c := by
          rfl
theorem basisComb_value_eq_wSum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (c : Fin (P.inertiaDeg ℤ) → QpAdic p) :
    (((∑ j : Fin (P.inertiaDeg ℤ), c j • wBasis p P α hα hgen j : Wk p P α)) : kpAdic p P)
      = wSum p P α c := by
  classical
  calc
    (((∑ j : Fin (P.inertiaDeg ℤ), c j • wBasis p P α hα hgen j : Wk p P α)) : kpAdic p P)
        = ∑ j : Fin (P.inertiaDeg ℤ),
            (((c j) • (wBasis p P α hα hgen j) : Wk p P α) : kpAdic p P) := by
          exact Wk_coe_sum p P α (fun j : Fin (P.inertiaDeg ℤ) => c j • wBasis p P α hα hgen j)
    _ = ∑ j : Fin (P.inertiaDeg ℤ),
          (algebraMap (QpAdic p) (kpAdic p P) (c j)) *
            (((teich p P α : kpInt p P) : kpAdic p P) ^ (j : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show (((c j) • (wBasis p P α hα hgen j) : Wk p P α) : kpAdic p P) =
              (algebraMap (QpAdic p) (kpAdic p P) (c j)) *
                (((wBasis p P α hα hgen j : Wk p P α) : kpAdic p P)) by rfl]
          rw [wBasis_apply_value p P α hα hgen j]
    _ = wSum p P α c := by rfl

end
end Submission.Vdw.LocalField
