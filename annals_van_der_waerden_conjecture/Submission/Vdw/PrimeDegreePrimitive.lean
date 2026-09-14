import Submission.Vdw.PrimitiveCase

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Imprimitivity in prime degree: the Widmer input is vacuous when `n` is prime

Bhargava, *Galois groups of random integer polynomials* (Annals of Math
201(2) (2025)), Theorem 1: for an irreducible `f` the natural action of
`Gal(f)` on its `n` roots is *transitive*
(`irrGalFinHom_pretransitive`), so "not primitive" means "imprimitive".  The
paper handles the imprimitive part of `IrreducibleBad n H` by Widmer's bound
`O(H^(n/2+2))` (only `≤ H^(n-1)` for `n ≥ 6`); for **prime** `n`, however,
there are no transitive imprimitive subgroups of `S_n` at all: a transitive
group of prime degree is primitive.  Mathlib's
`MulAction.IsPreprimitive.of_prime_card` is exactly that group-theoretic
fact, and it makes `ImprimitiveBad n H` *empty* for prime `n`:

* `galPrimitive_of_prime` — every `f ∈ IrreducibleBad n H` (`n` prime) has a
  primitive Galois action;
* `ImprimitiveBad_eq_empty_of_prime`;
* `ImprimitiveBad_isBigO_of_prime` — in particular the imprimitive residual
  bound of the final assembly holds *unconditionally* for prime `n`
  (`n = 3, 5, 7, 11, …`), so for those degrees the challenge theorem needs
  only three of the four residual inputs
  (`PrimeDegreeAssembly.theorem_1_of_perD_prime`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

/-- **Prime degree forces primitivity.**  For `f ∈ IrreducibleBad n H` with `n`
prime, the image of `Gal(f)` in `S_n` under the natural action on the roots
(`irrGalFinHom`) is preprimitive: it is transitive
(`irrGalFinHom_pretransitive`) and acts on the prime-cardinality type
`Fin n` (`MulAction.IsPreprimitive.of_prime_card`). -/
theorem galPrimitive_of_prime {n H : ℕ} (hn : Nat.Prime n) {f : ℤ[X]}
    (hf : f ∈ IrreducibleBad n H) :
    ∃ h : Irreducible (f.map φℚ), galPrimitive f h := by
  classical
  have hn1 : 1 ≤ n := hn.one_le
  have hirr : Irreducible (f.map φℚ) := irreducibleBad_mem_irreducible_rat hn1 hf
  refine ⟨hirr, ?_⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨hirr⟩
  have hbox : f ∈ Box n H := Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf)
  have hdeg : (f.map φℚ).natDegree = n := by
    rw [monic_natDegree_map_rat f hbox.1,
      Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1]
  have hcard : Nat.Prime (Nat.card (Fin ((f.map φℚ).natDegree))) := by
    rw [Nat.card_fin, hdeg]
    exact hn
  haveI : MulAction.IsPretransitive ((irrGalFinHom f).range)
      (Fin ((f.map φℚ).natDegree)) := irrGalFinHom_pretransitive f
  exact MulAction.IsPreprimitive.of_prime_card hcard

/-- **`ImprimitiveBad n H` is empty for prime `n`.** -/
theorem ImprimitiveBad_eq_empty_of_prime (n H : ℕ) (hn : Nat.Prime n) :
    ImprimitiveBad n H = ∅ := by
  classical
  ext f
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hf, hno⟩
  exact hno (galPrimitive_of_prime hn hf)

/-- **The imprimitive residual bound holds unconditionally for prime `n`.**
(The vanishing function is `=O` of anything.) -/
theorem ImprimitiveBad_isBigO_of_prime (n : ℕ) (hn : Nat.Prime n) :
    (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have h : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) = fun _ => 0 := by
    funext H
    rw [ImprimitiveBad_eq_empty_of_prime n H hn]
    simp
  rw [h]
  exact Asymptotics.isBigO_zero _ _

end Submission.Vdw
