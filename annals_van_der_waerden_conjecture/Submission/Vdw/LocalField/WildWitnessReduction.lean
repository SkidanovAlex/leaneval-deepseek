import Mathlib
import Submission.Vdw.LocalField.CRTTrace

open scoped NumberField WithZero Topology
open IsDedekindDomain
open IsLocalRing
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# WildWitnessReduction — the wild-witness existence is reduced to a
single-prime nonzero-trace (S1 gate, step (e2))

The wild-witness theorem needed to close the S1 gate (the per-prime wild
different bound `hwild` of `WildBound.discrVal_le_wild`, via
`WildDifferent.wild_count_le_of_wild_witness`) asserts, for each prime `p`
and maximal `P` over `(p)` with splitting data `P ⊔ Q = ⊤`,
`(p)·𝓞K = P^e·Q` (`e := P.ramificationIdx ℤ`):

    ∃ y : 𝓞K, y ∈ Q^(v+1) ∧ ¬ p^(v+1) ∣ Tr_{K/ℚ}(y),   v := padicValNat p e.

This module reduces that to a single-prime trace statement, in two clean
steps:

* `exists_crt_lift` (generic, any commutative ring): comaximal ideals `I`,
  `J` give, for every `x`, an element `y ≡ x (mod I)` with `y ∈ J`
  (`y := x·b` for a decomposition `1 = a + b`, `a ∈ I`, `b ∈ J`);
* **`exists_wild_witness_of_nonzero_trace`**: given `z : 𝓞K` whose
  `P^(e·n)`-class has nonzero trace over `R := ℤ/(p^n)`, the CRT lift
  `y ∈ Q^n` of `z` (same `P^(e·n)`-class) is a wild witness at level `n`
  (`p^n ∤ Tr_{K/ℚ}(y)`), by `crt_trace_identity`
  (`Tr_R(A)(mk_A y) = mk_R(Tr_{K/ℚ}(y))` for `y ∈ Q^n`).

The remaining content of (e3) is then to produce the `z` itself — the
level-`k` trace congruence `Tr_R(A)(mk_A z) ≡ u·(residue trace)·p^k`
(`e = p^k·u`, `p ∤ u`) via the residue-trace atoms (TraceResidue, KapTrace,
TowerDegree) — feeding this module's output
`wild_count_le_of_wild_witness` → `hwild` → S1.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **CRT lift (generic)**: comaximal ideals `I ⊔ J = ⊤` give, for every
`x`, an element `y` with `x - y ∈ I` and `y ∈ J` (write `1 = a + b` with
`a ∈ I`, `b ∈ J`, take `y := x·b`). -/
lemma exists_crt_lift {R : Type*} [CommRing R] (I J : Ideal R) (hsup : I ⊔ J = ⊤)
    (x : R) : ∃ y : R, x - y ∈ I ∧ y ∈ J := by
  classical
  have hone : (1 : R) ∈ I ⊔ J := by rw [hsup]; trivial
  rcases (Submodule.mem_sup.mp hone) with ⟨a, haI, b, hbJ, hab⟩
  refine ⟨x * b, ?_, ?_⟩
  · have hx : x - x * b = x * a := by
      calc
        x - x * b = x * (1 - b) := by ring
        _ = x * a := by rw [← hab]; ring
    rw [hx]
    exact (Ideal.mul_mem_left I x haI)
  · exact (Ideal.mul_mem_left J x hbJ)

/-- **Wild-witness reduction (level `n`)**: if some element `z : 𝓞K` has
nonzero `P^(e·n)`-class trace over `R := ℤ/(p^n)`, then a wild witness
exists at level `n`: an element `y ∈ Q^n` whose integer trace is not
divisible by `p^n`.  (`y` is the CRT lift of `z` into `Q^n`.) -/
theorem exists_wild_witness_of_nonzero_trace (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (n : ℕ) (hn : 0 < n)
    (hnt : ∃ z : 𝓞 K,
      Algebra.trace (ℤ ⧸ (pPowIdeal p n)) ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
        (Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) z) ≠ 0) :
    ∃ y : 𝓞 K, y ∈ Q ^ n ∧
      ¬ (p : ℤ) ^ n ∣ Algebra.intTrace ℤ (𝓞 K) y := by
  classical
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  rcases hnt with ⟨z, hz⟩
  let I : Ideal (𝓞 K) := P ^ (P.ramificationIdx ℤ * n)
  have hsupn : I ⊔ Q ^ n = ⊤ := sup_eq_top_of_pow_pow P Q hsup (P.ramificationIdx ℤ * n) n
  rcases exists_crt_lift I (Q ^ n) hsupn z with ⟨y, hyI, hyQ⟩
  refine ⟨y, hyQ, ?_⟩
  have hmkA : Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) y =
      Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) z := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem y z).mpr
    simpa using (P ^ (P.ramificationIdx ℤ * n)).neg_mem hyI
  have htr : Algebra.trace (ℤ ⧸ (pPowIdeal p n))
        ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
        (Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) y) ≠ 0 := by
    intro hfy
    apply hz
    exact (congrArg (Algebra.trace (ℤ ⧸ (pPowIdeal p n))
        ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))) hmkA).symm.trans hfy
  have hct := crt_trace_identity (p := p) (P := P) (Q := Q) hsup hspl n hn y hyQ
  have hmkne : Ideal.Quotient.mk (pPowIdeal p n) (Algebra.intTrace ℤ (𝓞 K) y) ≠ 0 := by
    rw [← hct]
    exact htr
  intro hdvd
  apply hmkne
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  rw [Ideal.mem_span_singleton]
  rcases hdvd with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    Algebra.intTrace ℤ (𝓞 K) y = (p : ℤ) ^ n * c := hc
    _ = ((p ^ n : ℕ) : ℤ) * c := by rw [Nat.cast_pow]


end
end Submission.Vdw.LocalField
