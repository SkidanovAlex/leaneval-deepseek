import Mathlib
import Submission.Vdw.LocalField.WildWitnessReduction
import Submission.Commons.LinearAlgebra.FreeModule.card_eq_card_pow_finrank
import Submission.Commons.Algebra.Trace.trace_one_eq_finrank

open scoped NumberField WithZero Topology
open IsDedekindDomain
open IsLocalRing
open UniqueFactorizationMonoid
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# SinglePrimeWitness — the p∤f wild witness (S1 gate, step (e3), case 1)

`WildWitnessReduction.exists_wild_witness_of_nonzero_trace` reduces the
level-`n` wild witness to finding `z : 𝓞K` whose `P^(e·n)`-class has
nonzero trace over `R := ℤ/(p^n)`.  This module produces that `z` in the
case where `p ∤ f := P.inertiaDeg ℤ` — then `z := 1` works: the trace of
`1` on the free rank-`e·f` quotient `A := 𝓞K ⧸ P^(e·n)` over `R` is
`(e·f : R)` (`trace_one_eq_finrank`), which is nonzero in `R = ℤ/(p^n)`
at the level `n := v + 1`, `v := padicValNat p e` (since `p^(v+1) ∤ e·f`
whenever `p ∤ f`; `e = p^v·(p-free)`, `padicValNat p (e·f) = v`).

Structure (all statements in namespace Submission.Vdw.LocalField, clean
axioms):

* `natCard_quotient_Ppow` — `Nat.card (𝓞K ⧸ P^m) = (p ^ f) ^ m` for a
  maximal `P` over `(p)` (`absNorm` + `pow_inertiaDeg` + `cardQuot_pow`);
* `card_quotientRamIdxPow` — `Nat.card (𝓞K ⧸ P^(e·n)) =
  (p ^ n) ^ (e·f)` (level-`n` quotient cardinality);
* `finrank_quotientRamIdxPow` — `Module.finrank R A = e·f`
  (`card_eq_card_pow_finrank` + injectivity of `x ↦ (p^n)^x`);
* **`tr_one_quotientRamIdxPow`** — `Algebra.trace R A 1 = (e·f : R)` on
  the free rank-`e·f` quotient;
* **`exists_wild_witness_of_not_dvd_inertiaDeg`** — the witness theorem:
  `p ∤ f` ⟹ `∃ y ∈ Q^(v+1), ¬ p^(v+1) ∣ Tr_{K/ℚ}(y)` — composing
  `tr_one_quotientRamIdxPow` (z = 1) with the reduction.

This closes S1 (the per-prime wild different bound `hwild`) for every prime
with `p ∤ f`; the remaining `p | f` (and `p | e`) case needs the residue
trace-level construction (Roadmap Session-131 notes).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **Quotient cardinality at a prime power**: `Nat.card (𝓞K ⧸ P^m) =
(p ^ f) ^ m` for `P` maximal over `(p)`, `f := P.inertiaDeg ℤ`. -/
lemma natCard_quotient_Ppow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (m : ℕ) :
    Nat.card ((𝓞 K) ⧸ P ^ m) = (p ^ P.inertiaDeg ℤ) ^ m := by
  classical
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  have hP : P ≠ ⊥ := by
    have hpne : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  calc
    Nat.card ((𝓞 K) ⧸ P ^ m) = Ideal.absNorm (P ^ m) := by
      rw [Ideal.absNorm_apply]
      rfl
    _ = (Ideal.absNorm P) ^ m := by
      rw [map_pow]
    _ = (p ^ P.inertiaDeg ℤ) ^ m := by
      rw [← Ideal.pow_inertiaDeg (R := 𝓞 K) p P]

/-- **Level-`n` quotient cardinality**: `Nat.card (𝓞K ⧸ P^(e·n)) =
(p ^ n) ^ (e·f)` with `e := P.ramificationIdx ℤ`, `f := P.inertiaDeg ℤ`. -/
lemma card_quotientRamIdxPow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) :
    Nat.card ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)) =
      (p ^ n) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
  classical
  let e := P.ramificationIdx ℤ
  let f := P.inertiaDeg ℤ
  have h1 : Nat.card ((𝓞 K) ⧸ P ^ (e * n)) = (p ^ n) ^ (e * f) := by
    calc
      Nat.card ((𝓞 K) ⧸ P ^ (e * n))
          = (p ^ f) ^ (e * n) := by
            simpa [e, f] using (natCard_quotient_Ppow (p := p) (P := P) (e * n))
      _ = p ^ (f * (e * n)) := by rw [← pow_mul]
      _ = p ^ (n * (e * f)) := by
            congr 1
            ring
      _ = (p ^ n) ^ (e * f) := by
            rw [pow_mul]
  calc
    Nat.card ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
        = Nat.card ((𝓞 K) ⧸ P ^ (e * n)) := by
          rfl
    _ = (p ^ n) ^ (e * f) := h1
    _ = (p ^ n) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
          rfl

/-- **The free rank**: `Module.finrank R A = e·f` for
`R := ℤ ⧸ (p^n)`, `A := 𝓞K ⧸ P^(e·n)` (given the splitting data), via
`card_eq_card_pow_finrank` and injectivity of `x ↦ (p^n)^x`. -/
theorem finrank_quotientRamIdxPow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (n : ℕ) (hn : 0 < n) :
    Module.finrank (ℤ ⧸ (pPowIdeal p n))
        ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)) =
      P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  classical
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  letI : Algebra R A := instAlgebraQuotientRamIdxPow p P n
  haveI : Module.Finite R A := module_finite_quotientRamIdxPow p P n
  haveI : Module.Free R A := module_free_quotientRamIdxPow p P Q hsup hspl n hn
  haveI : Finite R := by
    have hpne : (Ideal.span ({((p ^ n : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
      intro hz
      have hn0 : (p ^ n : ℕ) ≠ 0 := pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
      exact (Int.ofNat_ne_zero.mpr hn0) (Ideal.span_singleton_eq_bot.mp hz)
    dsimp [R]
    exact Ring.HasFiniteQuotients.finiteQuotient (R := ℤ) hpne
  haveI : Finite A := by
    dsimp [A]
    exact finite_quotientRamIdxPow p P n
  have hcardR : Nat.card R = p ^ n := by
    dsimp [R]
    calc
      Nat.card (ℤ ⧸ (Ideal.span ({((p ^ n : ℕ) : ℤ)} : Set ℤ)))
          = Nat.card (ZMod (((p ^ n : ℕ) : ℤ).natAbs)) :=
            Nat.card_congr (Int.quotientSpanEquivZMod ((p ^ n : ℕ) : ℤ)).toEquiv
      _ = p ^ n := by
            have hnat : ((p ^ n : ℕ) : ℤ).natAbs = p ^ n := by simp
            rw [hnat]
            simp
  have hcardA : Nat.card A = (Nat.card R) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
    calc
      Nat.card A = (p ^ n) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
            dsimp [A]
            exact card_quotientRamIdxPow p P n
      _ = (Nat.card R) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
            rw [hcardR]
  have hmain := Commons.LinearAlgebra.FreeModule.card_eq_card_pow_finrank (R := R) (M := A)
  have hbase : 1 < Nat.card R := by
    rw [hcardR]
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have h1 : p ^ 1 ≤ p ^ n := Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : 1 ≤ n)
    have hp1 : 2 ≤ p ^ 1 := by simpa using hp2
    exact lt_of_lt_of_le (by norm_num : 1 < 2) (le_trans hp1 h1)
  have heq : (Nat.card R) ^ Module.finrank R A =
      (Nat.card R) ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
    rw [← hmain]
    exact hcardA
  exact Nat.pow_right_injective hbase heq

/-- **The trace of 1**: `Algebra.trace R A 1 = (e·f : R)` on the level-`n`
quotient. -/
theorem tr_one_quotientRamIdxPow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (n : ℕ) (hn : 0 < n) :
    Algebra.trace (ℤ ⧸ (pPowIdeal p n))
        ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)) (1 : _) =
      (P.ramificationIdx ℤ * P.inertiaDeg ℤ : _) := by
  classical
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  letI : Algebra R A := instAlgebraQuotientRamIdxPow p P n
  haveI : Module.Finite R A := module_finite_quotientRamIdxPow p P n
  haveI : Module.Free R A := module_free_quotientRamIdxPow p P Q hsup hspl n hn
  rw [Commons.Algebra.Trace.trace_one_eq_finrank (R := R) (A := A)]
  rw [finrank_quotientRamIdxPow p P Q hsup hspl n hn]

/-- **p ∤ f wild witness**: if `p ∤ P.inertiaDeg ℤ` then the level-
`v + 1` (`v := padicValNat p e`) wild witness exists: `z := 1` has
trace `e·f ≠ 0 (mod p^(v+1))`. -/
theorem exists_wild_witness_of_not_dvd_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (hpf : ¬ (p : ℕ) ∣ P.inertiaDeg ℤ) :
    ∃ y : 𝓞 K, y ∈ Q ^ (padicValNat p (P.ramificationIdx ℤ) + 1) ∧
      ¬ (p : ℤ) ^ (padicValNat p (P.ramificationIdx ℤ) + 1) ∣
        Algebra.intTrace ℤ (𝓞 K) y := by
  classical
  let e := P.ramificationIdx ℤ
  let f := P.inertiaDeg ℤ
  let v := padicValNat p e
  let n := v + 1
  haveI : P.IsPrime := (inferInstance : P.IsMaximal).isPrime
  have hn : 0 < n := by
    dsimp [n]
    omega
  -- arithmetic: p^n ∤ e·f  (since p ∤ f and v = padicValNat p e)
  have he0 : e ≠ 0 := by
    dsimp [e]
    exact (Ideal.ramificationIdx_pos P ℤ).ne'
  have hf0 : f ≠ 0 := by
    dsimp [f]
    exact (Ideal.inertiaDeg_pos P ℤ).ne'
  have hv : padicValNat p (e * f) = v := by
    rw [padicValNat.mul he0 hf0]
    have hpf0 : padicValNat p f = 0 := padicValNat.eq_zero_of_not_dvd hpf
    rw [hpf0, add_zero]
  have hef : ¬ p ^ n ∣ e * f := by
    have hns : ¬ p ^ (padicValNat p (e * f) + 1) ∣ e * f :=
      pow_succ_padicValNat_not_dvd (n := e * f) (mul_ne_zero he0 hf0)
    have hne : ¬ p ^ (v + 1) ∣ e * f := by
      simpa [hv] using hns
    simpa [n] using hne
  -- assemble: z := 1 has nonzero A-class trace at level n
  let R := ℤ ⧸ (pPowIdeal p n)
  let A := (𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)
  letI : Algebra R A := instAlgebraQuotientRamIdxPow p P n
  haveI : Module.Finite R A := module_finite_quotientRamIdxPow p P n
  haveI : Module.Free R A := module_free_quotientRamIdxPow p P Q hsup hspl n hn
  apply exists_wild_witness_of_nonzero_trace (p := p) (P := P) (Q := Q) hsup hspl n hn
  refine ⟨(1 : 𝓞 K), ?_⟩
  have hmk1 : Ideal.Quotient.mk (P ^ (P.ramificationIdx ℤ * n)) (1 : 𝓞 K) = (1 : A) := by
    simp
  rw [hmk1]
  have htr := tr_one_quotientRamIdxPow (p := p) (P := P) (Q := Q) hsup hspl n hn
  rw [htr]
  have hefR : ((e * f : ℕ) : R) ≠ 0 := by
    intro hz
    apply hef
    have hmem : ((e * f : ℕ) : ℤ) ∈ pPowIdeal p n := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      simpa using hz
    rw [Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨c, hc⟩
    -- hc : ((e*f : ℕ) : ℤ) = ((p^n : ℕ) : ℤ) * c
    exact (Int.natCast_dvd_natCast.mp (show ((p ^ n : ℕ) : ℤ) ∣ ((e * f : ℕ) : ℤ) from ⟨c, hc⟩))
  simpa [e, f] using hefR

/-- **p ∤ f per-prime wild different bound**: for `p ∤ P.inertiaDeg ℤ`
the wild bound `m_P ≤ e − 1 + e·v_p(e)` holds (`wild_count_le_of_wild_witness`
fed with the p∤f witness) — i.e. the `hwild` hypothesis of
`WildBound.discrVal_le_wild` is satisfied at every prime not dividing the
inertia degree.  (The tame case `p ∤ e` was already closed unconditionally;
this closes `p | e` with `p ∤ f`.) -/
theorem wild_count_le_of_not_dvd_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) (hsup : P ⊔ Q = ⊤)
    (hspl : (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) =
      P ^ P.ramificationIdx ℤ * Q)
    (hpf : ¬ (p : ℕ) ∣ P.inertiaDeg ℤ) :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤
      P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  classical
  rcases (exists_wild_witness_of_not_dvd_inertiaDeg (p := p) (P := P) (Q := Q) hsup hspl hpf)
    with ⟨y, hyQ, hy⟩
  exact wild_count_le_of_wild_witness (p := p) (P := P) (Q := Q) hsup hspl y hyQ hy


end
end Submission.Vdw.LocalField
