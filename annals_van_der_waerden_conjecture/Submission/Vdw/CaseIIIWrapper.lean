import Mathlib
import Submission.Vdw.CaseIIIAssembly
import Submission.Commons.Analysis.Asymptotics.Ints.pow_two_mul_add_one
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): uniform-in-threshold box count and the power-of-`H`
threshold form

`CaseIIIAssembly.caseIII_subcase2_box_ncard_le` bounds, for a **fixed** prime
threshold `B` (`n < B`), the box polynomials admitting an admissible squarefree
divisor `A ∈ Adm B n H (u_f)` of `DD(u_f)` (`A > H`, primes `≥ B`), by
`(2H+1)^(n-1) · 2·(2(n-1))^(K·(log_B H + 1))` (eventually in `H`).  In the
eventual Case-III subcase-(ii) application the threshold is not fixed but grows
with `H` (`B = ⌈H^(δ/2)⌉`, `δ/2 = 1/(4n)`), and the whole point of the
subcase-(ii) split is that then `log_B H = O(1)`, killing the
`(2(n-1))^(K(log_B H+1))` factor.

This module makes that precise, in a real-power-free form: whenever the
threshold `B` satisfies `n < B` and `H ≤ B^M` (i.e. `B ≥ H^(1/M)`), the
`log_B H ≤ M` bound makes the whole `(2(n-1))^(K(log_B H+1))` factor bounded by
a constant depending only on `n`, `K`, `M` — so the count is eventually
`O((2H+1)^(n-1))`, uniformly over *all* such `B` (which is what the field-side
plumbing needs, since its `B` depends on `H`).

Contents:
* `CaseIIIArithSet B n H` — the arithmetic set counted by
  `caseIII_subcase2_box_ncard_le` (a named definition, reusable by the
  field-side plumbing);
* `log_le_of_le_pow` — `H ≤ B^M` and `1 < B` give `Nat.log B H ≤ M`;
* `caseIII_subcase2_box_ncard_uniform` — the box bound with `B` universally
  quantified (`∃K, ∀ᶠH, ∀B, n < B → …`): the threshold may depend on `H`;
* `caseIII_subcase2_threshold_le` — the log-free form: for every `M`,
  `∃C, ∀ᶠH, ∀B, n < B → H ≤ B^M → #CaseIIIArithSet B n H ≤ C·(2H+1)^(n-1)`.
-/

namespace Submission.Vdw

/-- The Case-III subcase-(ii) arithmetic set: box polynomials whose double
discriminant `DD(u_f)` does not vanish and which admit an admissible divisor
`A ∈ Adm B n H (u_f)` with `p | Disc(f)` for every prime `p | A`. -/
noncomputable def CaseIIIArithSet (B n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ Box n H ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
    ∃ A ∈ Adm B n H (upperCoeffs n f),
      ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr f}

/-- `H ≤ B^M` with `1 < B` gives `Nat.log B H ≤ M` (powers of `B` are
monotone and `Nat.log` is monotone in its right argument). -/
lemma log_le_of_le_pow {B H M : ℕ} (hB : 1 < B) (h : H ≤ B ^ M) :
    Nat.log B H ≤ M := by
  calc
    Nat.log B H ≤ Nat.log B (B ^ M) := Nat.log_mono_right h
    _ = M := Nat.log_pow hB M

/-- **Uniform box count.**  The `B` of
`caseIII_subcase2_box_ncard_le` may depend on `H`: for *every* `B` with
`n < B`, the subcase-(ii) arithmetic set is bounded by
`(2H+1)^(n-1) · 2·(2(n-1))^(K·(log_B H + 1))` — eventually in `H`, with `K`
independent of `B` (proof: re-run the assembly of
`caseIII_subcase2_box_ncard_le` with `B` abstract; the per-`u` bound
`perUpper_ncard_le` is pointwise uniform in `B`). -/
theorem caseIII_subcase2_box_ncard_uniform (n : ℕ) (hn : 3 ≤ n) :
    ∃ K : ℕ, ∀ᶠ H : ℕ in atTop, ∀ B : ℕ, n < B →
      (CaseIIIArithSet B n H).ncard ≤
        (2 * H + 1) ^ (n - 1) * (2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1))) := by
  classical
  have hn1 : 1 ≤ n := by omega
  rcases concDDZ_natAbs_box_pow_le n hn with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  rw [Filter.eventually_atTop] at hK ⊢
  rcases hK with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro H hH B hB
  have hHN : N ≤ H := le_trans (le_max_left N 1) hH
  have hleK : ∀ u : Fin (n - 1) → ℤ, (∀ i, |u i| ≤ (H : ℤ)) →
      (concDDZ n u).natAbs ≤ H ^ K := hN H hHN
  unfold CaseIIIArithSet
  let S : Set ℤ[X] := {f | f ∈ Box n H ∧ concDDZ n (upperCoeffs n f) ≠ 0 ∧
    ∃ A ∈ Adm B n H (upperCoeffs n f), ∀ p ∈ A.primeFactors, (p : ℤ) ∣ Polynomial.discr f}
  let UB := {u : Fin (n - 1) → ℤ // u ∈ upperBox n H}
  haveI : Fintype UB := Fintype.ofEquiv (Fin (n - 1) → BddInt H) (upperBoxEquiv n H).symm
  let F : UB → Type := fun u => {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
    ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
      (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
  haveI (u : UB) : Fintype (F u) := by
    dsimp [F]
    infer_instance
  let C : ℕ := 2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1))
  -- per-fiber bound
  have hFib (u : UB) : Nat.card (F u) ≤ C := by
    by_cases hdd : concDDZ n u.1 ≠ 0
    · have hu : ∀ i, |u.1 i| ≤ (H : ℤ) := u.2
      have hle := hleK u.1 hu
      have hpu := perUpper_ncard_le (B := B) (n := n) (K := K) (H := H) hn hB u.1 hdd hle
      let T1 : Type := {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
      let T2 : Type := {c : BddInt H // ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
      have hbij : T1 ≃ T2 := by
        refine ⟨fun c => (⟨c.1, c.2.2⟩ : T2), fun c => (⟨c.1, ⟨hdd, c.2⟩⟩ : T1), ?_, ?_⟩
        · intro c
          apply Subtype.ext
          rfl
        · intro c
          apply Subtype.ext
          rfl
      calc
        Nat.card {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
            ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
              (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))}
            = Nat.card {c : BddInt H // ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
                (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} := Nat.card_congr hbij
        _ = ({c : BddInt H | ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
              (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} : Set (BddInt H)).ncard := by
            exact (Nat.card_coe_set_eq
              ({c : BddInt H | ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
                (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} : Set (BddInt H))).symm
        _ ≤ C := by
          dsimp [C]
          exact hpu
    · have hz : concDDZ n u.1 = 0 := (Classical.not_not.mp hdd)
      have hIsEmpty : IsEmpty {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} :=
        ⟨fun c => c.2.1 hz⟩
      haveI : IsEmpty {c : BddInt H // concDDZ n u.1 ≠ 0 ∧
          ∃ A ∈ Adm B n H u.1, ∀ p ∈ A.primeFactors,
            (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u.1 (c : ℤ))} := hIsEmpty
      simp [C]

  -- S injects into the disjoint union of the fibers
  have hSle : S.ncard ≤ Nat.card (Σ u : UB, F u) := by
    let g : {f : ℤ[X] // f ∈ S} → Σ u : UB, F u := fun f =>
      ⟨⟨upperCoeffs n f.1, fun j => upperCoeffs_bound f.2.1 hn1 j⟩,
        ⟨⟨f.1.coeff 0, coeff0_bound f.2.1 hn1⟩,
          ⟨f.2.2.1, by
            rcases f.2.2.2 with ⟨A, hA, hφ⟩
            refine ⟨A, hA, ?_⟩
            intro p hp
            change (p : ℤ) ∣ Polynomial.discr (monicOfUpper n (upperCoeffs n f.1) (f.1.coeff 0))
            rw [monicOfUpper_eq_self n hn1 f.1 f.2.1.1
              (Polynomial.natDegree_eq_of_degree_eq_some f.2.1.2.1)]
            exact hφ p hp⟩⟩⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hux : ((g x).1).1 = ((g y).1).1 := congrArg (fun w : Σ u : UB, F u => w.1.1) hxy
      have huc : upperCoeffs n x.1 = upperCoeffs n y.1 := by
        change ((g x).1).1 = ((g y).1).1
        exact hux
      have hcBdd : ((g x).2).1 = ((g y).2).1 := congrArg (fun w : Σ u : UB, F u => w.2.1) hxy
      have hc0 : x.1.coeff 0 = y.1.coeff 0 := by
        have hc0' := congrArg (fun c : BddInt H => (c : ℤ)) hcBdd
        change ((g x).2.1 : ℤ) = ((g y).2.1 : ℤ) at hc0'
        change x.1.coeff 0 = y.1.coeff 0
        exact hc0'
      have hboxx : x.1 ∈ Box n H := x.2.1
      have hboxy : y.1 ∈ Box n H := y.2.1
      have hdegx : x.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxx.2.1
      have hdegy : y.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxy.2.1
      have hxe : monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) = x.1 :=
        monicOfUpper_eq_self n hn1 x.1 hboxx.1 hdegx
      have hye : monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) = y.1 :=
        monicOfUpper_eq_self n hn1 y.1 hboxy.1 hdegy
      calc
        x.1 = monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) := hxe.symm
        _ = monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) := by rw [huc, hc0]
        _ = y.1 := hye
    have hnc : S.ncard = Nat.card {f : ℤ[X] // f ∈ S} := (Nat.card_coe_set_eq S).symm
    rw [hnc]
    exact Nat.card_le_card_of_injective g hinj
  -- cardinality chain
  have hcardUB : Fintype.card UB = (2 * H + 1) ^ (n - 1) := by
    calc
      Fintype.card UB = Nat.card UB := (Nat.card_eq_fintype_card).symm
      _ = (upperBox n H).ncard := by
        exact (ncard_eq_natCard (upperBox n H)).symm
      _ = (2 * H + 1) ^ (n - 1) := upperBox_ncard_eq n H
  calc
    S.ncard ≤ Nat.card (Σ u : UB, F u) := hSle
    _ = ∑ u : UB, Nat.card (F u) := by
      exact Nat.card_sigma
    _ ≤ ∑ _u : UB, C := by
      refine Finset.sum_le_sum ?_
      intro u hu
      exact hFib u
    _ = Fintype.card UB * C := by
      rw [Finset.sum_const]
      simp
    _ = (2 * H + 1) ^ (n - 1) * C := by rw [hcardUB]

/-- **The power-of-`H` threshold form (log-free).**  For every `M`, if the
threshold `B` satisfies `n < B` and `H ≤ B^M` (i.e. `B ≥ H^(1/M)`), then the
Case-III subcase-(ii) count is eventually at most `C·(2H+1)^(n-1)` with `C`
independent of `H` and `B`.  The `(2(n-1))^(K·(log_B H + 1))` factor of
`caseIII_subcase2_box_ncard_uniform` is absorbed using `log_B H ≤ M`. -/
theorem caseIII_subcase2_threshold_le (n M : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℕ, ∀ᶠ H : ℕ in atTop, ∀ B : ℕ, n < B → H ≤ B ^ M →
      (CaseIIIArithSet B n H).ncard ≤ C * (2 * H + 1) ^ (n - 1) := by
  classical
  rcases caseIII_subcase2_box_ncard_uniform n hn with ⟨K, hK⟩
  refine ⟨2 * (2 * (n - 1)) ^ (K * (M + 1)), ?_⟩
  rw [Filter.eventually_atTop] at hK ⊢
  rcases hK with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro H hH B hB hBpow
  have hB1 : 1 < B := by omega
  have hHN : N ≤ H := le_trans (le_max_left N 1) hH
  have hb := hN H hHN B hB
  have hlog : Nat.log B H ≤ M := log_le_of_le_pow hB1 hBpow
  have hkm : K * (Nat.log B H + 1) ≤ K * (M + 1) := by
    exact Nat.mul_le_mul_left K (Nat.add_le_add_right hlog 1)
  have hpw : (2 * (n - 1)) ^ (K * (Nat.log B H + 1)) ≤ (2 * (n - 1)) ^ (K * (M + 1)) :=
    pow_le_pow_right₀ (by omega : 1 ≤ 2 * (n - 1)) hkm
  have hb' : (2 * H + 1) ^ (n - 1) * (2 * (2 * (n - 1)) ^ (K * (Nat.log B H + 1)))
      ≤ (2 * H + 1) ^ (n - 1) * (2 * (2 * (n - 1)) ^ (K * (M + 1))) := by
    exact Nat.mul_le_mul_left ((2 * H + 1) ^ (n - 1)) (Nat.mul_le_mul_left 2 hpw)
  have hfinal : (2 * H + 1) ^ (n - 1) * (2 * (2 * (n - 1)) ^ (K * (M + 1))) ≤
      (2 * (2 * (n - 1)) ^ (K * (M + 1))) * (2 * H + 1) ^ (n - 1) := by
    rw [Nat.mul_comm]
  exact le_trans hb (le_trans hb' hfinal)

/-- **Big-O corollary (the form the Case-III assembly will consume).**  Let
`Bfun : ℕ → ℕ` be any threshold family that eventually satisfies
`n < Bfun H` and `H ≤ (Bfun H)^M` (i.e. `Bfun H ≥ H^(1/M)`).  Then the
subcase-(ii) arithmetic count at the threshold `Bfun H` is eventually
`O(H^(n-1))` — uniformly over the threshold, since
`log_{Bfun H} H ≤ M` bounds the whole `(2(n-1))^(K(log_B H+1))` factor. -/
theorem caseIII_subcase2_isBigO_of_threshold (n M : ℕ) (hn : 3 ≤ n)
    (Bfun : ℕ → ℕ)
    (hthr : ∀ᶠ H : ℕ in atTop, n < Bfun H ∧ H ≤ (Bfun H) ^ M) :
    (fun H : ℕ => ((CaseIIIArithSet (Bfun H) n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  rcases caseIII_subcase2_threshold_le n M hn with ⟨C, hC⟩
  have hC' : ∀ᶠ H : ℕ in atTop,
      (CaseIIIArithSet (Bfun H) n H).ncard ≤ C * (2 * H + 1) ^ (n - 1) := by
    filter_upwards [hC, hthr] with H hCb hthr
    exact hCb (Bfun H) hthr.1 hthr.2
  -- absorb the (2H+1) factor and the constant C into one power of H
  have hpoint : ∀ᶠ H : ℕ in atTop,
      (CaseIIIArithSet (Bfun H) n H).ncard ≤ (C * 3 ^ (n - 1)) * H ^ (n - 1) := by
    filter_upwards [hC', eventually_ge_atTop (1 : ℕ)] with H hc hH
    calc
      (CaseIIIArithSet (Bfun H) n H).ncard ≤ C * (2 * H + 1) ^ (n - 1) := hc
      _ ≤ C * (3 * H) ^ (n - 1) := by
        exact Nat.mul_le_mul_left C (pow_le_pow_left₀ (by omega) (by omega) (n - 1))
      _ = (C * 3 ^ (n - 1)) * H ^ (n - 1) := by rw [mul_pow]; ring
  exact Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) (C * 3 ^ (n - 1))
    (fun H : ℕ => (CaseIIIArithSet (Bfun H) n H).ncard) hpoint
