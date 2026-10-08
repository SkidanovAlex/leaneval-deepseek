/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS)
-/
import Mathlib
import Submission.Work.FUS.TransferAux.prod_ne_one_of_odd
import Submission.Work.FUS.TransferAux.odd_fixed_orbits

-- `hσt` is redundant: it follows from `hfus` applied with `g = 1`, but it is part of the requested
-- statement, so it is kept and simply not used.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Thompson's transfer lemma (σ-form)

Let `G` be a finite group, `S ≤ G` a subgroup of **odd** index, `σ : S →* Multiplicative (ZMod 2)`
a homomorphism and `t ∈ S` an involution with `σ t ≠ 1`.  If every `G`-conjugate of `t` that lies
in `S` is sent by `σ` to the nontrivial element of `Multiplicative (ZMod 2)`, then `G` has a normal
subgroup of index `2` that does not contain `t`.

This is the "transfer" form of Thompson's transfer lemma.  The proof evaluates the transfer
homomorphism `ψ := MonoidHom.transfer σ : G →* Multiplicative (ZMod 2)` at `t`, using
`MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`, which writes `ψ t` as a product
indexed by the `⟨t⟩`-orbits on the coset space `G ⧸ S`:

* an orbit of size `2` contributes `σ` applied to a conjugate of `t ^ 2 = 1`, hence `1`;
* a fixed orbit (size `1`), with representative `u`, contributes `σ (u⁻¹ * t * u)`, which is
  nontrivial by hypothesis (`hfus` applies with `g = u⁻¹`);
* the number of fixed orbits is odd: `S.index = ∑_orbits (orbit size)`
  (`Subgroup.index_eq_sum_minimalPeriod`) is odd and every orbit has size `1` or `2`, so
  `Work.FUS.TransferAux.odd_fixed_orbits` applies.

Finally, every element of `Multiplicative (ZMod 2)` is an involution, so a product whose number of
nontrivial factors is odd is itself nontrivial (`Work.FUS.TransferAux.prod_ne_one_of_odd`); hence
`ψ t ≠ 1` and `ker ψ` is the required normal subgroup of index `2`.
-/

namespace Work.FUS

/-- If `φ : G →* A` is a homomorphism into a group `A` of cardinality `2` and `φ x ≠ 1`, then
`ker φ` has index `2`: the range of `φ` is a nontrivial subgroup of `A`, hence equal to `A` by
Lagrange (`Subgroup.card_subgroup_dvd_card`), and `ker φ` has index `Nat.card φ.range`
(`QuotientGroup.quotientKerEquivRange`). -/
theorem index_ker_eq_two {G A : Type*} [Group G] [Group A] (φ : G →* A) (x : G)
    (hx : φ x ≠ 1) (hcard : Nat.card A = 2) : φ.ker.index = 2 := by
  have hdvd : Nat.card φ.range ∣ 2 := hcard ▸ Subgroup.card_subgroup_dvd_card φ.range
  have hne : Nat.card φ.range ≠ 1 := by
    intro h1
    have hsub : Subsingleton φ.range := (Nat.card_eq_one_iff_unique.mp h1).1
    have hmem : (⟨φ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : φ.range) = ⟨1, φ.range.one_mem⟩ :=
      hsub.elim _ _
    exact hx (congrArg Subtype.val hmem)
  have h2 : Nat.card φ.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  exact h2

theorem thompson_transfer {G : Type*} [Group G] [Finite G] (S : Subgroup G) [S.FiniteIndex]
    (hodd : Odd S.index) (σ : S →* Multiplicative (ZMod 2)) (t : S)
    (ht : orderOf t = 2) (hσt : σ t ≠ 1)
    (hfus : ∀ g : G, ∀ (hh : g * (t : G) * g⁻¹ ∈ S), σ ⟨g * (t : G) * g⁻¹, hh⟩ ≠ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ (t : G) ∉ N := by
  classical
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have ht2 : (t : G) ^ 2 = 1 := by rw [← htG, pow_orderOf_eq_one]
  let ψ : G →* Multiplicative (ZMod 2) := MonoidHom.transfer σ
  have hψt : ψ (t : G) ≠ 1 := by
    let ι := Quotient (MulAction.orbitRel (Subgroup.zpowers (t : G)) (G ⧸ S))
    haveI : Fintype ι := Fintype.ofFinite ι
    have hmPmem : ∀ q : ι, (Quotient.out q.out)⁻¹ * (t : G) ^
        Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out ∈ S :=
      fun q => QuotientGroup.out_conj_pow_minimalPeriod_mem S (t : G) q.out
    have hformula : ψ (t : G) = ∏ q : ι, σ ⟨(Quotient.out q.out)⁻¹ * (t : G) ^
        Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out, hmPmem q⟩ :=
      MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot σ (t : G)
    have hmP12 : ∀ q : ι, Function.minimalPeriod (fun x => (t : G) • x) q.out = 1 ∨
        Function.minimalPeriod (fun x => (t : G) • x) q.out = 2 := by
      intro q
      have hdvd : Function.minimalPeriod (fun x => (t : G) • x) q.out ∣ 2 := by
        rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
        rw [Function.IsPeriodicPt]
        show (fun y : G ⧸ S => (t : G) • y)^[2] q.out = q.out
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
        rw [← mul_smul, ← pow_two, ht2, one_smul]
      exact (Nat.dvd_prime Nat.prime_two).mp hdvd
    have hkey : ∀ q : ι, (σ ⟨(Quotient.out q.out)⁻¹ * (t : G) ^
        Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out, hmPmem q⟩
        ≠ 1) ↔ Function.minimalPeriod (fun x => (t : G) • x) q.out = 1 := by
      intro q
      by_cases hq : Function.minimalPeriod (fun x => (t : G) • x) q.out = 1
      · refine ⟨fun _ => hq, fun _ => ?_⟩
        have hmem' : (Quotient.out q.out)⁻¹ * (t : G) * (Quotient.out q.out) ∈ S := by
          simpa [hq] using hmPmem q
        have h' := hfus (Quotient.out q.out)⁻¹ (by simpa using hmem')
        simpa [hq] using h'
      · have hq2 : Function.minimalPeriod (fun x => (t : G) • x) q.out = 2 :=
          (hmP12 q).resolve_left hq
        have heq : (Quotient.out q.out)⁻¹ * (t : G) ^
            Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out = 1 := by
          rw [hq2]
          simp [ht2]
        have hfac : σ ⟨(Quotient.out q.out)⁻¹ * (t : G) ^
            Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out,
            hmPmem q⟩ = 1 := by
          have h1 : (⟨(Quotient.out q.out)⁻¹ * (t : G) ^
              Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out,
              hmPmem q⟩ : S) = 1 := Subtype.ext heq
          rw [h1, map_one]
        exact ⟨fun hne => absurd hfac hne, fun h => absurd h (by omega)⟩
    rw [hformula]
    refine Work.FUS.TransferAux.prod_ne_one_of_odd _ ?_
    have hcard : Nat.card {q : ι // σ ⟨(Quotient.out q.out)⁻¹ * (t : G) ^
        Function.minimalPeriod (fun x => (t : G) • x) q.out * Quotient.out q.out, hmPmem q⟩
        ≠ 1} = Nat.card {q : ι // Function.minimalPeriod (fun x => (t : G) • x) q.out = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun q => hkey q))
    rw [hcard]
    exact Work.FUS.TransferAux.odd_fixed_orbits S (t : G) ht2 hodd
  refine ⟨ψ.ker, MonoidHom.normal_ker ψ, index_ker_eq_two ψ (t : G) hψt ?_, ?_⟩
  · simp [Nat.card_eq_fintype_card, ZMod.card]
  · intro h
    exact hψt (MonoidHom.mem_ker.mp h)

end Work.FUS
