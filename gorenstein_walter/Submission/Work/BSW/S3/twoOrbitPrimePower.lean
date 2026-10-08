/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Bender §3.8: two orbits force a prime power

This file proves `Work.BSW.BSWTwoOrbitPrimePowerProp`, the self-contained finite-group
fact used in Bender, *The Brauer–Suzuki–Wall theorem*, §3.8
(`REFS/vision/bender1974_bsw`), namely:

> If a finite group `D` acts fixed-point-freely (on non-identity elements) on a finite
> abelian group `F` of **odd** order and `2 * |D| + 1 = |F|`, then `|F|` is a prime power.

The mathematical argument (two orbits ⟹ no second prime):

* Every `D`-orbit on `F# = F \ {1}` has exactly `|D|` elements (the action is free), so
  there are exactly two orbits, since `|F#| = 2 * |D|`.
* Suppose two distinct primes `p ≠ q` divide `|F|`.  The `p`-torsion subgroup
  `Ω = {a : F | a ^ p = 1}` is non-trivial (Cauchy's theorem), is invariant under `D`
  (the action is by group automorphisms), and is a `p`-group, so `|Ω| = p ^ n`;
  in particular `q ∤ |Ω|`.
* Since `|Ω| ∣ |F|` (Lagrange) and `q ∣ |F|` with `q ∤ |Ω|`, we get `|Ω| * q ≤ |F|`.
* On the other hand `D` acts freely on the non-identity elements of `Ω`, so
  `|D| ∣ |Ω| - 1`, whence `|D| + 1 ≤ |Ω|` since `|Ω| ≥ 2`.
* Combining: `3 * (|D| + 1) ≤ 3 * |Ω| ≤ |Ω| * q ≤ |F| = 2 * |D| + 1`, i.e. `|D| ≤ -2`,
  a contradiction.
* Hence every prime divisor of `|F|` equals some fixed `p`, so `|F| = p ^ k` where
  `k = (|F|).factorization p`.

The supporting lemmas proved here are of independent use:

* `Work.BSW.S3.pTorsion` — the `p`-torsion subgroup of a commutative group;
* `Work.BSW.S3.card_dvd_card_of_fixedPointFree` — a group acting without non-identity
  fixed points has order dividing the cardinality of the set;
* `Work.BSW.S3.natCard_subtype_ne` — the number of elements different from a given one;
* `Work.BSW.S3.card_pred_card_dvd_of_invariant_subgroup` — the invariant-subgroup form.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs

set_option linter.style.haveILetI false

namespace Work.BSW.S3

open Subgroup

/-- The `p`-torsion subgroup `{a : F | a ^ p = 1}` of a commutative group `F`. -/
def pTorsion (F : Type*) [CommGroup F] (p : ℕ) : Subgroup F where
  carrier := {a : F | a ^ p = 1}
  mul_mem' := by
    intro a b ha hb
    show (a * b) ^ p = 1
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by show (1 : F) ^ p = 1; simp
  inv_mem' := by
    intro a ha
    show (a⁻¹) ^ p = 1
    rw [inv_pow, ha, inv_one]

/-- In a finite type, the number of elements different from a given one is one less than the
total number of elements. -/
theorem natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype {x : α // x ≠ a} := Fintype.ofFinite _
  haveI : Fintype {x : α // x = a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := {x : α // x ≠ a}), Nat.card_eq_fintype_card (α := α)]
  have h := Fintype.card_subtype_compl (α := α) (fun x : α => x = a)
  rw [Fintype.card_subtype_eq] at h
  exact h

/-- **Free actions have order dividing the cardinality.**  If a group `D` acts on a type `X`
in such a way that no non-identity element of `D` has a fixed point, then every orbit is in
bijection with `D`, so `Nat.card D ∣ Nat.card X`.

The bijection `(orbit of x, d) ↦ d • representative` is spelled out explicitly, so that no
finiteness hypotheses and no `Fintype` instances are needed. -/
theorem card_dvd_card_of_fixedPointFree {D X : Type*} [Group D] [MulAction D X]
    (h : ∀ d : D, d ≠ 1 → ∀ x : X, d • x = x → False) :
    Nat.card D ∣ Nat.card X := by
  classical
  let f : MulAction.orbitRel.Quotient D X × D → X := fun p => p.2 • (Quotient.out p.1 : X)
  -- `d • x` lies in the same orbit as `x`
  have hrel : ∀ (ω : MulAction.orbitRel.Quotient D X) (d : D),
      (⟦(Quotient.out ω : X)⟧ : Quotient (MulAction.orbitRel D X))
        = ⟦d • (Quotient.out ω : X)⟧ := by
    intro ω d
    apply Quotient.sound
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨d⁻¹, by rw [inv_smul_smul]⟩
  have hinj : Function.Injective f := by
    rintro ⟨ω₁, d₁⟩ ⟨ω₂, d₂⟩ heq
    simp only [f] at heq
    have hω : ω₁ = ω₂ :=
      calc ω₁ = Quotient.mk'' (Quotient.out ω₁) := (Quotient.out_eq ω₁).symm
        _ = Quotient.mk'' (d₁ • (Quotient.out ω₁ : X)) := hrel ω₁ d₁
        _ = Quotient.mk'' (d₂ • (Quotient.out ω₂ : X)) := by rw [heq]
        _ = Quotient.mk'' (Quotient.out ω₂) := (hrel ω₂ d₂).symm
        _ = ω₂ := Quotient.out_eq ω₂
    subst hω
    have hd : d₁ = d₂ := by
      by_contra hne
      have h1 : (d₂⁻¹ * d₁) • (Quotient.out ω₁ : X) = (Quotient.out ω₁ : X) := by
        rw [mul_smul, heq, inv_smul_smul]
      exact h (d₂⁻¹ * d₁) (by intro hc; exact hne ((inv_mul_eq_one.mp hc).symm)) _ h1
    exact Prod.ext rfl hd
  have hsurj : Function.Surjective f := by
    intro x
    have h0 : (MulAction.orbitRel D X) x
        (Quotient.out (Quotient.mk'' x : Quotient (MulAction.orbitRel D X))) :=
      Quotient.exact (s := MulAction.orbitRel D X)
        (Quotient.out_eq (Quotient.mk'' x : Quotient (MulAction.orbitRel D X))).symm
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h0
    obtain ⟨d, hd⟩ := h0
    exact ⟨(Quotient.mk'' x, d), hd⟩
  have e : MulAction.orbitRel.Quotient D X × D ≃ X := Equiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← Nat.card_congr e, Nat.card_prod]
  exact Nat.dvd_mul_left _ _

/-- **Orbit counting on an invariant subgroup.**  A finite group `D` acting fixed-point-freely
on a finite commutative group `F`, keeping a subgroup `Ω` invariant, satisfies
`|D| ∣ |Ω| - 1`.

Indeed `D` acts freely on the `|Ω| - 1` non-identity elements of `Ω`. -/
theorem card_pred_card_dvd_of_invariant_subgroup {D F : Type*} [Group D] [Finite D] [CommGroup F]
    [Finite F] [MulDistribMulAction D F] (Ω : Subgroup F)
    (hΩ : ∀ d : D, ∀ a : F, a ∈ Ω → d • a ∈ Ω)
    (hfree : ∀ d : D, d ≠ 1 → ∀ a : F, d • a = a → a = 1) :
    Nat.card D ∣ Nat.card Ω - 1 := by
  classical
  let S := {a : F // a ∈ Ω ∧ a ≠ 1}
  letI hSact : MulAction D S :=
    { smul := fun d a => ⟨d • a.1, ⟨hΩ d a.1 a.2.1, by
        intro hd
        have ha : a.1 = 1 := by
          have hdF : d • a.1 = (1 : F) := hd
          calc a.1 = d⁻¹ • (d • a.1) := (inv_smul_smul d a.1).symm
            _ = d⁻¹ • (1 : F) := by rw [hdF]
            _ = 1 := smul_one d⁻¹
        exact a.2.2 ha⟩⟩
      one_smul := fun a => Subtype.ext (one_smul D a.1)
      mul_smul := fun d e a => Subtype.ext (mul_smul d e a.1) }
  have hnp : ∀ d : D, d ≠ 1 → ∀ x : S, d • x = x → False := by
    intro d hd x hx
    have hF : d • (x.1 : F) = (x.1 : F) := congrArg (fun y : S => (y : F)) hx
    exact x.2.2 (hfree d hd _ hF)
  have hdvd : Nat.card D ∣ Nat.card S := card_dvd_card_of_fixedPointFree hnp
  have hcardS : Nat.card S = Nat.card Ω - 1 := by
    have e : S ≃ {a : ↥Ω // a ≠ 1} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by intro h; exact x.2.2 (congrArg Subtype.val h)⟩
        invFun := fun y => ⟨y.1.1, y.1.2, by intro h; exact y.2 (Subtype.ext h)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr e, natCard_subtype_ne (1 : ↥Ω)]
  rwa [hcardS] at hdvd

/-- **Bender §3.8, two-orbit argument.**  A finite abelian group `F` of odd order on which a
finite group `D` acts fixed-point-freely with `2 * |D| + 1 = |F|` has prime-power order.

See the module docstring for the proof sketch. -/
theorem twoOrbitPrimePower : Work.BSW.BSWTwoOrbitPrimePowerProp := by
  intro F D _ _ _ _ _ hodd hcard hfree
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype D := Fintype.ofFinite D
  have hNval : Nat.card F = 2 * Nat.card D + 1 := hcard.symm
  -- Step 1: `|F|` has at most one prime divisor.
  have huniq : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ Nat.card F → q ∣ Nat.card F → p = q := by
    intro p q hp hq hpd hqd
    by_contra hpq
    haveI : Fact p.Prime := ⟨hp⟩
    let Ω : Subgroup F := pTorsion F p
    have hmem : ∀ a : F, a ∈ Ω ↔ a ^ p = 1 := fun a => Iff.rfl
    -- `Ω` is invariant under the action
    have hΩinv : ∀ d : D, ∀ a : F, a ∈ Ω → d • a ∈ Ω := by
      intro d a ha
      have ha' : a ^ p = 1 := ha
      show (d • a) ^ p = 1
      have h2 : d • (a ^ p) = (d • a) ^ p := map_pow (MulDistribMulAction.toMonoidHom F d) a p
      rw [← h2, ha', smul_one]
    -- `Ω` is a `p`-group, hence has `p`-power order
    have hpg : IsPGroup p Ω := fun x => ⟨1, by
      show x ^ p ^ 1 = 1
      rw [pow_one]
      exact Subtype.ext ((hmem x.1).mp x.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    -- `Ω` is non-trivial, by Cauchy
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hxmem : x ∈ Ω := by
      show x ^ p = 1
      rw [← hx, pow_orderOf_eq_one]
    have hxne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx
      exact hp.ne_one hx.symm
    have hΩne : Ω ≠ ⊥ := by
      intro hbot
      have hxb : x ∈ (⊥ : Subgroup F) := by rw [hbot] at hxmem; exact hxmem
      rw [Subgroup.mem_bot] at hxb
      exact hxne hxb
    haveI : Nontrivial ↥Ω := (Subgroup.nontrivial_iff_ne_bot Ω).mpr hΩne
    haveI : Fintype ↥Ω := Fintype.ofFinite ↥Ω
    have hΩ2 : 2 ≤ Nat.card Ω := by
      rw [Nat.card_eq_fintype_card]
      have := Fintype.one_lt_card (α := ↥Ω)
      omega
    -- the free action on the non-identity elements of `Ω` gives `|D| ∣ |Ω| - 1`
    have hcount : Nat.card D ∣ Nat.card Ω - 1 :=
      card_pred_card_dvd_of_invariant_subgroup Ω hΩinv hfree
    have hMle : Nat.card D ≤ Nat.card Ω - 1 := Nat.le_of_dvd (by omega) hcount
    have hMs : Nat.card D + 1 ≤ Nat.card Ω := by omega
    -- `q` is coprime to `|Ω|`
    have hqΩ : ¬ q ∣ Nat.card Ω := by
      rw [hn]
      intro hdiv
      have hqp : q ∣ p := hq.dvd_of_dvd_pow hdiv
      rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h1
      · exact hq.ne_one h1
      · exact hpq h1.symm
    have hlag : Nat.card Ω * Ω.index = Nat.card F := Subgroup.card_mul_index Ω
    have hFpos : 0 < Nat.card F := Nat.card_pos
    have hqindex : q ∣ Ω.index := by
      have h : q ∣ Nat.card Ω * Ω.index := by rw [hlag]; exact hqd
      rcases hq.dvd_mul.mp h with h' | h'
      · exact absurd h' hqΩ
      · exact h'
    have hidxpos : 0 < Ω.index := by
      by_contra h
      have h0 : Ω.index = 0 := by omega
      rw [h0, mul_zero] at hlag
      omega
    have hq3 : 3 ≤ q := by
      have h2 : 2 ≤ q := hq.two_le
      have hne2 : q ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqd)
      omega
    have hΩq : Nat.card Ω * q ≤ Nat.card F := by
      calc Nat.card Ω * q ≤ Nat.card Ω * Ω.index :=
            Nat.mul_le_mul_left _ (Nat.le_of_dvd hidxpos hqindex)
        _ = Nat.card F := hlag
    have h3 : 3 * (Nat.card D + 1) ≤ 2 * Nat.card D + 1 := by
      calc 3 * (Nat.card D + 1) ≤ 3 * Nat.card Ω := Nat.mul_le_mul_left 3 hMs
        _ ≤ Nat.card Ω * q := by
              rw [Nat.mul_comm 3 (Nat.card Ω)]; exact Nat.mul_le_mul_left _ hq3
        _ ≤ Nat.card F := hΩq
        _ = 2 * Nat.card D + 1 := hNval
    omega
  -- Step 2: a number all of whose prime divisors are equal is a prime power.
  have hDpos : 0 < Nat.card D := Nat.card_pos
  obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F) (by omega)
  have hFne : Nat.card F ≠ 0 := by omega
  have hNpow : Nat.card F = p ^ (Nat.card F).factorization p := by
    refine Nat.eq_pow_of_factorization_eq_single hFne ?_
    ext r
    by_cases hr : p = r
    · subst hr
      rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hr)]
      by_contra hne
      have hrr : r.Prime := Nat.prime_of_mem_primeFactors (by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        exact hne)
      exact hr (huniq r p hrr hpp (Nat.dvd_of_factorization_pos hne) hpd).symm
  exact ⟨p, (Nat.card F).factorization p, hpp, hNpow⟩

end Work.BSW.S3
