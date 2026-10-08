/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS, step Z6.3/6.4, `d` even: setup for HB III XI 1.8–1.11

Setting (Huppert–Blackburn III.11 §1, `d` even): `G` is a Zassenhaus group of degree `q + 1`
(`Work.GW2.ZassHyps2 G X q`, `q` odd, `q ≥ 5`), `a ≠ b` are two points, `U ≤ G_a` is the
unipotent radical of order `q` normal in `G_a`, `H = G_{ab} = pairStab G a b` acts
fixed-point-freely on `U` (`Work.ZASS.FixedPointFreeConj`), `|H| = (q-1)/2` is even, and
`s ∈ G` is an involution interchanging `a` and `b`.

This file sets up the *additive coordinates* used by HB 1.8c–1.10.  Since `U` is abelian of
exponent `p` (Z4, `Work.ZASS.isMulCommutative_of_zass`), the Z3 bijection `u ↦ u • b`
identifies `U` with the point set `K = X ∖ {a}` and makes `K` an abelian group; in this file
that bijection is part of the data (`EvenData.kEq`), so that

* `τ(k) = e.symm k` is the element of `U` with `τ(k) • b = k` and `k₁ + k₂ = τ(k₁) • k₂`,
* `-k = e((e.symm k)⁻¹)`,
* `σ(u)` (defined for `u ≠ 1`) is the element of `U` with `s • (u • b) = σ u • b`, i.e.
  `τ(s • k) = σ(k)`.

The remaining ingredient of the `d` even branch of step Z6, recorded in `NOTES_ZASS.md` §3.3,
is the element of HB 1.9

  `hElem u := τ(u) · s · τ(σ u)⁻¹ · s · τ(u) · s`   (`u ≠ 1`),

together with HB 1.9 (`hElem u ∈ H`, proved by evaluating the action of `hElem u` on `a` and
`b` with the aid of HB 1.8b/1.8c), HB 1.10 and HB 1.11 (the conclusion
`Work.GW2.Inverts s (pairStab G a b)`).  `sigma` is the only part of that computation which
needs the pointwise bookkeeping established here. -/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.equiv_unipotent_compl
import Submission.Work.ZASS.Frobenius

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
variable {q : ℕ} {a b : X} {U : Subgroup G} {s : G}

/-- With `q` odd, `|U| = q` and `|G_{ab}| = (q-1)/2`, the subgroups `U` and `G_{ab}` have
coprime order, hence intersect trivially. -/
theorem inf_pairStab_eq_bot_of_coprime (hqodd : Odd q) (hcardU : Nat.card U = q)
    (hcardH : Nat.card (pairStab G a b) = (q - 1) / 2) :
    U ⊓ pairStab G a b = ⊥ := by
  have h2dvd : 2 ∣ q - 1 := by obtain ⟨m, hm⟩ := hqodd; exact ⟨m, by omega⟩
  have h1q : 1 ≤ q := by obtain ⟨m, hm⟩ := hqodd; omega
  have hcop1 : Nat.Coprime q (q - 1) := by
    rw [Nat.coprime_self_sub_right h1q]
    exact Nat.coprime_one_right q
  have hcop2 : Nat.Coprime q ((q - 1) / 2) := hcop1.of_dvd_right (Nat.div_dvd_of_dvd h2dvd)
  have hcop : Nat.Coprime (Nat.card U) (Nat.card (pairStab G a b)) := by
    rw [hcardU, hcardH]; exact hcop2
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

/-- The hypothesis bundle of the `d` even part of HB III.11 §1.  The field `kEq` is the Z3
coordinate bijection `u ↦ u • b`, which identifies `U` with the point set `K = X ∖ {a}` and
endows `K` with the (abelian) group structure of `U`. -/
structure EvenData (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (q : ℕ)
    (a b : X) where
  /-- the Zassenhaus hypotheses -/
  hyps : ZassHyps2 G X q
  /-- the two points are distinct -/
  hab : a ≠ b
  /-- the unipotent radical of the Borel subgroup `G_a` -/
  U : Subgroup G
  hUB : U ≤ borel G a
  hcardU : Nat.card U = q
  hcardH : Nat.card (pairStab G a b) = (q - 1) / 2
  hN : (U.subgroupOf (borel G a)).Normal
  hfree : FixedPointFreeConj U (pairStab G a b)
  /-- `d = (q-1)/2` is even -/
  hdeven : 2 ∣ Nat.card (pairStab G a b)
  hqodd : Odd q
  hq : 5 ≤ q
  /-- the involution interchanging `a` and `b` -/
  s : G
  hsa : s • a = b
  hsb : s • b = a
  hs2 : s ^ 2 = 1
  /-- **Z3 coordinates**: `u ↦ u • b` is a bijection onto `X ∖ {a}` -/
  kEq : U ≃ {x : X // x ≠ a}
  kEq_apply : ∀ u : U, (kEq u : X) = (u : G) • b

namespace EvenData

variable (D : EvenData G X q a b)

theorem one_lt_cardU : 1 < Nat.card D.U := by
  rw [D.hcardU]
  have := D.hq
  omega

theorem nontrivial_U : Nontrivial D.U :=
  Finite.one_lt_card_iff_nontrivial.mp D.one_lt_cardU

/-- The element `τ(k) ∈ U` with `τ(k) • b = k`, for `k = e u`. -/
noncomputable def tau (u : D.U) : D.U := u

theorem kEq_tau (u : D.U) : (D.kEq (D.tau u) : X) = (u : G) • b := D.kEq_apply u

/-- The element of `U` whose point is `s • (u • b)`; the hypothesis `u ≠ 1` makes this a point
different from `a` (because `s` interchanges `a` and `b`). -/
noncomputable def sigma (u : D.U) (hu : u ≠ 1) : D.U :=
  D.kEq.symm ⟨D.s • (D.kEq u : X), by
    intro hcon
    have h0 : D.s • (D.kEq u : X) = a := hcon
    have h1 : D.s • (D.s • (D.kEq u : X)) = D.s • a := by rw [h0]
    rw [← mul_smul, ← sq, D.hs2, one_smul, D.hsa] at h1
    have h3 : D.kEq u = ⟨b, (Ne.symm D.hab)⟩ := Subtype.ext h1
    have h4 : D.kEq (1 : D.U) = ⟨b, (Ne.symm D.hab)⟩ :=
      Subtype.ext (by rw [D.kEq_apply 1]; simp)
    exact hu (D.kEq.injective (h3.trans h4.symm))⟩

theorem kEq_sigma (u : D.U) (hu : u ≠ 1) :
    (D.kEq (D.sigma u hu) : X) = D.s • ((u : G) • b) := by
  simp only [sigma, Equiv.apply_symm_apply, Subtype.coe_mk, kEq_apply]

/-- `σ u` is not `1`. -/
theorem sigma_ne_one {u : D.U} (hu : u ≠ 1) : D.sigma u hu ≠ 1 := by
  intro hcon
  have h1 : D.s • ((u : G) • b) = b := by
    rw [← D.kEq_sigma u hu, hcon, D.kEq_apply (1 : D.U)]
    simp
  have h3 : D.s • (D.s • ((u : G) • b)) = D.s • b := by rw [h1]
  rw [← mul_smul, ← sq, D.hs2, one_smul, D.hsb] at h3
  exact (D.kEq u).2 ((D.kEq_apply u).trans h3)

end EvenData

end Work.ZASS
