/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: assembly of the recognition theorem

* `Work.ZASS.zassOdd_of_zassOdd2` (trivial): `ZassOdd2Prop`, the amended contract of design
  pass 2, implies the originally dispatched `ZassOddProp` — the latter assumes the additional
  cyclicity clause of `ZassHyps`.
* `Work.ZASS.zassOdd2_of_weyl`: the cardinality half of Z7.  Given step Z6 as a proposition
  (`Work.GW2.ZassWeylProp`: the action is equivalent to the standard action of
  `PSL(2, GaloisField p k)` on the projective line), Z1–Z4 finish: `Φ` is a bijection and the
  action is faithful, so `Ψ` is injective; `Work.ZASS.card_G` says `|G| = (q+1)q(q-1)/2` and
  `Work.ZASS.card_PSL2_galoisField_zass` says the same for `PSL(2,q)`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.card_G
import Submission.Work.ZASS.card_PSL2_galoisField_zass

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.ZASS

open Work.GW2 (ZassHyps ZassHyps2 ZassOddProp ZassOdd2Prop ZassWeylProp)

/-- The amended contract `ZassOdd2Prop` (no cyclicity clause) implies the dispatched
`ZassOddProp` (with it): the hypothesis set of the latter is the stronger one. -/
theorem zassOdd_of_zassOdd2 (h : ZassOdd2Prop) : ZassOddProp := by
  intro G X _ _ _ _ p k _ hp hq hsimple hhyps
  exact h G X p k hp hq hsimple
    ⟨hhyps.1, hhyps.2.1, hhyps.2.2.1, hhyps.2.2.2.1, hhyps.2.2.2.2.1⟩

/-- **Z7** (blueprint §ZASS), given step Z6: `Ψ : G →* PSL(2,q)` is injective because `Φ` is a
bijection and the action of `G` on `X` is faithful, and `|G| = |PSL(2,q)|` by Z1–Z4. -/
theorem zassOdd2_of_weyl (hW : ZassWeylProp) : ZassOdd2Prop := by
  intro G X _ _ _ _ p k hpfact hp hq hsimple hhyps
  obtain ⟨Φ, Ψ, hΦ⟩ := hW G X p k hp hq hsimple hhyps
  haveI : Fintype X := Fintype.ofFinite X
  have h2 : 1 < Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, hhyps.2.1]; omega
  obtain ⟨inf, zero, hne⟩ := Fintype.exists_pair_of_one_lt_card h2
  have hfaith : FaithfulSMul G X := hhyps.1
  haveI : FaithfulSMul G X := hfaith
  have hinj : Function.Injective Ψ := by
    intro g h hgh
    have hsm : ∀ x : X, g • x = h • x := by
      intro x
      have h1 : Φ (g • x) = Φ (h • x) := by rw [hΦ g x, hΦ h x, hgh]
      exact Φ.injective h1
    have h1 : g⁻¹ * h = 1 := FaithfulSMul.eq_of_smul_eq_smul (m₁ := g⁻¹ * h) (m₂ := 1)
      (fun x : X => by rw [mul_smul, ← hsm x, inv_smul_smul, one_smul])
    exact inv_mul_eq_one.mp h1
  have hcardG : Nat.card G = (p ^ k + 1) * p ^ k * ((p ^ k - 1) / 2) :=
    card_G (inf := inf) (zero := zero) hhyps hne
  have hcardP : Nat.card (PSL(2, GaloisField p k)) =
      (p ^ k + 1) * p ^ k * ((p ^ k - 1) / 2) :=
    card_PSL2_galoisField_zass hp (by intro hk0; rw [hk0, pow_zero] at hq; omega)
  have hbij : Function.Bijective Ψ :=
    hinj.bijective_of_nat_card_le (by rw [hcardP, hcardG])
  exact ⟨MulEquiv.ofBijective Ψ hbij⟩

end Work.ZASS
