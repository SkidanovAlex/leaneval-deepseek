import Mathlib
import Submission.Work.ZassenhausSuzuki.ttc_defs
import Submission.Work.ZassenhausSuzuki.canon_H8

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

/-- Pure group-theoretic core of `szTilde_mul_formula`.  For pairwise commuting `a b c` and
arbitrary `p q` one has
`(abc)⁻¹ · (c p c⁻¹ q) · (abc) = a⁻¹ (b⁻¹ p b) a · (b⁻¹ a⁻¹ (c⁻¹ q c) a b)`.

This is exactly the group computation obtained by expanding both sides of the `∼`-product
formula with `tildeOf_eq`, `canon_H7`, `canon_H8`, where `a = h(x₁)`, `b = h(y)`, `c = h(x₂)`
lie in the abelian group `D = twoPoint H t`, `p = f(y)` and `q = f(x₂)`. -/
lemma szTilde_mul_formula_aux {G : Type} [Group G] (a b c p q : G)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c)⁻¹ * (c * p * c⁻¹ * q) * (a * b * c)
      = a⁻¹ * (b⁻¹ * p * b) * a * (b⁻¹ * a⁻¹ * (c⁻¹ * q * c) * a * b) := by
  have hba : b * a = a * b := hab.symm
  have habinv : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
    have h := congrArg Inv.inv hab
    simpa [mul_inv_rev] using h.symm
  have hacb : (a * b) * c = c * (a * b) := by
    calc (a * b) * c = a * (b * c) := mul_assoc a b c
      _ = a * (c * b) := by rw [hbc.symm]
      _ = (a * c) * b := (mul_assoc a c b).symm
      _ = (c * a) * b := by rw [hac]
      _ = c * (a * b) := mul_assoc c a b
  have e1 : (a * b * c)⁻¹ * (c * p * c⁻¹ * q) * (a * b * c)
      = (a * b)⁻¹ * (p * c⁻¹ * q * c) * (a * b) := by
    rw [hacb]
    group
  have e2 : a⁻¹ * (b⁻¹ * p * b) * a * (b⁻¹ * a⁻¹ * (c⁻¹ * q * c) * a * b)
      = (a * b)⁻¹ * (p * c⁻¹ * q * c) * (a * b) := by
    have h2 : a⁻¹ * (b⁻¹ * p * b) * a * (b⁻¹ * a⁻¹ * (c⁻¹ * q * c) * a * b)
        = a⁻¹ * b⁻¹ * p * (b * a * b⁻¹ * a⁻¹) * (c⁻¹ * q * c) * a * b := by
      group
    rw [h2, show b * a * b⁻¹ * a⁻¹ = 1 from by rw [hba]; group, mul_one]
    rw [habinv, mul_inv_rev]
    group
  rw [e1, e2]

/-- **The `∼`-product formula.** Let `H = Q ⋊ D` (`D = twoPoint H t`) be a split rank-one
Zassenhaus configuration, `C` a canonical structure (`t x t = g(x) h(x) t f(x)` for `x ∈ Q#`) and
`∼ = tildeOf C`.  For `x₁, x₂ ∈ Q` with `x₁`, `x₂`, `x₁x₂` non-trivial and `y ∈ Q ∖ {1}` with
`(y : G) = f(x₁)·g(x₂)`,
`∼(x₁x₂) = (h₁⁻¹ · ∼y · h₁) · ((h₁·h_y)⁻¹ · ∼x₂ · (h₁·h_y))`, where `h₁ = h(x₁)`, `h_y = h(y)`,
written with `conjQ hsplit d x = d·x·d⁻¹` of `ttc_defs` (`conjQ_coe`).

Route (`NOTES_LEAD_bs_zs_tits.md` §1): `tildeOf_eq` (`∼x = h(x)⁻¹ f(x) h(x)`), the `h`-product
formula `canon_H8` (`Submission.Work.ZassenhausSuzuki.canon_H8`:
`h(x₁x₂) = h(x₁)·h(f x₁ g x₂)·h(x₂)`), `canon_H7`
(`f(x₁x₂) = h(x₂)·f(y)·h(x₂)⁻¹·f(x₂)`) and the commutativity of `D` (`canon_D_abelian_mul`).
Both sides are elements of `Q`, so `Subtype.ext` + `conjQ_coe` reduce everything to a group
computation in `G` (insert `h₁ h₁⁻¹`, `h_y h_y⁻¹` and commute the `D`-elements).  Do not cite the
`unproved` placeholders of `TitsDesign`; check `#print axioms`. -/
theorem szTilde_mul_formula {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x₁ x₂ y : Q}
    (hx₁ : (x₁ : G) ≠ 1) (hx₂ : (x₂ : G) ≠ 1) (hx₁₂ : ((x₁ * x₂ : Q) : G) ≠ 1)
    (hy : (y : G) = Work.ZassenhausSuzuki.fG C x₁ * Work.ZassenhausSuzuki.gG C x₂)
    (hy1 : (y : G) ≠ 1) :
    Work.ZassenhausSuzuki.tildeOf C (x₁ * x₂)
      = Work.ZassenhausSuzuki.conjQ hsplit (C.h x₁)⁻¹ (Work.ZassenhausSuzuki.tildeOf C y)
        * Work.ZassenhausSuzuki.conjQ hsplit (((C.h x₁) * (C.h y))⁻¹)
            (Work.ZassenhausSuzuki.tildeOf C x₂) := by
  have hy_eq : y = C.f x₁ * C.g x₂ := by
    apply Subtype.ext
    simpa [fG, gG] using hy
  have hH7 : fG C (x₁ * x₂)
      = hG C x₂ * fG C (C.f x₁ * C.g x₂) * (hG C x₂)⁻¹ * fG C x₂ := by
    simpa [fG, hG] using canon_H7 hsplit hzass h2 C x₁ x₂ hx₁ hx₂ hx₁₂
  have hH8 := canon_H8 hsplit hzass h2 C x₁ x₂ hx₁ hx₂ hx₁₂
  have hab : hG C x₁ * hG C y = hG C y * hG C x₁ :=
    canon_D_abelian_mul hsplit hzass h2 (C.h x₁).2 (C.h y).2
  have hac : hG C x₁ * hG C x₂ = hG C x₂ * hG C x₁ :=
    canon_D_abelian_mul hsplit hzass h2 (C.h x₁).2 (C.h x₂).2
  have hbc : hG C y * hG C x₂ = hG C x₂ * hG C y :=
    canon_D_abelian_mul hsplit hzass h2 (C.h y).2 (C.h x₂).2
  have hL : ((tildeOf C (x₁ * x₂) : Q) : G)
      = (hG C x₁ * hG C y * hG C x₂)⁻¹
        * (hG C x₂ * fG C y * (hG C x₂)⁻¹ * fG C x₂)
        * (hG C x₁ * hG C y * hG C x₂) := by
    rw [tildeOf_eq hsplit hzass h2 C hx₁₂, hH7, hH8, ← hy_eq]
  have hR : ((conjQ hsplit (C.h x₁)⁻¹ (tildeOf C y)
        * conjQ hsplit ((C.h x₁ * C.h y)⁻¹) (tildeOf C x₂) : Q) : G)
      = (hG C x₁)⁻¹ * ((hG C y)⁻¹ * fG C y * hG C y) * hG C x₁
        * ((hG C y)⁻¹ * (hG C x₁)⁻¹ * ((hG C x₂)⁻¹ * fG C x₂ * hG C x₂)
            * hG C x₁ * hG C y) := by
    rw [Subgroup.coe_mul, conjQ_coe, conjQ_coe,
      tildeOf_eq hsplit hzass h2 C hy1, tildeOf_eq hsplit hzass h2 C hx₂]
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev, inv_inv]
    group
  refine Subtype.ext ?_
  rw [hL, hR]
  exact szTilde_mul_formula_aux (hG C x₁) (hG C y) (hG C x₂) (fG C y) (fG C x₂) hab hac hbc

end Work.ZassenhausSuzuki
