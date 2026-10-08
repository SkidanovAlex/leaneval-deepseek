import Mathlib
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.no_conj_le_T_101`

Peterfalvi II Ch. V §3, step (12), case (10-1): **no conjugate of `P` is contained in `T`**.

In the standing context `CtxF H Q t s r P` the subgroup `P ≤ centD H t` has prime order, and
`T` is inverted elementwise by the involution `s` (`hsT`).  Hence every element of a conjugate
`cj g P ≤ T` is *strongly real*: if `s * y * s⁻¹ = y⁻¹` and `s² = 1`, then `y = s * (s * y)` is a
product of two involutions.  Since `x ∈ P^# ≤ centD H t` with `x ≠ 1`, the element
`g * x * g⁻¹ ∈ cj g P ≤ T` is strongly real, contradicting Ch. V §2 Lemma 4
(`S4_centD_not_stronglyReal`, which says that no non-trivial element of `centD H t` nor any of
its conjugates is strongly real).

Self-contained: the only mathematical input is `S4_centD_not_stronglyReal`; the two bookkeeping
lemmas are proved locally (with `_101` suffixes so as not to clash with the identical lemmas in
`Prove/orb_eq_AT_union_101`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

/-- `s * s = 1` from `orderOf s = 2`. -/
theorem sq_eq_one_of_orderOf_eq_two_101 {G : Type} [Group G] {s : G} (h : orderOf s = 2) :
    s * s = 1 := by
  have h1 := pow_orderOf_eq_one s
  rw [h, pow_two] at h1
  exact h1

/-- An involution `s` which inverts `y` makes `y` strongly real: `y = s * (s * y)`. -/
theorem stronglyReal_of_inv_conj_eq_inv_101 {G : Type} [Group G] {s y : G} (hs : s * s = 1)
    (hy : s * y * s⁻¹ = y⁻¹) : StronglyReal y := by
  have h3 : s * y * s = y⁻¹ := by
    calc s * y * s = (s * y * s⁻¹) * (s * s) := by group
      _ = y⁻¹ := by rw [hy, hs]; group
  refine ⟨s, s * y, hs, ?_, ?_⟩
  · calc (s * y) * (s * y) = (s * y * s) * y := by group
      _ = y⁻¹ * y := by rw [h3]
      _ = 1 := by group
  · rw [← mul_assoc, hs, one_mul]

theorem no_conj_le_T_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P T : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hsT : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹) :
    ∀ g : G, ¬ Work.ThmF.ChV3.cj g P ≤ T := by
  -- `s` is an involution
  have hs2 : s * s = 1 := sq_eq_one_of_orderOf_eq_two_101 c.s_inv
  -- `P` is non-trivial, of prime order
  have hbot : P ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥P = 1 := by rw [h]; simp
    exact absurd h1 (ne_of_gt c.P_prime.one_lt)
  intro g hle
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  -- the conjugate of `x` lies in `T`, hence is inverted by `s`, hence is strongly real
  have hmem : g * (x : G) * g⁻¹ ∈ T := by
    apply hle
    exact Subgroup.mem_map.mpr ⟨(x : G), x.2, MulAut.conj_apply g (x : G)⟩
  have hsr : StronglyReal (g * (x : G) * g⁻¹) :=
    stronglyReal_of_inv_conj_eq_inv_101 hs2 (hsT _ hmem)
  -- but `x ∈ P^# ≤ centD H t` is non-trivial, so Ch. V §2 Lemma 4 forbids this
  exact S4_centD_not_stronglyReal hC4 c (x : G) (c.P_le x.2)
    (fun h => hx1 (Subtype.ext h)) g hsr

end Work.ThmF.ChV3.Prove
