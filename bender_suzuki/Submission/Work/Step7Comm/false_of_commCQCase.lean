import Mathlib
import Submission.Work.Step7Comm.Defs
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.ChV12.L6faith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

/-!
# `Work.Step7Comm.false_of_commCQCase` — the case analysis of Ch. V §3 step (7), commutative branch

This is the last step of the *direct* (near-field-free) proof of step (7) in the abelian case.
The structural inputs are

* `h15.hQ0`: `|Q₀sub H| = 2 ^ |P|`,
* `h15.h4` : `|Q| = |C_Q(P)| ^ |P|`,
* `hcases` : `(|C_Q(P)|, f)` is `(2,3)`, `(4,5)` or `(8,3)` (`commCQCase_of_arithmetic`),
* `htri`   : `§2 Lemma 2 (c)` at the prime-order subgroup `⟨w⟩`: `f = 3` and
  `|Q ⊓ C_G(w)| = |Q₀sub H|`, or `f = 5` and `|Q ⊓ C_G(w)| = |Q₀sub H|²`, or `f = 3` and
  `|Q ⊓ C_G(w)| = |Q₀sub H|³` (`trichotomy_at_mem_W`),
* `helQ0`  : `Q₀sub H` is elementary abelian of exponent two,
* `c.F1`   : `C_G(P)` contains no four-group.

Writing `ℓ = |Q₀sub H| = 2 ^ |P| ≥ 2` and `C = Q ⊓ C_G(w)`, the arithmetic of `|Q| = |C_Q(P)| ^ |P|`
gives `|Q| = ℓ`, `ℓ²`, `ℓ³` in the three cases of `hcases`.  Since `C ≤ Q`, comparing with the
three possibilities of `htri`:

* `|C| = |Q|` forces `C = Q`, so `w` centralises `Q` — impossible because `D = H ⊓ H^t` acts
  faithfully on `Q` (`L6faith.eq_one_of_centralizes_Q`) while `w ∈ W ≤ D` and `w ≠ 1`;
* `|C| = ℓ³ > ℓ = |Q|` is impossible outright (`hbig`);
* the only remaining case is `|C_Q(P)| = 8`, `|C| = ℓ = |Q₀sub H|`: then `Q₀sub H ≤ C` with equal
  orders gives `C = Q₀sub H`, so `C_Q(P) ≤ Q₀sub H` (as `w` centralises `C_Q(P)`) is elementary
  abelian of exponent two of order `8 ≥ 4` and lies in `C_G(P)` — a four-group in `C_G(P)`,
  contradicting `c.F1`.
-/

namespace Work.Step7Comm

theorem false_of_commCQCase {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) {w : G}
    (hwW : w ∈ Work.ThmF.W H t) (hw1 : w ≠ 1)
    (hwC : w ∈ Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G))
    (hQ0leC : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({w} : Set G))
    (hQ0leQ : Work.ThmF.Q0sub H ≤ Q)
    (helQ0 : Work.Step7Comm.IsElementaryAbelianTwo (Work.ThmF.Q0sub H))
    (hcases : Work.Step7Comm.CommCQCase (orderOf (s * t))
      (Nat.card ↥(Work.ThmF.ChV3.CQ Q P)))
    (htri : (orderOf (s * t) = 3 ∧
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) = Nat.card ↥(Work.ThmF.Q0sub H)) ∨
      (orderOf (s * t) = 5 ∧
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Work.ThmF.Q0sub H) ^ 2) ∨
      (orderOf (s * t) = 3 ∧
        Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)) : False := by
  classical
  -- `w ∈ W ≤ centD H t ≤ D = twoPoint H t`
  have hwD : w ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint t (Work.ThmF.W_le_centD H t hwW)
  -- `ℓ = |Q₀sub H| = 2 ^ |P| ≥ 2`
  have hk1 : 1 ≤ Nat.card P := Nat.card_pos
  have hL2 : 2 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [h15.hQ0]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) hk1
  have hLcube : Nat.card ↥(Work.ThmF.Q0sub H) < (Nat.card ↥(Work.ThmF.Q0sub H)) ^ 3 := by
    nlinarith [sq_nonneg ((Nat.card ↥(Work.ThmF.Q0sub H) : ℤ))]
  -- `C = Q ⊓ C_G(w) ≤ Q`
  have hDleQ : (Q ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Q := inf_le_left
  have hcardDQ : Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) ≤ Nat.card ↥Q :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hDleQ) (Subgroup.inclusion_injective hDleQ)
  have hbig : Nat.card ↥Q < Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) → False :=
    fun hlt => absurd hcardDQ (not_le.mpr hlt)
  -- `|C| = |Q|` forces `C = Q`, so that `w` centralises `Q`: impossible by `L6faith`.
  have hfalseQ :
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) = Nat.card ↥Q → False := by
    intro hcard
    have hDQ : (Q ⊓ Subgroup.centralizer ({w} : Set G)) = Q :=
      Subgroup.eq_of_le_of_card_ge hDleQ (le_of_eq hcard.symm)
    have hcent : ∀ q ∈ Q, w * q = q * w := by
      intro q hq
      have hqD : q ∈ Q ⊓ Subgroup.centralizer ({w} : Set G) := hDQ.ge hq
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hqD).2).symm
    exact hw1 (Work.ThmF.ChV12.eq_one_of_centralizes_Q c.sit c.split hwD hcent)
  -- `|C_Q(P)| = 8` and `|C| = ℓ`: `C = Q₀sub H` and `C_Q(P)` is a four-group-bearing elementary
  -- abelian subgroup of `C_G(P)`, contradicting hypothesis (F1).
  have hfour : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 →
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(Work.ThmF.Q0sub H) → False := by
    intro hcq8 hDg
    have hQ0leD : Work.ThmF.Q0sub H ≤ Q ⊓ Subgroup.centralizer ({w} : Set G) :=
      le_inf hQ0leQ hQ0leC
    have hQ0eqD : Work.ThmF.Q0sub H = Q ⊓ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hQ0leD (le_of_eq hDg)
    have hCQleD : Work.ThmF.ChV3.CQ Q P ≤ Q ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine le_inf inf_le_left ?_
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwC y hy)
    have hCQleQ0 : Work.ThmF.ChV3.CQ Q P ≤ Work.ThmF.Q0sub H := by
      rw [hQ0eqD]; exact hCQleD
    exact c.F1 (Work.Step7Comm.hasFourGroup_centralizer_of_isElementaryAbelianTwo
      (X := P) (Y := Work.ThmF.ChV3.CQ Q P) inf_le_right (helQ0.mono hCQleQ0) (by omega))
  -- the arithmetic of `|Q| = |C_Q(P)| ^ |P|` against `|Q₀sub H| = 2 ^ |P|`
  have hpow : ∀ j : ℕ, Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 2 ^ j →
      Nat.card ↥Q = (Nat.card ↥(Work.ThmF.Q0sub H)) ^ j := by
    intro j hj
    rw [h15.h4, hj, ← pow_mul, Nat.mul_comm, pow_mul, h15.hQ0]
  rcases hcases with ⟨hcq2, hf3⟩ | ⟨hcq4, hf5⟩ | ⟨hcq8, hf3'⟩
  · -- `|C_Q(P)| = 2`, `f = 3`: `|Q| = ℓ`
    have hQ : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) := by
      have h := hpow 1 (by rw [hcq2]; norm_num)
      simpa using h
    rcases htri with ⟨-, hd⟩ | ⟨h5, -⟩ | ⟨-, hd3⟩
    · exact hfalseQ (by rw [hd, hQ])
    · omega
    · exact hbig (by rw [hQ, hd3]; exact hLcube)
  · -- `|C_Q(P)| = 4`, `f = 5`: `|Q| = ℓ²`
    have hQ : Nat.card ↥Q = (Nat.card ↥(Work.ThmF.Q0sub H)) ^ 2 := hpow 2 (by rw [hcq4]; norm_num)
    rcases htri with ⟨h3, -⟩ | ⟨-, hd⟩ | ⟨h3, -⟩
    · omega
    · exact hfalseQ (by rw [hd, hQ])
    · omega
  · -- `|C_Q(P)| = 8`, `f = 3`: `|Q| = ℓ³`
    have hQ : Nat.card ↥Q = (Nat.card ↥(Work.ThmF.Q0sub H)) ^ 3 := hpow 3 (by rw [hcq8]; norm_num)
    rcases htri with ⟨-, hd⟩ | ⟨h5, -⟩ | ⟨-, hd3⟩
    · exact hfour hcq8 hd
    · omega
    · exact hfalseQ (by rw [hd3, hQ])

end Work.Step7Comm
