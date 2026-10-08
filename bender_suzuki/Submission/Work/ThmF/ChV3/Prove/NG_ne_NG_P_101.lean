import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.PGroup.lt_normalizer_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.NG_ne_NG_P_101`

Peterfalvi II Ch. V §3, step (12), case (10-1): `N_G(R) ≠ N_G(P)`.

In the standing context of §3 one has `C_G(P) ≤ N_G(R)` (`hRn`) and, in case (10-1),
`|R| = |P|^{m+1}` (`hcardR`, `hKer`, `hpf`) while `|G|_p = |P|^{m+2}` (`h101.2`).  If moreover
`N_G(P) = C_G(P)` (`hNG`), then `R`, whose order is *exactly* the `p`-part of `|C_G(P)|`
(`hCGp`), is a Sylow `p`-subgroup of `N_G(R) = C_G(P)`.  The elementary fact that a proper
subgroup of a finite `p`-group is strictly contained in its normalizer
(`Work.PGroup.lt_normalizer_inf`) then forces `R` to be a Sylow `p`-subgroup of `G` itself,
i.e. `|G|_p = |R| = |P|^{m+1}`, contradicting `|G|_p = |P|^{m+2}`.

The statement is used verbatim by `Work.ThmF.ChV3.Prove.m_eq_one_101` (leaf 12a).
-/

set_option autoImplicit false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- A `p`-subgroup `X` of a finite group, contained in the subgroup `K`, has order at most the
`p`-part of `|K|`. -/
private lemma card_le_pPart_of_le {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hXK : X ≤ K) (hX : IsPGroup p X) :
    Nat.card X ≤ Work.ThmF.ChV3.pPart p (Nat.card ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hcard : Nat.card ↥(X.subgroupOf K) = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, hk]
  have hdvd : Nat.card ↥(X.subgroupOf K) ∣ Nat.card ↥K :=
    Subgroup.card_subgroup_dvd_card (X.subgroupOf K)
  rw [hcard] at hdvd
  have hle : k ≤ (Nat.card ↥K).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hdvd
  calc Nat.card X = p ^ k := hk
    _ ≤ p ^ (Nat.card ↥K).factorization p := Nat.pow_le_pow_right hp.pos hle
    _ = Work.ThmF.ChV3.pPart p (Nat.card ↥K) := rfl

theorem NG_ne_NG_P_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P R : Subgroup G}
    {m : ℕ}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t)) (hm : 1 ≤ m)
    (hRc : R ≤ Work.ThmF.ChV3.CG P) (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hKer : Work.ThmF.ChV3.Ker H Q P t = P)
    (hcardR : Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P)
    (hCGp : Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card ↥(Work.ThmF.ChV3.CG P)) = Nat.card P ^ (m+1))
    (h101 : Work.ThmF.ChV3.Case101 H t P m) :
    Work.ThmF.ChV3.NG R ≠ Work.ThmF.ChV3.NG P := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  -- `|R| = |P| ^ (m+1)`
  have hker_card : Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) = Nat.card P := by rw [hKer]
  have hRcard : Nat.card R = Nat.card P ^ (m + 1) := by
    rw [hcardR, hker_card, ← hpf, pow_succ']
  -- `R` is a `|P|`-group
  have hRpg : IsPGroup (Nat.card P) ↥R := IsPGroup.of_card hRcard
  intro heq
  have hNGR : Work.ThmF.ChV3.NG R = Work.ThmF.ChV3.CG P := heq.trans hNG
  -- a Sylow `|P|`-subgroup of `G` containing `R`
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hRpg
  -- `R` exhausts `Q`
  have hQle : (Q : Subgroup G) ≤ R := by
    by_contra hQnle
    have hne : R ≠ (Q : Subgroup G) := fun h => hQnle h.ge
    have hlt : R < (Q : Subgroup G) := lt_of_le_of_ne hRQ hne
    -- a proper subgroup of the `p`-group `Q` is strictly contained in its normalizer
    have hlt2 : R < (Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R :=
      Work.PGroup.lt_normalizer_inf hp Q.isPGroup' hlt
    -- but `Q ⊓ N_G(R) ≤ N_G(R) = C_G(P)`, whose `p`-part is `|R|`
    have hXle : (Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R ≤ Work.ThmF.ChV3.CG P :=
      le_trans inf_le_right hNGR.le
    have hXpg : IsPGroup (Nat.card P) ↥((Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R) :=
      Q.isPGroup'.to_inf_left
    have hcardX : Nat.card ↥((Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R) ≤ Nat.card R := by
      have h1 := card_le_pPart_of_le hp hXle hXpg
      rw [hCGp, ← hRcard] at h1
      exact h1
    have hRXle : R ≤ (Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R :=
      le_inf hRQ Subgroup.le_normalizer
    have heqX : R = (Q : Subgroup G) ⊓ Work.ThmF.ChV3.NG R := by
      refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hRXle ?_)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardX
    exact (ne_of_lt hlt2) heqX
  -- hence `R` is a Sylow `|P|`-subgroup of `G`
  have hRQeq : R = (Q : Subgroup G) := le_antisymm hRQ hQle
  have hcardR' : Nat.card R = Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card G) := by
    rw [hRQeq]
    exact Sylow.card_eq_multiplicity Q
  -- `|P|^(m+2) = |R| = |P|^(m+1)`: impossible
  have hcontra : Nat.card P ^ (m + 2) = Nat.card P ^ (m + 1) := by
    rw [← h101.2, ← hcardR', hRcard]
  exact absurd hcontra (ne_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega)))

end Work.ThmF.ChV3.Prove
