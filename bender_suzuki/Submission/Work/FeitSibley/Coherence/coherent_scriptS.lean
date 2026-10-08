import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.step1
import Submission.Work.FeitSibley.Coherence.step2
import Submission.Work.FeitSibley.Coherence.ti_selfnormalizing
import Submission.Work.FeitSibley.Coherence.pgroup_of_atMostOnePrime
import Submission.Work.FeitSibley.Coherence.coprime_card_Q_index
import Submission.Work.FeitSibley.Coherence.coherent_scriptS_sub_FSZ
import Submission.Work.FeitSibley.Coherence.coherent_scriptSR_of_pgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coherent_scriptS`

The Feit–Sibley coherence theorem (Peterfalvi II, Appendice XII, Théorème p. 289): for the
Feit–Sibley data `h : FSData G`, the set `𝒮 = scriptS h.H h.Q1` of irreducible characters of `H`
whose kernel does not contain `Q₁` is coherent for `Ind_H^G` (`indLin h.H`).

The engine of the proof lives in `Coherence/engine.lean` (linear-shift machinery,
`coherent_of_feit_step`, Milestone A `𝒮(Q')` coherent, the size bound `2|D| + 1 ≤ |A|`,
`H`-invariance of the lower central series of `S`); the pure reduction lemmas in
`Coherence/step1.lean`, `Coherence/step2.lean` and `Coherence/centerMod.lean`.  This file is the
assembly.

## The argument

The proof splits into four cases.

* **`[Q₁,Q₁] = ⊥` (i.e. `Q₁` abelian, any `D`).**  Then `[Q,Q] = [S,S]`, so `𝒮(S') = 𝒮(Q')` is
  coherent by Milestone A, and `𝒮(S')` suffices by Peterfalvi's **step (2)**
  (`Coherence/step1.lean`, `Coherence/step2.lean`).
* **`D = ⊥`.**  Then `H = Q`, so `Q` is a T.I. subgroup of `G` with `N_G(Q) = H = Q`.  For such
  a subgroup *every* orthonormal set of irreducible characters is coherent: the Dade shift
  `χ ↦ Ind_H^G (χ - χ(1)·1_H) + χ(1)·1_G` of `Ind_H^G` is an isometry with virtual-character
  values (`Coherence/ti_selfnormalizing.lean`).  This case is *outside* the range of App. XII
  (which assumes `D ≠ 1`).
* **`D ≠ ⊥` and `|Q₁|` divisible by two distinct primes**: Peterfalvi's **step (1)**, by
  descending a chief series in `Q₁` (`coherent_scriptSR_of_two_primes`).
* **`D ≠ ⊥` and `Q₁` a nonabelian `p`-group, `p` odd**: Peterfalvi's **steps (3)–(8)**, the
  two-block argument.  Here `Z = FSZ h = [Q₁,Q₁] ⊓ Z(Q₁) ≠ 1`, `𝒳 = 𝒮 - 𝒮(Z)` is coherent
  (`Coherence/coherent_scriptS_sub_FSZ.lean`, step (3)) and `𝒴 = 𝒮(Q')` is coherent (Milestone A);
  the coherent extensions of `𝒳` and `𝒴` provide the exceptional characters `e_i`, `e'_j`, whose
  mutual orthogonality (step (5), `Coherence/cfInner_eq_zero_of_two_coherent_blocks.lean`) and the
  congruence `ψ(z) ≡ ψ(1) mod |Q|` of step (7) (`Coherence/irr_congr_mod_card_Q.lean`) show
  `𝒳 ∪ 𝒴` coherent and then, by Feit's criterion, `𝒮(S')` coherent
  (`Coherence/coherent_scriptSR_of_pgroup.lean`).

Q is a Hall subgroup of G (`Coherence/coprime_card_Q_index.lean`), which step (7) requires; and
"`|Q₁|` divisible by at most one prime, `Q₁` not a `2`-group" makes `Q₁` a `p`-group with `p` odd
(`Coherence/pgroup_of_atMostOnePrime.lean`).
-/

set_option linter.unusedSectionVars false

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

theorem coherent_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1) (Work.FeitSibley.indLin h.H) := by
  classical
  by_cases hab : ⁅h.Q1, h.Q1⁆ = ⊥
  · -- `Q₁` abelian (any `D`): `[Q,Q] = [S,S]`, so `𝒮(S') = 𝒮(Q')` is coherent by Milestone A,
    -- and `𝒮(S')` suffices by Peterfalvi's step (2).  (This also covers `D = ⊥`.)
    refine coherent_scriptS_of_Q1_commutator_bot h hab ?_
    rw [FSQcomm_eq_sup h, hab, sup_bot_eq]
  · by_cases hD : h.D = ⊥
    · -- `D = ⊥`: then `H = Q`, so `Q` is a T.I. subgroup of `G` with `N_G(Q) = H = Q`.  By
      -- `coherent_of_ti_selfNormalizing` (`Coherence/ti_selfnormalizing.lean`) *every*
      -- orthonormal set of irreducible characters of `H` is then coherent for `Ind_H^G`: the
      -- Dade shift `χ ↦ Ind_H^G (χ - χ(1)·1_H) + χ(1)·1_G` of `Ind_H^G` by the single vector
      -- `1_G - Ind_H^G 1_H` is an isometry with virtual-character values.  This covers the
      -- case `D = 1`, which is outside the range of App. XII (there `D ≠ 1`).
      have hHQ : h.H = h.Q := by rw [← h.Q_sup_D, hD, sup_bot_eq]
      refine coherent_of_ti_selfNormalizing ?_ ?_ _ (fun x hx => ?_)
      · -- `H ≠ ⊥` (it contains `Q₁ ≠ 1`)
        intro hbot
        exact h.Q1_ne_bot (le_bot_iff.mp (hbot ▸ h.Q1_le_H))
      · -- `H` is a T.I. subgroup of `G`
        intro g hg
        rw [hHQ]
        exact h.Q_TI g hg
      · -- `𝒮` consists of irreducible characters
        exact Finset.mem_of_mem_filter x hx
    · refine coherent_scriptS_of_coherent_scriptSR_of_D_ne_bot h hD ?_
      by_cases h2 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
          p ∣ Nat.card h.Q1 ∧ q ∣ Nat.card h.Q1
      · -- `|Q₁|` divisible by two primes: Peterfalvi's step (1).
        exact coherent_scriptSR_of_two_primes h hD h2
      · -- `Q₁` a nonabelian `p`-group with `p` odd: Peterfalvi's steps (3)–(8).
        obtain ⟨p, hp, hp2, hpg⟩ :=
          exists_prime_isPGroup_of_atMostOnePrime h.Q1 h.Q1_ne_bot h.Q1_not_two h2
        exact coherent_scriptSR_of_pgroup h hD hp hp2 hpg hab (coprime_card_Q_index h)
          (coherent_scriptS_sub_FSZ h hD hp hp2 hpg hab)

end

end Work.FeitSibley.Coherence
