import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_four

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **App. I (4) sharpened: `K` is a subgroup when it meets `V = C_X(t)` trivially.**

Let `d` be prime, `t ∈ G` of order `d`, `X ≤ G` normalised by `t` with `|X|` prime to `d`, and
`K = Kapp t X = {t⁻¹x⁻¹tx | x ∈ X}`.  If `⟨K⟩ ∩ (C_G(t) ∩ X) = 1`, then `K` *is* a subgroup —
namely `⟨K⟩` — and it is a normal complement of `C_X(t) = C_G(t) ∩ X` in `X`:
`⟨K⟩ ≤ X`, `X ≤ N_G(⟨K⟩)`, `⟨K⟩ ∩ C_X(t) = 1`, `⟨K⟩ · C_X(t) = X`.

The mathematics: App. I (4) gives `K ⊆ X`, that `X` normalises `⟨K⟩`, the decomposition
`⟨K⟩ · C_X(t) = X`, and the counting identity `|⟨K⟩| = |K| · |C_X(t) ∩ ⟨K⟩|`.  The hypothesis
`⟨K⟩ ∩ C_X(t) = 1` makes the second factor `1`, so `|K| = |⟨K⟩|`; since `K ⊆ ⟨K⟩` and both are
finite, `K = ⟨K⟩` as sets.  The complement conditions are then the App. I (4) facts themselves. -/
theorem exists_normalComplement_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {d : ℕ}
    (hd : d.Prime) {t : G} (ht : orderOf t = d) {X : Subgroup G}
    (htX : Work.NormalComplement.NormalizedBy t X) (hdX : Nat.Coprime (Nat.card X) d)
    (hbot : Subgroup.closure (Work.NormalComplement.Kapp t X) ⊓
      (Subgroup.centralizer ({t} : Set G) ⊓ X) = ⊥) :
    ∃ K : Subgroup G, (K : Set G) = Work.NormalComplement.Kapp t X ∧
      Work.NormalComplement.IsNormalComplementOf K (Subgroup.centralizer ({t} : Set G) ⊓ X) X := by
  obtain ⟨hKappX, -, hXnorm, hsup, -, -, hcard⟩ := appI_four hd ht htX hdX
  -- `X` normalises `⟨K⟩`
  have hnormal : X ≤ Subgroup.normalizer ((Subgroup.closure (Kapp t X)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact hXnorm
  -- the hypothesis, re-associated as `C_X(t) ∩ ⟨K⟩ = 1`
  have hbot' : Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ Subgroup.closure (Kapp t X) = ⊥ := by
    rw [inf_comm (Subgroup.centralizer ({t} : Set G) ⊓ X)]
    exact hbot
  -- counting: `|⟨K⟩| = |K| · |C_X(t) ∩ ⟨K⟩| = |K|`
  have hcardK : Nat.card ↥(Subgroup.closure (Kapp t X)) = (Kapp t X).ncard := by
    rw [hcard, hbot', Subgroup.card_bot, mul_one]
  have hKc : ((Subgroup.closure (Kapp t X) : Subgroup G) : Set G).ncard = (Kapp t X).ncard := by
    rw [← Nat.card_coe_set_eq (Subgroup.closure (Kapp t X) : Set G)]
    exact hcardK
  -- `K ⊆ ⟨K⟩` with equal cardinality, in a finite group
  have hset : (Kapp t X) = ((Subgroup.closure (Kapp t X) : Subgroup G) : Set G) := by
    refine Set.eq_of_subset_of_ncard_le Subgroup.subset_closure ?_
    rw [hKc]
  exact ⟨Subgroup.closure (Kapp t X), hset.symm,
    (Subgroup.closure_le X).mpr hKappX, hnormal, hbot, hsup⟩

end Work.NormalComplement
