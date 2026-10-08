import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

set_option linter.dupNamespace false

namespace Work.CORE3

open Work.GW2

/-! ## Support API: the normalizer of the image of a normal subgroup -/

/-- If `M ⊴ ↥K` then `K` normalizes the image of `M` in `G`: the conjugation action of `K` on
itself is the restriction of the conjugation action of `G`.  (General group theory; used below
with `K = Ĥ` and `M = O₂(Ĥ)`.) -/
theorem le_normalizer_map_subtype {G : Type*} [Group G] (K : Subgroup G) (M : Subgroup ↥K)
    [M.Normal] : K ≤ Subgroup.normalizer (M.map K.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx g hg
  rw [Subgroup.mem_map] at hg ⊢
  obtain ⟨y, hy, rfl⟩ := hg
  exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : M.Normal) y hy ⟨x, hx⟩, by simp⟩

/-- Bender 1981 §3, p. 223: with `V = O₂(Ĥ)` a four-group, `V ⊴ Ĥ` and `V` is not normal in `G`
(`G` is non-abelian simple and `V ≠ 1`), so maximality of `Ĥ` gives `N_G(V) = Ĥ`.  Used in (5)
(an involution inverted in `N_G(V) = Ĥ` lies in `K`). -/
theorem NormalizerPcoreEqHhat (G : Type) [Group G] [Finite G] (h : BenderCtx G)
    (B : BenderSetup G) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) :
    Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := h.simple
  have h4card : Nat.card (pCoreIn 2 B.Hhat) = 4 := h4.1
  -- `V = O₂(Ĥ) ≤ Ĥ` and `V ⊴ Ĥ`, hence `Ĥ ≤ N_G(V)`.
  have hle : pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hnorm : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [pCoreIn] using le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat)
  -- `Ĥ` is a maximal subgroup, and `V ≠ 1`, `V ≠ G`: so `N_G(V)` cannot be `G`.
  refine le_antisymm ?_ hnorm
  by_contra hcon
  have hne : B.Hhat ≠ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    fun heq => hcon (le_of_eq heq.symm)
  have htop : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = ⊤ :=
    (B.Hhat_coatom.lt_iff).mp (lt_of_le_of_ne hnorm hne)
  -- So `V` would be normal in the simple group `G`, hence trivial or all of `G`.
  have hVn : (pCoreIn 2 B.Hhat : Subgroup G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreIn 2 B.Hhat) with hb | ht
  · -- `V = ⊥` contradicts `|V| = 4`.
    have h1 : Nat.card (pCoreIn 2 B.Hhat) = 1 := by rw [hb]; exact Subgroup.card_bot
    exact absurd (h4card.symm.trans h1) (by norm_num)
  · -- `V = ⊤` contradicts `V ≤ Ĥ ≠ ⊤`.
    exact B.Hhat_coatom.ne_top (top_le_iff.mp (ht ▸ hle))

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- The same statement, exposed under the doubly nested name `Work.CORE3.Work.CORE3.
NormalizerPcoreEqHhat` of the module's original skeleton: if `O₂(Ĥ)` is a four-group then it is
normal in `Ĥ` but not in `G` (`G` simple, `O₂(Ĥ) ≠ 1`, `Ĥ ≠ ⊤`), so maximality of `Ĥ` forces
`N_G(O₂(Ĥ)) = Ĥ`. -/
theorem NormalizerPcoreEqHhat (G : Type) [Group G] [Finite G] (h : BenderCtx G)
    (B : BenderSetup G) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) :
    Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
  _root_.Work.CORE3.NormalizerPcoreEqHhat G h B h4

end Work.CORE3

end Work.CORE3
