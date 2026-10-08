import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API

namespace Work.CORE2B

-- Prove `Work.CORE2B.UNeBotProp_of_h22` (Bender 1981, Lemma 2.2's rider "In particular, U is not
-- trivial"): `Lemma22Prop` implies `U = O(C(t)) ≠ ⊥` for every `BenderSetup B`.
-- Route: if `B.U = ⊥` then `invSet ⊥ s = {1}` (the underlying set of `⊥`), so
-- `I := ⊥` witnesses clause (b) of Bender 2.2's configuration, clause (a) `S₀ ≤ C(⊥)` is trivial and
-- clause (c) is vacuous (there is no `X ≠ ⊥` with `X ≤ ⊥`); `s ∈ S − S₀` exists because
-- `S0.relIndex S = 2` with `S` finite.  So the forbidden configuration of `Lemma22Prop` holds,
-- contradiction.
/-- If `U = ⊥` then `I_U(s)` is (the underlying set of) the trivial subgroup: it consists of those
`x ∈ ⊥`, i.e. `x = 1`, and `1` always lies in `I_U(s)`. -/
theorem invSet_bot_coe {G : Type} [Group G] (s : G) :
    Work.GW2.invSet (⊥ : Subgroup G) s = ((⊥ : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    have hx1 : x = 1 := by simpa using hx.1
    rw [hx1]
    exact Subgroup.mem_bot.mpr rfl
  · intro hx
    have hx1 : x = 1 := by simpa using hx
    rw [hx1]
    exact ⟨Subgroup.mem_bot.mpr rfl, by simp⟩

theorem UNeBotProp_of_h22_proved : Work.CORE2B.UNeBotProp_of_h22 := by
  intro h22 G hG hFin hFT hCtx B hU
  -- `hU : B.U = ⊥`; exhibit the forbidden configuration of Bender's Lemma 2.2.
  refine h22 G hFT hCtx B ⟨?_, ?_⟩
  · -- (a) `S₀ ≤ C(U)`: every element of `U = ⊥` is `1`.
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw1 : w = 1 := by rw [hU] at hw; simpa using hw
    rw [hw1]; simp
  · -- (b) with `I := ⊥`: pick `s ∈ S − S₀` (exists since `S₀` has index `2` in `S`).
    obtain ⟨s, hsS, hs0, -⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp B.S0_index
    refine ⟨s, hsS, hs0, ⊥, ?_, ?_, ?_⟩
    · rw [hU, invSet_bot_coe]
    · rw [Subgroup.bot_subgroupOf]; infer_instance
    · -- (c) is vacuous: no `X ≠ ⊥` is contained in `⊥`.
      intro X hX hXI
      exact absurd (le_bot_iff.mp hXI) hX

end Work.CORE2B
