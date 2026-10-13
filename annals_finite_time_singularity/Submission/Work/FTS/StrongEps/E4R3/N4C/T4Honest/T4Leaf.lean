/-
# `E4R3/N4C/T4Honest/T4Leaf` — the leaf-sum bound for the `D_θ`-transport pairing

Assembling the per-slot bound `T4SlotBound` over the fifteen slots of `ℋ⁴` and the three leaf
weights of `H1IP` gives

  `leafSum α (f·D_θg) g ≤ Cb·WDp 4 f·HkSq α 4 g`,

which is the input of the final `IP4`-level clause `T4HonestGen`.  This is the honest
`WDp`-coefficient twin of `Work.FTS.StrongPersist.N6Trans.T1Hon.leafSum_bound`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4Slot
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open Work.FTS.StrongPersist.N6Trans.T1Hon

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The leaf-sum bound for the `D_θ`-transport pairing with a `D`-sup coefficient.** -/
theorem T4LeafSumBound : ∃ Cb : ℝ, 0 < Cb ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
        ≤ Cb * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C, hCpos, hC⟩ := T4SlotBound
  refine ⟨75 * C, by linarith, ?_⟩
  intro α f g hα hα1 hf hwf hg hmg hdg
  set u : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  set K : ℝ := C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (le_of_lt hCpos)
      (Work.FTS.OpenPkg.WDp_nonneg 4 f)) (Work.Spaces.HkSq_nonneg α 4 g)
  have e1 : t1W Work.Spaces.eta = Work.FTS.TransportS.leafEta := rfl
  have e2 : t1W 0 = Work.FTS.TransportS.leafOne := by
    funext z θ
    simp only [t1W, Work.FTS.TransportS.leafOne, neg_zero, Real.rpow_zero, mul_one]
  have e3 : t1W (Work.Spaces.gam α) = Work.FTS.TransportS.leafGam α := rfl
  have key : ∀ a b : ℕ, a + b ≤ 4 →
      |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
             else 0)
        ≤ 3 * K := by
    intro a b hab
    have h1 : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g| ≤ K := by
      have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab Work.Spaces.eta
        (fun _ => Or.inr rfl) (fun _ => Or.inr (Or.inl rfl))
      rw [← hKdef] at ht
      rw [e1] at ht
      exact ht
    have h2 : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g| ≤ K := by
      have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab 0
        (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
      rw [← hKdef] at ht
      rw [e2] at ht
      exact ht
    by_cases ha : 1 ≤ a
    · have h3 : |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
          ≤ K := by
        have ht := hC α f g hα hα1 hf hwf hg hmg hdg a b hab (Work.Spaces.gam α)
          (fun h => absurd h (by omega)) (fun _ => Or.inr (Or.inr rfl))
        rw [← hKdef] at ht
        rw [e3] at ht
        exact ht
      rw [if_pos ha]
      linarith
    · rw [if_neg ha]
      linarith
  have hsum : (∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
        (if a + b ≤ 4 then
          |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
            + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
            + (if 1 ≤ a then
                |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
              else 0)
        else 0))
      ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, (3 * K) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hab : a + b ≤ 4
    · rw [if_pos hab]; exact key a b hab
    · rw [if_neg hab]; linarith
  rw [Work.FTS.TransportS.leafSum]
  calc (∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
        (if a + b ≤ 4 then
          |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
            + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
            + (if 1 ≤ a then
                |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
              else 0)
        else 0))
      ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, (3 * K) := hsum
    _ = 75 * K := by
        simp only [Finset.sum_const, Finset.card_range]
        ring
    _ = 75 * C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
        rw [hKdef]; ring

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
