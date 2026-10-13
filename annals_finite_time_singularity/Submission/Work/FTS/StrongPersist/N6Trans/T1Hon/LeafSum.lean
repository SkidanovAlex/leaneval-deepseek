/-
# `T1Hon/LeafSum` — the honest-class `leafSum` bound for the `D_θ`-transport pairing

Assembling the per-slot bound `slotPairing_bound` over the fifteen slots of `ℋ⁴` and the three
leaf weights of `H1IP` gives

  `leafSum α (f·D_θg) g ≤ Cb/√(γ-1)·|f|_{ℋ⁴}·HkSq α 4 g`

in the honest class (`SmoothOpen` + `HkMem α 4`, with `DecayAll 4 g`), which is exactly the
hypothesis of `IP4T1Aux.IP4T1Honest_of_leafSumBound`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Asm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The honest-class `leafSum` bound for the `D_θ`-transport pairing.** -/
theorem leafSum_bound : ∃ Cb : ℝ, 0 < Cb ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
        ≤ Cb / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C, hCpos, hC⟩ := slotPairing_bound
  refine ⟨75 * C, by linarith, ?_⟩
  intro α f g hα hα1 hf hmf hg hmg hdg
  set u : ℝ → ℝ → ℝ := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  set K : ℝ := C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
      * Work.Spaces.HkSq α 4 g with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (div_nonneg hCpos.le (Real.sqrt_nonneg _))
      (Work.Spaces.HkNorm_nonneg α 4 f)) (Work.Spaces.HkSq_nonneg α 4 g)
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
      have ht := hC α f g hα hα1 hf hmf hg hmg hdg a b hab Work.Spaces.eta
        (fun _ => Or.inr rfl) (fun _ => Or.inr (Or.inl rfl))
      rw [← hKdef] at ht
      rw [e1] at ht
      exact ht
    have h2 : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g| ≤ K := by
      have ht := hC α f g hα hα1 hf hmf hg hmg hdg a b hab 0
        (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
      rw [← hKdef] at ht
      rw [e2] at ht
      exact ht
    by_cases ha : 1 ≤ a
    · have h3 : |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
          ≤ K := by
        have ht := hC α f g hα hα1 hf hmf hg hmg hdg a b hab (Work.Spaces.gam α)
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
    _ = 75 * C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
        rw [hKdef]; ring

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
