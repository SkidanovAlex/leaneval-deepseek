import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T3Honest
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Asm
import Submission.Work.FTS.TransportS.T2Sup.srestBound
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T3HonestGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- The honest (open-quadrant) `T3S` transport clause for the coercive pairing
`Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''` with **free positive step coefficients**: the
per-slot bound `Hon.t3SlotHonest` summed over the `75` leaves of the unfolding, whose slot
domination is `IPGen.ip4SlotDomGen`.  (The unit-coefficient case is `IP4T3Honest`.) -/
theorem T3HonestGen (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₁' : 0 < c₁') (h₂' : 0 < c₂') (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
        Work.FTS.VocabO.CoefThMem 3 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          ≤ Ct * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨C, hC, hS⟩ := Work.FTS.StrongPersist.N6Trans.Hon.t3SlotHonest
  have hD := Work.FTS.IPGen.ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁')
    (c₂' := c₂') (c₁'' := c₁'') (c₂'' := c₂'') h₁.le h₂.le h₁'.le h₂'.le h₁''.le h₂''.le
  set K : ℝ := max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3
    * 10 ^ 22 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; exact hD.1
  have hDbound : ∀ α ∈ Set.Ioc 0 (1 : ℝ), ∀ u g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen g →
      |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α u g|
        ≤ K * Work.FTS.TransportS.leafSum α u g := by
    rw [hKdef]; exact hD.2
  refine ⟨K * 75 * C, 1, mul_pos (mul_pos hKpos (by norm_num)) hC, one_pos, ?_⟩
  intro α hα f g hsf hwf hcf hsg hm4 hm5 hdec
  have hαpos : 0 < α := hα.1
  have hαle : α ≤ 1 := hα.2
  have htr : Work.FTS.StrongPersist.N6Trans.Hon.TraceAe g :=
    Work.FTS.StrongPersist.N6Trans.Hon.traceAe_of_honG hαpos hsg hm4 hm5
  set u : Work.FTS.Galerkin.Fn := fun z θ => f z θ * Work.Spaces.Dz g z θ with hu
  have hsu : Work.FTS.EllipticEst.SmoothOpen u :=
    hsf.mul (Work.FTS.EllipticEst.SmoothOpen.Dz hsg)
  have hmain := hDbound α hα u g hsu hsg
  -- the per-slot constant
  set R : ℝ := C * α ^ (-(1 / 2 : ℝ))
      * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
      * (Work.Spaces.HkNorm α 4 g) ^ 2 with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hαpos.le _))
      (add_nonneg (Work.Spaces.WlInf_nonneg α 4 f hwf)
        (Work.FTS.TransportS.coefTh_nonneg 3 f))) (sq_nonneg _)
  have hslot : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b u g| ≤ R := by
    intro a b ρ hab hρ
    exact hS α f g hαpos hαle ⟨hsf, hwf, hcf⟩ hsg hm4 hm5 hdec htr a b ρ hab hρ
  -- every leaf term is at most `3R`
  have hterm : ∀ a ∈ Finset.range 5, ∀ b ∈ Finset.range 5,
      (if a + b ≤ 4 then
        |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b u g|
          + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b u g|
          + (if 1 ≤ a then
              |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b u g|
            else 0)
      else 0) ≤ 3 * R := by
    intro a _ b _
    by_cases hab : a + b ≤ 4
    · rw [if_pos hab]
      have h1 := hslot a b Work.FTS.TransportS.leafEta hab (Or.inl rfl)
      have h2 := hslot a b Work.FTS.TransportS.leafOne hab (Or.inr (Or.inl rfl))
      by_cases ha1 : 1 ≤ a
      · rw [if_pos ha1]
        have h3 := hslot a b (Work.FTS.TransportS.leafGam α) hab (Or.inr (Or.inr ⟨ha1, rfl⟩))
        linarith
      · rw [if_neg ha1]; linarith
    · rw [if_neg hab]; linarith
  have hsum : Work.FTS.TransportS.leafSum α u g ≤ 75 * R := by
    have h1 : Work.FTS.TransportS.leafSum α u g
        ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, (3 * R) := by
      unfold Work.FTS.TransportS.leafSum
      exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    have h2 : (∑ _a ∈ Finset.range 5, ∑ _b ∈ Finset.range 5, (3 * R)) = 75 * R := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact h1.trans h2.le
  rw [hu]
  calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ K * Work.FTS.TransportS.leafSum α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g :=
        hmain
    _ ≤ K * (75 * R) := mul_le_mul_of_nonneg_left hsum hKpos.le
    _ = (K * 75 * C) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.Spaces.HkNorm α 4 g) ^ 2 := by rw [hR]; ring

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.LeafSum =====
section

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
end
