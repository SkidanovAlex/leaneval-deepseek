import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAe
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.t3SlotHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

theorem IP4T3Honest : ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
        Work.FTS.VocabO.CoefThMem 3 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
      |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α
          (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
            * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨C, hC, hS⟩ := Work.FTS.StrongPersist.N6Trans.Hon.t3SlotHonest
  obtain ⟨K, α₂, hK, hα₂, hKD⟩ := Work.FTS.TransportS.ip4SlotDomFixed
  obtain ⟨hKpos, hD⟩ := hKD
  refine ⟨K * 75 * C, min α₂ 1, by positivity, lt_min hα₂ one_pos, ?_⟩
  intro α hα f g hsf hwf hcf hsg hm4 hm5 hdec
  have hαpos : 0 < α := hα.1
  have hαle : α ≤ 1 := le_trans hα.2 (min_le_right _ _)
  have hmem : α ∈ Set.Ioc 0 α₂ := ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
  have htr : Work.FTS.StrongPersist.N6Trans.Hon.TraceAe g :=
    Work.FTS.StrongPersist.N6Trans.Hon.traceAe_of_honG hαpos hsg hm4 hm5
  set u : Work.FTS.Galerkin.Fn := fun z θ => f z θ * Work.Spaces.Dz g z θ with hu
  have hsu : Work.FTS.EllipticEst.SmoothOpen u :=
    hsf.mul (Work.FTS.EllipticEst.SmoothOpen.Dz hsg)
  have hmain := hD α hmem u g hsu hsg
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
  calc |Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1 α u g|
      = |(Work.FTS.CoercivityStep.IP4 α) u g| := rfl
    _ ≤ K * Work.FTS.TransportS.leafSum α u g := hmain
    _ ≤ K * (75 * R) := mul_le_mul_of_nonneg_left hsum hK.le
    _ = (K * 75 * C) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * (Work.Spaces.HkNorm α 4 g) ^ 2 := by rw [hR]; ring

end Work.FTS.StrongPersist.N6Trans
