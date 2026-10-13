/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/ClauseHon`: the honest level-4 `T2` clause, and the target `IP4T2Honest`

This is the honest (`SmoothOpen`-based) form of `VocabO.T2Clause` for the concrete coercive
inner product `Assembly.IP4 1 1 1 1 1 1` of the `ℋ⁴` chapter.  The assembly is the frozen one
(`TransportS.ClauseBridge.T2Clause_of_slot` + `IPGen.ip4SlotDomGen`): the `75` leaves of the
unfolding of `IP4` are bounded by the per-slot estimates `T2SlotHon` (`Hon/SlotHon`) and summed.

The final theorem `IP4T2Honest_of_pieces` has exactly the shape of the assigned target
`Work.FTS.StrongPersist.N6Trans.IP4T2Honest`, with the two `Prop`s `TopSlotHonProp` /
`DelicateHonProp` (the honest radial integration by parts and the delicate term) as hypotheses.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotHon
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotAbsHon
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ClauseBridge
import Submission.Work.FTS.IPGen.ip4SlotDomGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

open Work.FTS.TransportS
open Work.FTS.TransportS.T2Sup

/-! ## The honest clause -/

/-- **The honest `T2` clause** of the level-four transport estimates: the pairing of `f·D_z g`
against `g`, with the angular liveness of the coefficient measured by `CoefTh 1 f`, in the
honest class (`SmoothOpen` on the open quadrant + `ℋ⁴`/`ℋ⁵`-honesty + the mixed radial decay
of order `4`). -/
def T2ClauseHon (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop :=
  ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.CoefThMem 1 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2

/-- The `25` leaf terms of `leafSum` are each at most `3R`, hence the sum is at most `75R`
(honest copy of the private `TransportS.leafSum_le`). -/
private theorem leafSum_le_hon (α : ℝ) (u v : Fn) (R : ℝ) (hR : 0 ≤ R)
    (hterm : ∀ a ∈ Finset.range 5, ∀ b ∈ Finset.range 5,
      (if a + b ≤ 4 then
          |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
            + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)
        else 0) ≤ 3 * R) :
    leafSum α u v ≤ 75 * R := by
  unfold leafSum
  refine le_trans (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
    hterm a ha b hb) ?_
  have : (∑ _a ∈ Finset.range 5, ∑ _b ∈ Finset.range 5, (3 * R)) = 75 * R := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [this]

/-- **The honest clause from the honest per-slot bound and a slot domination.** -/
theorem T2ClauseHon_of_slot {IP : ℝ → Fn → Fn → ℝ} {α₂ K C : ℝ} (hC : 0 ≤ C) (hα₂ : α₂ ≤ 1)
    (hS : T2SlotHon C) (hD : SlotDomIP α₂ K IP) : T2ClauseHon IP α₂ (K * 75 * C) := by
  obtain ⟨hKpos, hD⟩ := hD
  intro α hα f g hf1 hf2 hf3 hsg hmg4 hmg5 hdec
  have hf : HonF α f := ⟨hf1, hf2, hf3⟩
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂
  set u : Fn := fun z θ => f z θ * Work.Spaces.Dz g z θ with hu_def
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    hf.1.mul (Work.FTS.EllipticEst.SmoothOpen.Dz hsg)
  have hv : Work.FTS.EllipticEst.SmoothOpen g := hsg
  have hmain := hD α hα u g hu hv
  have hR : 0 ≤ C * α ^ (-(1 / 2 : ℝ))
      * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hα.1.le _))
      (add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (coefTh_nonneg 1 f))) (sq_nonneg _)
  have hslot : ∀ (a b : ℕ), a + b ≤ 4 → ∀ ρ : ℝ → ℝ → ℝ, IsLeafW α a ρ →
      |slotPairing ρ a b u g| ≤ C * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
    fun a b hab ρ hρ => hS α f g hαpos hα1 hf hsg hmg4 hmg5 hdec a b ρ hab hρ
  have hsum : leafSum α u g ≤ 75 * (C * α ^ (-(1 / 2 : ℝ))
      * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
      * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine leafSum_le_hon α u g _ hR ?_
    intro a ha b hb
    by_cases hab : a + b ≤ 4
    · rw [if_pos hab]
      have h1 := hslot a b hab leafEta (Or.inl rfl)
      have h2 := hslot a b hab leafOne (Or.inr (Or.inl rfl))
      by_cases ha1 : 1 ≤ a
      · rw [if_pos ha1]
        have h3 := hslot a b hab (leafGam α) (Or.inr (Or.inr ⟨ha1, rfl⟩))
        linarith
      · rw [if_neg ha1]; linarith
    · rw [if_neg hab]
      linarith
  calc |IP α u g| ≤ K * leafSum α u g := hmain
    _ ≤ K * (75 * (C * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2)) := mul_le_mul_of_nonneg_left hsum hKpos.le
    _ = (K * 75 * C) * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2 := by ring

/-! ## The target, from the two honest pieces -/

/-- **The level-four `T2` clause for `IP4` in the honest class**, from the honest radial
integration by parts and the honest delicate bound.  This is the assigned target
`Work.FTS.StrongPersist.N6Trans.IP4T2Honest` with precisely those two inputs. -/
theorem IP4T2Honest_of_pieces (hTop : TopSlotHonProp) (hDel : DelicateHonProp) :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      T2ClauseHon (Work.FTS.CoercivityFix.Assembly.IP4 1 1 1 1 1 1) α₂ Ct := by
  obtain ⟨C, hC, hS⟩ := T2SlotHon_of_slotAbs hTop hDel
  have hD := Work.FTS.IPGen.ip4SlotDomGen (c₁ := 1) (c₂ := 1) (c₁' := 1) (c₂' := 1)
    (c₁'' := 1) (c₂'' := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨(max 1 (max 1 (max 1 (max 1 (max 1 (max 1 1))))) ^ 3 * 3 ^ 3 * 10 ^ 22) * 75 * C,
    1, mul_pos (mul_pos hD.1 (by norm_num)) hC, one_pos, ?_⟩
  exact T2ClauseHon_of_slot (le_of_lt hC) le_rfl hS hD

end Work.FTS.StrongPersist.N6Trans.Hon
