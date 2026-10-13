/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-slot facts imply the frozen `IP4` transport clauses

`VocabO.T2Clause IP α₂ Ct` (resp. `VocabO.T3Clause IP α₂ Ct`) is the `t2` (resp. `t3`) clause
of `Work.FTS.Nonlin.N4Extra` with the new flat-coefficient hypotheses.  This module proves the
two implications

```
T2Slot C → SlotDomIP α₂ K IP → T2Clause IP α₂ (K * 75 * C)        (α₂ ≤ 1)
T3Slot C → SlotDomIP α₂ K IP → T3Clause IP α₂ (K * 75 * C)        (α₂ ≤ 1)
```

i.e. the N3 → N2 seam: once the per-slot transport bounds (`T2Slot`/`T3Slot`) and the (purely
algebraic) unfolding of the concrete `IP4` (`SlotDomIP`, proved as `ip4SlotDomFixed`) are
available, the clauses used by the rows follow by finite summation over the `75` leaves.
For the concrete `IP4` this gives

```
T2Clause (fun α => Work.FTS.CoercivityStep.IP4 α) α₂ (K * 75 * C)      -- from t2SlotGuarded
```

The only hypothesis beyond the two `Prop`s is `α₂ ≤ 1`: `T2Slot`/`T3Slot` are stated for
`0 < α ≤ 1`, while the clauses range over `α ∈ (0, α₂]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ip4SlotDomFixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `SmoothQuad` implies `SmoothOpen`.  (Named `_aux` because `GoodOpenBase.lean` in this
directory carries an identically-stated helper under the un-suffixed name.) -/
theorem smoothOpen_of_smoothQuad_aux {f : Fn} (h : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f :=
  h.mono fun p hp => ⟨by have := hp.1; simp only [Set.mem_Ioi] at this ⊢; linarith, hp.2⟩

/-- The `25` leaf terms of `leafSum` are each at most `3R`, hence the sum is at most `75R`. -/
private theorem leafSum_le (α : ℝ) (u v : Fn) (R : ℝ) (hR : 0 ≤ R)
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

/-- **`T2Clause` for any `IP` with a slot domination.** -/
theorem T2Clause_of_slot {IP : ℝ → Fn → Fn → ℝ} {α₂ K C : ℝ} (hC : 0 ≤ C) (hα₂ : α₂ ≤ 1)
    (hS : T2Slot C) (hD : SlotDomIP α₂ K IP) :
    Work.FTS.VocabO.T2Clause IP α₂ (K * 75 * C) := by
  obtain ⟨hKpos, hD⟩ := hD
  intro α hα f g hsf hmf hcf hreg hm5 hdec
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂
  set u : Fn := fun z θ => f z θ * Work.Spaces.Dz g z θ with hu_def
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    hsf.mul (Work.FTS.EllipticEst.SmoothOpen.Dz (smoothOpen_of_smoothQuad_aux hreg.1))
  have hv : Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad_aux hreg.1
  have hmain := hD α hα u g hu hv
  have hR : 0 ≤ C * α ^ (-(1 / 2 : ℝ))
      * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hα.1.le _))
      (add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (coefTh_nonneg 1 f))) (sq_nonneg _)
  have hslot : ∀ (a b : ℕ), a + b ≤ 4 → ∀ ρ : ℝ → ℝ → ℝ, IsLeafW α a ρ →
      |slotPairing ρ a b u g| ≤ C * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
    fun a b hab ρ hρ => hS α f g hαpos hα1 ⟨hsf, hmf, hcf⟩ ⟨hreg, hm5, hdec⟩ a b ρ hab hρ
  have hsum : leafSum α u g ≤ 75 * (C * α ^ (-(1 / 2 : ℝ))
      * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine leafSum_le α u g _ hR ?_
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

/-- **`T3Clause` for any `IP` with a slot domination.** -/
theorem T3Clause_of_slot {IP : ℝ → Fn → Fn → ℝ} {α₂ K C : ℝ} (hC : 0 ≤ C) (hα₂ : α₂ ≤ 1)
    (hS : T3Slot C) (hD : SlotDomIP α₂ K IP) :
    Work.FTS.VocabO.T3Clause IP α₂ (K * 75 * C) := by
  obtain ⟨hKpos, hD⟩ := hD
  intro α hα f g hsf hwf hcf hreg hm5 hdec
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂
  set u : Fn := fun z θ => f z θ * Work.Spaces.Dz g z θ with hu_def
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    hsf.mul (Work.FTS.EllipticEst.SmoothOpen.Dz (smoothOpen_of_smoothQuad_aux hreg.1))
  have hv : Work.FTS.EllipticEst.SmoothOpen g := smoothOpen_of_smoothQuad_aux hreg.1
  have hmain := hD α hα u g hu hv
  have hR : 0 ≤ C * α ^ (-(1 / 2 : ℝ))
      * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hα.1.le _))
      (add_nonneg (Work.FTS.H2.WPQ.WlInf_nonneg' hwf) (coefTh_nonneg 3 f))) (sq_nonneg _)
  have hslot : ∀ (a b : ℕ), a + b ≤ 4 → ∀ ρ : ℝ → ℝ → ℝ, IsLeafW α a ρ →
      |slotPairing ρ a b u g| ≤ C * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
    fun a b hab ρ hρ => hS α f g hαpos hα1 ⟨hsf, hwf, hcf⟩ ⟨hreg, hm5, hdec⟩ a b ρ hab hρ
  have hsum : leafSum α u g ≤ 75 * (C * α ^ (-(1 / 2 : ℝ))
      * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
      * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine leafSum_le α u g _ hR ?_
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
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2)) := mul_le_mul_of_nonneg_left hsum hKpos.le
    _ = (K * 75 * C) * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 f + Work.FTS.VocabO.CoefTh 3 f)
          * Work.FTS.Nonlin.Xn α g ^ 2 := by ring

/-- `SlotDomIP` is monotone in the range of `α`. -/
theorem SlotDomIP_mono {α₂ α₂' K : ℝ} (h : α₂' ≤ α₂) {IP : ℝ → Fn → Fn → ℝ}
    (hD : SlotDomIP α₂ K IP) : SlotDomIP α₂' K IP :=
  ⟨hD.1, fun α hα => hD.2 α ⟨hα.1, le_trans hα.2 h⟩⟩

/-- **The `t2` clause for the concrete coercive inner product `IP4`**, from the per-slot
transport bound `T2Slot` (delegated as `t2SlotGuarded`) and the proved slot domination
`ip4SlotDomFixed`.  This is the shape of `Work.FTS.Nonlin.N4Extra`'s `t2` clause with the
design's new coefficient hypotheses. -/
theorem T2Clause_IP4 {C : ℝ} (hC : 0 < C) (hS : T2Slot C) :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      Work.FTS.VocabO.T2Clause (fun α => Work.FTS.CoercivityStep.IP4 α) α₂ Ct := by
  obtain ⟨K, α₂, hK, hα₂, hD⟩ := ip4SlotDomFixed
  refine ⟨K * 75 * C, min α₂ 1, by positivity, lt_min hα₂ one_pos, ?_⟩
  refine T2Clause_of_slot hC.le (min_le_right _ _) hS ?_
  exact SlotDomIP_mono (min_le_left _ _) hD

/-- **The `t3` clause for the concrete coercive inner product `IP4`**, from the per-slot
transport bound `T3Slot` (delegated as `t3SlotGuarded`). -/
theorem T3Clause_IP4 {C : ℝ} (hC : 0 < C) (hS : T3Slot C) :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      Work.FTS.VocabO.T3Clause (fun α => Work.FTS.CoercivityStep.IP4 α) α₂ Ct := by
  obtain ⟨K, α₂, hK, hα₂, hD⟩ := ip4SlotDomFixed
  refine ⟨K * 75 * C, min α₂ 1, by positivity, lt_min hα₂ one_pos, ?_⟩
  refine T3Clause_of_slot hC.le (min_le_right _ _) hS ?_
  exact SlotDomIP_mono (min_le_left _ _) hD

end Work.FTS.TransportS
