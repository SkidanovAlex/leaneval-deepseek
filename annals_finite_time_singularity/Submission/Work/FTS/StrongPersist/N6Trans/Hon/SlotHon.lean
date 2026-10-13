/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/SlotHon`: the honest per-slot transport bound `T2SlotHon`

The honest (`SmoothOpen`-based) form of `TransportS.T2Slot`: for every slot `(a,b)` with
`a + b ≤ 4` of the unfolding of `IP4` and every *leaf* weight `ρ` of `H1IP`, the pairing
`slotPairing ρ a b (f·D_z g) g` is bounded by `C·α^{-1/2}(|f|_{ℋ⁴} + CoefTh 1 f)|g|²_{ℋ⁴}`.

It is deduced from the honest per-slot engine `slotAbsBound_hon` (`Hon/SlotAbsHon`) exactly as
the frozen `T2Slot` is deduced from `T2Sup.slotAbsBound` (`T2Sup/Final`): each leaf weight is
one of the canonical weights `canonW η`, `canonW 0`, `canonW γ`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotAbsHon
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.Final

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
open Work.FTS.TransportS.SlotT2
open Work.FTS.TransportS.T2Sup

/-- **The honest per-slot transport bound** (the `D_z`-transport clause, one leaf at a time). -/
def T2SlotHon (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → HonF α f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → IsLeafW α a ρ →
      |slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2

/-- **`T2SlotHon` from the honest per-slot engine.** -/
theorem T2SlotHon_of_slotAbs (hTop : TopSlotHonProp) (hDel : DelicateHonProp) :
    ∃ C : ℝ, 0 < C ∧ T2SlotHon C := by
  obtain ⟨C, hC, hb⟩ := slotAbsBound_hon hTop hDel
  refine ⟨C, hC, ?_⟩
  intro α f g hα hα1 hsf hsg hmg4 hmg5 hdec a b ρ hab hleaf
  rcases hleaf with hρ | hρ | ⟨ha, hρ⟩
  · -- `ρ = leafEta = canonW η`
    have hρ' : ρ = canonW Work.Spaces.eta := by rw [hρ]; exact leafWeight_eq_canon.1
    rw [slotPairing, hρ']
    exact hb α f g a b Work.Spaces.eta hα hα1 hsf hsg hmg4 hmg5 hdec hab Work.Spaces.eta_pos.le
      (fun _ => le_rfl) (eta_le_gam hα) (Or.inl le_rfl)
  · -- `ρ = leafOne = canonW 0`
    have hρ' : ρ = canonW 0 := by rw [hρ]; exact leafWeight_eq_canon.2.1
    rw [slotPairing, hρ']
    exact hb α f g a b 0 hα hα1 hsf hsg hmg4 hmg5 hdec hab le_rfl
      (fun _ => Work.Spaces.eta_pos.le) (le_of_lt (Work.Spaces.gam_pos hα))
      (Or.inl Work.Spaces.eta_pos.le)
  · -- `ρ = leafGam α = canonW γ`, only at slots with `a ≥ 1`
    have hρ' : ρ = canonW (Work.Spaces.gam α) := by rw [hρ]; exact leafWeight_eq_canon.2.2 α
    rw [slotPairing, hρ']
    exact hb α f g a b (Work.Spaces.gam α) hα hα1 hsf hsg hmg4 hmg5 hdec hab
      (le_of_lt (Work.Spaces.gam_pos hα))
      (fun h0 => absurd h0 (by omega)) le_rfl (Or.inr rfl)

end Work.FTS.StrongPersist.N6Trans.Hon
