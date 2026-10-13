/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/Final`: the per-slot transport bound `T2Slot` from the weighted estimate

The per-slot bound `T2Slot` (the frozen statement of `Slots.lean`) quantifies over the three
*leaf weights* of the coercive pairing `IP4`: `leafEta = w² sin(2θ)^{-η}`, `leafOne = w²` and
`leafGam α = w² sin(2θ)^{-γ}` (the last only for slots with `a ≥ 1`, `IsLeafW α a ρ`).  Each of
them is the canonical weight `canonW q` of `SlotT2.Basic` for `q ∈ {η, 0, γ}`, and the weighted
estimate `SlotAbsProp` (proved in `T2Sup/slotAbsBound.lean`) already covers all three exponents,
because it is stated for every `0 ≤ q` with `q ≤ η` at the pure `D_z`-slots and `q ≤ γ` at the
mixed ones.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.Ptwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- The weighted per-slot estimate: the statement proved in `T2Sup/slotAbsBound.lean`. -/
def SlotAbsProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ),
    0 < α → α ≤ 1 → Work.FTS.TransportS.T2SF α f → Work.FTS.TransportS.T2SG α g →
    a + b ≤ 4 → 0 ≤ q →
    (a = 0 → q ≤ Work.Spaces.eta) → q ≤ Work.Spaces.gam α →
    (q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ
          * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          * Work.Spaces.mixed b a g z θ|
      ≤ C * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.FTS.Nonlin.Xn α g ^ 2

/-- The three leaf weights are the canonical weights `canonW η`, `canonW 0` and `canonW γ`. -/
theorem leafWeight_eq_canon : (Work.FTS.TransportS.leafEta = canonW Work.Spaces.eta) ∧
    (Work.FTS.TransportS.leafOne = canonW 0) ∧
    (∀ α : ℝ, Work.FTS.TransportS.leafGam α = canonW (Work.Spaces.gam α)) := by
  refine ⟨rfl, ?_, fun α => rfl⟩
  funext z θ
  simp only [Work.FTS.TransportS.leafOne, canonW, neg_zero, Real.rpow_zero, mul_one]

/-- **`T2Slot` from the weighted estimate.**  Each leaf weight of a slot `(a,b)` is one of the
canonical weights, so the weighted estimate applies verbatim. -/
theorem T2Slot_of_slotAbs (h : SlotAbsProp) : ∃ C : ℝ, 0 < C ∧ Work.FTS.TransportS.T2Slot C := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro α f g hα hα1 hsf hsg a b ρ hab hleaf
  rcases hleaf with hρ | hρ | ⟨ha, hρ⟩
  · -- `ρ = leafEta = canonW η`
    have hρ' : ρ = canonW Work.Spaces.eta := by rw [hρ]; exact leafWeight_eq_canon.1
    rw [Work.FTS.TransportS.slotPairing, hρ']
    exact hb α f g a b Work.Spaces.eta hα hα1 hsf hsg hab Work.Spaces.eta_pos.le
      (fun _ => le_rfl) (eta_le_gam hα) (Or.inl le_rfl)
  · -- `ρ = leafOne = canonW 0`
    have hρ' : ρ = canonW 0 := by rw [hρ]; exact leafWeight_eq_canon.2.1
    rw [Work.FTS.TransportS.slotPairing, hρ']
    exact hb α f g a b 0 hα hα1 hsf hsg hab le_rfl
      (fun _ => Work.Spaces.eta_pos.le) (le_of_lt (Work.Spaces.gam_pos hα))
      (Or.inl Work.Spaces.eta_pos.le)
  · -- `ρ = leafGam α = canonW γ`, only at slots with `a ≥ 1`
    have hρ' : ρ = canonW (Work.Spaces.gam α) := by rw [hρ]; exact leafWeight_eq_canon.2.2 α
    rw [Work.FTS.TransportS.slotPairing, hρ']
    exact hb α f g a b (Work.Spaces.gam α) hα hα1 hsf hsg hab
      (le_of_lt (Work.Spaces.gam_pos hα))
      (fun h0 => absurd h0 (by omega)) le_rfl (Or.inr rfl)

end Work.FTS.TransportS.T2Sup
