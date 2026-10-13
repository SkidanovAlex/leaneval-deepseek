import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open MeasureTheory Set

set_option maxHeartbeats 1600000

/-! ## The `canonW`-weighted slot shift

The requested lemma is the "slot shift": a leaf weight `ρ` attached to the slot of order `a`
(the three leaves being `leafEta = w²sin(2θ)^{-η}`, `leafOne = w²` and, for `a ≥ 1`,
`leafGam α = w²sin(2θ)^{-γ}`) prices *any* higher slot `(a', j)` with `a ≤ a'` and
`a' + j ≤ 6`, with the same bound `C·HkSq α 6 f`.

Pointwise, every leaf weight of the slot of order `a ≤ a'` is dominated by `canonW q` for an
exponent `q` admissible at the higher slot `(a', j)` (namely `q ∈ {η, 0, γ}`, and the `γ`-leaf
necessarily comes with `a ≥ 1`, hence `a' ≥ 1`), and the level-six slot estimates
`T1SixAux.slotSliceIntegrable` / `T1SixAux.slotEnergyZOuter` give exactly the three conjuncts
of the target. -/

/-- **The slot shift at the level-six canonical weight.**  For an `ℋ⁶`-datum `f` and
`a' + j ≤ 6`, the `canonW q`-weighted square of the slot `D_z^jD_θ^{a'}f` is slice-integrable,
has integrable radial marginal, and the iterated integral is at most `C·HkSq α 6 f`, provided
the exponent `q` is admissible: `0 ≤ q ≤ γ`, and `q ≤ η` in the pure case `a' = 0`. -/
private theorem canonW_slotShift {C α q : ℝ} {f : ℝ → ℝ → ℝ} {a' j : ℕ} (hC : 1 ≤ C)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 6 f)
    (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a' = 0 → q ≤ Work.Spaces.eta)
    (haj : a' + j ≤ 6) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      Work.Spaces.Iz ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      Work.Spaces.Iθ) ∧
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
      ≤ C * Work.Spaces.HkSq α 6 f := by
  have hE := Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter α q hsm hm hq0 hqγ hqη
    (a := a') (b := j) haj
  refine ⟨hE.1, fun z hz => ?_, ?_⟩
  · exact Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hsm hm
      hqγ hqη (a := a') (b := j) haj hz
  · have hSq : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f := hE.2
      _ = 1 * Work.Spaces.HkSq α 6 f := (one_mul _).symm
      _ ≤ C * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_right hC hSq

/-- `leafEta = w²sin(2θ)^{-η}` is the canonical weight `canonW η` (definitionally). -/
private theorem leafEta_eq_canonW_eta :
    Work.FTS.TransportS.leafEta = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta := rfl

/-- `leafGam α = w²sin(2θ)^{-γ}` is the canonical weight `canonW γ` (definitionally). -/
private theorem leafGam_eq_canonW_gam (α : ℝ) :
    Work.FTS.TransportS.leafGam α
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl

/-- `leafOne = w²` is the canonical weight `canonW 0`. -/
private theorem leafOne_eq_canonW_zero :
    Work.FTS.TransportS.leafOne = Work.FTS.TransportS.SlotT2.canonW 0 := by
  funext z θ
  simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
    Real.rpow_zero, mul_one]

theorem fkSlotShift : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a a' j : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.TransportS.IsLeafW α a ρ → a ≤ a' → a' + j ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2)
          Work.Spaces.Iz ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
          (fun θ => ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) Work.Spaces.Iθ) ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed j a' f z θ) ^ 2) ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f a a' j ρ hsm hm hρ haa haj
  have h0eta : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  have h0gam : (0 : ℝ) ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  have hetagam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.1]
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = leafEta = canonW η`
    rw [hρ, leafEta_eq_canonW_eta]
    exact canonW_slotShift le_rfl hsm hm h0eta hetagam (fun _ => le_rfl) haj
  · -- `ρ = leafOne = canonW 0`
    rw [hρ, leafOne_eq_canonW_zero]
    exact canonW_slotShift le_rfl hsm hm le_rfl h0gam (fun _ => h0eta) haj
  · -- `ρ = leafGam α = canonW γ`, and `1 ≤ a ≤ a'`
    rw [hρ, leafGam_eq_canonW_gam]
    exact canonW_slotShift le_rfl hsm hm h0gam le_rfl
      (fun h => absurd h (by omega)) haj

end Work.FTS.StrongPersist.H6Row6
