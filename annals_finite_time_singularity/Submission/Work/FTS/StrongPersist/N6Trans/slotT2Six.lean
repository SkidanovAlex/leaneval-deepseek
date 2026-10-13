import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open MeasureTheory Set Filter
open scoped Real Topology

/-- The three leaf weights of `IsLeafW` are the canonical weights `canonW η`, `canonW 0 = w²` and
`canonW (gam α)` of the slot pairing. -/
theorem slotT2Six : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
        Work.FTS.VocabO.CoefThMem 1 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
        Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.HkNorm α 6 f + Work.FTS.VocabO.CoefTh 1 f)
            * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  obtain ⟨C, hC0, hmain⟩ := Work.FTS.StrongPersist.N6Trans.SixAux.main_bound
  refine ⟨C, 1, hC0, by norm_num, ?_⟩
  intro α hα f g a b ρ hfs hfm hfc hgs hgm hgm7 hgd hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hgam_ge : 1 ≤ Work.Spaces.gam α := by
    have := Work.Spaces.gam_sub_one α
    linarith [hα0.le]
  rcases hleaf with h | h | ⟨ha, h⟩
  · -- `ρ = leafEta`
    subst h
    have heq : Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
              * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
              * Work.Spaces.mixed b a g z θ := rfl
    rw [heq]
    exact hmain α f g a b Work.Spaces.eta hα0 hα1 hfs hfm hfc hgs hgm hgm7 hgd hab
      (le_of_lt Work.Spaces.eta_pos) (by linarith [Work.Spaces.eta_lt_one]) (fun _ => le_rfl)
  · -- `ρ = leafOne = canonW 0`
    subst h
    have heq : Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW 0 z θ
              * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
              * Work.Spaces.mixed b a g z θ := by
      simp only [Work.FTS.TransportS.slotPairing, Work.FTS.TransportS.leafOne,
        Work.FTS.TransportS.SlotT2.canonW, neg_zero, Real.rpow_zero, mul_one]
    rw [heq]
    exact hmain α f g a b 0 hα0 hα1 hfs hfm hfc hgs hgm hgm7 hgd hab
      le_rfl (by linarith [Work.Spaces.eta_lt_one])
      (fun _ => le_of_lt Work.Spaces.eta_pos)
  · -- `ρ = leafGam α`, which `IsLeafW` only allows for `a ≥ 1`
    subst h
    have heq : Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
              * Work.Spaces.mixed b a g z θ := rfl
    rw [heq]
    exact hmain α f g a b (Work.Spaces.gam α) hα0 hα1 hfs hfm hfc hgs hgm hgm7 hgd hab
      (by linarith) le_rfl (fun ha0 => absurd ha0 (by omega))

end Work.FTS.StrongPersist.N6Trans
