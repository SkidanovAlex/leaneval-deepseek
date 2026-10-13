import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The leaf weights of `IP6` are dominated by the slot weight of `HkIntegrand α 6`.**

For every slot `(a,b)` of the level-six pairing (`a + b ≤ 6`) and every leaf weight
`IsLeafW α a ρ` (i.e. `ρ = w²σ^{-η}`, `ρ = w²`, or `ρ = w²σ^{-γ}` with `a ≥ 1`), the
single weighted `L²` slot integral `∫_z ∫_θ ρ·(D_z^bD_θ^a f)²` is bounded by `HkSq α 6 f`.

The proof is a case distinction on the leaf weight, reducing each case to the corresponding
half of `intSlotLeHkSq` (which controls `∫∫ w²·θw·(D_z^bD_θ^a f)²` whenever `θw` is
pointwise dominated by `σ^{-η}` in the `D_z`-only slots resp. by `σ^{-γ}` in the slots with
an angular derivative).  The three elementary pointwise comparisons are

* `w²·σ^{-η} = (w z)²·σ^{-η}` (the `η`-leaf, a `D_z`-slot weight at `a = 0`);
* `w²·1 ≤ w²·σ^{-η}` when `a = 0` and `1 ≤ σ^{-γ}` when `a ≥ 1` (the σ-free leaf);
* `w²·σ^{-η} ≤ w²·σ^{-γ}` (`η ≤ γ`, `rpow_eta_le_gam`) and `w²·σ^{-γ}` exactly
  (the `γ`-leaf, which by `IsLeafW` only occurs at slots with `a ≥ 1`). -/
theorem leaf_slot_le6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 6 f) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
  intro a b ρ hab hleaf
  have h6 := intSlotLeHkSq α hmem
  have hsin_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have heta_nn : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · -- the `η`-leaf weight `w²σ^{-η}`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: compare `σ^{-η} ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafEta] using h
    · -- a `D_z`-only slot: `w²σ^{-η}` is exactly its slot weight
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 6 := by omega
      have h := h6.1 b hb (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => le_rfl)
      simpa only [Work.FTS.TransportS.leafEta, Work.Spaces.mixed_zero_right] using h
  · -- the σ-free leaf weight `w²`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: `1 ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg hgam_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one] using h
    · -- a `D_z`-only slot: `1 ≤ σ^{-η}`
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 6 := by omega
      have h := h6.1 b hb (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg heta_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one, Work.Spaces.mixed_zero_right] using h
  · -- the `γ`-leaf weight `w²σ^{-γ}`, which occurs only at slots with `a ≥ 1`
    subst hρ
    have h := h6.2 b a ha1 hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
      (fun θ hθ => le_rfl)
    simpa only [Work.FTS.TransportS.leafGam] using h

end Work.FTS.StrongPersist.H6Pair6Aux
