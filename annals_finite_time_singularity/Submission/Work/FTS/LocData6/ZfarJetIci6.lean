/-
# `Work.FTS.LocData6.ZfarJetIci6` — the order-`6` jet bound of `zfarR L` on `[L,∞)`, and its
unconditional form

`zfarR L = (1 - χ(·/L))·FM.Fstar` agrees with `FM.Fstar` beyond `2L` (`zfarR_eq_FM_Fstar_of_ge`)
and is covered by the Leibniz bound of `LocData6.zfarR_jet_le6_of_jets` on `[L, 2L]`.  This
module glues the two (the order-`6` instance of `Work.FTS.LocDataExt.zfarR_jet_le5_Ici`) and
instantiates the three order-`6` jet inputs

* `LocData6.oneSubChi_jet_le6` (cut-off),
* `LocData6.FM_Fstar_jet_le6` (profile),
* `LocData6.zfarR_jet_le6_of_jets` (Leibniz),

into the unconditional `LocData6.zfarR_jet_le6_clean`:  there is `A > 0` with
`|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, `j ≤ 6`, `z ≥ L` and `θ`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData6.oneSubChi_jet_le6
import Submission.Work.FTS.LocData6.FM_Fstar_jet_le6
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `D_z`-jets of `zfarR L` decay like `1/z` on all of `[L,∞)`**: on `[L,2L]` from the
Leibniz bound `hAz`, beyond `2L` from the jets of `FM.Fstar` (with which `zfarR L` agrees
there). -/
theorem zfarR_jet_le6_Ici (L : ℝ) (hL : 1 ≤ L) {A CF : ℝ} (hA : 0 ≤ A) (hCF : 0 ≤ CF)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Icc L (2 * L), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hF : ∀ j ≤ 6, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ max A CF / z := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j hj z hz θ
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hz
  by_cases h : z ≤ 2 * L
  · have h1 := hAz j hj z ⟨hz, h⟩ θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_left A CF) (le_of_lt hzpos)
  · push_neg at h
    have hev : ∀ᶠ z' in 𝓝 z, Work.FTS.LocDataExt.zfarR L z' = Work.FM.Fstar z' := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds h] with z' hz'
      exact Work.FTS.LocDataExt.zfarR_eq_FM_Fstar_of_ge hLpos (le_of_lt hz')
    rw [Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq
      (σ := fun z => Work.FM.Fstar z) hev j θ]
    have h1 := hF j hj z (by linarith) θ
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (le_max_right A CF) (le_of_lt hzpos)

/-- **The unconditional order-`6` jet bound of the far factor**: there is `A > 0` such that
`|D_z^j (zfarR L) z| ≤ A/z` for every `L ≥ 1`, every `j ≤ 6`, every `z ≥ L` and every `θ`. -/
theorem zfarR_jet_le6_clean :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 1 ≤ L → ∀ j : ℕ, j ≤ 6 →
      ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z := by
  obtain ⟨Cu, hCu1, hCu⟩ := oneSubChi_jet_le6
  obtain ⟨Cv, hCvpos, hCvle⟩ := FM_Fstar_jet_le6
  have hIcc := zfarR_jet_le6_of_jets hCu1 hCvpos hCu hCvle
  refine ⟨max (64 * Cu * Cv) Cv, by positivity, fun L hL j hj z hz θ => ?_⟩
  exact zfarR_jet_le6_Ici L hL (by positivity) (le_of_lt hCvpos)
    (fun j hj z hz θ => hIcc L hL j hj z hz θ)
    (fun j hj z hz θ => hCvle j hj z hz θ) j hj z hz θ

end Work.FTS.LocData6
