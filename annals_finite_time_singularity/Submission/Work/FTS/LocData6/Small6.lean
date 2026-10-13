/-
# `Work.FTS.LocData6.Small6` — the order-`6` smallness of the localised datum

This module discharges the two `ℋ⁶`-inputs of the far part that `LocData6.Small6Aux` carries as
hypotheses, and concludes the numerical smallness of the localised datum at order `6`:

* `HkMem_zfar_Fstar6` — `zfar L F_* ∈ ℋ⁶` for `L ≥ 1` (via the order-`6` majorant of the far
  summand, `LocData6.HkIntegrand_zfar6_le`);
* `locG6_small` — for every `ε > 0` there is `L₀` such that for every `L ≥ L₀` there is `β` with
  `|β| ≤ ε`, `L₁₂(locG α L β (hLoc α))(0) = 0` and `Xn₆(locG α L β (hLoc α)) = |·|_{ℋ⁶} ≤ ε`.

The inputs are the order-`6` radial jet bound `LocData6.zfarR_jet_le6_clean`, the angular bound
`LocData6.hGam6`, the bump majorant `LocData6.hLoc_majorant6` and the child lemma
`LocData6.HkSq_zfar_Fstar_le6` (the `α/L`-decay of `HkSq α 6` of the far part).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocData6.Small6Aux
import Submission.Work.FTS.LocData6.RegQ6
import Submission.Work.FTS.LocData6.ZfarMaj6
import Submission.Work.FTS.LocData6.ZfarJetIci6
import Submission.Work.FTS.LocData6.hLoc_majorant6
import Submission.Work.FTS.LocData6.HkSq_zfar_Fstar_le6

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

/-- **The far part `zfar L F_*` lies in `ℋ⁶`** for `L ≥ 1`, from the order-`6` jet bound of
`zfarR L` and the angular bound. -/
theorem HkMem_zfar_Fstar6 (α L : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) {A Rθ : ℝ}
    (hA : 0 ≤ A) (hRθ : 0 ≤ Rθ)
    (hAz : ∀ j ≤ 6, ∀ z ∈ Set.Ici L, ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FTS.LocDataExt.zfarR L z) z θ| ≤ A / z)
    (hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2) :
    Work.Spaces.HkMem α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) := by
  obtain ⟨K, _hK, hmaj⟩ := HkIntegrand_zfar6_le α L hα hL hA hRθ hAz hΓ
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
    intro z hz θ hθ
    have h1 : Work.Spaces.HkIntegrand α 6
        (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ) z θ
        ≤ K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2 := by
      refine le_trans (le_of_eq ?_) (hmaj z hz θ hθ)
      rw [show (fun z θ => -(Work.Stability.zfar L (Work.Construction.Fstar α)) z θ)
          = fun z θ => (-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z)
              * Work.Spaces.Gam α θ from by
        funext z' θ'
        rw [Work.FTS.LocDataExt.zfar_Fstar_eq α L]
        ring]
    rwa [Work.FTS.LocData.HkIntegrand_neg α 6
      (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ] at h1
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.Stability.zfar L (Work.Construction.Fstar α))
    (M := fun z θ => K * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 6 ?_ ?_ ?_ ?_
  · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 6 _
      (Work.FTS.LocData.SmoothQuad_zfar_Fstar α L)
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α K hα hα1).2
  · exact hmaj'

/-- **THE ORDER-`6` SMALLNESS OF THE LOCALISED DATUM.**  For every `ε > 0` there is `L₀` such
that for every `L ≥ L₀` there is a scalar `β` with `|β| ≤ ε`, `L₁₂(locG α L β (hLoc α))(0) = 0`
and `Xn₆(locG α L β (hLoc α)) ≤ ε`. -/
theorem locG6_small (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ ε > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∃ β : ℝ,
      |β| ≤ ε ∧
        Work.Construction.L12 (locG6 α L β) 0 = 0 ∧
        Xn6 α (locG6 α L β) ≤ ε := by
  intro ε hε
  obtain ⟨Kb, hKb0, hKb⟩ := hLoc_majorant6 α hα hα1
    (fun i hi θ hθ => hGam6 α hα hα1 hi hθ)
  obtain ⟨A, hA, hAz⟩ := zfarR_jet_le6_clean
  have hΓ : ∀ i ≤ 6, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ (10 : ℝ) ^ 10 * (Work.Spaces.Gam α θ) ^ 2 :=
    fun i hi θ hθ => hGam6 α hα hα1 hi hθ
  obtain ⟨Cz, _hCz0, hCz⟩ := HkSq_zfar_Fstar_le6 α hα hα1 (le_of_lt hA) (by norm_num)
    (fun L hL j hj z hz θ => hAz L hL j hj z hz θ) hΓ
  obtain ⟨L₀, hL₀⟩ := locData6_small_aux α hα hα1
    (Work.FTS.LocData.SmoothQuad_hLoc α)
    (fun z hz θ hθ => by
      rw [Real.sq_sqrt hKb0]
      exact hKb z hz θ hθ)
    (Work.FTS.LocData.L12_hLoc α hα hα1).2
    (fun L β hL => Work.FTS.LocData.L12_locG α L β hα hα1 hL)
    ⟨Cz, fun L hL => hCz L hL⟩
    (fun L hL => HkMem_zfar_Fstar6 α L hα hα1 hL (le_of_lt hA) (by norm_num)
      (fun j hj z hz θ => hAz L hL j hj z hz θ) hΓ)
    ε hε
  exact ⟨L₀, fun L hL => hL₀ L hL⟩

end Work.FTS.LocData6
