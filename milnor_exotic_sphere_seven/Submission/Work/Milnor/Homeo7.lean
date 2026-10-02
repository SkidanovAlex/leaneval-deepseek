import Mathlib
import Submission.Work.Milnor.MkCharted
import Submission.Work.Milnor.morseFun
import Submission.Work.Milnor.morseFun_crit
import Submission.Work.Morse.reeb
import Submission.Work.Morse.hasMorseThru_of_hasNondegHessian
import Submission.Work.Morse.isCritPoint_of_hasMorseThru

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Mk (-2)` is homeomorphic to `S⁷`

Part (A) of Milnor's theorem: the explicit two-critical-point Morse function
(`Work.Milnor.morseFun`, verified Morse in `Work.Milnor.morseFun_crit`) together with Reeb's theorem
(`Work.Morse.reeb`) gives `Mk (-2) ≃ₜ S⁷`.

The Morse function is constructed in the product charted structure (`ℝ⁴ × ℝ³`); here we use the
explicit `ℝ⁷` charted structure `Work.Milnor.mkChartedSpace` and the transfer lemmas of
`Submission.Work.Milnor.MkCharted` to move smoothness, critical points and nondegenerate Hessians
across, and the bridges `Work.Morse.hasMorseThru_of_hasNondegHessian` (the Morse lemma) and
`Work.Morse.isCritPoint_of_hasMorseThru` to match the hypotheses of `Work.Morse.reeb`.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Metric (sphere)
open Submission.Milnor

noncomputable section

theorem mk_minus_two_homeo :
    Nonempty (Mk (-2) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) := by
  obtain ⟨F, hFsm, hFX, hFY⟩ := morseFun
  obtain ⟨hcrit, p, q, hpq, hp, hq, huniq⟩ := morseFun_crit F hFX hFY
  -- use the explicit `ℝ⁷` charted structure on `Mk (-2)`
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 7)) (Mk (-2)) := mkChartedSpace (-2)
  letI : IsManifold (𝓡 7) ∞ (Mk (-2)) := mk_isManifold (-2)
  -- smoothness transfers
  have hFsm' : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ F := (mk_contMDiff_iff (-2)).mpr hFsm
  -- critical points and nondegenerate Hessians transfer
  have hcrit' : ∀ x : Mk (-2), mfderiv (𝓡 7) 𝓘(ℝ, ℝ) F x = 0 →
      HasNondegHessian (I := 𝓡 7) (n := ∞) F x := by
    intro x hx
    exact mk_hasNondegHessian (-2) (hcrit x ((mk_mfderiv_eq_zero_iff (-2)).mp hx))
  -- the Morse-lemma bridge
  have hMorse : ∀ x : Mk (-2), mfderiv (𝓡 7) 𝓘(ℝ, ℝ) F x = 0 →
      HasMorseThru (n := 7) F x :=
    fun x hx => Work.Morse.hasMorseThru_of_hasNondegHessian hFsm' (hcrit' x hx)
  have hpM : HasMorseThru (n := 7) F p :=
    hMorse p ((mk_mfderiv_eq_zero_iff (-2)).mpr hp)
  have hqM : HasMorseThru (n := 7) F q :=
    hMorse q ((mk_mfderiv_eq_zero_iff (-2)).mpr hq)
  have huniq' : ∀ x : Mk (-2), HasMorseThru (n := 7) F x → x = p ∨ x = q :=
    fun x hx => huniq x ((mk_mfderiv_eq_zero_iff (-2)).mp
      (Work.Morse.isCritPoint_of_hasMorseThru hx))
  obtain ⟨e⟩ := Work.Morse.reeb (n := 7) (M := Mk (-2)) (by norm_num) hFsm'
    ⟨p, q, hpq, hMorse, hpM, hqM, huniq'⟩
  exact ⟨e⟩

end

end Work.Milnor
