import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.MollifyBound
import Submission.Work.MRMT.Found.ExistsContDiffAux
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.inverse_limit
import Submission.Work.MRMT.Found.records_agree
import Submission.Work.MRMT.Found.record_dev_energy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-- Existence of a `PrincipalData μ` whose approximating coefficients satisfy the *prescribed*
bound `‖μn n‖ ≤ k` (the bound assumed on `μ` itself), for `0 ≤ k < 1`.  This is
`Work.MRMT.Found.principalData_exists` with the mollification replaced by
`mollify_admissible_of_bound`, which keeps the given constant `k`. -/
theorem principalData_exists_bounded {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ d : Work.MRMT.Found.PrincipalData μ, ∀ n z, ‖d.μn n z‖ ≤ k := by
  classical
  open Work.MRMT.Found in
  obtain ⟨M, μn, hM0, hμsupp, hμnC, hμnS, hμnB, hμnSp, hμnT⟩ :=
    Work.MRMT.Found.mollify_admissible_of_bound hμ hk0 hk1 hb
  open Work.MRMT.Found in
  choose F hFC hFCS hFB hFD using fun n =>
    Work.MRMT.Found.exists_contDiff_principal_of_contDiff_ec (hμnC n) (hμnS n) hk1 (hμnB n)
  open Work.MRMT.Found in
  obtain ⟨φ, D, Cd, Rd, hφc, hφconv, hφdec, hFdec, hDtend⟩ :=
    Work.MRMT.Found.forward_limit_pd hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hμnT hb hFC hFCS hFB hFD
  -- enlarge the decay constants so that they are non-negative / at least one
  have hCd' : 0 ≤ max Cd 0 := le_max_right _ _
  have hRd' : 1 ≤ max Rd 1 := le_max_right _ _
  have hFdec' : ∀ n : ℕ, ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖F n z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro n z hz
    exact (hFdec n z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hφdec' : ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖φ z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro z hz
    exact (hφdec z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  -- the inverse limit
  obtain ⟨ψ, hψc, hψconv, hφψ, hψφ⟩ :=
    Work.MRMT.Found.inverse_limit hk0 hk1 hM0 hCd' hRd' hμnB hμnSp hFC hFCS hFB hFdec' hφconv
  -- assemble the homeomorphism
  let Φ : ℂ ≃ₜ ℂ :=
    { toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      continuous_toFun := hφc
      continuous_invFun := hψc }
  open Work.MRMT.Found in
  exact ⟨{
    φ := Φ
    C := max Cd 0
    R := max Rd 1
    decay := hφdec'
    k := k
    hk := hk1
    μn := μn
    contDiff_μn := fun n => (hμnC n).of_le (by simp)
    compactSupport_μn := hμnS
    norm_μn := hμnB
    tendsto_μn := hμnT
    Fn := F
    contDiff_Fn := hFC
    contDiff_symm_Fn := hFCS
    beltrami_Fn := hFB
    tendsto_Fn := hφconv
    tendsto_symm_Fn := hψconv
    dz_tendsto := ⟨D, hDtend⟩ }, fun n z => hμnB n z⟩

end Work.Found
