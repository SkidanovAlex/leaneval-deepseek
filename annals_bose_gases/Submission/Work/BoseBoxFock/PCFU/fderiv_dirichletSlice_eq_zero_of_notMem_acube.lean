import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Fourier.peel_slot_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem fderiv_dirichletSlice_eq_zero_of_notMem_acube {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∉ Submission.BoseGases.acube ℓ)
    (r : Submission.BoseGases.X n) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r))) y = 0 := by
  -- `χ_ℓ` is supported in the centred cube, and `acube ℓ` is closed, so `χ_ℓ` vanishes on the
  -- (open) complement of `acube ℓ`, a neighbourhood of `y`.
  have hclosed : IsClosed (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_isClosed ℓ
  have hzero : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ Submission.BoseGases.acube ℓ → Submission.BoseGases.chiScale ℓ z = 0 :=
    fun z hz => not_ne_iff.mp (fun h => hz (Submission.BoseGases.chiScale_mem_acube hℓ h))
  have hev : (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ z * Φ (Submission.BoseGases.kcInsN n i (z, r)))
      =ᶠ[nhds y] (fun _ => (0 : ℝ)) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hy] with z hz
    rw [hzero z hz, zero_mul]
  rw [hev.fderiv_eq]
  simp

end Work.BoseBoxFock.PCFU
