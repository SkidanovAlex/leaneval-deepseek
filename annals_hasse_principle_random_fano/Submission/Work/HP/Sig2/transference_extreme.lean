import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Lat.transference_exact

namespace Work.HP.Sig2

/-- Banaszczyk's transference theorem, extreme cases: for a discrete lattice `L` of rank `R` inside `ℝ^ι` with dual `dualLat L`, we have `λ_1(L)·λ_R(L*) ≤ R` and `λ_R(L)·λ_1(L*) ≤ R`.
(Browning–Le Boudec–Sawin, Lemma Banaszczyk / Banaszczyk 1993; used twice in the paper's §3.) -/
theorem transference_extreme {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (R : ℕ) (hR : Module.finrank ℤ L = R) :
    lamR L 1 * lamR (dualLat L) R ≤ (R : ℝ) ∧ lamR L R * lamR (dualLat L) 1 ≤ (R : ℝ) := by
  constructor
  · -- `λ_1(L)·λ_R(L^*) ≤ R`, the sharp Banaszczyk direction (proved in `Lat/transference_exact`).
    exact Work.HP.Lat.lamR_dual_le L R hR
  · -- The second direction is the first applied to the dual lattice, using `(L^*)^* = L`.
    haveI : DiscreteTopology (dualLat L) := Work.HP.Lat.discreteTopology_dualLat L
    have hfin : Module.finrank ℤ (dualLat L) = R := by
      rw [Work.HP.Lat.finrank_dualLat L, hR]
    have h := Work.HP.Lat.lamR_dual_le (dualLat L) R hfin
    rw [Work.HP.Lat.dualLat_dualLat L] at h
    calc lamR L R * lamR (dualLat L) 1 = lamR (dualLat L) 1 * lamR L R := mul_comm _ _
      _ ≤ (R : ℝ) := h

end Work.HP.Sig2
