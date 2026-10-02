import Mathlib
import Submission.Work.SeedCertNum.A1Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

/-- The sup-norm ball `closedBall u₀ r` in `ℝ³` of the Krawczyk data is exactly the product of
the coordinate boxes `Xz × Xt`: this is the bridge between the analytic ball of the Krawczyk
argument and the interval-arithmetic boxes `Xz` (for `z`) and `Xt` (for `t = Im c`). -/
theorem mem_closedBall_iff (D : Work.SeedCert.KrawData) {z : ℂ} {t : ℝ} :
    (Work.SeedCert.mkE z t : Work.SeedCert.E3) ∈
        Metric.closedBall (Work.SeedCert.KrawData.u₀ D) (Work.SeedCert.KrawData.rad D) ↔
      z ∈ (Work.SeedCert.KrawData.Xz D).toSet ∧ t ∈ (Work.SeedCert.KrawData.Xt D).toSet := by
  rw [Metric.mem_closedBall]
  simp only [Prod.dist_eq, Real.dist_eq, Work.SeedCert.mkE_fst, Work.SeedCert.mkE_snd_fst,
    Work.SeedCert.mkE_snd_snd, Work.SeedCert.KrawData.u₀, Work.SeedCert.KrawData.rad,
    Work.SeedCert.KrawData.Xz, Work.SeedCert.KrawData.Xt, Work.SeedCert.CBox.toSet,
    Work.SeedCert.IV.toSet, Set.mem_ofPred_eq, Work.SeedCert.Dya.toReal_sub,
    Work.SeedCert.Dya.toReal_add]
  rw [max_le_iff, max_le_iff, abs_le, abs_le, abs_le]
  constructor
  · intro h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := h
    exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, by linarith, by linarith⟩
  · intro h
    obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end Work.SeedCertNum
