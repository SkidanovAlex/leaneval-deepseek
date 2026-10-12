import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.box_inv_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.momForm_eq_of_lamBox_eq` — `momForm` only sees the state on the box

FS `eq:DefT`'s third kinetic piece is the momentum form of the *windowed* mean-free state

    `momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹,∞)}(‖p‖)·‖kinFT (θ_u·Q_uψ)‖²`,

with `θ_u = indU ℓ u = 1_{Λ(u)}` the indicator of the sliding box `Λ(u) = lamBox ℓ u` and
`Q_uψ = Qfree ℓ u ψ = ψ − m_u(ψ)`.

The state `θ_u·Q_uψ` is a functional of the restriction of `ψ` to `Λ(u)`: outside the box the
indicator vanishes, and the box mean `m_u(ψ) = bsMean ℓ u ψ` is an integral over `Λ(u)`
(`Sector.bsMean_eq_of_lamBox_eq`).  Hence `ψ = ψ'` on `Λ(u)` forces `θ_u·Q_uψ = θ_u·Q_uψ'`
pointwise, and then the Fourier transforms, their norms, and the `p`-integrals coincide.
-/

namespace Work.BoseKinLoc.Sector

open Work.BoseKinLoc Work.BSKinetic

theorem momForm_eq_of_lamBox_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ Work.BoseKinLoc.lamBox ℓ u → ψ z = ψ' z) :
    Work.BoseKinLoc.momForm ℓ d u ψ = Work.BoseKinLoc.momForm ℓ d u ψ' := by
  -- the mean-free states agree on the box
  have hQ : ∀ z : ℝ³, z ∈ lamBox ℓ u → Qfree ℓ u ψ z = Qfree ℓ u ψ' z :=
    Qfree_eq_of_lamBox_eq hℓ u h
  -- hence the *windowed* mean-free states agree everywhere (outside the box both vanish)
  have hstat : (fun z : ℝ³ => ((indU ℓ u z : ℝ) : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ))
      = (fun z : ℝ³ => ((indU ℓ u z : ℝ) : ℂ) * ((Qfree ℓ u ψ' z : ℝ) : ℂ)) := by
    funext z
    by_cases hz : z ∈ lamBox ℓ u
    · have : (Qfree ℓ u ψ z : ℂ) = (Qfree ℓ u ψ' z : ℂ) := by rw [hQ z hz]
      rw [this]
    · have h0 : indU ℓ u z = 0 := by
        simp only [indU]
        exact Set.indicator_of_notMem hz _
      rw [h0]
      simp
  unfold momForm
  rw [hstat]

end Work.BoseKinLoc.Sector
