import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.E5G5.DthIter_intervalIntegral_eq_gen
import Submission.Work.FTS.StrongEps.E5G5.DzIter_intervalIntegral_eq_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G5

/-- **Exchange of `mixed j i` (`j + i ≤ n`) with the interval integral.**

This is the order-unrestricted version of `Work.FTS.StrongEps.mixed_intervalIntegral_eq` (which
is the case `n = 4`): for a family `s ↦ H s` of functions smooth on the open quadrant `Q0`,
uniformly bounded in every slot of order `≤ n` on a closed box `⊆ Q0`, and with every slot
a.e.-strongly-measurable in `s`, the iterated derivatives `D_z^j D_θ^i` (for `j + i ≤ n`) of the
interval integral `∫_a^b H s z θ ds` are the interval integrals of the iterated derivatives.

The two inductions behind it (`DthIter_intervalIntegral_eq_gen` in the angular direction and
`DzIter_intervalIntegral_eq_gen` in the radial one) are the order-`n` versions of the
corresponding lemmas of `EpsSlotAux`; the same parametric differentiation
(`hasDerivAt_intervalIntegral_of_deriv_le`) supplies each single step. -/
theorem mixed_intervalIntegral_eq_gen {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  have hbox_open : IsOpen (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo
  intro z θ hzθ
  have hA := DthIter_intervalIntegral_eq_gen (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ
    (l := i) (by omega)
  have hB := DzIter_intervalIntegral_eq_gen (H := H) haT hbT hab hC hsm hmeas hbdd hboxQ
    j i hji z θ hzθ
  have hA' : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)))
      (Function.uncurry (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ))
      (Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂) := fun p hp => hA p.1 p.2 hp
  have hloc := DzIter_congr_of_isOpen hbox_open hA' j hzθ
  simp only [Function.uncurry] at hloc
  calc Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => ∫ s in a..b, H s z θ)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∫ s in a..b, Work.Spaces.DthIter i (H s) z θ) z θ := hloc
    _ = ∫ s in a..b, Work.Spaces.DzIter j (Work.Spaces.DthIter i (H s)) z θ := hB
    _ = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := rfl

end Work.FTS.StrongEps.E5G5
