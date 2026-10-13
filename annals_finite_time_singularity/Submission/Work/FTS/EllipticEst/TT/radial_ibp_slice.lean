import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.radialPairIBP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory

/-- **Radial integration by parts on a single angular slice.**

For `G` smooth on the open quadrant, vanishing for `z ∉ [A,B]` (`0 < A < B`) and for
`θ ∉ [c,d]` (`0 < c`, `d < π/2`), and for `θ ∈ Iθ`, the radial pairing
`∫_z (D_zG)(D_z∂_θ²G) w²` equals `-∫_z (D_z²G + b D_zG)(∂_θ²G) w²`, `b z = (z-3)/(1+z)`.

This is the compactly supported radial integration by parts
`Work.EllipticEst.Core.radialPairIBP` applied to the two `z`-slices
`φ = z ↦ G z θ` and `ψ = z ↦ ∂_θ²G z θ`: at an interior angle `θ` both slices are
`C^∞` on `(0,∞)` by `SmoothOpen.curry_z`, while for `θ = 0` or `θ = π/2` the hypothesis
`hθsupp` forces `G z θ = 0` and both sides of the identity vanish.  The support condition
needed for `ψ` is `hZsupp`: off `[A,B]` the whole `θ`-slice of `G` is zero, hence so are all
its `θ`-derivatives. -/
theorem radial_ibp_slice {G : ℝ → ℝ → ℝ} {A B c d θ : ℝ} (hA : 0 < A) (hAB : A < B)
    (hc : 0 < c) (hd : d < Real.pi / 2)
    (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hZsupp : ∀ z : ℝ, z ∉ Set.Icc A B → ∀ θ : ℝ, G z θ = 0)
    (hθsupp : ∀ z θ : ℝ, θ ∉ Set.Icc c d → G z θ = 0)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
        * (Work.Spaces.w z) ^ 2)
      = - ∫ z in Work.Spaces.Iz,
          (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + Work.FTS.EllipticEst.TT.bcoef z
            * Work.Spaces.Dz G z θ) * Work.Spaces.pthIter 2 G z θ * (Work.Spaces.w z) ^ 2 := by
  by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · -- ## Interior angle: apply the compactly supported radial integration by parts
    have hφ : ContDiffOn ℝ 2 (fun z : ℝ => G z θ) (Set.Ioi 0) :=
      (hG.curry_z hθi).of_le (by simp [Work.Stability.smoothOrder])
    have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 G) := by
      have h := hG.pth.pth
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
    have hψ : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
      (hpth2.curry_z hθi).of_le (by simp [Work.Stability.smoothOrder])
    have hφs : ∀ z : ℝ, z ∉ Set.Icc A B → (fun z : ℝ => G z θ) z = 0 :=
      fun z hz => hZsupp z hz θ
    have hψs : ∀ z : ℝ, z ∉ Set.Icc A B →
        (fun z : ℝ => Work.Spaces.pthIter 2 G z θ) z = 0 := by
      intro z hz
      -- off `[A,B]` the whole `θ`-slice of `G` is zero, hence so are all its `θ`-derivatives
      have h1 : ∀ θ' : ℝ, Work.Spaces.pth G z θ' = 0 := by
        intro θ'
        have hc0 : (fun θ'' : ℝ => G z θ'') = fun _ : ℝ => (0 : ℝ) :=
          funext (fun θ'' => hZsupp z hz θ'')
        show deriv (fun θ'' : ℝ => G z θ'') θ' = 0
        rw [hc0, deriv_const]
      have h2 : ∀ θ' : ℝ, Work.Spaces.pthIter 2 G z θ' = 0 := by
        intro θ'
        have hc0 : (fun θ'' : ℝ => Work.Spaces.pth G z θ'') = fun _ : ℝ => (0 : ℝ) :=
          funext h1
        show deriv (fun θ'' : ℝ => Work.Spaces.pth G z θ'') θ' = 0
        rw [hc0, deriv_const]
      exact h2 θ
    have key := Work.EllipticEst.Core.radialPairIBP hA hAB
      (fun z : ℝ => G z θ) (fun z : ℝ => Work.Spaces.pthIter 2 G z θ) hφ hψ hφs hψs
    -- ## Identify the two integrands with those of `radialPairIBP`
    have hL : (∫ z in Work.Spaces.Iz, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (z * deriv (fun z : ℝ => G z θ) z)
            * (z * deriv (fun z : ℝ => Work.Spaces.pthIter 2 G z θ) z) := by
      refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz)
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z _ => ?_)
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      ring
    have hR : (∫ z in Work.Spaces.Iz, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.TT.bcoef z * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (z * deriv (fun y : ℝ => y * deriv (fun z : ℝ => G z θ) y) z
                + (z - 3) / (1 + z) * (z * deriv (fun z : ℝ => G z θ) z))
            * (fun z : ℝ => Work.Spaces.pthIter 2 G z θ) z := by
      refine MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iz)
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z _ => ?_)
      simp only [Work.FTS.EllipticEst.TT.bcoef, Work.Spaces.Dz, Work.Spaces.pz]
      ring
    rw [hL, hR]
    exact key
  · -- ## Endpoint angle `θ = 0` or `θ = π/2`: both sides vanish
    have hθ0 : θ = 0 ∨ θ = Real.pi / 2 := by
      obtain ⟨h0, h1⟩ := Set.mem_Icc.mp (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ)
      rw [Set.mem_Ioo] at hθi
      by_cases hz : θ ≤ 0
      · exact Or.inl (le_antisymm hz h0)
      · refine Or.inr (le_antisymm h1 ?_)
        exact not_lt.mp (fun hcon => hθi ⟨not_le.mp hz, hcon⟩)
    -- `hθsupp` makes the whole `z`-slice of `G` vanish at such an angle
    have hzero : ∀ z : ℝ, G z θ = 0 := by
      rcases hθ0 with hθz | hθp
      · intro z
        rw [hθz]
        exact hθsupp z 0 (fun hmem => absurd (Set.mem_Icc.mp hmem).1 (not_le.mpr hc))
      · intro z
        rw [hθp]
        exact hθsupp z (Real.pi / 2)
          (fun hmem => absurd (Set.mem_Icc.mp hmem).2 (not_le.mpr hd))
    have hDzG : ∀ z : ℝ, Work.Spaces.Dz G z θ = 0 := by
      intro z
      have hc0 : (fun z' : ℝ => G z' θ) = fun _ : ℝ => (0 : ℝ) := funext hzero
      show z * deriv (fun z' : ℝ => G z' θ) z = 0
      rw [hc0, deriv_const, mul_zero]
    have hDz2G : ∀ z : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) z θ = 0 := by
      intro z
      have hc0 : (fun z' : ℝ => Work.Spaces.Dz G z' θ) = fun _ : ℝ => (0 : ℝ) := funext hDzG
      show z * deriv (fun z' : ℝ => Work.Spaces.Dz G z' θ) z = 0
      rw [hc0, deriv_const, mul_zero]
    have hL0 : (∫ z in Work.Spaces.Iz, Work.Spaces.Dz G z θ
        * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ * (Work.Spaces.w z) ^ 2) = 0 := by
      rw [show (fun z : ℝ => Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ * (Work.Spaces.w z) ^ 2)
          = fun _ : ℝ => (0 : ℝ) from funext (fun z => by rw [hDzG z]; ring)]
      simp
    have hR0 : (∫ z in Work.Spaces.Iz, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + Work.FTS.EllipticEst.TT.bcoef z * Work.Spaces.Dz G z θ)
        * Work.Spaces.pthIter 2 G z θ * (Work.Spaces.w z) ^ 2) = 0 := by
      rw [show (fun z : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.TT.bcoef z * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ * (Work.Spaces.w z) ^ 2)
          = fun _ : ℝ => (0 : ℝ) from
            funext (fun z => by rw [hDz2G z, hDzG z]; ring)]
      simp
    rw [hL0, hR0]
    ring

end Work.FTS.EllipticEst.TT
