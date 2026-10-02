import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.ecalPt_deriv_eq
import Submission.Work.PARIMPL2.Direct.norm_ecalPt_deriv
import Submission.Work.PARIMPL2.Direct.taylor_second_order
import Submission.Work.PARIMPL2.Direct.logSin_hasDerivAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Second-order Taylor estimate for `log (sin (λ·))` along the segment `[u, u+δ]`.

Since `d/dz log (sin (λz)) = ecalPt (iλ) z` on the half-strip `0 < λ Re z < π`, and since
`d/dz ecalPt (iλ) z = -λ²/sin(λz)²` there with `‖d/dz ecalPt (iλ) z‖ = λ²/‖sin(λz)‖² ≤ λ²/c²`
whenever `‖sin(λz)‖ ≥ c`, the mean-value (Taylor) bound of `taylor_second_order` gives the
stated `O(‖δ‖²)` estimate for the first-order remainder. -/
theorem logSin_second_order (lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c) (u δ : ℂ)
    (hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < lam * (u + (t:ℂ) * δ).re)
    (hlt : ∀ t ∈ Set.Icc (0:ℝ) 1, lam * (u + (t:ℂ) * δ).re < Real.pi)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, c ≤ ‖Complex.sin ((lam:ℂ) * (u + (t:ℂ)*δ))‖) :
    ‖Complex.log (Complex.sin ((lam:ℂ)*(u+δ))) - Complex.log (Complex.sin ((lam:ℂ)*u))
        - δ * Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) u‖ ≤ (lam^2/c^2) * ‖δ‖^2 := by
  -- Every point of the segment is `u + t·δ` with `t ∈ [0,1]`.
  have hrep : ∀ w ∈ segment ℝ u (u + δ), ∃ t ∈ Set.Icc (0:ℝ) 1, w = u + (t:ℂ) * δ := by
    intro w hw
    rw [segment_eq_image' ℝ u (u + δ)] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    refine ⟨t, ht, ?_⟩
    simp only [Complex.real_smul]
    ring
  -- `sin (λ·)` does not vanish on the segment (its real part is positive).
  have hsin_ne : ∀ t ∈ Set.Icc (0:ℝ) 1, Complex.sin ((lam:ℂ)*(u + (t:ℂ)*δ)) ≠ 0 := by
    intro t ht
    have hre : 0 < (Complex.sin ((lam:ℂ)*(u + (t:ℂ)*δ))).re := by
      rw [inbound_sin_re]
      exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (hpos t ht) (hlt t ht)) (Real.cosh_pos _)
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  -- Hence the multiplier coordinate `e^{2iλz}` avoids `1` on the segment.
  have hE1 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      Work.Implosion.ecalE ((lam:ℂ)*Complex.I) (u + (t:ℂ)*δ) ≠ 1 := by
    intro t ht h
    have hsub : Work.Implosion.ecalE ((lam:ℂ)*Complex.I) (u + (t:ℂ)*δ) - 1 = 0 := by
      rw [h]; ring
    rw [inbound_ecalE_sub_one] at hsub
    rcases mul_eq_zero.mp hsub with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · rw [show (((lam:ℂ)*Complex.I)*(u + (t:ℂ)*δ)) = ((lam:ℂ)*(u + (t:ℂ)*δ))*Complex.I
            by ring, Complex.sinh_mul_I] at h4
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact hsin_ne t ht h5
        · exact Complex.I_ne_zero h5
    · exact Complex.exp_ne_zero _ h2
  refine taylor_second_order (fun z : ℂ => Complex.log (Complex.sin ((lam:ℂ)*z)))
      (fun z : ℂ => Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) z) u δ (lam^2/c^2) ?_ ?_ ?_
  · -- first derivative along the segment
    intro w hw
    obtain ⟨t, ht, rfl⟩ := hrep w hw
    exact logSin_hasDerivAt lam hlam _ (hpos t ht) (hlt t ht)
  · -- complex-differentiability of the derivative along the segment
    intro w hw
    obtain ⟨t, ht, rfl⟩ := hrep w hw
    exact (Work.Implosion.Ecalle.ecallePt_hasDerivAt ((lam:ℂ)*Complex.I) _
      (hE1 t ht)).differentiableAt
  · -- second derivative bound
    intro w hw
    obtain ⟨t, ht, rfl⟩ := hrep w hw
    rw [ecalPt_deriv_eq lam hlam _ (hpos t ht) (hlt t ht), norm_ecalPt_deriv]
    have hcle : c ^ 2 ≤ ‖Complex.sin ((lam:ℂ)*(u + (t:ℂ)*δ))‖ ^ 2 := by
      have h := hseg t ht
      nlinarith [h, hc, norm_nonneg (Complex.sin ((lam:ℂ)*(u + (t:ℂ)*δ)))]
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (pow_pos hc 2) hcle

end Work.PARIMPL2.Direct
