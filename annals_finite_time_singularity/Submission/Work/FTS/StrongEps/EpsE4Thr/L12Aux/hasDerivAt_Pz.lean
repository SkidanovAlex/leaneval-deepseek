import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular integrand of `Pz`, with the `z`-variable displayed: `(D_z^k x u θ)² sin(2θ)^{-η}`.

The angular weight `sin(2θ)^{-η}` is kept as a function of `θ` so that it can play the rôle of
the dominating weight in the parametric-integral theorem; the `z`-derivative of this function
is `PzF'`. -/
private def PzF (x : Work.FTS.Galerkin.Fn) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun u θ => (Work.Spaces.DzIter k x u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The `z`-derivative of `PzF`: `2 · D_z^k x u θ · ∂_z(D_z^k x) u θ · sin(2θ)^{-η}`. -/
private def PzF' (x : Work.FTS.Galerkin.Fn) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun u θ => 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ)
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

private theorem PzF_apply (x : Work.FTS.Galerkin.Fn) (k : ℕ) (u θ : ℝ) :
    PzF x k u θ = (Work.Spaces.DzIter k x u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  rfl

private theorem PzF'_apply (x : Work.FTS.Galerkin.Fn) (k : ℕ) (u θ : ℝ) :
    PzF' x k u θ = 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  rfl

/-- **The pointwise sup bound for the `D_z`-iterates of a `ClassC` profile.**

`classC_mixed_sup_le_four` bounds every mixed slot of order `≤ 4` on the open quadrant, and
`mixed b 0 x = D_z^b x` definitionally, so all the `D_z`-iterates up to order `4` are bounded by
a single constant `K₀` on the open quadrant. -/
private theorem dzIter_sup_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ b : ℕ, b ≤ 4 → ∀ {u θ : ℝ}, 0 < u → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter b x u θ| ≤ K₀ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  refine ⟨C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.StrongGlobal.Xn6 α x,
    mul_nonneg (div_nonneg hCpos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _), ?_⟩
  intro b hb u θ hu hθ0 hθ1
  have hmem : (u, θ) ∈ Work.Construction.Qd := by
    rw [Work.Construction.Qd]; exact ⟨hu, hθ0, hθ1⟩
  have h := hC α hα hx b 0 (by omega) hmem
  simpa using h

/-- The angular weight `θ ↦ sin(2θ)^{-η}` is continuous on the open quadrant (where `sin 2θ > 0`),
and so is the full `z`-derivative integrand. -/
private theorem continuousOn_sin_rpow_eta :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (x := 2 * p.2)
      (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos]))))

/-- **The derivative of the angular energy `Pz`.**

`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² sin(2θ)^{-η} dθ` and
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) sin(2θ)^{-η} dθ`
(`D_z = z ∂_z`, `D_z^{k+1} = D_z (D_z^k)`, `η = 99/100`; see
`Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

For `ClassC α x` with `α ∈ (0,1]` and `k ≤ 3`, and every `z > 0`,

  `(Pz x k)' z = (2/z) · Qz x k z`.

Proof route: `DzIter (k+1) x = Dz (DzIter k x) = z * pz (DzIter k x)` is `rfl`, so pointwise
`∂_z ((DzIter k x z θ)² sin(2θ)^{-η}) = 2 * DzIter k x z θ * pz (DzIter k x) z θ * sin(2θ)^{-η}`
by `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter` and the product rule.  Apply
Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with `μ = volume.restrict (Ioo 0 (π/2))`
(which equals `volume.restrict Iθ` by `Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo`),
`s = Ioo (z/2) (2*z)`, `bound θ = (4 * C₀^2 / z) * sin(2θ)^{-η}`, where
`Work.FTS.StrongEps.classC_mixed_sup_le_four` bounds `|mixed b 0 x t θ| ≤ C₀` on the open
quadrant for `b ≤ 4`; `bound` is integrable since `η < 1` (`Work.Spaces.sin_two_rpow` with
`p = -η`).  The a.e. strong measurability of the slices is
`Work.FTS.EllipticEst.SmoothOpen.aesm_slice_summand` composed with `summand_sq_eq`.  Finally move
the constants out of the integral and use `z * pz (DzIter k x) z θ = DzIter (k+1) x z θ`. -/
theorem hasDerivAt_Pz {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Pz x k) (2 / z * Qz x k z) z := by
  have hF : Work.FTS.EllipticEst.SmoothOpen x := hx.reg
  obtain ⟨K₀, hK₀nn, hK₀⟩ := dzIter_sup_le hα hx
  -- the localisation neighbourhood of `z`
  have hnhds : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hk4 : k ≤ 4 := by omega
  have hk14 : k + 1 ≤ 4 := by omega
  -- the rate `2 K₀ / z` at which the angular weight grows
  have hrate : 0 ≤ 2 * K₀ / z := div_nonneg (by linarith) hz.le
  -- the slice of the `z`-derivative of the `k`-th iterate: `|∂_z(D_z^k x)| ≤ 2K₀/z`
  have hpz_le : ∀ {u θ : ℝ}, 0 < u → z / 2 < u → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ| ≤ 2 * K₀ / z := by
    intro u θ hu hzu hθ0 hθ1
    have hb := hK₀ (k + 1) hk14 hu hθ0 hθ1
    have hident : u * |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ|
        = |Work.Spaces.DzIter (k + 1) x u θ| := by
      rw [Work.Spaces.DzIter_succ]
      simp only [Work.Spaces.Dz]
      rw [abs_mul, abs_of_pos hu]
    have h2 : |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ| ≤ K₀ / u := by
      rw [le_div_iff₀ hu]
      rw [mul_comm]
      rw [hident]
      exact hb
    have h3 : K₀ / u ≤ 2 * K₀ / z := by
      rw [div_le_iff₀ hu]
      calc K₀ = (2 * K₀ / z) * (z / 2) := by field_simp
        _ ≤ (2 * K₀ / z) * u := mul_le_mul_of_nonneg_left (le_of_lt hzu) hrate
    exact le_trans h2 h3
  -- ### measurability of the slices
  have hmeas_F : ∀ᶠ u in 𝓝 z,
      AEStronglyMeasurable (PzF x k u) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter k x p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hF.DzIter k).continuousOn.pow 2).mul continuousOn_sin_rpow_eta
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter k x p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont hu
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h
  have hmeas_F' : AEStronglyMeasurable (PzF' x k z)
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => 2 * (Work.Spaces.DzIter k x p.1 p.2
        * Work.Spaces.pz (Work.Spaces.DzIter k x) p.1 p.2)
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))).mul
        ((hF.DzIter k).continuousOn.mul ((hF.DzIter k).pz).continuousOn)).mul
        continuousOn_sin_rpow_eta
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => 2 * (Work.Spaces.DzIter k x p.1 p.2
        * Work.Spaces.pz (Work.Spaces.DzIter k x) p.1 p.2)
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hcont hz
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h
  -- ### integrability of the slice at `z`
  have h_int : Integrable (PzF x k z) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hwz' : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hwz : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz'
    have hs := Work.FTS.EllipticEst.integrableOn_zSummand α 7 hF hx.mem k (by omega)
      (Set.mem_Ici.mpr hz.le)
    have h2 : IntegrableOn (PzF x k z) Work.Spaces.Iθ :=
      MeasureTheory.IntegrableOn.congr_fun (hs.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)
        (fun θ hθ => by
          show (Work.Spaces.w z ^ 2)⁻¹ * (Work.Spaces.DzIter k x z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
            = PzF x k z θ
          rw [PzF_apply, summand_sq_eq x k hθ]
          field_simp [hwz'])
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h2
  -- ### integrability of the dominating bound
  have hb_int : Integrable (fun θ : ℝ => (2 * K₀ * (2 * K₀ / z))
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
    rw [← Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact h.const_mul _
  -- ### the a.e. bound on the derivative
  have h_bound : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ∀ u ∈ Set.Ioo (z / 2) (2 * z), ‖PzF' x k u θ‖ ≤ (2 * K₀ * (2 * K₀ / z))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ u hu => ?_)
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < π / 2 := hθ.2
    have hu0 : 0 < u := lt_trans (by linarith) hu.1
    have hsθ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos])) _).le
    have hA := hK₀ k hk4 hu0 hθ0 hθ1
    have hB := hpz_le hu0 hu.1 hθ0 hθ1
    have hnorm : ‖PzF' x k u θ‖ = 2 * |Work.Spaces.DzIter k x u θ|
        * |Work.Spaces.pz (Work.Spaces.DzIter k x) u θ|
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [PzF'_apply, Real.norm_eq_abs]
      simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg hsθ]
      ring
    rw [hnorm]
    have h2K : 0 ≤ 2 * K₀ := by linarith
    exact mul_le_mul
      (mul_le_mul (by linarith : 2 * |Work.Spaces.DzIter k x u θ| ≤ 2 * K₀) hB
        (abs_nonneg _) h2K)
      (le_refl _) hsθ (mul_nonneg h2K hrate)

  -- ### the a.e. pointwise derivative
  have h_diff : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ∀ u ∈ Set.Ioo (z / 2) (2 * z),
        HasDerivAt (fun u' => PzF x k u' θ) (PzF' x k u θ) u := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ u hu => ?_)
    have hu0 : 0 < u := lt_trans (by linarith) hu.1
    have h1 := ((hF.hasDerivAt_slice_DzIter k hθ hu0).pow 2).congr_deriv
      (show (2 : ℝ) * Work.Spaces.DzIter k x u θ ^ (2 - 1)
            * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ
          = 2 * (Work.Spaces.DzIter k x u θ * Work.Spaces.pz (Work.Spaces.DzIter k x) u θ) by
        rw [show 2 - 1 = (1 : ℕ) from rfl, pow_one]; ring)
    have h2 := h1.mul_const ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    simpa only [PzF_apply, PzF'_apply, Pi.pow_apply] using h2

  -- ### differentiate under the integral sign
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioo 0 (π / 2)))
    (bound := fun θ : ℝ => (2 * K₀ * (2 * K₀ / z)) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (F := PzF x k) (F' := PzF' x k) (x₀ := z) (s := Set.Ioo (z / 2) (2 * z))
    hnhds hmeas_F h_int hmeas_F' h_bound hb_int h_diff
  -- ### identify the two sides with `Pz` and `Qz`
  have hfun : Pz x k = fun u => ∫ a, PzF x k u a
      ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    funext u
    simp only [Pz]
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    simp only [PzF_apply]
  have hQz : Qz x k z = z * ∫ a, (Work.Spaces.DzIter k x z a
      * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
      * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))
      ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    simp only [Qz]
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    have hpt : (fun θ => Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun θ => z * ((Work.Spaces.DzIter k x z θ
          * Work.Spaces.pz (Work.Spaces.DzIter k x) z θ)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      funext θ
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hF'val : (∫ a, PzF' x k z a ∂(volume.restrict (Set.Ioo 0 (π / 2))))
      = 2 * ∫ a, (Work.Spaces.DzIter k x z a * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
          * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))
          ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hpt : (fun a => PzF' x k z a)
        = fun a => 2 * ((Work.Spaces.DzIter k x z a
          * Work.Spaces.pz (Work.Spaces.DzIter k x) z a)
          * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta))) := by
      funext a
      rw [PzF'_apply]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
  have hval : 2 / z * Qz x k z
      = ∫ a, PzF' x k z a ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    rw [hQz, hF'val]
    field_simp
  rw [hfun, hval]
  exact key.2

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
