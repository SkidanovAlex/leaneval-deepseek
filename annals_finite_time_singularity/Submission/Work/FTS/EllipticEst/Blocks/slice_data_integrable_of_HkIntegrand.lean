import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-! ## The two scaling identities that strip the radial weight

The `j`-th summand of `HkIntegrand α k G z ·` carrying the *radial* `D_z`-weight is
`(D_z^j G z θ · w z / sin(2θ)^{η/2})²`.  By the weight identifications `w_div_sin_sq`
and `Wt_sq` of `Work.FTS.EllipticEst.SliceAux` this is

`(D_z^j G z θ)² · (w z)² · sin(2θ)^{-η}`  resp.  `(D_z^j D_θ^m G z θ)² · (w z)² · sin(2θ)^{-γ}`,

so multiplying by the *constant* `((w z)²)^{-1}` removes the factor `(w z)²` and leaves
exactly the slice integrands `(·)² · thEta θ` resp. `(·)² · thGam α θ` of the slice
estimates.  These two algebraic lemmas isolate that manipulation (which is the only place
where the hypothesis `z > 0` is used, through `w z ≠ 0`). -/

/-- For `z > 0` the radial weight `w z = (1+z)²/z²` is nonzero. -/
private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2

/-- Stripping the radial weight from a pure `D_z`-summand: for `θ ∈ Iθ`, `z > 0`,
`(w z)^{-2} · (c · w z / sin(2θ)^{η/2})² = c² · sin(2θ)^{-η}`. -/
private lemma inv_w_sq_mul_zsummand (z θ c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.w_div_sin_sq hθ z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ * (c ^ 2 *
          ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
        rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thEta θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

/-- Stripping the radial weight from a mixed summand: for `θ ∈ Iθ`, `z > 0`,
`(w z)^{-2} · (c · Wt α z θ)² = c² · sin(2θ)^{-γ}`. -/
private lemma inv_w_sq_mul_mixed (z θ α c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.Wt_sq hθ α z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * (Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ)) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by
        rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thGam α θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

/-- At a fixed radial level `z > 0`, the integrability of the `H^k`-integrand of `∂_θ² f`
makes its individual summands integrable; hence the `θ`-slice data of `u_j = D_z^j f z ·`
(namely `u_j'' = D_z^j (∂_θ² f)` and its `D_θ`-iterates) is integrable against the angular
weights `sin(2θ)^{-η}` resp. `sin(2θ)^{-γ}`, which is exactly the integrability input the
slice estimate `slice_d_bound` requires for the slice `u_j`. -/
theorem slice_data_integrable_of_HkIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
      (∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) := by
  -- `pthIter 2 f` is smooth on the same neighbourhood as `f`
  have hzI : z ∈ Work.Spaces.Iz := hz.le
  have hterms := Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms α k
    (Work.Spaces.pthIter 2 f) (hsm.pth.pth) hzI hInt
  constructor
  · -- the pure `D_z^j (∂_θ² f)`-summand of the integrand, rescaled by the constant
    -- `((w z)²)^{-1}` so that the radial factor `(w z)²` disappears
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul (hterms.1 j hj) ((Work.Spaces.w z) ^ 2)⁻¹)
      ?_ measurableSet_Icc
    intro θ hθ
    exact inv_w_sq_mul_zsummand z θ _ hθ hz
  · -- the mixed summands `D_z^j D_θ^m (∂_θ² f)`
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul (hterms.2 m j hm1 (by omega))
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ measurableSet_Icc
    intro θ hθ
    exact inv_w_sq_mul_mixed z θ α _ hθ hz

end Work.FTS.EllipticEst.Blocks
