import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `f² · sin(2θ)^{-η}` on the angular interval, from `ℋ^k`-membership

The `0`-th summand of the `ℋ^k`-weighted integrand of `f` is

`(D_z^0 f · w(z) / sin(2θ)^{η/2})² = f(z,θ)² · w(z)² · sin(2θ)^{-η}`,

and `Work.FTS.EllipticEst.integrableOn_zSummand` (the open-quadrant version of the basic
`ℋ^k` API of `OpenQDefs.lean`) says that this summand is integrable on `Iθ` for every
`z ∈ Iz`.  On the open quadrant the radial weight `w` is a positive *constant* (in `θ`), so
scalar multiplication by `(w(z)²)^{-1}` transfers the integrability to the unweighted
quantity `f(z,θ)² · sin(2θ)^{-η}`.  (At the two endpoints `θ = 0, π/2` both sides of the
pointwise identity vanish separately, so no exceptional set has to be removed.)

This is the `η`-weighted honesty statement consumed by the pinning argument at the corner
`θ = π/2`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Pinning

/-- **The pointwise identity converting the `0`-th weighted summand into the unweighted
`η`-weighted square.**  For `z > 0` and `θ ∈ Iθ`,

`(w z²)^{-1} · (F · w z / sin(2θ)^{η/2})² = F² · sin(2θ)^{-η}`.

Both sides vanish at the endpoints `θ = 0, π/2` (where `sin(2θ) = 0`); on the open interval
the identity is the `rpow` algebra `(sin(2θ)^{η/2})² = sin(2θ)^{η}` together with the
cancellation of the constant factor `w z²`. -/
lemma inv_w_sq_mul_weighted_sq_eq (z θ F : ℝ) (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z ^ 2)⁻¹ * (F * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = F ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    have h2 : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi := by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    exact Real.sin_nonneg_of_mem_Icc ⟨h2.1, h2.2⟩
  have hwn : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with hs | hs
  · -- endpoints: `sin(2θ) = 0`, both sides vanish
    rw [hs]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [h1, h2]
    simp
  · -- interior: `0 < sin(2θ)` and the `rpow` exponent is additive
    have hspos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsin0 (Ne.symm hs)
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hsin0]
      norm_num
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, Real.rpow_neg hsin0 (Work.Spaces.eta)]
    field_simp

theorem integrableOn_sq_rpow_of_HkMem {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn
        (fun θ => (f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
  intro z hz
  -- the `i = 0` weighted `D_z`-summand of the `ℋ^k`-integrand is integrable on `Iθ`
  have hsum : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 0 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hmem 0 (Nat.zero_le k)
      (Set.mem_Ici.mpr hz.le)
  -- rescale by the (positive, `θ`-independent) constant `(w z²)^{-1}`
  have hc : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z ^ 2)⁻¹ *
      (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    hsum.integrable.const_mul _
  refine hc.congr_fun ?_ ?_
  · intro θ hθ
    rw [Work.Spaces.DzIter_zero]
    exact inv_w_sq_mul_weighted_sq_eq z θ (f z θ) hz hθ
  · rw [Work.Spaces.Iθ]
    exact measurableSet_Icc

end Work.FTS_EllLimOK.Pinning
