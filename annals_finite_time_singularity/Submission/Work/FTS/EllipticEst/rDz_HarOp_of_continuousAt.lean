/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z` of the weighted Hardy operator, from continuity of the integrand

The weighted Hardy operator of `GbarSetup.lean` is
`HarOp β u z = z^{-β} ∫_0^z s^{β-1} u s ds`.  Its commutation with `rDz g z = z ∂_z g z` is the
identity

  `rDz (HarOp β u) z = -β · HarOp β u z + u z`,

which is the one-variable version (`D_z` applied to `Ḡ(z) sin 2θ`) of the recursion used in
Elgindi's §'Elliptic Regularity Estimates' when pushing `D_z^j` through `Ḡ`.

The existing `Work.FTS.EllipticEst.rDz_HarOp` (`Gbar_Hk_fts.lean`) proves this under the
stronger hypotheses `1 ≤ β` and `u ∈ C⁰((-1,∞))`.  Here we prove the form needed in this
development, where only `0 < β`, `u` continuous on `(0,∞)` and the *interval integrability* of
the weighted integrand `s ↦ s^{β-1} u s` on `[0,z]` are assumed (so that `β < 1` is allowed
and the integrand need not be continuous up to `0`), and where the continuity of `u` is only
required near the *upper* endpoint `z > 0` — the new ingredient being that `z > 0` makes the
map `s ↦ s^{β-1}` differentiable (hence continuous) at `z` for **every** real exponent.

The proof is the fundamental theorem of calculus at the upper endpoint plus the product rule:

  `∂_z HarOp β u z = (-β z^{-β-1}) · ∫_0^z s^{β-1} u s ds + z^{-β} · (z^{β-1} u z)`,

and `z` times this is `-β HarOp β u z + u z` because `z·z^{-β-1} = z^{-β}` and
`z·z^{-β}·z^{β-1} = 1` for `z > 0`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.GbarSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Work.FTS.EllipticEst

/-- For `x > 0` the weighted integrand `s ↦ s ^ (β - 1) * u s` is continuous at `x` as soon as
`u` is continuous on `(0,∞)`: at a positive point the real power `s ↦ s ^ (β - 1)` is
differentiable, for any real exponent. -/
theorem continuousAt_rpow_sub_one_mul_of_continuousOn (β : ℝ) {u : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hu : ContinuousOn u (Set.Ioi 0)) :
    ContinuousAt (fun s : ℝ => s ^ (β - 1) * u s) x :=
  ((Real.hasDerivAt_rpow_const (p := β - 1) (Or.inl (ne_of_gt hx))).continuousAt).mul
    (hu.continuousAt (Ioi_mem_nhds hx))

/-- `HasDerivAt` form of the commutation of `rDz` with the Hardy operator: under the hypotheses
that `u` is continuous on `(0,∞)` and that `s ↦ s^{β-1} u s` is interval integrable on `[0,z]`,
`HarOp β u` has derivative `(-β) z^{-β-1} ∫_0^z s^{β-1} u s ds + z^{-β} (z^{β-1} u z)` at `z`. -/
theorem hasDerivAt_HarOp_of_continuousAt (β : ℝ) {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hu : ContinuousOn u (Set.Ioi 0))
    (hint : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * u s) volume 0 z) :
    HasDerivAt (HarOp β u)
      ((-β) * z ^ (-β - 1) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s)
        + z ^ (-β) * (z ^ (β - 1) * u z)) z := by
  have hcont : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt (fun s : ℝ => s ^ (β - 1) * u s) x :=
    fun x hx => continuousAt_rpow_sub_one_mul_of_continuousOn β hx hu
  have hsm : StronglyMeasurableAtFilter (fun s : ℝ => s ^ (β - 1) * u s) (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi (0 : ℝ)) (μ := volume)
      isOpen_Ioi hcont z hz
  -- the fundamental theorem of calculus at the upper endpoint `z > 0`
  have hJ : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, s ^ (β - 1) * u s)
      (z ^ (β - 1) * u z) z :=
    intervalIntegral.integral_hasDerivAt_right hint hsm (hcont z hz)
  have hA : HasDerivAt (fun y : ℝ => y ^ (-β)) ((-β) * z ^ (-β - 1)) z :=
    Real.hasDerivAt_rpow_const (p := -β) (Or.inl (ne_of_gt hz))
  have h := hA.mul hJ
  have hfun : HarOp β u
      = (fun y : ℝ => y ^ (-β))
        * (fun y : ℝ => ∫ s in (0 : ℝ)..y, s ^ (β - 1) * u s) := rfl
  rw [hfun]
  convert h using 1

/-- `rDz` of the Hardy operator: `z ∂_z (HarOp β u)(z) = -β · HarOp β u z + u z`, for `0 < β`,
`u` continuous on `(0,∞)` and `s ↦ s^{β-1} u s` interval integrable on `[0,z]`. -/
theorem rDz_HarOp_of_continuousAt (β : ℝ) (hβ : 0 < β) {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hu : ContinuousOn u (Set.Ioi 0))
    (hint : IntervalIntegrable (fun s : ℝ => s ^ (β - 1) * u s) MeasureTheory.volume 0 z) :
    Work.FTS.EllipticEst.rDz (Work.FTS.EllipticEst.HarOp β u) z
      = -β * Work.FTS.EllipticEst.HarOp β u z + u z := by
  have h := (hasDerivAt_HarOp_of_continuousAt (u := u) (z := z) β hz hu hint).deriv
  -- the three real-power identities at `z > 0`
  have h1 : z * z ^ (-β - 1) = z ^ (-β) := by
    have hsp : z ^ (-β) * z ^ (-1 : ℝ) = z ^ (-β - 1) := by
      rw [← Real.rpow_add hz, show -β + (-1 : ℝ) = -β - 1 by ring]
    have hz1 : z * z ^ (-1 : ℝ) = 1 := by
      have h' : z ^ (1 : ℝ) * z ^ (-1 : ℝ) = 1 := by
        rw [← Real.rpow_add hz, show (1 : ℝ) + (-1) = 0 by ring, Real.rpow_zero]
      rwa [Real.rpow_one] at h'
    calc z * z ^ (-β - 1) = z * (z ^ (-β) * z ^ (-1 : ℝ)) := by rw [← hsp]
      _ = z ^ (-β) * (z * z ^ (-1 : ℝ)) := by ring
      _ = z ^ (-β) := by rw [hz1, mul_one]
  have h2 : z * z ^ (-β) = z ^ (1 - β) := by
    have h' : z ^ (1 : ℝ) * z ^ (-β) = z ^ (1 - β) := by
      rw [← Real.rpow_add hz, show (1 : ℝ) + -β = 1 - β by ring]
    rwa [Real.rpow_one] at h'
  have h3 : z ^ (1 - β) * z ^ (β - 1) = 1 := by
    rw [← Real.rpow_add hz, show 1 - β + (β - 1) = 0 by ring, Real.rpow_zero]
  set J := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * u s with hJdef
  -- the pointwise algebra `z · (derivative) = -β · HarOp β u z + u z`
  have hmain : z * ((-β) * z ^ (-β - 1) * J + z ^ (-β) * (z ^ (β - 1) * u z))
      = -β * (z ^ (-β) * J) + u z := by
    have e1 : z * ((-β) * z ^ (-β - 1) * J) = -β * (z ^ (-β) * J) := by
      rw [show z * ((-β) * z ^ (-β - 1) * J) = (z * z ^ (-β - 1)) * (-β * J) by ring, h1]
      ring
    have e2 : z * (z ^ (-β) * (z ^ (β - 1) * u z)) = u z := by
      rw [show z * (z ^ (-β) * (z ^ (β - 1) * u z))
          = (z * z ^ (-β)) * (z ^ (β - 1) * u z) by ring, h2]
      rw [show z ^ (1 - β) * (z ^ (β - 1) * u z)
          = (z ^ (1 - β) * z ^ (β - 1)) * u z by ring, h3, one_mul]
    rw [mul_add, e1, e2]
  simp only [rDz, h, HarOp]
  exact hmain

end Work.FTS.EllipticEst
