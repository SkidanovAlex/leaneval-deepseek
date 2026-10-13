import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.Pinning.leftLimitOfBoundedDeriv
import Submission.Work.FTS_EllLimOK.Pinning.tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_div_cos_sq_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.Pinning

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Pinning of `Ψ` at the corner `θ = π/2`

`Work.FTS_EllLimOK.Reconstruct` records the `θ`-reconstruction of a solution from the
coefficient `Vop Ψ = ∂_θΨ - tan θ · Ψ`: the identity

`cos θ · Vop Ψ z θ = ∂_θ (cos θ · Ψ z θ)`

shows that `cos θ · Vop Ψ` is the derivative of `θ ↦ cos θ · Ψ z θ`, so a bound
`|Vop Ψ| ≤ K` on the open quadrant makes that function `K`-Lipschitz there and gives the
*existence* of the corner value `lim_{θ → π/2⁻} cos θ · Ψ z θ`.

What the reconstruction deliberately does not supply — and what the pinning lemma below does —
is that this corner value *vanishes*.  That comes from the honest `ℋ⁰`-membership of
`Ψ / cos`: since `1/cos²` is not integrable at `π/2`, a non-zero limit would force
`∫ (Ψ z θ / cos θ)² = ∞` on a whole tail `(t, π/2)`.

The two analytic ingredients are delegated and live in this same directory:

* `Work.FTS.EllLimOK.Pinning.leftLimitOfBoundedDeriv` — `φ` with `|φ'| ≤ M` on a left
  neighbourhood of `x` has a finite left limit at `x`;
* `Work.FTS.EllLimOK.Pinning.tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq` — a finite limit
  of `θ ↦ cos θ · f θ` at `π/2⁻` together with the integrability of `(f θ/cos θ)²` forces that
  limit to be `0`;
* `Work.FTS.EllLimOK.Pinning.integrableOn_div_cos_sq_of_HkMem` — `ℋ⁰`-membership of
  `Ψ z θ / cos θ` gives the plain square-integrability of the angular slice `(Ψ z ·/cos ·)²`.
-/

/-- **The corner value `cos θ · Ψ z θ → 0` at `θ = π/2⁻`.**

For every `z > 0`, if `Ψ` is `C^∞` on the open quadrant, `Vop Ψ = ∂_θΨ - tan θ · Ψ` is bounded
by `K` there and `Ψ z θ / cos θ` belongs to the weighted space `ℋ⁰` (over the angular variable),
then `cos θ · Ψ z θ` tends to `0` as `θ → π/2⁻`. -/
theorem tendsto_cos_mul_of_hkMem_cosDiv {α K : ℝ} (hK : 0 ≤ K) {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hbound : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop Ψ z θ| ≤ K)
    (hmem : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0) := by
  intro z hz
  have hzpos : 0 < z := hz
  -- `(Ψ z θ / cos θ)²` is integrable on `(0, π/2)`
  have hint : IntegrableOn (fun θ : ℝ => (Ψ z θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_div_cos_sq_of_HkMem hsm hmem hzpos
  -- `θ ↦ cos θ · Ψ z θ` has derivative `cos θ · Vop Ψ z θ`, whose modulus is at most `K`
  have hder : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2),
      HasDerivAt (fun s : ℝ => Real.cos s * Ψ z s)
        (Real.cos θ * Work.Construction.Vop Ψ z θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩
    have hslice : HasDerivAt (fun s : ℝ => Ψ z s) (Work.Spaces.pth Ψ z θ) θ :=
      (((hsm.curry_θ hzpos).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ')).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => Real.cos s * Ψ z s)
        (-Real.sin θ * Ψ z θ + Real.cos θ * Work.Spaces.pth Ψ z θ) θ :=
      (Real.hasDerivAt_cos θ).mul hslice
    refine h3.congr_deriv ?_
    rw [cos_mul_Vop_eq Ψ hθ']
    ring
  have hbdd : ∀ θ ∈ Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2),
      |Real.cos θ * Work.Construction.Vop Ψ z θ| ≤ K := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩
    have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hzpos, hθ'⟩
    have h1 := hbound z θ hQd
    calc |Real.cos θ * Work.Construction.Vop Ψ z θ|
        = |Real.cos θ| * |Work.Construction.Vop Ψ z θ| := abs_mul _ _
      _ ≤ 1 * K := mul_le_mul (Real.abs_cos_le_one θ) h1 (abs_nonneg _) (by norm_num)
      _ = K := one_mul K
  -- the corner value exists, and then must vanish
  obtain ⟨G, hG⟩ := leftLimitOfBoundedDeriv (φ := fun s : ℝ => Real.cos s * Ψ z s)
    (ψ := fun θ : ℝ => Real.cos θ * Work.Construction.Vop Ψ z θ) (x := Real.pi / 2) (d := 1)
    (M := K) one_pos hK hder hbdd
  exact tendsto_cos_mul_eq_zero_of_integrable_div_cos_sq hint ⟨G, hG⟩

end Work.FTS_EllLimOK.Pinning
