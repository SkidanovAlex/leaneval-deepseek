import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.LocUnif.LocAux
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-- **The `(1a)` tower, radial and angular halves.**

Let `G n` be a sequence of functions which are `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
and let the mixed jets `mixed c d (G (φ n)) = D_z^c D_θ^d (G (φ n))` converge locally uniformly
on `Q0` to `F c d`, for all `c + d ≤ 2`.  Then the limiting first-order jets are differentiable
with the derivatives predicted by the operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`:

* `∂_z (F c d) = F (c+1) d / z` (the recursion `D_z^{c+1} = z ∂_z ∘ D_z^c`);
* `∂_θ (F c d) = F c (d+1) / sin(2θ)` (the recursion `D_θ^{d+1} = sin(2θ) ∂_θ ∘ D_θ^d`).

The proof is `hasDerivAt_of_tendstoLocallyUniformlyOn` applied slicewise: on each `z`-slice
(with `θ ∈ (0,π/2)` fixed) the functions `z ↦ mixed c d (G (φ n)) z θ` are differentiable with
derivative `mixed (c+1) d (G (φ n)) z θ / z` (the defining recursion of `D_z`), which converges
locally uniformly to `F (c+1) d · θ / ·`; and the `θ`-slices are handled the same way using the
commutation `D_θ D_z^c = D_z^c D_θ` of the two operators on `C^∞`-functions (Lean name:
`mixed_partials_of_smoothOpen`). -/
theorem LimTower_dz {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) :
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) := by
  have hinv : ContinuousOn (fun p : ℝ × ℝ => p.1⁻¹) Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀ continuousOn_fst
      (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.inv₀
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      (fun p hp => by
        obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ne_of_gt (Work.FTS.StrongEps.LocUnif.sin_two_pos_Q0 ⟨h0, h1⟩))
  constructor
  · -- the radial half: `∂_z (F c d) = F (c+1) d / z`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ x : ℝ, 0 < x → (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx, hθ0, hθ1⟩
    have hcd2 : c + 1 + d ≤ 2 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv (c + 1) d hcd2) hinv
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_fst
      (U := Work.FTS.EllipticEst.Q0) (θ := θ) (W := Set.Ioi (0 : ℝ)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n x => x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ)
        (fun x => x⁻¹ * F (c + 1) d x θ) Filter.atTop (Set.Ioi (0 : ℝ)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d (G (φ n)) z' θ)
          (x⁻¹ * Work.Spaces.mixed (c + 1) d (G (φ n)) x θ) x :=
      Filter.Eventually.of_forall fun n x hx => by
        have hd := ((hsm (φ n)).mixed c d).hasDerivAt_slice (θ := θ) ⟨hθ0, hθ1⟩ hx
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).1 x θ (hmem x hx), div_eq_mul_inv, mul_comm]
    have hfg : ∀ x ∈ Set.Ioi (0 : ℝ), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) x θ) Filter.atTop (𝓝 (F c d x θ)) :=
      fun x hx => (hconv c d (by omega)).tendsto_at (hmem x hx)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hf' hf hfg hz
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])
  · -- the angular half: `∂_θ (F c d) = F c (d+1) / sin 2θ`
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hmem : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (π / 2) →
        (z, t) ∈ Work.FTS.EllipticEst.Q0 :=
      fun t ht => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ht.1, ht.2⟩
    have hcd2 : c + (d + 1) ≤ 2 := by omega
    have hmul := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_mul_continuousOn
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (hconv c (d + 1) hcd2) hsin
    have hslice := Work.FTS.StrongEps.LocUnif.tendstoLocallyUniformlyOn_slice_snd
      (U := Work.FTS.EllipticEst.Q0) (z := z) (W := Set.Ioo (0 : ℝ) (π / 2)) hmem hmul
    have hf' : TendstoLocallyUniformlyOn
        (fun n t => (Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t)
        (fun t => (Real.sin (2 * t))⁻¹ * F c (d + 1) z t)
        Filter.atTop (Set.Ioo (0 : ℝ) (π / 2)) := hslice
    have hf : ∀ᶠ n in Filter.atTop, ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
          ((Real.sin (2 * t))⁻¹ * Work.Spaces.mixed c (d + 1) (G (φ n)) z t) t :=
      Filter.Eventually.of_forall fun n t ht => by
        have hd : HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ')
            (Work.Spaces.pth (Work.Spaces.mixed c d (G (φ n))) z t) t :=
          (((hsm (φ n)).mixed c d).curry_θ hz).contDiffAt
            (isOpen_Ioo.mem_nhds ⟨ht.1, ht.2⟩) |>.differentiableAt (by simp) |>.hasDerivAt
        refine hd.congr_deriv ?_
        rw [(Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen c d
          (hsm (φ n))).2.1 z t (hmem t ht), div_eq_mul_inv, mul_comm]
    have hfg : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), Tendsto
        (fun n => Work.Spaces.mixed c d (G (φ n)) z t) Filter.atTop (𝓝 (F c d z t)) :=
      fun t ht => (hconv c d (by omega)).tendsto_at (hmem t ht)
    have key := hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hf' hf hfg ⟨hθ0, hθ1⟩
    exact key.congr_deriv (by rw [div_eq_mul_inv, mul_comm])

end Work.FTS_EllLimOK
