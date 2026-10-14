import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.LocData.HkMem_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The pointwise calculus: `D_z`, `D_θ` and their iterates commute with a scalar -/

/-- `D_z (β·g) = β·(D_z g)`: multiplication by a constant commutes with `D_z = z ∂_z`.
No differentiability of `g` is needed, `deriv` being linear over constants. -/
theorem Dz_const_mul (β : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => β * g z θ) = fun z θ => β * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
  ring

/-- `D_θ (β·g) = β·(D_θ g)`: multiplication by a constant commutes with
`D_θ = sin(2θ) ∂_θ`.  No differentiability of `g` is needed. -/
theorem Dth_const_mul (β : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => β * g z θ) = fun z θ => β * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const_mul_field]
  ring

/-- `D_z^i (β·g) = β·(D_z^i g)`. -/
theorem DzIter_const_mul (β : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      exact Dz_const_mul β _

/-- `D_θ^i (β·g) = β·(D_θ^i g)`. -/
theorem DthIter_const_mul (β : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_const_mul β _

/-- `D_z^j D_θ^i (β·g) = β·(D_z^j D_θ^i g)`, i.e. the mixed operators of `HkIntegrand`
commute with a scalar. -/
theorem mixed_const_mul (β : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## The `ℋ^k`-integrand of a scalar multiple -/

/-- The `ℋ^k`-integrand scales by `β²`:
`HkIntegrand α k (β·f) z θ = β² · HkIntegrand α k f z θ`.

Every summand of `HkIntegrand` is the square of a weighted derivative, and each weighted
derivative of `β·f` is `β` times the corresponding derivative of `f`
(`DzIter_const_mul`, `mixed_const_mul`); the weights `w z / sin(2θ)^{η/2}`, `Wt α z θ` do not
depend on `f`. -/
theorem hkIntegrand_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  simp only [DzIter_const_mul, mixed_const_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hp : (1 ≤ i ∧ i + j ≤ k)
    · simp [hp]; ring
    · simp [hp]

/-! ## The main result -/

/-- **`ℋ^k` is closed under scalar multiplication.**  If `f ∈ ℋ^k` then `β·f ∈ ℋ^k` for every
`β : ℝ`.

Both integrability requirements transfer from `f` to `β·f` because the corresponding
`ℋ^k`-integrands differ by the constant factor `β²` (`hkIntegrand_const_mul`):
the angular slices by `Integrable.const_mul`, and the outer `z`-integral by
`integral_const_mul` followed by `Integrable.const_mul`. -/
theorem HkMem_const_mul (α : ℝ) (k : ℕ) (β : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => β * f z θ) := by
  constructor
  · intro z hz
    have h := hf.1 z hz
    rw [funext (fun θ => hkIntegrand_const_mul α k β f z θ)]
    exact h.const_mul _
  · have h := hf.2
    have key : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = fun z => β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      simp only [hkIntegrand_const_mul]
      rw [integral_const_mul]
    rw [key]
    exact h.const_mul _

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.hLoc_vanishing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.LocData

/-- **The radial bump vanishes near `z = 0`.**  For `|z| < 1/2` one has `4z - 5 ∈ (-7,-3)`, hence
`|4z - 5| > 2` and `χ(4z-5) = 0` (`Work.Stability.chi_eq_zero`). -/
theorem bumpZ_eventuallyEq_zero : ∀ᶠ z in 𝓝 (0 : ℝ), bumpZ z = 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [Metric.mem_ball, Real.dist_eq] at hz
  have hz' : |z| < 1 / 2 := by simpa using hz
  rw [bumpZ_apply, Work.Stability.chi_eq_zero]
  have hzlt : z < 1 / 2 := (abs_lt.mp hz').2
  have hneg : 4 * z - 5 < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

/-- The radial bump vanishes at `z = 0` (specialisation of `bumpZ_eventuallyEq_zero`). -/
theorem bumpZ_zero : bumpZ 0 = 0 := by
  rw [bumpZ_apply, show (4 : ℝ) * 0 - 5 = -5 by norm_num]
  exact Work.Stability.chi_eq_zero (by norm_num)

theorem hLoc_vanishing (α : ℝ) (hα : 0 < α) :
    Work.Spaces.VanishTheta (hLoc α) ∧
      (∀ θ ∈ Work.Spaces.Iθ, hLoc α 0 θ = 0 ∧ Work.Spaces.pz (hLoc α) 0 θ = 0) := by
  have hG0 : Work.Spaces.Gam α 0 = 0 := Work.Spaces.Gam_zero_left α (ne_of_gt hα)
  have hGpi : Work.Spaces.Gam α (π / 2) = 0 := Work.Spaces.Gam_zero_right α (ne_of_gt hα)
  -- The radial factor vanishes at `z = 0`, so both `hLoc α 0 θ` and its `z`-derivative vanish.
  have hz0 : ∀ θ : ℝ, hLoc α 0 θ = 0 := by
    intro θ
    rw [hLoc_apply, bumpZ_zero, zero_mul]
  have hdz0 : ∀ θ : ℝ, Work.Spaces.pz (hLoc α) 0 θ = 0 := by
    intro θ
    have hev : (fun z => hLoc α z θ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [bumpZ_eventuallyEq_zero] with z hz
      rw [hLoc_apply, hz, zero_mul]
    show deriv (fun z => hLoc α z θ) 0 = 0
    rw [hev.deriv_eq, deriv_const]
  refine ⟨⟨fun z => ?_, fun z => ?_⟩, fun θ _ => ⟨hz0 θ, hdz0 θ⟩⟩
  · rw [hLoc_apply, hG0, mul_zero]
  · rw [hLoc_apply, hGpi, mul_zero]

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.omegaProfile_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Compact support of the physical vorticity of a profile

The physical vorticity of the localised data is the `e_θ`-field

  `omegaProfile p F x = F (ρ(x)^p) (θ(x)) • e_θ(x)`

(`Work.FTS.LocData.omegaProfile`).  Its support is controlled by the single property of the
profile that the localisation provides, namely that `F` vanishes for self-similar variables
beyond a scale `Z` (`Work.FTS.LocData.ProfileZeroFar`).

This module records the two consequences:

* a pointwise vanishing criterion: `Z ≤ ρ(x)^p` forces `omegaProfile p F x = 0`;
* `HasCompactSupport (omegaProfile p F)`: the support is contained in the closed ball of radius
  `Z^(1/p)`, because `ρ(x)^p < Z` with `p > 0` forces `ρ(x) < Z^(1/p)` and `ρ = ‖·‖`.

Note that no regularity of `F` is needed: only the vanishing.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData





end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.profileZeroFar_locData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData


end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.vanishTheta_locG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.LocData.vanishTheta_locG` — the angular vanishing of the localised perturbation

The perturbation `g = locG α L β h = -zfar L F_* + β h` of the route is a `VanishTheta`
function: it vanishes on both angular boundaries `θ = 0` and `θ = π/2` of the quadrant.

The reason is that *both* terms do: `F_* = α (Γ(θ)/c(α)) 2z/(1+z)²` has the angular factor
`Γ(θ) = (sin θ cos²θ)^{α/3}`, which vanishes at `θ = 0` (because `sin 0 = 0`) and at
`θ = π/2` (because `cos (π/2) = 0`), the exponent `α/3 > 0` being strictly positive; and `h`
vanishes there by hypothesis.  Note that the vanishing of `F_*` on the boundary is used only
through the two *pointwise* facts `Fstar_theta_zero` and `Fstar_theta_pi_half` below — no
regularity, no integrability, and in particular no hypothesis on `L`, is involved.

(The hypotheses `hα1 : α ≤ 1` of the statement are not needed here; they are part of the
uniform interface of the chapter.)
-/

set_option linter.unusedVariables false

namespace Work.FTS.LocData

/-- `F_*(z,0) = 0`: the angular factor `Γ(0) = (sin 0 · cos²0)^{α/3} = 0` because
`sin 0 = 0` and the exponent `α/3` is nonzero. -/
theorem Fstar_theta_zero (α : ℝ) (hα : 0 < α) (z : ℝ) : Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam,
    show Real.sin 0 * Real.cos 0 ^ 2 = 0 by simp,
    Real.zero_rpow (by positivity : α / 3 ≠ 0), zero_div]
  ring

/-- `F_*(z,π/2) = 0`: the angular factor `Γ(π/2) = (sin(π/2) · cos²(π/2))^{α/3} = 0` because
`cos (π/2) = 0`. -/
theorem Fstar_theta_pi_half (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (Real.pi / 2) = 0 := by
  rw [Work.Construction.Fstar, Work.Spaces.Gam,
    show Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 by
      simp [Real.cos_pi_div_two],
    Real.zero_rpow (by positivity : α / 3 ≠ 0), zero_div]
  ring

/-- **The angular vanishing of the localised perturbation.**  If `h` vanishes at `θ = 0` and
`θ = π/2`, so does `locG α L β h = F_*·χ(·/L) + β h - F_*`: both `F_*·χ(·/L)` and `F_*` vanish
on the boundary and `β · h` does by hypothesis. -/
theorem vanishTheta_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z : ℝ, h z 0 = 0 ∧ h z (Real.pi / 2) = 0) :
    Work.Spaces.VanishTheta (locG α L β h) := by
  constructor
  · intro z
    rw [locG_apply, locData_apply, Fstar_theta_zero α hα z, (hh z).1]
    ring
  · intro z
    rw [locG_apply, locData_apply, Fstar_theta_pi_half α hα z, (hh z).2]
    ring

end Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.LocData.zero_slice_locG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

open Filter
open scoped Topology

theorem zero_slice_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ, z ≤ 3 / 4 → h z θ = 0) (hL : 1 ≤ L) :
    ∀ θ ∈ Work.Spaces.Iθ, locG α L β h 0 θ = 0 ∧ Work.Spaces.pz (locG α L β h) 0 θ = 0 := by
  intro θ hθ
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hchi0 : Work.Stability.chi (0 / L) = 1 := by rw [zero_div, Work.Stability.chi_zero]
  have hh0 : h 0 θ = 0 := hh 0 θ (by norm_num)
  constructor
  · -- the value at `z = 0`: the far part vanishes because `χ 0 = 1`, and so does the bump
    rw [locG_eq_zfar, Work.Stability.zfar_apply, hchi0, hh0]
    ring
  · -- the `z`-derivative at `0`: the slice is zero on the neighbourhood `(-1, 3/4)` of `0`
    rw [Work.Spaces.pz]
    have hev : (fun z => locG α L β h z θ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1) (3 / 4) by norm_num)]
        with z hz
      have hz1 : |z| < 1 := abs_lt.mpr ⟨hz.1, by linarith [hz.2]⟩
      have hzL : |z / L| ≤ 1 := by
        rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
        exact le_trans (le_of_lt hz1) hL
      have hchiz : Work.Stability.chi (z / L) = 1 := Work.Stability.chi_eq_one hzL
      have hhz : h z θ = 0 := hh z θ (le_of_lt hz.2)
      rw [locG_eq_zfar, Work.Stability.zfar_apply, hchiz, hhz]
      ring
    rw [hev.deriv_eq, deriv_const]

end Work.FTS.LocData
end
