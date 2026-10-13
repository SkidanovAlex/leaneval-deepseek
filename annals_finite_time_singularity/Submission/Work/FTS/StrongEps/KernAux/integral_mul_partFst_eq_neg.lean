import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts in the first coordinate on `ℝ × ℝ`

`Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg` is the two-dimensional
integration-by-parts identity

`∫ p, u p * ∂₁v p = - ∫ p, ∂₁u p * v p`

for `u : ℝ × ℝ → ℝ` of class `C¹` with **compact support** and an arbitrary
`C¹` function `v` (no support condition on `v`; everything is localised by the
support of `u`).

The proof is by Fubini together with the one-dimensional integration by parts
`∫ x, f x * deriv g x = - ∫ x, deriv f x * g x` for `f` of class `C¹` with
compact support, applied to every fibre `x ↦ u (x, y)`, `x ↦ v (x, y)`.

The file also provides the small fibre calculus used on the way, in particular
* `deriv_slice_fst_eq` : the derivative of the fibre is the Fréchet derivative
  applied to the unit vector `(1, 0)`,
* `continuous_deriv_slice_fst` : that fibre-derivative is continuous in `p`,
* `hasCompactSupport_slice_fst` : the fibre of a compactly supported function
  still has compact support,
* `hasCompactSupport_deriv_slice_fst` : the derivative of the fibre of a
  compactly supported function has compact support,
* `oneDim_ibp_compact` : the one-dimensional integration by parts on `ℝ`.
-/

namespace Work.FTS.StrongEps.KernAux

open MeasureTheory

open scoped Topology

/-- The derivative of the first-coordinate slice of a function on `ℝ × ℝ`
is the Fréchet derivative at the point, evaluated at the unit vector `(1, 0)`. -/
lemma deriv_slice_fst_eq {f : ℝ × ℝ → ℝ} {x y : ℝ} (hf : DifferentiableAt ℝ f (x, y)) :
    deriv (fun s : ℝ => f (s, y)) x = fderiv ℝ f (x, y) (1, 0) := by
  have hγ : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) x := by
    simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).hasDerivAt
  have h := hf.hasFDerivAt.comp_hasDerivAt x hγ
  simpa [Function.comp_def] using h.deriv

/-- For a `C¹` function on `ℝ × ℝ`, the function sending a point to the
derivative of its first-coordinate slice is continuous. -/
lemma continuous_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ f p (1, 0)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact h1.congr (fun p => (deriv_slice_fst_eq (x := p.1) (y := p.2)
    hf.differentiable_one.differentiableAt).symm)

/-- The derivative of the first-coordinate slice of a compactly supported `C¹`
function again has compact support. -/
lemma hasCompactSupport_deriv_slice_fst {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (s, p.2)) p.1) := by
  refine hfs.mono' ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hcon
  have h0 : f =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) := notMem_tsupport_iff_eventuallyEq.mp hcon
  have hfd : fderiv ℝ f p = 0 := by
    rw [h0.fderiv_eq]; simp
  exact hp (by rw [deriv_slice_fst_eq (hf.differentiable_one.differentiableAt), hfd]; rfl)

/-- Every first-coordinate slice of a compactly supported function has compact
support. -/
lemma hasCompactSupport_slice_fst {f : ℝ × ℝ → ℝ} (hfs : HasCompactSupport f) (y : ℝ) :
    HasCompactSupport (fun x : ℝ => f (x, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Prod.fst '' tsupport f) ?_ ?_
  · exact IsCompact.image hfs continuous_fst
  · intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    exact hx ((notMem_tsupport_iff_eventuallyEq.mp
      (fun hmem => hcon ⟨(x, y), hmem, rfl⟩)).eq_of_nhds)

/-- Every first-coordinate slice of a smooth function on `ℝ × ℝ` is smooth. -/
lemma contDiff_slice_fst {f : ℝ × ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (y : ℝ) :
    ContDiff ℝ n (fun x : ℝ => f (x, y)) := by
  have hφ : ContDiff ℝ n (fun x : ℝ => (x, y)) := contDiff_id.prodMk (contDiff_const (c := y))
  exact hf.comp hφ

/-- One-dimensional integration by parts on `ℝ` for a `C¹` function with
compact support. -/
theorem oneDim_ibp_compact {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) :
    ∫ x : ℝ, f x * deriv g x = - ∫ x : ℝ, deriv f x * g x :=
  MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun _x _ => (hf.differentiable_one.differentiableAt).hasDerivAt)
    (fun _x _ => (hg.differentiable_one.differentiableAt).hasDerivAt)
    ((hf.continuous.mul hg.continuous_deriv_one).integrable_of_hasCompactSupport (hfs.mul_right))
    ((hf.continuous_deriv_one.mul hg.continuous).integrable_of_hasCompactSupport (hfs.deriv.mul_right))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hfs.mul_right))

theorem integral_mul_partFst_eq_neg {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) (hv : ContDiff ℝ 1 v) :
    ∫ p : ℝ × ℝ, u p * deriv (fun s : ℝ => v (s, p.2)) p.1
      = - ∫ p : ℝ × ℝ, deriv (fun s : ℝ => u (s, p.2)) p.1 * v p := by
  -- Both integrands are continuous with compact support, hence integrable.
  have hFint : Integrable (fun p : ℝ × ℝ => u p * deriv (fun s : ℝ => v (s, p.2)) p.1) :=
    (hu.continuous.mul (continuous_deriv_slice_fst hv)).integrable_of_hasCompactSupport
      (hus.mul_right)
  have hGint : Integrable (fun p : ℝ × ℝ => deriv (fun s : ℝ => u (s, p.2)) p.1 * v p) :=
    ((continuous_deriv_slice_fst hu).mul hv.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_deriv_slice_fst hu hus).mul_right)
  -- Fubini, written in the order `∫ y ∫ x`.
  have hL : (∫ p : ℝ × ℝ, u p * deriv (fun s : ℝ => v (s, p.2)) p.1)
      = ∫ y : ℝ, ∫ x : ℝ, u (x, y) * deriv (fun s : ℝ => v (s, y)) x :=
    MeasureTheory.integral_prod_symm _ hFint
  have hR : (∫ p : ℝ × ℝ, deriv (fun s : ℝ => u (s, p.2)) p.1 * v p)
      = ∫ y : ℝ, ∫ x : ℝ, deriv (fun s : ℝ => u (s, y)) x * v (x, y) :=
    MeasureTheory.integral_prod_symm _ hGint
  rw [hL, hR]
  -- Integration by parts in `x`, fibre by fibre.
  have hfiber : ∀ y : ℝ, ∫ x : ℝ, u (x, y) * deriv (fun s : ℝ => v (s, y)) x
      = - ∫ x : ℝ, deriv (fun s : ℝ => u (s, y)) x * v (x, y) := fun y =>
    oneDim_ibp_compact (contDiff_slice_fst hu y) (hasCompactSupport_slice_fst hus y)
      (contDiff_slice_fst hv y)
  simp only [hfiber]
  rw [MeasureTheory.integral_neg]

end Work.FTS.StrongEps.KernAux
