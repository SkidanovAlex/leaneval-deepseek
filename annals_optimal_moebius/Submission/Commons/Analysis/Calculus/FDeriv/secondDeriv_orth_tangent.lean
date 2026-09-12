import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
import Submission.Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually

/-!
# Second derivatives of an orthonormal-coordinate parametrization are normal

Let `f : E → F` (codomain `F` a real inner product space) be twice
continuously differentiable on an open set `s`, and fix two directions
`u v : E`.  Assume that on `s` the two coordinate tangent fields are unit
and orthogonal:

  `‖fderiv f y u‖ = 1`, `‖fderiv f y v‖ = 1`, `⟪fderiv f y u, fderiv f y v⟫ = 0`.

Then at any `x ∈ s` the second directional derivatives have no tangential
part, i.e. they are orthogonal to both tangent fields:

  (a) `⟪∂u (∂u f) x, df v x⟫ = 0`, i.e. `f_uu ⊥ f_v`
  (b) `⟪∂v (∂u f) x, df u x⟫ = 0` and `⟪∂v (∂u f) x, df v x⟫ = 0` (`f_uv` normal)
  (c) `⟪∂v (∂v f) x, df u x⟫ = 0` (`f_vv ⊥ f_u`)

where `∂a g x := fderiv ℝ g x a`.  Each claim follows by differentiating the
corresponding constant inner product: e.g. `‖df u‖² = 1` gives
`⟪fderiv (fun y => fderiv f y u) x u, fderiv f x u⟫ = 0`, and
`⟪df u, df v⟫ = 0` differentiated in direction `u` gives
`⟪f_uu, f_v⟫ + ⟪f_u, f_uv⟫ = 0` combined with `⟪f_u, f_uv⟫ = 0` (from
`‖df u‖² = 1`).  Use `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean` and
`ContDiffOn` machinery for differentiability of `fderiv`, and the commons
result `Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually`.
-/

open scoped ContDiff
open Topology

noncomputable section
namespace Commons.Analysis.Calculus.FDeriv

/-- Differentiating `‖fderiv f · w‖² = 1` in any direction `a` shows the
second directional derivative `∂a (∂w f)` is orthogonal to the tangent
field `∂w f`. -/
theorem inner_second_self {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s) (w a : E)
    (hw_unit : ∀ y ∈ s, ‖fderiv ℝ f y w‖ = 1) :
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y w) x a) (fderiv ℝ f x w) = 0 := by
  -- `fun y ↦ fderiv f y w` is differentiable at `x` (f is C² on an open set).
  have hcontAt : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
  have hfdiff_clm : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x := by
    exact (hcontAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdiff : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y w) x := by
    exact DifferentiableAt.clm_apply (𝕜 := ℝ) hfdiff_clm (differentiableAt_const w)
  -- On a neighbourhood of `x` (namely `s`) the inner product is constantly 1.
  have hevent :
      (fun y : E => inner ℝ (fderiv ℝ f y w) (fderiv ℝ f y w)) =ᶠ[𝓝 x]
        (fun _ : E => (1 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    have hnorm := hw_unit y hy
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num
  -- ... hence its derivative in direction `a` vanishes.
  have hzero : fderiv ℝ (fun y : E => inner ℝ (fderiv ℝ f y w) (fderiv ℝ f y w)) x a = 0 := by
    rw [hevent.fderiv_eq]
    simp
  -- Product rule for the inner product.
  have hprod := fderiv_inner_apply ℝ hdiff hdiff a
  -- hprod : fderiv ℝ (fun y => inner ℝ (df y w) (df y w)) x a
  --       = inner ℝ (df x w) (fderiv (fun y => df y w) x a)
  --       + inner ℝ (fderiv (fun y => df y w) x a) (df x w)
  rw [hzero] at hprod
  rw [real_inner_comm] at hprod
  -- hprod : 0 = c + c where c is the target inner product.
  have hsum : inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y w) x a) (fderiv ℝ f x w) +
      inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y w) x a) (fderiv ℝ f x w) = 0 := by
    simpa using hprod.symm
  linarith

/-- Differentiating the (identically zero) inner product `⟪∂w f, ∂z f⟫` in
the direction `a` gives the product-rule identity
`⟪∂a (∂w f), ∂z f⟫ + ⟪∂w f, ∂a (∂z f)⟫ = 0`. -/
theorem inner_second_mixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s) (w z a : E)
    (hzw : ∀ y ∈ s, inner ℝ (fderiv ℝ f y w) (fderiv ℝ f y z) = 0) :
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y w) x a) (fderiv ℝ f x z)
      + inner ℝ (fderiv ℝ f x w) (fderiv ℝ (fun y : E => fderiv ℝ f y z) x a) = 0 := by
  have hcontAt : ContDiffAt ℝ 2 f x := hf.contDiffAt (hs.mem_nhds hx)
  have hfdiff_clm : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x := by
    exact (hcontAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdiff_w : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y w) x := by
    exact DifferentiableAt.clm_apply (𝕜 := ℝ) hfdiff_clm (differentiableAt_const w)
  have hdiff_z : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y z) x := by
    exact DifferentiableAt.clm_apply (𝕜 := ℝ) hfdiff_clm (differentiableAt_const z)
  have hevent :
      (fun y : E => inner ℝ (fderiv ℝ f y w) (fderiv ℝ f y z)) =ᶠ[𝓝 x]
        (fun _ : E => (0 : ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hzw y hy
  exact Commons.Analysis.InnerProductSpace.fderiv_inner_zero_of_eventually
    (E := F) (G := E) hdiff_w hdiff_z hevent a

/-- Second derivatives of an orthonormal-coordinate parametrization are
normal (no tangential component). -/
theorem secondDeriv_orth_tangent {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    {u v : E} (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s)
    (hu_unit : ∀ y ∈ s, ‖fderiv ℝ f y u‖ = 1)
    (hv_unit : ∀ y ∈ s, ‖fderiv ℝ f y v‖ = 1)
    (huv : ∀ y ∈ s, inner ℝ (fderiv ℝ f y u) (fderiv ℝ f y v) = 0) :
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x v) (fderiv ℝ f x v) = 0 ∧
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x v) (fderiv ℝ f x u) = 0 ∧
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x u) (fderiv ℝ f x v) = 0 ∧
    inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y v) x v) (fderiv ℝ f x u) = 0 := by
  -- mixed second partials commute (f is C² on the open set `s`)
  have hsym := secondDirectional_commute_two (s := s) (f := f) (x := x) hs hx hf u v
  -- hsym : fderiv ℝ (fun y => fderiv f y u) x v = fderiv ℝ (fun y => fderiv f y v) x u
  -- normalising `∂v (∂u f) ⊥ f_v` : rotate `∂v (∂v f) ⊥ f_v` (from
  -- `‖f_v‖ = 1`) with the symmetry of mixed partials.
  have h1 : inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x v) (fderiv ℝ f x v) = 0 := by
    have h := inner_second_self hs hx hf v u hv_unit
    rw [← hsym] at h
    exact h
  -- `∂v (∂u f) ⊥ f_u` comes directly from `‖f_u‖ = 1` differentiated in `v`.
  have h2 : inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x v) (fderiv ℝ f x u) = 0 := by
    exact inner_second_self hs hx hf u v hu_unit
  -- `∂u (∂u f) ⊥ f_v`: differentiate `⟪f_u, f_v⟫ = 0` in direction `u` and
  -- use `h2` (via the symmetry of mixed partials).
  have h3 : inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y u) x u) (fderiv ℝ f x v) = 0 := by
    have hsum := inner_second_mixed hs hx hf u v u huv
    -- hsum : ⟪∂u (∂u f), ∂v f⟫ + ⟪∂u f, ∂u (∂v f)⟫ = 0
    have hzero2 : inner ℝ (fderiv ℝ f x u) (fderiv ℝ (fun y : E => fderiv ℝ f y v) x u) = 0 := by
      rw [← hsym]
      rw [real_inner_comm]
      exact h2
    rw [hzero2] at hsum
    simpa using hsum
  -- `∂v (∂v f) ⊥ f_u`: differentiate `⟪f_u, f_v⟫ = 0` in direction `v` and
  -- use `h1`.
  have h4 : inner ℝ (fderiv ℝ (fun y : E => fderiv ℝ f y v) x v) (fderiv ℝ f x u) = 0 := by
    have hsum := inner_second_mixed hs hx hf u v v huv
    -- hsum : ⟪∂v (∂u f), ∂v f⟫ + ⟪∂u f, ∂v (∂v f)⟫ = 0
    rw [h1] at hsum
    have h4' : inner ℝ (fderiv ℝ f x u) (fderiv ℝ (fun y : E => fderiv ℝ f y v) x v) = 0 := by
      simpa using hsum
    rw [real_inner_comm] at h4'
    exact h4'
  exact ⟨h1, h2, h3, h4⟩

end Commons.Analysis.Calculus.FDeriv