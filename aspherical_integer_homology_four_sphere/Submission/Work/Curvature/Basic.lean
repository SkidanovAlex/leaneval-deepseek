import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Curvature of the model metrics on `ℝ⁴`

This file sets up the *model computations* for the curvature chapter of the
aspherical integer homology 4-sphere project.  The blueprint fixes four
coordinate models for the metric on the Ratcliffe–Tschantz manifold `M̂`:

* the upper half space metric `uhsMetric q = (q 3)⁻² • δ` on `{q 3 > 0}` (the
  hyperbolic region);
* the warped metric `warpedMetric f h q = diag(1, f(q 0)², h(q 0)², h(q 0)²)` in
  coordinates `(r, θ, w₁, w₂)` (the filling region);
* the flat metric `flatMetric h₀ q = diag(1, 1, h₀², h₀²)` (the core).

Everything in the chapter is phrased for a *metric field*
`G : E4 → E4 → E4 → ℝ`, i.e. a pointwise symmetric bilinear form written in the
standard coordinates of `E4 = EuclideanSpace ℝ (Fin 4)`.

The three central definitions are:

* `dG G q v a c` — the derivative `D_v (G · a c)` of a metric component;
* `koszulRHS G q a b c` — the right hand side of the Koszul formula
  `½ (D_b(G·a c) + D_a(G·b c) − D_c(G·a b))`;
* `koszulChr G q a b` — the Christoffel symbol `∇_{∂_a} ∂_b` of `G`, defined as the
  unique vector `z` with `G q z c = koszulRHS G q a b c` for all `c`
  (`koszulChr_eq_of_forall` shows that any such `z` is equal to it, so that it can
  be computed by exhibiting a solution);
* `modelCurv G q u v w` — the coordinate vector of the curvature operator
  `R(∂_u, ∂_v) ∂_w`, in the *same index order* as the library computation
  `Submission.ChartCurv.curvVec_eq_chart`, namely
  `∂_u Γ^·_{vw} − ∂_v Γ^·_{uw} + Γ(Γ(w,v), u) − Γ(Γ(w,u), v)`.

## Main results of the chapter (in the companion files)

* `Work.Curvature.uhs_sec` — the UHS model has constant sectional curvature `−1`;
* `Work.Curvature.warped_sec_nonpos` — the warped model has non-positive sectional
  curvature as soon as `f, h > 0`, `f', h' ≥ 0`, `f'', h'' ≥ 0`;
* `Work.Curvature.flat_sec` — the flat model is flat.
-/

open scoped RealInnerProductSpace
open Filter Topology
open Classical

namespace Work.Curvature

noncomputable section

/-- The model space `ℝ⁴` of the blueprint: `E4 := EuclideanSpace ℝ (Fin 4)`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A metric field: a (pointwise) bilinear form on `ℝ⁴`, written in the standard
coordinates as a curried function. -/
abbrev MetricField := E4 → E4 → E4 → ℝ

/-! ## Coordinates -/

/-- The `i`-th coordinate projection of `ℝ⁴`, as a continuous linear map. -/
noncomputable def coord (i : Fin 4) : E4 →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

@[simp] lemma coord_apply (i : Fin 4) (q : E4) : coord i q = q i :=
  PiLp.proj_apply 2 (fun _ : Fin 4 => ℝ) i q

/-- Evaluation of a scalar multiple of a coordinate projection. -/
theorem coord_smul_apply (c : ℝ) (i : Fin 4) (v : E4) :
    ((c • coord i : E4 →L[ℝ] ℝ)) v = c * (v i) := by
  show c • ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) i) v) = c * (v i)
  rw [PiLp.proj_apply]
  rfl

/-- The coordinate functions are differentiable, with derivative the coordinate
projection. -/
theorem hasFDerivAt_coord (i : Fin 4) (q : E4) :
    HasFDerivAt (fun q' : E4 => q' i) (coord i) q := by
  have h : (fun q' : E4 => q' i) = fun q' : E4 => coord i q' := by
    funext q'; rw [coord_apply]
  rw [h]
  exact (coord i).hasFDerivAt

/-- Chain rule for a function of one coordinate: `φ ∘ (coord i)`. -/
theorem hasFDerivAt_comp_coord (φ : ℝ → ℝ) (i : Fin 4) (q : E4) {c : ℝ}
    (hφ : HasDerivAt φ c (q i)) :
    HasFDerivAt (fun q' : E4 => φ (q' i)) (c • coord i) q := by
  have h := hφ.comp_hasFDerivAt q (hasFDerivAt_coord i q)
  simpa [Function.comp_def] using h

/-! ## The three model metrics -/

/-- The upper half space metric `s⁻² • δ` (`s = q 3`), i.e. the hyperbolic metric
on `{q 3 > 0}`. -/
noncomputable def uhsMetric : MetricField := fun q a b => (q 3)⁻¹ ^ 2 * ⟪a, b⟫

/-- The warped metric `diag(1, f(r)², h(r)², h(r)²)` in coordinates
`(r, θ, w₁, w₂)`, `r = q 0`. -/
noncomputable def warpedMetric (f h : ℝ → ℝ) : MetricField :=
  fun q a b => a 0 * b 0 + f (q 0) ^ 2 * (a 1 * b 1)
    + h (q 0) ^ 2 * (a 2 * b 2 + a 3 * b 3)

/-- The flat metric `diag(1, 1, h₀², h₀²)` in Cartesian coordinates. -/
noncomputable def flatMetric (h₀ : ℝ) : MetricField :=
  fun _ a b => a 0 * b 0 + a 1 * b 1 + h₀ ^ 2 * (a 2 * b 2 + a 3 * b 3)

@[simp] lemma uhsMetric_apply (q a b : E4) : uhsMetric q a b = (q 3)⁻¹ ^ 2 * ⟪a, b⟫ := rfl

@[simp] lemma warpedMetric_apply (f h : ℝ → ℝ) (q a b : E4) :
    warpedMetric f h q a b = a 0 * b 0 + f (q 0) ^ 2 * (a 1 * b 1)
      + h (q 0) ^ 2 * (a 2 * b 2 + a 3 * b 3) := rfl

@[simp] lemma flatMetric_apply (h₀ : ℝ) (q a b : E4) :
    flatMetric h₀ q a b = a 0 * b 0 + a 1 * b 1 + h₀ ^ 2 * (a 2 * b 2 + a 3 * b 3) := rfl

/-! ## Positivity -/

/-- Positivity of a sum of four weighted squares. -/
theorem sum_sq_four_pos {g : Fin 4 → ℝ} (hg : ∀ i, 0 < g i) (x : E4) (hx : x ≠ 0) :
    0 < g 0 * x 0 ^ 2 + g 1 * x 1 ^ 2 + g 2 * x 2 ^ 2 + g 3 * x 3 ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 4, x k ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (PiLp.ext h)
  have hle : g k * x k ^ 2 ≤ ∑ i, g i * x i ^ 2 :=
    Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hg i)) (sq_nonneg (x i)))
      (Finset.mem_univ k)
  rw [Fin.sum_univ_four] at hle
  have hpos : 0 < g k * x k ^ 2 := mul_pos (hg k) (sq_pos_of_ne_zero hk)
  linarith

theorem uhsMetric_pos (q : E4) (hq : q 3 ≠ 0) : ∀ x : E4, x ≠ 0 → 0 < uhsMetric q x x := by
  intro x hx
  rw [uhsMetric_apply]
  exact mul_pos (sq_pos_of_ne_zero (inv_ne_zero hq)) (real_inner_self_pos.mpr hx)

theorem warpedMetric_pos (f h : ℝ → ℝ) (hf : ∀ r, 0 < f r) (hh : ∀ r, 0 < h r) (q : E4) :
    ∀ x : E4, x ≠ 0 → 0 < warpedMetric f h q x x := by
  intro x hx
  have hsq : warpedMetric f h q x x
      = 1 * x 0 ^ 2 + f (q 0) ^ 2 * x 1 ^ 2 + h (q 0) ^ 2 * x 2 ^ 2
        + h (q 0) ^ 2 * x 3 ^ 2 := by
    rw [warpedMetric_apply]; ring
  rw [hsq]
  have := sum_sq_four_pos (g := ![1, f (q 0) ^ 2, h (q 0) ^ 2, h (q 0) ^ 2]) ?_ x hx
  · simpa using this
  · intro i
    fin_cases i <;> simp [hf (q 0), hh (q 0)]

/-- Pointwise version of `warpedMetric_pos`: non-vanishing of the warping functions at `q 0`
alone suffices at the point `q`. -/
theorem warpedMetric_pos' (f h : ℝ → ℝ) (q : E4) (hf : f (q 0) ≠ 0) (hh : h (q 0) ≠ 0) :
    ∀ x : E4, x ≠ 0 → 0 < warpedMetric f h q x x := by
  intro x hx
  have hsq : warpedMetric f h q x x
      = 1 * x 0 ^ 2 + f (q 0) ^ 2 * x 1 ^ 2 + h (q 0) ^ 2 * x 2 ^ 2
        + h (q 0) ^ 2 * x 3 ^ 2 := by
    rw [warpedMetric_apply]; ring
  rw [hsq]
  have := sum_sq_four_pos (g := ![1, f (q 0) ^ 2, h (q 0) ^ 2, h (q 0) ^ 2]) ?_ x hx
  · simpa using this
  · intro i
    fin_cases i <;> simp [sq_pos_of_ne_zero hf, sq_pos_of_ne_zero hh]

theorem flatMetric_pos (h₀ : ℝ) (h0 : h₀ ≠ 0) (q : E4) :
    ∀ x : E4, x ≠ 0 → 0 < flatMetric h₀ q x x := by
  intro x hx
  have hsq : flatMetric h₀ q x x
      = 1 * x 0 ^ 2 + 1 * x 1 ^ 2 + h₀ ^ 2 * x 2 ^ 2 + h₀ ^ 2 * x 3 ^ 2 := by
    rw [flatMetric_apply]; ring
  rw [hsq]
  have := sum_sq_four_pos (g := ![1, 1, h₀ ^ 2, h₀ ^ 2]) ?_ x hx
  · simpa using this
  · intro i
    fin_cases i <;> simp [sq_pos_of_ne_zero h0]

/-! ## Linearity -/

theorem uhsMetric_sub_fst (q x y c : E4) :
    uhsMetric q (x - y) c = uhsMetric q x c - uhsMetric q y c := by
  simp [uhsMetric_apply, inner_sub_left, mul_sub]

theorem warpedMetric_sub_fst (f h : ℝ → ℝ) (q x y c : E4) :
    warpedMetric f h q (x - y) c = warpedMetric f h q x c - warpedMetric f h q y c := by
  simp only [warpedMetric_apply, PiLp.sub_apply, sub_mul]
  ring

theorem flatMetric_sub_fst (h₀ : ℝ) (q x y c : E4) :
    flatMetric h₀ q (x - y) c = flatMetric h₀ q x c - flatMetric h₀ q y c := by
  simp only [flatMetric_apply, PiLp.sub_apply, sub_mul]
  ring

/-! ## The Koszul formula and the Christoffel symbol -/

/-- The derivative of the metric component `G · a c` in the direction `v`. -/
noncomputable def dG (G : MetricField) (q v a c : E4) : ℝ :=
  fderiv ℝ (fun q' : E4 => G q' a c) q v

/-- The right hand side of the Koszul formula. -/
noncomputable def koszulRHS (G : MetricField) (q a b c : E4) : ℝ :=
  (2 : ℝ)⁻¹ * (dG G q b a c + dG G q a b c - dG G q c a b)

/-- The Christoffel symbol of `G`, defined as the vector solving the Koszul
formula against the metric. -/
noncomputable def koszulChr (G : MetricField) (q a b : E4) : E4 := by
  classical
  exact if h : ∃ z : E4, ∀ c, G q z c = koszulRHS G q a b c then Classical.choose h else 0

theorem koszulChr_spec {G : MetricField} {q a b : E4}
    (h : ∃ z : E4, ∀ c, G q z c = koszulRHS G q a b c) :
    ∀ c, G q (koszulChr G q a b) c = koszulRHS G q a b c := by
  rw [koszulChr, dif_pos h]
  exact Classical.choose_spec h

/-- **Uniqueness / computation rule** for `koszulChr`: it suffices to exhibit a
vector `z` satisfying the Koszul formula against the (positive definite) metric. -/
theorem koszulChr_eq_of_forall {G : MetricField} {q a b z : E4}
    (hlin : ∀ x y c, G q (x - y) c = G q x c - G q y c)
    (hpos : ∀ x : E4, x ≠ 0 → 0 < G q x x)
    (hz : ∀ c, G q z c = koszulRHS G q a b c) :
    koszulChr G q a b = z := by
  have hspec := koszulChr_spec (G := G) (q := q) (a := a) (b := b) ⟨z, hz⟩
  by_contra hne
  have h1 : G q (koszulChr G q a b - z) (koszulChr G q a b - z)
      = koszulRHS G q a b (koszulChr G q a b - z) - koszulRHS G q a b (koszulChr G q a b - z) := by
    rw [hlin, hspec, hz]
  rw [sub_self] at h1
  exact absurd h1 (ne_of_gt (hpos _ (sub_ne_zero.mpr hne)))

/-! ## The model curvature -/

/-- The derivative of the Christoffel symbol `q ↦ ∇_{∂_a} ∂_b` in the direction `d`. -/
noncomputable def dBmodel (G : MetricField) (q d a b : E4) : E4 :=
  fderiv ℝ (fun q' : E4 => koszulChr G q' a b) q d

/-- **The model curvature**: the coordinate vector of `R(∂_u, ∂_v) ∂_w`, in the index
order of `Submission.ChartCurv.curvVec_eq_chart`
(`∂_u Γ^·_{vw} − ∂_v Γ^·_{uw} + Γ(Γ(w,v), u) − Γ(Γ(w,u), v)`). -/
noncomputable def modelCurv (G : MetricField) (q u v w : E4) : E4 :=
  dBmodel G q u w v - dBmodel G q v w u
    + koszulChr G q (koszulChr G q w v) u - koszulChr G q (koszulChr G q w u) v

/-! ## The explicit Christoffel symbols of the model metrics -/

/-- **`G` has non-positive sectional curvature at the point `q`**: the sectional curvature
numerator `⟨R(u,v)v, u⟩ = G q (modelCurv G q u v v) u` is `≤ 0` for all tangent vectors `u`, `v`.
This is the pointwise form in which the model inequalities are fed to the bridge to the
Cartan–Hadamard machinery (`uhs_sec`/`warped_sec_nonpos`/`flat_sec` are its producers). -/
def SecNonposAt (G : MetricField) (q : E4) : Prop :=
  ∀ u v : E4, G q (modelCurv G q u v v) u ≤ 0

/-- The conformal factor of the Christoffel symbol of the UHS metric:
`Γ(∇_{∂_a} ∂_b) = s⁻¹ • chrUHSvec a b`, `s = q 3`. -/
noncomputable def chrUHSvec (a b : E4) : E4 :=
  !₂[-(a 0 * b 3 + a 3 * b 0), -(a 1 * b 3 + a 3 * b 1), -(a 2 * b 3 + a 3 * b 2),
    a 0 * b 0 + a 1 * b 1 + a 2 * b 2 - a 3 * b 3]

/-- The Christoffel symbol of `uhsMetric`: with `s = q 3`,
`Γ^k_{ab} = −s⁻¹ (a_k b_3 + a_3 b_k)` for `k < 3` and
`Γ^3_{ab} = s⁻¹ (a₀b₀ + a₁b₁ + a₂b₂ − a₃b₃)`. -/
noncomputable def chrUHS (q a b : E4) : E4 := (q 3)⁻¹ • chrUHSvec a b

/-- The Christoffel symbol of `warpedMetric f h`. -/
noncomputable def chrWarped (f h : ℝ → ℝ) (q a b : E4) : E4 :=
  !₂[-(deriv f (q 0) * f (q 0)) * (a 1 * b 1)
        - (deriv h (q 0) * h (q 0)) * (a 2 * b 2 + a 3 * b 3),
    (deriv f (q 0) / f (q 0)) * (a 0 * b 1 + a 1 * b 0),
    (deriv h (q 0) / h (q 0)) * (a 0 * b 2 + a 2 * b 0),
    (deriv h (q 0) / h (q 0)) * (a 0 * b 3 + a 3 * b 0)]

/-- The `s`-derivative of `chrUHS`: `∂_s (s⁻¹ • V) = s⁻² • chrUHSderiv d a b` along a
direction `d` with `d 3 = ds`. -/
noncomputable def chrUHSderiv (d a b : E4) : E4 := -(d 3) • chrUHSvec a b

/-- The derivative of the warped Christoffel symbol `chrWarped f h · a b` with respect to
`r = q 0`. -/
noncomputable def chrWarpedDeriv (f h : ℝ → ℝ) (r : ℝ) (a b : E4) : E4 :=
  !₂[-((deriv^[2] f r * f r + deriv f r ^ 2) * (a 1 * b 1)
        + (deriv^[2] h r * h r + deriv h r ^ 2) * (a 2 * b 2 + a 3 * b 3)),
    ((deriv^[2] f r * f r - deriv f r ^ 2) / f r ^ 2) * (a 0 * b 1 + a 1 * b 0),
    ((deriv^[2] h r * h r - deriv h r ^ 2) / h r ^ 2) * (a 0 * b 2 + a 2 * b 0),
    ((deriv^[2] h r * h r - deriv h r ^ 2) / h r ^ 2) * (a 0 * b 3 + a 3 * b 0)]

end

end Work.Curvature
