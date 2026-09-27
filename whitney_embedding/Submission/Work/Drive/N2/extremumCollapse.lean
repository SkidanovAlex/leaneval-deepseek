import Mathlib
import Submission.Work.Drive.N2.ModelDefs
import Submission.Work.Drive.N2.gapDrawing_extremum_chart

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The extremum window: the radial-collapse model block

`NOTES_S2_window_assembly_interface_placement.md` §7 fixes the shape of the missing window block of
the movie route: the model piece has to be used on a *spatial* set `D` (a neighbourhood of the
critical point together with the trapped trajectories), and it has to be **constant along the flow
trajectories on a neighbourhood of `∂D`**, so that it can be glued (`goodDrawingOn_of_pieces`) to a
*transported* drawing, which is automatically trajectory-constant.

For an **extremum** this is cheap: the flow lines of the model field `u' = chartMult (‖u‖²) • u`
are the *rays* through the critical point, and the natural trajectory-constant drawing of a level
set of `f = c₀ + s ‖u‖²` is the *direction* `u / ‖u‖`.  The drawing

    g x = incl23 (μ (‖φ x‖²) • φ x)

with a profile `μ` which is `1` near the critical point and `1 / ‖u‖` outside a fixed radius does
both jobs at once:

* near the critical point `μ = 1` and `g` is the chart model `incl23 ∘ φ`, hence smooth with an
  injective differential at the critical point (rank `2`);
* on the annulus `{b ≤ ‖φ ·‖}`, `μ (‖u‖²) = 1 / ‖u‖` and `g` is the direction map, constant along
  every ray, in the explicit form `g x = incl23 ((‖φ x‖)⁻¹ • φ x)`;
* on every sphere `‖φ ·‖ = const` the map is `φ` scaled by the constant `μ (‖φ ·‖²) ≠ 0`, hence
  injective; and its differential on `ker (df)` (the tangent of the sphere, i.e. `⟪φ x, ·⟫ = 0`) is
  the same scaling, hence injective.

This file proves those rows, so that the extremum window block can be assembled from it exactly as
`Work.Drive.N2.saddleWindowAssembly` assembles the saddle window.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The two coordinates of a point of `ℝ²` add up to its squared norm. -/
lemma coord_sq_eq_norm_sq (v : EuclideanSpace ℝ (Fin 2)) :
    (v 0) ^ 2 + (v 1) ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two]

/-- The **radial-collapse drawing** of a chart: the chart coordinate `φ x` is scaled by the profile
`μ` evaluated at `‖φ x‖²`.  With `μ = 1` near the origin and `μ t = t ^ (-1/2)` far out, this is
the chart model near the critical point and the direction map on the outer annulus. -/
noncomputable def extremumCollapse (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (μ : ℝ → ℝ) : M → EuclideanSpace ℝ (Fin 3) :=
  fun x => incl23 (μ (‖φ x‖ ^ 2) • φ x)

/-- The extremum model is the norm form `c₀ + s ‖v‖²`. -/
lemma extremumModel_eq (c₀ s : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2) = c₀ + s * ‖v‖ ^ 2 := by
  rw [coord_sq_eq_norm_sq]

/-- The extremum model is smooth. -/
lemma contDiff_extremumModel (c₀ s : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2)) := by
  have h : (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2))
      = fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ‖v‖ ^ 2 := by
    funext v
    exact extremumModel_eq c₀ s v
  rw [h]
  exact contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))

/-- The radial scaling `v ↦ μ (‖v‖²) • v` is smooth when `μ` is. -/
lemma contDiff_radialScale (μ : ℝ → ℝ) (hμ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) :=
  (hμ.comp (contDiff_norm_sq ℝ)).smul contDiff_id

/-- **The derivative of the radial scaling `v ↦ μ (‖v‖²) • v`.**  The profile contributes only the
*radial* direction `w`, so on the tangent of a sphere (where `⟪w, u⟫ = 0`) the derivative is just
the scalar multiple `μ (‖w‖²) • u`. -/
lemma fderiv_radialScale_apply (μ : ℝ → ℝ) (w u : EuclideanSpace ℝ (Fin 2))
    (hμ : DifferentiableAt ℝ μ (‖w‖ ^ 2)) :
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) w u
      = μ (‖w‖ ^ 2) • u + (deriv μ (‖w‖ ^ 2) * (2 * inner ℝ w u)) • w := by
  have hns : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ 2)
      (2 • innerSL ℝ w) w := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hc : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2))
      ((fderiv ℝ μ (‖w‖ ^ 2)).comp (2 • innerSL ℝ w)) w :=
    (hμ.hasFDerivAt).comp w hns
  have hid : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) w := hasFDerivAt_id w
  have h := hc.smul hid
  have hfd : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) w
      = μ (‖w‖ ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))
        + ((fderiv ℝ μ (‖w‖ ^ 2)).comp (2 • innerSL ℝ w)).smulRight w := h.fderiv
  have hscal : ∀ r : ℝ, (fderiv ℝ μ (‖w‖ ^ 2)) r = r * deriv μ (‖w‖ ^ 2) := by
    intro r
    have h1 : (fderiv ℝ μ (‖w‖ ^ 2)) 1 = deriv μ (‖w‖ ^ 2) := fderiv_apply_one_eq_deriv
    have h2 : (fderiv ℝ μ (‖w‖ ^ 2)) (r • (1 : ℝ)) = r • ((fderiv ℝ μ (‖w‖ ^ 2)) 1) :=
      map_smul _ r 1
    rw [smul_eq_mul, mul_one] at h2
    rw [h2, h1, smul_eq_mul]
  rw [hfd]
  simp only [ContinuousLinearMap.add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [hscal]
  ring

/-- **The derivative of the extremum model.**  At `w` it is `2 s ⟪w, ·⟫`. -/
lemma fderiv_extremumModel_apply (c₀ s : ℝ) (w u : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2)) w u
      = 2 * s * inner ℝ w u := by
  have h : (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2))
      = fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ‖v‖ ^ 2 := by
    funext v
    exact extremumModel_eq c₀ s v
  rw [h]
  have hd : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ‖v‖ ^ 2)
      (s • (2 • innerSL ℝ w)) w := by
    have h1 := (((hasStrictFDerivAt_norm_sq w).hasFDerivAt).const_mul s).const_add c₀
    simpa [smul_smul] using h1
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- **The derivative of the extremum model, in `mfderiv` form.** -/
lemma mfderiv_extremumModel_apply (c₀ s : ℝ) (w u : EuclideanSpace ℝ (Fin 2)) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2)) w u
      = 2 * s * inner ℝ w u := by
  have hmeq : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2)) w
      = fderiv ℝ
        (fun v : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((v 0) ^ 2 + (v 1) ^ 2)) w :=
    mfderiv_eq_fderiv
  rw [hmeq]
  exact fderiv_extremumModel_apply c₀ s w u

/-- **The derivative of the radial scaling, in `mfderiv` form.** -/
lemma mfderiv_radialScale_apply (μ : ℝ → ℝ) (w u : EuclideanSpace ℝ (Fin 2))
    (hμ : DifferentiableAt ℝ μ (‖w‖ ^ 2)) :
    mfderiv (𝓡 2) (𝓡 2) (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) w u
      = μ (‖w‖ ^ 2) • u + (deriv μ (‖w‖ ^ 2) * (2 * inner ℝ w u)) • w := by
  have hmeq : mfderiv (𝓡 2) (𝓡 2)
        (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) w
      = fderiv ℝ (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) w :=
    mfderiv_eq_fderiv
  rw [hmeq]
  exact fderiv_radialScale_apply μ w u hμ

/-- **The extremum window model block (radial collapse).**

`φ` is a chart around an extremum on whose source `f` is the model `c₀ + s ((φ·0)² + (φ·1)²)` with
`s = ±1`; `μ` is a smooth positive profile which is `1` on `[0, a²]` and `1/√t` on `[b², ∞)`
(`0 < a ≤ b`); `U` is an open set of the chart source carrying the model piece.  Then
`x ↦ incl23 (μ (‖φ x‖²) • φ x)` satisfies, on `U`:

* smoothness;
* injectivity on the level sets of `f` (inside `U`);
* injectivity of the differential on `ker (df)`;
* on the annulus `{b ≤ ‖φ ·‖}` it is the direction map `incl23 ((‖φ ·‖)⁻¹ • φ ·)`, hence constant
  on every ray through the critical point — i.e. constant along the flow trajectories of the model
  field `u' = chartMult (‖u‖²) • u` — which is exactly the row that lets it be glued to a
  transported drawing. -/
theorem extremumCollapseBlock (f : M → ℝ)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (c₀ s : ℝ)
    (hs : s = 1 ∨ s = -1) (U : Set M) (hU : IsOpen U) (hUsrc : U ⊆ φ.source)
    (hφsm : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    (hφsymm : ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => φ.symm z) φ.target)
    (hmodel : ∀ y ∈ φ.source, f y = c₀ + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2))
    (μ : ℝ → ℝ) (hμsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hμpos : ∀ t, 0 < μ t)
    {a b : ℝ} (hab : 0 < a) (hab' : a ≤ b)
    (hμone : ∀ t, t ≤ a ^ 2 → μ t = 1)
    (hμinv : ∀ t, b ^ 2 ≤ t → μ t = 1 / Real.sqrt t) :
    (∀ x ∈ U, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (extremumCollapse φ μ) x) ∧
    (∀ x ∈ U, ∀ y ∈ U, f x = f y → extremumCollapse φ μ x = extremumCollapse φ μ y → x = y) ∧
    (∀ x ∈ U, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (extremumCollapse φ μ) x v = 0 → v = 0) ∧
    (∀ x ∈ U, b ≤ ‖φ x‖ → extremumCollapse φ μ x = incl23 ((‖φ x‖)⁻¹ • φ x)) ∧
    (∀ x ∈ U, b ≤ ‖φ x‖ → ∀ y ∈ U, b ≤ ‖φ y‖ →
      (∃ c : ℝ, 0 < c ∧ φ y = c • φ x) →
      extremumCollapse φ μ y = extremumCollapse φ μ x) := by
  have hφAt : ∀ x ∈ U, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) x :=
    fun x hx => hφsm.contMDiffAt ((φ.open_source).mem_nhds (hUsrc hx))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro x hx
    have hF : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : EuclideanSpace ℝ (Fin 2) => μ (‖v‖ ^ 2) • v) (φ x) :=
      (contDiff_radialScale μ hμsm).contMDiff.contMDiffAt
    have h1 : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => μ (‖φ y‖ ^ 2) • φ y) x := hF.comp x (hφAt x hx)
    exact (incl23.contMDiff.contMDiffAt).comp x h1
  · -- injectivity on the level sets
    intro x hx y hy hf hg
    have hval : μ (‖φ x‖ ^ 2) • φ x = μ (‖φ y‖ ^ 2) • φ y := incl23_inj hg
    have hnorm2 : ‖φ x‖ ^ 2 = ‖φ y‖ ^ 2 := by
      have h2 := hf
      rw [hmodel x (hUsrc hx), hmodel y (hUsrc hy), coord_sq_eq_norm_sq,
        coord_sq_eq_norm_sq] at h2
      rcases hs with h | h <;> rw [h] at h2 <;> linarith
    have hμne : μ (‖φ x‖ ^ 2) ≠ 0 := ne_of_gt (hμpos _)
    have hφxy : φ x = φ y := by
      have h2 : μ (‖φ x‖ ^ 2) • φ x = μ (‖φ x‖ ^ 2) • φ y := by
        rw [hval, hnorm2]
      exact smul_right_injective _ hμne h2
    exact φ.injOn (hUsrc hx) (hUsrc hy) hφxy
  · -- the differential is injective on `ker (df)`
    intro x hx v hfv hgv
    have hxs : x ∈ φ.source := hUsrc hx
    have hφmd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y => φ y) x :=
      (hφAt x hx).mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt (𝓡 2) (𝓡 2)
        (fun w : EuclideanSpace ℝ (Fin 2) => μ (‖w‖ ^ 2) • w) (φ x) :=
      ((contDiff_radialScale μ hμsm).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
    have hQmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
        (fun w : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((w 0) ^ 2 + (w 1) ^ 2)) (φ x) :=
      ((contDiff_extremumModel c₀ s).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
    have hHmd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y : M => μ (‖φ y‖ ^ 2) • φ y) x :=
      hFmd.comp x hφmd
    set u : EuclideanSpace ℝ (Fin 2) := mfderiv (𝓡 2) (𝓡 2) (fun y : M => φ y) x v with hu
    -- (a) the collapse is `incl23` after the radial scale
    have hcoll_v : mfderiv (𝓡 2) (𝓡 3) (extremumCollapse φ μ) x v
        = incl23 (mfderiv (𝓡 2) (𝓡 2)
            (fun w : EuclideanSpace ℝ (Fin 2) => μ (‖w‖ ^ 2) • w) (φ x) u) := by
      rw [show mfderiv (𝓡 2) (𝓡 3) (extremumCollapse φ μ) x v
          = mfderiv (𝓡 2) (𝓡 3)
              ((incl23 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) ∘
                fun y : M => μ (‖φ y‖ ^ 2) • φ y) x v from rfl]
      have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := fun y : M => μ (‖φ y‖ ^ 2) • φ y)
        (g := (incl23 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))) (x := x)
        incl23.mdifferentiableAt hHmd v
      rw [hcomp, ContinuousLinearMap.mfderiv_eq]
      congr 1
      rw [show mfderiv (𝓡 2) (𝓡 2) (fun y : M => μ (‖φ y‖ ^ 2) • φ y) x v
          = mfderiv (𝓡 2) (𝓡 2)
              ((fun w : EuclideanSpace ℝ (Fin 2) => μ (‖w‖ ^ 2) • w) ∘
                (fun y : M => φ y)) x v from rfl]
      exact mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
        (f := fun y : M => φ y) (g := fun w : EuclideanSpace ℝ (Fin 2) => μ (‖w‖ ^ 2) • w)
        (x := x) hFmd hφmd v
    -- (b) the `df`-condition says `⟪φ x, u⟫ = 0`
    have hinner : inner ℝ (φ x) u = 0 := by
      have hev : f =ᶠ[𝓝 x]
          (fun y : M => c₀ + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2)) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hmodel y (hUsrc hy)
      have h1p : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun y : M => c₀ + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2)) x v = 0 := by
        have hfv' := hfv
        rw [hev.mfderiv_eq] at hfv'
        exact hfv'
      have h1' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          ((fun w : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((w 0) ^ 2 + (w 1) ^ 2)) ∘
            (fun y : M => φ y)) x v = 0 := h1p
      have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
        (f := fun y : M => φ y)
        (g := fun w : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((w 0) ^ 2 + (w 1) ^ 2))
        (x := x) hQmd hφmd v
      have h3 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun w : EuclideanSpace ℝ (Fin 2) => c₀ + s * ((w 0) ^ 2 + (w 1) ^ 2)) (φ x) u = 0 := by
        rw [hcomp] at h1'
        exact h1'
      have h4 : 2 * s * inner ℝ (φ x) u = 0 := by
        rw [← mfderiv_extremumModel_apply c₀ s (φ x) u]
        exact h3
      have hsne : 2 * s ≠ 0 := by
        rcases hs with h | h <;> rw [h] <;> norm_num
      exact (mul_eq_zero.mp h4).resolve_left hsne
    -- (c) conclude
    rw [hcoll_v] at hgv
    rw [mfderiv_radialScale_apply μ (φ x) u
      (hμsm.differentiable (by simp)).differentiableAt] at hgv
    rw [hinner] at hgv
    simp only [mul_zero, zero_smul, add_zero] at hgv
    have hw : u = 0 := by
      have hμne : μ (‖φ x‖ ^ 2) ≠ 0 := ne_of_gt (hμpos _)
      exact (smul_eq_zero.mp (incl23_inj (by simpa using hgv))).resolve_left hμne
    rw [hu] at hw
    exact mfderiv_chart_injective hφsm hφsymm hxs (by rw [hw, map_zero])
  · -- the annulus: the collapse is the direction map
    intro x hx hb
    have hb0 : 0 ≤ ‖φ x‖ := norm_nonneg _
    have hb2 : b ^ 2 ≤ ‖φ x‖ ^ 2 := by nlinarith
    have hμx : μ (‖φ x‖ ^ 2) = (‖φ x‖)⁻¹ := by
      rw [hμinv _ hb2, Real.sqrt_sq hb0, one_div]
    rw [extremumCollapse, hμx]
  · -- constancy on the rays
    intro x hx hb y hy hyb ⟨c, hc, hcy⟩
    have hny : ‖φ y‖ = c * ‖φ x‖ := by
      rw [hcy, norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
    have hb2 : b ^ 2 ≤ ‖φ x‖ ^ 2 := by
      have h0 : 0 ≤ ‖φ x‖ := norm_nonneg _
      nlinarith
    have hb2' : b ^ 2 ≤ ‖φ y‖ ^ 2 := by
      have h0 : 0 ≤ ‖φ y‖ := norm_nonneg _
      nlinarith
    have hμx : μ (‖φ x‖ ^ 2) = (‖φ x‖)⁻¹ := by
      rw [hμinv _ hb2, Real.sqrt_sq (norm_nonneg _), one_div]
    have hμy : μ (‖φ y‖ ^ 2) = (‖φ y‖)⁻¹ := by
      rw [hμinv _ hb2', Real.sqrt_sq (norm_nonneg _), one_div]
    have harg : (‖φ y‖)⁻¹ • φ y = (‖φ x‖)⁻¹ • φ x := by
      rw [hny, hcy, smul_smul]
      congr 1
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), mul_one]
    rw [extremumCollapse, extremumCollapse, hμx, hμy, harg]

end Work.Drive.N2
