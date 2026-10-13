/-
The **Leibniz rule (product rule) for the Laplacian on tempered distributions**:

  `Δ (g · u) = g · Δ u + 2 • ((∂_{e₀} g) · ∂_{e₀} u + (∂_{e₁} g) · ∂_{e₁} u) + (Δ g) · u`,

for a multiplier `g` of temperate growth whose first derivatives `d0 g`, `d1 g` and whose
(pointwise) Laplacian `lapF g = ∂_{e₀}∂_{e₀} g + ∂_{e₁}∂_{e₁} g` are of temperate growth, and any
tempered distribution `u`.

The proof is a test-function computation.  Writing `S h` for the multiplication operator
`TemperedDistribution.smulLeftCLM ℂ h` and `∂_m` for `LineDeriv.lineDerivOp m`, the two elementary
dualities

* `(Δ w) φ = w (Δ φ)`  (`TemperedDistribution.laplacian_apply_apply`),
* `(∂_m w) φ = w (-∂_m φ)`  (`TemperedDistribution.lineDerivOp_apply_apply`),
* `(S h w) φ = w (h · φ)`  (`TemperedDistribution.smulLeftCLM_apply_apply`)

reduce the statement, for each test function `φ`, to the *pointwise* Leibniz rule

  `∂_{e₀}∂_{e₀}(g φ) + ∂_{e₁}∂_{e₁}(g φ) = g · Δφ + 2 (∂_{e₀}g ∂_{e₀}φ + ∂_{e₁}g ∂_{e₁}φ) + (Δg) φ`

for the product of the smooth multiplier `g` with the Schwartz function `φ`.  That identity is
proved here as an identity of Schwartz maps (`schwartzMap_laplacian_smulLeftCLM`) by evaluating
both sides pointwise: the only inputs are `SchwartzMap.laplacian_eq_sum` in the orthonormal basis
`EuclideanSpace.basisFun (Fin 2) ℝ` (whose two vectors are `e0` and `e1`), the coercion lemma
`SchwartzMap.lineDerivOp_apply`, and two applications of the pointwise product rule for
`lineDeriv` (`lineDeriv_mul_eq`).

Note that the `2` in the statement is a *natural* scalar (the `nsmul` of the additive group of
tempered distributions), which is why the final linearity bookkeeping uses `map_nsmul` /
`nsmul_eq_mul`.
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.lineDerivOp_smulLeftCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory TemperedDistribution Filter Set
open scoped SchwartzMap LineDeriv Laplacian

set_option maxHeartbeats 1000000

/-! ### Elementary pointwise calculus on `E2` -/

/-- Additivity of the line derivative of functions on `E2` (the function space carries no
`LineDeriv` instance, so the identity is proved directly from `fderiv_add`). -/
theorem lineDeriv_add_fun {f k : E2 → ℂ} {x m : E2}
    (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) :
    lineDeriv ℝ (f + k) x m = lineDeriv ℝ f x m + lineDeriv ℝ k x m := by
  rw [hf.lineDeriv_eq_fderiv, hk.lineDeriv_eq_fderiv, (hf.add hk).lineDeriv_eq_fderiv,
    fderiv_add hf hk]
  simp

/-- The second order product rule for the line derivative: for smooth `g` and `k`,
`∂_m∂_m(g k) = (∂_m∂_m k) g + 2 (∂_m g)(∂_m k) + (∂_m∂_m g) k`. -/
theorem lineDeriv_lineDeriv_mul {g k : E2 → ℂ} {x m : E2}
    (hg : ∀ y, DifferentiableAt ℝ g y) (hk : ∀ y, DifferentiableAt ℝ k y)
    (hg' : DifferentiableAt ℝ (fun y => lineDeriv ℝ g y m) x)
    (hk' : DifferentiableAt ℝ (fun y => lineDeriv ℝ k y m) x) :
    lineDeriv ℝ (fun y => lineDeriv ℝ (fun z => g z * k z) y m) x m
      = g x * lineDeriv ℝ (fun y => lineDeriv ℝ k y m) x m
        + 2 * (lineDeriv ℝ g x m * lineDeriv ℝ k x m)
        + (lineDeriv ℝ (fun y => lineDeriv ℝ g y m) x m) * k x := by
  have h1 : (fun y => lineDeriv ℝ (fun z => g z * k z) y m)
      = fun y => g y * lineDeriv ℝ k y m + lineDeriv ℝ g y m * k y := by
    funext y
    exact lineDeriv_mul_eq (hg y) (hk y)
  rw [h1]
  change lineDeriv ℝ ((fun y => g y * lineDeriv ℝ k y m)
    + (fun y => lineDeriv ℝ g y m * k y)) x m = _
  rw [lineDeriv_add_fun (f := fun y => g y * lineDeriv ℝ k y m)
        (k := fun y => lineDeriv ℝ g y m * k y) ((hg x).mul hk') (hg'.mul (hk x))]
  rw [lineDeriv_mul_eq (hg x) hk']
  rw [lineDeriv_mul_eq hg' (hk x)]
  ring

/-! ### The Schwartz-map level -/

/-- The coercion of the line derivative of a Schwartz map is the pointwise line derivative. -/
theorem lineDerivOp_coe (m : E2) (ψ : 𝓢(E2, ℂ)) :
    (⇑(LineDeriv.lineDerivOp m ψ) : E2 → ℂ) = fun y => lineDeriv ℝ (⇑ψ) y m := by
  funext y
  rw [SchwartzMap.lineDerivOp_apply]

/-- The angular/radial slices of a Schwartz map are differentiable. -/
theorem differentiableAt_lineDeriv_schwartz (m : E2) (φ : 𝓢(E2, ℂ)) (x : E2) :
    DifferentiableAt ℝ (fun y => lineDeriv ℝ (⇑φ) y m) x := by
  rw [← lineDerivOp_coe m φ]
  exact (LineDeriv.lineDerivOp m φ).differentiableAt

/-- The Laplacian of a Schwartz map, evaluated in the basis `(e0, e1)`. -/
theorem schwartzMap_laplacian_apply (ψ : 𝓢(E2, ℂ)) (x : E2) :
    Laplacian.laplacian ψ x
      = lineDeriv ℝ (fun y => lineDeriv ℝ (⇑ψ) y e0) x e0
        + lineDeriv ℝ (fun y => lineDeriv ℝ (⇑ψ) y e1) x e1 := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 2) ℝ), Fin.sum_univ_two,
    add_apply, SchwartzMap.lineDerivOp_apply, lineDerivOp_coe, SchwartzMap.lineDerivOp_apply,
    lineDerivOp_coe]
  simp only [e0, e1]

/-- **Pointwise Leibniz rule for the Laplacian.**  For a multiplier `g` of temperate growth whose
first derivatives are of temperate growth, and a Schwartz function `φ`,

  `Δ (g · φ) = g · Δφ + 2 (∂_{e₀}g ∂_{e₀}φ + ∂_{e₁}g ∂_{e₁}φ) + (Δg) φ`

pointwise, where `Δg = lapF g = ∂_{e₀}∂_{e₀}g + ∂_{e₁}∂_{e₁}g`. -/
theorem laplacian_smul_apply {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (h0 : (d0 g).HasTemperateGrowth) (h1 : (d1 g).HasTemperateGrowth)
    (φ : 𝓢(E2, ℂ)) (x : E2) :
    (Laplacian.laplacian (SchwartzMap.smulLeftCLM ℂ g φ)) x
      = g x * (Laplacian.laplacian φ) x
        + 2 * (lineDeriv ℝ g x e0 * lineDeriv ℝ (⇑φ) x e0
             + lineDeriv ℝ g x e1 * lineDeriv ℝ (⇑φ) x e1)
        + lapF g x * φ x := by
  have hgd : ∀ y, DifferentiableAt ℝ g y :=
    fun y => (hg.1.differentiable (by simp)).differentiableAt
  have hk0 : DifferentiableAt ℝ (fun y => lineDeriv ℝ g y e0) x :=
    (h0.1.differentiable (by simp)).differentiableAt
  have hk1 : DifferentiableAt ℝ (fun y => lineDeriv ℝ g y e1) x :=
    (h1.1.differentiable (by simp)).differentiableAt
  have hco : (⇑(SchwartzMap.smulLeftCLM ℂ g φ) : E2 → ℂ) = fun z => g z * φ z := by
    rw [SchwartzMap.smulLeftCLM_apply hg]
    funext z
    simp [smul_eq_mul]
  have hlap : lapF g x = lineDeriv ℝ (fun y => lineDeriv ℝ g y e0) x e0
      + lineDeriv ℝ (fun y => lineDeriv ℝ g y e1) x e1 := rfl
  rw [schwartzMap_laplacian_apply (SchwartzMap.smulLeftCLM ℂ g φ) x, hco]
  rw [lineDeriv_lineDeriv_mul (g := g) (k := ⇑φ) hgd (fun y => φ.differentiableAt) hk0
        (differentiableAt_lineDeriv_schwartz e0 φ x)]
  rw [lineDeriv_lineDeriv_mul (g := g) (k := ⇑φ) hgd (fun y => φ.differentiableAt) hk1
        (differentiableAt_lineDeriv_schwartz e1 φ x)]
  rw [schwartzMap_laplacian_apply φ x, hlap]
  ring

/-- **The Leibniz rule for the Laplacian, as an identity of Schwartz maps.** -/
theorem schwartzMap_laplacian_smulLeftCLM {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (h0 : (d0 g).HasTemperateGrowth) (h1 : (d1 g).HasTemperateGrowth)
    (h2 : (lapF g).HasTemperateGrowth) (φ : 𝓢(E2, ℂ)) :
    Laplacian.laplacian (SchwartzMap.smulLeftCLM ℂ g φ)
      = SchwartzMap.smulLeftCLM ℂ g (Laplacian.laplacian φ)
        + 2 • (LineDeriv.lineDerivOp e0 (SchwartzMap.smulLeftCLM ℂ (d0 g) φ)
              + LineDeriv.lineDerivOp e1 (SchwartzMap.smulLeftCLM ℂ (d1 g) φ))
        - SchwartzMap.smulLeftCLM ℂ (lapF g) φ := by
  have hgm0 : ∀ y, DifferentiableAt ℝ (fun y => lineDeriv ℝ g y e0) y :=
    fun y => (h0.1.differentiable (by simp)).differentiableAt
  have hgm1 : ∀ y, DifferentiableAt ℝ (fun y => lineDeriv ℝ g y e1) y :=
    fun y => (h1.1.differentiable (by simp)).differentiableAt
  have hco0 : (⇑(SchwartzMap.smulLeftCLM ℂ (d0 g) φ) : E2 → ℂ)
      = fun y => lineDeriv ℝ g y e0 * φ y := by
    rw [SchwartzMap.smulLeftCLM_apply h0]
    funext y
    simp [d0, smul_eq_mul]
  have hco1 : (⇑(SchwartzMap.smulLeftCLM ℂ (d1 g) φ) : E2 → ℂ)
      = fun y => lineDeriv ℝ g y e1 * φ y := by
    rw [SchwartzMap.smulLeftCLM_apply h1]
    funext y
    simp [d1, smul_eq_mul]
  apply SchwartzMap.ext
  intro x
  simp only [sub_apply, add_apply, smul_apply]
  rw [laplacian_smul_apply hg h0 h1 φ x]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply h2]
  simp only [smul_eq_mul]
  rw [SchwartzMap.lineDerivOp_apply, hco0, lineDeriv_mul_eq (hgm0 x) φ.differentiableAt,
    SchwartzMap.lineDerivOp_apply, hco1, lineDeriv_mul_eq (hgm1 x) φ.differentiableAt]
  rw [show lapF g x = lineDeriv ℝ (fun y => lineDeriv ℝ g y e0) x e0
      + lineDeriv ℝ (fun y => lineDeriv ℝ g y e1) x e1 from rfl]
  ring

/-! ### The distributional Leibniz rule -/

theorem laplacian_smulLeftCLM {g : E2 → ℂ} (hg : Function.HasTemperateGrowth g)
    (h0 : (Work.EllipticEst.InteriorRegularity.d0 g).HasTemperateGrowth)
    (h1 : (Work.EllipticEst.InteriorRegularity.d1 g).HasTemperateGrowth)
    (h2 : (Work.EllipticEst.InteriorRegularity.Q0.lapF g).HasTemperateGrowth)
    (u : TemperedDistribution E2 ℂ) :
    Laplacian.laplacian (TemperedDistribution.smulLeftCLM ℂ g u)
      = TemperedDistribution.smulLeftCLM ℂ g (Laplacian.laplacian u)
        + 2 • (TemperedDistribution.smulLeftCLM ℂ (Work.EllipticEst.InteriorRegularity.d0 g)
                (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e0 u)
              + TemperedDistribution.smulLeftCLM ℂ (Work.EllipticEst.InteriorRegularity.d1 g)
                (LineDeriv.lineDerivOp Work.EllipticEst.InteriorRegularity.e1 u))
        + TemperedDistribution.smulLeftCLM ℂ (Work.EllipticEst.InteriorRegularity.Q0.lapF g) u := by
  ext φ
  -- evaluate both sides at the test function `φ`
  simp only [add_apply, smul_apply]
  rw [TemperedDistribution.laplacian_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.laplacian_apply_apply]
  rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.lineDerivOp_apply_apply]
  rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.lineDerivOp_apply_apply]
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  -- substitute the Schwartz-map Leibniz rule, in the form that isolates the `u`-argument
  rw [show SchwartzMap.smulLeftCLM ℂ g (Laplacian.laplacian φ)
      = Laplacian.laplacian (SchwartzMap.smulLeftCLM ℂ g φ)
        - 2 • (LineDeriv.lineDerivOp e0 (SchwartzMap.smulLeftCLM ℂ (d0 g) φ)
              + LineDeriv.lineDerivOp e1 (SchwartzMap.smulLeftCLM ℂ (d1 g) φ))
        + SchwartzMap.smulLeftCLM ℂ (lapF g) φ from by
    rw [schwartzMap_laplacian_smulLeftCLM hg h0 h1 h2 φ]
    abel]
  -- linearity of `u`
  simp only [map_add, map_sub, map_neg, map_nsmul, nsmul_eq_mul]
  ring

end Work.EllipticEst.InteriorRegularity.Q0
