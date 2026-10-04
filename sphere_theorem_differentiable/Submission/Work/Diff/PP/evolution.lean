import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Contract E: the evolution of the curvature tensor along the Ricci flow (definitions)

This file fixes the *vocabulary* in which contract E (the component-level curvature evolution,
Hamilton's equation after the Uhlenbeck trick) is stated, so that the areas `GE` (EV1/EV2/EV3),
`EXT` and `L` can import it.  Nothing here is a statement about Ricci flows: it is the tensorial
second covariant derivative of the curvature, its trace (the rough Laplacian) and the two pieces of
the Uhlenbeck-frame data.

The intended statement, requested at path `Diff/PP/curvature_evolution` (theorem
`Work.Diff.PP.curvature_evolution`), is

```
theorem curvature_evolution (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∀ (G : ℝ → SMet I M) (T t₀ : ℝ), IsRicciFlow G T → t₀ ∈ Ico 0 T →
      ∀ (x : M) (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x),
        IsONFrame (G t₀) x (e t₀) →
        (∃ v : Fin (Module.finrank ℝ E) → TangentSpace I x,
          (∀ i, HasDerivWithinAt (fun s : ℝ ↦ (e s i : E)) (v i : E) (Ico 0 T) t₀) ∧
          (∀ i j, (G t₀).inner x (v i) (e t₀ j) = ricAt (lcOf (G t₀)) x (e t₀ i) (e t₀ j))) →
        HasDerivWithinAt (fun s : ℝ ↦ rmFrame (G s) x (e s))
          (fun i j k l ↦ roughLap (G t₀) x (e t₀) i j k l + Q (rmFrame (G t₀) x (e t₀)) i j k l)
          (Ico 0 T) t₀
```

i.e. *in an orthonormal frame that is evolved by the Uhlenbeck trick
`∂ₜ eᵢ = Ric(eᵢ)^♯` (equivalently `⟨∂ₜeᵢ, eⱼ⟩ = Ric(eᵢ,eⱼ)`), the component array of the curvature
evolves by `∂ₜ R = ΔR + Q(R)`, where `ΔR = tr_g ∇²Rm` is the rough Laplacian of the 4-tensor and `Q`
is Hamilton's reaction term from `Submission.Diff.Alg`.*

Sign/sanity calibration (see `PP/Q_Iso.lean`, `PP/hasDerivAt_K_Iso.lean`): on the unit round sphere
`∇Rm = 0` so `ΔR = 0`, `rmFrame = K·Iso` with `K' = 2(n−1)K²`, and the right-hand side is
`Q(K·Iso) = 2(n−1)K²·Iso` — the `+` sign and the factor `2(n−1)`.  A sign error in `Q`, in the Ric
normalisation or in the Uhlenbeck correction would show up here.

Derivation (for the prover of `curvature_evolution`):

1. `LCVariation` with `h = ∂ₜ g = −2 Ric` gives `∂ₜ R(X,Y)Z = (∇_X A)(Y,Z) − (∇_Y A)(X,Z)` where
   `g(A(X,Y),Z) = −(∇_X Ric)(Y,Z) − (∇_Y Ric)(X,Z) + (∇_Z Ric)(X,Y)` (first variation of the
   curvature; this is the file `PP/evolution_basic.lean`).
2. The second Bianchi identity turns the right-hand side into `ΔRm + Q(Rm)` in the frame.
3. The frame rotation `∂ₜeᵢ = Ric(eᵢ)^♯` contributes exactly the terms that make the `Q` term
   appear with the normalisation of `Submission.Diff.Alg`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.PP

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Second covariant derivative of the curvature 4-tensor of the explicit smooth metric `g`:
`(∇_v ∇_w Rm)(a,b,c,d)` at `x`, where `Rm(a,b,c,d) = g(R(a,b)d, c)`.

The `−covRm (∇_v w) …` term is the correction that makes `∇²Rm` tensorial, so that
`∑_m cov2Rm (e_m) (e_m) …` over an orthonormal frame is the trace `tr_g ∇²Rm = ΔRm`. -/
noncomputable def cov2Rm (g : SMet I M) (x : M) (v w a b c d : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ covRm g y (smoothExt x w y) (smoothExt x a y) (smoothExt x b y)
      (smoothExt x c y) (smoothExt x d y)) x v
    - covRm g x (lcOf g (smoothExt x w) x v) a b c d
    - covRm g x w (lcOf g (smoothExt x a) x v) b c d
    - covRm g x w a (lcOf g (smoothExt x b) x v) c d
    - covRm g x w a b (lcOf g (smoothExt x c) x v) d
    - covRm g x w a b c (lcOf g (smoothExt x d) x v)

/-- The rough Laplacian `ΔRm = tr_g ∇²Rm` of the curvature, evaluated in an orthonormal frame:
`(ΔRm)ᵢⱼₖₗ = ∑_m (∇_{e_m}∇_{e_m}Rm)(eᵢ,eⱼ,eₖ,eₗ)`.  This is a tensor, so its value does not
depend on which orthonormal frame `e` is used. -/
noncomputable def roughLap (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) : Curv4 (Module.finrank ℝ E) :=
  fun i j k l ↦ ∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)

end Work.Diff.PP
