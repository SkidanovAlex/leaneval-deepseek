import Mathlib
import Submission.Work.Drive.PushDisc.asymSignDefs
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Drive.PushDisc.det_pairZ_inc_coprod_graph

/-!
# `Work.Drive.PushDisc.signCoreBricks`: the determinant of a split crossing, with a general
first-sheet jet

`Work.Drive.PushDisc.det_pairZ_inc_coprod_graph` computes the determinant of the split crossing
`pairZ ∘ (incLM coprod graphLM yx b a D)` and finds `yx`: this is the case in which the *first*
sheet's jet is the identity inclusion `incLM` (i.e. the first sheet's chart pins the `(x,u)`
coordinates).

The theorem below is the **general** case: the first sheet's jet is `incLM ∘ e` for an arbitrary
`e : (ℝ × E^k) →ₗ (ℝ × E^k)` (an arbitrary `(x,u)`-Jacobian of the first chart), and the second
sheet's `(y,v)`-block is `y'.prod snd`.  The block matrix is

    [[e, g₁], [0, g₂]]-shaped,      det = det e * y' (1,0),

i.e. **the first sheet's `(x,u)`-Jacobian enters the crossing determinant multiplicatively**.

This is the formal content of the following fact, which matters for the interface
`Work.Drive.PushDisc.signOfCoreDerivative` (see the docstring of that file): a hypothesis which
elects only that the first sheet's image lies in the model plane `{y = 0, v = 0}` (and does *not*
pin the `(x,u)`-coordinates, i.e. does not fix `e`) does **not** determine the sign of the crossing
determinant: it only determines `det e * yx`, and `det e` is free.  In particular the two crossings
of a bigon obey `pairDet₁ * pairDet₂ < 0` no matter what the sign of `det e` is at the two points,
so the opposite-sign hypothesis alone cannot force `yx` to change sign between them.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff

/-- **The determinant of the split crossing with a general first-sheet `(x,u)`-jet.**

With `E = EuclideanSpace ℝ (Fin k)`, `P = ℝ × E`, `pairZ : Mdl k ≃ P × P` the pairing
`(x,y,u,v) ↦ ((x,u),(y,v))`, `incLM` the inclusion of the first sheet's plane and
`P →ₗ P`, `g₁ : P →ₗ P`, `y' : P →ₗ ℝ` arbitrary, the endomorphism
`pairZ ∘ ((incLM ∘ e) coprod (pairZ⁻¹ ∘ (g₁.prod (y'.prod snd))))` of `P × P` has determinant
`det e * y' (1,0)`.

The three factors are exactly the three blocks of the crossing: the first sheet's `(x,u)`-Jacobian
`e`, the first sheet's `(y,v)`-block (here `0`, i.e. the first sheet lies in the plane `{y=0,v=0}`),
and the second sheet's `y`-slope `y' (1,0)` along its `x`-direction. -/
theorem det_pairZ_coprod_components {k : ℕ}
    (e g₁ : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)))
    (y' : (ℝ × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ] ℝ) :
    LinearMap.det ((pairZ k).toLinearMap.comp
        (((incLM k).comp e).coprod
          (((pairZ k).symm).toLinearMap.comp
            (g₁.prod (y'.prod (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k))))))))
      = LinearMap.det e * y' ((1 : ℝ), 0) := by
  let E := EuclideanSpace ℝ (Fin k)
  let P := ℝ × E
  set g₂ : P →ₗ[ℝ] P := y'.prod (LinearMap.snd ℝ ℝ E) with hg₂def
  -- (1) `pairZ ∘ incLM = id.prod 0`
  have hAinc : (pairZ k).toLinearMap.comp (incLM k)
      = (LinearMap.id : P →ₗ[ℝ] P).prod (0 : P →ₗ[ℝ] P) := by
    apply LinearMap.ext
    intro X
    rcases X with ⟨x, u⟩
    simp [pairZ, incLM_apply, LinearMap.prod_apply]
  -- (2) the first sheet's block (its `(y,v)`-block is `0`)
  have hA : (pairZ k).toLinearMap.comp ((incLM k).comp e)
      = e.prod (0 : P →ₗ[ℝ] P) := by
    rw [← LinearMap.comp_assoc, hAinc]
    apply LinearMap.ext
    intro X
    simp [LinearMap.prod_apply]
  -- (3) `pairZ` cancels its own inverse on the second sheet's block
  have hB : (pairZ k).toLinearMap.comp
        (((pairZ k).symm).toLinearMap.comp (g₁.prod g₂)) = g₁.prod g₂ := by
    rw [← LinearMap.comp_assoc]
    have hcancel : (pairZ k).toLinearMap.comp ((pairZ k).symm).toLinearMap
        = LinearMap.id := by
      apply LinearMap.ext
      intro X
      exact (pairZ k).apply_symm_apply X
    rw [hcancel, LinearMap.id_comp]
  -- (4) the composite is block upper triangular with diagonal blocks `e` and `g₂`
  have hcomp : (pairZ k).toLinearMap.comp
        (((incLM k).comp e).coprod (((pairZ k).symm).toLinearMap.comp (g₁.prod g₂)))
      = ((e.comp (LinearMap.fst ℝ P P)) + (g₁.comp (LinearMap.snd ℝ P P))).prod
          (g₂.comp (LinearMap.snd ℝ P P)) := by
    rw [LinearMap.comp_coprod, hA, hB]
    apply LinearMap.ext
    intro X
    rcases X with ⟨X, Z⟩
    simp only [LinearMap.coprod_apply, LinearMap.prod_apply, LinearMap.comp_apply,
      Function.prod, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    simp
  -- (5) determinants: `det e * det g₂`
  rw [hcomp, det_prod_block]
  congr 1
  -- (6) `det g₂ = y' (1,0)`: the `(y,v)`-block of a graph over `(x,v)` is block triangular
  have hg2 : g₂ = (((LinearMap.mulLeft ℝ (y' ((1 : ℝ), 0))).comp
        (LinearMap.fst ℝ ℝ E)) +
      ((y'.comp (LinearMap.inr ℝ ℝ E)).comp (LinearMap.snd ℝ ℝ E))).prod
        ((LinearMap.id : E →ₗ[ℝ] E).comp (LinearMap.snd ℝ ℝ E)) := by
    rw [hg₂def]
    apply LinearMap.ext
    intro X
    rcases X with ⟨t, v⟩
    simp only [LinearMap.prod_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.inr_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply, Function.prod]
    have hdec : (t, v) = t • ((1 : ℝ), (0 : E)) + ((0 : ℝ), v) := by
      ext <;> simp
    rw [hdec, map_add, map_smul, smul_eq_mul, mul_comm]
  rw [hg2, det_prod_block, LinearMap.det_mulLeft, LinearMap.det_id, mul_one]

/-- **The transport step: `pairDet` splits into a constant factor and the split crossing.**

For linear maps `A B : E^{k+1} →ₗ Mdl k` (the two charts' jets of `f`, read through
`Work.Drive.Whitney.Mdl k`) and `T : Mdl k →ₗ E^{2(k+1)}` (the jet of the ambient chart `Θ`, with
`A` and `B` factored through `T`), the determinant of the two-chart crossing splits as

    det (pairEquiv ∘ (T ∘ (A coprod B)))
      = det (pairZ'⁻¹ ∘ pairEquiv ∘ T) * det (pairZ ∘ ((A ∘ splitE) coprod (B ∘ splitE))).

The first factor is the "constant" `Work.Drive.PushDisc.det_fderiv_mul_pos` controls (its two values
at the two crossings of a bigon have the same sign); the second is exactly the argument of
`Work.Drive.PushDisc.det_pairZ_coprod_components`, in which the first sheet's `(x,u)`-Jacobian
`det e` appears **multiplicatively**.  Together with `Work.Drive.PushDisc.pairDet_model`
(this is the value of `Work.Whitney.pairDet` when the two chart jets factor through one `T`), this is
the whole bookkeeping of the sign of a crossing in the split coordinates. -/
theorem det_pairEquiv_coprod_split {k : ℕ}
    (A B : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (T : Work.Drive.Whitney.Mdl k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1)))) :
    LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp (T.comp (A.coprod B)))
      = LinearMap.det ((pairZ' k).symm.toLinearMap.comp
            ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp T))
        * LinearMap.det ((pairZ k).toLinearMap.comp
            ((A.comp (splitE k).toLinearMap).coprod (B.comp (splitE k).toLinearMap))) := by
  set σ : (ℝ × EuclideanSpace ℝ (Fin k)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) := splitE k
  set σP := σ.prodCongr σ
  set pz := pairZ k
  set pz' := pairZ' k
  set pe := Work.Projection.pairEquiv (k + 1)
  have hpz'eq : pz'.toLinearMap = σP.toLinearMap.comp pz.toLinearMap := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [show pz' = (pairZ k).trans (σ.prodCongr σ) from rfl, LinearEquiv.trans_apply]
  have hins : pe.toLinearMap.comp (T.comp (A.coprod B))
      = (pe.toLinearMap.comp (T.comp pz'.symm.toLinearMap)).comp
          (pz'.toLinearMap.comp (A.coprod B)) := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearEquiv.symm_apply_apply]
  have hsplit : pz'.toLinearMap.comp (A.coprod B)
      = σP.toLinearMap.comp ((pz.toLinearMap.comp
          ((A.comp σ.toLinearMap).coprod (B.comp σ.toLinearMap))).comp σP.symm.toLinearMap) := by
    rw [hpz'eq]
    apply LinearMap.ext
    intro X
    rcases X with ⟨X₁, X₂⟩
    have hsymm : σP.symm (X₁, X₂) = (σ.symm X₁, σ.symm X₂) := by
      rw [show σP = σ.prodCongr σ from rfl, LinearEquiv.prodCongr_symm,
        LinearEquiv.prodCongr_apply]
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearEquiv.coe_toLinearMap]
    rw [hsymm]
    simp
  have hdet_split : LinearMap.det (pz'.toLinearMap.comp (A.coprod B))
      = LinearMap.det (pz.toLinearMap.comp
          ((A.comp σ.toLinearMap).coprod (B.comp σ.toLinearMap))) := by
    rw [← LinearMap.det_conj (f := pz.toLinearMap.comp
        ((A.comp σ.toLinearMap).coprod (B.comp σ.toLinearMap))) (e := σP)]
    rw [hsplit]
  have hdet1 : LinearMap.det (pe.toLinearMap.comp (T.comp pz'.symm.toLinearMap))
      = LinearMap.det (pz'.symm.toLinearMap.comp (pe.toLinearMap.comp T)) := by
    rw [← LinearMap.det_conj (f := pe.toLinearMap.comp (T.comp pz'.symm.toLinearMap))
      (e := pz'.symm)]
    congr 1
    apply LinearMap.ext
    intro X
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_symm]
    rw [LinearEquiv.symm_apply_apply]
  rw [hins, LinearMap.det_comp, hdet1, hdet_split]

end Work.Drive.PushDisc
