import Mathlib
import Submission.Work.Drive.PushDisc.signOfCoreDerivative_of_immersion

/-!
# The crossing determinant with a *general* second-sheet jet (the lead's B1)

`Work.Drive.PushDisc.det_pairZ_coprod_of_shape` computes the determinant of the split crossing
`pairZ ∘ (A' coprod B')` from the two *shape* rows

    `∀ w, Yv (A' w) = 0`                (the first sheet lies in the plane `{y = 0, v = 0}`),
    `∀ w, (Yv (B' w)).2 = w.2`          (the second sheet is a graph *over its own `(x,v)`-chart*).

The second row is exactly the hypothesis `hsh₂` of `Work.Drive.PushDisc.pairDet_factor_of_model`,
and `hsh₂` is the whole-arc `(x,v)`-graph condition that the lead's clean-lens decision
(`Drive/PushDisc/NOTES_LEAD_lensAssembly.md`, 04:30) drops: it cannot be supplied by the assembly
(the finger's chart has a bounded domain), and the sign does not need it.

This file removes it: with only the *first* row, the crossing determinant factors as

    det (pairZ ∘ (A' coprod B')) = det (Xu ∘ A') * det (Yv ∘ B'),

i.e. the *full* `(y,v)`-block determinant of the second sheet replaces the single `y`-slope of the
graph case.  The two ingredients are
* `det_pairZ_coprod_components_general` — `det_pairZ_coprod_components` with a general second block
  `g₂ : P →ₗ P` in place of the graph block `y'.prod snd` (its proof is steps (1)–(5) of the
  existing one, verbatim);
* the same `hAeq`/`hBeq` factorisation of `A'`, `B'` through `pairZ` as in
  `det_pairZ_coprod_of_shape`.
-/

namespace Work.Drive.PushDisc

noncomputable section

open scoped ContDiff
open Set Filter

abbrev AB (k : ℕ) := ℝ × EuclideanSpace ℝ (Fin k)

/-- **The determinant of the split crossing with a general second block.**  This is
`Work.Drive.PushDisc.det_pairZ_coprod_components` with `g₂ : P →ₗ P` arbitrary (there the second
block was the graph block `y'.prod snd`, whose determinant is `y' (1,0)`). -/
theorem det_pairZ_coprod_components_general {k : ℕ}
    (e g₁ g₂ : AB k →ₗ[ℝ] AB k) :
    LinearMap.det ((pairZ k).toLinearMap.comp
        (((incLM k).comp e).coprod
          (((pairZ k).symm).toLinearMap.comp (g₁.prod g₂))))
      = LinearMap.det e * LinearMap.det g₂ := by
  let E := EuclideanSpace ℝ (Fin k)
  let P := ℝ × E
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
  -- (5) determinants
  rw [hcomp, det_prod_block]

/-- **The lead's B1: the crossing determinant without the `(x,v)`-graph row.**  From the single
shape row `Yv ∘ A' = 0` (the first sheet lies in the plane `{y = 0, v = 0}`) the split crossing
factors as `det (Xu ∘ A') * det (Yv ∘ B')`. -/
theorem det_pairZ_coprod_of_general {k : ℕ}
    (A' B' : AB k →ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (hA : ∀ w : AB k, Yv k (A' w) = 0) :
    LinearMap.det ((pairZ k).toLinearMap.comp (A'.coprod B'))
      = LinearMap.det ((Xu k).comp A') * LinearMap.det ((Yv k).comp B') := by
  set e : AB k →ₗ[ℝ] AB k := (Xu k).comp A' with he
  set g₁ : AB k →ₗ[ℝ] AB k := (Xu k).comp B' with hg₁
  set g₂ : AB k →ₗ[ℝ] AB k := (Yv k).comp B' with hg₂
  have hYvA : (Yv k).comp A' = 0 := by
    apply LinearMap.ext
    intro w
    simpa using hA w
  have hAeq : A' = (incLM k).comp e := by
    have h1 : (pairZ k).toLinearMap.comp A'
        = ((LinearMap.id : AB k →ₗ[ℝ] AB k).prod (0 : AB k →ₗ[ℝ] AB k)).comp e := by
      rw [pairZ_eq_prod k, LinearMap.prod_comp, hYvA, he]
      apply LinearMap.ext
      intro w
      rfl
    have h2 : (pairZ k).toLinearMap.comp ((incLM k).comp e)
        = ((LinearMap.id : AB k →ₗ[ℝ] AB k).prod (0 : AB k →ₗ[ℝ] AB k)).comp e := by
      rw [← LinearMap.comp_assoc, pairZ_comp_incLM k, LinearMap.prod_comp]
    have h3 : (pairZ k).toLinearMap.comp A'
        = (pairZ k).toLinearMap.comp ((incLM k).comp e) := by rw [h1, h2]
    apply LinearMap.ext
    intro w
    exact (pairZ k).injective (by simpa using congrArg (fun L => L w) h3)
  have hBeq : B' = (pairZ k).symm.toLinearMap.comp (g₁.prod g₂) := by
    have h1 : (pairZ k).toLinearMap.comp B' = g₁.prod g₂ := by
      rw [pairZ_eq_prod k, LinearMap.prod_comp, hg₁, hg₂]
    rw [← h1, ← LinearMap.comp_assoc, pairZ_symm_comp_toLinearMap k, LinearMap.id_comp]
  rw [hAeq, hBeq, det_pairZ_coprod_components_general]


/-- **The lead's B1 at the `pairDet` level**: `Work.Drive.PushDisc.pairDet_factor_of_model` with
the whole-arc `(x,v)`-graph row `hsh₂` removed.  Only the *first* sheet's shape row `hsh₁` (the first
sheet lies in the plane `{y = 0, v = 0}`) is used; the second sheet's contribution is the full
`(y,v)`-block determinant `det (Yv ∘ B)`. -/
theorem pairDet_factor_general {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₁ : Work.Whitney.IsSmoothChart c₁) (hc₂ : Work.Whitney.IsSmoothChart c₂)
    {a b : M} (ha : a ∈ c₁.source) (hb : b ∈ c₂.source) (hfab : f a = f b)
    (hsh₁ : ∀ x : M, x ∈ c₁.source → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0) :

    Work.Whitney.pairDet f c₁ c₂ a b
      = LinearMap.det ((Work.Projection.pairEquiv (k + 1)).toLinearMap.comp
            ((fderiv ℝ Θ (Φ (f a))).toLinearMap.comp (pairZ' k).symm.toLinearMap)) *
        (LinearMap.det ((Xu k).comp
            ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
              (c₁ a)).toLinearMap.comp (splitE k).toLinearMap)) *
          (LinearMap.det ((Yv k).comp
            ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
              (c₂ b)).toLinearMap.comp (splitE k).toLinearMap)))) := by
  set T := (fderiv ℝ Θ (Φ (f a))).toLinearMap with hT
  set A := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
    (c₁ a)).toLinearMap with hAdef
  set B := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
    (c₂ b)).toLinearMap with hBdef
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hAchain : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      f (c₁.symm u)) (c₁ a)).toLinearMap = T.comp A := by
    have hΘd : DifferentiableAt ℝ Θ (Φ (f (c₁.symm (c₁ a)))) :=
      (hΘsm.differentiable hne).differentiableAt
    have hGd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₁.symm u))) (c₁ a) :=
      differentiableAt_comp_symm_of_isSmoothChart_general (hΦsm.contMDiff.comp hf) hc₁ ha
    have hcomp := fderiv_comp (x := c₁ a)
      (f := fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u)))
      (g := Θ) hΘd hGd
    have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₁.symm u))
        = Θ ∘ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₁.symm u))) := by
      funext u
      exact (hΘΦ _).symm
    rw [hfun, hcomp, c₁.left_inv ha]
    rfl
  have hBchain : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
      f (c₂.symm u)) (c₂ b)).toLinearMap = T.comp B := by
    have hΘd : DifferentiableAt ℝ Θ (Φ (f (c₂.symm (c₂ b)))) :=
      (hΘsm.differentiable hne).differentiableAt
    have hGd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (k + 1)) =>
        Φ (f (c₂.symm u))) (c₂ b) :=
      differentiableAt_comp_symm_of_isSmoothChart_general (hΦsm.contMDiff.comp hf) hc₂ hb
    have hcomp := fderiv_comp (x := c₂ b)
      (f := fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
      (g := Θ) hΘd hGd
    have hfun : (fun u : EuclideanSpace ℝ (Fin (k + 1)) => f (c₂.symm u))
        = Θ ∘ (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u))) := by
      funext u
      exact (hΘΦ _).symm
    rw [hfun, hcomp, c₂.left_inv hb, ← hfab]
    rfl
  rw [pairDet_model f T c₁ c₂ a b A B hAchain hBchain,
    det_pairEquiv_transport T A B, det_pairZ'_coprod_eq A B]
  rw [det_pairZ_coprod_of_general (A.comp (splitE k).toLinearMap)
    (B.comp (splitE k).toLinearMap)
    (fun w => Yv_comp_fderiv_first hf Φ hΦsm c₁ hc₁ hsh₁ ha w)]



end

end Work.Drive.PushDisc
