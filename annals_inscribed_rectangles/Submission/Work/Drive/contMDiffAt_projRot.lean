import Mathlib
import Submission.Work.Drive.projRot
import Submission.Work.Drive.projRotSmooth
import Submission.Work.Drive.contMDiffAt_projChartMap
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.contMDiffAt_projMk

/-!
# The rotation of `ℝP³` is `C^∞` in the rotation parameter jointly with the point

`Work.Drive.projRot t : ℝP³ → ℝP³` is the projectivisation of the diagonal rotation `diagRot t` of
`ℂ² ≅ ℝ⁴` (`Submission/Work/Drive/projRot.lean`).  `Work.Drive.contMDiffAt_projRot_mk_prod`
(`Submission/Work/Drive/projRotSmooth.lean`) gives the smoothness of `(t, x) ↦ projRot t [V x]` for a
`C^∞` nowhere vanishing lift `V` of a map into `ℝP³` — a two-variable statement whose *source* is the
model space `ℝ × ℝ³`.  What is still missing is the same statement with the **source the product
manifold** `ℝ × ℝP³`, i.e. the joint smoothness of the action

`(t, p) ↦ projRot t p`

for the product charted structure `prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 3)) (projCharted 3)`
on `ℝ × ℝP³` and the transparent projective structure `projCharted 3` on the target `ℝP³`.  This is
the statement proved here, `Work.Drive.contMDiffAt_projRot`; it is the smoothness input for the
rotation action on the capping space (see `ROT_SMOOTHNESS_STATUS.md`, §2 and §5).

The proof is the one described in §5 of that note, carried out with the *preferred charts* of the two
structures (so no general "chart criterion for product manifolds" is needed):

* pick the chart indices `i` of the preferred chart at `p₀` and `j` of the preferred chart at
  `projRot t₀ p₀` (`Classical.choose (exists_mem_projChartSource ·)`), so that both preferred charts
  are *definitionally* the explicit charts `projChart i`, `projChart j`;
* by `contMDiffAt_projRot_mk_prod` applied to the lift `V = projSection i` (smooth by
  `contDiff_projSection`, nowhere zero by `projSection_ne_zero`) the map

  `Φ : (t, x) ↦ projRot t (projChartInv i x)`

  is `C^∞` at `(t₀, projChartMap i p₀)`, and composing with the chart `projChart j` (smooth on its
  source `projChartSource j ∋ projRot t₀ p₀` by `contMDiffAt_projChartMap`) gives

  `hchart : ContDiffAt ℝ ∞ ((t,x) ↦ projChartMap j (projRot t (projChartInv i x))) (t₀, projChartMap i p₀)`;

* the extended chart of the source at `(t₀, p₀)` is computed by `extChartAt_prod` (with
  `modelWithCornersSelf_prod`): its `symm` is `x ↦ (x.1, projChartInv i x.2)` (`src`) and its value at
  `(t₀, p₀)` is `(t₀, projChartMap i p₀)` (`hpt`), while the preferred chart at the image point is
  `projChartMap j` (`tgt`); hence the composite of `contMDiffAt_iff` is exactly the function of
  `hchart` at the point `(t₀, projChartMap i p₀)`;
* continuity (the other half of `contMDiffAt_iff`) follows because `(t,p) ↦ projRot t p` agrees on
  the neighbourhood `ℝ × projChartSource i` of `(t₀,p₀)` with the composite of the *continuous* maps
  `(t,p) ↦ (t, projChartMap i p)` (`ContinuousAt` from `contMDiffAt_projChartMap`) and `Φ`
  (`ContinuousAt` from the `ContMDiffAt` above), using `projChartInv_projChartMap`.

The `H`-argument of `ContMDiffAt` is written with the type tag `ModelProd` (`Is` below): this is the
form in which the *product* charted space is the canonical instance, so that type-class synthesis
finds `prodChartedSpace` for `ChartedSpace (ModelProd ℝ ℝ³) (ℝ × ℝP³)`; the statement with the
plain product type is definitionally the same (`ModelProd` is `@[implicit_reducible]`).
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Filter

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

theorem contMDiffAt_projRot (t₀ : ℝ) (p₀ : Projectivization ℝ (Work.Drive.Eucl 3)) :
    @ContMDiffAt ℝ _ (ℝ × EuclideanSpace ℝ (Fin 3)) _ _ (ℝ × EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3)))
      (ℝ × Projectivization ℝ (Work.Drive.Eucl 3)) _
      (@prodChartedSpace ℝ _ ℝ _ _ (EuclideanSpace ℝ (Fin 3)) _ (Projectivization ℝ (Work.Drive.Eucl 3)) _
        (Work.Drive.projCharted 3))
      (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Projectivization ℝ (Work.Drive.Eucl 3)) _ (Work.Drive.projCharted 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) => Work.Drive.projRot q.1 q.2) (t₀, p₀) := by
  letI := Work.Drive.projCharted 3
  -- the source model-with-corners, written with the `ModelProd` type tag so that the product
  -- charted-space instance is the canonical one for type-class synthesis
  let Is : ModelWithCorners ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) :=
    modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3))
  have hIs : Is = (modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) :=
    modelWithCornersSelf_prod
  -- the chart indices of the preferred charts at `p₀` and at `projRot t₀ p₀`
  set i : Fin (3+1) := Classical.choose (Work.Drive.exists_mem_projChartSource p₀) with hi
  have hpi : p₀ ∈ Work.Drive.projChartSource i :=
    Classical.choose_spec (Work.Drive.exists_mem_projChartSource p₀)
  set j : Fin (3+1) := Classical.choose (Work.Drive.exists_mem_projChartSource (Work.Drive.projRot t₀ p₀)) with hj
  have hpj : Work.Drive.projRot t₀ p₀ ∈ Work.Drive.projChartSource j :=
    Classical.choose_spec (Work.Drive.exists_mem_projChartSource (Work.Drive.projRot t₀ p₀))
  -- the chart expression is smooth
  have hVs : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (modelWithCornersSelf ℝ (Eucl 3))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.projSection i) (Work.Drive.projChartMap i p₀) :=
    (Work.Drive.contDiff_projSection 3 i).contMDiff.contMDiffAt
  have hmk' := Work.Drive.contMDiffAt_projRot_mk_prod (V := Work.Drive.projSection i)
      (fun x => Work.Drive.projSection_ne_zero i x) t₀ (Work.Drive.projChartMap i p₀) hVs
  have hmk : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => Work.Drive.projRot q.1 (Work.Drive.projChartInv i q.2))
      (t₀, Work.Drive.projChartMap i p₀) := by
    simpa only [Work.Drive.projChartInv] using hmk'
  have hpj' : Work.Drive.projRot t₀ (Work.Drive.projChartInv i (Work.Drive.projChartMap i p₀)) ∈
      Work.Drive.projChartSource j := by
    rw [Work.Drive.projChartInv_projChartMap hpi]; exact hpj
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap j (Work.Drive.projRot q.1 (Work.Drive.projChartInv i q.2)))
      (t₀, Work.Drive.projChartMap i p₀) :=
    (Work.Drive.contMDiffAt_projChartMap 3 j _ hpj').comp (t₀, Work.Drive.projChartMap i p₀) hmk
  have hchart' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        Work.Drive.projChartMap j (Work.Drive.projRot q.1 (Work.Drive.projChartInv i q.2)))
      (t₀, Work.Drive.projChartMap i p₀) := hchart.contDiffAt
  -- the extended charts of the source and of the target
  have tgt : (↑(extChartAt (𝓡 3) (Work.Drive.projRot t₀ p₀)) :
        Projectivization ℝ (Work.Drive.Eucl 3) → EuclideanSpace ℝ (Fin 3)) = Work.Drive.projChartMap j := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) (Work.Drive.projRot t₀ p₀)) = projChart j from rfl]
    rfl
  have src : (↑(extChartAt Is (t₀, p₀)).symm :
        ℝ × EuclideanSpace ℝ (Fin 3) → ℝ × Projectivization ℝ (Work.Drive.Eucl 3))
      = fun x => (x.1, Work.Drive.projChartInv i x.2) := by
    rw [hIs, extChartAt_prod, PartialEquiv.prod_coe_symm]
    funext x
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  have hpt : (↑(extChartAt Is (t₀, p₀)) : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) →
        ℝ × EuclideanSpace ℝ (Fin 3)) (t₀, p₀) = (t₀, Work.Drive.projChartMap i p₀) := by
    rw [hIs, extChartAt_prod, PartialEquiv.prod_coe]
    simp only [extChartAt_model_space_eq_id, extChartAt_coe, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq, PartialEquiv.refl_coe]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  -- the composite of `contMDiffAt_iff` is the function of `hchart`
  have hG : (↑(extChartAt (𝓡 3) (Work.Drive.projRot t₀ p₀)) ∘
        (fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) => Work.Drive.projRot q.1 q.2) ∘
          ↑(extChartAt Is (t₀, p₀)).symm)
      = (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
          Work.Drive.projChartMap j (Work.Drive.projRot q.1 (Work.Drive.projChartInv i q.2))) := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, src, tgt]
  -- rewrite the goal in the `ModelProd` form and test it in the preferred charts
  change @ContMDiffAt ℝ _ (ℝ × EuclideanSpace ℝ (Fin 3)) _ _ (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) _ Is
      (ℝ × Projectivization ℝ (Work.Drive.Eucl 3)) _
      (@prodChartedSpace ℝ _ ℝ _ _ (EuclideanSpace ℝ (Fin 3)) _ (Projectivization ℝ (Work.Drive.Eucl 3)) _
        (Work.Drive.projCharted 3))
      (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Projectivization ℝ (Work.Drive.Eucl 3)) _ (Work.Drive.projCharted 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) => Work.Drive.projRot q.1 q.2) (t₀, p₀)
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · -- continuity, from the continuity of the chart coordinates
    have hΨ : ContinuousAt (fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) =>
        (q.1, Work.Drive.projChartMap i q.2)) (t₀, p₀) :=
      continuousAt_fst.prodMk ((Work.Drive.contMDiffAt_projChartMap 3 i p₀ hpi).continuousAt.comp
        continuousAt_snd)
    have hcont : ContinuousAt (fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) =>
        Work.Drive.projRot q.1 (Work.Drive.projChartInv i (Work.Drive.projChartMap i q.2))) (t₀, p₀) :=
      ContinuousAt.comp (f := fun q : ℝ × Projectivization ℝ (Work.Drive.Eucl 3) =>
          (q.1, Work.Drive.projChartMap i q.2)) (x := (t₀, p₀)) hmk.continuousAt hΨ
    refine hcont.congr ?_
    filter_upwards [((Work.Drive.isOpen_projChartSource i).preimage continuous_snd).mem_nhds hpi]
      with q hq
    rw [Work.Drive.projChartInv_projChartMap hq]
  · -- smoothness in the charts
    rw [show Set.range (↑Is) = Set.univ from by
        simp only [Is, modelWithCornersSelf_coe, Set.range_id],
      contDiffWithinAt_univ, hG, hpt]
    exact hchart'

end

end Work.Drive
