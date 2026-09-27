import Mathlib
import Submission.Work.Drive.PushDisc.sheetOneFlatteningData
import Submission.Work.Drive.PushDisc.sheetATwoPlaneShear
import Submission.Work.Drive.Whitney.foldCollar

set_option maxHeartbeats 1000000

namespace Work.Drive.PushDisc


open scoped Manifold ContDiff Topology
open Set Metric Filter

/-! ## Auxiliary lemmas for `exists_chart_twoPlaneFraming` -/

/-- The model space `Mdl k` of the Whitney move, as a normed space, is linearly isomorphic to
`ℝ^{2n}` when `n = k + 1`. -/
noncomputable def mdlEquivL {n k : ℕ} (hk : n = k + 1) :
    Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  LinearEquiv.ofFinrankEq _ _
    (by rw [hk, finrank_Mdl, finrank_euclideanSpace, Fintype.card_fin])

set_option backward.isDefEq.respectTransparency false in
/-- The tangent space of an `n`-manifold at a point is `n`-dimensional. -/
theorem finrank_tangentSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    Module.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p) = n :=
  (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin n)).trans (Fintype.card_fin n)

set_option backward.isDefEq.respectTransparency false in
/-- The range of the `mfderiv` of an immersion of an `n`-manifold has dimension `n`. -/
theorem finrank_range_mfderiv_self {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y)) (p : M) :
    Module.finrank ℝ (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p).toLinearMap) = n := by
  rw [LinearMap.finrank_range_of_inj (by simpa using himm p), finrank_tangentSpace p]

/-- Pushforwards of a submodule along an injective linear map have the same dimension. -/
theorem finrank_map_eq_of_injective {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {L : E →ₗ[ℝ] F} (hL : Function.Injective L)
    (T : Submodule ℝ E) :
    Module.finrank ℝ (Submodule.map L T) = Module.finrank ℝ T := by
  have hinj : Function.Injective (L.comp T.subtype) := by
    intro x y hxy
    exact Subtype.ext (hL (by simpa using hxy))
  have hrange : LinearMap.range (L.comp T.subtype) = Submodule.map L T := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hinj

/-- The `kerXV`-form of the two-plane framing condition. -/
theorem map_inf_kerXV_eq_bot {k : ℕ}
    {F : Work.Drive.Whitney.Mdl k →ₗ[ℝ] Work.Drive.Whitney.Mdl k}
    {T : Submodule ℝ (Work.Drive.Whitney.Mdl k)}
    (hT : ∀ t ∈ T, F t ∈ kerXV k → t = 0) : T.map F ⊓ kerXV k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hz.1
  rw [hT t ht hz.2, map_zero]
/-- `toContinuousLinearMap` does not change the underlying function. -/
theorem lc_apply {k : ℕ} (L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (x : Work.Drive.Whitney.Mdl k) : L.toContinuousLinearMap x = L x := rfl

/-- The same for the inverse. -/
theorem lc_symm_apply {k : ℕ} (L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (x : Work.Drive.Whitney.Mdl k) : L.symm.toContinuousLinearMap x = L.symm x := rfl

/-- The inverse of a linear equivalence cancels it, also through `toContinuousLinearMap`. -/
theorem lc_symm_apply_apply {k : ℕ} (L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (x : Work.Drive.Whitney.Mdl k) :
    L.symm.toContinuousLinearMap (L.toContinuousLinearMap x) = x := by
  rw [lc_symm_apply, lc_apply, LinearEquiv.symm_apply_apply]

/-- The other order. -/
theorem lc_apply_symm {k : ℕ} (L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k)
    (x : Work.Drive.Whitney.Mdl k) :
    L.toContinuousLinearMap (L.symm.toContinuousLinearMap x) = x := by
  rw [lc_apply, lc_symm_apply, LinearEquiv.apply_symm_apply]

/-- **The flattened chart with the two-plane framing at the double points.**  From the flattening
data of the first sheet (`sheetOneFlatteningData`) and the two-plane shear
(`exists_linearEquiv_sheetA_two_planes`), one obtains a chart `Φ` (with inverse `Θ`) and an open tube
`U₁` around `γ₁` such that the first sheet is flat (`Φ (f x) ∈ sheetA` for `x ∈ U₁`), the two double
points `p₁`, `q₁` of the arc are pinned to `(-1,0,0,0)`, `(1,0,0,0)`, and — the new part — the
tangent planes of the *second* sheet at `p₂` and `q₂` become **graphs over the `(x,v)`-plane**, i.e.
their images under the chart's derivative miss the plane `kerXV k = {x = 0, v = 0}`.

Intended proof: `sheetOneFlatteningData` gives `Φ₀`, `Θ₀`, `U`, `k`, the rows.  Its chart is
post-composed with a linear equivalence `M` of `Mdl k` with `M (sheetA) ⊆ sheetA` and
`M (±1,0,0,0) = (±1,0,0,0)` (this preserves every row: smoothness, the two inverse rows, the
flatness and the pinning).  The two tangent planes are
`T₂ := (range (mfderiv f p₂)).map (fderiv ℝ Φ₀ (f p₁)).toLinearMap` and
`T₃ := (range (mfderiv f q₂)).map (fderiv ℝ Φ₀ (f q₁)).toLinearMap`; each has `finrank = k+1`, and
`sheetASub k ⊔ T = ⊤` because `fderiv ℝ Φ₀ (f p₁)` is invertible, `htransP`/`htransQ` say the two
tangent ranges span `⊤`, and it carries the *first* sheet's tangent range (which maps into `sheetA`
since `f '' U ⊆ Φ₀ ⁻¹' sheetA`, so by equal dimensions onto `sheetA`) to `sheetA`.
`exists_linearEquiv_sheetA_two_planes T₂ T₃ …` then supplies the shear `M := shearEquiv k c`
(`c > |t₀(T₂).1| + |t₀(T₃).1|`), and `Φ := M ∘ Φ₀`, `Θ := Θ₀ ∘ M⁻¹` finish.

NOTE (reviewer 2): the two planes are pushed by `fderiv ℝ Φ` at `f p₁` resp. `f q₁`; the equalities
`hfp`, `hfq` are what make these the genuine tangent planes of the two sheets at the double points. -/
theorem exists_chart_twoPlaneFraming {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective
      (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (_hk : n = k + 1)
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (U₁ : Set M),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U₁ ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁ ∧ U₁ ⊆ W ∧
      (∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) ∧
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).toLinearMap).map
          (fderiv ℝ Φ (f p₁)).toLinearMap ⊓ Work.Drive.PushDisc.kerXV k = ⊥ ∧
      (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).toLinearMap).map
          (fderiv ℝ Φ (f q₁)).toLinearMap ⊓ Work.Drive.PushDisc.kerXV k = ⊥ := by
  classical
  obtain ⟨k, hk, A, Ainv, K, Φ₀, Θ₀, U, hA, hAinv, hAl, hAr, hΦ₀sm, hΘ₀sm, hΘΦ, hΦΘ, hUo, hUcl,
    hUarc, hp₂U, hq₂U, hKfin, hAK, hsheet, hΦp₁, hΦq₁⟩ :=
    sheetOneFlatteningData hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃ hp₁p₂ hfp hclean hsep
      γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm hp₂arc hq₂arc
  have hp₁U : p₁ ∈ U := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0⟩
  have hq₁U : q₁ ∈ U := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1⟩
  have hdΦp : DifferentiableAt ℝ Φ₀ (f p₁) := (hΦ₀sm.differentiable (by simp)).differentiableAt
  have hdΦq : DifferentiableAt ℝ Φ₀ (f q₁) := (hΦ₀sm.differentiable (by simp)).differentiableAt
  have hdΘp : DifferentiableAt ℝ Θ₀ (Φ₀ (f p₁)) :=
    (hΘ₀sm.differentiable (by simp)).differentiableAt
  have hdΘq : DifferentiableAt ℝ Θ₀ (Φ₀ (f q₁)) :=
    (hΘ₀sm.differentiable (by simp)).differentiableAt
  -- a linear isomorphism of the model space with `ℝ^{2n}`
  let h : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := mdlEquivL hk
  -- the tangent planes of `f` at the four points, as submodules of `ℝ^{2n}`
  let S₁ : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).toLinearMap
  let S₂ : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).toLinearMap
  let S₃ : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).toLinearMap
  let S₄ : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))) :=
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).toLinearMap
  -- ## the derivatives of the flattening chart at the two double points are linear equivalences
  have hbij₁ : Function.Bijective (fderiv ℝ Φ₀ (f p₁)) := by
    have hchainL : (fderiv ℝ Φ₀ (f p₁)).comp (fderiv ℝ Θ₀ (Φ₀ (f p₁))) = 1 := by
      have hdΦ' : DifferentiableAt ℝ Φ₀ (Θ₀ (Φ₀ (f p₁))) := by
        rw [hΘΦ (f p₁)]; exact hdΦp
      have hcomp := fderiv_comp (x := Φ₀ (f p₁)) (g := Φ₀) (f := Θ₀) hdΦ' hdΘp
      have h1 : fderiv ℝ (Φ₀ ∘ Θ₀) (Φ₀ (f p₁)) = 1 := by
        rw [show (Φ₀ ∘ Θ₀) = id from funext hΦΘ, fderiv_id]
        rfl
      rw [h1] at hcomp
      rw [hΘΦ (f p₁)] at hcomp
      exact hcomp.symm
    have hchainR : (fderiv ℝ Θ₀ (Φ₀ (f p₁))).comp (fderiv ℝ Φ₀ (f p₁)) = 1 := by
      have hcomp := fderiv_comp (x := f p₁) (g := Θ₀) (f := Φ₀) hdΘp hdΦp
      have h1 : fderiv ℝ (Θ₀ ∘ Φ₀) (f p₁) = 1 := by
        rw [show (Θ₀ ∘ Φ₀) = id from funext hΘΦ, fderiv_id]
        rfl
      rw [h1] at hcomp
      exact hcomp.symm
    have hleft : ∀ z : Work.Drive.Whitney.Mdl k,
        (fderiv ℝ Φ₀ (f p₁)) ((fderiv ℝ Θ₀ (Φ₀ (f p₁))) z) = z := by
      intro z
      have hh := congrArg (fun (L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) =>
        L z) hchainL
      simpa [ContinuousLinearMap.comp_apply] using hh
    have hright : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
        (fderiv ℝ Θ₀ (Φ₀ (f p₁))) ((fderiv ℝ Φ₀ (f p₁)) y) = y := by
      intro y
      have hh := congrArg (fun (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n))) => L y) hchainR
      simpa [ContinuousLinearMap.comp_apply] using hh
    exact ⟨fun x y hxy => by
        have hx := hright x
        rw [hxy] at hx
        exact hx.symm.trans (hright y),
      fun z => ⟨(fderiv ℝ Θ₀ (Φ₀ (f p₁))) z, hleft z⟩⟩
  have hbij₃ : Function.Bijective (fderiv ℝ Φ₀ (f q₁)) := by
    have hchainL : (fderiv ℝ Φ₀ (f q₁)).comp (fderiv ℝ Θ₀ (Φ₀ (f q₁))) = 1 := by
      have hdΦ' : DifferentiableAt ℝ Φ₀ (Θ₀ (Φ₀ (f q₁))) := by
        rw [hΘΦ (f q₁)]; exact hdΦq
      have hcomp := fderiv_comp (x := Φ₀ (f q₁)) (g := Φ₀) (f := Θ₀) hdΦ' hdΘq
      have h1 : fderiv ℝ (Φ₀ ∘ Θ₀) (Φ₀ (f q₁)) = 1 := by
        rw [show (Φ₀ ∘ Θ₀) = id from funext hΦΘ, fderiv_id]
        rfl
      rw [h1] at hcomp
      rw [hΘΦ (f q₁)] at hcomp
      exact hcomp.symm
    have hchainR : (fderiv ℝ Θ₀ (Φ₀ (f q₁))).comp (fderiv ℝ Φ₀ (f q₁)) = 1 := by
      have hcomp := fderiv_comp (x := f q₁) (g := Θ₀) (f := Φ₀) hdΘq hdΦq
      have h1 : fderiv ℝ (Θ₀ ∘ Φ₀) (f q₁) = 1 := by
        rw [show (Θ₀ ∘ Φ₀) = id from funext hΘΦ, fderiv_id]
        rfl
      rw [h1] at hcomp
      exact hcomp.symm
    have hleft : ∀ z : Work.Drive.Whitney.Mdl k,
        (fderiv ℝ Φ₀ (f q₁)) ((fderiv ℝ Θ₀ (Φ₀ (f q₁))) z) = z := by
      intro z
      have hh := congrArg (fun (L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) =>
        L z) hchainL
      simpa [ContinuousLinearMap.comp_apply] using hh
    have hright : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
        (fderiv ℝ Θ₀ (Φ₀ (f q₁))) ((fderiv ℝ Φ₀ (f q₁)) y) = y := by
      intro y
      have hh := congrArg (fun (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n))) => L y) hchainR
      simpa [ContinuousLinearMap.comp_apply] using hh
    exact ⟨fun x y hxy => by
        have hx := hright x
        rw [hxy] at hx
        exact hx.symm.trans (hright y),
      fun z => ⟨(fderiv ℝ Θ₀ (Φ₀ (f q₁))) z, hleft z⟩⟩
  -- ## the first sheet is flat: the tangent planes along the arc are carried onto `sheetA`
  have hA₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y)) := by
    simpa only [Function.comp_def] using h.toContinuousLinearMap.contDiff.comp hΦ₀sm
  have hmem₁ : ∀ᶠ x in 𝓝 p₁,
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y)) (f x) ∈
        Submodule.map h.toContinuousLinearMap.toLinearMap (sheetASub k) := by
    filter_upwards [hUo.mem_nhds hp₁U] with x hx
    exact Submodule.mem_map.mpr ⟨Φ₀ (f x), hsheet x (subset_closure hx), rfl⟩
  have hmem₄ : ∀ᶠ x in 𝓝 q₁,
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y)) (f x) ∈
        Submodule.map h.toContinuousLinearMap.toLinearMap (sheetASub k) := by
    filter_upwards [hUo.mem_nhds hq₁U] with x hx
    exact Submodule.mem_map.mpr ⟨Φ₀ (f x), hsheet x (subset_closure hx), rfl⟩
  have hle₁ : Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₁ ≤ sheetASub k := by
    have hle := Work.Drive.Whitney.map_fderiv_range_le_of_eventually_mem
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y)) hA₀sm hf hmem₁
    have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y))
          (f p₁) = h.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f p₁)) := by
      have hcomp := (h.toContinuousLinearMap.hasFDerivAt.comp (f p₁) hdΦp.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    have hcomp2 : (h.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f p₁))).toLinearMap
        = h.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ₀ (f p₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    have hker : LinearMap.ker h.toContinuousLinearMap.toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact fun x y hxy => h.injective hxy
    have hle₂ : Submodule.map (h.toContinuousLinearMap.toLinearMap.comp
          (fderiv ℝ Φ₀ (f p₁)).toLinearMap) S₁ ≤
        Submodule.map h.toContinuousLinearMap.toLinearMap (sheetASub k) := by
      rw [← hcomp2, ← hder]
      exact hle
    rw [Submodule.map_comp] at hle₂
    exact (LinearMap.map_le_map_iff' hker).mp hle₂
  have hle₄ : Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₄ ≤ sheetASub k := by
    have hle := Work.Drive.Whitney.map_fderiv_range_le_of_eventually_mem
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y)) hA₀sm hf hmem₄
    have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => h.toContinuousLinearMap (Φ₀ y))
          (f q₁) = h.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f q₁)) := by
      have hcomp := (h.toContinuousLinearMap.hasFDerivAt.comp (f q₁) hdΦq.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    have hcomp2 : (h.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f q₁))).toLinearMap
        = h.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ₀ (f q₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    have hker : LinearMap.ker h.toContinuousLinearMap.toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact fun x y hxy => h.injective hxy
    have hle₂ : Submodule.map (h.toContinuousLinearMap.toLinearMap.comp
          (fderiv ℝ Φ₀ (f q₁)).toLinearMap) S₄ ≤
        Submodule.map h.toContinuousLinearMap.toLinearMap (sheetASub k) := by
      rw [← hcomp2, ← hder]
      exact hle
    rw [Submodule.map_comp] at hle₂
    exact (LinearMap.map_le_map_iff' hker).mp hle₂
  have hfin₁ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₁) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ₀ (f p₁)).toLinearMap) hbij₁.injective S₁]
    dsimp only [S₁]
    exact (finrank_range_mfderiv_self f himm p₁).trans hk
  have hfin₄ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₄) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ₀ (f q₁)).toLinearMap) hbij₃.injective S₄]
    dsimp only [S₄]
    exact (finrank_range_mfderiv_self f himm q₁).trans hk
  have hS₁eq₁ : Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₁ = sheetASub k := by
    refine Submodule.eq_of_le_of_finrank_eq hle₁ ?_
    exact hfin₁.trans (finrank_sheetASub k).symm
  have hS₄eq : Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₄ = sheetASub k := by
    refine Submodule.eq_of_le_of_finrank_eq hle₄ ?_
    exact hfin₄.trans (finrank_sheetASub k).symm
  -- ## the two planes of the second sheet, pushed into the model space
  have hdim₂ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₂) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ₀ (f p₁)).toLinearMap) hbij₁.injective S₂]
    dsimp only [S₂]
    exact (finrank_range_mfderiv_self f himm p₂).trans hk
  have hsup₂ : sheetASub k ⊔ Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₂ = ⊤ := by
    have hsurj : LinearMap.range (fderiv ℝ Φ₀ (f p₁)).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hbij₁.surjective
    have htr : S₁ ⊔ S₂ = ⊤ := htransP
    have hmap : Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap (S₁ ⊔ S₂) = ⊤ := by
      rw [htr, Submodule.map_top, hsurj]
    rw [Submodule.map_sup, hS₁eq₁] at hmap
    exact hmap
  have hdim₃ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₃) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ₀ (f q₁)).toLinearMap) hbij₃.injective S₃]
    dsimp only [S₃]
    exact (finrank_range_mfderiv_self f himm q₂).trans hk
  have hsup₃ : sheetASub k ⊔ Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₃ = ⊤ := by
    have hsurj : LinearMap.range (fderiv ℝ Φ₀ (f q₁)).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hbij₃.surjective
    have htr : S₄ ⊔ S₃ = ⊤ := htransQ
    have hmap : Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap (S₄ ⊔ S₃) = ⊤ := by
      rw [htr, Submodule.map_top, hsurj]
    rw [Submodule.map_sup, hS₄eq] at hmap
    exact hmap
  -- ## the shear that makes both planes graphs over the `(x,v)`-plane
  obtain ⟨M', hM'sheet, hM'one, hM'neg, hM'T₂, hM'T₃⟩ :=
    exists_linearEquiv_sheetA_two_planes
      (Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₂)
      (Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₃) hdim₂ hdim₃ hsup₂ hsup₃
  -- ## the chart and its inverse
  let Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k :=
    fun y => M'.toContinuousLinearMap (Φ₀ y)
  let Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun ξ => Θ₀ (M'.symm.toContinuousLinearMap ξ)
  have hM'sheetL : ∀ a ∈ sheetASub k, M'.toContinuousLinearMap a ∈ sheetASub k := by
    intro a ha
    rw [lc_apply]
    exact hM'sheet a ha
  have hM'negL : M'.toContinuousLinearMap (((-1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k)
      = (((-1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    rw [lc_apply]; exact hM'neg
  have hM'oneL : M'.toContinuousLinearMap (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k)
      = (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    rw [lc_apply]; exact hM'one
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    simpa only [Function.comp_def] using M'.toContinuousLinearMap.contDiff.comp hΦ₀sm
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := by
    simpa only [Function.comp_def] using hΘ₀sm.comp M'.symm.toContinuousLinearMap.contDiff
  refine ⟨k, hk, Φ, Θ, U, hΦsm, hΘsm, ?_, ?_, hUo, hUarc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    show Θ₀ (M'.symm.toContinuousLinearMap (M'.toContinuousLinearMap (Φ₀ y))) = y
    rw [lc_symm_apply_apply, hΘΦ y]
  · intro ξ
    show M'.toContinuousLinearMap (Φ₀ (Θ₀ (M'.symm.toContinuousLinearMap ξ))) = ξ
    rw [hΦΘ (M'.symm.toContinuousLinearMap ξ)]
    exact lc_apply_symm M' ξ
  · exact fun x hx => hUcl (subset_closure hx)
  · intro x hx
    exact hM'sheetL (Φ₀ (f x)) (hsheet x (subset_closure hx))
  · show M'.toContinuousLinearMap (Φ₀ (f p₁)) = ((-1 : ℝ), 0, 0, 0)
    rw [hΦp₁, hM'negL]
  · show M'.toContinuousLinearMap (Φ₀ (f q₁)) = ((1 : ℝ), 0, 0, 0)
    rw [hΦq₁, hM'oneL]
  · change Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₂ ⊓ kerXV k = ⊥
    have hder : fderiv ℝ Φ (f p₁) = M'.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f p₁)) := by
      have hcomp := (M'.toContinuousLinearMap.hasFDerivAt.comp (f p₁) hdΦp.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    rw [hder]
    have hcomp2 : (M'.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f p₁))).toLinearMap
        = M'.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ₀ (f p₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    rw [hcomp2, Submodule.map_comp]
    exact map_inf_kerXV_eq_bot (F := M'.toContinuousLinearMap.toLinearMap)
      (T := Submodule.map (fderiv ℝ Φ₀ (f p₁)).toLinearMap S₂)
      (fun t ht h => hM'T₂ t ht (show M' t ∈ kerXV k from h))
  · change Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₃ ⊓ kerXV k = ⊥
    have hder : fderiv ℝ Φ (f q₁) = M'.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f q₁)) := by
      have hcomp := (M'.toContinuousLinearMap.hasFDerivAt.comp (f q₁) hdΦq.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    rw [hder]
    have hcomp2 : (M'.toContinuousLinearMap.comp (fderiv ℝ Φ₀ (f q₁))).toLinearMap
        = M'.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ₀ (f q₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    rw [hcomp2, Submodule.map_comp]
    exact map_inf_kerXV_eq_bot (F := M'.toContinuousLinearMap.toLinearMap)
      (T := Submodule.map (fderiv ℝ Φ₀ (f q₁)).toLinearMap S₃)
      (fun t ht h => hM'T₃ t ht (show M' t ∈ kerXV k from h))

end Work.Drive.PushDisc
