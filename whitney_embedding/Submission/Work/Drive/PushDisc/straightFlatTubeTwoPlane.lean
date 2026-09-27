import Mathlib
import Submission.Work.Drive.PushDisc.exists_straightFlatTube
import Submission.Work.Drive.PushDisc.sheetATwoPlaneShear
import Submission.Work.Drive.PushDisc.exists_chart_twoPlaneFraming

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff Topology
open Set Metric Filter

set_option maxHeartbeats 1000000

/-!
# The straight flat tube with the two-plane framing

`Work.Drive.PushDisc.exists_straightFlatTube` produces the flat tube of the first sheet with the
arc's image straightened (the segment row `hU₁seg`).  `Work.Drive.PushDisc.exists_chart_twoPlaneFraming`
produces a chart with the two *tangent planes* of the second sheet at the double points transverse to
`kerXV k`.  This file *merges* the two rows: the same chart carries both the straightened segment and
the two-plane framing.

The merge is possible because both properties are invariant under post-composition of the chart with
the elementary shear `L_c (x, y, u, v) = (x + c y, y, u, v)` of
`Work.Drive.PushDisc.sheetATwoPlaneShear`:

* the shear fixes `sheetA` **pointwise**, hence preserves the flatness row, the pinning rows and the
  straightened segment row;
* the shear is a linear isomorphism, hence preserves the two inverse rows;
* and `exists_shear_transverse_two_planes` chooses `c` so that the two pushed tangent planes miss
  `kerXV k`.

The only extra input is the *transversality of the first sheet*: for the chart `Φ` of
`exists_straightFlatTube` the pushed tangent plane of the **first** sheet at `p₁` (resp. `q₁`) is
`sheetASub k` — this is `map_fderiv_range_le_of_eventually_mem` plus equal dimensions
(`exists_shear_twoPlanes_of_flatChart` below).
-/

/-! ## Auxiliary facts about the elementary shear -/

/-- The continuous-linear-map form of the shear has the same underlying function. -/
theorem shear_toCLM_apply {k : ℕ} (c : ℝ) (x : Work.Drive.Whitney.Mdl k) :
    (shear k c).toContinuousLinearMap x = shear k c x := rfl

/-- The shear with `-c` inverts the shear with `c`. -/
theorem shear_neg_comp_shear {k : ℕ} (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    shear k (-c) (shear k c ξ) = ξ := by
  rw [shear_apply, shear_apply]
  ext <;> simp <;> ring

/-- The shear with `c` inverts the shear with `-c`. -/
theorem shear_comp_shear_neg {k : ℕ} (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    shear k c (shear k (-c) ξ) = ξ := by
  rw [shear_apply, shear_apply]
  ext <;> simp <;> ring

/-- **The shear fixes the first sheet pointwise** (not only setwise): it changes only the `x`
coordinate, and `y = 0` on `sheetA`. -/
theorem shear_fixes_sheetASub {k : ℕ} (c : ℝ) {ξ : Work.Drive.Whitney.Mdl k}
    (hξ : ξ ∈ sheetASub k) : shear k c ξ = ξ := by
  rw [shear_apply]
  have h1 : ξ.2.1 = 0 := hξ.1
  rw [h1, mul_zero, zero_smul, add_zero]

/-! ## The two-plane framing of an already flat chart -/

/-- **The two-plane framing of a flat chart.**  Let `Φ` be a chart of `ℝ^{2n}` (with inverse `Θ`)
which is flat over the open set `U` (i.e. `Φ (f x) ∈ sheetA` for `x ∈ U`) and let `U ∋ p₁, q₁`.  If the
tangent plane of the second sheet at `p₂` (resp. `q₂`) is transverse to the tangent plane of the first
sheet at `p₁` (resp. `q₁`) — the hypotheses `htransP`, `htransQ` — then there is a shear `c` of the
model space such that, after post-composition with it, the pushed tangent planes of the second sheet
at the two double points both miss `kerXV k`.

The shear keeps `sheetA` pointwise, the two model double points, and the flatness of the tube, so it
can be applied to the chart of `exists_straightFlatTube` without destroying any of its rows. -/
theorem exists_shear_twoPlanes_of_flatChart {n k : ℕ} (hk : n = k + 1)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (p₁ p₂ q₁ q₂ : M)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (U : Set M) (hUo : IsOpen U) (hp₁U : p₁ ∈ U) (hq₁U : q₁ ∈ U)
    (hsheet : ∀ x : M, x ∈ U → Φ (f x) ∈ Work.Drive.Whitney.sheetA) :
    ∃ c : ℝ,
      (Submodule.map (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ y)) (f p₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) ∧
      (Submodule.map (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ y)) (f q₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) := by
  classical
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
  let hE : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := mdlEquivL hk
  have hdΦp : DifferentiableAt ℝ Φ (f p₁) := (hΦsm.differentiable (by simp)).differentiableAt
  have hdΦq : DifferentiableAt ℝ Φ (f q₁) := (hΦsm.differentiable (by simp)).differentiableAt
  have hdΘp : DifferentiableAt ℝ Θ (Φ (f p₁)) := (hΘsm.differentiable (by simp)).differentiableAt
  have hdΘq : DifferentiableAt ℝ Θ (Φ (f q₁)) := (hΘsm.differentiable (by simp)).differentiableAt
  -- ## `fderiv Φ` at the two double points is a linear equivalence
  have hbij₁ : Function.Bijective (fderiv ℝ Φ (f p₁)) := by
    have hchainL : (fderiv ℝ Φ (f p₁)).comp (fderiv ℝ Θ (Φ (f p₁))) = 1 := by
      have hdΦ' : DifferentiableAt ℝ Φ (Θ (Φ (f p₁))) := by
        rw [hΘΦ (f p₁)]; exact hdΦp
      have hcomp := fderiv_comp (x := Φ (f p₁)) (g := Φ) (f := Θ) hdΦ' hdΘp
      have h1 : fderiv ℝ (Φ ∘ Θ) (Φ (f p₁)) = 1 := by
        rw [show (Φ ∘ Θ) = id from funext hΦΘ, fderiv_id]
        rfl
      rw [h1] at hcomp
      rw [hΘΦ (f p₁)] at hcomp
      exact hcomp.symm
    have hchainR : (fderiv ℝ Θ (Φ (f p₁))).comp (fderiv ℝ Φ (f p₁)) = 1 := by
      have hcomp := fderiv_comp (x := f p₁) (g := Θ) (f := Φ) hdΘp hdΦp
      have h1 : fderiv ℝ (Θ ∘ Φ) (f p₁) = 1 := by
        rw [show (Θ ∘ Φ) = id from funext hΘΦ, fderiv_id]
        rfl
      rw [h1] at hcomp
      exact hcomp.symm
    have hleft : ∀ z : Work.Drive.Whitney.Mdl k,
        (fderiv ℝ Φ (f p₁)) ((fderiv ℝ Θ (Φ (f p₁))) z) = z := by
      intro z
      have hh := congrArg (fun (L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) =>
        L z) hchainL
      simpa [ContinuousLinearMap.comp_apply] using hh
    have hright : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
        (fderiv ℝ Θ (Φ (f p₁))) ((fderiv ℝ Φ (f p₁)) y) = y := by
      intro y
      have hh := congrArg (fun (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n))) => L y) hchainR
      simpa [ContinuousLinearMap.comp_apply] using hh
    exact ⟨fun x y hxy => by
        have hx := hright x
        rw [hxy] at hx
        exact hx.symm.trans (hright y),
      fun z => ⟨(fderiv ℝ Θ (Φ (f p₁))) z, hleft z⟩⟩
  have hbij₃ : Function.Bijective (fderiv ℝ Φ (f q₁)) := by
    have hchainL : (fderiv ℝ Φ (f q₁)).comp (fderiv ℝ Θ (Φ (f q₁))) = 1 := by
      have hdΦ' : DifferentiableAt ℝ Φ (Θ (Φ (f q₁))) := by
        rw [hΘΦ (f q₁)]; exact hdΦq
      have hcomp := fderiv_comp (x := Φ (f q₁)) (g := Φ) (f := Θ) hdΦ' hdΘq
      have h1 : fderiv ℝ (Φ ∘ Θ) (Φ (f q₁)) = 1 := by
        rw [show (Φ ∘ Θ) = id from funext hΦΘ, fderiv_id]
        rfl
      rw [h1] at hcomp
      rw [hΘΦ (f q₁)] at hcomp
      exact hcomp.symm
    have hchainR : (fderiv ℝ Θ (Φ (f q₁))).comp (fderiv ℝ Φ (f q₁)) = 1 := by
      have hcomp := fderiv_comp (x := f q₁) (g := Θ) (f := Φ) hdΘq hdΦq
      have h1 : fderiv ℝ (Θ ∘ Φ) (f q₁) = 1 := by
        rw [show (Θ ∘ Φ) = id from funext hΘΦ, fderiv_id]
        rfl
      rw [h1] at hcomp
      exact hcomp.symm
    have hleft : ∀ z : Work.Drive.Whitney.Mdl k,
        (fderiv ℝ Φ (f q₁)) ((fderiv ℝ Θ (Φ (f q₁))) z) = z := by
      intro z
      have hh := congrArg (fun (L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) =>
        L z) hchainL
      simpa [ContinuousLinearMap.comp_apply] using hh
    have hright : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
        (fderiv ℝ Θ (Φ (f q₁))) ((fderiv ℝ Φ (f q₁)) y) = y := by
      intro y
      have hh := congrArg (fun (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n))) => L y) hchainR
      simpa [ContinuousLinearMap.comp_apply] using hh
    exact ⟨fun x y hxy => by
        have hx := hright x
        rw [hxy] at hx
        exact hx.symm.trans (hright y),
      fun z => ⟨(fderiv ℝ Θ (Φ (f q₁))) z, hleft z⟩⟩
  -- ## the first sheet is flat: the pushed tangent plane at `p₁` is `sheetA`
  have hA₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => hE.toContinuousLinearMap (Φ y)) := by
    simpa only [Function.comp_def] using hE.toContinuousLinearMap.contDiff.comp hΦsm
  have hmem₁ : ∀ᶠ x in 𝓝 p₁,
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => hE.toContinuousLinearMap (Φ y)) (f x) ∈
        Submodule.map hE.toContinuousLinearMap.toLinearMap (sheetASub k) := by
    filter_upwards [hUo.mem_nhds hp₁U] with x hx
    exact Submodule.mem_map.mpr ⟨Φ (f x), hsheet x hx, rfl⟩
  have hmem₄ : ∀ᶠ x in 𝓝 q₁,
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => hE.toContinuousLinearMap (Φ y)) (f x) ∈
        Submodule.map hE.toContinuousLinearMap.toLinearMap (sheetASub k) := by
    filter_upwards [hUo.mem_nhds hq₁U] with x hx
    exact Submodule.mem_map.mpr ⟨Φ (f x), hsheet x hx, rfl⟩
  have hle₁ : Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₁ ≤ sheetASub k := by
    have hle := Work.Drive.Whitney.map_fderiv_range_le_of_eventually_mem
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => hE.toContinuousLinearMap (Φ y)) hA₀sm hf hmem₁
    have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          hE.toContinuousLinearMap (Φ y)) (f p₁)
        = hE.toContinuousLinearMap.comp (fderiv ℝ Φ (f p₁)) := by
      have hcomp := (hE.toContinuousLinearMap.hasFDerivAt.comp (f p₁) hdΦp.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    have hcomp2 : (hE.toContinuousLinearMap.comp (fderiv ℝ Φ (f p₁))).toLinearMap
        = hE.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ (f p₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    have hker : LinearMap.ker hE.toContinuousLinearMap.toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact fun x y hxy => hE.injective hxy
    have hle₂ : Submodule.map (hE.toContinuousLinearMap.toLinearMap.comp
          (fderiv ℝ Φ (f p₁)).toLinearMap) S₁ ≤
        Submodule.map hE.toContinuousLinearMap.toLinearMap (sheetASub k) := by
      rw [← hcomp2, ← hder]
      exact hle
    rw [Submodule.map_comp] at hle₂
    exact (LinearMap.map_le_map_iff' hker).mp hle₂
  have hle₄ : Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₄ ≤ sheetASub k := by
    have hle := Work.Drive.Whitney.map_fderiv_range_le_of_eventually_mem
      (fun y : EuclideanSpace ℝ (Fin (2 * n)) => hE.toContinuousLinearMap (Φ y)) hA₀sm hf hmem₄
    have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          hE.toContinuousLinearMap (Φ y)) (f q₁)
        = hE.toContinuousLinearMap.comp (fderiv ℝ Φ (f q₁)) := by
      have hcomp := (hE.toContinuousLinearMap.hasFDerivAt.comp (f q₁) hdΦq.hasFDerivAt).fderiv
      simpa only [Function.comp_def] using hcomp
    have hcomp2 : (hE.toContinuousLinearMap.comp (fderiv ℝ Φ (f q₁))).toLinearMap
        = hE.toContinuousLinearMap.toLinearMap.comp (fderiv ℝ Φ (f q₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    have hker : LinearMap.ker hE.toContinuousLinearMap.toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact fun x y hxy => hE.injective hxy
    have hle₂ : Submodule.map (hE.toContinuousLinearMap.toLinearMap.comp
          (fderiv ℝ Φ (f q₁)).toLinearMap) S₄ ≤
        Submodule.map hE.toContinuousLinearMap.toLinearMap (sheetASub k) := by
      rw [← hcomp2, ← hder]
      exact hle
    rw [Submodule.map_comp] at hle₂
    exact (LinearMap.map_le_map_iff' hker).mp hle₂
  have hfin₁ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₁) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ (f p₁)).toLinearMap) hbij₁.injective S₁]
    dsimp only [S₁]
    exact (finrank_range_mfderiv_self f himm p₁).trans hk
  have hS₁eq₁ : Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₁ = sheetASub k :=
    Submodule.eq_of_le_of_finrank_eq hle₁ (hfin₁.trans (finrank_sheetASub k).symm)
  have hfin₄ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₄) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ (f q₁)).toLinearMap) hbij₃.injective S₄]
    dsimp only [S₄]
    exact (finrank_range_mfderiv_self f himm q₁).trans hk
  have hS₄eq : Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₄ = sheetASub k :=
    Submodule.eq_of_le_of_finrank_eq hle₄ (hfin₄.trans (finrank_sheetASub k).symm)
  -- ## the two planes of the second sheet, pushed into the model space
  have hdim₂ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₂) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ (f p₁)).toLinearMap) hbij₁.injective S₂]
    dsimp only [S₂]
    exact (finrank_range_mfderiv_self f himm p₂).trans hk
  have hsup₂ : sheetASub k ⊔ Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₂ = ⊤ := by
    have hsurj : LinearMap.range (fderiv ℝ Φ (f p₁)).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hbij₁.surjective
    have htr : S₁ ⊔ S₂ = ⊤ := htransP
    have hmap : Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap (S₁ ⊔ S₂) = ⊤ := by
      rw [htr, Submodule.map_top, hsurj]
    rw [Submodule.map_sup, hS₁eq₁] at hmap
    exact hmap
  have hdim₃ : Module.finrank ℝ (Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₃) = k + 1 := by
    rw [finrank_map_eq_of_injective (L := (fderiv ℝ Φ (f q₁)).toLinearMap) hbij₃.injective S₃]
    dsimp only [S₃]
    exact (finrank_range_mfderiv_self f himm q₂).trans hk
  have hsup₃ : sheetASub k ⊔ Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₃ = ⊤ := by
    have hsurj : LinearMap.range (fderiv ℝ Φ (f q₁)).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hbij₃.surjective
    have htr : S₄ ⊔ S₃ = ⊤ := htransQ
    have hmap : Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap (S₄ ⊔ S₃) = ⊤ := by
      rw [htr, Submodule.map_top, hsurj]
    rw [Submodule.map_sup, hS₄eq] at hmap
    exact hmap
  -- ## the shear that makes both planes graphs over the `(x,v)`-plane
  obtain ⟨c, hc₁, hc₂⟩ := exists_shear_transverse_two_planes
    (Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₂)
    (Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₃) hdim₂ hdim₃ hsup₂ hsup₃
  refine ⟨c, ?_, ?_⟩
  · have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ y)) (f p₁)
        = (shear k c).toContinuousLinearMap.comp (fderiv ℝ Φ (f p₁)) := by
      have hcomp :=
        ((shear k c).toContinuousLinearMap.hasFDerivAt.comp (f p₁) hdΦp.hasFDerivAt).fderiv
      simpa only [Function.comp_def, shear_toCLM_apply] using hcomp
    rw [hder]
    have hcomp2 : ((shear k c).toContinuousLinearMap.comp (fderiv ℝ Φ (f p₁))).toLinearMap
        = (shear k c).toContinuousLinearMap.toLinearMap.comp
            (fderiv ℝ Φ (f p₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    rw [hcomp2, Submodule.map_comp]
    exact map_inf_kerXV_eq_bot (F := (shear k c).toContinuousLinearMap.toLinearMap)
      (T := Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap S₂)
      (fun t ht hh => hc₁ t ht (show shear k c t ∈ kerXV k from hh))
  · have hder : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ y)) (f q₁)
        = (shear k c).toContinuousLinearMap.comp (fderiv ℝ Φ (f q₁)) := by
      have hcomp :=
        ((shear k c).toContinuousLinearMap.hasFDerivAt.comp (f q₁) hdΦq.hasFDerivAt).fderiv
      simpa only [Function.comp_def, shear_toCLM_apply] using hcomp
    rw [hder]
    have hcomp2 : ((shear k c).toContinuousLinearMap.comp (fderiv ℝ Φ (f q₁))).toLinearMap
        = (shear k c).toContinuousLinearMap.toLinearMap.comp
            (fderiv ℝ Φ (f q₁)).toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_comp]
    rw [hcomp2, Submodule.map_comp]
    exact map_inf_kerXV_eq_bot (F := (shear k c).toContinuousLinearMap.toLinearMap)
      (T := Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap S₃)
      (fun t ht hh => hc₂ t ht (show shear k c t ∈ kerXV k from hh))

/-! ## The straight flat tube with the two-plane framing -/

theorem straightFlatTubeTwoPlane {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W) (hp₁p₂ : p₁ ≠ p₂)
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
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (hk : n = k + 1)
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
      (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (U₁ : Set M) (δ₀ : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y) ∧
      (∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ) ∧
      IsOpen U₁ ∧ U₁ ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁ ∧ p₂ ∉ U₁ ∧ q₂ ∉ U₁ ∧
      (∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA) ∧
      0 < δ₀ ∧ (∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ (f z) = (x, 0, 0, 0)) ∧
      Φ (f p₁) = ((-1 : ℝ), 0, 0, 0) ∧ Φ (f q₁) = ((1 : ℝ), 0, 0, 0) ∧
      (Submodule.map (fderiv ℝ Φ (f p₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) ∧
      (Submodule.map (fderiv ℝ Φ (f q₁)).toLinearMap
        (LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).toLinearMap) ⊓
        Work.Drive.PushDisc.kerXV k = ⊥) := by
  classical
  obtain ⟨k, hk, Φ₀, Θ₀, U₁, δ₀, hΦ₀sm, hΘ₀sm, hΘΦ, hΦΘ, hUo, hUW, hUarc, hp₂U, hq₂U,
    hsheet, hδ₀, hseg, hpin₁, hpin₂⟩ :=
    exists_straightFlatTube hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃ hp₁p₂ hfp hclean
      hsep γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm hp₂arc hq₂arc
  have hp₁U : p₁ ∈ U₁ := hUarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₁0⟩
  have hq₁U : q₁ ∈ U₁ := hUarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₁1⟩
  obtain ⟨c, hc₁, hc₂⟩ := exists_shear_twoPlanes_of_flatChart hk f hf himm p₁ p₂ q₁ q₂ htransP
    htransQ Φ₀ Θ₀ hΦ₀sm hΘ₀sm hΘΦ hΦΘ U₁ hUo hp₁U hq₁U hsheet
  refine ⟨k, hk, (fun y : EuclideanSpace ℝ (Fin (2 * n)) => shear k c (Φ₀ y)),
    (fun ξ : Work.Drive.Whitney.Mdl k => Θ₀ (shear k (-c) ξ)), U₁, δ₀,
    ?_, ?_, ?_, ?_, hUo, hUW, hUarc, hp₂U, hq₂U, ?_, hδ₀, ?_, ?_, ?_, hc₁, hc₂⟩
  · -- smoothness of the sheared chart
    simpa only [Function.comp_def, shear_toCLM_apply] using
      ((shear k c).toContinuousLinearMap.contDiff).comp hΦ₀sm
  · -- smoothness of the sheared inverse
    simpa only [Function.comp_def, shear_toCLM_apply] using
      hΘ₀sm.comp ((shear k (-c)).toContinuousLinearMap.contDiff)
  · -- `Θ' ∘ Φ' = id`
    intro y
    show Θ₀ (shear k (-c) (shear k c (Φ₀ y))) = y
    rw [shear_neg_comp_shear, hΘΦ y]
  · -- `Φ' ∘ Θ' = id`
    intro ξ
    show shear k c (Φ₀ (Θ₀ (shear k (-c) ξ))) = ξ
    rw [hΦΘ (shear k (-c) ξ), shear_comp_shear_neg]
  · -- the tube is flat for the sheared chart
    intro x hx
    have hfix := shear_fixes_sheetASub c (hsheet x hx)
    show shear k c (Φ₀ (f x)) ∈ Work.Drive.Whitney.sheetA
    rw [hfix]
    exact hsheet x hx
  · -- the straightened segment
    intro x hx
    obtain ⟨z, hzU, hz⟩ := hseg x hx
    refine ⟨z, hzU, ?_⟩
    show shear k c (Φ₀ (f z)) = (x, 0, 0, 0)
    rw [hz]
    exact shear_fixes_sheetASub c (ξ := ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k)) ⟨rfl, rfl⟩
  · -- the first pin
    show shear k c (Φ₀ (f p₁)) = ((-1 : ℝ), 0, 0, 0)
    rw [hpin₁]
    exact shear_fixes_sheetASub c (ξ := (((-1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
      ⟨rfl, rfl⟩
  · -- the second pin
    show shear k c (Φ₀ (f q₁)) = ((1 : ℝ), 0, 0, 0)
    rw [hpin₂]
    exact shear_fixes_sheetASub c (ξ := (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
      ⟨rfl, rfl⟩

end Work.Drive.PushDisc
