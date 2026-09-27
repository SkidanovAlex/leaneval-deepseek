import Mathlib
import Submission.Work.Whitney.OrientedAtlas
import Submission.Work.Whitney.PairDet
import Submission.Work.Projection.mfderiv_chartAt_decomp

/-!
# The Whitney push: definitions and analytic machinery

This module collects the definitions and the analytic (non-geometric) part of the Whitney push
used by `Work.Whitney.exists_manifold_push`:

* the bigon curve and its cone (the "Whitney disc" data) in the manifold setting
  (`bigonSrcM`, `bigonCurveM`, `coneM`, `HasConeData`);
* the *collar data* (`HasManifoldCollarData`) and the *radial push data*
  (`HasRadialPushData`): the two "placement" forms of the push, together with the reduction
  `collarData_of_radialPushData` of the former to the latter;
* the radial push `pushMapM` with its smoothness, its injectivity on a collar and the
  fact that it is an immersion (`injective_mfderiv_pushMapM`), deduced from the Euclidean
  linear algebra (`injective_of_add_rankOne`) through the chart decomposition
  `Work.Projection.mfderiv_chartAt_decomp`;
* the set-theoretic assembly `push_of_collar_data`: the collar data implies the conclusion of
  `Work.Whitney.exists_manifold_push`.

These results are kept in a module that does *not* import `exists_manifold_push`, so that the
geometric lemmas producing `HasConeData` / `HasRadialPushData` (which are stated in terms of
these definitions) can be proved in import-parallel and then consumed by the main theorem.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- The source points of the bigon circle: `γ₁` on the first half and `γ₂` reversed on the second. -/
noncomputable def bigonSrcM {M : Type*} (γ₁ γ₂ : ℝ → M) (s : ℝ) : M :=
  if s ≤ 1 then γ₁ s else γ₂ (2 - s)

/-- The bigon curve in the target: the union of the two arcs' images. -/
noncomputable def bigonCurveM {n : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (s : ℝ) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  f (bigonSrcM γ₁ γ₂ s)

/-- The cone with apex `z` over the bigon curve. -/
noncomputable def coneM {n : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (z : EuclideanSpace ℝ (Fin (2 * n))) (s t : ℝ) : EuclideanSpace ℝ (Fin (2 * n)) :=
  z + t • (bigonCurveM f γ₁ γ₂ s - z)

variable {n : ℕ}

/-- **The cone ("Whitney disc") data in the manifold setting.**  A point `z` such that the cone
over the bigon curve is embedded, meets the image of `f` only along its boundary, and the radial
direction from `z` is transverse to the sheet along the curve and at the second preimage `q₂` of
the second double point (`q₂` is not attained by `bigonSrcM`, so its transversality has to be
recorded separately). -/
def HasConeData {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (q₂ : M)
    (z : EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  z ∉ Set.range f ∧
  (∀ s ∈ Set.Icc (0:ℝ) 2, ∀ t ∈ Set.Ioo (0:ℝ) 1, coneM f γ₁ γ₂ z s t ∉ Set.range f) ∧
  (∀ s ∈ Set.Icc (0:ℝ) 2, ∀ s' ∈ Set.Icc (0:ℝ) 2, ∀ t ∈ Set.Ioo (0:ℝ) 1,
      ∀ t' ∈ Set.Ioo (0:ℝ) 1, coneM f γ₁ γ₂ z s t = coneM f γ₁ γ₂ z s' t' →
      ((s = s') ∨ (s = 0 ∧ s' = 2) ∨ (s = 2 ∧ s' = 0)) ∧ t = t') ∧
  (∀ s ∈ Set.Icc (0:ℝ) 2,
      (bigonCurveM f γ₁ γ₂ s - z) ∉
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (bigonSrcM γ₁ γ₂ s)).range) ∧
  (f q₂ - z) ∉
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range

/-- **The collar data of the Whitney push.**  A modification `i` of `f`, supported in an open
`W₀ ⊆ W` containing `p₂`, `q₂` but neither `p₁` nor `q₁`, which is an immersion, injective on
`W₀`, and whose image on `W₀` meets the image of `f` only inside the image of `W₀` itself (the
*placement* property), and which does not attain the two double point values `f p₂`, `f q₂`. -/
def HasManifoldCollarData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) : Prop :=
  ∃ (W₀ : Set M) (i : M → EuclideanSpace ℝ (Fin (2 * n))),
    IsOpen W₀ ∧ W₀ ⊆ W ∧ p₂ ∈ W₀ ∧ q₂ ∈ W₀ ∧ p₁ ∉ W₀ ∧ q₁ ∉ W₀ ∧
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) i ∧
    (∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) i y)) ∧
    Set.InjOn i W₀ ∧
    (∀ y : M, y ∉ W₀ → i y = f y) ∧
    i '' W₀ ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ ∧
    f p₂ ∉ i '' W₀ ∧ f q₂ ∉ i '' W₀


/-- **The data produced by the Whitney push**: a cut-off `χ` (supported in an open `W₀ ⊆ W` that
contains `p₂`, `q₂` but neither `p₁` nor `q₁`), non-negative and < 1, with the *placement* property
for the radial push `x ↦ χ x • z + (1 - χ x) • f x`, together with the two analytic side
conditions (transversality of the push direction to the sheet and injectivity of the radial
projection on `W₀`) that make the pushed map an immersion, injective on `W₀`. -/
def HasRadialPushData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (z : EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  ∃ (W₀ : Set M) (χ : M → ℝ),
    IsOpen W₀ ∧ W₀ ⊆ W ∧ p₂ ∈ W₀ ∧ q₂ ∈ W₀ ∧ p₁ ∉ W₀ ∧ q₁ ∉ W₀ ∧
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
    (∀ x : M, 0 ≤ χ x) ∧ (∀ x : M, χ x < 1) ∧
    (∀ x : M, x ∉ W₀ → χ x = 0) ∧
    (∀ x : M, x ∉ W₀ → ∀ᶠ y in 𝓝 x, χ y = 0) ∧ χ p₂ ≠ 0 ∧ χ q₂ ≠ 0 ∧
    (∀ x ∈ W₀, (f x - z) ∉
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x).range) ∧
    Set.InjOn (fun x : M => (‖f x - z‖)⁻¹ • (f x - z)) W₀ ∧
    (fun x : M => χ x • z + (1 - χ x) • f x) '' W₀ ⊆
      f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ ∧
    f p₂ ∉ (fun x : M => χ x • z + (1 - χ x) • f x) '' W₀ ∧
    f q₂ ∉ (fun x : M => χ x • z + (1 - χ x) • f x) '' W₀

/-! ## The radial push

The manifold version of the radial push `x ↦ χ x • z + (1 - χ x) • f x` and the two analytic
facts used below: it is an immersion whenever the cut-off does not saturate and the radial
direction `f x - z` is transverse to the sheet, and it is injective wherever the radial
projection `x ↦ (f x - z)/‖f x - z‖` is. -/

/-- The radial push of `f` towards the apex `z`, with cut-off `χ`. -/
noncomputable def pushMapM {M : Type*} (χ : M → ℝ)
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (z : EuclideanSpace ℝ (Fin (2 * n))) :
    M → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun x => χ x • z + (1 - χ x) • f x

theorem pushMapM_eq {M : Type*} (χ : M → ℝ)
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (z : EuclideanSpace ℝ (Fin (2 * n))) (x : M) :
    pushMapM χ f z x = z + (1 - χ x) • (f x - z) := by
  simp only [pushMapM]
  module

/-- The radial push is smooth. -/
theorem contMDiff_pushMapM {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {χ : M → ℝ} {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {z : EuclideanSpace ℝ (Fin (2 * n))}
    (hχ : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (pushMapM χ f z) := by
  have h1 : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => 1 - χ x) :=
    contMDiff_const.sub hχ
  have h2 : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => f x - z) :=
    hf.sub contMDiff_const
  have h3 : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (1 - χ x) • (f x - z)) := h1.smul h2
  have h4 : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => z + (1 - χ x) • (f x - z)) := contMDiff_const.add h3
  exact h4.congr (fun x => pushMapM_eq χ f z x)

/-- The radial push is injective on any set on which the radial projection
`x ↦ (f x - z)/‖f x - z‖` is injective and where the cut-off is non-negative and non-saturating. -/
theorem injOn_pushMapM {M : Type*} {χ : M → ℝ}
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {z : EuclideanSpace ℝ (Fin (2 * n))} {W : Set M}
    (hχ0 : ∀ x ∈ W, 0 ≤ χ x) (hχ1 : ∀ x ∈ W, χ x < 1)
    (hπ : Set.InjOn (fun x : M => (‖f x - z‖)⁻¹ • (f x - z)) W) :
    Set.InjOn (pushMapM χ f z) W := by
  intro u hu u' hu' h
  rw [pushMapM_eq, pushMapM_eq] at h
  have hkey : (1 - χ u) • (f u - z) = (1 - χ u') • (f u' - z) := add_left_cancel h
  have ha : (0:ℝ) < 1 - χ u := by linarith [hχ1 u hu]
  have ha' : (0:ℝ) < 1 - χ u' := by linarith [hχ1 u' hu']
  have hdir : f u - z = ((1 - χ u)⁻¹ * (1 - χ u')) • (f u' - z) := by
    have h4 : (1 - χ u)⁻¹ • ((1 - χ u) • (f u - z))
        = (1 - χ u)⁻¹ • ((1 - χ u') • (f u' - z)) := by rw [hkey]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h4
    exact h4
  have hc : (0:ℝ) < (1 - χ u)⁻¹ * (1 - χ u') := mul_pos (inv_pos.mpr ha) ha'
  have hnorm : (‖f u - z‖)⁻¹ • (f u - z) = (‖f u' - z‖)⁻¹ • (f u' - z) := by
    rw [hdir, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  exact hπ hu hu' hnorm

/-! ## The Euclidean linear algebra behind the push -/

/-- A linear map that is injective stays injective after adding a rank-one term `φ w • v`,
provided `v` is not in its range. -/
theorem injective_of_add_rankOne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hA : Function.Injective A)
    (v : F) (hv : v ∉ Set.range A) (φ : E →L[ℝ] ℝ) :
    Function.Injective (fun w : E => A w + φ w • v) := by
  intro w w' h
  have hzero : A (w - w') + φ (w - w') • v = 0 := by
    rw [map_sub, map_sub, sub_smul]
    rw [show A w - A w' + (φ w • v - φ w' • v) = (A w + φ w • v) - (A w' + φ w' • v)
      by abel]
    exact sub_eq_zero.mpr h
  rcases eq_or_ne (φ (w - w')) 0 with hφ | hφ
  · have hz : A (w - w') = 0 := by rw [hφ, zero_smul, add_zero] at hzero; exact hzero
    rw [← sub_eq_zero]
    exact hA (by rw [hz, map_zero])
  · exfalso
    have h4 : A (w - w') = -(φ (w - w') • v) := eq_neg_of_add_eq_zero_left hzero
    refine hv ⟨(-(φ (w - w'))⁻¹) • (w - w'), ?_⟩
    rw [map_smul, h4, smul_neg, smul_smul]
    rw [show (-(φ (w - w'))⁻¹) * φ (w - w') = -1 by rw [neg_mul, inv_mul_cancel₀ hφ]]
    rw [neg_one_smul, neg_neg]

/-- The Fréchet derivative of the Euclidean radial push `u ↦ χ u • z + (1 - χ u) • g u`. -/
theorem hasFDerivAt_radialPush {n : ℕ} {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    {z : EuclideanSpace ℝ (Fin (2 * n))} {u : EuclideanSpace ℝ (Fin n)}
    (hχ : HasFDerivAt χ (fderiv ℝ χ u) u) (hg : HasFDerivAt g (fderiv ℝ g u) u) :
    HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => χ v • z + (1 - χ v) • g v)
      ((1 - χ u) • fderiv ℝ g u + (fderiv ℝ χ u).smulRight (z - g u)) u := by
  have h1 : HasFDerivAt (fun v => χ v • z) ((fderiv ℝ χ u).smulRight z) u := hχ.smul_const z
  have h3 : HasFDerivAt (fun v => 1 - χ v)
      ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) - fderiv ℝ χ u) u :=
    (hasFDerivAt_const (1 : ℝ) u).sub hχ
  have h2 := h3.smul hg
  have htot := h1.add h2
  have hderiv : (fderiv ℝ χ u).smulRight z
        + ((1 - χ u) • fderiv ℝ g u + (0 - fderiv ℝ χ u).smulRight (g u))
      = (1 - χ u) • fderiv ℝ g u + (fderiv ℝ χ u).smulRight (z - g u) := by
    apply ContinuousLinearMap.ext
    intro w
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, sub_apply,
      zero_apply]
    rw [smul_sub]
    module
  rw [← hderiv]
  exact htot

/-- The Euclidean radial push is an immersion when the sheet is immersed, the cut-off does not
saturate and the push direction is transverse to the sheet. -/
theorem injective_fderiv_radialPush {n : ℕ} {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n))}
    {z : EuclideanSpace ℝ (Fin (2 * n))} {u : EuclideanSpace ℝ (Fin n)}
    (hχ : DifferentiableAt ℝ χ u) (hg : DifferentiableAt ℝ g u)
    (hg_inj : Function.Injective (fderiv ℝ g u)) (hχ1 : χ u ≠ 1)
    (htrans : g u - z ∉ Set.range (fderiv ℝ g u)) :
    Function.Injective (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => χ v • z + (1 - χ v) • g v) u) := by
  have hfd := hasFDerivAt_radialPush (z := z) hχ.hasFDerivAt hg.hasFDerivAt
  rw [hfd.fderiv]
  have hcoe : (1 - χ u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hχ1)
  have hA : Function.Injective ((1 - χ u) • fderiv ℝ g u) := by
    intro a b hab
    exact hg_inj (smul_right_injective _ hcoe hab)
  have hrange : (z - g u) ∉ Set.range ((1 - χ u) • fderiv ℝ g u) := by
    rintro ⟨a, ha⟩
    refine htrans ⟨(1 - χ u) • (-a), ?_⟩
    rw [map_smul, map_neg]
    have ha' : (1 - χ u) • (fderiv ℝ g u a) = z - g u := ha
    rw [smul_neg, ha', neg_sub]
  have hL : ⇑((1 - χ u) • fderiv ℝ g u + (fderiv ℝ χ u).smulRight (z - g u))
      = fun w => (1 - χ u) • fderiv ℝ g u w + (fderiv ℝ χ u w) • (z - g u) := by
    funext w
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hL]
  exact injective_of_add_rankOne _ hA _ hrange _

/-! ## The chart injectivity used to descend to coordinates -/

/-- The manifold derivative of a chart-like `c` is injective at every point of `c.source`. -/
theorem mfderiv_chart_injectiveM {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    {y : M} (hy : y ∈ c.source) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) c y) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) :=
    (hcinv (c y) (c.map_source hy)).mdifferentiableAt hne
  have hcd : MDifferentiableAt (𝓡 n) (𝓡 n) c y := (hcsm y hy).mdifferentiableAt hne
  have hev : (fun z : M => c.symm (c z)) =ᶠ[𝓝 y] id := by
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    exact c.left_inv hz
  have hcomp : mfderiv (𝓡 n) (𝓡 n) (fun z : M => c.symm (c z)) y
      = (mfderiv (𝓡 n) (𝓡 n) c.symm (c y)).comp (mfderiv (𝓡 n) (𝓡 n) c y) :=
    mfderiv_comp y hsymm hcd
  have hid : mfderiv (𝓡 n) (𝓡 n) (fun z : M => c.symm (c z)) y
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) y) := by
    rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id]; ext v; rfl
  have hleft : ∀ v : TangentSpace (𝓡 n) y,
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) ((mfderiv (𝓡 n) (𝓡 n) c y) v) = v := by
    intro v
    have h : (mfderiv (𝓡 n) (𝓡 n) (fun z : M => c.symm (c z)) y) v = v := by
      rw [hid]; rfl
    rwa [hcomp, ContinuousLinearMap.comp_apply] at h
  intro a b hab
  have h2 := congrArg (mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) hab
  rw [hleft a, hleft b] at h2
  exact h2

/-- **The radial push is an immersion.**  If the cut-off does not saturate at `x` and the push
direction `f x - z` is transverse to the sheet at `x`, then the derivative of the radial push at
`x` is injective. -/
theorem injective_mfderiv_pushMapM {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {χ : M → ℝ} {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    {z : EuclideanSpace ℝ (Fin (2 * n))} {x : M}
    (hχ : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f x))
    (hχ1 : χ x ≠ 1)
    (htrans : f x - z ∉ (mfderiv (𝓡 n) (𝓡 (2 * n)) f x).range) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) (pushMapM χ f z) x) := by
  classical
  set c := chartAt (EuclideanSpace ℝ (Fin n)) x with hc
  have hx : x ∈ c.source := mem_chart_source _ _
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcsm : ∀ y : M, y ∈ c.source → ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c y :=
    fun y hy => (contMDiffOn_chart (I := 𝓡 n) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := x)).contMDiffAt
      (c.open_source.mem_nhds hy)
  have hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u :=
    fun u hu => (contMDiffOn_chart_symm (I := 𝓡 n) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := x)).contMDiffAt
      (c.open_target.mem_nhds hu)
  have hcinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) (⇑c) x) :=
    mfderiv_chart_injectiveM c hcsm hcinv hx
  -- analyticity of the chart representations
  have hcs_md : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑c.symm) (c x) :=
    (hcinv (c x) (c.map_source hx)).mdifferentiableAt hne
  have hχd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => χ (c.symm u)) (c x) := by
    rw [← mdifferentiableAt_iff_differentiableAt]
    exact MDifferentiableAt.comp_of_eq (c x) (hχ.mdifferentiableAt hne) hcs_md (c.left_inv hx)
  have hfd : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c x) := by
    rw [← mdifferentiableAt_iff_differentiableAt]
    exact MDifferentiableAt.comp_of_eq (c x) (hf.mdifferentiableAt hne) hcs_md (c.left_inv hx)
  -- the chart decomposition of `mfderiv f x`
  have hdecay := Work.Projection.mfderiv_chartAt_decomp f hf x x hx
  have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) (⇑c) x) := by
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 n) (c x)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
    let L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) (c x) :=
      mfderiv (𝓡 n) (𝓡 n) (⇑c) x
    have hker : LinearMap.ker L = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      exact hcinj
    have hfr := LinearMap.finrank_range_add_finrank_ker L
    rw [hker, finrank_bot, add_zero] at hfr
    have htop : L.range = ⊤ := Submodule.eq_top_of_finrank_eq hfr
    exact LinearMap.range_eq_top.mp htop
  have hrange : (mfderiv (𝓡 n) (𝓡 (2 * n)) f x).range
      = (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c x)).range := by
    ext v
    constructor
    · rintro ⟨a, ha⟩
      rw [hdecay] at ha
      exact ⟨mfderiv (𝓡 n) (𝓡 n) (⇑c) x a, ha⟩
    · rintro ⟨a, ha⟩
      obtain ⟨b, rfl⟩ := hsurj a
      exact ⟨b, by rw [hdecay]; exact ha⟩
  have htr : f (c.symm (c x)) - z
      ∉ (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c x)).range := by
    rw [c.left_inv hx, ← hrange]
    exact htrans
  have hfinj : Function.Injective
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c x)) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    have h1 : mfderiv (𝓡 n) (𝓡 (2 * n)) f x a' = mfderiv (𝓡 n) (𝓡 (2 * n)) f x b' := by
      rw [hdecay]
      exact hab
    exact congrArg (mfderiv (𝓡 n) (𝓡 n) (⇑c) x) (himm h1)
  have hχ1' : χ (c.symm (c x)) ≠ 1 := by
    rw [c.left_inv hx]; exact hχ1
  have hA : Function.Injective
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) =>
        (χ (c.symm u)) • z + (1 - χ (c.symm u)) • (f (c.symm u))) (c x)) :=
    injective_fderiv_radialPush hχd hfd hfinj hχ1' htr
  -- assembly
  have hrep : (fun u : EuclideanSpace ℝ (Fin n) => (pushMapM χ f z) (c.symm u))
      = fun u : EuclideanSpace ℝ (Fin n) =>
          (χ (c.symm u)) • z + (1 - χ (c.symm u)) • (f (c.symm u)) := by
    funext u; rfl
  have hdec := Work.Projection.mfderiv_chartAt_decomp (pushMapM χ f z)
    (contMDiff_pushMapM hχ hf) x x hx
  rw [hdec, hrep]
  exact hA.comp hcinj

/-- **The radial push data produce the collar data.**  This is the analytic part of the Whitney
push: once the cut-off `χ` and its support `W₀` are produced (with the placement property and the
two transversality side conditions), the radial push
`x ↦ χ x • z + (1 - χ x) • f x` is a smooth immersion (with the chart decomposition above), it is
injective on `W₀`, it agrees with `f` outside `W₀`, and the placement property is inherited. -/
theorem collarData_of_radialPushData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (W : Set M) (p₁ p₂ q₁ q₂ : M) (z : EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ x, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x))
    (hdata : HasRadialPushData f W p₁ p₂ q₁ q₂ z) :
    HasManifoldCollarData f W p₁ p₂ q₁ q₂ := by
  obtain ⟨W₀, χ, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, hχc, hχ0, hχ1, hχzero, hχzero_nhds,
    hχp₂, hχq₂, htrans, hπ, hplace, hne₁, hne₂⟩ := hdata
  refine ⟨W₀, pushMapM χ f z, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁,
    contMDiff_pushMapM hχc hf, ?_, ?_, ?_, hplace, hne₁, hne₂⟩
  · -- the push is an immersion
    intro y
    by_cases hy : y ∈ W₀
    · exact injective_mfderiv_pushMapM hχc hf (himm y) (ne_of_lt (hχ1 y)) (htrans y hy)
    · -- outside `W₀` the cut-off vanishes in a neighbourhood, so the push agrees with `f`
      have hev : pushMapM χ f z =ᶠ[𝓝 y] f := by
        filter_upwards [hχzero_nhds y hy] with w hw
        show χ w • z + (1 - χ w) • f w = f w
        rw [hw]
        simp
      rw [hev.mfderiv_eq]
      exact himm y
  · -- injectivity on `W₀`
    exact injOn_pushMapM (fun x _ => hχ0 x) (fun x _ => hχ1 x) hπ
  · -- agreement outside `W₀`
    intro y hy
    show χ y • z + (1 - χ y) • f y = f y
    rw [hχzero y hy]
    simp

/-- **Assembly of the Whitney push.**  The collar data (the "placement" form of the push, which
is what the geometric construction produces) implies the conclusion of
`Work.Whitney.exists_manifold_push`: the pushed image of the collar is disjoint from the image of
the complement.

The proof is set-theoretic: if `i x = f y` with `x ∈ W₀` and `y ∉ W₀`, then the placement
property puts `i x` in `f '' W₀`, say `i x = f x'` with `x' ∈ W₀`; then `f x' = f y` with
`x' ∈ W₀ ⊆ W`, `y ∉ W₀` is a double point of `f` inside `W`, so by `hclean` it is one of the four
listable pairs: the only possibilities with `x' ∈ W₀` and `p₁, q₁ ∉ W₀` are `(p₂,p₁)` and
`(q₂,q₁)`, and both are excluded by the two non-attainment conditions. -/
theorem push_of_collar_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hdata : HasManifoldCollarData f W p₁ p₂ q₁ q₂) :
    ∃ (W₀ : Set M) (i : M → EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen W₀ ∧ W₀ ⊆ W ∧ p₂ ∈ W₀ ∧ q₂ ∈ W₀ ∧ p₁ ∉ W₀ ∧ q₁ ∉ W₀ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) i ∧
      (∀ y, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) i y)) ∧
      Set.InjOn i W₀ ∧
      (∀ y : M, y ∉ W₀ → i y = f y) ∧
      (i '' W₀) ∩ (f '' W₀ᶜ) = ∅ := by
  obtain ⟨W₀, i, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, hi_c, hi_imm, hi_inj, hi_eq, hplace,
    hne₁, hne₂⟩ := hdata
  refine ⟨W₀, i, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, hi_c, hi_imm, hi_inj, hi_eq, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨x, hx, hix⟩, ⟨y, hy, hfy⟩⟩
  have hiy : i x = f y := hix.trans hfy.symm
  have hmem : i x ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := hplace ⟨x, hx, rfl⟩
  rcases hmem with ⟨x', hx', hx'eq⟩ | hnotmem
  · have hx'y : f x' = f y := hx'eq.trans hiy
    by_cases hyW : y ∈ W
    · rcases hclean x' y (hW₀W hx') hyW hx'y with h | h | h | h | h
      · exact hy (h ▸ hx')
      · exact hp₁ (h.1 ▸ hx')
      · exact hne₁ ⟨x, hx, hx'eq.symm.trans (by rw [h.1])⟩
      · exact hq₁ (h.1 ▸ hx')
      · exact hne₂ ⟨x, hx, hx'eq.symm.trans (by rw [h.1])⟩
    · exact hsep x' y (hW₀W hx') hyW hx'y
  · exact hnotmem ⟨y, Set.mem_univ y, hiy.symm⟩





/-- **The ambient (diffeomorphism) data of the Whitney push.**  Instead of a radial cut-off, the
push is produced by an ambient diffeomorphism `ψ` of the target (with inverse `σ`) which is the
identity near the image of the frontier of an open `W₀ ⊆ W`, and which moves the image `f '' W₀`
so that it meets `f '' W₀` only inside itself (*placement*) and misses the two double point
values.  This is the "cut and paste" form of the Whitney move: the modified map is `ψ ∘ f` on
`W₀` and `f` outside. -/
def HasAmbientPushData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) : Prop :=
  ∃ (W₀ : Set M) (O : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
    IsOpen W₀ ∧ W₀ ⊆ W ∧ p₂ ∈ W₀ ∧ q₂ ∈ W₀ ∧ p₁ ∉ W₀ ∧ q₁ ∉ W₀ ∧
    IsOpen O ∧ f '' frontier W₀ ⊆ O ∧ (∀ y, y ∈ O → ψ y = y) ∧
    (∀ y, σ (ψ y) = y) ∧ (∀ y, ψ (σ y) = y) ∧
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
    ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ ∧
    f p₂ ∉ ψ '' (f '' W₀) ∧ f q₂ ∉ ψ '' (f '' W₀)

/-- The derivative of a smooth self-map of `ℝ^N` having a smooth inverse is injective. -/
theorem injective_fderiv_of_rightInverse {N : ℕ}
    {ψ σ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hleft : ∀ y, σ (ψ y) = y) (x : EuclideanSpace ℝ (Fin N)) :
    Function.Injective (fderiv ℝ ψ x) := by
  have hσd : DifferentiableAt ℝ σ (ψ x) := hσ.differentiable (by simp) (ψ x)
  have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by simp) x
  have hcomp : fderiv ℝ (fun y => σ (ψ y)) x
      = (fderiv ℝ σ (ψ x)).comp (fderiv ℝ ψ x) :=
    fderiv_comp x hσd hψd
  have hid : fderiv ℝ (fun y => σ (ψ y)) x
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N)) := by
    rw [show (fun y => σ (ψ y)) = id from funext hleft, fderiv_id]
  have hchain : (fderiv ℝ σ (ψ x)).comp (fderiv ℝ ψ x)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin N)) := hcomp.symm.trans hid
  have hleft' : ∀ v : EuclideanSpace ℝ (Fin N),
      (fderiv ℝ σ (ψ x)) ((fderiv ℝ ψ x) v) = v := by
    intro v
    have h := congrArg
      (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) => L v) hchain
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  intro a b hab
  have h2 := congrArg (fderiv ℝ σ (ψ x)) hab
  rwa [hleft' a, hleft' b] at h2

end Work.Whitney
