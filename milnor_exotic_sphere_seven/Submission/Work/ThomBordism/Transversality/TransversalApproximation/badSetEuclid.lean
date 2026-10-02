import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Rectangular

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The *Euclidean* bad-set lemma (first half of item 3 of the plan)

For a `C^∞` map `G : ℝ^a → ℝ^b`, a nonnegative `C^∞` function `χ` and the perturbation
`G - χ • t`, the set of parameters `t` for which there is a witness `z` with `χ z > 0`,
`G z = χ z • t` and a *critical* point of `z ↦ G z - χ z • t` is Lebesgue-null.

This is `Sard.sardParametric` *without* its extra hypothesis "`G` is a submersion on its zero set":
here the witnesses are restricted by `0 < χ z`, so the branch `χ z = 0` never occurs and its
analysis (which is what needed the extra hypothesis) is not needed at all.  This is the exact
Euclidean core of `TransversalApproximation.volume_badSet_eq_zero`.
-/

open scoped ContDiff MeasureTheory Topology
open MeasureTheory Set Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

open Work.ThomBordism.Transversality (CInf CInfOn IsCriticalPoint SardEuclidOn)
open Work.ThomBordism.Transversality.Sard (sardEuclidOn_of_steps sardSteps)

private lemma fderiv_sub_smul_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (χ : E → ℝ) (t : F) {x : E}
    (hG : DifferentiableAt ℝ G x) (hχ : DifferentiableAt ℝ χ x) :
    fderiv ℝ (fun y => G y - χ y • t) x = fderiv ℝ G x - (fderiv ℝ χ x).smulRight t :=
  (hG.hasFDerivAt.sub (hχ.hasFDerivAt.smul_const t)).fderiv

private lemma surjective_smul_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ} (hc : c ≠ 0) (L : E →L[ℝ] F) :
    Function.Surjective (c • L) ↔ Function.Surjective L := by
  constructor
  · intro h y
    obtain ⟨v, hv⟩ := h (c • y)
    refine ⟨v, ?_⟩
    have h1 : c • L v = c • y := by simpa [smul_apply] using hv
    have h2 : c⁻¹ • (c • L v) = c⁻¹ • (c • y) := by rw [h1]
    simpa [smul_smul, inv_mul_cancel₀ hc] using h2
  · intro h y
    obtain ⟨v, hv⟩ := h (c⁻¹ • y)
    refine ⟨v, ?_⟩
    rw [smul_apply, hv, smul_smul, mul_inv_cancel₀ hc, one_smul]

private lemma fderiv_perturb_eq_smul_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (χ : E → ℝ) (u : E → F) {t : F} {x : E}
    (heq : G =ᶠ[𝓝 x] fun y => χ y • u y) (hux : u x = t)
    (hG : DifferentiableAt ℝ G x) (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => G y - χ y • t) x = χ x • fderiv ℝ u x := by
  have h1 : fderiv ℝ G x = χ x • fderiv ℝ u x + (fderiv ℝ χ x).smulRight t := by
    have h2 : fderiv ℝ (fun y => χ y • u y) x
        = χ x • fderiv ℝ u x + (fderiv ℝ χ x).smulRight (u x) :=
      (hχ.hasFDerivAt.smul hu.hasFDerivAt).fderiv
    rw [heq.fderiv_eq, h2, hux]
  rw [fderiv_sub_smul_const G χ t hG hχ, h1]
  abel

/-- **The Euclidean bad-set lemma.**  For `C^∞` maps `G : ℝ^a → ℝ^b` and nonnegative `C^∞` `χ`, the
set of `t` for which some `z` with `χ z > 0` satisfies `G z = χ z • t` and is a critical point of
`z ↦ G z - χ z • t` is null. -/
theorem volume_badSet_eq_zero_euclid {a b : ℕ}
    (G : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b))
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (χ : EuclideanSpace ℝ (Fin a) → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ z, 0 ≤ χ z) :
    volume {t : EuclideanSpace ℝ (Fin b) |
      ∃ z, 0 < χ z ∧ G z = χ z • t ∧
        ¬ Function.Surjective (fderiv ℝ (fun y => G y - χ y • t) z)} = 0 := by
  let U : Set (EuclideanSpace ℝ (Fin a)) := {z | 0 < χ z}
  have hUopen : IsOpen U := isOpen_lt continuous_const hχ.continuous
  let u : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b) := fun z => (χ z)⁻¹ • G z
  have hχdiff : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hGdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hu : CInfOn u U := by
    have h1 : ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹) U :=
      hχ.contDiffOn.inv (fun z hz => ne_of_gt (show 0 < χ z from hz))
    have h2 : ContDiffOn ℝ smoothHeight ((fun z => (χ z)⁻¹) • G) U := h1.smul hG.contDiffOn
    change ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹ • G z) U at h2
    change ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹ • G z) U
    exact h2
  have hsard : volume (u '' ({z | IsCriticalPoint u z} ∩ U)) = 0 :=
    (sardEuclidOn_of_steps sardSteps (a + b) a b rfl) u U hUopen hu
  refine measure_mono_null ?_ hsard
  rintro t ⟨z, hzpos, hzG, hzcrit⟩
  have hzU : z ∈ U := hzpos
  have huz : u z = t := by
    show (χ z)⁻¹ • G z = t
    rw [hzG, smul_smul, inv_mul_cancel₀ (ne_of_gt hzpos), one_smul]
  refine ⟨z, ⟨?_, hzU⟩, huz⟩
  intro hsu
  have heq : G =ᶠ[𝓝 z] fun y => χ y • u y := by
    filter_upwards [hUopen.mem_nhds hzpos] with y hy
    have hy' : 0 < χ y := hy
    show G y = χ y • u y
    show G y = χ y • ((χ y)⁻¹ • G y)
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hy'), one_smul]
  have hudiff : DifferentiableAt ℝ u z := by
    have heq2 : u =ᶠ[𝓝 z] (fun y => (χ y)⁻¹) • G := by
      filter_upwards with y
      show (χ y)⁻¹ • G y = (χ y)⁻¹ • G y
      rfl
    rw [heq2.differentiableAt_iff]
    exact (hχdiff.differentiableAt.inv (ne_of_gt hzpos)).smul hGdiff.differentiableAt
  have hderiv : fderiv ℝ (fun y => G y - χ y • t) z = χ z • fderiv ℝ u z :=
    fderiv_perturb_eq_smul_fderiv G χ u heq huz hGdiff.differentiableAt
      hχdiff.differentiableAt hudiff
  refine hzcrit ?_
  have h2 : Function.Surjective (χ z • fderiv ℝ u z) :=
    (surjective_smul_iff (ne_of_gt hzpos) (fderiv ℝ u z)).mpr hsu
  rwa [← hderiv] at h2

/-- **The localized Euclidean bad-set lemma.**  Same conclusion as
`volume_badSet_eq_zero_euclid`, but `G` and `χ` only need to be `C^∞` on an open set `V`, and the
witnesses are required to lie in `V`.  This is the form in which the per-chart step of the manifold
transport consumes the result (a chart expression is smooth on the chart's target, an open subset of
the model space). -/
theorem volume_badSet_eq_zero_euclid_of_isOpen {a b : ℕ}
    (G : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b))
    (χ : EuclideanSpace ℝ (Fin a) → ℝ)
    (V : Set (EuclideanSpace ℝ (Fin a))) (hV : IsOpen V)
    (hG : CInfOn G V) (hχ : CInfOn χ V) (hχ0 : ∀ z, 0 ≤ χ z) :
    volume {t : EuclideanSpace ℝ (Fin b) |
      ∃ z ∈ V, 0 < χ z ∧ G z = χ z • t ∧
        ¬ Function.Surjective (fderiv ℝ (fun y => G y - χ y • t) z)} = 0 := by
  let U : Set (EuclideanSpace ℝ (Fin a)) := {z | 0 < χ z}
  have hVUopen : IsOpen (V ∩ U) := by
    have h1 : IsOpen ({z : ℝ | (0:ℝ) < z}) :=
      isOpen_lt (f := fun _ : ℝ => (0:ℝ)) (g := id) continuous_const continuous_id
    have h2 := hχ.continuousOn.isOpen_inter_preimage hV h1
    simpa [U] using h2
  let u : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b) := fun z => (χ z)⁻¹ • G z
  have hu : CInfOn u (V ∩ U) := by
    have h1 : ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹) (V ∩ U) :=
      (hχ.mono Set.inter_subset_left).inv
        (fun z hz => ne_of_gt (show 0 < χ z from hz.2))
    have h2 : ContDiffOn ℝ smoothHeight ((fun z => (χ z)⁻¹) • G) (V ∩ U) :=
      h1.smul (hG.mono Set.inter_subset_left)
    change ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹ • G z) (V ∩ U) at h2
    change ContDiffOn ℝ smoothHeight (fun z => (χ z)⁻¹ • G z) (V ∩ U)
    exact h2
  have hsard : volume (u '' ({z | IsCriticalPoint u z} ∩ (V ∩ U))) = 0 :=
    (sardEuclidOn_of_steps sardSteps (a + b) a b rfl) u (V ∩ U) hVUopen hu
  refine measure_mono_null ?_ hsard
  rintro t ⟨z, hzV, hzpos, hzG, hzcrit⟩
  have hzU : z ∈ V ∩ U := ⟨hzV, hzpos⟩
  have huz : u z = t := by
    show (χ z)⁻¹ • G z = t
    rw [hzG, smul_smul, inv_mul_cancel₀ (ne_of_gt hzpos), one_smul]
  refine ⟨z, ⟨?_, hzU⟩, huz⟩
  intro hsu
  have heq : G =ᶠ[𝓝 z] fun y => χ y • u y := by
    filter_upwards [hVUopen.mem_nhds ⟨hzV, hzpos⟩] with y hy
    have hy' : 0 < χ y := hy.2
    show G y = χ y • u y
    show G y = χ y • ((χ y)⁻¹ • G y)
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hy'), one_smul]
  have hudiff : DifferentiableAt ℝ u z := by
    have heq2 : u =ᶠ[𝓝 z] (fun y => (χ y)⁻¹) • G := by
      filter_upwards with y
      show (χ y)⁻¹ • G y = (χ y)⁻¹ • G y
      rfl
    rw [heq2.differentiableAt_iff]
    exact ((hχ.differentiableOn (by norm_num) z hzV).differentiableAt
      (hV.mem_nhds hzV)).inv (ne_of_gt hzpos) |>.smul
      ((hG.differentiableOn (by norm_num) z hzV).differentiableAt (hV.mem_nhds hzV))
  have hderiv : fderiv ℝ (fun y => G y - χ y • t) z = χ z • fderiv ℝ u z :=
    fderiv_perturb_eq_smul_fderiv G χ u heq huz
      ((hG.differentiableOn (by norm_num) z hzV).differentiableAt (hV.mem_nhds hzV))
      ((hχ.differentiableOn (by norm_num) z hzV).differentiableAt (hV.mem_nhds hzV)) hudiff
  refine hzcrit ?_
  have h2 : Function.Surjective (χ z • fderiv ℝ u z) :=
    (surjective_smul_iff (ne_of_gt hzpos) (fderiv ℝ u z)).mpr hsu
  rwa [← hderiv] at h2

end Work.ThomBordism.Transversality.TransversalApproximation
