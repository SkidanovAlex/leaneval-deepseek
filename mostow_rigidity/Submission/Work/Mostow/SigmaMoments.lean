import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.invarianceMoments

set_option linter.style.haveILetI false

/-!
# Moments of the rotation-invariant probability measure `sigma n` on the unit sphere

`Submission.Mostow.sigma n` is the normalised surface measure of the unit sphere
`Submission.Mostow.Sph n ⊂ E n = EuclideanSpace ℝ (Fin n)`, pushed forward to `E n` by
`Subtype.val`.  This file collects the basic probabilistic and symmetry properties of that
measure and computes its first and second moments:

* it is a probability measure carried by the sphere and has no atoms (for `n ≥ 2`);
* it is invariant under every linear isometry equivalence of `E n`;
* its barycentre is `0` and its covariance matrix is `(1/n) • I`, i.e.
  `∫ ξ, ⟪ξ,v⟫ * ⟪ξ,w⟫ ∂σ = ⟪v,w⟫ / n`.

The invariance is proved from the definition of `Measure.toSphere` (the generalised polar
coordinate change): `μ.toSphere s = finrank ℝ E • μ (Ioo 0 1 • (↑''s))`, which exhibits
`toSphere` as the angular part of Lebesgue measure, hence invariant under the orthogonal group.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric
open scoped ENNReal Pointwise

noncomputable section

/-- The orthogonal group of `EuclideanSpace ℝ (Fin n)` acts transitively on the unit sphere:
any two unit vectors are related by a linear isometry equivalence. -/
theorem sphereTransitive {n : ℕ} {e u : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hu : ‖u‖ = 1) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), A e = u := by
  by_cases hn : n = 0
  · subst hn
    have h0 : e = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero] at he
    exact absurd he (by norm_num)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    let i₀ : Fin n := ⟨0, hpos⟩
    have hb1 : ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), b i₀ = e := by
      obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) (v := fun _ : Fin n => e) (s := {i₀})
        (finrank_euclideanSpace)
        (by refine ⟨fun i => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
            simpa using he)
      exact ⟨b, hb i₀ (Set.mem_singleton i₀)⟩
    have hb2 : ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), b i₀ = u := by
      obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
        (E := EuclideanSpace ℝ (Fin n)) (ι := Fin n) (v := fun _ : Fin n => u) (s := {i₀})
        (finrank_euclideanSpace)
        (by refine ⟨fun i => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
            simpa using hu)
      exact ⟨b, hb i₀ (Set.mem_singleton i₀)⟩
    obtain ⟨b₁, hb₁⟩ := hb1
    obtain ⟨b₂, hb₂⟩ := hb2
    refine ⟨b₁.repr.trans b₂.repr.symm, ?_⟩
    rw [← hb₁, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
      OrthonormalBasis.repr_symm_single, hb₂]

/-- The normalised surface measure of the unit sphere (`sphMeas`, i.e. `toSphere` of Lebesgue
measure pushed to `E n` by `Subtype.val`) is invariant under every linear isometry equivalence
of `E n`. -/
theorem sigmaRot {n : ℕ} (A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map Subtype.val).map A
      = ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map Subtype.val := by
  have hmem : ∀ x : EuclideanSpace ℝ (Fin n),
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↔ ‖x‖ = 1 := by
    intro x; rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have hmaps : Set.MapsTo A (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    fun x hx => (hmem (A x)).mpr (by rw [A.norm_map]; exact (hmem x).mp hx)
  have hsym : Set.MapsTo A.symm (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    fun x hx => (hmem (A.symm x)).mpr (by rw [A.symm.norm_map]; exact (hmem x).mp hx)
  let φ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := fun x => ⟨A ↑x, hmaps x.2⟩
  have hφcont : Continuous φ :=
    Continuous.subtype_mk (A.continuous.comp continuous_subtype_val) (fun x => hmaps x.2)
  have hφmeas : Measurable φ := hφcont.measurable
  have hφinv : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      φ ⟨A.symm ↑x, hsym x.2⟩ = x := by
    intro x; ext; simp [φ]
  have himg : ∀ X : Set (EuclideanSpace ℝ (Fin n)), A.symm '' X = A ⁻¹' X := by
    intro X
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨A y, hy, by simp⟩
  have hpre : ∀ X : Set (EuclideanSpace ℝ (Fin n)),
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (A ⁻¹' X) = volume X := by
    intro X
    apply le_antisymm
    · have h := Measure.le_map_apply (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        A.continuous.aemeasurable X
      rwa [(LinearIsometryEquiv.measurePreserving A).map_eq] at h
    · rw [← himg X]
      have h := Measure.le_map_apply (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        A.symm.continuous.aemeasurable (A.symm '' X)
      rw [(LinearIsometryEquiv.measurePreserving A.symm).map_eq,
          Set.preimage_image_eq X A.symm.injective] at h
      exact h
  have htoS : Measure.map φ (volume.toSphere) = volume.toSphere := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply hφmeas hs, Measure.toSphere_apply' volume (hφmeas hs),
        Measure.toSphere_apply' volume hs]
    congr 1
    have hcone : (Set.Ioo (0:ℝ) 1 • (Subtype.val '' (φ ⁻¹' s))) =
        A ⁻¹' (Set.Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨r, hr, x, ⟨a, ha, hax⟩, hxy⟩ := hy
        exact ⟨r, hr, ↑(φ a), ⟨φ a, ha, rfl⟩, by rw [← hxy, ← hax]; simp [φ]⟩
      · intro hy
        obtain ⟨r, hr, z, ⟨w, hw, hwz⟩, hzy⟩ := hy
        have ha : (⟨A.symm ↑w, hsym w.2⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∈ φ ⁻¹' s := by
          show φ ⟨A.symm ↑w, hsym w.2⟩ ∈ s
          rw [hφinv w]; exact hw
        have hgoal : r • (↑(⟨A.symm ↑w, hsym w.2⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)) = y := by
          have hA : A (r • (A.symm ↑w)) = r • ↑w := by
            rw [map_smul, LinearIsometryEquiv.apply_symm_apply]
          have h1 : A y = A (r • (A.symm ↑w)) := by rw [hA, hwz, ← hzy]
          exact (A.injective h1).symm
        exact ⟨r, hr,
          (↑(⟨A.symm ↑w, hsym w.2⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)),
          ⟨⟨A.symm ↑w, hsym w.2⟩, ha, rfl⟩, hgoal⟩
    rw [hcone]
    exact hpre _
  rw [Measure.map_map A.continuous.measurable measurable_subtype_coe]
  have hcomp : A ∘ (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      EuclideanSpace ℝ (Fin n)) = Subtype.val ∘ φ := rfl
  rw [hcomp, ← Measure.map_map measurable_subtype_coe hφmeas, htoS]

theorem SigmaMoments (n : ℕ) (hn : 2 ≤ n) :
    MeasureTheory.IsProbabilityMeasure (Submission.Mostow.sigma n) ∧
    Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0 ∧
    (∀ ξ : Submission.Mostow.E n, Submission.Mostow.sigma n {ξ} = 0) ∧
    (∫ ξ, ξ ∂(Submission.Mostow.sigma n)) = 0 ∧
    (∀ v w : Submission.Mostow.E n,
      ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ w) ∂(Submission.Mostow.sigma n)
        = (inner ℝ v w) / n) := by
  set m : Measure (EuclideanSpace ℝ (Fin n)) :=
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map Subtype.val with hm_def
  set c : ℝ≥0∞ := (m Set.univ)⁻¹ with hc_def
  have hm_univ_ne : m Set.univ ≠ 0 := by
    rw [hm_def, Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ ?_
    · simp [finrank_euclideanSpace]; omega
    · exact ne_of_gt
        (Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
          (0 : EuclideanSpace ℝ (Fin n)) (by norm_num))
  haveI hne : NeZero m := ⟨fun h => hm_univ_ne (by rw [h]; simp)⟩
  have hprob : MeasureTheory.IsProbabilityMeasure (Submission.Mostow.sigma n) := by
    unfold Submission.Mostow.sigma
    exact isProbabilityMeasureSMul
  have hsupp : Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0 := by
    show (c • m) (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0
    rw [Measure.smul_apply]
    have h0 : m (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0 := by
      rw [hm_def, Measure.map_apply measurable_subtype_coe (isClosed_sphere.measurableSet).compl]
      have h : Subtype.val ⁻¹' (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ =
          (∅ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
        ext x; simp
      rw [h]; simp
    rw [h0]; simp
  have hatom : ∀ ξ : Submission.Mostow.E n, Submission.Mostow.sigma n {ξ} = 0 := by
    intro ξ
    show (c • m) {ξ} = 0
    rw [Measure.smul_apply]
    have h0 : m {ξ} = 0 := by
      rw [hm_def, Measure.map_apply measurable_subtype_coe (measurableSet_singleton ξ)]
      by_cases hξ : ξ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      · have h : Subtype.val ⁻¹' {ξ} = {⟨ξ, hξ⟩} := by
          ext x
          exact ⟨fun hx => Subtype.ext (by simpa using hx),
                 fun hx => by simpa using congrArg Subtype.val hx⟩
        rw [h, Measure.toSphere_apply' volume (MeasurableSet.singleton _)]
        have himg : Subtype.val '' ({⟨ξ, hξ⟩} :
            Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) = {ξ} := by
          ext y
          constructor
          · rintro ⟨x, hx, rfl⟩
            simp only [Set.mem_singleton_iff] at hx ⊢
            rw [hx]
          · intro hy
            rw [Set.mem_singleton_iff] at hy
            exact ⟨⟨ξ, hξ⟩, rfl, hy.symm⟩
        rw [himg]
        have hξ0 : ξ ≠ 0 := by
          intro h0; rw [mem_sphere] at hξ; rw [h0, dist_self] at hξ; norm_num at hξ
        have hne' : Submodule.span ℝ {ξ} ≠ ⊤ := by
          intro htop
          have h1 : Module.finrank ℝ (Submodule.span ℝ {ξ}) = 1 :=
            finrank_span_singleton hξ0
          have h2 : Module.finrank ℝ (Submodule.span ℝ {ξ}) =
              Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
            rw [htop, finrank_top]
          have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
            rw [finrank_euclideanSpace, Fintype.card_fin]
          omega
        have hsub : (Set.Ioo (0:ℝ) 1 • ({ξ} : Set (EuclideanSpace ℝ (Fin n)))) ⊆
            (Submodule.span ℝ {ξ} : Set (EuclideanSpace ℝ (Fin n))) := by
          rintro y ⟨r, hr, b, hb, hby⟩
          rw [Set.mem_singleton_iff] at hb
          rw [← hby, hb]
          exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton ξ))
        have hzero : volume (Set.Ioo (0:ℝ) 1 •
            ({ξ} : Set (EuclideanSpace ℝ (Fin n)))) = 0 :=
          measure_mono_null hsub
            (Measure.addHaar_submodule volume (Submodule.span ℝ {ξ}) hne')
        rw [hzero, mul_zero]
      · have h : Subtype.val ⁻¹' ({ξ} : Set (EuclideanSpace ℝ (Fin n))) =
            (∅ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hξ (hx ▸ x.2)
        rw [h]; simp
    rw [h0]; simp
  have hinv : ∀ A : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (Submission.Mostow.sigma n).map A = Submission.Mostow.sigma n := by
    intro A
    show (c • m).map A = c • m
    rw [Measure.map_smul c A.continuous.aemeasurable, sigmaRot A]
  haveI : MeasureTheory.IsProbabilityMeasure (Submission.Mostow.sigma n) := hprob
  obtain ⟨hmean, hcov⟩ := invarianceMoments (Submission.Mostow.sigma n) hsupp hinv
    (fun e u he hu => sphereTransitive he hu)
  exact ⟨hprob, hsupp, hatom, hmean, hcov⟩

end

end Work.Mostow
