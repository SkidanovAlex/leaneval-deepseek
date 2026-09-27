import Mathlib
import Submission.Work.Drive.classTripleSystem
import Submission.Work.Drive.qform_kernel
import Submission.Work.Drive.qform_bilinear

namespace Work.Drive

open scoped ContDiff Topology

/- Helpers for `Work.Drive.classSystem_hsurj`: the class map of a triple of vectors (a composition
of `qform` and `pair33`) has surjective derivative wherever the first vector does not vanish.

The mathematics is short.  The *horizontal* parameter map of the class system is the composite
`csMap ∘ G`, where `G p' k = A p' k (V k (parOf y k))` is the map whose derivative `hjoint` makes
surjective, and `csMap x = pair33 (qform x₀ x₁) (qform x₀ x₂)` is the "class map" of a triple.  So
it suffices that `fderiv csMap x` is surjective whenever `x 0 ≠ 0`: the derivative of `csMap` is
`δ ↦ pair33 (qform x₀ (δ 1) + qform (δ 0) x₁) (qform x₀ (δ 2) + qform (δ 0) x₂)`, and on the
subspace `δ 0 = 0` this is `δ ↦ pair33 (qform x₀ δ₁) (qform x₀ δ₂)`, which is onto because
`w ↦ qform x₀ w` is onto for `x₀ ≠ 0` (its kernel is the line `ℝ x₀`). -/
namespace ClassSystemHsurj

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ## 1. `pair33` is (jointly) linear -/

lemma pair33_add (a a' b b' : E3) : pair33 (a + a') (b + b') = pair33 a b + pair33 a' b' := by
  ext i
  by_cases hi : i.val < 3
  · rw [pair33_apply_lt _ _ hi]
    simp only [WithLp.ofLp_add, Pi.add_apply, pair33_apply_lt _ _ hi]
  · rw [pair33_apply_ge _ _ hi]
    simp only [WithLp.ofLp_add, Pi.add_apply, pair33_apply_ge _ _ hi]

lemma pair33_smul (c : ℝ) (a b : E3) : pair33 (c • a) (c • b) = c • pair33 a b := by
  ext i
  by_cases hi : i.val < 3
  · rw [pair33_apply_lt _ _ hi]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, pair33_apply_lt _ _ hi]
  · rw [pair33_apply_ge _ _ hi]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, pair33_apply_ge _ _ hi]

/-- `pair33` as a linear map. -/
def pair33Lin : E3 × E3 →ₗ[ℝ] Tgt 6 where
  toFun p := pair33 p.1 p.2
  map_add' p q := pair33_add p.1 q.1 p.2 q.2
  map_smul' c p := pair33_smul c p.1 p.2

@[simp] lemma pair33Lin_apply (p : E3 × E3) : pair33Lin p = pair33 p.1 p.2 := rfl

/-- `pair33` as a continuous linear map. -/
noncomputable def pair33CLM : E3 × E3 →L[ℝ] Tgt 6 :=
  pair33Lin.mkContinuousOfExistsBound
    ((SemilinearMapClass.bound_of_continuous pair33Lin
      (LinearMap.continuous_of_finiteDimensional pair33Lin)).imp fun _ h => h.2)

@[simp] lemma pair33CLM_apply (p : E3 × E3) : pair33CLM p = pair33 p.1 p.2 := by
  simp [pair33CLM, pair33Lin]

/-- **`pair33` is onto**: every vector of `ℝ⁶` is a stacked pair. -/
lemma pair33_surjective : Function.Surjective (fun p : E3 × E3 => pair33 p.1 p.2) := by
  intro z
  refine ⟨(WithLp.toLp 2 (fun i : Fin 3 => z (Fin.castAdd 3 i)),
           WithLp.toLp 2 (fun i : Fin 3 => z ⟨i.val + 3, by omega⟩)), ?_⟩
  ext j
  by_cases hj : j.val < 3
  · rw [pair33_apply_lt _ _ hj, WithLp.ofLp_toLp]
    have h : Fin.castAdd 3 (⟨j.val, hj⟩ : Fin 3) = j := Fin.ext rfl
    rw [h]
  · rw [pair33_apply_ge _ _ hj, WithLp.ofLp_toLp]
    have h : (⟨(⟨j.val - 3, by omega⟩ : Fin 3).val + 3, by omega⟩ : Fin 6) = j :=
      Fin.ext (by show (↑j - 3) + 3 = (↑j : ℕ); omega)
    rw [h]

/-! ## 2. `qform` as a continuous linear map -/

noncomputable def qformCLM1 (v : Eucl 3) : Eucl 3 →L[ℝ] E3 :=
  (qformRight v).mkContinuousOfExistsBound
    ((SemilinearMapClass.bound_of_continuous (qformRight v)
      (LinearMap.continuous_of_finiteDimensional (qformRight v))).imp fun _ h => h.2)

@[simp] lemma qformCLM1_apply (v w : Eucl 3) : qformCLM1 v w = qform v w := by
  simp [qformCLM1, qformRight]

/-- `qform` as a continuous bilinear map (curried). -/
noncomputable def qformCLM : Eucl 3 →L[ℝ] Eucl 3 →L[ℝ] E3 :=
  let φ : Eucl 3 →ₗ[ℝ] (Eucl 3 →L[ℝ] E3) :=
    { toFun := qformCLM1
      map_add' := fun u u' => by
        ext w
        simp only [add_apply, qformCLM1_apply, qform_add_left]
      map_smul' := fun c u => by
        ext w
        simp only [smul_apply, qformCLM1_apply, qform_smul_left,
          RingHom.id_apply] }
  φ.mkContinuousOfExistsBound
    ((SemilinearMapClass.bound_of_continuous φ
      (LinearMap.continuous_of_finiteDimensional φ)).imp fun _ h => h.2)

@[simp] lemma qformCLM_apply (u v : Eucl 3) : qformCLM u v = qform u v := by
  simp [qformCLM, qformCLM1_apply]

lemma qform_zero_left (w : Eucl 3) : qform (0 : Eucl 3) w = 0 := by
  simpa using qform_smul_left (0 : ℝ) (0 : Eucl 3) w

/-- **`w ↦ qform v w` is onto for `v ≠ 0`**: its kernel is the line `ℝ v`, so its rank is
`dim ℝ³ = 3`. -/
lemma qformRight_surjective (v : Eucl 3) (hv : v ≠ 0) : Function.Surjective (qformRight v) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  have h := LinearMap.finrank_range_add_finrank_ker (qformRight v)
  rw [qformRight_ker v hv, finrank_span_singleton hv] at h
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp [Eucl]
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [h4] at h
  omega

/-! ## 3. The class map and its derivative -/

/-- The "class map" of a triple of vectors of `ℝ⁴ = ℍ`: the pair of the imaginary parts of
`x₀ · conj x₁` and `x₀ · conj x₂`, stacked.  Zeros of the class system are of this shape. -/
def csMap (x : Fin 3 → Eucl 3) : Tgt 6 :=
  pair33 (qform (x 0) (x 1)) (qform (x 0) (x 2))

lemma hasFDerivAt_pair33CLM (p : E3 × E3) :
    HasFDerivAt (fun q : E3 × E3 => pair33 q.1 q.2) pair33CLM p :=
  ContinuousLinearMap.hasFDerivAt (f := pair33CLM) (x := p)

/-- The derivative at `x` of `y ↦ qform (y i) (y j)`. -/
noncomputable def qformCompDeriv (x : Fin 3 → Eucl 3) (i j : Fin 3) :
    (Fin 3 → Eucl 3) →L[ℝ] E3 :=
  ((qformCLM.isBoundedBilinearMap).deriv (x i, x j)).comp
    ((ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j))

lemma hasFDerivAt_qformComp (x : Fin 3 → Eucl 3) (i j : Fin 3) :
    HasFDerivAt (fun y : Fin 3 → Eucl 3 => qform (y i) (y j)) (qformCompDeriv x i j) x :=
  ((qformCLM.isBoundedBilinearMap).hasFDerivAt (x i, x j)).comp x
    (f := fun y : Fin 3 → Eucl 3 => (y i, y j))
    (g := fun p : Eucl 3 × Eucl 3 => qformCLM p.1 p.2)
    ((hasFDerivAt_apply i x).prodMk (hasFDerivAt_apply j x))

/-- The derivative of the class map at `x`. -/
noncomputable def csMapDeriv (x : Fin 3 → Eucl 3) : (Fin 3 → Eucl 3) →L[ℝ] Tgt 6 :=
  pair33CLM.comp ((qformCompDeriv x 0 1).prod (qformCompDeriv x 0 2))

lemma hasFDerivAt_csMap (x : Fin 3 → Eucl 3) : HasFDerivAt csMap (csMapDeriv x) x :=
  (hasFDerivAt_pair33CLM (qform (x 0) (x 1), qform (x 0) (x 2))).comp x
    (f := fun y : Fin 3 → Eucl 3 => (qform (y 0) (y 1), qform (y 0) (y 2)))
    (g := fun q : E3 × E3 => pair33 q.1 q.2)
    ((hasFDerivAt_qformComp x 0 1).prodMk (hasFDerivAt_qformComp x 0 2))

/-- **The derivative of the class map in explicit form.** -/
lemma fderiv_csMap_apply (x δ : Fin 3 → Eucl 3) :
    fderiv ℝ csMap x δ =
      pair33 (qform (x 0) (δ 1) + qform (δ 0) (x 1))
        (qform (x 0) (δ 2) + qform (δ 0) (x 2)) := by
  rw [(hasFDerivAt_csMap x).fderiv]
  simp only [csMapDeriv, qformCompDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, IsBoundedBilinearMap.deriv_apply,
    ContinuousLinearMap.proj_apply, qformCLM_apply, pair33CLM_apply]

/-- **The derivative of the class map is onto whenever `x 0 ≠ 0`**: take `δ 0 = 0` and solve
`qform (x 0) δ₁ = c₁`, `qform (x 0) δ₂ = c₂` in the second and third slots. -/
lemma csMap_fderiv_surjective {x : Fin 3 → Eucl 3} (hx : x 0 ≠ 0) :
    Function.Surjective (fderiv ℝ csMap x) := by
  intro z
  obtain ⟨⟨c1, c2⟩, hz⟩ := pair33_surjective z
  obtain ⟨δ1, hδ1⟩ := qformRight_surjective (x 0) hx c1
  obtain ⟨δ2, hδ2⟩ := qformRight_surjective (x 0) hx c2
  have hδ1' : qform (x 0) δ1 = c1 := by simpa using hδ1
  have hδ2' : qform (x 0) δ2 = c2 := by simpa using hδ2
  refine ⟨![0, δ1, δ2], ?_⟩
  rw [fderiv_csMap_apply, ← hz]
  simp [qform_zero_left, hδ1', hδ2']

end

end ClassSystemHsurj

theorem classSystem_hsurj {m : ℕ} (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.Eucl 3)
    (A : EuclideanSpace ℝ (Fin m) → Fin 3 → Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3)
    (hA : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin m) × Work.Drive.Eucl 3 => A z.1 k z.2))
    (hjoint : ∀ (p : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Tgt 6),
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        fun k : Fin 3 => A p' k (V k (Work.Drive.parOf y k))) p))
    (p : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Tgt 6)
    (hVne : ∀ k, V k (Work.Drive.parOf y k) ≠ 0)
    (hAinj : ∀ k, Function.Injective (A p k))
    (hzero : Work.Drive.classSystem V A p y = 0) :
    Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
      Work.Drive.classSystem V A p' y) p) := by
  set G : EuclideanSpace ℝ (Fin m) → (Fin 3 → Eucl 3) :=
    fun p' k => A p' k (V k (parOf y k)) with hG
  have hGsurj : Function.Surjective (fderiv ℝ G p) := hjoint p y
  have hGdiff : DifferentiableAt ℝ G p := by
    rw [hG]
    rw [differentiableAt_pi]
    intro k
    have hAz : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin m) × Eucl 3 => A z.1 k z.2) (p, V k (parOf y k)) :=
      ((hA k).differentiable (by simp)).differentiableAt
    have hpair : DifferentiableAt ℝ
        (fun p' : EuclideanSpace ℝ (Fin m) => (p', V k (parOf y k))) p :=
      differentiableAt_id.prodMk (differentiableAt_const (V k (parOf y k)))
    exact hAz.comp p hpair
  have hx0 : G p 0 ≠ 0 := by
    intro h
    exact hVne 0 (hAinj 0 (by simpa using h))
  -- The zero condition says that the three perturbed classes coincide at `y`.  It is *not* needed
  -- for the surjectivity below: that only uses `G p 0 ≠ 0`, i.e. that the first perturbed class
  -- does not vanish.  We record the consequence for the record.
  have hprop : (∃ a : ℝ, a • A p 0 (V 0 (parOf y 0)) = A p 1 (V 1 (parOf y 1)))
      ∧ (∃ a : ℝ, a • A p 0 (V 0 (parOf y 0)) = A p 2 (V 2 (parOf y 2))) :=
    (classSystem_eq_zero_iff V A p y hVne hAinj).mp hzero
  have hcsDiff : DifferentiableAt ℝ ClassSystemHsurj.csMap (G p) :=
    (ClassSystemHsurj.hasFDerivAt_csMap (G p)).differentiableAt
  have hfun : (fun p' : EuclideanSpace ℝ (Fin m) => Work.Drive.classSystem V A p' y)
      = (fun p' => ClassSystemHsurj.csMap (G p')) := rfl
  rw [hfun]
  have hcomp : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        ClassSystemHsurj.csMap (G p')) p
      = (fderiv ℝ ClassSystemHsurj.csMap (G p)).comp (fderiv ℝ G p) :=
    fderiv_comp (f := G) (g := ClassSystemHsurj.csMap) p hcsDiff hGdiff
  rw [hcomp]
  intro z
  obtain ⟨a, ha⟩ := ClassSystemHsurj.csMap_fderiv_surjective (x := G p) hx0 z
  obtain ⟨b, hb⟩ := hGsurj a
  exact ⟨b, by rw [ContinuousLinearMap.comp_apply, hb, ha]⟩

end Work.Drive
