import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise BigOperators

namespace Commons.Analysis.MeasureTheory

private def isometrySphere {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 where
  toFun θ := ⟨L θ.1, by simp⟩
  invFun θ := ⟨L.symm θ.1, by simp⟩
  left_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.symm_apply_apply]
  right_inv θ := by
    apply Subtype.ext
    simp [LinearIsometryEquiv.apply_symm_apply]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private lemma volume_preimage_isometry {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (L : V ≃ₗᵢ[ℝ] V) (X : Set V) :
    volume ((L : V → V) ⁻¹' X) = volume X := by
  let e : V ≃ᵐ V := L.toHomeomorph.toMeasurableEquiv
  have he : ⇑e = (L : V → V) := rfl
  have hemap : Measure.map (⇑e) volume = volume := by
    simpa [he] using (LinearIsometryEquiv.measurePreserving L).map_eq
  calc
    volume ((L : V → V) ⁻¹' X) = volume ((e : V → V) ⁻¹' X) := by rw [he]
    _ = (volume.map e) X := (MeasurableEquiv.map_apply e X).symm
    _ = volume X := by rw [hemap]

private lemma cone_preimage_isometry {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) (B : Set V) :
    Ioo (0 : ℝ) 1 • ((L : V → V) ⁻¹' B) = (L : V → V) ⁻¹' (Ioo (0 : ℝ) 1 • B) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, y, hy, hxy⟩
    rw [Set.mem_preimage]
    rw [Set.mem_preimage] at hy
    rw [Set.mem_smul]
    refine ⟨r, hr, (L : V → V) y, hy, ?_⟩
    calc
      r • ((L : V → V) y) = (L : V → V) (r • y) := by rw [map_smul]
      _ = (L : V → V) x := by rw [hxy]
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨r, hr, b, hb, hLx⟩
    rw [Set.mem_smul]
    refine ⟨r, hr, (L.symm : V → V) b, ?_, ?_⟩
    · rw [Set.mem_preimage]
      simpa using hb
    · calc
        r • ((L.symm : V → V) b) = (L.symm : V → V) (r • b) := by rw [map_smul]
        _ = (L.symm : V → V) ((L : V → V) x) := by rw [hLx]
        _ = x := by simp

private lemma isometrySphere_preimage_image {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) (A : Set (Metric.sphere (0 : V) 1)) :
    (fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' (isometrySphere L ⁻¹' A) =
      (L : V → V) ⁻¹' ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [Set.mem_preimage]
    refine ⟨isometrySphere L θ, hθ, ?_⟩
    rfl
  · intro hx
    rw [Set.mem_preimage] at hx
    rcases hx with ⟨a, ha, hLx⟩
    have hmem : x ∈ Metric.sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm]
      calc
        ‖x‖ = ‖(L : V → V) x‖ := (LinearIsometryEquiv.norm_map L x).symm
        _ = ‖(a : V)‖ := by rw [← hLx]
        _ = 1 := (mem_sphere_zero_iff_norm.mp a.2)
    refine ⟨⟨x, hmem⟩, ?_, rfl⟩
    have hEq : (isometrySphere L) ⟨x, hmem⟩ = a := by
      apply Subtype.ext
      change (L : V → V) (⟨x, hmem⟩ : Metric.sphere (0 : V) 1).1 = (a : V)
      exact hLx.symm
    simpa [hEq] using ha

private theorem isometrySphere_measurePreserving {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (L : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (isometrySphere L : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1)
      (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) volume.toSphere := by
  refine ⟨(isometrySphere L).measurable, ?_⟩
  apply Measure.ext
  intro A hA
  let f : Metric.sphere (0 : V) 1 → Metric.sphere (0 : V) 1 := isometrySphere L
  have hpre : MeasurableSet (f ⁻¹' A) := (isometrySphere L).measurable hA
  calc
    (Measure.map f (volume.toSphere : Measure (Metric.sphere (0 : V) 1))) A
        = (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) (f ⁻¹' A) := by
            rw [Measure.map_apply (isometrySphere L).measurable hA]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' (f ⁻¹' A))) := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V)) (s := f ⁻¹' A) hpre]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((L : V → V) ⁻¹' ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A))) := by
            congr 1
            rw [isometrySphere_preimage_image L A]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          ((L : V → V) ⁻¹' (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A))) := by
            congr 1
            rw [cone_preimage_isometry L]
    _ = (↑(Module.finrank ℝ V) : ℝ≥0∞) * volume
          (Ioo (0 : ℝ) 1 • ((fun θ : Metric.sphere (0 : V) 1 => (θ : V)) '' A)) := by
            congr 1
            rw [volume_preimage_isometry L]
    _ = (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) A := by
            rw [Measure.toSphere_apply' (μ := (volume : Measure V)) (s := A) hA]

private noncomputable def coordFlip (n : ℕ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin n => if j = i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) else (LinearIsometryEquiv.refl ℝ ℝ : ℝ ≃ₗᵢ[ℝ] ℝ))

private lemma coordFlip_apply {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (coordFlip n i x : EuclideanSpace ℝ (Fin n)) j = if j = i then - x j else x j := by
  simp [coordFlip, LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases h : j = i <;> simp [h]

private lemma prod_ite_pow {n : ℕ} (i0 : Fin n) (e : Fin n →₀ ℕ) :
    (Finset.univ.prod (fun i : Fin n => (if i = i0 then (-1 : ℝ) else 1) ^ (e i))) = (-1 : ℝ) ^ (e i0) := by
  have hmain : (Finset.univ.prod (fun i : Fin n => (if i = i0 then (-1 : ℝ) else 1) ^ (e i))) =
      (if i0 = i0 then (-1 : ℝ) else 1) ^ (e i0) := by
    exact Finset.prod_eq_single (s := Finset.univ)
      (f := fun i : Fin n => (if i = i0 then (-1 : ℝ) else 1) ^ (e i)) i0
      (by intro b hb hbne; simp [hbne])
      (by intro hnotin; simp at hnotin)
  simpa using hmain

private lemma prod_coordFlip_pow {n : ℕ} (i0 : Fin n) (e : Fin n →₀ ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (Finset.univ.prod (fun i : Fin n => ((coordFlip n i0 x : EuclideanSpace ℝ (Fin n)) i) ^ (e i))) =
      (-1 : ℝ) ^ (e i0) * (Finset.univ.prod (fun i : Fin n => (x : EuclideanSpace ℝ (Fin n)) i ^ (e i))) := by
  calc
    (Finset.univ.prod (fun i : Fin n => ((coordFlip n i0 x : EuclideanSpace ℝ (Fin n)) i) ^ (e i)))
        = Finset.univ.prod (fun i : Fin n => ((if i = i0 then (-1 : ℝ) else 1) * (x : EuclideanSpace ℝ (Fin n)) i) ^ (e i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            by_cases h : i = i0 <;> simp [h, coordFlip_apply]
    _ = (Finset.univ.prod (fun i : Fin n => (if i = i0 then (-1 : ℝ) else 1) ^ (e i))) *
        (Finset.univ.prod (fun i : Fin n => (x : EuclideanSpace ℝ (Fin n)) i ^ (e i))) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro i hi
            rw [mul_pow]
    _ = (-1 : ℝ) ^ (e i0) * (Finset.univ.prod (fun i : Fin n => (x : EuclideanSpace ℝ (Fin n)) i ^ (e i))) := by
            rw [prod_ite_pow i0 e]

theorem sphere_monomial_integral_zero_of_odd
    {n : ℕ} (hn : 0 < n) (e : Fin n →₀ ℕ)
    (hodd : ∃ i : Fin n, Odd (e i)) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        Finset.univ.prod (fun i : Fin n => ((θ : EuclideanSpace ℝ (Fin n)) i) ^ (e i))
      ∂MeasureTheory.volume.toSphere) = 0 := by
  classical
  rcases hodd with ⟨i0, hodd_i0⟩
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let σ : Measure S := MeasureTheory.volume.toSphere
  let f : S → S := isometrySphere (coordFlip n i0)
  let mon : S → ℝ := fun θ => Finset.univ.prod (fun i : Fin n => ((θ : E) i) ^ (e i))
  have hMP : MeasurePreserving f σ σ := by
    simpa [f, σ, S] using (isometrySphere_measurePreserving (V := E) (coordFlip n i0))
  have hME : MeasurableEmbedding f := by
    simpa [f] using (isometrySphere (coordFlip n i0)).measurableEmbedding
  have hflip : ∀ θ : S, mon (f θ) = - mon θ := by
    intro θ
    change (Finset.univ.prod (fun i : Fin n => ((coordFlip n i0 (θ : E) : E) i) ^ (e i))) =
      - (Finset.univ.prod (fun i : Fin n => ((θ : E) i) ^ (e i)))
    have hprod := prod_coordFlip_pow (n := n) (i0 := i0) (e := e) (x := (θ : E))
    rw [hprod]
    rw [hodd_i0.neg_one_pow]
    ring
  have hcomp : (∫ θ : S, mon (f θ) ∂σ) = (∫ θ : S, mon θ ∂σ) :=
    MeasurePreserving.integral_comp hMP hME mon
  have hneg : (∫ θ : S, mon θ ∂σ) = - (∫ θ : S, mon θ ∂σ) := by
    calc
      (∫ θ : S, mon θ ∂σ) = ∫ θ : S, mon (f θ) ∂σ := hcomp.symm
      _ = ∫ θ : S, - mon θ ∂σ := by
          apply integral_congr_ae
          filter_upwards with θ
          exact hflip θ
      _ = - (∫ θ : S, mon θ ∂σ) := by rw [integral_neg]
  linarith

end Commons.Analysis.MeasureTheory