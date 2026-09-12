import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.interior_empty_iff_affineSpan_ne_top
import Submission.Commons.Geometry.Convex.Hadwiger.parallel_body_valuation
import Submission.Commons.Geometry.Convex.Hadwiger.klain_333_box_vanishing

open scoped Pointwise
open MeasureTheory Metric Set
noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

/-! ## Basic measure facts -/

private lemma volume_eq_zero_of_empty_interior
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (K : ConvexBody V) (hK : interior (K : Set V) = ∅) : volume (K : Set V) = 0 := by
  have hsp : affineSpan ℝ (K : Set V) ≠ ⊤ :=
    (Commons.Geometry.Convex.Hadwiger.interior_empty_iff_affineSpan_ne_top (V := V) K).mp hK
  have hsub : (K : Set V) ⊆ (affineSpan ℝ (K : Set V) : Set V) := subset_affineSpan ℝ (K : Set V)
  have hvol : volume (affineSpan ℝ (K : Set V) : Set V) = 0 :=
    MeasureTheory.Measure.addHaar_affineSubspace (μ := volume) (affineSpan ℝ (K : Set V)) hsp
  exact le_antisymm (le_trans (measure_mono hsub) (le_of_eq hvol)) bot_le

private lemma volume_image_linearIsometry_general
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ V] [InnerProductSpace ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (s : Set V) :
    volume (e '' s) = volume s := by
  have hmp := e.measurePreserving
  have hemb := e.toHomeomorph.measurableEmbedding
  calc
    volume (e '' s) = volume (e ⁻¹' (e '' s)) := by
      rw [hmp.measure_preimage_emb hemb (e '' s)]
    _ = volume s := by rw [Set.preimage_image_eq s e.injective]

private lemma volume_image_add_right_vol
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (s : Set V) (t : V) :
    volume ((fun x : V => x + t) '' s) = volume s := by
  exact Commons.Geometry.Convex.Hadwiger.measure_image_add_right (V := V) volume s t

private lemma volume_image_neg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (s : Set V) : volume ((fun x : V => -x) '' s) = volume s := by
  have e : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.neg ℝ
  have h := volume_image_linearIsometry_general (V := V) (W := V) e s
  simpa using h

/-! ## The unit cube in `EuclideanSpace ℝ (Fin n)` -/

private def cubeFun (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)

private lemma cubeFun_convex (n : ℕ) : Convex ℝ (cubeFun n) := by
  dsimp [cubeFun]
  exact convex_pi (by intro i hi; exact convex_Icc 0 1)

private lemma cubeFun_compact (n : ℕ) : IsCompact (cubeFun n) := by
  dsimp [cubeFun]
  exact isCompact_univ_pi (fun i => isCompact_Icc)

private lemma cubeFun_nonempty (n : ℕ) : (cubeFun n).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  intro i hi
  exact ⟨le_rfl, by norm_num⟩

private lemma cubeFun_volume (n : ℕ) : volume (cubeFun n) = 1 := by
  dsimp [cubeFun]
  rw [volume_pi, MeasureTheory.Measure.pi_pi]
  simp [Real.volume_Icc]

private def stdCube (n : ℕ) : ConvexBody (EuclideanSpace ℝ (Fin n)) :=
  ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm '' cubeFun n,
    (cubeFun_convex n).linear_image ((EuclideanSpace.equiv (Fin n) ℝ).symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
    (cubeFun_compact n).image (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous,
    (cubeFun_nonempty n).image (fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm x)⟩

@[simp] lemma stdCube_coe (n : ℕ) :
    ((stdCube n : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' cubeFun n := rfl

private lemma stdCube_volume (n : ℕ) : volume ((stdCube n : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) = 1 := by
  rw [stdCube_coe]
  have hEq : (EuclideanSpace.equiv (Fin n) ℝ).symm '' cubeFun n = (WithLp.toLp 2) '' cubeFun n := by
    ext x; simp
  rw [hEq]
  have hto : MeasurePreserving (WithLp.toLp 2) volume volume := PiLp.volume_preserving_toLp (ι := Fin n)
  have hme : MeasurableEmbedding (WithLp.toLp 2) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hpre : (WithLp.toLp 2) ⁻¹' ((WithLp.toLp 2) '' cubeFun n) = cubeFun n :=
    Set.preimage_image_eq _ (WithLp.toLp_injective 2)
  have hvolpre := hto.measure_preimage_emb hme ((WithLp.toLp 2) '' cubeFun n)
  rw [← hvolpre, hpre]
  exact cubeFun_volume n

private lemma stdCube_volume_ne_zero (n : ℕ) :
    ((volume ((stdCube n : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))).toReal) ≠ 0 := by
  rw [stdCube_volume n]
  norm_num

/-! ## Transport of convex bodies along linear isometric equivalences -/

private def convexBody_map {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) : ConvexBody W :=
  ⟨e '' (K : Set V),
    K.convex.linear_image (e : V →ₗ[ℝ] W),
    K.isCompact.image e.continuous,
    K.nonempty.image (e : V → W)⟩

@[simp]
private theorem convexBody_map_coe {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    ((convexBody_map e K : ConvexBody W) : Set W) = e '' (K : Set V) := rfl

private theorem convexBody_map_symm_image {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    convexBody_map e.symm (convexBody_map e K) = K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases hy with ⟨z, hz, hzy⟩
    have h1 : e.symm (e z) = z := by simp
    have hx : x = z := by
      calc
        x = e.symm y := hxy.symm
        _ = e.symm (e z) := by rw [hzy]
        _ = z := h1
    simpa [hx] using hz
  · intro hx
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    simp

private lemma convexBody_map_volume {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ V] [InnerProductSpace ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    volume ((convexBody_map e K : ConvexBody W) : Set W) = volume (K : Set V) := by
  rw [convexBody_map_coe]
  exact volume_image_linearIsometry_general (V := V) (W := W) e (K : Set V)

private lemma convexBody_map_interior {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) :
    interior ((convexBody_map e K : ConvexBody W) : Set W) = e '' interior (K : Set V) := by
  rw [convexBody_map_coe]
  exact (e.toHomeomorph.image_interior (K : Set V)).symm

private lemma convexBody_map_continuous {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) : Continuous (fun K : ConvexBody V => convexBody_map e K) := by
  rw [Metric.continuous_iff]
  intro K ε hε
  refine ⟨ε, hε, ?_⟩
  intro L hKL
  rw [← ConvexBody.hausdorffDist_coe]
  rw [convexBody_map_coe, convexBody_map_coe]
  have hd : Metric.hausdorffDist (e '' (L : Set V)) (e '' (K : Set V)) =
      Metric.hausdorffDist (L : Set V) (K : Set V) := Metric.hausdorffDist_image e.isometry
  rw [hd]
  rwa [ConvexBody.hausdorffDist_coe]

end Commons.Geometry.Convex.Hadwiger

namespace Commons.Geometry.Convex.Hadwiger

/-! ## Transport set-level facts along `τ` -/

section Transport

variable {V S : Type*} [NormedAddCommGroup V] [NormedAddCommGroup S]
    [Module ℝ V] [Module ℝ S] (τ : V ≃ₗᵢ[ℝ] S)

private lemma symm_image_union (s t : Set S) :
    τ.symm '' (s ∪ t) = τ.symm '' s ∪ τ.symm '' t := by
  rw [Set.image_union]

private lemma symm_image_inter (s t : Set S) :
    τ.symm '' (s ∩ t) = τ.symm '' s ∩ τ.symm '' t := by
  rw [Set.image_inter τ.symm.injective]

private lemma symm_image_neg (s : Set S) :
    τ.symm '' (-s) = -(τ.symm '' s) := by
  exact Set.image_neg (f := (τ.symm : S →ₗ[ℝ] V)) s

private lemma symm_image_translate (t : S) (s : Set S) :
    τ.symm '' ((fun x : S => x + t) '' s) = (fun y : V => y + τ.symm t) '' (τ.symm '' s) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨x, hx, rfl⟩
    refine ⟨τ.symm x, ⟨x, hx, rfl⟩, ?_⟩
    rw [map_add]
  · rintro ⟨y, hy, hvy⟩
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨x + t, ⟨x, hx, rfl⟩, ?_⟩
    rw [map_add]
    exact hvy

private lemma symm_preimage_union (s t : Set S) :
    τ ⁻¹' (s ∪ t) = τ ⁻¹' s ∪ τ ⁻¹' t := by
  rw [Set.preimage_union]

end Transport

/-! ## Valuation transported from `S` to `V` (preimage along `τ : V ≃ₗᵢ S`) -/

section Pullback

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (τ : V ≃ₗᵢ[ℝ] S)

/-- preimage body in V of a body in S -/
noncomputable def preBody (K : ConvexBody S) : ConvexBody V := convexBody_map τ.symm K

@[simp] lemma preBody_coe (K : ConvexBody S) :
    ((preBody τ K : ConvexBody V) : Set V) = τ.symm '' (K : Set S) := by
  rfl

private lemma preBody_continuous : Continuous (fun K : ConvexBody S => preBody τ K) := by
  change Continuous (fun K : ConvexBody S => convexBody_map τ.symm K)
  exact convexBody_map_continuous (V := S) (W := V) τ.symm

/-- pull-back of a continuous valuation -/
noncomputable def pullVal (φ : ConvexBody V → ℝ) (hφ : Continuous φ) : ConvexBody S → ℝ :=
  fun K => φ (preBody τ K)

private lemma pullVal_continuous (φ : ConvexBody V → ℝ) (hφ : Continuous φ) :
    Continuous (pullVal τ φ hφ) := by
  change Continuous (fun K : ConvexBody S => φ (convexBody_map τ.symm K))
  exact hφ.comp (preBody_continuous (V := V) (S := S) τ)

end Pullback

/-! ## `volReal`: the (real) volume of a convex body in `EuclideanSpace ℝ (Fin n)` -/

section VolReal

private def volReal (n : ℕ) : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun K => (volume (K : Set (EuclideanSpace ℝ (Fin n)))).toReal

private lemma volReal_continuous (n : ℕ) : Continuous (volReal n) := by
  change Continuous (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
    (volume (K : Set (EuclideanSpace ℝ (Fin n)))).toReal)
  exact Commons.Geometry.Convex.Hadwiger.continuous_volume_convexBody n

private lemma volReal_additive (n : ℕ) :
    ∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin n)),
      (A : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∪ (D : Set (EuclideanSpace ℝ (Fin n))) →
      (B : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∩ (D : Set (EuclideanSpace ℝ (Fin n))) →
      volReal n A + volReal n B = volReal n C + volReal n D := by
  classical
  intro A B C D hU hI
  let S := EuclideanSpace ℝ (Fin n)
  have hmeasD : MeasurableSet (D : Set S) := D.isCompact.measurableSet
  have hie := MeasureTheory.measure_union_add_inter (μ := volume) (s := (C : Set S)) (ht := hmeasD)
  have hfin1 : volume ((C : Set S) ∪ (D : Set S)) ≠ ⊤ := by
    exact (C.isCompact.union D.isCompact).measure_lt_top.ne
  have hfin2 : volume ((C : Set S) ∩ (D : Set S)) ≠ ⊤ := by
    exact (C.isCompact.inter D.isCompact).measure_lt_top.ne
  have hfin3 : volume (C : Set S) ≠ ⊤ := C.isCompact.measure_lt_top.ne
  have hfin4 : volume (D : Set S) ≠ ⊤ := D.isCompact.measure_lt_top.ne
  have hto := congrArg ENNReal.toReal hie
  calc
    volReal n A + volReal n B
        = (volume ((C : Set S) ∪ (D : Set S))).toReal + (volume ((C : Set S) ∩ (D : Set S))).toReal := by
          change (volume (A : Set S)).toReal + (volume (B : Set S)).toReal =
            (volume ((C : Set S) ∪ (D : Set S))).toReal + (volume ((C : Set S) ∩ (D : Set S))).toReal
          rw [hU, hI]
    _ = (volume ((C : Set S) ∪ (D : Set S)) + volume ((C : Set S) ∩ (D : Set S))).toReal := by
          rw [ENNReal.toReal_add hfin1 hfin2]
    _ = (volume (C : Set S) + volume (D : Set S)).toReal := hto
    _ = (volume (C : Set S)).toReal + (volume (D : Set S)).toReal := by
          rw [ENNReal.toReal_add hfin3 hfin4]
    _ = volReal n C + volReal n D := by
          simp [volReal]

private lemma volReal_simple (n : ℕ) :
    ∀ K : ConvexBody (EuclideanSpace ℝ (Fin n)),
      interior (K : Set (EuclideanSpace ℝ (Fin n))) = ∅ → volReal n K = 0 := by
  intro K hK
  have hvol : volume (K : Set (EuclideanSpace ℝ (Fin n))) = 0 :=
    volume_eq_zero_of_empty_interior (V := EuclideanSpace ℝ (Fin n)) K hK
  simp [volReal, hvol]

private lemma volReal_translation (n : ℕ) :
    ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)), ∀ t : EuclideanSpace ℝ (Fin n),
      (B : Set (EuclideanSpace ℝ (Fin n))) = (fun x : EuclideanSpace ℝ (Fin n) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin n))) →
      volReal n A = volReal n B := by
  intro A B t hB
  have hvol : volume (B : Set (EuclideanSpace ℝ (Fin n))) = volume (A : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hB]
    exact volume_image_add_right_vol (V := EuclideanSpace ℝ (Fin n)) (A : Set (EuclideanSpace ℝ (Fin n))) t
  simp [volReal, hvol]

private lemma volReal_neg (n : ℕ) :
    ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)),
      (B : Set (EuclideanSpace ℝ (Fin n))) = -(A : Set (EuclideanSpace ℝ (Fin n))) →
      volReal n A = volReal n B := by
  intro A B hB
  have hvol : volume (B : Set (EuclideanSpace ℝ (Fin n))) = volume (A : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [hB]
    have hset : -(A : Set (EuclideanSpace ℝ (Fin n))) = (fun x : EuclideanSpace ℝ (Fin n) => -x) '' (A : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      simp [Set.mem_neg]
    rw [hset]
    exact volume_image_neg (V := EuclideanSpace ℝ (Fin n)) (A : Set (EuclideanSpace ℝ (Fin n)))
  simp [volReal, hvol]

end VolReal

/-! ## Negation invariance from isometry invariance -/

section NegInv

private lemma hiso_neg {V : Type*} [NormedAddCommGroup V] [Module ℝ V]
    (φ : ConvexBody V → ℝ)
    (hiso : ∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e '' (A : Set V) → φ B = φ A)
    {A B : ConvexBody V} (h : (B : Set V) = -(A : Set V)) : φ A = φ B := by
  let e : V ≃ₗᵢ[ℝ] V := LinearIsometryEquiv.neg ℝ
  have hEq : (B : Set V) = e '' (A : Set V) := by
    rw [h]
    ext x
    constructor
    · intro hx
      refine ⟨-x, Set.mem_neg.mp hx, ?_⟩
      change (LinearIsometryEquiv.neg ℝ : V → V) (-x) = x
      simp
    · rintro ⟨y, hy, hxy⟩
      apply Set.mem_neg.mpr
      have hxy' : y = -x := by
        change (LinearIsometryEquiv.neg ℝ : V → V) y = x at hxy
        simpa using congrArg (fun z : V => -z) hxy
      simpa [hxy'] using hy
  exact (hiso A B e hEq).symm

end NegInv

/-! ## Properties of the pulled-back valuation -/

section PullProps

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (τ : V ≃ₗᵢ[ℝ] S)

private lemma pullVal_additive (φ : ConvexBody V → ℝ) (hφcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D) :
    ∀ A B C D : ConvexBody S,
      (A : Set S) = (C : Set S) ∪ (D : Set S) →
      (B : Set S) = (C : Set S) ∩ (D : Set S) →
      pullVal τ φ hφcont A + pullVal τ φ hφcont B = pullVal τ φ hφcont C + pullVal τ φ hφcont D := by
  intro A B C D hU hI
  have hU' : ((preBody τ A : ConvexBody V) : Set V) =
      ((preBody τ C : ConvexBody V) : Set V) ∪ ((preBody τ D : ConvexBody V) : Set V) := by
    rw [preBody_coe, preBody_coe, preBody_coe]
    rw [← symm_image_union (V := V) (S := S) τ (C : Set S) (D : Set S)]
    rw [hU]
  have hI' : ((preBody τ B : ConvexBody V) : Set V) =
      ((preBody τ C : ConvexBody V) : Set V) ∩ ((preBody τ D : ConvexBody V) : Set V) := by
    rw [preBody_coe, preBody_coe, preBody_coe]
    rw [← symm_image_inter (V := V) (S := S) τ (C : Set S) (D : Set S)]
    rw [hI]
  have h := hadd (preBody τ A) (preBody τ B) (preBody τ C) (preBody τ D) hU' hI'
  change pullVal τ φ hφcont A + pullVal τ φ hφcont B = pullVal τ φ hφcont C + pullVal τ φ hφcont D
  exact h

private lemma pullVal_simple (φ : ConvexBody V → ℝ) (hφcont : Continuous φ)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) :
    ∀ K : ConvexBody S, interior (K : Set S) = ∅ → pullVal τ φ hφcont K = 0 := by
  intro K hK
  have hint : interior ((preBody τ K : ConvexBody V) : Set V) = ∅ := by
    have hint' := convexBody_map_interior (V := S) (W := V) τ.symm K
    change interior ((convexBody_map τ.symm K : ConvexBody V) : Set V) = ∅
    rw [hint', hK, Set.image_empty]
  have h := hsimple (preBody τ K) hint
  change pullVal τ φ hφcont K = 0
  exact h

private lemma pullVal_translation (φ : ConvexBody V → ℝ) (hφcont : Continuous φ)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B) :
    ∀ A B : ConvexBody S, ∀ t : S,
      (B : Set S) = (fun x : S => x + t) '' (A : Set S) →
      pullVal τ φ hφcont A = pullVal τ φ hφcont B := by
  intro A B t hB
  have hcar : ((preBody τ B : ConvexBody V) : Set V) =
      (fun y : V => y + τ.symm t) '' ((preBody τ A : ConvexBody V) : Set V) := by
    rw [preBody_coe, preBody_coe]
    rw [hB]
    exact symm_image_translate (V := V) (S := S) τ t (A : Set S)
  have h := htrans (preBody τ A) (preBody τ B) (τ.symm t) hcar
  change pullVal τ φ hφcont A = pullVal τ φ hφcont B
  exact h

private lemma pullVal_neg (φ : ConvexBody V → ℝ) (hφcont : Continuous φ)
    (hiso : ∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e '' (A : Set V) → φ B = φ A) :
    ∀ A B : ConvexBody S,
      (B : Set S) = -(A : Set S) →
      pullVal τ φ hφcont A = pullVal τ φ hφcont B := by
  intro A B hB
  have hcar : ((preBody τ B : ConvexBody V) : Set V) = -((preBody τ A : ConvexBody V) : Set V) := by
    rw [preBody_coe, preBody_coe]
    rw [hB]
    exact symm_image_neg (V := V) (S := S) τ (A : Set S)
  have h := hiso_neg (V := V) φ hiso (A := preBody τ A) (B := preBody τ B) hcar
  change pullVal τ φ hφcont A = pullVal τ φ hφcont B
  exact h

end PullProps

end Commons.Geometry.Convex.Hadwiger

namespace Commons.Geometry.Convex.Hadwiger

/-! ## Main derivation (development version, using stub for box vanishing) -/

section Main

open scoped Pointwise

theorem simple_rigid_invariant_eq_const_volume
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (φ : ConvexBody V → ℝ)
    (hcont : Continuous φ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hiso : ∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e '' (A : Set V) → φ B = φ A)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) :
    ∃ c : ℝ, ∀ K : ConvexBody V, φ K = c * (MeasureTheory.volume (K : Set V)).toReal := by
  classical
  let n : ℕ := Module.finrank ℝ V
  let E : Type := EuclideanSpace ℝ (Fin n)
  let b : OrthonormalBasis (Fin n) ℝ V := stdOrthonormalBasis ℝ V
  let τ : V ≃ₗᵢ[ℝ] E := b.repr
  let Q : ConvexBody E := stdCube n
  let Φ : ConvexBody E → ℝ := pullVal (V := V) (S := E) τ φ hcont
  let vR : ConvexBody E → ℝ := volReal n
  let c : ℝ := Φ Q / (volume ((Q : ConvexBody E) : Set E)).toReal
  let ψ : ConvexBody E → ℝ := fun K => Φ K - c * vR K
  have hvolQ : (volume ((Q : ConvexBody E) : Set E)).toReal ≠ 0 := by
    dsimp [Q]
    exact stdCube_volume_ne_zero n
  have hΦcont : Continuous Φ := by
    dsimp [Φ]
    exact pullVal_continuous (V := V) (S := E) τ φ hcont
  have hψcont : Continuous ψ := by
    dsimp [ψ, vR]
    exact hΦcont.sub (continuous_const.mul (volReal_continuous n))
  have hΦadd : ∀ A B C D : ConvexBody E,
      (A : Set E) = (C : Set E) ∪ (D : Set E) →
      (B : Set E) = (C : Set E) ∩ (D : Set E) → Φ A + Φ B = Φ C + Φ D := by
    intro A B C D hU hI
    dsimp [Φ]
    exact pullVal_additive (V := V) (S := E) τ φ hcont hadd A B C D hU hI
  have hvadd : ∀ A B C D : ConvexBody E,
      (A : Set E) = (C : Set E) ∪ (D : Set E) →
      (B : Set E) = (C : Set E) ∩ (D : Set E) → vR A + vR B = vR C + vR D := by
    intro A B C D hU hI
    dsimp [vR]
    exact volReal_additive n A B C D hU hI
  have hψadd : ∀ A B C D : ConvexBody E,
      (A : Set E) = (C : Set E) ∪ (D : Set E) →
      (B : Set E) = (C : Set E) ∩ (D : Set E) → ψ A + ψ B = ψ C + ψ D := by
    intro A B C D hU hI
    have h1 := hΦadd A B C D hU hI
    have h2 := hvadd A B C D hU hI
    have hAB : ψ A + ψ B = (Φ A + Φ B) - c * (vR A + vR B) := by
      dsimp [ψ]
      ring
    have hCD : ψ C + ψ D = (Φ C + Φ D) - c * (vR C + vR D) := by
      dsimp [ψ]
      ring
    rw [hAB, hCD, h1, h2]
  have hψtrans : ∀ A B : ConvexBody E, ∀ t : E,
      (B : Set E) = (fun x : E => x + t) '' (A : Set E) → ψ A = ψ B := by
    intro A B t hB
    have h1 : Φ A = Φ B := by
      dsimp [Φ]
      exact pullVal_translation (V := V) (S := E) τ φ hcont htrans A B t hB
    have h2 : vR A = vR B := by
      dsimp [vR]
      exact volReal_translation n A B t hB
    dsimp [ψ]
    rw [h1, h2]
  have hΦsimple : ∀ K : ConvexBody E, interior (K : Set E) = ∅ → Φ K = 0 := by
    intro K hK
    dsimp [Φ]
    exact pullVal_simple (V := V) (S := E) τ φ hcont hsimple K hK
  have hψsimple : ∀ K : ConvexBody E, interior (K : Set E) = ∅ → ψ K = 0 := by
    intro K hK
    have h1 := hΦsimple K hK
    have h2 : vR K = 0 := by
      dsimp [vR]
      exact volReal_simple n K hK
    dsimp [ψ]
    rw [h1, h2]
    simp
  have hΦneg : ∀ A B : ConvexBody E,
      (B : Set E) = -(A : Set E) → Φ A = Φ B := by
    intro A B hB
    dsimp [Φ]
    exact pullVal_neg (V := V) (S := E) τ φ hcont hiso A B hB
  have hvneg : ∀ A B : ConvexBody E,
      (B : Set E) = -(A : Set E) → vR A = vR B := by
    intro A B hB
    dsimp [vR]
    exact volReal_neg n A B hB
  have hψneg : ∀ A B : ConvexBody E,
      (B : Set E) = -(A : Set E) → ψ A = ψ B := by
    intro A B hB
    have h1 := hΦneg A B hB
    have h2 := hvneg A B hB
    dsimp [ψ]
    rw [h1, h2]
  have hcube0 : ψ Q = 0 := by
    dsimp [ψ, Q, vR, c, volReal]
    rw [← stdCube_coe n]
    rw [stdCube_volume n]
    norm_num
  have hcube : ∀ Q' : ConvexBody E,
      (Q' : Set E) = (EuclideanSpace.equiv (Fin n) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) →
      ψ Q' = 0 := by
    intro Q' hQ'
    have hb : Q' = stdCube n := by
      apply ConvexBody.ext
      rw [hQ']
      exact stdCube_coe n
    rw [hb]
    exact hcube0
  have hzero : ∀ K : ConvexBody E, ψ K = 0 := by
    simpa [E, ψ] using
      klain_333_box_vanishing n ψ hψcont hψadd hψtrans hψsimple hψneg hcube
  refine ⟨c, ?_⟩
  intro K
  let K' : ConvexBody E := convexBody_map τ K
  have hψK : ψ K' = 0 := hzero K'
  have hpre : preBody (V := V) (S := E) τ K' = K := by
    dsimp [preBody, K']
    exact convexBody_map_symm_image (V := V) (W := E) τ K
  have hvolE : volume ((K' : ConvexBody E) : Set E) = volume (K : Set V) := by
    dsimp [K']
    exact convexBody_map_volume (V := V) (W := E) τ K
  have hΦK : Φ K' = φ K := by
    change φ (preBody (V := V) (S := E) τ K') = φ K
    rw [hpre]
  dsimp [ψ, vR, volReal] at hψK
  rw [hΦK] at hψK
  have hvv : (volume ((K' : ConvexBody E) : Set E)).toReal = (volume (K : Set V)).toReal := by
    rw [hvolE]
  rw [hvv] at hψK
  have : φ K = c * (volume (K : Set V)).toReal := by
    linarith
  exact this

end Main

end Commons.Geometry.Convex.Hadwiger