import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal

set_option linter.unusedSectionVars false

open scoped NumberField
open scoped WithZero WithZeroTopology

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

section Finite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem globalCFT_valuation_smulHeightOneSpectrum (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (x : L) :
    (Place.smulHeightOneSpectrum σ q).valuation L (σ.toRingEquiv x) = q.valuation L x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq (R := 𝓞 L) (K := L)
    (Place.ringOfIntegersEquiv σ) σ.toRingEquiv (fun _ => rfl) q
    (Place.smulHeightOneSpectrum σ q) (Place.smulHeightOneSpectrum_asIdeal σ q) x

theorem globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (WithVal.congr (q.valuation L)
      ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv) :=
  Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
      σ.toRingEquiv).toRingHom
    (by
      intro x
      change (WithVal.valuation ((Place.smulHeightOneSpectrum σ q).valuation L))
          ((WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
            σ.toRingEquiv) x) = (WithVal.valuation (q.valuation L)) x
      rw [WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal, WithVal.ofVal_toVal,
        WithVal.valuation_apply_eq_ofVal]
      exact globalCFT_valuation_smulHeightOneSpectrum σ q x.ofVal)
    (by
      intro γ hγ
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L q γ
      exact ⟨WithVal.toVal (q.valuation L) y, by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩)

theorem globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformContinuous (WithVal.congr (q.valuation L)
      ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv).symm := by
  rw [WithVal.congr_symm]
  exact Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (WithVal.congr ((Place.smulHeightOneSpectrum σ q).valuation L) (q.valuation L)
      σ.toRingEquiv.symm).toRingHom
    (by
      intro x
      change (WithVal.valuation (q.valuation L))
          ((WithVal.congr ((Place.smulHeightOneSpectrum σ q).valuation L) (q.valuation L)
            σ.toRingEquiv.symm) x) =
          (WithVal.valuation ((Place.smulHeightOneSpectrum σ q).valuation L)) x
      rw [WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal, WithVal.ofVal_toVal,
        WithVal.valuation_apply_eq_ofVal]
      have h := globalCFT_valuation_smulHeightOneSpectrum σ q ((σ.toRingEquiv).symm x.ofVal)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm)
    (by
      intro γ hγ
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L
        (Place.smulHeightOneSpectrum σ q) γ
      exact ⟨WithVal.toVal ((Place.smulHeightOneSpectrum σ q).valuation L) y,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
        by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩)

/-- The `WithVal`-level ring isomorphism of completions induced by `σ`. -/
noncomputable def globalCFT_withValCongrEquiv (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    UniformSpace.Completion (WithVal (q.valuation L)) ≃+*
      UniformSpace.Completion (WithVal ((Place.smulHeightOneSpectrum σ q).valuation L)) :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv)
    (globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q).continuous
    (globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum_symm σ q).continuous

variable (σ : L ≃ₐ[K] L) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))

theorem globalCFT_withValCongrEquiv_coe (y : WithVal (q.valuation L)) :
    globalCFT_withValCongrEquiv σ q
        (y : UniformSpace.Completion (WithVal (q.valuation L)))
      = ((WithVal.congr (q.valuation L) ((Place.smulHeightOneSpectrum σ q).valuation L)
          σ.toRingEquiv) y :
        UniformSpace.Completion (WithVal ((Place.smulHeightOneSpectrum σ q).valuation L))) := by
  rw [globalCFT_withValCongrEquiv, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe]
  exact globalCFT_uniformContinuous_withVal_smulHeightOneSpectrum σ q

theorem globalCFT_algebraMap_valuationCompletion (x : L) :
    algebraMap L ((q.valuation L).Completion) x
      = (WithVal.toVal (q.valuation L) x :
        UniformSpace.Completion (WithVal (q.valuation L))) := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply]
  simp

theorem globalCFT_algebraMap_eq_coe (y : L) :
    algebraMap L (q.adicCompletion L) y = (y : q.adicCompletion L) := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp

/-- The ring isomorphism of adic completions induced by a `K`-algebra automorphism `σ`. -/
noncomputable def globalCFT_adicCongrEquiv :
    q.adicCompletion L ≃+* (Place.smulHeightOneSpectrum σ q).adicCompletion L :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L q).trans
    ((globalCFT_withValCongrEquiv σ q).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L
        (Place.smulHeightOneSpectrum σ q)).symm)

theorem globalCFT_adicCongrEquiv_algebraMap (x : L) :
    globalCFT_adicCongrEquiv σ q (algebraMap L (q.adicCompletion L) x) =
      algebraMap L ((Place.smulHeightOneSpectrum σ q).adicCompletion L) (σ.toRingEquiv x) := by
  rw [globalCFT_adicCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply]
  have h1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L q)
      (algebraMap L (q.adicCompletion L) x) = algebraMap L ((q.valuation L).Completion) x := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
    exact IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
      (R := 𝓞 L) (K := L) (S := L) q x
  rw [h1]
  rw [globalCFT_algebraMap_valuationCompletion (q := q) x, globalCFT_withValCongrEquiv_coe σ q,
    WithVal.congr_apply, WithVal.ofVal_toVal]
  rw [← globalCFT_algebraMap_valuationCompletion (q := Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]
  rw [← IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
    (R := 𝓞 L) (K := L) (S := L) (Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]
  rfl

theorem globalCFT_withValCongrEquiv_continuous :
    Continuous (globalCFT_withValCongrEquiv σ q) := by
  have h : ⇑(globalCFT_withValCongrEquiv σ q) =
      UniformSpace.Completion.map ⇑(WithVal.congr (q.valuation L)
        ((Place.smulHeightOneSpectrum σ q).valuation L) σ.toRingEquiv) := by
    funext a
    rw [globalCFT_withValCongrEquiv, UniformSpace.Completion.mapRingEquiv_apply]
  rw [h]
  exact UniformSpace.Completion.continuous_map

theorem globalCFT_adicCongrEquiv_continuous :
    Continuous (globalCFT_adicCongrEquiv σ q) := by
  have h : ⇑(globalCFT_adicCongrEquiv σ q) =
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion (R := 𝓞 L) (K := L)
          (v := Place.smulHeightOneSpectrum σ q)) ∘
        (⇑(globalCFT_withValCongrEquiv σ q) ∘
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion (R := 𝓞 L) (K := L)
            (v := q))) := by
    funext a
    simp only [Function.comp_apply, globalCFT_adicCongrEquiv, RingEquiv.trans_apply,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
    rfl
  rw [h]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L
    (Place.smulHeightOneSpectrum σ q)).comp
    ((globalCFT_withValCongrEquiv_continuous σ q).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L q))

theorem globalCFT_adicCongrEquiv_coe (x : L) :
    globalCFT_adicCongrEquiv σ q (x : q.adicCompletion L) =
      ((σ.toRingEquiv x : L) : (Place.smulHeightOneSpectrum σ q).adicCompletion L) := by
  rw [← globalCFT_algebraMap_eq_coe (q := q) x, globalCFT_adicCongrEquiv_algebraMap σ q x,
    globalCFT_algebraMap_eq_coe (q := Place.smulHeightOneSpectrum σ q) (σ.toRingEquiv x)]

theorem globalCFT_adicCongrEquiv_valued (y : q.adicCompletion L) :
    Valued.v (globalCFT_adicCongrEquiv σ q y) = Valued.v y := by
  have hdense : DenseRange ((↑) : L → q.adicCompletion L) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L q
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
    simpa using h
  have hcont1 : Continuous (fun y : q.adicCompletion L => Valued.v (globalCFT_adicCongrEquiv σ q y)) :=
    (Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L
        (Place.smulHeightOneSpectrum σ q))).comp (globalCFT_adicCongrEquiv_continuous σ q)
  have hcont2 : Continuous (fun y : q.adicCompletion L => Valued.v y) :=
    Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L q)
  have heq : (fun y : q.adicCompletion L => Valued.v (globalCFT_adicCongrEquiv σ q y)) =
      fun y => Valued.v y :=
    hdense.equalizer hcont1 hcont2 (by
      funext x
      rw [Function.comp_apply, Function.comp_apply, globalCFT_adicCongrEquiv_coe σ q x,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
      simpa using globalCFT_valuation_smulHeightOneSpectrum σ q x)
  exact congrFun heq y

theorem globalCFT_adicCongrEquiv_localUnits (u : (q.adicCompletion L)ˣ) :
    u ∈ Place.localUnits L (Place.ofFinite q) ↔
      Units.map (globalCFT_adicCongrEquiv σ q).toMonoidHom u ∈
        Place.localUnits L (Place.ofFinite (Place.smulHeightOneSpectrum σ q)) := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one,
    Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
  change Valued.v ((u : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 1 ↔
    Valued.v ((globalCFT_adicCongrEquiv σ q) ↑u) = 1
  rw [globalCFT_adicCongrEquiv_valued σ q (u : q.adicCompletion L)]

/-- The nonarchimedean case of the functoriality of the local field. -/
theorem globalCFT_exists_localRingEquiv_smul_finite :
    ∃ e : q.adicCompletion L ≃+* (Place.smulHeightOneSpectrum σ q).adicCompletion L,
      (∀ x : L, e (algebraMap L (q.adicCompletion L) x) =
        algebraMap L ((Place.smulHeightOneSpectrum σ q).adicCompletion L) (σ x)) ∧
      (∀ u : (q.adicCompletion L)ˣ,
        u ∈ Place.localUnits L (Place.ofFinite q) ↔
          Units.map e.toMonoidHom u ∈ Place.localUnits L
            (Place.ofFinite (Place.smulHeightOneSpectrum σ q))) :=
  ⟨globalCFT_adicCongrEquiv σ q,
    fun x => globalCFT_adicCongrEquiv_algebraMap σ q x,
    fun u => globalCFT_adicCongrEquiv_localUnits σ q u⟩

end Finite

section Infinite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The ring equivalence `WithAbs w.1 ≃+* WithAbs ((σ • w).1)` induced by `σ`. -/
noncomputable def globalCFT_withAbsCongrEquiv (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    WithAbs w.1 ≃+* WithAbs ((σ • w).1) :=
  WithAbs.congr w.1 ((σ • w).1) σ.toRingEquiv

theorem globalCFT_withAbsCongrEquiv_norm (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L)
    (z : WithAbs w.1) : ‖globalCFT_withAbsCongrEquiv σ w z‖ = ‖z‖ := by
  rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_apply, WithAbs.norm_toAbs_eq,
    WithAbs.norm_eq_apply_ofAbs]
  rw [← NumberField.InfinitePlace.coe_apply, ← NumberField.InfinitePlace.coe_apply,
    NumberField.InfinitePlace.smul_apply]
  congr 1
  simp

theorem globalCFT_isometry_withAbsCongrEquiv (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    Isometry (globalCFT_withAbsCongrEquiv σ w) := by
  rw [isometry_iff_dist_eq]
  intro x y
  simp only [dist_eq_norm, ← map_sub]
  rw [globalCFT_withAbsCongrEquiv_norm]

theorem globalCFT_isometry_withAbsCongrEquiv_symm (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    Isometry (globalCFT_withAbsCongrEquiv σ w).symm := by
  have hnorm : ∀ z : WithAbs ((σ • w).1),
      ‖(WithAbs.congr ((σ • w).1) (w.1) σ.toRingEquiv.symm) z‖ = ‖z‖ := by
    intro z
    rw [WithAbs.congr_apply, WithAbs.norm_toAbs_eq, WithAbs.norm_eq_apply_ofAbs]
    rw [← NumberField.InfinitePlace.coe_apply, ← NumberField.InfinitePlace.coe_apply,
      NumberField.InfinitePlace.smul_apply]
    simp
  rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_symm]
  rw [isometry_iff_dist_eq]
  intro x y
  simp only [dist_eq_norm, ← map_sub]
  rw [hnorm]

/-- The ring isomorphism of archimedean completions induced by `σ`. -/
noncomputable def globalCFT_infiniteCongrEquiv (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) : w.Completion ≃+* (σ • w).Completion :=
  (NumberField.InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
        (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous).trans
      (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm)

theorem globalCFT_infiniteCongrEquiv_algebraMap (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) (x : L) :
    globalCFT_infiniteCongrEquiv σ w (algebraMap L w.Completion x) =
      algebraMap L (σ • w).Completion (σ x) := by
  have h1 : (NumberField.InfinitePlace.Completion.equiv w) (algebraMap L w.Completion x)
      = algebraMap L (w.1.Completion) x := by
    rw [NumberField.InfinitePlace.Completion.equiv_apply]
    exact NumberField.InfinitePlace.Completion.algebraMap_toCompletion w L x
  have h2 : (UniformSpace.Completion.mapRingEquiv (globalCFT_withAbsCongrEquiv σ w)
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
        (globalCFT_isometry_withAbsCongrEquiv_symm σ w).continuous)
        (algebraMap L (w.1.Completion) x)
      = algebraMap L ((σ • w).1.Completion) (σ x) := by
    have hcoe : algebraMap L (w.1.Completion) x
        = (WithAbs.toAbs w.1 x : UniformSpace.Completion (WithAbs w.1)) := by
      rw [UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
      simp
    rw [hcoe, UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.map_coe]
    · rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_apply]
      rw [UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
      simp
    · exact uniformContinuous_addMonoidHom_of_continuous
        (globalCFT_isometry_withAbsCongrEquiv σ w).continuous
  have h3 : (NumberField.InfinitePlace.Completion.equiv (σ • w)).symm
      (algebraMap L ((σ • w).1.Completion) (σ x))
      = algebraMap L ((σ • w).Completion) (σ x) := by
    rw [← NumberField.InfinitePlace.Completion.algebraMap_toCompletion (σ • w) L (σ x)]
    rfl
  rw [globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, h1, h2, h3]

/-- The archimedean case of the functoriality of the local field. -/
theorem globalCFT_exists_localRingEquiv_smul_infinite (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) :
    ∃ e : w.Completion ≃+* (σ • w).Completion,
      (∀ x : L, e (algebraMap L w.Completion x) = algebraMap L (σ • w).Completion (σ x)) ∧
      (∀ u : (w.Completion)ˣ,
        u ∈ Place.localUnits L (Place.ofInfinite w) ↔
          Units.map e.toMonoidHom u ∈ Place.localUnits L (Place.ofInfinite (σ • w))) :=
  ⟨globalCFT_infiniteCongrEquiv σ w,
    fun x => globalCFT_infiniteCongrEquiv_algebraMap σ w x,
    fun u => by simp [Place.localUnits_ofInfinite]⟩

end Infinite

theorem globalCFT_exists_localRingEquiv_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (v : NK.GlobalCFT.Place L) :
    ∃ e : (NK.GlobalCFT.Place.localField L v) ≃+* (NK.GlobalCFT.Place.localField L (σ • v)),
      (∀ x : L, e (algebraMap L (NK.GlobalCFT.Place.localField L v) x) =
        algebraMap L (NK.GlobalCFT.Place.localField L (σ • v)) (σ x)) ∧
      (∀ u : (NK.GlobalCFT.Place.localField L v)ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits L v ↔
          Units.map e.toMonoidHom u ∈ NK.GlobalCFT.Place.localUnits L (σ • v)) := by
  cases v with
  | inl w =>
      obtain ⟨e, h1, h2⟩ := globalCFT_exists_localRingEquiv_smul_infinite σ w
      exact ⟨e, h1, h2⟩
  | inr q =>
      obtain ⟨e, h1, h2⟩ := globalCFT_exists_localRingEquiv_smul_finite σ q
      exact ⟨e, h1, h2⟩

end NK.GlobalCFT.Galois
