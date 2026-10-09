import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
import Submission.NK.GlobalCFTdeep.Transport.valuation_mapRingEquiv
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal

/-!
# Transport of the local fields along a ring equivalence of number fields

...
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField WithZero WithZeroTopology
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.HasseIndex

open NK.GlobalCFT NK.GlobalCFTdeep.Transport

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-! ## The finite places -/

/-- The `Q`-adic valuation on `K` is carried to the `Q'`-adic valuation on `K'` by the ring
equivalence `e`, where `Q' = finitePlaceEquiv e Q`. -/
theorem valuation_mapRingEquiv' (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    (finitePlaceEquiv e Q).valuation K' (e x) = Q.valuation K x :=
  NK.GlobalCFTdeep.Transport.valuation_mapRingEquiv e Q x

/-- **The `WithVal`-level transport of a finite place**: the `Q`-adic value groups of `K` and
`K'` are identified by `e`. -/
noncomputable def withValCongr (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    WithVal (Q.valuation K) ≃+* WithVal ((finitePlaceEquiv e Q).valuation K') :=
  WithVal.congr (Q.valuation K) ((finitePlaceEquiv e Q).valuation K') (e : K ≃+* K')

theorem withValCongr_valuation (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K))
    (x : WithVal (Q.valuation K)) :
    WithVal.valuation ((finitePlaceEquiv e Q).valuation K') (withValCongr e Q x) =
      WithVal.valuation (Q.valuation K) x := by
  simp only [withValCongr, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal,
    valuation_mapRingEquiv']

theorem withValCongr_symm_valuation (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K))
    (x : WithVal ((finitePlaceEquiv e Q).valuation K')) :
    WithVal.valuation (Q.valuation K) ((withValCongr e Q).symm x) =
      WithVal.valuation ((finitePlaceEquiv e Q).valuation K') x := by
  conv_lhs => rw [← withValCongr_valuation e Q ((withValCongr e Q).symm x)]
  rw [RingEquiv.apply_symm_apply]

theorem withValCongr_uniformContinuous (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    UniformContinuous (withValCongr e Q : WithVal (Q.valuation K) →
      WithVal ((finitePlaceEquiv e Q).valuation K')) := by
  refine Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (withValCongr e Q).toRingHom (withValCongr_valuation e Q) ?_
  intro γ hγ
  obtain ⟨y, hy⟩ := HeightOneSpectrum.valuation_surjective K Q γ
  exact ⟨WithVal.toVal (Q.valuation K) y,
    by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
    by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩

theorem withValCongr_symm_uniformContinuous (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    UniformContinuous ((withValCongr e Q).symm : WithVal ((finitePlaceEquiv e Q).valuation K') →
      WithVal (Q.valuation K)) := by
  refine Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
    (withValCongr e Q).symm.toRingHom (withValCongr_symm_valuation e Q) ?_
  intro γ hγ
  obtain ⟨y, hy⟩ := HeightOneSpectrum.valuation_surjective K' (finitePlaceEquiv e Q) γ
  exact ⟨WithVal.toVal ((finitePlaceEquiv e Q).valuation K') y,
    by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
    by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩

/-- The isometry of the `Q`-adic completions induced by `e`. -/
noncomputable def completionCongr (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    (Q.valuation K).Completion ≃+* ((finitePlaceEquiv e Q).valuation K').Completion :=
  UniformSpace.Completion.mapRingEquiv (withValCongr e Q)
    (withValCongr_uniformContinuous e Q).continuous
    (withValCongr_symm_uniformContinuous e Q).continuous

theorem completionCongr_coe (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    completionCongr e Q (x : (Q.valuation K).Completion) =
      (e x : ((finitePlaceEquiv e Q).valuation K').Completion) := by
  rw [completionCongr, UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe (withValCongr_uniformContinuous e Q)]
  try rw [WithVal.equiv_symm_apply]
  try rfl

theorem completionCongr_continuous (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    Continuous (completionCongr e Q : (Q.valuation K).Completion →
      ((finitePlaceEquiv e Q).valuation K').Completion) := by
  have hfun : (completionCongr e Q : (Q.valuation K).Completion →
      ((finitePlaceEquiv e Q).valuation K').Completion) =
      UniformSpace.Completion.map (withValCongr e Q : WithVal (Q.valuation K) →
        WithVal ((finitePlaceEquiv e Q).valuation K')) :=
    funext fun a => UniformSpace.Completion.mapRingEquiv_apply _ _ _ a
  rw [hfun]
  exact UniformSpace.Completion.continuous_map

/-- **The transport of a finite local field along a ring equivalence of number fields.** -/
noncomputable def finiteLocalEquiv (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    Q.adicCompletion K ≃+* (finitePlaceEquiv e Q).adicCompletion K' :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q).trans
    ((completionCongr e Q).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K' (finitePlaceEquiv e Q)).symm)

theorem finiteLocalEquiv_coe (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    finiteLocalEquiv e Q (x : Q.adicCompletion K) =
      (e x : (finitePlaceEquiv e Q).adicCompletion K') := by
  change (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K' (finitePlaceEquiv e Q)).symm
    (completionCongr e Q ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q)
      (x : Q.adicCompletion K))) = _
  rw [show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q) (x : Q.adicCompletion K) =
      (x : (Q.valuation K).Completion) from rfl, completionCongr_coe]
  rfl

theorem finiteLocalEquiv_algebraMap (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    finiteLocalEquiv e Q (algebraMap K (Q.adicCompletion K) x) =
      algebraMap K' ((finitePlaceEquiv e Q).adicCompletion K') (e x) := by
  have hcoe : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  have hcoe' : algebraMap K' ((finitePlaceEquiv e Q).adicCompletion K') (e x) =
      (e x : (finitePlaceEquiv e Q).adicCompletion K') := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  rw [hcoe, hcoe', finiteLocalEquiv_coe]

theorem finiteLocalEquiv_continuous (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteLocalEquiv e Q : Q.adicCompletion K →
      (finitePlaceEquiv e Q).adicCompletion K') := by
  have hfun : (finiteLocalEquiv e Q : Q.adicCompletion K →
      (finitePlaceEquiv e Q).adicCompletion K') = fun x =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion (R := 𝓞 K') (K := K')
        (v := finitePlaceEquiv e Q)
        (completionCongr e Q (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion
          (R := 𝓞 K) (K := K) (v := Q) x)) := by
    funext a
    simp only [finiteLocalEquiv, RingEquiv.trans_apply,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
    rfl
  rw [hfun]
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K'
    (finitePlaceEquiv e Q)).comp
    ((completionCongr_continuous e Q).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K Q))

theorem finiteLocalEquiv_valued (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K))
    (y : Q.adicCompletion K) :
    Valued.v (finiteLocalEquiv e Q y) = Valued.v y := by
  have hdense : DenseRange ((↑) : K → Q.adicCompletion K) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
    simpa using h
  have hcont1 : Continuous (fun y : Q.adicCompletion K => Valued.v (finiteLocalEquiv e Q y)) :=
    (Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K'
        (finitePlaceEquiv e Q))).comp (finiteLocalEquiv_continuous e Q)
  have hcont2 : Continuous (fun y : Q.adicCompletion K => Valued.v y) :=
    Valued.continuous_valuation_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K Q)
  have heq : (fun y : Q.adicCompletion K => Valued.v (finiteLocalEquiv e Q y)) =
      fun y => Valued.v y :=
    hdense.equalizer hcont1 hcont2 (by
      funext x
      rw [Function.comp_apply, Function.comp_apply, finiteLocalEquiv_coe,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
      exact valuation_mapRingEquiv' e Q x)
  exact congrFun heq y

theorem finiteLocalEquiv_localUnits (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K))
    (u : (Q.adicCompletion K)ˣ) :
    u ∈ Place.localUnits K (Place.ofFinite Q) ↔
      Units.map (finiteLocalEquiv e Q).toMonoidHom u ∈
        Place.localUnits K' (Place.ofFinite (finitePlaceEquiv e Q)) := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one,
    Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
  change Valued.v ((u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 ↔
    Valued.v (finiteLocalEquiv e Q ↑u) = 1
  rw [finiteLocalEquiv_valued]

/-- **The local algebra maps commute with the transport**: the square
`L_q ← K_Q → ...` is compatible with `(eK, eL)`.  This is the input for Mathlib's
`Algebra.norm_eq_of_equiv_equiv` in the comparison of the local norm maps. -/
theorem finiteLocalEquiv_adicCompletionMap
    {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
    [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq' : (finitePlaceEquiv eL q).asIdeal.LiesOver (finitePlaceEquiv eK Q).asIdeal)
    (x : Q.adicCompletion K) :
    finiteLocalEquiv eL q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
      Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
        (finitePlaceEquiv eL q) hq' (finiteLocalEquiv eK Q x) := by
  have hdense : DenseRange ((↑) : K → Q.adicCompletion K) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
    simpa using h
  have hfun := DenseRange.equalizer
    (f := algebraMap K (Q.adicCompletion K))
    (g := fun z => finiteLocalEquiv eL q
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq z))
    (h := fun z => Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
      (finitePlaceEquiv eL q) hq' (finiteLocalEquiv eK Q z))
    hdense
    ((finiteLocalEquiv_continuous eL q).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq))
    ((Commons.RingTheory.Henselian.adicCompletionMap_continuous (finitePlaceEquiv eK Q)
      (finitePlaceEquiv eL q) hq').comp (finiteLocalEquiv_continuous eK Q))
    (by
      funext y
      show finiteLocalEquiv eL q (Commons.RingTheory.Henselian.adicCompletionMap Q q hq
          (algebraMap K (Q.adicCompletion K) y)) =
        Commons.RingTheory.Henselian.adicCompletionMap (finitePlaceEquiv eK Q)
          (finitePlaceEquiv eL q) hq'
          (finiteLocalEquiv eK Q (algebraMap K (Q.adicCompletion K) y))
      have hcoe : algebraMap K (Q.adicCompletion K) y = (y : Q.adicCompletion K) := by
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp
      rw [hcoe]
      rw [Commons.RingTheory.Henselian.adicCompletionMap_apply,
        finiteLocalEquiv_coe eL q (algebraMap K L y), hcomp y,
        finiteLocalEquiv_coe eK Q y,
        Commons.RingTheory.Henselian.adicCompletionMap_apply])
  exact congrFun hfun x

/-! ## The infinite places -/

section Infinite

open NumberField

/-- The `WithAbs`-level transport of an infinite place. -/
noncomputable def withAbsCongr (e : K ≃+* K') (w : InfinitePlace K) :
    WithAbs w.1 ≃+* WithAbs (infinitePlaceEquiv e w).1 :=
  WithAbs.congr w.1 (infinitePlaceEquiv e w).1 (e : K ≃+* K')

theorem withAbsCongr_norm (e : K ≃+* K') (w : InfinitePlace K) (x : WithAbs w.1) :
    ‖withAbsCongr e w x‖ = ‖x‖ := by
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, withAbsCongr,
    WithAbs.congr_apply]
  show (infinitePlaceEquiv e w).1 (e x.ofAbs) = w.1 x.ofAbs
  rw [infinitePlaceEquiv_apply]
  show (w.comap (e.symm : K' →+* K)) (e x.ofAbs) = w.1 x.ofAbs
  rw [NumberField.InfinitePlace.comap_apply]
  show w.1 (e.symm (e x.ofAbs)) = w.1 x.ofAbs
  rw [RingEquiv.symm_apply_apply]

theorem withAbsCongr_isometry (e : K ≃+* K') (w : InfinitePlace K) :
    Isometry (withAbsCongr e w) :=
  AddMonoidHomClass.isometry_of_norm _ (withAbsCongr_norm e w)

theorem withAbsCongr_symm_isometry (e : K ≃+* K') (w : InfinitePlace K) :
    Isometry (withAbsCongr e w).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro y
  rw [← withAbsCongr_norm e w ((withAbsCongr e w).symm y), RingEquiv.apply_symm_apply]

/-- **The transport of an infinite local field along a ring equivalence of number fields.** -/
noncomputable def infiniteLocalEquiv (e : K ≃+* K') (w : InfinitePlace K) :
    w.Completion ≃+* (infinitePlaceEquiv e w).Completion :=
  (NumberField.InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (withAbsCongr e w)
        (withAbsCongr_isometry e w).continuous (withAbsCongr_symm_isometry e w).continuous).trans
      (NumberField.InfinitePlace.Completion.equiv (infinitePlaceEquiv e w)).symm)

theorem infiniteLocalEquiv_coe_withAbs (e : K ≃+* K') (w : InfinitePlace K)
    (y : WithAbs w.1) :
    infiniteLocalEquiv e w (y : w.Completion) =
      (withAbsCongr e w y : (infinitePlaceEquiv e w).Completion) := by
  rw [infiniteLocalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    NumberField.InfinitePlace.Completion.equiv_apply,
    NumberField.InfinitePlace.Completion.toCompletion_ofCompletion,
    UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe (withAbsCongr_isometry e w).uniformContinuous]
  rfl

theorem infiniteLocalEquiv_coe (e : K ≃+* K') (w : InfinitePlace K) (x : K) :
    infiniteLocalEquiv e w (x : w.Completion) =
      (e x : (infinitePlaceEquiv e w).Completion) := by
  rw [infiniteLocalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    NumberField.InfinitePlace.Completion.equiv_apply,
    NumberField.InfinitePlace.Completion.toCompletion_ofCompletion,
    UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe (withAbsCongr_isometry e w).uniformContinuous,
    withAbsCongr, WithAbs.congr_apply, WithAbs.ofAbs_toAbs]
  rfl

theorem infiniteLocalEquiv_algebraMap (e : K ≃+* K') (w : InfinitePlace K) (x : K) :
    infiniteLocalEquiv e w (algebraMap K w.Completion x) =
      algebraMap K' (infinitePlaceEquiv e w).Completion (e x) := by
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
    NumberField.InfinitePlace.Completion.algebraMap_apply, infiniteLocalEquiv_coe]

theorem infiniteLocalEquiv_continuous (e : K ≃+* K') (w : InfinitePlace K) :
    Continuous (infiniteLocalEquiv e w : w.Completion →
      (infinitePlaceEquiv e w).Completion) := by
  have hfun : (infiniteLocalEquiv e w : w.Completion →
      (infinitePlaceEquiv e w).Completion) = fun x =>
      NumberField.InfinitePlace.Completion.ofCompletion
        (UniformSpace.Completion.map (withAbsCongr e w :
          WithAbs w.1 → WithAbs (infinitePlaceEquiv e w).1)
          (NumberField.InfinitePlace.Completion.toCompletion x)) := by
    funext a
    simp only [infiniteLocalEquiv, RingEquiv.trans_apply,
      NumberField.InfinitePlace.Completion.equiv_apply,
      UniformSpace.Completion.mapRingEquiv_apply]
    rfl
  rw [hfun]
  exact (NumberField.InfinitePlace.Completion.continuous_ofCompletion
    (infinitePlaceEquiv e w)).comp
    (UniformSpace.Completion.continuous_map.comp
      (NumberField.InfinitePlace.Completion.continuous_toCompletion w))

theorem infiniteLocalEquiv_localUnits (e : K ≃+* K') (w : InfinitePlace K)
    (u : (w.Completion)ˣ) :
    u ∈ Place.localUnits K (Place.ofInfinite w) ↔
      Units.map (infiniteLocalEquiv e w).toMonoidHom u ∈
        Place.localUnits K' (Place.ofInfinite (infinitePlaceEquiv e w)) := by
  rw [Place.localUnits_ofInfinite, Place.localUnits_ofInfinite]
  exact iff_of_true trivial trivial

/-- At the level of the `WithAbs`-copies, the transport commutes with the algebra maps. -/
theorem withAbsCongr_algebraMap {L L' : Type*} [Field L] [NumberField L] [Field L']
    [NumberField L'] [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    [(infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v)] (a : WithAbs v.1) :
    withAbsCongr eL w (algebraMap (WithAbs v.1) (WithAbs w.1) a) =
      algebraMap (WithAbs (infinitePlaceEquiv eK v).1)
        (WithAbs (infinitePlaceEquiv eL w).1) (withAbsCongr eK v a) := by
  rw [withAbsCongr, WithAbs.congr_apply, WithAbs.ofAbs_algebraMap,
    WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
  congr 1
  exact hcomp a.ofAbs

/-- **The archimedean case of the equivariance**: the infinite local field transport intertwines
the completion maps. -/
theorem infiniteLocalEquiv_completionMap {L L' : Type*} [Field L] [NumberField L] [Field L']
    [NumberField L'] [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    [(infinitePlaceEquiv eL w).LiesOver (infinitePlaceEquiv eK v)] (x : v.Completion) :
    infiniteLocalEquiv eL w (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
      NumberField.LiesOver.completionMap (v := infinitePlaceEquiv eK v)
        (w := infinitePlaceEquiv eL w) (infiniteLocalEquiv eK v x) := by
  induction x using NumberField.InfinitePlace.Completion.induction_on
  · exact isClosed_eq
      ((infiniteLocalEquiv_continuous eL w).comp
        (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)))
      ((NumberField.LiesOver.continuous_completionMap (v := infinitePlaceEquiv eK v)
        (w := infinitePlaceEquiv eL w)).comp (infiniteLocalEquiv_continuous eK v))
  · rename_i a
    rw [NumberField.LiesOver.completionMap_coe (v := v) (w := w),
      infiniteLocalEquiv_coe_withAbs eL w,
      withAbsCongr_algebraMap eK eL hcomp v w a,
      infiniteLocalEquiv_coe_withAbs eK v,
      NumberField.LiesOver.completionMap_coe (v := infinitePlaceEquiv eK v)
        (w := infinitePlaceEquiv eL w)]

end Infinite

end NK.GlobalCFTdeep.HasseIndex
