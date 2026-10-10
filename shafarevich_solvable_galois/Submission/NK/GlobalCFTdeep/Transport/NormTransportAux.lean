import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Transport.liesOver_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.valuation_mapRingEquiv

/-!
# The local field transport along a ring equivalence of number fields

For a ring equivalence `e : K ≃+* K'` of number fields and a place `v` of `K` we construct a ring
equivalence of local fields

`localFieldIso e v : K_v ≃+* K'_{placeEquiv e v}`

satisfying the three properties that the transport of the idèle group and of the local norms needs:

* compatibility with the structure maps `algebraMap K K_v`;
* preservation of the local units `𝒪_vˣ`;
* continuity.

The three properties together are enough for all downstream arguments: in particular the
commutation with the local algebra maps `K_v → L_w` (proved in the companion file
`NormTransportLocal`) is a density argument which only uses these properties, never the
construction of the isomorphism.

The construction of the isomorphism is a copy of the `K`-automorphism case
(`NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul`): at a nonarchimedean place it is the
lift to the completions of the `WithVal`-level isomorphism `WithVal.congr`, at an archimedean place
the lift of the `WithAbs`-level isomorphism `WithAbs.congr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct WithZero WithZeroTopology
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

namespace NormTransport

open NK.GlobalCFT

/-! ## Existence of the local field transport -/

section Exists

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- **Existence of the transport of a nonarchimedean local field along a ring equivalence**,
together with the four properties needed downstream. -/
theorem localFieldIsoFinite_exists (e : K ≃+* K') (Q : HeightOneSpectrum (𝓞 K)) :
    ∃ Φ : Q.adicCompletion K ≃+* (finitePlaceEquiv e Q).adicCompletion K',
      (∀ x : K, Φ (algebraMap K (Q.adicCompletion K) x) =
        algebraMap K' ((finitePlaceEquiv e Q).adicCompletion K') (e x)) ∧
      (∀ u : (Q.adicCompletion K)ˣ,
        u ∈ Place.localUnits K (Place.ofFinite Q) ↔
          Units.map Φ.toMonoidHom u ∈
            Place.localUnits K' (Place.ofFinite (finitePlaceEquiv e Q))) ∧
      Continuous Φ := by
  classical
  set Q' : HeightOneSpectrum (𝓞 K') := finitePlaceEquiv e Q with hQ'
  have hval : ∀ x : K, Q'.valuation K' (e x) = Q.valuation K x :=
    fun x => NK.GlobalCFTdeep.Transport.valuation_mapRingEquiv e Q x
  let F : WithVal (Q.valuation K) ≃+* WithVal (Q'.valuation K') :=
    WithVal.congr (Q.valuation K) (Q'.valuation K') (e : K ≃+* K')
  have hFa : ∀ x : WithVal (Q.valuation K),
      WithVal.valuation (Q'.valuation K') (F x) = WithVal.valuation (Q.valuation K) x := by
    intro x
    simp only [F, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal, hval]
  have hFb : ∀ x : WithVal (Q'.valuation K'),
      WithVal.valuation (Q.valuation K) (F.symm x) = WithVal.valuation (Q'.valuation K') x := by
    intro x
    simp only [F, WithVal.congr_symm, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal]
    rw [← hval (e.symm x.ofVal), RingEquiv.apply_symm_apply]
  have hcof : ∀ γ : ℤᵐ⁰, 0 < γ → ∃ x : WithVal (Q.valuation K),
      0 < WithVal.valuation (Q.valuation K) x ∧ WithVal.valuation (Q.valuation K) x ≤ γ := by
    intro γ hγ
    obtain ⟨y, hy⟩ := HeightOneSpectrum.valuation_surjective K Q γ
    exact ⟨WithVal.toVal (Q.valuation K) y,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩
  have hcof' : ∀ γ : ℤᵐ⁰, 0 < γ → ∃ x : WithVal (Q'.valuation K'),
      0 < WithVal.valuation (Q'.valuation K') x ∧ WithVal.valuation (Q'.valuation K') x ≤ γ := by
    intro γ hγ
    obtain ⟨y, hy⟩ := HeightOneSpectrum.valuation_surjective K' Q' γ
    exact ⟨WithVal.toVal (Q'.valuation K') y,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩
  have hFuc : UniformContinuous (F : WithVal (Q.valuation K) → WithVal (Q'.valuation K')) :=
    Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      F.toRingHom hFa hcof
  have hFuc' : UniformContinuous (F.symm : WithVal (Q'.valuation K') → WithVal (Q.valuation K)) :=
    Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      F.symm.toRingHom hFb hcof'
  let Ψ : (Q.valuation K).Completion ≃+* (Q'.valuation K').Completion :=
    UniformSpace.Completion.mapRingEquiv F hFuc.continuous hFuc'.continuous
  let Φ : Q.adicCompletion K ≃+* Q'.adicCompletion K' :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q).trans
      (Ψ.trans (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K' Q').symm)
  have hΨ_app : ∀ y : K, Ψ (y : (Q.valuation K).Completion) =
      (e y : (Q'.valuation K').Completion) := by
    intro y
    change UniformSpace.Completion.mapRingEquiv F hFuc.continuous hFuc'.continuous
      (y : (Q.valuation K).Completion) = (e y : (Q'.valuation K').Completion)
    rw [UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.map_coe hFuc]
    try rw [WithVal.equiv_symm_apply]
    have hFapp : F (WithVal.toVal (Q.valuation K) y) =
        WithVal.toVal (Q'.valuation K') (e y) := by
      simp only [F, WithVal.congr_apply]
    rw [hFapp]
    try rfl
  have hΦ_coe : ∀ x : K, Φ (x : Q.adicCompletion K) = (e x : Q'.adicCompletion K') := by
    intro x
    change (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K' Q').symm
        (Ψ ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q)
          (x : Q.adicCompletion K))) = (e x : Q'.adicCompletion K')
    rw [show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q)
        (x : Q.adicCompletion K) = (x : (Q.valuation K).Completion) from rfl, hΨ_app x]
    rfl
  have hcoe : ∀ x : K, algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    intro x
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  have hcoe' : ∀ y : K', algebraMap K' (Q'.adicCompletion K') y = (y : Q'.adicCompletion K') := by
    intro y
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  have hΦ_alg : ∀ x : K, Φ (algebraMap K (Q.adicCompletion K) x) =
      algebraMap K' (Q'.adicCompletion K') (e x) := by
    intro x
    rw [hcoe x, hcoe' (e x), hΦ_coe x]
  have hΨcont : Continuous (Ψ : (Q.valuation K).Completion → (Q'.valuation K').Completion) := by
    have hfun : (Ψ : (Q.valuation K).Completion → (Q'.valuation K').Completion) =
        UniformSpace.Completion.map (F : WithVal (Q.valuation K) → WithVal (Q'.valuation K')) :=
      funext fun a =>
        UniformSpace.Completion.mapRingEquiv_apply F hFuc.continuous hFuc'.continuous a
    rw [hfun]
    exact UniformSpace.Completion.continuous_map
  have hΦcont : Continuous (Φ : Q.adicCompletion K → Q'.adicCompletion K') := by
    have hfun : (Φ : Q.adicCompletion K → Q'.adicCompletion K') = fun x =>
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
          (R := 𝓞 K') (K := K') (v := Q')
          (Ψ (IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion
            (R := 𝓞 K) (K := K) (v := Q) x)) := by
      funext a
      simp only [Φ, RingEquiv.trans_apply,
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
      rfl
    rw [hfun]
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K' Q').comp
      (hΨcont.comp (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K Q))
  have hdense : DenseRange ((↑) : K → Q.adicCompletion K) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at h
    simpa using h
  have hΦval : ∀ y : Q.adicCompletion K, Valued.v (Φ y) = Valued.v y := by
    intro y
    have hcont1 : Continuous (fun y : Q.adicCompletion K => Valued.v (Φ y)) :=
      (Valued.continuous_valuation_of_surjective
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K' Q')).comp hΦcont
    have hcont2 : Continuous (fun y : Q.adicCompletion K => Valued.v y) :=
      Valued.continuous_valuation_of_surjective
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K Q)
    have heq : (fun y : Q.adicCompletion K => Valued.v (Φ y)) = fun y => Valued.v y :=
      hdense.equalizer hcont1 hcont2 (by
        funext x
        rw [Function.comp_apply, Function.comp_apply, hΦ_coe x,
          IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe,
          IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
        exact hval x)
    exact congrFun heq y
  refine ⟨Φ, hΦ_alg, ?_, hΦcont⟩
  intro u
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one,
    Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
  change Valued.v ((u : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) = 1 ↔
    Valued.v (Φ ↑u) = 1
  rw [hΦval (u : Q.adicCompletion K)]

/-- **Existence of the transport of an archimedean local field along a ring equivalence**,
together with the four properties needed downstream. -/
theorem localFieldIsoInfinite_exists (e : K ≃+* K') (w : NumberField.InfinitePlace K) :
    ∃ Φ : w.Completion ≃+* (infinitePlaceEquiv e w).Completion,
      (∀ x : K, Φ (algebraMap K w.Completion x) =
        algebraMap K' (infinitePlaceEquiv e w).Completion (e x)) ∧
      (∀ u : (w.Completion)ˣ,
        u ∈ Place.localUnits K (Place.ofInfinite w) ↔
          Units.map Φ.toMonoidHom u ∈
            Place.localUnits K' (Place.ofInfinite (infinitePlaceEquiv e w))) ∧
      Continuous Φ := by
  set w' := infinitePlaceEquiv e w with hw'
  let f : WithAbs w.1 ≃+* WithAbs w'.1 := WithAbs.congr w.1 w'.1 e
  have hf_norm : ∀ x : WithAbs w.1, ‖f x‖ = ‖x‖ := by
    intro x
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    show w'.1 (e x.ofAbs) = w.1 x.ofAbs
    rw [hw', infinitePlaceEquiv_apply]
    show (w.comap (e.symm : K' →+* K)) (e x.ofAbs) = w.1 x.ofAbs
    rw [NumberField.InfinitePlace.comap_apply]
    show w.1 (e.symm (e x.ofAbs)) = w.1 x.ofAbs
    rw [RingEquiv.symm_apply_apply]
  have hfiso : Isometry (⇑f) := AddMonoidHomClass.isometry_of_norm f hf_norm
  have hf : Continuous (⇑f) := hfiso.continuous
  have hfiso' : Isometry (⇑f.symm) := by
    apply AddMonoidHomClass.isometry_of_norm
    intro y
    rw [← hf_norm (f.symm y), RingEquiv.apply_symm_apply]
  have hfs : Continuous (⇑f.symm) := hfiso'.continuous
  refine ⟨(NumberField.InfinitePlace.Completion.equiv w).trans
      ((UniformSpace.Completion.mapRingEquiv f hf hfs).trans
        (NumberField.InfinitePlace.Completion.equiv w').symm), ?_, ?_, ?_⟩
  · intro x
    have hx : algebraMap K w.Completion x
        = NumberField.InfinitePlace.Completion.ofCompletion
            (↑(WithAbs.toAbs w.1 x) : (w.1).Completion) := by
      rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
    rw [hx, RingEquiv.trans_apply, RingEquiv.trans_apply,
      NumberField.InfinitePlace.Completion.equiv_apply,
      NumberField.InfinitePlace.Completion.toCompletion_ofCompletion,
      UniformSpace.Completion.mapRingEquiv_apply,
      UniformSpace.Completion.map_coe hfiso.uniformContinuous,
      WithAbs.congr_apply, WithAbs.ofAbs_toAbs]
    rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
    rfl
  · intro u
    rw [Place.localUnits_ofInfinite, Place.localUnits_ofInfinite]
    simp
  · have h1 : Continuous (NumberField.InfinitePlace.Completion.equiv w) := by
      change Continuous (NumberField.InfinitePlace.Completion.toCompletion (v := w))
      exact NumberField.InfinitePlace.Completion.continuous_toCompletion w
    have h3 : Continuous (NumberField.InfinitePlace.Completion.equiv w').symm := by
      change Continuous (NumberField.InfinitePlace.Completion.ofCompletion (v := w'))
      exact NumberField.InfinitePlace.Completion.continuous_ofCompletion w'
    have h2 : Continuous (UniformSpace.Completion.mapRingEquiv f hf hfs) := by
      rw [show ⇑(UniformSpace.Completion.mapRingEquiv f hf hfs) =
          UniformSpace.Completion.map (⇑f) from by
        funext a; rw [UniformSpace.Completion.mapRingEquiv_apply]]
      exact UniformSpace.Completion.continuous_map
    have hfun : ⇑((NumberField.InfinitePlace.Completion.equiv w).trans
        ((UniformSpace.Completion.mapRingEquiv f hf hfs).trans
          (NumberField.InfinitePlace.Completion.equiv w').symm)) =
        fun x => (NumberField.InfinitePlace.Completion.equiv w').symm
          (UniformSpace.Completion.mapRingEquiv f hf hfs
            ((NumberField.InfinitePlace.Completion.equiv w) x)) := by
      funext x
      simp only [RingEquiv.trans_apply]
    rw [hfun]
    exact h3.comp (h2.comp h1)

end Exists

/-! ## The transport of the local field and its properties -/

section Combined

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- **The transport of the local field at a place along a ring equivalence of number fields.** -/
noncomputable def localFieldIso (e : K ≃+* K') (v : Place K) :
    Place.localField K v ≃+* Place.localField K' (placeEquiv e v) :=
  match v with
  | Sum.inl w => Classical.choose (localFieldIsoInfinite_exists e w)
  | Sum.inr Q => Classical.choose (localFieldIsoFinite_exists e Q)

theorem localFieldIso_algebraMap (e : K ≃+* K') (v : Place K) (x : K) :
    localFieldIso e v (algebraMap K (Place.localField K v) x) =
      algebraMap K' (Place.localField K' (placeEquiv e v)) (e x) := by
  cases v with
  | inl w => exact (Classical.choose_spec (localFieldIsoInfinite_exists e w)).1 x
  | inr Q => exact (Classical.choose_spec (localFieldIsoFinite_exists e Q)).1 x

theorem localFieldIso_localUnits (e : K ≃+* K') (v : Place K)
    (u : (Place.localField K v)ˣ) :
    u ∈ Place.localUnits K v ↔
      Units.map (localFieldIso e v).toMonoidHom u ∈
        Place.localUnits K' (placeEquiv e v) := by
  cases v with
  | inl w => exact (Classical.choose_spec (localFieldIsoInfinite_exists e w)).2.1 u
  | inr Q => exact (Classical.choose_spec (localFieldIsoFinite_exists e Q)).2.1 u

theorem localFieldIso_continuous (e : K ≃+* K') (v : Place K) :
    Continuous (localFieldIso e v) := by
  cases v with
  | inl w => exact (Classical.choose_spec (localFieldIsoInfinite_exists e w)).2.2
  | inr Q => exact (Classical.choose_spec (localFieldIsoFinite_exists e Q)).2.2

end Combined

end NormTransport

end NK.GlobalCFTdeep.Transport
