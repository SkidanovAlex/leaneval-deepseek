import Mathlib
import Submission.NK.Mine.CompletionAPI
import Submission.NK.NumberTheory.NumberField.Completion.place_transport
import Submission.NK.NumberTheory.NumberField.Completion.completion_transport
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal

/-!
# The local isomorphism induced by a global one

Let `e : L₁ ≃ₐ[K] L₂` be an isomorphism of number fields over `K`, let `p` be a finite place of
`K`, and let `q₁`, `q₂` be finite places of `L₁`, `L₂` above `p`.  If the valuation subring of
`q₂` is the transport of the valuation subring of `q₁` along `e` — i.e.
`V_{q₂} = e(V_{q₁})` — then `e` is an isometry of the two valued fields and therefore induces an
isomorphism of the completed fields `(L₁)_{q₁} ≃ (L₂)_{q₂}`.  Since `e` is a `K`-algebra map, this
isomorphism is one of `K_p`-algebras.

This is the "uniqueness of the local isomorphism" step of the local--global dictionary used in
the Neukirch--Uchida theorem (CoNF XII, §12.1).
-/

open scoped WithZero

set_option linter.style.haveILetI false

namespace NK.NumberTheory.NumberField.Completion

/-- **The local isomorphism induced by a global one.**  Let `e : L₁ ≃ₐ[K] L₂` be an isomorphism
of number fields over `K` and let `q₁`, `q₂` be places of `L₁`, `L₂` above the place `p` of `K`.
If the valuation subring of `q₂` is the image of that of `q₁` under `e`, then `e` induces an
isomorphism `(L₁)_{q₁} ≃ (L₂)_{q₂}` of `K_p`-algebras between the completed fields.

This is the step "a global isomorphism matching the places is local" of the local–global
dictionary used in the Neukirch–Uchida theorem (CoNF XII, §12.1). -/
theorem exists_algEquiv_adicCompletion_of_valuationSubringAtPrime_comap {K L1 L2 : Type*}
    [Field K] [NumberField K] [Field L1] [NumberField L1] [Algebra K L1]
    [Field L2] [NumberField L2] [Algebra K L2]
    [FiniteDimensional K L1] [FiniteDimensional K L2]
    (e : L1 ≃ₐ[K] L2)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q1 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L1))
    (q2 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L2))
    (h1 : q1.asIdeal.LiesOver p.asIdeal) (h2 : q2.asIdeal.LiesOver p.asIdeal)
    (hV : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L2 q2 =
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L1 q1).comap
        (e.symm : L2 →+* L1)) :
    letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra p q1 h1
    letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra p q2 h2
    Nonempty (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1 ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
      IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) := by
  classical
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra p q1 h1
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra p q2 h2
  -- ## The valuation attached to `q₁`, `q₂`, and the transport of the latter along `e`
  let v1 : Valuation L1 ℤᵐ⁰ := q1.valuation L1
  let v2 : Valuation L2 ℤᵐ⁰ := q2.valuation L2
  let w : Valuation L2 ℤᵐ⁰ := v1.comap (e.symm : L2 →+* L1)
  have hwe : ∀ y : L1, w (e y) = v1 y := by
    intro y
    change v1 (e.symm (e y)) = v1 y
    rw [e.symm_apply_apply]
  -- ## `w` and `v₂` have the same valuation subring
  have hVsub : w.valuationSubring = v2.valuationSubring := by
    have h1' : v2.valuationSubring = (v1.valuationSubring).comap (e.symm : L2 →+* L1) := by
      have hh := hV
      simpa only [v1, v2,
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] using hh
    rw [h1']
    ext y
    have hwy : w y = v1 ((e.symm : L2 →+* L1) y) := rfl
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, hwy]
  have hv : w.IsEquiv v2 := (Valuation.isEquiv_iff_valuationSubring w v2).mpr hVsub
  -- ## The isometries at the `WithVal` level
  let E : WithVal v1 ≃+* WithVal w := WithVal.congr v1 w (e : L1 ≃+* L2)
  let G : WithVal w ≃+* WithVal v2 := WithVal.congr w v2 (RingEquiv.refl L2)
  let F : WithVal v1 ≃+* WithVal v2 := E.trans G
  have hEval : ∀ x : WithVal v1, WithVal.valuation w (E x) = WithVal.valuation v1 x := by
    intro x
    simp only [E, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal]
    exact hwe x.ofVal
  have hcof : ∀ γ : ℤᵐ⁰, 0 < γ → ∃ x : WithVal v1,
      0 < WithVal.valuation v1 x ∧ WithVal.valuation v1 x ≤ γ := by
    intro γ hγ
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L1 q1 γ
    refine ⟨WithVal.toVal v1 y, ?_, le_of_eq ?_⟩
    · rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ
    · rw [WithVal.valuation_apply_eq_ofVal, hy]
  have hEuc : UniformContinuous (E : WithVal v1 → WithVal w) :=
    Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      (E : WithVal v1 →+* WithVal w) hEval hcof
  have hEval' : ∀ x : WithVal w, WithVal.valuation v1 (E.symm x) = WithVal.valuation w x := by
    intro x
    rw [← hEval (E.symm x), RingEquiv.apply_symm_apply]
  have hcof' : ∀ γ : ℤᵐ⁰, 0 < γ → ∃ x : WithVal w,
      0 < WithVal.valuation w x ∧ WithVal.valuation w x ≤ γ := by
    intro γ hγ
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective L1 q1 γ
    refine ⟨WithVal.toVal w (e y), ?_, le_of_eq ?_⟩
    · rw [WithVal.valuation_apply_eq_ofVal, hwe y, hy]; exact hγ
    · rw [WithVal.valuation_apply_eq_ofVal, hwe y, hy]
  have hEuc' : UniformContinuous (E.symm : WithVal w → WithVal v1) :=
    Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      (E.symm : WithVal w →+* WithVal v1) hEval' hcof'
  have hGuc : UniformContinuous (G : WithVal w → WithVal v2) := hv.uniformContinuous_congr
  have hGuc' : UniformContinuous (G.symm : WithVal v2 → WithVal w) :=
    hv.symm.uniformContinuous_congr
  have hFuc : UniformContinuous (F : WithVal v1 → WithVal v2) := by
    have h := hGuc.comp hEuc
    exact h
  have hFuc' : UniformContinuous (F.symm : WithVal v2 → WithVal v1) := by
    have h := hEuc'.comp hGuc'
    exact h
  -- ## The induced ring equivalence of the completions
  let Ψ : (v1).Completion ≃+* (v2).Completion :=
    UniformSpace.Completion.mapRingEquiv F hFuc.continuous hFuc'.continuous
  let Φ : q1.adicCompletion L1 ≃+* q2.adicCompletion L2 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L1 q1).trans
      (Ψ.trans (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L2 q2).symm)
  have hΨ_coe : ∀ z : WithVal v1, Ψ ((z : (v1).Completion)) = ((F z : WithVal v2) : (v2).Completion) := by
    intro z
    change UniformSpace.Completion.mapRingEquiv F hFuc.continuous hFuc'.continuous
      ((z : WithVal v1) : (v1).Completion) = ((F z : WithVal v2) : (v2).Completion)
    rw [UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.map_coe hFuc]
  have hF_coe : ∀ z : WithVal v1, F z = WithVal.toVal v2 (e z.ofVal) := by
    intro z
    change G (E z) = WithVal.toVal v2 (e z.ofVal)
    rw [show E z = WithVal.toVal w (e z.ofVal) from WithVal.congr_apply v1 w (e : L1 ≃+* L2) z]
    simp only [G, WithVal.congr_apply, RingEquiv.refl_apply]
  have hΦ_alg : ∀ y : L1, Φ ((y : q1.adicCompletion L1)) = ((e y : L2) : q2.adicCompletion L2) := by
    intro y
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext L2 q2
    have hL : (Φ ((y : q1.adicCompletion L1))).toCompletion
        = ((WithVal.toVal v2 (e y) : WithVal v2) : (v2).Completion) := by
      rw [show (Φ ((y : q1.adicCompletion L1))).toCompletion
        = Ψ (↑((WithVal.equiv v1).symm y) : (v1).Completion) from rfl]
      rw [hΨ_coe, WithVal.equiv_symm_apply, hF_coe]
    have hR : (((e y : L2) : q2.adicCompletion L2)).toCompletion
        = ((WithVal.toVal v2 (e y) : WithVal v2) : (v2).Completion) := rfl
    exact hL.trans hR.symm
  -- ## Continuity and the `K_p`-linearity of `Φ`
  have hΨcont : Continuous (Ψ : (v1).Completion → (v2).Completion) := by
    have hfun : (Ψ : (v1).Completion → (v2).Completion) =
        UniformSpace.Completion.map (F : WithVal v1 → WithVal v2) :=
      funext fun a => UniformSpace.Completion.mapRingEquiv_apply F hFuc.continuous hFuc'.continuous a
    rw [hfun]
    exact UniformSpace.Completion.continuous_map
  have hΦcont : Continuous (Φ : q1.adicCompletion L1 → q2.adicCompletion L2) := by
    have hfun : (Φ : q1.adicCompletion L1 → q2.adicCompletion L2) = fun x =>
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L2 q2).symm
          (Ψ ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L1 q1) x)) := rfl
    rw [hfun]
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L2 q2).comp
      (hΨcont.comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion L1 q1))
  have hmap1 : (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K p →+*
        IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1)
      = Commons.RingTheory.Henselian.adicCompletionMap p q1 h1 :=
    RingHom.algebraMap_toAlgebra _
  have hmap2 : (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K p →+*
        IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2)
      = Commons.RingTheory.Henselian.adicCompletionMap p q2 h2 :=
    RingHom.algebraMap_toAlgebra _
  have hlin : ∀ c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
      Φ (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) c) =
        algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) c := by
    have hf : Continuous (fun c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
        Φ (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) c)) := by
      refine hΦcont.comp ?_
      rw [hmap1]
      exact Commons.RingTheory.Henselian.adicCompletionMap_continuous p q1 h1
    have hg : Continuous (fun c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
        algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) c) := by
      rw [hmap2]
      exact Commons.RingTheory.Henselian.adicCompletionMap_continuous p q2 h2
    have hdense : DenseRange
        (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)) :=
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (R := NumberField.RingOfIntegers K) K p
    have hEq : (fun c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
        Φ (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion L1 q1) c)) =
        fun c : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p =>
          algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion L2 q2) c :=
      DenseRange.equalizer hdense hf hg (funext fun x => by
        simp only [Function.comp_apply]
        rw [hmap1, hmap2]
        rw [show Commons.RingTheory.Henselian.adicCompletionMap p q1 h1
            (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x)
            = (algebraMap K L1 x : q1.adicCompletion L1) from
          Commons.RingTheory.Henselian.adicCompletionMap_apply p q1 h1 x]
        rw [show Commons.RingTheory.Henselian.adicCompletionMap p q2 h2
            (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x)
            = (algebraMap K L2 x : q2.adicCompletion L2) from
          Commons.RingTheory.Henselian.adicCompletionMap_apply p q2 h2 x]
        rw [hΦ_alg (algebraMap K L1 x), AlgEquiv.commutes e x])
    intro c
    exact congrFun hEq c
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) hlin⟩

end NK.NumberTheory.NumberField.Completion
