import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# The map between adic completions induced by a prime lying over

If `L / K` is an extension of number fields, `Q` is a height-one prime ideal of the ring of
integers of `K` and `q` is a height-one prime ideal of the ring of integers of `L` lying over
`Q`, then the inclusion `K → L` extends to a ring homomorphism between the corresponding
`Q`-adic completion of `K` and the `q`-adic completion of `L`.
-/

open scoped NumberField

set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain.HeightOneSpectrum

namespace Commons.RingTheory.Henselian

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- When `q` lies over `Q`, the algebra map between the `WithVal`-spaces (i.e. `K` and `L`
equipped with the `Q`-adic and `q`-adic topologies) is uniformly continuous. -/
lemma adicValuedMap_uniformContinuous
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    UniformContinuous (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L))) := by
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  exact uniformContinuous_algebraMap_liesOver (A := 𝓞 K) (B := 𝓞 L) K L Q q

/-- The algebra map between the `WithVal`-spaces, seen as a continuous ring homomorphism. -/
lemma withValMap_continuous
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Continuous (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L))) :=
  (adicValuedMap_uniformContinuous Q q hq).continuous

/-- The map between the underlying uniform-space completions of the `WithVal`-spaces. -/
lemma completionMap_apply
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : K) :
    (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
        (withValMap_continuous Q q hq) (x : (Q.valuation K).Completion)) =
      (algebraMap K L x : (q.valuation L).Completion) := by
  rw [show (x : (Q.valuation K).Completion) =
      ((WithVal.toVal (Q.valuation K) x : WithVal (Q.valuation K)) : (Q.valuation K).Completion)
      from rfl]
  rw [UniformSpace.Completion.mapRingHom_coe (withValMap_continuous Q q hq)]
  first | rfl | (rw [WithVal.equiv_symm_apply]; congr 1)

/-- The ring homomorphism `Q.adicCompletion K →+* q.adicCompletion L` induced by the inclusion
`K → L`, when the prime `q` of `𝓞 L` lies over the prime `Q` of `𝓞 K`. -/
noncomputable def adicCompletionMap
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Q.adicCompletion K →+* q.adicCompletion L :=
  ((adicCompletion.equiv L q).symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
        (withValMap_continuous Q q hq))).comp
    (adicCompletion.equiv K Q).toRingHom

/-- The map `adicCompletionMap` extends `algebraMap K L`, i.e. it makes the diagram
```
K → L
↓   ↓
K_Q → L_q
```
commute. -/
lemma adicCompletionMap_apply
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : K) :
    adicCompletionMap Q q hq (x : Q.adicCompletion K) = (algebraMap K L x : q.adicCompletion L) := by
  let eK : Q.adicCompletion K ≃+* (Q.valuation K).Completion := adicCompletion.equiv K Q
  let eL : q.adicCompletion L ≃+* (q.valuation L).Completion := adicCompletion.equiv L q
  let g : (Q.valuation K).Completion →+* (q.valuation L).Completion :=
    UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (Q.valuation K)) (WithVal (q.valuation L)))
      (withValMap_continuous Q q hq)
  change (eL.symm.toRingHom.comp g).comp eK.toRingHom (x : Q.adicCompletion K) =
    (algebraMap K L x : q.adicCompletion L)
  apply adicCompletion.ext
  have hLHS : (((eL.symm.toRingHom.comp g).comp eK.toRingHom)
        (x : Q.adicCompletion K)).toCompletion =
      g (x : (Q.valuation K).Completion) := by
    change eL (eL.symm (g (eK (x : Q.adicCompletion K)))) = g (x : (Q.valuation K).Completion)
    rw [RingEquiv.apply_symm_apply]
    change g ((x : (Q.valuation K).Completion)) = g (x : (Q.valuation K).Completion)
    rfl
  have hRHS : ((algebraMap K L x : q.adicCompletion L)).toCompletion =
      (algebraMap K L x : (q.valuation L).Completion) := rfl
  rw [hLHS, hRHS]
  exact completionMap_apply Q q hq x

theorem adicCompletionMap_liesOver
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ φ : Q.adicCompletion K →+* q.adicCompletion L,
      ∀ x : K, φ (x : Q.adicCompletion K) = (algebraMap K L x : q.adicCompletion L) := by
  exact ⟨adicCompletionMap Q q hq, adicCompletionMap_apply Q q hq⟩

end Commons.RingTheory.Henselian