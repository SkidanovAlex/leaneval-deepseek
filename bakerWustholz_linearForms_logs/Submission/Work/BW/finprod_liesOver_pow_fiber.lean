import Mathlib
import Submission.Work.BW.finprod_mem_eq_fintype_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

open NumberField

/-- **Fiber of finite places.** The finite places of `K` lying above a finite place `w` of an
intermediate field `F ⊆ K` correspond, via `v ↦ v.maximalIdeal.asIdeal`, exactly to the prime
ideals of `𝓞 K` lying over `w.maximalIdeal`, i.e. to `(w.maximalIdeal.asIdeal).primesOver (𝓞 K)`. -/
theorem liesOver_fiber_bijOn {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (w : FinitePlace F) :
    Set.BijOn (fun v : FinitePlace K => v.maximalIdeal.asIdeal)
      {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal}
      ((w.maximalIdeal.asIdeal).primesOver (𝓞 K)) := by
  classical
  have hp_ne_bot : w.maximalIdeal.asIdeal ≠ ⊥ := w.maximalIdeal.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact ⟨v.maximalIdeal.isPrime, hv⟩
  · intro v₁ _ v₂ _ h
    rw [← FinitePlace.mk_maximalIdeal v₁, ← FinitePlace.mk_maximalIdeal v₂,
      FinitePlace.mk_eq_iff]
    exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr h
  · intro Q hQ
    have hQp : Q.IsPrime := Ideal.primesOver.isPrime _ ⟨Q, hQ⟩
    have hQl : Q.LiesOver w.maximalIdeal.asIdeal := Ideal.primesOver.liesOver _ ⟨Q, hQ⟩
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp_ne_bot hQ
    refine ⟨FinitePlace.mk (⟨Q, hQp, hQne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ?_, ?_⟩
    · show (FinitePlace.mk (⟨Q, hQp, hQne⟩ :
        IsDedekindDomain.HeightOneSpectrum (𝓞 K))).maximalIdeal.asIdeal.LiesOver
          w.maximalIdeal.asIdeal
      rw [FinitePlace.maximalIdeal_mk]
      exact hQl
    · show (FinitePlace.mk (⟨Q, hQp, hQne⟩ :
        IsDedekindDomain.HeightOneSpectrum (𝓞 K))).maximalIdeal.asIdeal = Q
      rw [FinitePlace.maximalIdeal_mk]

/-- **Finite places.** The finite places of `K` lying above a finite place `w` of `F`
(`ℚ ⊆ F ⊆ K`), weighted by their local degree `e_v * f_v`, multiply up to the `[K : F]`-th power
of `A`.

Suggested route: `{v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal}`
is the image of `(w.maximalIdeal.asIdeal).primesOver (𝓞 K)` under `FinitePlace.mk` (bijection via
`FinitePlace.mk_eq_iff`, `FinitePlace.maximalIdeal_mk`), so
`∏ᶠ v ∈ {…}, A ^ (…) = ∏ P : (w.maximalIdeal.asIdeal).primesOver (𝓞 K), A ^ (e P * f P)`
(`finprod_mem_eq_of_bijOn`, `finprod_mem_eq_toFinset_prod`, then it is a `Fintype` sum:
`Set.Finite.fintype` from `IsDedekindDomain.primesOver_finite` / the instance in
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`, available once `p.IsMaximal` is provided
by `Ideal.IsPrime.isMaximal p.isPrime p.ne_bot`). Then
`Finset.prod_pow_eq_pow_sum` turns it into `A ^ ∑ P, e P * f P`, and
`Ideal.sum_ramification_inertia_eq_finrank` (Mathlib, `RingTheory/RamificationInertia/Basic.lean`)
gives `∑ P, P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = Module.finrank (𝓞 F) (𝓞 K)`, while
`IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K` identifies that with `Module.finrank F K`.
NOTE: this statement deliberately has NO dependency on `Submission.Work.BW.logHeight_intermediate`
(do not import that module: its file imports this one's sibling). -/
theorem finprod_liesOver_pow_fiber {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (w : FinitePlace F) (A : ℝ) :
    ∏ᶠ v ∈ {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal},
        A ^ (v.maximalIdeal.asIdeal.ramificationIdx (𝓞 F) *
          v.maximalIdeal.asIdeal.inertiaDeg (𝓞 F)) =
      A ^ Module.finrank F K := by
  classical
  set p := w.maximalIdeal.asIdeal with hp_def
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal w.maximalIdeal.isPrime w.maximalIdeal.ne_bot
  -- the fiber of finite places above `w` is the set of primes of `𝓞 K` above `p`
  have hbij : Set.BijOn (fun v : FinitePlace K => v.maximalIdeal.asIdeal)
      {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver p} (p.primesOver (𝓞 K)) := by
    rw [hp_def]
    exact liesOver_fiber_bijOn F w
  -- the weighted sum over the fiber is `[K : F]`
  have hsum : (∑ Q : p.primesOver (𝓞 K),
      Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F)) = Module.finrank F K := by
    rw [Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm
  rw [finprod_mem_eq_of_bijOn (f := fun v : FinitePlace K => A ^
        (v.maximalIdeal.asIdeal.ramificationIdx (𝓞 F) *
          v.maximalIdeal.asIdeal.inertiaDeg (𝓞 F)))
      (g := fun Q : Ideal (𝓞 K) => A ^ (Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F)))
      (fun v : FinitePlace K => v.maximalIdeal.asIdeal) hbij (fun _ _ => rfl)]
  rw [finprod_mem_eq_fintype_prod, Finset.prod_pow_eq_pow_sum, hsum]

end Work.BW
