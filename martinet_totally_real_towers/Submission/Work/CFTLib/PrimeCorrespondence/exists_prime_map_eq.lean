import Mathlib

namespace Work.CFTLib.PrimeCorrespondence

theorem exists_prime_map_eq {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] (e : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K')
    (hcomp : ∀ x : NumberField.RingOfIntegers F,
      e (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) x) =
        algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K') x)
    (u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K'))
    (hw : w.asIdeal.LiesOver u.asIdeal) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v.asIdeal.LiesOver u.asIdeal ∧
        w.asIdeal = v.asIdeal.map (e : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K') := by
  -- view the ring equivalence as a ring hom, which is surjective
  let f : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K' := e
  have hf : Function.Surjective f := e.surjective
  -- the compatibility of `e` with the structure maps of `F`
  have hcomp' : f.comp (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)) =
      algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K') := by
    apply RingHom.ext
    intro x
    exact hcomp x
  -- the pulled back ideal is nonzero
  have hvne : Ideal.comap f w.asIdeal ≠ ⊥ := by
    intro hbot
    have hmap : Ideal.map f (Ideal.comap f w.asIdeal) = w.asIdeal :=
      Ideal.map_comap_of_surjective f hf w.asIdeal
    rw [hbot, Ideal.map_bot] at hmap
    exact w.ne_bot hmap.symm
  refine ⟨⟨Ideal.comap f w.asIdeal, Ideal.comap_isPrime f w.asIdeal, hvne⟩, ?_, ?_⟩
  · -- it lies over `u`
    refine ⟨?_⟩
    show u.asIdeal = Ideal.comap (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K))
      (Ideal.comap f w.asIdeal)
    rw [Ideal.comap_comap, hcomp']
    exact hw.over
  · -- and pushes forward to `w`
    exact (Ideal.map_comap_of_surjective f hf w.asIdeal).symm

end Work.CFTLib.PrimeCorrespondence
