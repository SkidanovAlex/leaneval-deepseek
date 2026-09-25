import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.splitSet_determines_field
import Submission.Work.CFTLib.splitSet_eq_imp_proportional
-- (import of Submission.Work.CFTLib.InvCharCrux removed: that module currently fails to build; the
-- complete-splitting variant `splitsCompletelySet_determines_field` is not needed here since
-- `Work.CFTLib.splitSet_determines_field` below is imported directly.)
import Submission.Work.Tower.Shafarevich.Frobenius.splitsCompletelyIn_iff_ncard_primesOver
import Submission.Work.CFTLib.InvCharCrux.ConjField
import Submission.Work.CFTLib.InvCharCrux.under_map_conjRingAlgEquiv
import Submission.Work.CFTLib.InvCharCrux.inertiaDeg_map_conjRingAlgEquiv

open NumberField
open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Work.CFTLib.InvCharCrux

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']

/-! ## The transport of inertia degrees to the conjugate field -/

/-- The contraction to `𝓞 F` of an ideal of `𝓞 K` is unchanged by mapping along the ring
equivalence induced by an `F`-automorphism of `K` (which fixes `𝓞 F` pointwise). -/
theorem under_map_mapRingEquiv (h : K ≃ₐ[F] K) (I : Ideal (𝓞 K)) :
    (I.map ((NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv)).under (𝓞 F)
      = I.under (𝓞 F) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_under,
    Ideal.mem_map_iff_of_surjective
      ((NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv)
      (NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h2 : (NumberField.RingOfIntegers.mapAlgEquiv h) y =
        (NumberField.RingOfIntegers.mapAlgEquiv h) (algebraMap (𝓞 F) (𝓞 K) x) := by
      rw [show (NumberField.RingOfIntegers.mapAlgEquiv h) y = algebraMap (𝓞 F) (𝓞 K) x from hyx,
        (NumberField.RingOfIntegers.mapAlgEquiv h).commutes x]
    have h1 : y = algebraMap (𝓞 F) (𝓞 K) x :=
      (NumberField.RingOfIntegers.mapAlgEquiv h).injective h2
    rwa [h1] at hy
  · intro hx
    exact ⟨algebraMap (𝓞 F) (𝓞 K) x, hx,
      (NumberField.RingOfIntegers.mapAlgEquiv h).commutes x⟩

/-- The same statement for prime ideals, phrased through `mapPrime`. -/
theorem under_mapPrime (h : K ≃ₐ[F] K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ((mapPrime ((NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv) v).asIdeal).under (𝓞 F)
      = v.asIdeal.under (𝓞 F) := by
  rw [mapPrime_asIdeal]
  exact under_map_mapRingEquiv h v.asIdeal

/-- `mapRingEquiv` commutes with inversion. -/
theorem mapRingEquiv_inv (e : K ≃+* K) :
    (NumberField.RingOfIntegers.mapRingEquiv e)⁻¹
      = NumberField.RingOfIntegers.mapRingEquiv e⁻¹ := by
  ext x
  rw [show (NumberField.RingOfIntegers.mapRingEquiv e)⁻¹
      = (NumberField.RingOfIntegers.mapRingEquiv e).symm from rfl,
    show e⁻¹ = e.symm from rfl,
    NumberField.RingOfIntegers.mapRingEquiv_symm_apply,
    NumberField.RingOfIntegers.mapRingEquiv_apply]

/-- Taking rings of integers commutes with inversion of an `F`-algebra automorphism of `K`. -/
theorem mapAlgEquiv_toRingEquiv_inv (h : K ≃ₐ[F] K) :
    ((NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv)⁻¹ =
      (NumberField.RingOfIntegers.mapAlgEquiv h⁻¹).toRingEquiv := by
  rw [show (NumberField.RingOfIntegers.mapAlgEquiv h).toRingEquiv
      = NumberField.RingOfIntegers.mapRingEquiv (h : K ≃+* K) from rfl,
    show (NumberField.RingOfIntegers.mapAlgEquiv h⁻¹).toRingEquiv
      = NumberField.RingOfIntegers.mapRingEquiv ((h⁻¹ : K ≃ₐ[F] K) : K ≃+* K) from rfl,
    mapRingEquiv_inv]
  congr 1

/-- **The inertia degree of the conjugate field.**  For every prime `v` of `𝓞 K`,

`inertiaDegIn v (𝓞 (conjField g M)) = inertiaDegIn (ḡ⁻¹ v) (𝓞 M)`,

where `ḡ = g.restrictNormal K` is the restriction of `g` to `K`, `e` is the ring equivalence of
`𝓞 K` induced by `ḡ`, and `ḡ⁻¹ v` is the image prime `mapPrime e⁻¹ v`.

Indeed, both sides compute the inertia degree over `𝓞 K` of a prime `Q` of `𝓞 M` above `e⁻¹ v` and
of its image `P` in `𝓞 (conjField g M)` above `v`; the two agree over `𝓞 F`
(`inertiaDeg_map_conjRingAlgEquiv`, the `𝓞 F`-algebra structure being preserved by the isomorphism
`conjRingAlgEquiv g M`), and the contractions of `P` and `Q` to `𝓞 F` agree since
`P.under (𝓞 K) = (Q.under (𝓞 K)).map e` and `e` fixes `𝓞 F` pointwise. -/
theorem inertiaDegIn_conjField (g : K' ≃ₐ[F] K') (M : IntermediateField K K')
    [FiniteDimensional K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal.inertiaDegIn v.asIdeal (𝓞 ↥(conjField g M)) =
      Ideal.inertiaDegIn
        (mapPrime ((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)⁻¹).toRingEquiv)
          v).asIdeal (𝓞 ↥M) := by
  classical
  haveI hfdC : FiniteDimensional K ↥(conjField g M) := finiteDimensional_conjField g M
  haveI hgalC : IsGalois K ↥(conjField g M) := isGalois_conjField g M
  haveI hnfC : NumberField ↥(conjField g M) := NumberField.of_module_finite K ↥(conjField g M)
  haveI hnfM : NumberField ↥M := NumberField.of_module_finite K ↥M
  set e : 𝓞 K ≃+* 𝓞 K :=
    (NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)).toRingEquiv with he
  have he' : ((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)⁻¹).toRingEquiv) =
      e⁻¹ := by
    rw [← mapAlgEquiv_toRingEquiv_inv (g.restrictNormal K), ← he]
  rw [he']
  -- a prime `Q` of `𝓞 M` above `e⁻¹ v`
  obtain ⟨Q, hQp, hQl⟩ :
      ∃ Q : Ideal (𝓞 ↥M), Q.IsPrime ∧ Q.LiesOver (mapPrime e⁻¹ v).asIdeal := by
    obtain ⟨Q⟩ := (inferInstance : Nonempty ((mapPrime e⁻¹ v).asIdeal.primesOver (𝓞 ↥M)))
    exact ⟨Q.1, Q.2.1, Q.2.2⟩
  haveI := hQp
  haveI := hQl
  -- its image `P` in the conjugate field
  set P : Ideal (𝓞 ↥(conjField g M)) := Q.map (conjRingAlgEquiv g M).toRingHom with hP
  have hPp : P.IsPrime := by
    rw [hP]
    exact Ideal.map_isPrime_of_equiv (conjRingAlgEquiv g M)
  have hQu : Q.under (𝓞 K) = (mapPrime e⁻¹ v).asIdeal :=
    (Ideal.over_def Q (mapPrime e⁻¹ v).asIdeal).symm
  have hPu : P.under (𝓞 K) = (Q.under (𝓞 K)).map e := by
    rw [hP]
    exact under_map_conjRingAlgEquiv g M Q
  have hPu' : P.under (𝓞 K) = v.asIdeal := by
    rw [hPu, hQu, ← mapPrime_asIdeal e (mapPrime e⁻¹ v),
      ← mapPrime_comp e⁻¹ e, mul_inv_cancel, mapPrime_id]
  haveI : P.LiesOver v.asIdeal := hPu' ▸ Ideal.over_under P
  haveI := hPp
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P
        (↥(conjField g M) ≃ₐ[K] ↥(conjField g M)),
      Ideal.inertiaDegIn_eq_inertiaDeg (mapPrime e⁻¹ v).asIdeal Q (↥M ≃ₐ[K] ↥M)]
  -- it remains to compare the inertia degrees over `𝓞 K`
  have htop : P.inertiaDeg (𝓞 F) = Q.inertiaDeg (𝓞 F) := by
    rw [hP]
    exact inertiaDeg_map_conjRingAlgEquiv g M Q
  have hbot : (P.under (𝓞 K)).inertiaDeg (𝓞 F) = (Q.under (𝓞 K)).inertiaDeg (𝓞 F) := by
    have hunder : (P.under (𝓞 K)).under (𝓞 F) = (Q.under (𝓞 K)).under (𝓞 F) := by
      rw [hPu, hQu, mapPrime_asIdeal]
      exact under_map_mapRingEquiv (g.restrictNormal K) (v.asIdeal.map e⁻¹)
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg ((P.under (𝓞 K)).under (𝓞 F)) (P.under (𝓞 K))
          (K ≃ₐ[F] K),
      ← Ideal.inertiaDegIn_eq_inertiaDeg ((Q.under (𝓞 K)).under (𝓞 F)) (Q.under (𝓞 K))
          (K ≃ₐ[F] K),
      hunder]
  have ht1 := Ideal.inertiaDeg_tower (R := 𝓞 F) (S := 𝓞 K) (T := 𝓞 ↥(conjField g M))
    (P.under (𝓞 K)) P
  have ht2 := Ideal.inertiaDeg_tower (R := 𝓞 F) (S := 𝓞 K) (T := 𝓞 ↥M)
    (Q.under (𝓞 K)) Q
  have hpos : 0 < (P.under (𝓞 K)).inertiaDeg (𝓞 F) :=
    Ideal.inertiaDeg_pos (P.under (𝓞 K)) (𝓞 F)
  have hmul : (P.under (𝓞 K)).inertiaDeg (𝓞 F) * P.inertiaDeg (𝓞 K) =
      (P.under (𝓞 K)).inertiaDeg (𝓞 F) * Q.inertiaDeg (𝓞 K) := by
    rw [← ht1, htop, ht2, hbot]
  exact Nat.mul_left_cancel hpos hmul

/-! ## The main theorem -/

/-- **The class field of a Galois-invariant character is Galois over the base field.** Setting: `K/F` and `K'/F` finite Galois extensions of number fields with `K ⊆ K'` (scalar tower), `p` prime, `ψ : Cl(𝓞 K) →* Multiplicative (ZMod p)` nontrivial, and `M ⊆ K'` an intermediate field which is the class field of `ψ`: `M/K` finite Galois, the `𝓞 K`-primes of inertia degree `1` in `M` are exactly those whose class is sent to `1` by `ψ` (`hlaw`), `M/K` unramified at every finite prime (`hunr`), and `ψ` invariant under the `Gal(K/F)`-action on `Cl(𝓞 K)` given by `clEquiv` (`hinv`). Then `M` is stable under `Gal(K'/F)`: the fixing subgroup of `M`, viewed as an `F`-intermediate field of `K'`, is normal in `Gal(K'/F)`.

## Proof strategy

For `g : K' ≃ₐ[F] K'` let `M'` be the conjugate field, i.e. the `K`-subfield of `K'` whose
elements are those `x` with `g⁻¹ x ∈ M` (the fixed field inside `K'/F` of
`g · M.fixingSubgroup · g⁻¹`; the `K`-structure on `M'` comes from `g(k·x) = ḡ(k)·g(x)` where
`ḡ = g|_K`). It suffices to show `M' = M`.

1. `M'` is a finite Galois extension of `K` of the same degree as `M` (conjugate the
   `Gal(K'/K)`-action).
2. Its inertia-degree-one set over `K` is `{v : ψ (primeCls (ḡ⁻¹ v)) = 1}`: if `P` is a prime of
   `𝓞 M'` over `v` then `g⁻¹P` is a prime of `𝓞 M` over `ḡ⁻¹ v`, and ramification/inertia data is
   preserved.
3. `hinv` gives `ψ (primeCls (ḡ⁻¹ v)) = ψ (primeCls v)`, so the two sets agree.
4. Hence `M' = M` by `Work.CFTLib.splitSet_determines_field`, so every `g` normalises
   `M.fixingSubgroup`, which is exactly `Subgroup.Normal`. -/
theorem fixingSubgroup_normal_of_classField {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K'] (p : ℕ) [Fact p.Prime] (M : IntermediateField K K') [FiniteDimensional K M] [IsGalois K ↥M] (ψ : ClassGroup (NumberField.RingOfIntegers K) →* Multiplicative (ZMod p)) (hψ : ψ ≠ 1) (hlaw : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers ↥M) = 1 ↔ ψ (Work.CFTLib.primeCls v) = 1) (hunr : Work.Tower.IsUnramifiedExtensionForallPrimes K ↥M) (hinv : ∀ (h : K ≃ₐ[F] K) (c : ClassGroup (NumberField.RingOfIntegers K)), ψ (Work.CFTLib.clEquiv F K h c) = ψ c) : ((IntermediateField.restrictScalars F M).fixingSubgroup).Normal := by
  classical
  -- Every conjugate of `M` is `M`; this is the class-field-theoretic content.
  have key : ∀ g : K' ≃ₐ[F] K', conjField g M = M := by
    intro g
    haveI hfdC : FiniteDimensional K ↥(conjField g M) := finiteDimensional_conjField g M
    haveI hgalC : IsGalois K ↥(conjField g M) := isGalois_conjField g M
    haveI hnfC : NumberField ↥(conjField g M) := NumberField.of_module_finite K ↥(conjField g M)
    haveI hnfM : NumberField ↥M := NumberField.of_module_finite K ↥M
    refine splitSet_determines_field (conjField g M) M ?_
    ext v
    simp only [Set.mem_ofPred_eq]
    have hψ' : ψ (Work.CFTLib.primeCls
          (mapPrime ((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)⁻¹).toRingEquiv)
            v)) = ψ (Work.CFTLib.primeCls v) := by
      rw [primeCls_mapPrime]
      exact hinv (g.restrictNormal K)⁻¹ (Work.CFTLib.primeCls v)
    rw [inertiaDegIn_conjField g M v, hlaw _, hlaw v, hψ']
  -- Conjugation by any `g` therefore preserves the fixing subgroup.
  have hconj : ∀ g : K' ≃ₐ[F] K',
      MulAut.conj g • (IntermediateField.restrictScalars F M).fixingSubgroup =
        (IntermediateField.restrictScalars F M).fixingSubgroup := by
    intro g
    rw [← IsGalois.map_fixingSubgroup (IntermediateField.restrictScalars F M) g,
      ← restrictScalars_conjField g M, key g]
  exact Subgroup.Normal.of_conjugate_fixed hconj

end Work.CFTLib.InvCharCrux
