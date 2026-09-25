import Mathlib
import Submission.Commons.Algebra.Module.range_sum_eq_span
import Submission.Commons.Algebra.Module.mem_span_iff_exists_sum
import Submission.Commons.Algebra.Module.span_subset_span_of_isScalarTower
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open scoped NumberField WithZero
open IsDedekindDomain

namespace Commons.NumberTheory.NumberField.Completion

/-- The canonical ring homomorphism `Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L`
induced by an inclusion of number fields `K → L` and a prime `q` of `𝓞 L` lying over `Q`. -/
noncomputable def adicCompletionMapIntegers {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Q.adicCompletionIntegers K →+* q.adicCompletionIntegers L :=
  ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
    (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2)

/-- The `𝓞 K`-algebra structure on `q.adicCompletion L` is compatible with the
`𝓞 K`-algebra structure on `𝓞 L`. -/
lemma isScalarTower_ringOfIntegers_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsScalarTower (𝓞 K) (𝓞 L) (q.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The `𝓞 K`-algebra structure on `q.adicCompletion L` is compatible with the algebra structure
coming from the ring of integers of the `Q`-adic completion of `K`. -/
lemma isScalarTower_ringOfIntegers_adicCompletionIntegers {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    IsScalarTower (𝓞 K) (Q.adicCompletionIntegers K) (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  change (algebraMap (𝓞 K) (q.adicCompletion L)) c =
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      ((algebraMap (𝓞 K) (Q.adicCompletionIntegers K)) c)
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [IsScalarTower.algebraMap_eq (𝓞 K) K (q.adicCompletion L)]
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply]
  exact rfl

/-- The `Q.adicCompletionIntegers K`-algebra structure on `q.adicCompletion L` is compatible
with the natural algebra structure on `q.adicCompletionIntegers L`. -/
lemma isScalarTower_adicCompletionIntegers_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
    IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rfl

/-- The image in `q.adicCompletion L` of an element of `𝓞 L` is integral over
`Q.adicCompletionIntegers K`. -/
theorem isIntegral_algebraMap_adicCompletion_ringOfIntegers {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (b : 𝓞 L) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    IsIntegral (Q.adicCompletionIntegers K) (algebraMap (𝓞 L) (q.adicCompletion L) b) := by
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST1 : IsScalarTower (𝓞 K) (𝓞 L) (q.adicCompletion L) :=
    isScalarTower_ringOfIntegers_adicCompletion q
  haveI hST2 : IsScalarTower (𝓞 K) (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    isScalarTower_ringOfIntegers_adicCompletionIntegers Q q hq
  exact (IsIntegral.map (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) (q.adicCompletion L))
    (Algebra.IsIntegral.isIntegral (R := 𝓞 K) (A := 𝓞 L) b)).tower_top

/-- Every element of the ring of integers `q.adicCompletionIntegers L` of the `q`-adic
completion of `L` is a `Q.adicCompletionIntegers K`-linear combination of the images of a
finite generating set of `𝓞 L` as an `𝓞 K`-module.

This is the key step in identifying `q.adicCompletionIntegers L` with the integral closure of
`Q.adicCompletionIntegers K` in `q.adicCompletion L`: it exhibits the former as a finitely
generated module over the latter.  The proof is the standard approximation argument: the
`R`-span of the images of a finite generating set of `𝓞 L` over `𝓞 K` is a closed subset of
`q.adicCompletion L` (being the image of the compact space `S → R` under the continuous
"sum of scalar multiples" map), it contains the image of `𝓞 L`, and `q.adicCompletionIntegers L`
is the closure of the image of `𝓞 L`
(`Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers`). -/
theorem exists_finset_sum_of_mem_adicCompletionIntegers {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    ∃ S : Finset (𝓞 L), ∀ y : q.adicCompletionIntegers L,
      ∃ r : S → Q.adicCompletionIntegers K,
        (y : q.adicCompletion L) =
          ∑ i : S, r i • algebraMap (𝓞 L) (q.adicCompletion L) (i : 𝓞 L) := by
  classical
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  haveI hST1 : IsScalarTower (𝓞 K) (𝓞 L) (q.adicCompletion L) :=
    isScalarTower_ringOfIntegers_adicCompletion q
  haveI hST2 : IsScalarTower (𝓞 K) (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    isScalarTower_ringOfIntegers_adicCompletionIntegers Q q hq
  obtain ⟨S, hS⟩ : ∃ S : Finset (𝓞 L), Submodule.span (𝓞 K) (S : Set (𝓞 L)) = ⊤ := by
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := 𝓞 K) (M := 𝓞 L)
    exact ⟨S, hS⟩
  refine ⟨S, ?_⟩
  let f : S → q.adicCompletion L := fun i => algebraMap (𝓞 L) (q.adicCompletion L) (i : 𝓞 L)
  have hrange : (Submodule.span (Q.adicCompletionIntegers K) (Set.range f) :
      Set (q.adicCompletion L)) = Set.range fun r : S → Q.adicCompletionIntegers K =>
        ∑ i, r i • f i :=
    (Commons.Algebra.Module.range_sum_eq_span (R := Q.adicCompletionIntegers K)
        (S := q.adicCompletion L) (ι := S) f).symm
  haveI : CompactSpace (Q.adicCompletionIntegers K) :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K Q
  have hcont_alg : Continuous (fun r : Q.adicCompletionIntegers K =>
      algebraMap (Q.adicCompletionIntegers K) (q.adicCompletion L) r) := by
    change Continuous (fun r : Q.adicCompletionIntegers K =>
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq (r : Q.adicCompletion K))
    exact (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq).comp
      continuous_subtype_val
  have hcont : Continuous (fun r : S → Q.adicCompletionIntegers K => ∑ i, r i • f i) := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    simp only [Algebra.smul_def]
    exact (hcont_alg.comp (continuous_apply i)).mul continuous_const
  have hMclosed : IsClosed (Submodule.span (Q.adicCompletionIntegers K) (Set.range f) :
      Set (q.adicCompletion L)) := by
    rw [hrange]
    exact (isCompact_range hcont).isClosed
  -- the image of `𝓞 L` lies in the span
  have him : Set.range (algebraMap (𝓞 L) (q.adicCompletion L)) ⊆
      (Submodule.span (Q.adicCompletionIntegers K) (Set.range f) : Set (q.adicCompletion L)) := by
    intro z hz
    obtain ⟨b, rfl⟩ := hz
    let φ : 𝓞 L →ₗ[𝓞 K] q.adicCompletion L :=
      { toFun := fun b => algebraMap (𝓞 L) (q.adicCompletion L) b
        map_add' := fun x y => map_add _ _ _
        map_smul' := fun c x => by
          show algebraMap (𝓞 L) (q.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) c * x) =
            c • algebraMap (𝓞 L) (q.adicCompletion L) x
          rw [map_mul, Algebra.smul_def, DFunLike.congr_fun (IsScalarTower.algebraMap_eq
            (𝓞 K) (𝓞 L) (q.adicCompletion L)) c]
          rfl }
    have hb : b ∈ Submodule.span (𝓞 K) (S : Set (𝓞 L)) := by rw [hS]; trivial
    have hφb : φ b ∈ Submodule.span (𝓞 K) (Set.range f) := by
      have htop : (⊤ : Submodule (𝓞 K) (𝓞 L)) ≤
          Submodule.comap φ (Submodule.span (𝓞 K) (Set.range f)) := by
        rw [← hS, Submodule.span_le]
        exact fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact (Submodule.map_le_iff_le_comap.mpr htop) ⟨b, trivial, rfl⟩
    refine Commons.Algebra.Module.span_subset_span_of_isScalarTower (S := 𝓞 K)
      (R := Q.adicCompletionIntegers K) (Set.range f) ?_
    exact hφb
  -- density of the image of `𝓞 L` in `q.adicCompletionIntegers L`
  have hset : {z : q.adicCompletion L | ∃ r : 𝓞 L,
        algebraMap L (q.adicCompletion L) (r : L) = z} =
      Set.range (algebraMap (𝓞 L) (q.adicCompletion L)) := by
    ext z
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, by rw [← hr, IsScalarTower.algebraMap_apply (𝓞 L) L
        (q.adicCompletion L)]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, by rw [IsScalarTower.algebraMap_apply (𝓞 L) L (q.adicCompletion L)]⟩
  intro y
  have hx1 : (y : q.adicCompletion L) ∈
      closure (Set.range (algebraMap (𝓞 L) (q.adicCompletion L))) := by
    have h := Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
      L q y
    rwa [hset] at h
  have hx2 : (y : q.adicCompletion L) ∈
      (Submodule.span (Q.adicCompletionIntegers K) (Set.range f) :
        Set (q.adicCompletion L)) :=
    hMclosed.closure_eq ▸ closure_mono him hx1
  exact (Commons.Algebra.Module.mem_span_iff_exists_sum (R := Q.adicCompletionIntegers K)
    (S := q.adicCompletion L) (ι := S) f (y : q.adicCompletion L)).mp hx2
/-- The main theorem: the ring of integers of the `q`-adic completion of `L` is the integral
closure of the ring of integers of the `Q`-adic completion of `K`, for a prime `q` of `𝓞 L`
lying over `Q`. -/
theorem isIntegralClosure_adicCompletionIntegers_extension {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
      RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype)
    IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) := by
  classical
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (adicCompletionMapIntegers Q q hq)
  haveI hST : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    isScalarTower_adicCompletionIntegers_adicCompletion Q q hq
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact Subtype.ext hab
  · intro x
    constructor
    · -- an element integral over `R` is integral over `A`, hence lies in `A`
      intro hx
      have hxA : IsIntegral (q.adicCompletionIntegers L) x := hx.tower_top
      have hv : (Valued.v : Valuation (q.adicCompletion L) ℤᵐ⁰).Integers
          (q.adicCompletionIntegers L) :=
        Valuation.integer.integers (Valued.v : Valuation (q.adicCompletion L) ℤᵐ⁰)
      have hmem : x ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L)) :=
        Valuation.Integers.mem_of_integral hv hxA
      exact ⟨⟨x, hmem⟩, rfl⟩
    · -- conversely, `A` is generated as an `R`-module by integral elements
      rintro ⟨y, rfl⟩
      obtain ⟨S, hSsum⟩ := exists_finset_sum_of_mem_adicCompletionIntegers Q q hq
      obtain ⟨r, hr⟩ := hSsum y
      change IsIntegral (Q.adicCompletionIntegers K) (y : q.adicCompletion L)
      rw [hr]
      refine IsIntegral.sum (s := Finset.univ)
        (fun i : S => r i • algebraMap (𝓞 L) (q.adicCompletion L) (i : 𝓞 L)) ?_
      intro i _
      exact IsIntegral.smul (r i)
        (isIntegral_algebraMap_adicCompletion_ringOfIntegers Q q hq (i : 𝓞 L))


end Commons.NumberTheory.NumberField.Completion
