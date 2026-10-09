import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.localField_subfield_place_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The compositum fact `K_w = k_v · K` (`NOTE_e1a_session5.md` §4c.11 sub-fact (i))

For a finite place `A` of `Ω` over a finite place `q` of `K`, the completion `K_w = q.adicCompletion K`
is generated over the local field `k_v = localFieldAt k A hA` by the image of `K`:

    IntermediateField.adjoin (localFieldAt k A hA) (Set.range (algebraMap K (q.adicCompletion K))) = ⊤.

Pattern: the `hgen` block of `Submission/Work/ZDataTwo/localNormSubgroup_eq_normGroup_quadLevel.lean`
(density of `K` in its completion + `Submodule.closed_of_finiteDimensional`).

**Instance note (why this statement carries `hLies` as an `haveI` instead of a `letI`-`Algebra`).**
The place glue writes its `Algebra (localFieldAt k A hA) (q.adicCompletion K)` as a `letI`; that
*shadows* the global instance and makes the `Module`/`AddCommMonoid` of `q.adicCompletion K` come from
the `DivisionSemiring` path, which makes `Submodule.closed_of_finiteDimensional` fail with
`expected AddCommGroup.toAddCommMonoid`.  Using the global instance (from `hLies`, exactly as the
quad-level template does) keeps the normed path, and the lemma applies verbatim.
-/

namespace Work.SSGRoute.ExtChain

open scoped Classical

noncomputable section

theorem adicCompletion_eq_adjoin_image (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal)
    (hcompat : ∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x)) :
    IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (fun x : K => algebraMap K (q.adicCompletion K) x)) = ⊤ := by
  haveI : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal := hLies
  haveI : IsScalarTower k (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun x => hcompat x)
  haveI hfin : Module.Finite (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
      (Work.SSGRoute.primeUnder k A hA) q hLies
  haveI hfd : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    inferInstance
  have hcont : Continuous
      (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)) :=
    Commons.RingTheory.Henselian.adicCompletionMap_continuous
      (Work.SSGRoute.primeUnder k A hA) q hLies
  haveI hcsm : ContinuousSMul (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    continuousSMul_of_algebraMap _ _ hcont
  set S := IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
    (Set.range (fun x : K => algebraMap K (q.adicCompletion K) x)) with hS
  -- NOTE (session 5, §4c.14): the single remaining step.  With the global `Algebra` (from `hLies`)
  -- the `Module.Finite`/continuity inputs are now the template's
  -- (`Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion`,
  -- `Commons.RingTheory.Henselian.adicCompletionMap_continuous`), but `S.toSubmodule` still carries
  -- the `Field.toSemifield.toDivisionSemiring.toAddCommMonoid` / `Algebra.toModule` instance
  -- arguments, while `Submodule.closed_of_finiteDimensional` expects the
  -- `AddCommGroup`/`NormedAddCommGroup` path:
  --   Application type mismatch ... expected AddCommGroup.toAddCommMonoid ...
  -- The remaining fix is to *re-form* the submodule under the intended instances (an `@Submodule`
  -- ascription with explicit `AddCommGroup`/`SMul`/`Module` arguments, or an
  -- `IntermediateField`-flavoured closedness lemma), not to change the ambient instances.
  obtain ⟨s, hsfin, hsspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := k) (M := K))
  have hspan_eq : Submodule.span (Work.SSGRoute.localFieldAt k A hA)
        (Set.range (algebraMap K (q.adicCompletion K)))
      = Submodule.span (Work.SSGRoute.localFieldAt k A hA)
        ((algebraMap K (q.adicCompletion K)) '' s) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span k s := by rw [hsspan]; exact Submodule.mem_top
      refine Submodule.span_induction
        (p := fun y _ => (algebraMap K (q.adicCompletion K)) y ∈
          Submodule.span (Work.SSGRoute.localFieldAt k A hA)
            ((algebraMap K (q.adicCompletion K)) '' s))
        (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩) (Submodule.zero_mem _)
        (fun y z _ _ hy hz => by rw [map_add]; exact Submodule.add_mem _ hy hz) ?_ hx
      intro a y _ hy
      rw [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply k K (q.adicCompletion K) a, hcompat a]
      exact Submodule.smul_mem _ _ hy
    · exact Submodule.span_mono (Set.image_subset_range _ _)
  haveI hPfd : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA)
      ↥(Submodule.span (Work.SSGRoute.localFieldAt k A hA)
        ((algebraMap K (q.adicCompletion K)) '' s)) :=
    Module.Finite.span_of_finite (Work.SSGRoute.localFieldAt k A hA)
      (hsfin.image (algebraMap K (q.adicCompletion K)))
  have hPclosed : IsClosed
      ((Submodule.span (Work.SSGRoute.localFieldAt k A hA)
        (Set.range (algebraMap K (q.adicCompletion K)))) : Set (q.adicCompletion K)) := by
    letI nf : NontriviallyNormedField ((Work.SSGRoute.primeUnder k A hA).adicCompletion k) :=
      Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
    haveI : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA)
        ↥(Submodule.span (Work.SSGRoute.localFieldAt k A hA)
          (Set.range (algebraMap K (q.adicCompletion K)))) := by
      rw [hspan_eq]
      exact hPfd
    exact Submodule.closed_of_finiteDimensional
      (𝕜 := (Work.SSGRoute.primeUnder k A hA).adicCompletion k) _
  have hdense : DenseRange (algebraMap K (q.adicCompletion K)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K q
  have hPtop : Submodule.span (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (algebraMap K (q.adicCompletion K))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hd : closure (Set.range (algebraMap K (q.adicCompletion K))) = Set.univ :=
      hdense.closure_range
    have hx : x ∈ closure (Set.range (algebraMap K (q.adicCompletion K))) := by
      rw [hd]; trivial
    exact closure_minimal (Submodule.subset_span) hPclosed hx
  have hfinal : ∀ x ∈ Submodule.span (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (algebraMap K (q.adicCompletion K))), x ∈ IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
      (Set.range (algebraMap K (q.adicCompletion K))) := by
    intro x hx
    refine Submodule.span_induction
      (p := fun y _ => y ∈ IntermediateField.adjoin (Work.SSGRoute.localFieldAt k A hA)
        (Set.range (algebraMap K (q.adicCompletion K))))
      (fun y hy => IntermediateField.subset_adjoin _ _ hy) (IntermediateField.zero_mem _)
      (fun y z _ _ hy hz => IntermediateField.add_mem _ hy hz) ?_ hx
    intro a y _ hy
    rw [Algebra.smul_def]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ a) hy
  refine le_antisymm le_top ?_
  intro x _
  exact hfinal x (hPtop.symm ▸ Submodule.mem_top)

end

end Work.SSGRoute.ExtChain
