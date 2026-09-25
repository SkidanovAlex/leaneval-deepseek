import Mathlib
import Submission.Work.Tower.Assembly.Main
import Submission.Work.Tower.Assembly.Setup
import Submission.Work.Tower.Assembly.Primes
import Submission.Work.Tower.Assembly.Analysis

set_option linter.style.haveILetI false

namespace Work.Tower.Assembly

/-- Two `ℚ`-module structures on the same additive commutative monoid whose scalar actions
agree as functions have the same `Module.finrank`.  This is the workhorse of the type-class
translation below: it lets one move `Module.finrank ℚ ↥F` between the two canonical module
structures on an intermediate field. -/
lemma finrank_congr_of_smul {A : Type*} (sr : Semiring ℚ) (acm : AddCommMonoid A)
    (m₁ m₂ : @Module ℚ A sr acm)
    (h : ∀ (q : ℚ) (a : A), (letI := m₁; q • a) = (letI := m₂; q • a)) :
    @Module.finrank ℚ A sr acm m₁ = @Module.finrank ℚ A sr acm m₂ := by
  rw [Module.ext' m₁ m₂ (fun q a => h q a)]

/-- The coercion to the ambient field of `algebraMap ℚ ↥F q`, for any `ℚ`-algebra structure
`alg` on the intermediate field `F`, equals `algebraMap ℚ M q`: both sides are ring
homomorphisms `ℚ →+* M` composed with the inclusion, and homomorphisms out of `ℚ` are unique
(`RingHom.ext_rat`). -/
lemma coe_algebraMap_eq {M : Type*} [Field M] [Algebra ℚ M] (F : IntermediateField ℚ M)
    (alg : Algebra ℚ ↥F) (q : ℚ) :
    ((@algebraMap ℚ ↥F _ _ alg q : ↥F) : M) = algebraMap ℚ M q := by
  have h : (F.val : ↥F →+* M).comp (@algebraMap ℚ ↥F _ _ alg) = algebraMap ℚ M :=
    RingHom.ext_rat _ _
  exact RingHom.congr_fun h q

/-- **The final assembly, in the literal `IntermediateField` shape of the base interface.**

This is the `Tower/Assembly` deliverable with `hbase` producing `F : IntermediateField ℚ M`
exactly as the base area (`Tower/CyclotomicBase`) naturally does.  It follows from
`Work.Tower.Assembly.exists_tower_of_base_and_shafarevich` (in
`Submission/Work/Tower/Assembly/Main.lean`, already proved, whose `hbase` is the same statement
with `F` a bare type) applied to a bridge that turns the `IntermediateField` data into the
packaged data.

The only non-trivial step of the bridge is a type-class translation.  For
`F : IntermediateField ℚ M` there are two canonical `ℚ`-module structures on `↥F`:
`IntermediateField.module'`, whose scalar action is the restriction of that of `M`, and
`Algebra.toModule (F.algebra')`, whose scalar action is `q • x = algebraMap ℚ ↥F q * x`.  They
agree as functions but are not definitionally equal, and the packaged statement resolves
`Module.finrank ℚ` with one while the `IntermediateField`-flavoured lemmas of the base area
resolve it with the other; hence one needs a transfer of the form
`@Module.finrank ℚ ↥F _ _ F.module' = @Module.finrank ℚ ↥F _ _ (Algebra.toModule (F.algebra'))`,
provable by exhibiting the identity as a linear equivalence (the two `AddCommMonoid` structures
on `↥F` coincide, and the scalar actions agree by `Algebra.smul_def`).  Everything else in the
bridge is type-class-agnostic: `NumberField.discr` does not depend on which `NumberField`
instance is used, `NumberField.IsTotallyReal` takes only a `[Field K]` argument,
`FiniteDimensional ↥F M` follows from `Module.finrank ↥F M = 3 ^ (ℓ - 1)` via
`Module.finite_of_finrank_pos`, and `IsGalois ↥F M` follows from `IsAbelianGalois ↥F M`. -/
theorem exists_tower_intermediateField
    (hbase : ∀ (ℓ : ℕ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
      Function.Injective r →
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : IsGalois ℚ M)
        (F : IntermediateField ℚ M),
        Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ NumberField.IsTotallyReal ↥F ∧
        IsAbelianGalois ↥F M ∧ Module.finrank ↥F M = 3 ^ (ℓ - 1) ∧
        (∀ σ : Gal(M/↥F), σ ^ 3 = 1) ∧ Work.Tower.IsUnramifiedExtension ↥F M ∧
        |NumberField.discr ↥F| = ((∏ i, r i : ℕ) : ℤ) ^ 2)
    (hshaf : ∃ C₀ : ℕ,
      ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
        Module.finrank ℚ F = 3 →
        ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
          Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
          ∀ (T : Finset (Ideal (NumberField.RingOfIntegers F))), (∀ 𝔭 ∈ T, 𝔭.IsPrime) →
            (∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
               [FiniteDimensional F L] [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
               (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭) →
            (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
               [IsGalois F L],
               Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
               (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
            Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F))) ≤
              Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine exists_tower_of_base_and_shafarevich ?_ hshaf
  intro ℓ r hr hr3 hrinj
  obtain ⟨M, hMF, hMN, hMA, hMG, F, hF3, hFgal, hFTR, hFab, hFMdeg, hFexp,
    hFunr, hFdisc⟩ := hbase ℓ r hr hr3 hrinj
  letI : Field M := hMF
  letI : NumberField M := hMN
  letI : Algebra ℚ M := hMA
  letI : IsGalois ℚ M := hMG
  -- The bridge: package the `IntermediateField` data as the bare-type data, taking `F` to be
  -- the carrier `↥F` of the intermediate field.
  refine ⟨↥F, inferInstance, inferInstance, hFTR, hFgal, M, inferInstance, inferInstance,
    inferInstance, ?_, hFab.toIsGalois, ?_, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩
  · -- `FiniteDimensional ↥F M`, from `Module.finrank ↥F M = 3 ^ (ℓ - 1) > 0`.
    exact Module.finite_of_finrank_pos (by rw [hFMdeg]; positivity)
  · -- the transfer of `Module.finrank ℚ ↥F` between the two canonical module structures
    refine Eq.trans ?_ hF3
    refine finrank_congr_of_smul _ _ _ _ ?_
    intro q a
    apply Subtype.ext
    rw [Algebra.smul_def]
    simp only [IntermediateField.coe_mul]
    rw [coe_algebraMap_eq F _ q, IntermediateField.coe_smul, Algebra.smul_def]

end Work.Tower.Assembly
