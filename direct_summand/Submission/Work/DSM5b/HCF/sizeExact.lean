import Mathlib
import Submission.Work.DSM5b.HCF.Filtration

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

/-- The quotient map of the size filtration, evaluated termwise at a tuple `τ`: definitionally the
quotient map `Submodule.mkQ` of the `τ`-th component.  This is the termwise presentation of
`CoeffSys.sizeQuot` used to compute its kernel. -/
@[simp] lemma sizeQuot_apply {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k m : ℕ) (z : CoeffSys.SizeC 𝒜 k m) (τ : Fin (m + 1) → ι) :
    CoeffSys.sizeQuot 𝒜 k m z τ =
      Submodule.mkQ (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ))).range (z τ) :=
  rfl

/-- **Termwise exactness of the filtration sequence.**  For a coefficient system `𝒜` (on the
finite subsets of `ι`, with `R` commutative), and `k m : ℕ`, the size-filtration maps
`sizeIncl 𝒜 k m : SizeC 𝒜 (k+1) m →ₗ SizeC 𝒜 k m` (termwise the inclusion
`↥((sizeSubSys 𝒜 (k+1)).N S) → ↥((sizeSubSys 𝒜 k).N S)` of the nested size sub-systems) and
`sizeQuot 𝒜 k m : SizeC 𝒜 k m →ₗ SizeQ 𝒜 k m` (termwise the quotient map
`↥((sizeSubSys 𝒜 k).N S) → ↥((sizeSubSys 𝒜 k).N S) ⧸ (the image of the smaller sub-system)`) form
the termwise short exact sequence `0 → ↥(N_{k+1} S) → ↥(N_k S) → ↥(N_k S) ⧸ image → 0` of
`R`-modules: `sizeIncl` is injective, `sizeQuot` is surjective, and
`ker sizeQuot = range sizeIncl`.

All notions are in `Submission/Work/DSM5b/HCF/Filtration.lean` (`SizeC`, `SizeQ`, `sizeIncl`,
`sizeQuot`, built on `CoeffSys.sizeSubSys`, `CoeffSys.sizeSubSys_mono`, `CoeffSys.exactlyCoeff`).
Route: every statement is *termwise*, i.e. pointwise in the tuple `τ : Fin (m+1) → ι`, and each
termwise statement is a grading-free fact about the `R`-modules `↥(N_{k+1} S) ⊆ ↥(N_k S) ⊆ 𝒜.M S`
and the quotient `↥(N_k S) ⧸ (Submodule.inclusion _).range` (the exactness of
`0 → ↥(N_{k+1} S) → ↥(N_k S) → ↥(N_k S) ⧸ image → 0`), using `Submodule.mkQ_surjective`,
`Submodule.ker_mkQ` / `Submodule.mkQ_eq_zero_iff`-style lemmas, `LinearMap.mem_ker`,
`LinearMap.mem_range` and `Subtype.ext`.  The third conjunct follows because `SizeQ`'s quotient is
defined by exactly the range in question.

Presentation note: the definitions emit terms of the shape `Submodule.mkQ _ x`, not the
`⟦x⟧`/`Quotient.mk (Submodule.quotientRel _) x` presentation; when a quotient induction is needed
prefer `obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x` over `Quotient.inductionOn`, whose
`⟦x⟧`-shaped goals do not match `Submodule.mkQ`-patterns.  Annotate the submodule in
`Submodule.mkQ _` explicitly (a metavariable ring otherwise gives a stuck instance).

Do NOT use `sorry` and do NOT use any frozen `DSMap`/`area_*` declaration.  Helper lemmas may be
added in the same file (declare `universe u` if needed). -/
theorem sizeExact {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] (𝒜 : Work.DSM5b.CoeffSys R ι) (k m : ℕ) : Function.Injective (Work.DSM5b.CoeffSys.sizeIncl 𝒜 k m) ∧ Function.Surjective (Work.DSM5b.CoeffSys.sizeQuot 𝒜 k m) ∧ LinearMap.ker (Work.DSM5b.CoeffSys.sizeQuot 𝒜 k m) = LinearMap.range (Work.DSM5b.CoeffSys.sizeIncl 𝒜 k m) := by
  constructor
  · -- Injectivity is termwise: the underlying `𝒜.M`-values agree, hence the subtypes agree.
    intro z z' h
    funext τ
    apply Subtype.ext
    have hτ : (CoeffSys.sizeIncl 𝒜 k m z) τ = (CoeffSys.sizeIncl 𝒜 k m z') τ := congr_fun h τ
    simpa using congrArg Subtype.val hτ
  constructor
  · -- Surjectivity is termwise: each `Submodule.mkQ` is surjective.
    intro x
    refine ⟨fun τ => (Submodule.mkQ_surjective
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ))).range (x τ)).choose, ?_⟩
    funext τ
    simpa using (Submodule.mkQ_surjective
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ))).range (x τ)).choose_spec
  · -- `ker sizeQuot = range sizeIncl`, termwise.
    ext z
    constructor
    · -- ker ⊆ range: a vanishing class is the class of an element of the smaller sub-system.
      intro hz
      have hmem : ∀ τ, ∃ y : ↥((CoeffSys.sizeSubSys 𝒜 (k + 1)).N (tupRng τ)),
          Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ)) y = z τ := by
        intro τ
        have hzτ : Submodule.mkQ
            (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ))).range (z τ) = 0 :=
          congr_fun hz τ
        have hmem' : z τ ∈
            (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k (tupRng τ))).range := by
          rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
          exact hzτ
        exact LinearMap.mem_range.mp hmem'
      rw [LinearMap.mem_range]
      refine ⟨fun τ => ⟨(hmem τ).choose.1, (hmem τ).choose.2⟩, ?_⟩
      funext τ
      apply Subtype.ext
      simpa using congrArg Subtype.val (hmem τ).choose_spec
    · -- range ⊆ ker: an element in the image is a multiple of something in the smaller sub-system.
      intro hz
      rw [LinearMap.mem_range] at hz
      obtain ⟨w, rfl⟩ := hz
      rw [LinearMap.mem_ker]
      funext τ
      rw [sizeQuot_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range.mpr ⟨w τ, rfl⟩)

end Work.DSM5b.HCF
