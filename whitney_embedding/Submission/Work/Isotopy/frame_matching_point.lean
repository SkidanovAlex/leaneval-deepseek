import Mathlib

/-!
# Frame matching: the single-point (algebraic) leaf

This file starts the chapter needed by the collar trivialisation: matching a smooth family of
orthonormal `k`-frames `B s` to a fixed orthonormal `k`-frame `C` by a smooth family
`R s` of linear equivalences with `R s (B s i) = C i` (the input consumed by
`Work.Whitney.CutPush.tube_cone_flat_of_frame_matching` and
`Work.Isotopy.fibered_diffeomorphism_of_linearFamily`).

Mathlib ingredients located in this revision (for the following leaves):

* `Orthonormal.exists_orthonormalBasis_extension` — extend an orthonormal family of a
  finite-dimensional inner product space to an orthonormal basis (the *completion* `(B s, z)` and
  the completion of `C`);
* `OrthonormalBasis.repr` — a *linear isometry* equivalence `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`;
* `OrthonormalBasis.mk`, `Orthonormal.linearIndependent`, `orthonormal_iff_ite`,
  `EuclideanSpace.single`;
* `LinearEquiv.ofBijective`, `Fintype.card_eq`, `Submodule.orthogonalProjectionOnto`.

Negatives (do not look for them): `gramSchmidt`, `Basis.equiv` (use `Module.Basis` API instead).

Plan for the single-point leaf `frame_matching_point` (next):

> orthonormal `B C : Fin k → E` ⟹ `∃ R : E ≃L[ℝ] E, ∀ i, R (B i) = C i`.

Proof: complete `B` and `C` to orthonormal bases `bB`, `bC` (indices `u`, `w`, with `Set.range B ⊆ u`,
`Set.range C ⊆ w`) using `Orthonormal.exists_orthonormalBasis_extension` (whose hypothesis is
`Orthonormal ℝ (Subtype.val : Set.range B → E)`, supplied by `orthonormal_subtype_range` below);
choose a bijection `u ≃ w` carrying `B i ↦ C i` (possible because the complements of the ranges have
equal cardinality, `finrank ℝ E - k`, since both bases have cardinality `finrank ℝ E`); conjugate
`bB.repr` with that bijection and `bC.repr`.

The local and global leaves (Gram–Schmidt against the completion at a base parameter, then gluing
over a cover of `ℝ` with the `π₀ O (M-k)` torsion absorbed — the nerve of a cover by intervals is a
tree) are described in `Submission/Work/Isotopy/tube_uniform_radius.lean`.
-/

namespace Work.Isotopy

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Reindexing an orthonormal family by its range.**  The family `x ↦ (x : E)` indexed by the set
`Set.range B` is orthonormal whenever `B` is; this is the hypothesis form required by
`Orthonormal.exists_orthonormalBasis_extension`. -/
theorem orthonormal_subtype_range {ι : Type*} {B : ι → E} (hB : Orthonormal ℝ B) :
    Orthonormal ℝ (fun x : Set.range B => (x : E)) := by
  classical
  have hinj : Function.Injective B := (Orthonormal.linearIndependent hB).injective
  have key : ∀ i j : ι,
      ((⟨B i, Set.mem_range_self i⟩ : Set.range B) = ⟨B j, Set.mem_range_self j⟩) ↔ i = j := by
    intro i j
    constructor
    · intro h
      exact hinj (congrArg Subtype.val h)
    · intro h
      subst h
      rfl
  rw [orthonormal_iff_ite]
  rintro ⟨x, i, rfl⟩ ⟨y, j, rfl⟩
  change inner ℝ (B i) (B j) = if (⟨B i, Set.mem_range_self i⟩ : Set.range B) =
      ⟨B j, Set.mem_range_self j⟩ then 1 else 0
  rw [(orthonormal_iff_ite.mp hB) i j]
  by_cases hij : (⟨B i, Set.mem_range_self i⟩ : Set.range B) = ⟨B j, Set.mem_range_self j⟩
  · rw [if_pos hij, if_pos ((key i j).mp hij)]
  · rw [if_neg hij, if_neg (fun h => hij ((key i j).mpr h))]

/-- **Completing a frame to an orthonormal basis, in interface form.**  For an orthonormal family
`B : ι → E` in a finite-dimensional real inner product space there is an orthonormal basis `b` of
`E` (indexed by a set `u ⊇ Set.range B`, with `b = Subtype.val`) whose elements include the `B i`.
This is the packaged form of `Orthonormal.exists_orthonormalBasis_extension` used by the frame
matching argument. -/
theorem exists_orthonormalBasis_extension_range {ι : Type*} [FiniteDimensional ℝ E] {B : ι → E}
    (hB : Orthonormal ℝ B) :
    ∃ (u : Finset E) (b : OrthonormalBasis u ℝ E),
      Set.range B ⊆ ↑u ∧ (∀ x : u, b x = (x : E)) ∧
      (∀ i : ι, ∃ hx : B i ∈ u, b ⟨B i, hx⟩ = B i) := by
  obtain ⟨u, b, hsub, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension (𝕜 := ℝ) (v := Set.range B)
      (orthonormal_subtype_range hB)
  refine ⟨u, b, hsub, fun x => congrFun hb x, fun i => ⟨hsub (Set.mem_range_self i), ?_⟩⟩
  exact congrFun hb ⟨B i, hsub (Set.mem_range_self i)⟩

end Work.Isotopy

/-!
## Verified call shapes (this session)

* `Orthonormal.exists_orthonormalBasis_extension (𝕜 := ℝ) (v := Set.range B)
    (orthonormal_subtype_range hB)` returns `u : Finset E` (a **Finset**, not a `Set`!), with
  `b : OrthonormalBasis ↥u ℝ E`, `hb : ⇑b = Subtype.val` and `hsub : Set.range B ⊆ ↑u`.
  Because the index is a `Finset`, the `Fintype ↥u` instance is automatic — so a wrapper that
  *states* the same existential must use `Finset E` and must **not** bundle a `Fintype` argument
  (stating it with `Set E` fails to synthesize `Fintype ↥u`).
* `hb : ⇑b = Subtype.val` is used as `congrFun hb x`, and the membership proof must be given
  explicitly in `congrFun hb ⟨B i, hsub (Set.mem_range_self i)⟩` (leaving the argument as a `_`
  placeholder fails).

Both are packaged as `Work.Isotopy.exists_orthonormalBasis_extension_range`.
-/

/-!
## Names confirmed for the conjugation step (single-point frame matching)

* `LinearIsometryEquiv.piLpCongrLeft (p : ℝ≥0∞) (𝕜) (E : Type*) (e : ι ≃ ι') :
    PiLp p (fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p (fun _ : ι' => E)` — the index-equivalence
  functoriality.  With `p = 2`, `𝕜 = E = ℝ` this is the needed reindexing
  `EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι'`.
* `OrthonormalBasis.repr_self (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i 1` — the closing identity, which together with
  `bC.repr.symm (bC.repr (C i)) = C i` gives `R (B i) = C i` for
  `R := bC.repr.symm ∘ reindex e ∘ bB.repr`.
* `Equiv.ofBijective`, `Equiv.ofInjective`, `LinearIsometryEquiv.ofEq` are available.

Two formalisations of `e : ↥u ≃ ↥w` (with `e ⟨B i, ·⟩ = ⟨C i, hCw i⟩`):

1. *Index route*: define `f : ↥u → ↥w` by cases on `x.1 ∈ Set.range B` (extracting the index with
   `Classical.choose`), pair the complements via `Fintype.card_eq.mp` from the common cardinality
   `finrank ℝ E`, and derive `Equiv.ofBijective f` (`hinj` gives injectivity on the range part; the
   two parts of the definition land in disjoint subsets).
2. *Span-and-complement route (recommended: no Finset/index bookkeeping at all)*: build `R`
   directly as `σ ⊕ τ` where `σ : span (Set.range B) ≃ₗ[ℝ] span (Set.range C)` sends `B i ↦ C i`
   (an explicit map `x ↦ ∑ i, ⟪B i, x⟫ • C i` on the span) and `τ` is *any* linear equivalence
   between the orthogonal complements, obtained from the equality of their `finrank`s
   (`finrank ℝ E - k`) by the equal-finrank existence lemma.  Assemble
   `R x = σ (proj_{span B} x) + τ (proj_{(span B)ᗮ} x)` with the orthogonal projections, and
   `R⁻¹ y = σ⁻¹ (proj_{span C} y) + τ⁻¹ (proj_{(span C)ᗮ} y)`; the identities
   `proj_{span C} (σ z) = σ z`, `proj_{span C} (τ w) = 0` and the orthogonal decomposition
   `E = span B ⊕ (span B)ᗮ` give `R⁻¹ ∘ R = id`.  Note `σ` and `τ` need only be *linear
   equivalences*, not isometries: the frame-matching statement does not require `R` to be an
   isometry.
-/
