import Mathlib
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep.Orthonormal

/-!
# A Hilbert basis of the finite `ℓ²`-sum of `ℓ²(G)`

`δ_g ∈ ℓ²(G)` is the indicator function of the singleton `{g}`; the family `g ↦ δ_g` is a
Hilbert basis of `ℓ²(G)` (`Work.ORVonNeumann.Rep.deltaGHilbertBasis`).  Placing `δ_g` in the
`i`-th coordinate of the finite `ℓ²`-sum `PiLp 2 (fun _ : Fin n => ℓ²(G))` produces an
orthonormal family indexed by `G × Fin n`, and its span is dense: an element of the sum is the
finite sum `∑ i, PiLp.single 2 i (x i)` of its coordinates, and each coordinate lies in the
closed span of the `δ_g`.  Hence

* `Work.ORP311.piLp_l2_hilbertBasis` — there is a Hilbert basis of
  `PiLp 2 (fun _ : Fin n => ℓ²(G))` indexed by `G × Fin n`.

The intermediate results are `Work.ORP311.inner_piLp_single` (the inner product of a
`PiLp.single` only sees one coordinate), `Work.ORP311.orthonormal_piLpBasisVec` (orthonormality
of the family) and `Work.ORP311.span_piLpBasisVec_orthogonal_eq_bot` (its span has trivial
orthogonal complement).
-/

namespace Work.ORP311

open Work.ORVonNeumann

/-- The `i`-th coordinate copy `δ_g` of the finite `ℓ²`-sum `PiLp 2 (fun _ : Fin n => ℓ²(G))`,
indexed by the pair `p = (g, i)`. -/
noncomputable def piLpBasisVec (G : Type*) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (p : G × Fin n) :
    PiLp 2 (fun _ : Fin n => l2 G) :=
  PiLp.single 2 p.2 (Rep.deltaG p.1)

@[simp]
theorem piLpBasisVec_apply {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (p : G × Fin n) :
    piLpBasisVec G n p = PiLp.single 2 p.2 (Rep.deltaG p.1) := rfl

/-- The inner product of an element of the sum supported in the `i`-th coordinate only sees the
`i`-th coordinate of the second argument. -/
theorem inner_piLp_single {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (i : Fin n) (a : l2 G)
    (y : PiLp 2 (fun _ : Fin n => l2 G)) :
    inner ℂ (PiLp.single (β := fun _ : Fin n => l2 G) 2 i a) y = inner ℂ a (y i) := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [PiLp.single_eq_of_ne (p := 2) (β := fun _ : Fin n => l2 G) hji a]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The family `p ↦ PiLp.single 2 p.2 (δ_{p.1})` is orthonormal.** -/
theorem orthonormal_piLpBasisVec {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) :
    Orthonormal ℂ (piLpBasisVec G n) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨g, i⟩ ⟨h, j⟩
  show inner ℂ (PiLp.single 2 i (Rep.deltaG g))
      (PiLp.single (β := fun _ : Fin n => l2 G) 2 j (Rep.deltaG h))
    = if (g, i) = (h, j) then 1 else 0
  rw [inner_piLp_single i (Rep.deltaG g) (PiLp.single 2 j (Rep.deltaG h))]
  by_cases hij : i = j
  · subst hij
    rw [PiLp.single_eq_same]
    by_cases hgh : g = h
    · subst hgh
      rw [if_pos rfl, Rep.inner_deltaG_self]
    · refine Eq.trans (Rep.inner_deltaG_of_ne hgh) ?_
      simp [hgh]
  · rw [PiLp.single_eq_of_ne (p := 2)
        (β := fun _ : Fin n => l2 G) hij (Rep.deltaG h), inner_zero_right]
    simp [hij]

/-- **The closed span of the family `p ↦ PiLp.single 2 p.2 (δ_{p.1})` is everything.** -/
theorem span_piLpBasisVec_orthogonal_eq_bot {G : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) :
    (Submodule.span ℂ (Set.range (piLpBasisVec G n)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_orthogonal] at hx
  -- every coordinate of `x` is orthogonal to every `δ_g`, hence is zero
  have key : ∀ i : Fin n, x i = 0 := by
    intro i
    have h1 : ∀ g : G, inner ℂ (Rep.deltaG g) (x i) = 0 := by
      intro g
      have h := hx (piLpBasisVec G n (g, i))
        (Submodule.subset_span (Set.mem_range_self (g, i)))
      rwa [piLpBasisVec_apply, inner_piLp_single i (Rep.deltaG g) x] at h
    have h2 : Rep.deltaGHilbertBasis.repr (x i) = 0 := by
      apply lp.ext
      funext g
      rw [HilbertBasis.repr_apply_apply]
      simpa using h1 g
    have h3 : x i = 0 := by
      have := congrArg (Rep.deltaGHilbertBasis.repr.symm) h2
      simpa using this
    exact h3
  exact PiLp.ext (fun i => by simp [key i])

theorem piLp_l2_hilbertBasis {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) :
    Nonempty (HilbertBasis (G × Fin n) ℂ (PiLp 2 (fun _ : Fin n => Work.ORVonNeumann.l2 G))) :=
  ⟨HilbertBasis.mkOfOrthogonalEqBot (orthonormal_piLpBasisVec n)
    (span_piLpBasisVec_orthogonal_eq_bot n)⟩

end Work.ORP311
