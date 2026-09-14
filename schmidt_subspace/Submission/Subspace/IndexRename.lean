import Mathlib
import Submission.Subspace.Index

/-!
# Naturality of the index under an injective change of variables

The index `Ind_{α,r}(P)` is defined by the Taylor expansion of `P` at `α` together with the
weighted value `∑ i, m i / r i` of a multi-index.  Both are compatible with an injective
change of variables `rename e`:

`Ind_{β, r}(rename e P) = Ind_{β ∘ e, r ∘ e}(P)`,

which is what allows the Roth induction to pass between polynomials in `n` variables and
polynomials in `n + 1` variables which do not involve the last one (or the first one).
-/

open scoped BigOperators

namespace Submission.Subspace

open Commons.Algebra.MvPolynomial (indexWt indexTay indexSet)

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- The Taylor shift commutes with a change of variables. -/
lemma indexTay_rename (e : ι → κ) (β : κ → K) (P : MvPolynomial ι K) :
    indexTay β (MvPolynomial.rename e P) = MvPolynomial.rename e (indexTay (β ∘ e) P) := by
  have hcomp : (MvPolynomial.rename e).comp
        (MvPolynomial.aeval (fun i => MvPolynomial.C (β (e i)) + MvPolynomial.X i)) =
      MvPolynomial.aeval (fun i => MvPolynomial.C (β (e i)) + MvPolynomial.X (e i)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [MvPolynomial.rename_X]
  have h1 : MvPolynomial.aeval ((fun j : κ => MvPolynomial.C (β j) + MvPolynomial.X j) ∘ e) P =
      MvPolynomial.aeval (fun i => MvPolynomial.C (β (e i)) + MvPolynomial.X (e i)) P := rfl
  rw [indexTay, indexTay, MvPolynomial.aeval_rename, h1, ← hcomp]
  rfl

omit [DecidableEq ι] in
/-- The weighted value is compatible with an injective change of variables. -/
lemma indexWt_mapDomain (r : κ → ℕ) (e : ι → κ) (he : Function.Injective e)
    (m : ι →₀ ℕ) :
    indexWt (r ∘ e) m = indexWt r (Finsupp.mapDomain e m) := by
  rw [indexWt, indexWt]
  have hrestrict : (∑ j : κ, ((Finsupp.mapDomain e m) j : ℝ) / (r j : ℝ))
      = ∑ j ∈ Finset.univ.image e, ((Finsupp.mapDomain e m) j : ℝ) / (r j : ℝ) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ hj
    rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · intro hmem
      obtain ⟨a, rfl⟩ := hmem
      exact hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  rw [hrestrict, Finset.sum_image (fun a _ b _ hab => he hab)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Finsupp.mapDomain_apply he]

omit [DecidableEq ι] in
/-- **The index is natural under an injective change of variables.** -/
theorem index_rename (e : ι → κ) (he : Function.Injective e) (β : κ → K) (r : κ → ℕ)
    (P : MvPolynomial ι K) :
    index β r (MvPolynomial.rename e P) = index (β ∘ e) (r ∘ e) P := by
  have hsupp : (indexTay β (MvPolynomial.rename e P)).support
      = (indexTay (β ∘ e) P).support.image (Finsupp.mapDomain e) := by
    rw [indexTay_rename, MvPolynomial.support_rename_of_injective (f := e) he]
  rw [index_def, index_def]
  have hset : indexSet β r (MvPolynomial.rename e P) = indexSet (β ∘ e) (r ∘ e) P := by
    ext t
    rw [indexSet, hsupp]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [Finset.mem_image] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      exact ⟨m', hm', (indexWt_mapDomain r e he m').symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨Finsupp.mapDomain e m, Finset.mem_image.mpr ⟨m, hm, rfl⟩,
        indexWt_mapDomain r e he m⟩
  rw [hset]

/-- **The index of a tensor product is the sum of the indices.**  If `Φ` and `Ψ` are
polynomials in two disjoint sets of variables (embedded into a common ring by `rename e₁`,
`rename e₂`), then the index of their product is the sum of the two individual indices, computed
with the restricted point and weights. -/
theorem index_mul_rename {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e₁ : ι → κ) (e₂ : ι' → κ) (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (β : κ → K) (r : κ → ℕ) (Φ : MvPolynomial ι K) (Ψ : MvPolynomial ι' K)
    (hΦ : Φ ≠ 0) (hΨ : Ψ ≠ 0) :
    index β r (MvPolynomial.rename e₁ Φ * MvPolynomial.rename e₂ Ψ) =
      index (β ∘ e₁) (r ∘ e₁) Φ + index (β ∘ e₂) (r ∘ e₂) Ψ := by
  have hne₁ : MvPolynomial.rename e₁ Φ ≠ 0 := (MvPolynomial.rename_injective e₁ he₁).ne hΦ
  have hne₂ : MvPolynomial.rename e₂ Ψ ≠ 0 := (MvPolynomial.rename_injective e₂ he₂).ne hΨ
  have h1 : index β r (MvPolynomial.rename e₁ Φ) = index (β ∘ e₁) (r ∘ e₁) Φ :=
    index_rename e₁ he₁ β r Φ
  have h2 : index β r (MvPolynomial.rename e₂ Ψ) = index (β ∘ e₂) (r ∘ e₂) Ψ :=
    index_rename e₂ he₂ β r Ψ
  rw [index_mul β r _ _ hne₁ hne₂, h1, h2]

end Submission.Subspace
