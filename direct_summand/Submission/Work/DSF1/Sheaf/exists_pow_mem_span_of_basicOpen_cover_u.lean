import Mathlib

/-!
# A power of `g` lies in the span when `D(g)` is covered by the `D(f i)` (universe-polymorphic)

This is the same statement as `Work.DSF1.Sheaf.exists_pow_mem_span_of_basicOpen_cover`, but
with the index type at the universe of the scheme: everything is as in the reference proof,
which reduces (via `X ≅ Spec Γ(X,⊤)`) to the ring-theoretic statement that
`D(g) ⊆ ⋃ D(f i)` implies `g ∈ √(f i)`.
-/

namespace Work.DSF1.Sheaf

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

/-- Ring-theoretic form: in `Spec R`, if the basic open of `g` is covered by the basic opens
of the family `f`, then some power of `g` lies in the ideal spanned by the family. -/
lemma primeSpectrum_exists_pow_mem_span_of_basicOpen_cover {R : Type u} [CommRing R]
    {ι : Type u} (f : ι → R) (g : R)
    (hcov : PrimeSpectrum.basicOpen g ≤ ⨆ i, PrimeSpectrum.basicOpen (f i)) :
    ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range f) := by
  have key : PrimeSpectrum.zeroLocus (Set.range f) ⊆ PrimeSpectrum.zeroLocus ({g} : Set R) := by
    intro x hx
    rw [PrimeSpectrum.mem_zeroLocus] at hx ⊢
    by_contra hxg
    rw [Set.singleton_subset_iff] at hxg
    have hx1 : x ∈ PrimeSpectrum.basicOpen g := (PrimeSpectrum.mem_basicOpen g x).mpr hxg
    have hx2 : x ∈ (⨆ i, PrimeSpectrum.basicOpen (f i) :
        TopologicalSpace.Opens (PrimeSpectrum R)) := hcov hx1
    rw [TopologicalSpace.Opens.mem_iSup] at hx2
    obtain ⟨i, hi⟩ := hx2
    exact ((PrimeSpectrum.mem_basicOpen (f i) x).mp hi) (hx (Set.mem_range_self i))
  have h2 : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span ({g} : Set R) : Set R) := by
    simpa only [PrimeSpectrum.zeroLocus_span] using key
  have h3 : Ideal.span ({g} : Set R) ≤ (Ideal.span (Set.range f)).radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff (Ideal.span (Set.range f))
      (Ideal.span {g})).mp h2
  exact Ideal.mem_radical_iff.mp (h3 (Ideal.subset_span (Set.mem_singleton g)))

/-- If `D (g)` is covered by the family of basic opens `D (f i)` on an affine scheme, then some
power of `g` lies in the ideal spanned by the `f i`. -/
theorem exists_pow_mem_span_of_basicOpen_cover_u {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] {ι : Type u}
    (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤))) (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) :
    ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range f) := by
  refine primeSpectrum_exists_pow_mem_span_of_basicOpen_cover f g ?_
  refine fun x hx => ?_
  let y : X := X.isoSpec.inv x
  have hyx : X.toSpecΓ y = x := by
    show X.isoSpec.hom (X.isoSpec.inv x) = x
    exact Scheme.inv_hom_apply X.isoSpec x
  have hy_g : y ∈ X.basicOpen g := by
    have h2 : X.toSpecΓ y ∈ PrimeSpectrum.basicOpen g := by
      rw [hyx]; exact hx
    rw [← Scheme.toSpecΓ_preimage_basicOpen X g]
    exact h2
  have hy_sup : y ∈ ⨆ i, X.basicOpen (f i) := hcov hy_g
  obtain ⟨i, hi⟩ :=
    (TopologicalSpace.Opens.mem_iSup (s := fun i => X.basicOpen (f i))).mp hy_sup
  refine le_iSup (fun i => PrimeSpectrum.basicOpen (f i)) i ?_
  have h2 : X.toSpecΓ y ∈ PrimeSpectrum.basicOpen (f i) := by
    have h3 := hi
    rw [← Scheme.toSpecΓ_preimage_basicOpen X (f i)] at h3
    exact h3
  rwa [hyx] at h2

end Work.DSF1.Sheaf
