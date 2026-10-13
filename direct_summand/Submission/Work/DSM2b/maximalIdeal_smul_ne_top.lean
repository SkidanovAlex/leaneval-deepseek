import Mathlib

namespace Work.DSM2b

universe u

/-- For an `R`-algebra `S` and an `S`-module `M` which is also an `R`-module compatibly
(`IsScalarTower R S M`), the `S`-submodule `(I.map (algebraMap R S)) • ⊤ ⊆ M` is everything
iff the `R`-submodule `I • ⊤ ⊆ M` is everything.  (Restriction of scalars is an order
embedding carrying `⊤` to `⊤`; `Ideal.smul_restrictScalars` identifies
`((I.map (algebraMap R S)) • ⊤).restrictScalars R` with `I • ⊤`.) -/
theorem smul_top_map_eq {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) :
    (I.map (algebraMap R S)) • (⊤ : Submodule S M) = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ := by
  have h1 : Submodule.restrictScalars R ((I.map (algebraMap R S)) • (⊤ : Submodule S M))
      = I • (⊤ : Submodule R M) := by
    rw [Ideal.smul_restrictScalars]; rfl
  have hT : Submodule.restrictScalars R (⊤ : Submodule S M) = (⊤ : Submodule R M) :=
    Submodule.restrictScalars_top (S := R) (R := S) (M := M)
  constructor
  · intro h
    rw [← h1, congrArg (Submodule.restrictScalars R) h, hT]
  · intro h
    apply Submodule.restrictScalars_injective R
    rw [h1, hT, h]

theorem maximalIdeal_smul_ne_top {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (π : R)
    (h : Module.FaithfullyFlat (R ⧸ Ideal.span {π}) (B ⧸ (Ideal.span {π}).map (algebraMap R B)))
    (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (hπ𝔪 : π ∈ 𝔪) :
    𝔪 • (⊤ : Submodule R B) ≠ ⊤ := by
  intro htop
  -- The image of `𝔪` in `R ⧸ (π)` is maximal (it contains the kernel of the quotient map).
  have hker : RingHom.ker (algebraMap R (R ⧸ Ideal.span {π})) ≤ 𝔪 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ𝔪)
  have hmax : (𝔪.map (algebraMap R (R ⧸ Ideal.span {π}))).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := algebraMap R (R ⧸ Ideal.span {π})) Ideal.Quotient.mk_surjective hker
  -- Faithful flatness of `B ⧸ (π)` over `R ⧸ (π)` makes the corresponding submodule proper.
  have hne : (𝔪.map (algebraMap R (R ⧸ Ideal.span {π}))) •
      (⊤ : Submodule (R ⧸ Ideal.span {π})
        (B ⧸ (Ideal.span {π}).map (algebraMap R B))) ≠ ⊤ :=
    h.submodule_ne_top hmax
  -- Descend from the `(R ⧸ (π))`-submodule to the `R`-submodule.
  have key := smul_top_map_eq (R := R) (S := R ⧸ Ideal.span {π})
    (M := B ⧸ (Ideal.span {π}).map (algebraMap R B)) 𝔪
  have hR : 𝔪 • (⊤ : Submodule R (B ⧸ (Ideal.span {π}).map (algebraMap R B))) ≠ ⊤ :=
    fun hh => hne (key.mpr hh)
  -- Push `𝔪 • ⊤ = ⊤` in `B` forward along the quotient `B ↠ B ⧸ (π)B`.
  have hmaps : (𝔪 • (⊤ : Submodule R B)).map
      ((Ideal.Quotient.mkₐ R ((Ideal.span {π}).map (algebraMap R B))).toLinearMap) = ⊤ := by
    rw [htop, Submodule.map_top, LinearMap.range_eq_top.mpr
      (Ideal.Quotient.mkₐ_surjective R ((Ideal.span {π}).map (algebraMap R B)))]
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr
      (Ideal.Quotient.mkₐ_surjective R ((Ideal.span {π}).map (algebraMap R B)))] at hmaps
  exact hR hmaps

end Work.DSM2b
