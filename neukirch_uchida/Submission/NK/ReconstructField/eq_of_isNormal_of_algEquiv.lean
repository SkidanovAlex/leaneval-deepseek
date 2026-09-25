import Mathlib

namespace NK.ReconstructField

/-- **Key step.** If `M ⊆ K'` is a normal extension of `ℚ` (as an intermediate field) and
`F ⊆ K'` is any intermediate field that is `ℚ`-isomorphic to `M`, then `F ≤ M`.

The proof shows that the image of any element `x ∈ M` under the isomorphism, viewed in `K'`,
is a root of `minpoly ℚ x`; all roots of `minpoly ℚ x` lie in `M` because `M/ℚ` is normal. -/
lemma le_of_isNormal_of_algEquiv {K' : Type*} [Field K'] [Algebra ℚ K']
    {M F : IntermediateField ℚ K'} [Normal ℚ M] (e : ↥M ≃ₐ[ℚ] ↥F) : F ≤ M := by
  have hM : Normal ℚ M := inferInstance
  have key : ∀ x : ↥M, ((e x : ↥F) : K') ∈ (M : Set K') := by
    intro x
    -- The composite of `e` with the inclusion of `F` in `K'`, as a ring homomorphism.
    let Φ : ↥M →+* K' := (algebraMap ↥F K').comp (e : ↥M →+* ↥F)
    have hsq : (algebraMap ℚ K').comp (RingHom.id ℚ) = Φ.comp (algebraMap ℚ ↥M) := by
      ext q
      show algebraMap ℚ K' q = algebraMap ↥F K' (e (algebraMap ℚ ↥M q))
      rw [AlgEquiv.commutes e q]
      exact (RingHom.map_rat_algebraMap (algebraMap ↥F K') q).symm
    -- `Φ x` is a root of `minpoly ℚ x` in `K'`.
    have hA : (Polynomial.aeval ((e x : ↥F) : K')) (minpoly ℚ x) = 0 := by
      have h1 := Polynomial.map_aeval_eq_aeval_map (R := ℚ) (S := ↥M) (T := ℚ) (U := K')
        (φ := RingHom.id ℚ) (ψ := Φ) hsq (minpoly ℚ x) x
      simp only [Polynomial.map_id] at h1
      rw [minpoly.aeval, map_zero] at h1
      exact h1.symm
    have hmem : ((e x : ↥F) : K') ∈ (minpoly ℚ x).aroots K' := by
      rw [Polynomial.mem_aroots]
      exact ⟨minpoly.ne_zero (Normal.isIntegral hM x), hA⟩
    -- Every root of `minpoly ℚ x` in `K'` already lies in `M`.
    have hsub : ∀ a ∈ (minpoly ℚ x).aroots K', a ∈ (M : Set K') := by
      intro a ha
      have hsplitM : ((minpoly ℚ x).map (algebraMap ℚ ↥M)).Splits := Normal.splits hM x
      have hcomp : (algebraMap ↥M K').comp (algebraMap ℚ ↥M) = algebraMap ℚ K' :=
        RingHom.ext fun q => RingHom.map_rat_algebraMap (algebraMap ↥M K') q
      have hinj : Function.Injective (algebraMap ↥M K') := fun a b h => Subtype.ext h
      have hroots := Polynomial.Splits.roots_map_of_injective hsplitM hinj
      have ha2 : a ∈ (Polynomial.map (algebraMap ↥M K')
          ((minpoly ℚ x).map (algebraMap ℚ ↥M))).roots := by
        rw [Polynomial.map_map, hcomp]
        exact ha
      obtain ⟨b, _hb, hbm⟩ := Multiset.mem_map.mp (hroots ▸ ha2)
      rw [← hbm]
      exact b.2
    exact hsub _ hmem
  intro y hy
  simpa using key (e.symm ⟨y, hy⟩)

theorem eq_of_isNormal_of_algEquiv {K' : Type*} [Field K'] [Algebra ℚ K']
    {M : IntermediateField ℚ K'} [Normal ℚ M] (F : IntermediateField ℚ K')
    (e : ↥M ≃ₐ[ℚ] ↥F) : F = M := by
  haveI : Normal ℚ F := Normal.of_algEquiv e
  exact le_antisymm (le_of_isNormal_of_algEquiv e) (le_of_isNormal_of_algEquiv e.symm)

end NK.ReconstructField
