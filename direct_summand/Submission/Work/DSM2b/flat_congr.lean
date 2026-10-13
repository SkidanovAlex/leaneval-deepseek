import Mathlib

namespace Work.DSM2b

universe u

/-- Flatness is invariant under a ring isomorphism together with a compatible additive
equivalence of the modules.  `hf` says that `f` intertwines the two scalar actions through `e`.

Proof sketch: use the equational criterion `Module.Flat.iff_forall_isTrivialRelation`; a relation
`∑ fᵢ • xᵢ = 0` in `M` is carried by `e`/`f` to a relation in `N`, and a trivialisation of the
latter is carried back. -/
theorem flat_congr {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (hf : ∀ (r : R) (m : M), f (r • m) = e r • f m)
    (h : Module.Flat R M) : Module.Flat S N := by
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l g x hx
  -- Transport the relation `∑ gᵢ • xᵢ = 0` from `N` to `M` along `e` and `f`.
  have hsum : ∑ i, e.symm (g i) • f.symm (x i) = 0 := by
    apply f.injective
    rw [map_zero]
    calc f (∑ i, e.symm (g i) • f.symm (x i))
        = ∑ i, f (e.symm (g i) • f.symm (x i)) := by simp
      _ = ∑ i, e (e.symm (g i)) • f (f.symm (x i)) :=
            Finset.sum_congr rfl fun i _ => hf _ _
      _ = ∑ i, g i • x i := by simp
      _ = 0 := hx
  -- Trivialise it in `M` by flatness, then transport the trivialisation back.
  obtain ⟨k, a, z, hz, haz⟩ := Module.Flat.iff_forall_isTrivialRelation.mp h hsum
  have hz' : ∀ i, f.symm (x i) = ∑ j, a i j • z j := fun i => by simpa using hz i
  have haz' : ∀ j, ∑ i, e.symm (g i) * a i j = 0 := fun j => by simpa using haz j
  refine ⟨k, fun i j => e (a i j), fun j => f (z j), ?_, ?_⟩
  · intro i
    have h1 : f (f.symm (x i)) = ∑ j, e (a i j) • f (z j) := by
      rw [hz' i, map_sum]
      exact Finset.sum_congr rfl fun j _ => hf _ _
    simpa using h1
  · intro j
    have h1 : (∑ i, g i * e (a i j)) = e (∑ i, e.symm (g i) * a i j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul, RingEquiv.apply_symm_apply]
    rw [h1, haz' j, map_zero]

end Work.DSM2b
