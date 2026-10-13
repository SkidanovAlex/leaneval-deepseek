import Mathlib

namespace Work.DSM5c.Eta

/-- **Descent of a `W`-algebra map along an injective `W`-algebra map, on an `adjoin`.**

Let `g : B →ₐ[W] C'` and `ι : C →ₐ[W] C'` with `ι` injective, and suppose that `g` carries a
generating set `G ⊆ B` into the image of `ι`.  Then there is a `W`-algebra map
`f : Algebra.adjoin W G →ₐ[W] C` with `ι (f x) = g x` for all `x` in the adjoin.

Proof: the image of `ι` is a subring of `C'` containing `g (algebraMap W B w) = algebraMap W C' w`,
so `g` maps `Algebra.adjoin W G` into it (`Algebra.adjoin_le_iff`); choose preimages and use the
injectivity of `ι` to show that the resulting function is additive, multiplicative and `W`-linear.
This is the abstract form of the descent step of the chart map `η` of the M5c node (there
`C = D_S`, `C' = D_S[1/v_S]`, `B = W_{t_S}`, `G = chartGens t S` and `Algebra.adjoin W G` is
definitionally `chartRing t S`). -/
theorem exists_algHom_of_le_range {W B C C' : Type} [CommRing W] [CommRing B] [Algebra W B]
    [CommRing C] [CommRing C'] [Algebra W C] [Algebra W C'] (ι : C →ₐ[W] C')
    (hι : Function.Injective ι) (g : B →ₐ[W] C') {G : Set B}
    (hG : ∀ x ∈ G, ∃ d : C, ι d = g x) :
    ∃ f : Algebra.adjoin W G →ₐ[W] C,
      ∀ x : Algebra.adjoin W G, ι (f x) = g (x : B) := by
  -- The image of `ι` contains `g x` for every generator `x ∈ G`, hence — being a subalgebra —
  -- contains `g` of everything in `Algebra.adjoin W G`.
  have hle : Algebra.adjoin W G ≤ Subalgebra.comap g ι.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨d, hd⟩ := hG x hx
    exact (Subalgebra.mem_comap ι.range g x).mpr ((AlgHom.mem_range ι).mpr ⟨d, hd⟩)
  have hmem : ∀ x : Algebra.adjoin W G, g (x : B) ∈ ι.range :=
    fun x => (Subalgebra.mem_comap ι.range g (x : B)).mp (hle x.2)
  -- `g` corestricted to the range of `ι`, and the inverse of the injective `ι` onto its range.
  let gA : Algebra.adjoin W G →ₐ[W] C' := g.comp (Algebra.adjoin W G).val
  let φ : Algebra.adjoin W G →ₐ[W] ι.range := gA.codRestrict ι.range hmem
  let ee : C ≃ₐ[W] ι.range := AlgEquiv.ofInjective ι hι
  let e' : ι.range →ₐ[W] C := ee.symm
  -- On the range of `ι`, the coercion back to `C'` is exactly `ι ∘ e'`.
  have key : ∀ y : ι.range, (y : C') = ι (e' y) := by
    intro y
    have h : (↑(ee (e' y)) : C') = ι (e' y) := AlgEquiv.ofInjective_apply ι hι (e' y)
    have h1 : ee (e' y) = y := by
      change ee (ee.symm y) = y
      exact AlgEquiv.apply_symm_apply ee y
    rw [h1] at h
    exact h
  refine ⟨e'.comp φ, ?_⟩
  intro x
  have keyx : (↑(φ x) : C') = ι (e' (φ x)) := key (φ x)
  rw [AlgHom.comp_apply]
  rw [← keyx]
  rfl

end Work.DSM5c.Eta
