import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.BSLit.Wielandt

/-- For a finite group `F` and a finite-dimensional `𝔽_p`-representation `ρ` of `F` with
`p ∤ |F|`, the module `ρ.asModule` underlying `ρ` is a direct summand of a free `𝔽_p[F]`-module of
finite rank: there are `n : ℕ` and an idempotent `𝔽_p[F]`-endomorphism `e` of
`P := Fin n → MonoidAlgebra (ZMod p) F` with `LinearMap.range e ≃ₗ ρ.asModule`.

Route (Maschke).  Put `n := Module.finrank (ZMod p) V` and
`P := Fin n → MonoidAlgebra (ZMod p) F`.  Fix a basis `b : Fin n → V` (e.g.
`Module.finBasis (ZMod p) V`), transported along `ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod p] V`.
The `𝔽_p[F]`-linear map `φ : P → ρ.asModule`, `φ f = ∑ i, f i • b i`, is surjective (the images of
the standard basis vectors are the basis).  Since `p ∤ |F|`, `|F|` is invertible in `𝔽_p`, so by
Maschke (`Submodule.exists_isCompl` in `Mathlib.RepresentationTheory.Maschke`, requiring
`[NeZero (Nat.card F : ZMod p)]`) the submodule `ker φ` has a complement `K` in `P`; the projection
of `P` onto `K` along `ker φ` (e.g. `Submodule.projectionOnto` composed with `K.subtype`) is an
idempotent `e` with `LinearMap.range e = K ≅ P/ker φ ≃ ρ.asModule`. -/
theorem ExistsProjector {F V : Type*} [Group F] [Fintype F] {p : ℕ} [Fact p.Prime]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) F V) (hcop : ¬ p ∣ Nat.card F) :
    ∃ (n : ℕ) (e : (Fin n → MonoidAlgebra (ZMod p) F) →ₗ[MonoidAlgebra (ZMod p) F]
        (Fin n → MonoidAlgebra (ZMod p) F)),
      e * e = e ∧
      Nonempty (↥(LinearMap.range e) ≃ₗ[MonoidAlgebra (ZMod p) F] ρ.asModule) := by
  -- `p ∤ |F|` means `|F|` is nonzero (hence invertible) in `𝔽_p`: Maschke's hypothesis.
  haveI : NeZero (Nat.card F : ZMod p) :=
    ⟨fun h => hcop ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  set R := MonoidAlgebra (ZMod p) F with hR
  set n := Module.finrank (ZMod p) ρ.asModule with hn
  -- A `𝔽_p`-basis gives a surjection from the free `𝔽_p[F]`-module `Fin n → R` onto `ρ.asModule`.
  set b : Module.Basis (Fin n) (ZMod p) ρ.asModule := Module.finBasis (ZMod p) ρ.asModule with hb
  set φ : (Fin n → R) →ₗ[R] ρ.asModule :=
    Fintype.linearCombination R (fun i : Fin n => (b i : ρ.asModule)) with hφ
  have hsurj : Function.Surjective φ := by
    intro m
    refine ⟨fun i => algebraMap (ZMod p) R (b.repr m i), ?_⟩
    rw [hφ, Fintype.linearCombination_apply]
    conv_rhs => rw [← b.sum_repr m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IsScalarTower.algebraMap_smul R]
  -- Maschke: `ker φ` has a complement `K` in the free module `Fin n → R`.
  obtain ⟨K, hK⟩ := MonoidAlgebra.Submodule.exists_isCompl (V := Fin n → R) (LinearMap.ker φ)
  -- Project onto `K` along `ker φ`; it is idempotent with range `K ≅ P ⧸ ker φ ≅ ρ.asModule`.
  refine ⟨n, K.projection (LinearMap.ker φ) hK.symm, ?_, ?_⟩
  · exact Submodule.isIdempotentElem_projection hK.symm
  · refine ⟨(LinearEquiv.ofEq _ _ (Submodule.range_projection hK.symm)) ≪≫ₗ
      (Submodule.quotientEquivOfIsCompl (LinearMap.ker φ) K hK).symm ≪≫ₗ
      φ.quotKerEquivOfSurjective hsurj⟩

end Work.BSLit.Wielandt
