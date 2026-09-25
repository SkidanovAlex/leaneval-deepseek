import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.cardH2P_adicCompletion
import Submission.NK.NUV2.LC.exists_zeroPreserving_equiv_h2Profinite_of_homeomorph
import Submission.NK.Reconstruct.isHomeomorph_levelGalEquiv
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv
import Submission.NK.TowerRank.exists_numberField_completion_of_finiteDimensional

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.NUV2.LC.RouteB

universe u

/-! ## Two general tools -/

/-- **A homeomorphic group isomorphism is a continuous multiplication equivalence.** -/
noncomputable def continuousMulEquivOfIsHomeomorph {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃* H) (he : IsHomeomorph (e : G → H)) : G ≃ₜ* H :=
  ContinuousMulEquiv.mk' (he.homeomorph (e : G → H)) (fun x y => map_mul e x y)

/-- **The cardinality of the profinite cohomology is invariant under a topological isomorphism of
closed subgroups.**  This is the general-`p` form of
`NK.NUV2.LC.exists_zeroPreserving_equiv_h2Profinite_of_homeomorph`: the level systems of the two
colimits are matched by the isomorphism, and the induced map of colimits (`HTX.Phi`, inverse
`HTX.Psi`) is a bijection. -/
theorem natCard_h2Profinite_of_homeomorph {k k' κ κ' : Type u} [Field k] [Field k']
    [Algebra k k'] [IsSepClosure k k'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (H : Subgroup Gal(k'/k)) (J : Subgroup Gal(κ'/κ)) (p : ℕ) (e : ↥H ≃ₜ* ↥J) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := k) (K' := k') p H)
      = Nat.card (NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p J) :=
  Nat.card_congr
    { toFun := fun x => NK.NUV2.LC.HTX.Phi H J p e x
      invFun := fun y => NK.NUV2.LC.HTX.Psi H J p e y
      left_inv := fun x => NK.NUV2.LC.HTX.Psi_Phi H J p e x
      right_inv := fun y => NK.NUV2.LC.HTX.Phi_Psi H J p e y }

/-- **A separable closure transported across a ring isomorphism of the base field.**

If `C` is a separable closure of `B` and `e : A ≃+* B` is a ring isomorphism, then `C` is also a
separable closure of `A` when the `A`-algebra structure on `C` is `(algebraMap B C) ∘ e`. -/
theorem isSepClosure_of_ringEquiv {A B C : Type*} [Field A] [Field B] [Field C] [Algebra B C]
    [IsSepClosure B C] (e : A ≃+* B) :
    letI : Algebra A C := RingHom.toAlgebra ((algebraMap B C).comp (e : A →+* B))
    IsSepClosure A C := by
  letI : Algebra A C := RingHom.toAlgebra ((algebraMap B C).comp (e : A →+* B))
  have he : (algebraMap A C).comp (↑e.symm : B →+* A)
      = (↑(RingEquiv.refl C) : C →+* C).comp (algebraMap B C) := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.refl_apply]
    rw [show (algebraMap A C) = (algebraMap B C).comp (e : A →+* B) from rfl,
      RingHom.comp_apply]
    simp
  exact ⟨IsSepClosure.sep_closed B,
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl C) he⟩

/-! ## The local Brauer computation at `M` -/

/-- **The local Brauer computation at a finite extension of a local field, realised at a number
field.**  Let `κ = 𝔮.adicCompletion L` be the completion of a number field at a finite prime, `κ'`
a separable closure of `κ`, and `M/κ` a finite Galois subextension containing a primitive `p`-th
root of unity.  Then the profinite cohomology `H²(Gal(κ'/M), Z/p)` has exactly `p` elements.

Proof: `M` is the completion of a finite extension `L'` of `L` at a prime `q` above `𝔮`
(`exists_numberField_completion_of_finiteDimensional`); the identification of the two separable
closures `κ'` of `M` and `SeparableClosure (q.adicCompletion L')` of `q.adicCompletion L'` gives a
topological isomorphism `Gal(κ'/M) ≃ₜ* Gal(κ'_{q}/κ_q)`, along which the cardinality is transported
(`h2CardTransport`), and there it is `card_h2P_top_adicCompletion`. -/
theorem card_h2P_fixingSubgroup (p : ℕ) (hp : p.Prime) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)))
    (hζ : ∃ ζ : ↥M, IsPrimitiveRoot ζ p) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p M.fixingSubgroup) = p := by
  have hreal : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
      (hq : q.asIdeal.LiesOver 𝔮.asIdeal),
      letI : Algebra (𝔮.adicCompletion L) (q.adicCompletion L') :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔮 q hq)
      Nonempty (↥M.toIntermediateField ≃ₐ[𝔮.adicCompletion L] q.adicCompletion L') :=
    NK.TowerRank.exists_numberField_completion_of_finiteDimensional (K := L) 𝔮 M.toIntermediateField
  obtain ⟨L', hL'f, hL'nf, hL'a, q, hq, ⟨φ⟩⟩ := hreal
  letI : Field L' := hL'f
  letI : NumberField L' := hL'nf
  letI : Algebra L L' := hL'a
  letI : Algebra (𝔮.adicCompletion L) (q.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔮 q hq)
  -- A primitive `p`-th root of unity in the completion
  have hζ' : ∃ ζ : q.adicCompletion L', IsPrimitiveRoot ζ p := by
    obtain ⟨ζ, hζp⟩ := hζ
    refine ⟨φ.toRingEquiv ζ, ?_, ?_⟩
    · rw [← map_pow, hζp.pow_eq_one, map_one]
    · intro l hl
      exact hζp.dvd_of_pow_eq_one l (φ.toRingEquiv.injective (by rw [map_pow, hl, map_one]))
  -- ## The two separable closures
  let φh : ↥M.toIntermediateField →+* q.adicCompletion L' := φ.toRingEquiv.toRingHom
  letI : Algebra ↥M.toIntermediateField (SeparableClosure (q.adicCompletion L')) :=
    RingHom.toAlgebra
      ((algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).comp φh)
  haveI hscM : IsSepClosure ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L)) :=
    ⟨IsSepClosure.sep_closed (𝔮.adicCompletion L), inferInstance⟩
  haveI hscL : IsSepClosure ↥M.toIntermediateField (SeparableClosure (q.adicCompletion L')) :=
    isSepClosure_of_ringEquiv (C := SeparableClosure (q.adicCompletion L')) φ.toRingEquiv
  let ψ : SeparableClosure (𝔮.adicCompletion L) ≃ₐ[↥M.toIntermediateField]
      SeparableClosure (q.adicCompletion L') :=
    IsSepClosure.equiv ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L))
      (SeparableClosure (q.adicCompletion L'))
  -- ## The base compatibility of ψ (and hence of σ)
  have h1φ : ∀ c : q.adicCompletion L', φh (φ.symm.toRingEquiv c) = c :=
    fun c => by
      change φ.toRingEquiv.toRingHom (φ.toRingEquiv.symm c) = c
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact (φ.toRingEquiv).apply_symm_apply c
  have hstruct : ∀ a : ↥M.toIntermediateField,
      (algebraMap ↥M.toIntermediateField (SeparableClosure (q.adicCompletion L')) a)
        = (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))) (φh a) :=
    fun a => rfl
  have hψ : (algebraMap ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L))).range.map
      ψ.toRingHom = (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).range := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hx
      exact ⟨φh a, ((ψ.commutes a).trans (hstruct a)).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L))
        (φ.symm.toRingEquiv c), ⟨_, rfl⟩,
        (ψ.commutes (φ.symm.toRingEquiv c)).trans (by rw [hstruct, h1φ c])⟩
  let σ : SeparableClosure (q.adicCompletion L') ≃+* SeparableClosure (𝔮.adicCompletion L) :=
    ψ.symm.toRingEquiv
  have hσ : Submission.NeukirchUchida.MapsBase
      (algebraMap ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L)))
      (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))) σ :=
    Submission.NeukirchUchida.subring_map_symm_of_map_eq ψ.toRingEquiv
      (algebraMap ↥M.toIntermediateField (SeparableClosure (𝔮.adicCompletion L))).range
      (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).range hψ
  -- ## The topological isomorphism `↥M.fixingSubgroup ≃ₜ* Gal(κ'_q/κ_q)`
  have hfix := NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv (K := 𝔮.adicCompletion L)
    (Ω := SeparableClosure (𝔮.adicCompletion L)) M.toIntermediateField
  have hconj := NK.NeukirchUchida.isHomeomorph_conjHomEquiv σ hσ
  let e1 : ↥(IntermediateField.fixingSubgroup M.toIntermediateField) ≃ₜ*
      Gal(SeparableClosure (𝔮.adicCompletion L)/↥M.toIntermediateField) :=
    continuousMulEquivOfIsHomeomorph (IntermediateField.fixingSubgroupEquiv M.toIntermediateField) hfix
  let e2 : Gal(SeparableClosure (𝔮.adicCompletion L)/↥M.toIntermediateField) ≃ₜ*
      Gal(SeparableClosure (q.adicCompletion L')/q.adicCompletion L') :=
    continuousMulEquivOfIsHomeomorph (Submission.NeukirchUchida.conjHomEquiv hσ) hconj
  -- ## The transport to the completion model
  have hcl : IsClosed (M.fixingSubgroup :
      Set Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)) :=
    IntermediateField.fixingSubgroup_isClosed M.toIntermediateField
  have hmain := NK.NUV2.LC.h2CardTransport p (𝔮.adicCompletion L)
    (SeparableClosure (𝔮.adicCompletion L)) (q.adicCompletion L')
    (SeparableClosure (q.adicCompletion L')) M.fixingSubgroup hcl (e1.trans e2)
  rw [hmain]
  exact NK.NUV2.LC.card_h2P_top_adicCompletion L' q hp hζ'

/-- **Route B, lemma (L0): the local Brauer computation at an open local subgroup.**

Let `κ = 𝔮.adicCompletion L` be the completion of a number field at a finite prime and let `M/κ` be a
finite Galois extension inside a separable closure `κ'` of `κ` containing a primitive `p`-th root of
unity (so that on all the levels of `M` the trivial coefficients `Z/p` agree with the cyclotomic
`μ_p`).  A closed subgroup `V ≤ Gal(K'/K)` which is continuously isomorphic to `Gal(κ'/M)`
satisfies `|H²(V, Z/p)| = p`.

Proof route: `H2Profinite p V` is the filtered colimit of `H²(V/(V ∩ Gal(K'/L)), Z/p)` over the
levels `L/K`; after the continuous isomorphism `e` these level groups are the Galois groups of the
finite extensions `M'/M`, and at the cofinal levels `M' ⊇ M(ζ_p)` the trivial coefficients `Z/p` are
`μ_p(M')`; hence `H2Profinite p V` is the colimit of `Br(M'/M)[p]` over the finite Galois `M'/M`,
which is `Br(M)[p] ≅ Z/p` (local class field theory; on disk as
`NK.NUV2.ABHN.muColimCardFree`/`muColim_card_p` together with the coefficient comparison
`NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot` and the cardinality transport
`NK.NUV2.LC.h2CardTransport`). -/
theorem card_open_local (p : ℕ) (hp : p.Prime) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)))
    (hζ : ∃ ζ : ↥M, IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (e : ↥V ≃ₜ* ↥(M.fixingSubgroup)) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) = p := by
  rw [natCard_h2Profinite_of_homeomorph (k := K) (k' := K') (κ := 𝔮.adicCompletion L)
    (κ' := SeparableClosure (𝔮.adicCompletion L)) V M.fixingSubgroup p e]
  exact card_h2P_fixingSubgroup p hp 𝔮 M hζ

end NK.NUV2.LC.RouteB
