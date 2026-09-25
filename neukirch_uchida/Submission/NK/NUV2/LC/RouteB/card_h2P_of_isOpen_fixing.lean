import Mathlib
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.LC.h2CardTransport
import Submission.NK.TowerRank.exists_numberField_completion_of_finiteDimensional
import Submission.NK.Reconstruct.isHomeomorph_levelGalEquiv
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv

namespace NK.NUV2.LC.RouteB


/-- **The local Brauer computation at an arbitrary finite intermediate field.** -/
theorem card_h2P_fixingSubgroup_of_finiteDimensional (p : ℕ) (hp : p.Prime) {L : Type}
    [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : IntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)))
    [FiniteDimensional (𝔮.adicCompletion L) M]
    (hζ : ∃ ζ : ↥M, IsPrimitiveRoot ζ p) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p M.fixingSubgroup) = p := by
  have hreal : ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
      (hq : q.asIdeal.LiesOver 𝔮.asIdeal),
      letI : Algebra (𝔮.adicCompletion L) (q.adicCompletion L') :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔮 q hq)
      Nonempty (↥M ≃ₐ[𝔮.adicCompletion L] q.adicCompletion L') :=
    NK.TowerRank.exists_numberField_completion_of_finiteDimensional (K := L) 𝔮 M
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
  let φh : ↥M →+* q.adicCompletion L' := φ.toRingEquiv.toRingHom
  letI : Algebra ↥M (SeparableClosure (q.adicCompletion L')) :=
    RingHom.toAlgebra
      ((algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).comp φh)
  haveI hscM : IsSepClosure ↥M (SeparableClosure (𝔮.adicCompletion L)) :=
    ⟨IsSepClosure.sep_closed (𝔮.adicCompletion L), inferInstance⟩
  haveI hscL : IsSepClosure ↥M (SeparableClosure (q.adicCompletion L')) :=
    isSepClosure_of_ringEquiv (C := SeparableClosure (q.adicCompletion L')) φ.toRingEquiv
  let ψ : SeparableClosure (𝔮.adicCompletion L) ≃ₐ[↥M]
      SeparableClosure (q.adicCompletion L') :=
    IsSepClosure.equiv ↥M (SeparableClosure (𝔮.adicCompletion L))
      (SeparableClosure (q.adicCompletion L'))
  -- ## The base compatibility of ψ (and hence of σ)
  have h1φ : ∀ c : q.adicCompletion L', φh (φ.symm.toRingEquiv c) = c :=
    fun c => by
      change φ.toRingEquiv.toRingHom (φ.toRingEquiv.symm c) = c
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      exact (φ.toRingEquiv).apply_symm_apply c
  have hstruct : ∀ a : ↥M,
      (algebraMap ↥M (SeparableClosure (q.adicCompletion L')) a)
        = (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))) (φh a) :=
    fun a => rfl
  have hψ : (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L))).range.map
      ψ.toRingHom = (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).range := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hx
      exact ⟨φh a, ((ψ.commutes a).trans (hstruct a)).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L))
        (φ.symm.toRingEquiv c), ⟨_, rfl⟩,
        (ψ.commutes (φ.symm.toRingEquiv c)).trans (by rw [hstruct, h1φ c])⟩
  let σ : SeparableClosure (q.adicCompletion L') ≃+* SeparableClosure (𝔮.adicCompletion L) :=
    ψ.symm.toRingEquiv
  have hσ : Submission.NeukirchUchida.MapsBase
      (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L)))
      (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))) σ :=
    Submission.NeukirchUchida.subring_map_symm_of_map_eq ψ.toRingEquiv
      (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L))).range
      (algebraMap (q.adicCompletion L') (SeparableClosure (q.adicCompletion L'))).range hψ
  -- ## The topological isomorphism `↥M.fixingSubgroup ≃ₜ* Gal(κ'_q/κ_q)`
  have hfixh := NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv (K := 𝔮.adicCompletion L)
    (Ω := SeparableClosure (𝔮.adicCompletion L)) M
  have hconj := NK.NeukirchUchida.isHomeomorph_conjHomEquiv σ hσ
  let e1 : ↥(IntermediateField.fixingSubgroup M) ≃ₜ*
      Gal(SeparableClosure (𝔮.adicCompletion L)/↥M) :=
    continuousMulEquivOfIsHomeomorph (IntermediateField.fixingSubgroupEquiv M) hfixh
  let e2 : Gal(SeparableClosure (𝔮.adicCompletion L)/↥M) ≃ₜ*
      Gal(SeparableClosure (q.adicCompletion L')/q.adicCompletion L') :=
    continuousMulEquivOfIsHomeomorph (Submission.NeukirchUchida.conjHomEquiv hσ) hconj
  -- ## The transport to the completion model
  have hcl : IsClosed (M.fixingSubgroup :
      Set Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)) :=
    IntermediateField.fixingSubgroup_isClosed M
  have hmain := NK.NUV2.LC.h2CardTransport p (𝔮.adicCompletion L)
    (SeparableClosure (𝔮.adicCompletion L)) (q.adicCompletion L')
    (SeparableClosure (q.adicCompletion L')) M.fixingSubgroup hcl (e1.trans e2)
  rw [hmain]
  exact NK.NUV2.LC.card_h2P_top_adicCompletion L' q hp hζ'


/-- **The local Brauer cardinality at an open subgroup of the absolute Galois group of a `p`-adic
field, when the subgroup fixes a primitive `p`-th root of unity.**

Let `L` be a number field, `𝔮` a finite prime, `κ = 𝔮.adicCompletion L`, `κ' = SeparableClosure κ`,
`ζ ∈ κ'` a primitive `p`-th root of unity and `W ≤ Gal(κ'/κ)` an **open** subgroup fixing `ζ`.
Then `H²(W, Z/p)` has exactly `p` elements.

Proof route (two steps).

*Step 1 — reduce to a finite intermediate field.*  Let `M = IntermediateField.fixedField W`.  Since
`W` is open, it is closed (`Subgroup.isClosed_of_isOpen`), so
`InfiniteGalois.fixingSubgroup_fixedField ⟨W, _⟩ : M.fixingSubgroup = W`, and
`InfiniteGalois.isOpen_iff_finite M` gives `FiniteDimensional κ M` (rewrite `M.fixingSubgroup = W`
and use `hWopen`).  Finally `ζ ∈ M`: from `hWζ` and the Galois connection
(`IntermediateField.le_iff_le`) get `adjoin κ {ζ} ≤ M`, so the subtype element
`⟨ζ, _⟩ : ↥M` is a primitive `p`-th root (transfer `hζ` along the injective coercion
`Subtype.val : ↥M → κ'` with `IsPrimitiveRoot.of_map_of_injective`).

*Step 2 — the finite-intermediate-field computation.*  Show
`Nat.card (NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p M.fixingSubgroup) = p` for an
arbitrary finite-dimensional `M` with a primitive `p`-th root in `M`.  This is the generalisation of
the proven `NK.NUV2.LC.RouteB.card_h2P_fixingSubgroup` (same statement with
`M : FiniteGaloisIntermediateField`) to non-Galois `M`, and its proof is the *same* proof with
`M.toIntermediateField` replaced by `M`: `NK.TowerRank.exists_numberField_completion_of_finiteDimensional`
(takes an arbitrary `IntermediateField` with `[FiniteDimensional]`) realises `↥M` as
`q.adicCompletion L'` via `φ : ↥M ≃ₐ[κ] q.adicCompletion L'`; then
`NK.Reconstruct.isHomeomorph_fixingSubgroupEquiv` (needs only `[FiniteDimensional]`),
`isSepClosure_of_ringEquiv` (in `card_open_local.lean`), `IsSepClosure.equiv`,
`NK.NeukirchUchida.isHomeomorph_conjHomEquiv` + `MapsBase` +
`NK.NeukirchUchida.subring_map_symm_of_map_eq` build
`e1.trans e2 : ↥(M.fixingSubgroup) ≃ₜ* Gal(SeparableClosure (q.adicCompletion L')/q.adicCompletion L')`,
and `NK.NUV2.LC.h2CardTransport` (with `IntermediateField.fixingSubgroup_isClosed`, which needs
`[FiniteDimensional]` only) transports the cardinality to
`Nat.card (H2Profinite p ⊤) = p`, which is `NK.NUV2.LC.card_h2P_top_adicCompletion L' q hp hζ'`
(the primitive root `hζ' : ∃ ζ : q.adicCompletion L', IsPrimitiveRoot ζ p` is the image of a root
of `M` under `φ`).  Copying the body of `card_h2P_fixingSubgroup` verbatim with this replacement is
the intended proof. -/
theorem card_h2P_of_isOpen_fixing (p : ℕ) (hp : p.Prime) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (ζ : SeparableClosure (𝔮.adicCompletion L)) (hζ : IsPrimitiveRoot ζ p)
    (W : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))
    (hWopen : IsOpen (W : Set Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)))
    (hWζ : W ≤ (IntermediateField.adjoin (𝔮.adicCompletion L) {ζ}).fixingSubgroup) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p W) = p := by
  -- ## Step 1: reduce to the finite intermediate field `M = κ'^W`
  let M : IntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)) :=
    IntermediateField.fixedField W
  have hcl : IsClosed (W : Set Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
    Subgroup.isClosed_of_isOpen W hWopen
  have hfix : M.fixingSubgroup = W := InfiniteGalois.fixingSubgroup_fixedField ⟨W, hcl⟩
  haveI : FiniteDimensional (𝔮.adicCompletion L) M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfix]; exact hWopen)
  have hle : IntermediateField.adjoin (𝔮.adicCompletion L) {ζ} ≤ M :=
    (IntermediateField.le_iff_le W (IntermediateField.adjoin (𝔮.adicCompletion L) {ζ})).mpr hWζ
  have hζM : ζ ∈ M :=
    hle (IntermediateField.subset_adjoin (𝔮.adicCompletion L) {ζ} (Set.mem_singleton ζ))
  have hprim : ∃ ζ' : ↥M, IsPrimitiveRoot ζ' p := by
    refine ⟨⟨ζ, hζM⟩, ?_⟩
    refine IsPrimitiveRoot.of_map_of_injective
      (f := (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L)))) ?_ ?_
    · simpa using hζ
    · exact fun a b hab => Subtype.ext hab
  -- ## Step 2: the finite-level computation
  have hmain := card_h2P_fixingSubgroup_of_finiteDimensional (L := L) p hp 𝔮 M hprim
  rw [hfix] at hmain
  exact hmain

end NK.NUV2.LC.RouteB
