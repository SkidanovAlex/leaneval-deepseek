import Mathlib
import Submission.NK.ReconstructField.MainWeakNU
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.compactness_conjHomEquiv
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.Reconstruct.keyFinitePrimeMatch
import Submission.NK.ReconstructField.primeTransport_eq_levelPrimeMap_imp_base

set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- **The pigeonhole lemma which upgrades a finitary statement to a global one.**

Let `R : β → α → Prop` be a relation with `β` *finite*.  If for every finite set `S ⊆ α` there is a
single `b : β` satisfying `R b x` for all `x ∈ S`, then there is a single `b : β` satisfying `R b x`
for *all* `x`.

This is the finiteness upgrade used in Neukirch's reconstruction (CoNF XII §12.2): the set of
level isomorphisms `↥L ≃+* ↥(levelMap ϕ L)` is finite (it embeds into the `ℚ`-algebra
homomorphisms), so the finitary prime identifications produced by the differentiation argument can
be glued. -/
lemma exists_forall_of_exists_finset {α β : Type*} [Fintype β] [DecidableEq α]
    {R : β → α → Prop} (h : ∀ S : Finset α, ∃ b : β, ∀ x ∈ S, R b x) :
    ∃ b : β, ∀ x, R b x := by
  classical
  by_contra hc
  push Not at hc
  choose w hw using hc
  obtain ⟨b, hb⟩ := h (Finset.univ.image w)
  exact (hw b) (hb (w b) (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩))

/-- **Finiteness of the set of ring isomorphisms between two finite `ℚ`-algebras.**

A ring isomorphism `A ≃+* B` of two fields of characteristic zero is automatically `ℚ`-linear, so
the set of ring isomorphisms embeds into the (finite, by `AlgHom.fintype`) set of `ℚ`-algebra
homomorphisms `A →ₐ[ℚ] B` as soon as `A` is a finite-dimensional `ℚ`-vector space. -/
@[instance_reducible] noncomputable def ringEquivFintype (A B : Type*) [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B]
    [FiniteDimensional ℚ A] : Fintype (A ≃+* B) :=
  Fintype.ofInjective
    (fun τ : A ≃+* B => (AlgEquiv.ofRingEquiv (f := τ)
      (fun q => RingHom.map_rat_algebraMap (τ : A →+* B) q)).toAlgHom)
    (by intro τ σ h
        exact RingEquiv.ext (fun x => congrArg (fun f : A →ₐ[ℚ] B => f x) h))

/-- **The differentiation step of the reconstruction: the level prime-map identification.**

Given the σ-free local correspondence `a` for `ϕ`, a base-field isomorphism `τ₀` whose induced prime
map *is* `a.primeMap` (`hbase`, the weak Neukirch–Uchida statement in its prime form), the levelwise
weak isomorphism input `LevelIsoInput ϕ hϕ` (a *non-compatible* family: for every finite level
`L/K₁` merely `Nonempty (↥L ≃+* ↥(levelMap ϕ L))`), and a prime `ℓ` with `μ_ℓ ⊆ K₁`, this produces
`NK.ReconstructField.LevelPrimeIdentification ϕ hϕ a τ₀`: for every finite Galois level `L` whose
image level is Galois over `ℚ`, a field isomorphism `↥L ≃+* ↥(levelMap ϕ L)` compatible with `τ₀`
whose induced prime map is `levelPrimeMap ϕ hϕ a L`.

This is the Kummer-theoretic differentiation of Uchida/Shimizu: using
`NK.UchidaKummer.isDifferentiable_of_kummerMachinery` (proved in the sibling area) one constructs
finite levels whose local degrees at prescribed primes are prescribed powers of `ℓ`; a levelwise weak
isomorphism must then match the primes of `a`, because the local degrees of the corresponding primes
agree and are `ℓ`-adically different from those of every other prime.

With `NK.ReconstructField.exists_sigma_levelMatch_of_levelPrimeIdentification` and
`compactness_conjHomEquiv` (both on disk) this closes the σ-producing step of Neukirch–Uchida: the
conclusion `∃ σ, Conjugates σ ϕ` follows.  `LevelIsoInput` is *strictly weaker* than that conclusion
(`LevelCandidate.lean` derives it from `IsWeakUchida`), so this is not a circular input.

The statement is copied verbatim from `Submission/Work/ReconstructField/levelPrimeIdentification.lean`
(the sibling's own target, the last remaining gap between the fleet and the existence half of
CoNF XII 12.2.1), so that a proof here can be reused there. -/
theorem levelPrimeIdentification {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ₀ 𝔭)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    NK.ReconstructField.LevelPrimeIdentification ϕ hϕ a τ₀ := by
  intro L _ _ _ _ _ _ _
  classical
  -- the set of candidate level isomorphisms is finite
  haveI : Fintype (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)) :=
    ringEquivFintype ↥L ↥(NK.Reconstruct.levelMap ϕ L)
  -- the finitary prime identification, upgraded to all primes by the pigeonhole lemma
  obtain ⟨τ, hτ⟩ := exists_forall_of_exists_finset
    (α := NK.Chebotarev.PrimeIdeal ↥L)
    (β := ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L))
    (R := fun τ P => NK.Reconstruct.primeTransport τ P =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L P)
    (fun S => NK.Reconstruct.keyFinitePrimeMatch ϕ hϕ a hlev hℓ hμ L S)
  -- a level isomorphism with the prescribed prime map is automatically compatible with `τ₀`
  exact ⟨τ, funext hτ,
    (NK.ReconstructField.primeTransport_eq_levelPrimeMap_imp_base ϕ hϕ a τ₀ hbase L τ
      (funext hτ)).2⟩

end NK.Reconstruct
