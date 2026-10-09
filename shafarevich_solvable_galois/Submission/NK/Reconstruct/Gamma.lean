import Mathlib
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.GroupTheory.Abelianization.Finite
import Submission.NK.Reconstruct.Basic
import Submission.NeukirchUchida.PlaceSystem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ℓ-adic abelianisation of an absolute Galois group: Shimizu's invariants

This file provides the global vocabulary of the *reconstruction* in the form used by Shimizu's
proof of Neukirch–Uchida (arXiv:2009.10431, §4, and CoNF Chapter X): the ℓ-part of the
abelianisation of `G_K`, its rank `r_ℓ(K)`, the Frobenius elements of the arithmetic
`ℤ_ℓ`-extension, and the class-field-theoretic input (10.3.20) of CoNF, together with the
*provable* engine of Shimizu's Prop. 4f.3 (a finite union of proper closed subgroups of the
relevant compact module cannot exhaust it).

## Contents

* `ellRank A ℓ` — the ℓ-rank of a finite abelian group `A`, i.e. the rank of its ℓ-primary part as
  a `ℤ_ℓ`-module (equivalently `dim_{𝔽_ℓ} (A/ℓA)`), computed as `log_ℓ #A[ℓ]`.
* `levelRankSup K K' ℓ` — the *supremum of the ℓ-ranks of the abelianisations of the finite levels*
  `L/K` of `K'`.  **Beware**: this is *not* Shimizu's `r_ℓ(K)`; the level ℓ-ranks are in general
  *unbounded* (for `K = ℚ`, `ℓ = 2` the multiquadratic levels `ℚ(√2, …, √p_k)` have
  `ℓ-rank k`), while `r_2(ℚ) = 1`.  Since `ℕ` is given the `SupSet` of
  `Mathlib/Order/Lattice/Nat.lean`, an unbounded supremum evaluates to `0`, so this invariant
  degenerates.  The correct invariant `r_ℓ(K)` is `NK.Reconstruct.rankGamma` of
  `Submission/Work/Reconstruct/torsionFreeGamma.lean` (the `ℤ_ℓ`-rank of the torsion-free quotient
  of the ℓ-adic abelianisation); use that.  This definition is retained only because the
  *boundedness* of the level ranks is a legitimate intermediate hypothesis
  (`NK.Reconstruct.moduleFinite_gamma_of_bddAbove`).
* `levelRankSupLevel K K' ℓ L` — the same supremum relative to the extension `K'/L`.
* `rComplex K` — the number of complex places `r_ℂ(K)` of a number field.
* `exists_notMem_ker_finset` — **the engine of Shimizu's Prop. 4f.3**: given finitely many linear
  maps whose kernels are proper, there is a vector outside all of them.  Applied to
  `Γ_L ⊗ ℚ_ℓ` (and scaled back into `Γ_L`) this is the measure-theoretic statement that a finite
  union of proper closed subgroups of `Γ_L` has measure zero, which together with the density of
  the Frobenius elements (`NK.Reconstruct.dense_frobeniusSet_of_chebotarev`) produces the
  element of Shimizu's Prop. 4f.3.
-/

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The ℓ-rank of a finite abelian group -/

/-- **The ℓ-rank of a finite abelian group**: the number of cyclic `ℤ_ℓ`-summands of its
ℓ-primary part, equivalently `dim_{𝔽_ℓ}(A/ℓA)`, computed as `log_ℓ` of the order of the ℓ-torsion
subgroup `A[ℓ]` (an elementary abelian ℓ-group of order `ℓ^{r}`). -/
noncomputable def ellRank (A : Type*) [CommGroup A] [Fintype A] (ℓ : ℕ) : ℕ :=
  Nat.log ℓ (Nat.card {x : A // x ^ ℓ = 1})

/-- The ℓ-torsion subgroup of a finite abelian group is elementary abelian, so that its order is a
power of `ℓ`: this is the content of the definition of `ellRank`. -/
theorem ellRank_le_log_card (A : Type*) [CommGroup A] [Fintype A] (ℓ : ℕ) :
    ellRank A ℓ ≤ Nat.log ℓ (Nat.card A) := by
  unfold ellRank
  refine Nat.log_mono_right ?_
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The ℓ-rank of a finite abelian group which is trivial (no ℓ-torsion), e.g. of odd order. -/
theorem ellRank_eq_zero_of_subsingleton (A : Type*) [CommGroup A] [Fintype A] (ℓ : ℕ)
    (h : Subsingleton A) : ellRank A ℓ = 0 := by
  have hcard : Nat.card {x : A // x ^ ℓ = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨⟨1, by simp⟩⟩⟩
  rw [ellRank, hcard, Nat.log_one_right]

/-- The ℓ-rank of a finite abelian group of exponent dividing `ℓ` is the `log_ℓ` of its order. -/
theorem ellRank_eq_log_card_of_pow_eq_one (A : Type*) [CommGroup A] [Fintype A] {ℓ : ℕ}
    (h : ∀ x : A, x ^ ℓ = 1) : ellRank A ℓ = Nat.log ℓ (Nat.card A) := by
  unfold ellRank
  congr 1
  exact Nat.card_congr (Equiv.subtypeUnivEquiv h)

/-! ## The rank of the ℓ-adic abelianisation -/

/-- The ℓ-adic abelianisation of a finite Galois group, as a finite abelian group (the
abelianisation of `Gal(L/K)`). -/
abbrev LevelAbelianization {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (L : IntermediateField K K') := Abelianization Gal(↥L/K)

/-- **The ℓ-rank of the abelianisation of a finite Galois level**, with the instances needed to
form the quotient `Abelianization Gal(L/K)` supplied explicitly. -/
noncomputable def levelRank {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] (ℓ : ℕ) : ℕ := by
  classical
  exact ellRank (LevelAbelianization L) ℓ

/-- **The finite normal number-field levels of `K'` over `K`**, as an index type for the supremum
computing the rank of the ℓ-adic abelianisation: this is the projective system whose limit is
`G_K^{ab,(ℓ)}`. -/
structure FrobLevel (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K'] where
  /-- the level -/
  L : IntermediateField K K'
  /-- it is finite over `K` -/
  finite : FiniteDimensional K L
  /-- it is normal (hence Galois) over `K` -/
  normal : Normal K L
  /-- it is a number field -/
  numberField : NumberField ↥L

attribute [instance] FrobLevel.finite FrobLevel.normal FrobLevel.numberField

/-- The ℓ-rank of the abelianisation of a finite normal level. -/
noncomputable def FrobLevel.rank {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    (L : FrobLevel K K') (ℓ : ℕ) : ℕ := by
  classical
  exact ellRank (LevelAbelianization L.L) ℓ

/-- **The supremum of the ℓ-ranks of the finite levels** `L/K` of `K'`.

This is **not** Shimizu's `r_ℓ(K)` and it is *not* the rank of `Γ_K`: the level ℓ-ranks are
unbounded in general (for `K = ℚ`, `ℓ = 2`, the level `ℚ(√2, …, √p_k)` has ℓ-rank `k`, while
`r_2(ℚ) = 1`).  Since `ℕ` carries the `SupSet` of `Mathlib/Order/Lattice/Nat.lean`, an unbounded
supremum of natural numbers evaluates to `0` (`Nat.iSup_of_not_bddAbove`), so this definition
degenerates in the very cases that matter.  The correct invariant is
`NK.Reconstruct.rankGamma` (`Submission/Work/Reconstruct/torsionFreeGamma.lean`), the
`ℤ_ℓ`-rank of the torsion-free quotient of the ℓ-adic abelianisation; use that.  This definition
is retained only because the *boundedness* of the level ℓ-ranks is a legitimate (if conditional)
intermediate hypothesis, consumed by `NK.Reconstruct.moduleFinite_gamma_of_bddAbove`. -/
noncomputable def levelRankSup (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) : ℕ :=
  ⨆ (L : FrobLevel K K'), FrobLevel.rank L ℓ

/-- The supremum of the ℓ-ranks of the finite levels `M/L` of `K'` (the relative version of
`levelRankSup`; see there for the warning that this is *not* `r_ℓ(L)`). -/
noncomputable def levelRankSupLevel (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : IntermediateField K K') : ℕ :=
  ⨆ (M : FrobLevel ↥L K'), FrobLevel.rank M ℓ

/-- The defining property of the supremum `levelRankSup`: the ℓ-rank of a finite Galois level is
at most the supremum of all of them (under the hypothesis that they are bounded — without it the
supremum in `ℕ` degenerates to `0`). -/
theorem levelRank_le_levelRankSup (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : IntermediateField K K') [FiniteDimensional K L]
    [Normal K L] [NumberField ↥L]
    (hbdd : BddAbove (Set.range (fun L : FrobLevel K K' => FrobLevel.rank L ℓ))) :
    levelRank L ℓ ≤ levelRankSup K K' ℓ :=
  le_ciSup hbdd ⟨L, ‹FiniteDimensional K L›, ‹Normal K L›, ‹NumberField ↥L›⟩

/-- **The number `r_ℂ(K)` of complex places** of a number field. -/
noncomputable def rComplex (K : Type*) [Field K] [NumberField K] : ℕ :=
  Nat.card {v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex v}


/-! ## The Frobenius elements of the ℓ-adic abelianisation -/

section Frobenius

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']

/-- **The Frobenius class of a prime in the abelianisation of a finite Galois level.**  For a prime
`P` of `𝓞 L` lying over a prime `p` of `K`, this is the image in `Gal(L/K)^{ab}` of an arithmetic
Frobenius element at `P` (`NK.Chebotarev.IsFrobAt`).  It is well defined when `P` is unramified
over `p` (`frobeniusClass_eq_of_isFrobAt`); its compatibility with the restriction maps of the
projective system (`frobeniusClass_map_restrict`) is *not yet formalised* — it is the element-level
statement `NK.Chebotarev.IsFrobAtRestrictNormalHom` transported to the abelianisation.  In the
limit this is Shimizu's element `Frob_𝔭 ∈ Γ_K` of §4, defined for the primes `𝔭` unramified in
`K^{(∞,ℓ)}/K`. -/
noncomputable def frobeniusClass (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    [NumberField ↥L] {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal ↥L}
    (hP : P.asIdeal.LiesOver p.asIdeal) : Abelianization Gal(↥L/K) := by
  classical
  haveI : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  exact Abelianization.of (Classical.choose (NK.Chebotarev.exists_isFrobAt (K := K) (L := ↥L) p P hP))

/-- **A level viewed inside a larger one**: for intermediate fields `E ≤ M` of `K'/K`, `E` is also
an intermediate field of `K'/M`. -/
def restrictLevelTo {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    (E M : IntermediateField K K') (h : E ≤ M) : IntermediateField K ↥M :=
  Subfield.toIntermediateField (E.toSubfield.comap (algebraMap ↥M K')) (fun a => by
    simp only [Subfield.mem_comap]
    exact E.algebraMap_mem a)

/-- **The Frobenius class is well defined at an unramified prime**: it is the image of *every*
Frobenius element at `P`, by uniqueness of the Frobenius element over an unramified prime
(`NK.Chebotarev.IsFrobAt.eq_of_isFrobAt`). -/
theorem frobeniusClass_eq_of_isFrobAt (L : IntermediateField K K') [FiniteDimensional K L]
    [Normal K L] [NumberField ↥L] {p : NK.Chebotarev.PrimeIdeal K}
    {P : NK.Chebotarev.PrimeIdeal ↥L} (hP : P.asIdeal.LiesOver p.asIdeal)
    (he : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {σ : Gal(↥L/K)} (hσ : NK.Chebotarev.IsFrobAt P σ) :
    frobeniusClass L hP = Abelianization.of σ := by
  classical
  haveI : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  unfold frobeniusClass
  rw [NK.Chebotarev.IsFrobAt.eq_of_isFrobAt (K := K) (L := ↥L) hP he
    (Classical.choose_spec (NK.Chebotarev.exists_isFrobAt (K := K) (L := ↥L) p P hP)) hσ]

end Frobenius

/-! ## The measure-theoretic engine of Shimizu's Prop. 4f.3 -/

/-- **A finite union of proper kernels is proper** (the engine of Shimizu's Prop. 4f.3).

Let `V` be a vector space over an infinite field and `f i : V →ₗ[k] W i` finitely many linear maps
with `Ker (f i) ≠ ⊤`.  Then there is a vector lying in no kernel.

Shimizu applies this with `V = Γ_L ⊗_{ℤ_ℓ} ℚ_ℓ` (and then scales the resulting vector into `Γ_L`):
the kernels of the maps `γ ↦ σ̄_π_{L/K₁}(γ) · (π_{L/K₂} τ^*(γ))⁻¹` have rank `< r_ℓ(L)`, so the
union of these kernels has Haar measure `0` in `Γ_L`.  Together with the density of the Frobenius
elements (`NK.Chebotarev.DenseFrobeniusSet`, from the Čebotarev input
`NK.Reconstruct.ChebotarevInput`) this yields the element of Prop. 4f.3. -/
theorem exists_notMem_ker_finset {k V : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]
    (f : ∀ i, V →ₗ[k] W i) (hf : ∀ i, LinearMap.ker (f i) ≠ ⊤) :
    ∃ v : V, ∀ i, v ∉ LinearMap.ker (f i) :=
  Submodule.exists_forall_notMem_of_forall_ne_top (fun i => LinearMap.ker (f i)) hf

end NK.Reconstruct
