import Mathlib
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.baseChange
import Submission.NK.Reconstruct.denseSet_avoidClosedSubgroups
import Submission.NK.Chebotarev.ExistsFrobeniusOfRestriction
import Submission.NK.Chebotarev.DenseFrobeniusSet
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Reconstruct.exists_split_frobAt
import Submission.NK.Reconstruct.exists_split_frobAt_unramified
import Submission.NK.Reconstruct.exists_isFrobElementAt_split_of_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open scoped NumberField
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Frobenius-avoidance statement of Proposition 4f.3 at completely split primes

This file proves the form of Shimizu's Proposition 4f.3 (arXiv:2009.10431, §4) in which the
escaping prime is required to be **completely split over `ℚ`**, which is the form needed for the
pointwise step `IsFrobElementAt 𝔭 g → IsFrobElementAt (𝔭|_{K}) (g|_{K})` of the reconstruction
(see `Submission/Work/Reconstruct/README.md` §19.8: without the splitting hypothesis the residue
degree `f` intervenes and the step is false).

The mathematical content is, as in `NK.Reconstruct.frobElementAt`, the combination of

* a **density statement** for the Frobenius elements at completely split primes — Čebotarev, in the
  form `NK.Reconstruct.exists_split_frobAt_unramified`, transported through the compactness
  argument `NK.Reconstruct.exists_isFrobElementAt_split_of_restrict` and the continuous map
  `galToGamma` (whose range is dense), and
* the **Baire-category statement** `NK.Reconstruct.exists_mem_dense_notMem_iUnion_closedSubgroup`.

## Contents

* `frobLevelBot` — the trivial finite normal level over `L` (needed to have at least one level);
* `exists_levelComponent_eq` — every element of the ℓ-part of the abelianisation of a finite level
  is an ℓ-primary component;
* `exists_split_isFrobElementAt` — a Frobenius element at a completely split prime exists;
* `dense_image_galToGamma_splitFrobenius` — the images under `galToGamma` of the Frobenius elements
  at completely split primes are dense in `Γ_L`;
* `exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup` — the target statement.
-/

/-! ## The trivial level over `L` -/

section BotLevel

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]

/-- **The trivial finite normal level over `L`**: `L` itself, as a level of `Ω/L`. -/
noncomputable def frobLevelBot (L : FrobLevel ℚ Ω) : FrobLevel ↥L.L Ω where
  L := ⊥
  finite := inferInstance
  normal := inferInstance
  numberField :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥L.L) (K' := Ω) ⊥

@[simp]
theorem frobLevelBot_L (L : FrobLevel ℚ Ω) : (frobLevelBot L).L = ⊥ := rfl

end BotLevel

/-! ## Every element of a level is an ℓ-primary component -/

section LevelComponent

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- **Every element of the ℓ-primary part of the abelianisation of a finite level is the ℓ-primary
component of the restriction of some automorphism.**  The ℓ-primary projection `ellComp ℓ` is the
identity on the ℓ-primary part (`ellComp_eq_self`), and the abelianisation map
`Gal(L/K) → Gal(L/K)^{ab}` is surjective. -/
theorem exists_levelComponent_eq (ℓ : ℕ) (T : FrobLevel K K') (x : LevelEllPart T.L ℓ) :
    ∃ τ : Gal(↥T.L/K), ellComp ℓ (Abelianization.of τ) = x := by
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective ((x : LevelEllPart T.L ℓ) : LevelAbelianization T.L)
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(↥T.L/K), Abelianization.of τ = (x : LevelAbelianization T.L) := ⟨b, hb⟩
  exact ⟨τ, by rw [hτ]; exact ellComp_eq_self x⟩

end LevelComponent

/-! ## A density statement for the Frobenius elements at completely split primes -/

section Density

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]

/-- The split Čebotarev input in the form used below, assembled from
`NK.Reconstruct.exists_split_frobAt_unramified`. -/
theorem splitChebotarevInput (hc : ChebotarevInput ℚ Ω) (L : FrobLevel ℚ Ω) :
    ∀ (N : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L N] [Normal ↥L.L N]
      [NumberField ↥N] (τ : Gal(↥N/↥L.L)),
      ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (P : NK.Chebotarev.PrimeIdeal ↥N),
        P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L.L) = 1 ∧
        NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥N) P τ :=
  fun N _ _ _ τ => exists_split_frobAt_unramified (Ω := Ω) hc L N τ

/-- **A Frobenius element at a completely split prime exists.**  This is the split Čebotarev input
applied at the trivial level over `L`, together with the compactness lemma
`NK.Reconstruct.exists_isFrobElementAt_split_of_restrict`. -/
theorem exists_split_isFrobElementAt (hc : ChebotarevInput ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥L.L Ω] :
    ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (σ : Gal(Ω/↥L.L)),
      SplitsCompletelyOverRat 𝔭 ∧ IsFrobElementAt 𝔭 σ := by
  obtain ⟨𝔭, σ, hsplit, hfrob, -⟩ :=
    exists_isFrobElementAt_split_of_restrict (Ω := Ω) L (splitChebotarevInput hc L)
      (frobLevelBot L).L (1 : Gal(↥(frobLevelBot L).L/↥L.L))
  exact ⟨𝔭, σ, hsplit, hfrob⟩

/-- **The density of the Frobenius elements at completely split primes in `Γ_L`.**

The images under `galToGamma ℓ` of the elements of `Gal(Ω/L)` which are Frobenius elements at a
fixed completely split prime of `L` (at every finite normal level over `L`) form a dense subset of
`Γ_L`.

Indeed, `Γ_L` is the projective limit of the finite discrete level groups, so a nonempty basic open
set is given by finitely many levels `M_i` and values `v_i`.  Taking an upper bound `T` of the
`M_i`, an element `τ ∈ Gal(T/L)` with ℓ-primary component the `T`-component of the given point
(`exists_levelComponent_eq`), and applying `NK.Reconstruct.exists_isFrobElementAt_split_of_restrict`
to `(T, τ)` produces `σ ∈ Gal(Ω/L)` with `σ|_T = τ` which is a Frobenius element at a completely
split prime `𝔭`; then `galToGamma ℓ σ` agrees with the given point at every `M_i` by coherence. -/
theorem dense_image_galToGamma_splitFrobenius (hc : ChebotarevInput ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥L.L Ω] (ℓ : ℕ) :
    Dense ((galToGamma (K := ↥L.L) (K' := Ω) ℓ) ''
      {σ : Gal(Ω/↥L.L) | ∃ 𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L,
        SplitsCompletelyOverRat 𝔭 ∧ IsFrobElementAt 𝔭 σ}) := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨f, hfU⟩
  rw [isOpen_induced_iff] at hU
  obtain ⟨Ũ, hŨ, rfl⟩ := hU
  obtain ⟨I, u, hu, hIU⟩ :=
    isOpen_pi_iff.mp hŨ (f : ∀ a : FrobLevel ↥L.L Ω, LevelEllPart a.L ℓ) hfU
  have key : ∃ σ : Gal(Ω/↥L.L),
      (∀ a ∈ I, Gamma.proj a (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) ∈ u a) ∧
      ∃ 𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L,
        SplitsCompletelyOverRat 𝔭 ∧ IsFrobElementAt 𝔭 σ := by
    by_cases hI : I.Nonempty
    · obtain ⟨L₀, hL₀⟩ := hI
      obtain ⟨T, hT, -⟩ :=
        projSurj_finset_exists_upper_bound (K := ↥L.L) (K' := Ω) L₀ I
      obtain ⟨τ, hτ⟩ :=
        exists_levelComponent_eq (K := ↥L.L) (K' := Ω) ℓ T (Gamma.proj T f)
      obtain ⟨𝔭, σ, hsplit, hfrob, hσT⟩ :=
        exists_isFrobElementAt_split_of_restrict (Ω := Ω) L (splitChebotarevInput hc L) T.L τ
      refine ⟨σ, ?_, 𝔭, hsplit, hfrob⟩
      intro a ha
      have hle : a.L ≤ T.L := hT a ha
      have h1 : Gamma.proj a (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) = Gamma.proj a f := by
        rw [← Gamma.proj_compatible a T hle (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ),
          galToGamma_proj, levelComponent, hσT, hτ,
          Gamma.proj_compatible a T hle f]
      rw [h1]
      exact (hu a ha).2
    · obtain ⟨𝔭, σ, hsplit, hfrob⟩ := exists_split_isFrobElementAt (Ω := Ω) hc L
      refine ⟨σ, ?_, 𝔭, hsplit, hfrob⟩
      intro a ha
      rw [Finset.not_nonempty_iff_eq_empty.mp hI] at ha
      exact absurd ha (Finset.notMem_empty a)
  obtain ⟨σ, hσ, 𝔭, hsplit, hfrob⟩ := key
  exact ⟨galToGamma (K := ↥L.L) (K' := Ω) ℓ σ, hIU (by rw [Set.mem_pi]; exact hσ),
    ⟨σ, ⟨𝔭, hsplit, hfrob⟩, rfl⟩⟩

end Density

/-! ## The target statement -/

/-- **The Frobenius-avoidance statement of Shimizu's Proposition 4f.3, restricted to primes
completely split over `ℚ`.**  Given finitely many closed subgroups `H_i` of the ℓ-adic
abelianisation `Γ_L = Gamma ↥L.L Ω ℓ` of `G_L` which are not open (in the application they are the
kernels of the finitely many `φ_τ`, each of which has finite cokernel and hence infinite image),
there is a prime `𝔭` of `L` which is **completely split over `ℚ`** and a Frobenius element
`σ ∈ Gal(Ω/L)` at `𝔭` whose image `galToGamma σ ∈ Γ_L` lies outside every `H_i`.

Plan: for every finite Galois level `N/L` and every `τ ∈ Gal(N/L)`, `exists_split_frobAt` provides a
prime of `L` completely split over `ℚ` with `τ` a Frobenius at a prime above it; a compactness
argument (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, as in the proof of
`NK.Chebotarev.ExistsFrobeniusOfRestriction`: restrict to a level, extend along the directed family
of levels, using `exists_isFrobAtPrime_of_le`-style transfer and the closedness of the conditions in
the Krull topology) produces a single `σ ∈ Gal(Ω/L)` which is a Frobenius element at one such prime
`𝔭` at *every* finite normal level over `L`, i.e. `IsFrobElementAt 𝔭 σ` with
`SplitsCompletelyOverRat 𝔭`.  Hence the set of `galToGamma σ` over such `σ` is dense in `Γ_L`
(`DenseRange.dense_image` for the continuous map `galToGamma`, whose range is dense).  Finally a
dense subset of a compact space meets the non-empty open complement of the finite union `⋃ H_i`
(`NK.Reconstruct.exists_mem_dense_notMem_iUnion_closedSubgroup`).

WARNING: `NK.Chebotarev.DenseFrobeniusSet` cannot be reused verbatim: its input `hC` demands the
prime be unramified in the level, which `exists_split_frobAt` does not give (and does not need —
`IsFrobAt` carries no unramifiedness requirement).  Build the split-prime density directly from
`exists_split_frobAt`. -/
theorem exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup {Ω : Type*}
    [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] (hc : NK.Reconstruct.ChebotarevInput ℚ Ω)
    (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) {ι : Type*} [Finite ι] (H : ι → Subgroup (NK.Reconstruct.Gamma ↥L.L Ω ℓ))
    (hcl : ∀ i, IsClosed ((H i : Subgroup (NK.Reconstruct.Gamma ↥L.L Ω ℓ)) :
      Set (NK.Reconstruct.Gamma ↥L.L Ω ℓ)))
    (hopen : ∀ i, ¬ IsOpen ((H i : Subgroup (NK.Reconstruct.Gamma ↥L.L Ω ℓ)) :
      Set (NK.Reconstruct.Gamma ↥L.L Ω ℓ))) :
    ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (σ : Gal(Ω/↥L.L)),
      NK.Reconstruct.IsFrobElementAt 𝔭 σ ∧ NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧
      ∀ i, galToGamma (K := ↥L.L) (K' := Ω) ℓ σ ∉ H i := by
  obtain ⟨d, hdD, hd⟩ :=
    exists_mem_dense_notMem_iUnion_closedSubgroup H hcl hopen
      (dense_image_galToGamma_splitFrobenius hc L ℓ)
  obtain ⟨σ, hσ, rfl⟩ := hdD
  obtain ⟨𝔭, hsplit, hfrob⟩ := hσ
  exact ⟨𝔭, σ, hfrob, hsplit, hd⟩

end NK.Reconstruct
