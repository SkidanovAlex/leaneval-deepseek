/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ramification filtration of a local Galois group of `p`-adic fields

The abstract filtration of `Submission/Work/Ramification/Defs.lean` is here specialised to the
local fields of this workspace: `K`, `L` are number fields, `Q` a finite prime of `K`, `q` a
finite prime of `L` lying over `Q`, and

  `Gal(L_q/K_Q) = q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L`

is the local Galois group at `q`, with valuation ring `A = q.adicCompletionIntegers L`.  The
higher ramification subgroups in lower numbering are

  `adicRamificationSubgroup i = { σ | ∀ x ∈ A, σ x - x ∈ 𝔪_A^{i+1} }`,

so that `adicRamificationSubgroup 0` is the inertia subgroup and `adicRamificationSubgroup 1` is
the wild inertia subgroup.

The classical existence statement in this workspace
(`Commons.NumberTheory.NumberField.Completion.exists_ramificationSubgroups_adicCompletion`) produces
such a filtration *existentially*, without a definition; the present chapter replaces it by a
canonical definition and supplies the theory (`ramificationSubgroup_zero`,
`iInf_ramificationSubgroup_eq_bot`, `exists_ramificationSubgroup_eq_bot`, the Herbrand function of
`Submission/Work/Ramification/Herbrand.lean`).

The *order* of the zeroth subgroup is the ramification index `e(q|Q)`; the corresponding
statement `natCard_ramificationSubgroup_zero_adicCompletion` and the eventual triviality
`exists_adicRamificationSubgroup_eq_bot` are proved in the companion files of this directory.
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.CommonsBridge

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Ramification

universe u

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
  (hq : q.asIdeal.LiesOver Q.asIdeal)
  [Algebra (Q.adicCompletion K) (q.adicCompletion L)]

/-- **The `i`-th higher ramification subgroup of the local Galois group `Gal(L_q/K_Q)`**, in lower
numbering: `σ` acts trivially on `𝒪_{L_q}/𝔪^{i+1}`.

For `i = 0` this is the inertia subgroup, for `i = 1` the wild inertia subgroup. -/
noncomputable def adicRamificationSubgroup (i : ℕ) :
    Subgroup ((q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K)) :=
  ramificationSubgroup (K := Q.adicCompletion K) (q.adicCompletionIntegers L) i

variable {Q q}

theorem mem_adicRamificationSubgroup_iff (i : ℕ)
    (σ : ((q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K))) :
    σ ∈ adicRamificationSubgroup (K := K) (L := L) Q q i ↔
      ∀ x : q.adicCompletionIntegers L,
        σ • x - x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (i + 1) :=
  Iff.rfl

theorem adicRamificationSubgroup_normal (i : ℕ) :
    (adicRamificationSubgroup (K := K) (L := L) Q q i).Normal :=
  ramificationSubgroup_normal _ _

theorem adicRamificationSubgroup_antitone :
    Antitone (adicRamificationSubgroup (K := K) (L := L) Q q) :=
  ramificationSubgroup_antitone _

/-- **The zeroth ramification subgroup is the inertia subgroup** of the local Galois group
`Gal(L_q/K_Q)`. -/
theorem adicRamificationSubgroup_zero :
    adicRamificationSubgroup (K := K) (L := L) Q q 0 =
      (q.adicCompletionIntegers L).inertiaSubgroup (Q.adicCompletion K) :=
  ramificationSubgroup_zero _

/-- Every higher ramification subgroup is contained in the inertia subgroup. -/
theorem adicRamificationSubgroup_le_inertiaSubgroup (i : ℕ) :
    adicRamificationSubgroup (K := K) (L := L) Q q i ≤
      (q.adicCompletionIntegers L).inertiaSubgroup (Q.adicCompletion K) :=
  ramificationSubgroup_le_inertiaSubgroup _ i

end

end NK.Ramification
