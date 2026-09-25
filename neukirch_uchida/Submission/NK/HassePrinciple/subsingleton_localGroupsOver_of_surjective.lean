/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's rank count: surjectivity of the localisation forces a single local group

Umbrella development: `Submission/Work/HassePrinciple/` (README §18).

Neukirch's proof of the local characterisation of decomposition groups (Invent. Math. **6** (1969),
Theorem 1; NSW (9.2.1)) runs the following *rank count*.  For a closed subgroup `U ≤ G_K` of
`p`-decomposition type one knows `|H²(U, Z/p)| = p`, while at every local group `V = U ⊓ D_A` over a
place `A` of `K'` above a fixed prime `𝔭` one has `p ≤ |H²(V, Z/p)|`.  Neukirch's arithmetic input
is the **surjectivity** of the localisation

  `L : H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭} H²(V, Z/p)`.

Since `L` is a surjection from a set of `p` elements, its target has at most `p` elements.  But the
target is a product of local groups, each of size at least `p`; if there were two *distinct* local
groups `V ≠ W`, the evaluation `L ↦ (L V, L W)` would exhibit a surjection onto a set of size at
least `p · p = p² > p`.  Hence there can be only one local group over `𝔭`.

This is the module's `NK.HassePrinciple.subsingleton_localGroupsOver_of_surjective`: the rank
count, stripped of everything arithmetic, as a statement about a surjection between the profinite
cohomology `NK.BrauerHasse.H2Profinite p U` and the product of the local cohomologies
`NK.BrauerHasse.H2Profinite p V` over the local groups `V ∈ localGroupsOver U 𝔭`.

The conclusion — that `localGroupsOver U 𝔭` is a subsingleton, i.e. the prime `𝔭` is *indecomposed*
for `U` — is what turns Neukirch's (9.2.1) into the statement `U ≤ D_A` via the coincidence theorem
`NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective`, and hence into the Hasse principle
(`NK.HassePrinciple.rankInput_of_nswsInput`).
-/
import Mathlib
import Submission.NK.HassePrinciple.LocalGroupInputDefs

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

/-- **Neukirch's rank count.**  If the localisation
`H²(U, Z/p) → ∏_{V ∈ localGroupsOver U 𝔭} H²(V, Z/p)` is surjective, `|H²(U, Z/p)| = p`, and every
local group `V = U ⊓ D_A` over `𝔭` satisfies `p ≤ |H²(V, Z/p)|`, then all the local groups over `𝔭`
coincide: `localGroupsOver U 𝔭` is a subsingleton.

The proof is the cardinality count of the module header: surjectivity bounds the product by `p`,
while a pair of distinct local groups would produce a surjection onto a product of two sets of size
at least `p`, i.e. at least `p² > p` elements. -/
theorem subsingleton_localGroupsOver_of_surjective {p : ℕ} (hp : p.Prime)
    {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) = p)
    (hloc : ∀ V ∈ NK.HassePrinciple.localGroupsOver (K := K) (K' := K') U 𝔭,
      p ≤ Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V))
    (hsurj : Function.Surjective
      (NK.HassePrinciple.localGroupLoc (K := K) (K' := K') p U 𝔭)) :
    (NK.HassePrinciple.localGroupsOver (K := K) (K' := K') U 𝔭).Subsingleton := by
  classical
  -- `localGroupsOver U 𝔭` is a set of subgroups; a subsingleton is a set of pairwise equal
  -- elements, so we suppose two members `V ≠ W` and derive a contradiction.
  intro V hV W hW
  by_contra hne
  -- `H²(U, Z/p)` is finite, because its cardinality is the prime `p ≠ 0`.
  haveI hfinA : Finite (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact hp.ne_zero)).2
  -- The two members of the index set, as elements of the subtype, are distinct.
  have hne' : (⟨W, hW⟩ : ↥(NK.HassePrinciple.localGroupsOver (K := K) (K' := K') U 𝔭)) ≠
      ⟨V, hV⟩ :=
    fun h => hne (congrArg Subtype.val h).symm
  -- Evaluation at the two indices `V` and `W` is a surjection onto the product of the two local
  -- groups: a pair `(a, b)` is realised by the function which is `a` at `V`, `b` at `W` and
  -- arbitrary elsewhere (each local group is nonempty, as `p ≥ 2 ≤ Nat.card`).
  have hsurj' : Function.Surjective
      (fun f : ((V' : ↥(NK.HassePrinciple.localGroupsOver (K := K) (K' := K') U 𝔭)) →
          NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V'.1) =>
        (f ⟨V, hV⟩, f ⟨W, hW⟩)) := by
    have hnon : ∀ V' : ↥(NK.HassePrinciple.localGroupsOver (K := K) (K' := K') U 𝔭),
        Nonempty (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V'.1) :=
      fun V' => (Nat.card_ne_zero.mp (by have h := hloc V' V'.2; have := hp.two_le; omega)).1
    rintro ⟨a, b⟩
    refine ⟨Function.update (Function.update
        (fun V' => Classical.choice (hnon V')) ⟨W, hW⟩ b) ⟨V, hV⟩ a, ?_⟩
    simp only [Function.update_self, Function.update_of_ne hne']
  -- Composing with the localisation gives a surjection `H²(U, Z/p) → H²(V) × H²(W)`, so the
  -- product of the two local groups has at most `p` elements.
  have hcomp := hsurj'.comp hsurj
  have hle := Nat.card_le_card_of_surjective _ hcomp
  rw [hcard] at hle
  rw [Nat.card_prod] at hle
  -- But each local group has at least `p` elements, so the product has at least `p · p > p`.
  have h1 := hloc V hV
  have h2 := hloc W hW
  have hpp : p * p ≤ p := le_trans (Nat.mul_le_mul h1 h2) hle
  nlinarith [hp.two_le, hpp]

end NK.HassePrinciple
