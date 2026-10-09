/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelianised Frattini rank from the maximal abelian subextension (with openness)

The sibling file `hasAbelianFrattiniRank_of_maxAbelian.lean` states the transfer

  `HasFrattiniRank p r (maxAbelianSubext κ K' ≃ₐ[κ] maxAbelianSubext κ K')`
    `→ HasAbelianFrattiniRank p r (Gal(K'/κ))`

**without** any hypothesis on the Krull topology of `Gal(K'/κ)`, and that statement is
*false*: with `G := Gal(K'/κ)` and `S := commutator G` (the *algebraic* commutator
subgroup), `Gal(maxAbelianSubext κ K'/κ) ≃* G ⧸ S.topologicalClosure` — the *topological*
abelianisation — whereas `HasAbelianFrattiniRank p r G` speaks about the *abstract*
abelianisation `Abelianization G = G ⧸ S`.  The natural surjection
`G ⧸ S ↠ G ⧸ S.topologicalClosure` need not be injective; see `Hints.lean` in this
directory for the counterexample (`G = (∏_ℤ ℤ/2) ⋊ ℤ/2` over a PAC field, where the
hypothesis holds with `p = 2`, `r = 2` while `numIndexSubgroups 2 (Abelianization G) = 0`).

The transfer becomes a theorem as soon as one assumes that index-`p` *normal* subgroups of
`Gal(K'/κ)` are open — equivalently closed — which is exactly the structural input used
elsewhere in the workspace (`NK.LocalAnabelian.PadicField.FrattiniRank.lean`,
`NK.LocalAnabelian.GaloisCorrespondence.IndexP.lean`,
`.../numIndexSubgroups_abelianization_eq_natCard_galois.lean`).  For `κ` a `p`-adic field
this holds because `Gal(κ̄/κ)` is topologically finitely generated and hence every
finite-index subgroup is open (Nikolov–Segal).

The main theorem of this file is `hasAbelianFrattiniRank_of_maxAbelian_of_isOpen`, the
corrected statement.  It is proved from two reusable ingredients:

* `numIndexSubgroups_eq_natCard_comap`: for a surjective `f : G →* H`, subgroups of index
  `n` of `H` are the subgroups `M` of `G` with `f.ker ≤ M` and `[G : M] = n`;
* `numIndexSubgroups_quotient_commutator_eq_topologicalClosure`: under the openness
  hypothesis, `numIndexSubgroups n (G ⧸ commutator G) = numIndexSubgroups n
  (G ⧸ (commutator G).topologicalClosure)`.

The structural Galois-theoretic input
`(fixedField H).fixingSubgroup = H.topologicalClosure` is in the sibling file
`fixingSubgroup_fixedField_eq_topologicalClosure.lean`.
-/
import Mathlib
import Submission.NK.LocalReciprocity.All
import Submission.NK.LocalInputs.AbelianRank.fixingSubgroup_fixedField_eq_topologicalClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical commutatorElement

namespace NK.LocalInputs.AbelianRank

noncomputable section

-- `haveI` is genuinely used to register the `IsGalois`/`Normal` instances below.
set_option linter.style.haveILetI false

/-- **Index-`n` subgroups of the target of a surjection.**  For a surjective group
homomorphism `f : G →* H`, the subgroups of `H` of index `n` correspond to the subgroups
`M` of `G` with `f.ker ≤ M` and `M.index = n`. -/
theorem numIndexSubgroups_eq_natCard_comap {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    NK.LocalAnabelian.numIndexSubgroups n H =
      Nat.card {M : Subgroup G // f.ker ≤ M ∧ M.index = n} := by
  unfold NK.LocalAnabelian.numIndexSubgroups
  refine Nat.card_congr ?_
  refine
    { toFun := fun K => ⟨K.1.comap f, ?_, ?_⟩
      invFun := fun M => ⟨M.1.map f, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x hx
    have h1 : f x = 1 := MonoidHom.mem_ker.mp hx
    show f x ∈ K.1
    rw [h1]
    exact K.1.one_mem
  · rw [Subgroup.index_comap_of_surjective K.1 hf]
    exact K.2
  · rw [Subgroup.index_map_eq M.1 hf M.2.1]
    exact M.2.2
  · intro K
    refine Subtype.ext ?_
    exact Subgroup.map_comap_eq_self_of_surjective hf K.1
  · intro M
    refine Subtype.ext ?_
    show (M.1.map f).comap f = M.1
    rw [Subgroup.comap_map_eq, sup_comm]
    exact sup_eq_right.mpr M.2.1

/-- **The quotient by the commutator subgroup versus the quotient by its closure.**  If
every index-`n` normal subgroup of the topological group `G` is open, then the abstract
abelianisation `G ⧸ commutator G` and the topological abelianisation
`G ⧸ (commutator G).topologicalClosure` have the same number of subgroups of index `n`.

The point is that `M ⊇ commutator G` forces `M` to be normal (for `g ∈ G`, `m ∈ M` one has
`g * m * g⁻¹ = ⁅g, m⁆ * m ∈ M`), so `M` is open, hence closed, hence contains
`(commutator G).topologicalClosure`; thus the two sets of index-`n` subgroups from
`numIndexSubgroups_eq_natCard_comap` coincide. -/
theorem numIndexSubgroups_quotient_commutator_eq_topologicalClosure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ)
    (hopen : ∀ M : Subgroup G, M.index = n → M.Normal → IsOpen (M : Set G)) :
    NK.LocalAnabelian.numIndexSubgroups n (G ⧸ commutator G) =
      NK.LocalAnabelian.numIndexSubgroups n (G ⧸ (commutator G).topologicalClosure) := by
  rw [numIndexSubgroups_eq_natCard_comap (QuotientGroup.mk' (commutator G))
      (QuotientGroup.mk'_surjective (commutator G)) n,
    numIndexSubgroups_eq_natCard_comap (QuotientGroup.mk' (commutator G).topologicalClosure)
      (QuotientGroup.mk'_surjective _) n,
    QuotientGroup.ker_mk' (commutator G),
    QuotientGroup.ker_mk' (commutator G).topologicalClosure]
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro M
  constructor
  · rintro ⟨hSM, hidx⟩
    have hnorm : M.Normal := by
      refine Subgroup.Normal.mk fun m hm g => ?_
      have h1 : ⁅g, m⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top m)
      have h2 : ⁅g, m⁆ * m ∈ M := M.mul_mem (hSM h1) hm
      have h3 : g * m * g⁻¹ = ⁅g, m⁆ * m := by rw [commutatorElement_def]; group
      rwa [h3]
    exact ⟨Subgroup.topologicalClosure_minimal (commutator G) hSM
      (Subgroup.isClosed_of_isOpen M (hopen M hidx hnorm)), hidx⟩
  · rintro ⟨hCM, hidx⟩
    exact ⟨le_trans (Subgroup.le_topologicalClosure (commutator G)) hCM, hidx⟩

/-- **The abelianised Frattini rank from the maximal abelian subextension**, with the
openness hypothesis which makes the transfer true.

If every index-`p` normal subgroup of `Gal(K'/κ)` is open (true for `p`-adic `κ` by
Nikolov–Segal) and `Gal(maxAbelianSubext κ K'/κ)` has Frattini rank `p^r`, then
`Gal(K'/κ)^{ab}` does. -/
theorem hasAbelianFrattiniRank_of_maxAbelian_of_isOpen {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsGalois κ K'] {p r : ℕ}
    (hopen : ∀ H : Subgroup (Gal(K'/κ)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/κ))))
    (h : NK.LocalAnabelian.HasFrattiniRank p r
      (NK.LocalReciprocity.maxAbelianSubext κ K' ≃ₐ[κ]
        NK.LocalReciprocity.maxAbelianSubext κ K')) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p r (Gal(K'/κ)) := by
  haveI : IsGalois κ (NK.LocalReciprocity.maxAbelianSubext κ K') := inferInstance
  haveI : Normal κ (NK.LocalReciprocity.maxAbelianSubext κ K') := IsGalois.to_normal
  -- the kernel of the restriction map is the closure of the commutator subgroup
  have hker : (AlgEquiv.restrictNormalHom (NK.LocalReciprocity.maxAbelianSubext κ K')).ker =
      (commutator (Gal(K'/κ))).topologicalClosure :=
    (IntermediateField.restrictNormalHom_ker _).trans (by
      rw [NK.LocalReciprocity.maxAbelianSubext]
      exact fixingSubgroup_fixedField_eq_topologicalClosure (commutator (Gal(K'/κ))))
  have hq : NK.LocalAnabelian.numIndexSubgroups p
      (Gal(K'/κ) ⧸ (commutator (Gal(K'/κ))).topologicalClosure) = (p ^ r - 1) / (p - 1) := by
    rw [numIndexSubgroups_eq_natCard_comap
      (QuotientGroup.mk' (commutator (Gal(K'/κ))).topologicalClosure)
      (QuotientGroup.mk'_surjective _) p, QuotientGroup.ker_mk' _]
    rw [← hker]
    rw [← numIndexSubgroups_eq_natCard_comap
      (AlgEquiv.restrictNormalHom (NK.LocalReciprocity.maxAbelianSubext κ K'))
      (AlgEquiv.restrictNormalHom_surjective K') p]
    exact h
  unfold NK.LocalAnabelian.HasAbelianFrattiniRank NK.LocalAnabelian.HasFrattiniRank
  change NK.LocalAnabelian.numIndexSubgroups p
      (Gal(K'/κ) ⧸ commutator (Gal(K'/κ))) = (p ^ r - 1) / (p - 1)
  rw [numIndexSubgroups_quotient_commutator_eq_topologicalClosure (G := Gal(K'/κ)) p hopen]
  exact hq

end

end NK.LocalInputs.AbelianRank
