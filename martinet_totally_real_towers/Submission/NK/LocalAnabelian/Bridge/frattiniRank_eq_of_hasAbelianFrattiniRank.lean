import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.ProfiniteP.Frattini
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexSubgroups_abelianization_eq_natCard_galois

namespace NK.LocalAnabelian.Bridge

open Subgroup

/-- **Normal index-`p` subgroups of `G` are the index-`p` subgroups of the Frattini
quotient `G ⧸ Φ_p(G)`**, provided every normal index-`p` subgroup of `G` is open.

A normal subgroup of index a prime `p` contains the `p`-th powers and the commutators, and
by hypothesis it is open, hence closed: so it contains the closure `Φ_p(G)`.  Conversely a
subgroup containing `Φ_p(G)` corresponds to a subgroup of the quotient. -/
lemma natCard_normal_indexP_eq_frattiniQuotient {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hopen : ∀ H : Subgroup G, H.index = p → H.Normal → IsOpen (H : Set G)) :
    Nat.card {K : Subgroup G // K.index = p ∧ K.Normal} =
      Nat.card {K : Subgroup (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) // K.index = p} := by
  classical
  -- **Step 1.** For an index-`p` subgroup, being normal is the same as containing `Φ_p(G)`.
  have hkey : ∀ K : Subgroup G, K.index = p →
      (K.Normal ↔ NK.ProfiniteP.frattiniSubgroup p G ≤ K) := by
    intro K hK
    constructor
    · intro hN
      have hopenK : IsOpen (K : Set G) := hopen K hK hN
      refine NK.ProfiniteP.frattiniSubgroup_le (K.isClosed_of_isOpen hopenK) ?_ ?_
      · rw [NK.ProfiniteP.powSubgroup, Subgroup.closure_le K]
        rintro _ ⟨g, rfl⟩
        rw [← hK]
        exact Subgroup.pow_index_mem K g
      · rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
        have hcard : Nat.card (G ⧸ K) = p := by rw [← Subgroup.index_eq_card]; exact hK
        exact (isCyclic_of_prime_card hcard).isMulCommutative
    · intro hle
      have hcomm : commutator G ≤ K :=
        le_trans (NK.ProfiniteP.commutator_le_frattiniSubgroup p G) hle
      have h1 : ⁅(⊤ : Subgroup G), K⁆ ≤ K :=
        le_trans (Subgroup.commutator_mono le_rfl le_top) hcomm
      exact Subgroup.commutator_top_left_le_iff.mp h1
  -- **Step 2.** Replace the normality condition by the condition `Φ_p(G) ≤ K`.
  have e1 : {K : Subgroup G // K.index = p ∧ K.Normal} ≃
      {K : Subgroup G // K.index = p ∧ NK.ProfiniteP.frattiniSubgroup p G ≤ K} :=
    Equiv.subtypeEquivRight fun K => by
      constructor
      · rintro ⟨hK, hN⟩; exact ⟨hK, (hkey K hK).mp hN⟩
      · rintro ⟨hK, hle⟩; exact ⟨hK, (hkey K hK).mpr hle⟩
  -- **Step 3.** The quotient correspondence.
  have e2 : {K : Subgroup G // K.index = p ∧ NK.ProfiniteP.frattiniSubgroup p G ≤ K} ≃
      {K : Subgroup (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) // K.index = p} :=
    { toFun := fun H =>
        ⟨H.1.map (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G)), by
          rw [Subgroup.index_map_eq H.1 (QuotientGroup.mk'_surjective _) (by
            rw [QuotientGroup.ker_mk']; exact H.2.2)]
          exact H.2.1⟩
      invFun := fun K =>
        ⟨K.1.comap (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G)), by
          refine ⟨?_, ?_⟩
          · rw [Subgroup.index_comap_of_surjective K.1 (QuotientGroup.mk'_surjective _)]
            exact K.2
          · intro x hx
            have h1 : QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G) x = 1 := by
              rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
              exact hx
            show QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G) x ∈ K.1
            rw [h1]
            exact K.1.one_mem⟩
      left_inv := fun H => by
        apply Subtype.ext
        show Subgroup.comap (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G))
            (Subgroup.map (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G)) H.1) = H.1
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        exact sup_eq_left.mpr H.2.2
      right_inv := fun K => by
        apply Subtype.ext
        show Subgroup.map (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G))
            (Subgroup.comap (QuotientGroup.mk' (NK.ProfiniteP.frattiniSubgroup p G)) K.1) = K.1
        rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _
          (QuotientGroup.mk'_surjective (NK.ProfiniteP.frattiniSubgroup p G)), top_inf_eq] }
  exact Nat.card_congr (e1.trans e2)


/-! ## Counting codimension-one `𝔽_p`-submodules

The Frattini quotient `G ⧸ Φ_p(G)` is an elementary abelian `p`-group, i.e. a vector space
over `𝔽_p = ZMod p`, and its index-`p` subgroups are exactly its codimension-one subspaces.
Counting those is the linear algebra of this file; it is the group-theoretic form in which
the arithmetic counts of `NK.LocalAnabelian` are expressed. -/

/-- The index of a submodule, computed as the cardinality of the (module) quotient. -/
theorem index_toAddSubgroup_eq_natCard_quotient {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (W : Submodule R M) : W.toAddSubgroup.index = Nat.card (M ⧸ W) := by
  rw [AddSubgroup.index_eq_card]
  refine Nat.card_congr (Quotient.congr (Equiv.refl M) (fun a b => ?_))
  show QuotientAddGroup.leftRel W.toAddSubgroup a b ↔ Submodule.quotientRel W a b
  rw [Submodule.quotientRel_def, QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup]
  constructor
  · intro h
    have he : a - b = -(-a + b) := by abel
    rw [he]; exact W.neg_mem h
  · intro h
    have he : -a + b = -(a - b) := by abel
    rw [he]; exact W.neg_mem h

/-- A finite `ZMod p`-module of cardinality `p` is one-dimensional. -/
theorem finrank_eq_one_of_natCard_eq {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (hM : Nat.card M = p) : Module.finrank (ZMod p) M = 1 := by
  have hp : p.Prime := Fact.out
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hp.ne_zero)
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite (R := ZMod p) (M := M)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M), Nat.card_zmod] at hM
  have h2 : p ^ Module.finrank (ZMod p) M = p ^ 1 := by rw [hM, pow_one]
  exact Nat.pow_right_injective hp.two_le h2

/-- Conversely, a one-dimensional `ZMod p`-module has cardinality `p`. -/
theorem natCard_eq_of_finrank_eq_one {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (hM : Module.finrank (ZMod p) M = 1) : Nat.card M = p := by
  have hp : p.Prime := Fact.out
  haveI : Module.Finite (ZMod p) M := by
    by_contra hnf
    rw [Module.finrank_of_not_finite (R := ZMod p) (M := M) hnf] at hM
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M), hM, pow_one, Nat.card_zmod]

/-- A one-dimensional `ZMod p`-module is finite. -/
theorem finite_of_finrank_eq_one {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (h : Module.finrank (ZMod p) M = 1) : Module.Finite (ZMod p) M := by
  by_contra hnf
  rw [Module.finrank_of_not_finite (R := ZMod p) (M := M) hnf] at h
  omega

/-- **Counting the codimension-one submodules of a `ZMod p`-module.**  A submodule `W` of a
`ZMod p`-module `V` has index `p` exactly when the quotient `V ⧸ W` is one-dimensional, and
those submodules are the codimension-one subspaces: they correspond to the lines of the dual
`Vᐟ = Module.Dual (ZMod p) V` via the annihilator `W ↦ Wᵃ` and its inverse `Λ ↦ Λ_𝔞`, hence
number `(p ^ dim V - 1)/(p - 1)` — one per point of the projective space `ℙ Vᐟ`.

For an infinite-dimensional `V` both sides are `0` (`Module.finrank` vanishes on the
infinite-dimensional part and there are infinitely many hyperplanes). -/
theorem natCard_indexP_submodule {p : ℕ} [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] :
    Nat.card {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} =
      (p ^ Module.finrank (ZMod p) V - 1) / (p - 1) := by
  have hp : p.Prime := Fact.out
  -- Index `p` is codimension one.
  have hA : ∀ W : Submodule (ZMod p) V, W.toAddSubgroup.index = p ↔
      Module.finrank (ZMod p) (V ⧸ W) = 1 := by
    intro W
    rw [index_toAddSubgroup_eq_natCard_quotient W]
    exact ⟨fun h => finrank_eq_one_of_natCard_eq h, fun h => natCard_eq_of_finrank_eq_one h⟩
  -- Codimension-one subspaces of `V` are the codimension-one subspaces of the dual.
  have hfinrank : ∀ W : Submodule (ZMod p) V,
      Module.finrank (ZMod p) (V ⧸ W) = Module.finrank (ZMod p) ↥(W.dualAnnihilator) := by
    intro W
    exact (Subspace.dual_finrank_eq (K := ZMod p) (V := V ⧸ W)).symm.trans
      W.dualQuotEquivDualAnnihilator.finrank_eq
  have eB : {W : Submodule (ZMod p) V // Module.finrank (ZMod p) (V ⧸ W) = 1} ≃
      {H : Submodule (ZMod p) (Module.Dual (ZMod p) V) // Module.finrank (ZMod p) ↥H = 1} :=
    { toFun := fun W => ⟨W.1.dualAnnihilator, by rw [← hfinrank W.1, W.2]⟩
      invFun := fun H => ⟨H.1.dualCoannihilator, by
        haveI : Module.Finite (ZMod p) ↥H.1 := finite_of_finrank_eq_one (p := p) (M := ↥H.1) H.2
        rw [hfinrank H.1.dualCoannihilator, Subspace.dualCoannihilator_dualAnnihilator_eq, H.2]⟩
      left_inv := fun W => Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
      right_inv := fun H => by
        haveI : Module.Finite (ZMod p) ↥H.1 := finite_of_finrank_eq_one (p := p) (M := ↥H.1) H.2
        exact Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq }
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun W => hA W),
    Nat.card_congr eB,
    Nat.card_congr (Projectivization.equivSubmodule (ZMod p) (Module.Dual (ZMod p) V)).symm,
    Projectivization.card'' (ZMod p) (Module.Dual (ZMod p) V), Nat.card_zmod]
  -- Cardinality of the dual: `p ^ dim V` in finite dimension, `0` (as is `p ^ 0`) otherwise.
  by_cases hV : Module.Finite (ZMod p) V
  · have hfin : Module.Finite (ZMod p) (Module.Dual (ZMod p) V) :=
      (Module.finite_dual_iff (ZMod p)).mpr hV
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Module.Dual (ZMod p) V),
      Subspace.dual_finrank_eq, Nat.card_zmod]
  · have hnf : ¬ Module.Finite (ZMod p) (Module.Dual (ZMod p) V) :=
      fun hh => hV ((Module.finite_dual_iff (ZMod p)).mp hh)
    have hInf : Infinite (Module.Dual (ZMod p) V) :=
      not_finite_iff_infinite.mp fun hf =>
        hnf (Module.Finite.of_finite (R := ZMod p) (M := Module.Dual (ZMod p) V))
    rw [Nat.card_eq_zero.mpr (Or.inr hInf),
      Module.finrank_of_not_finite (R := ZMod p) (M := V) hV]
    simp

theorem frattiniRank_eq_of_hasAbelianFrattiniRank {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {p r : ℕ} [Fact p.Prime]
    (hopen : ∀ H : Subgroup G, H.index = p → H.Normal → IsOpen (H : Set G))
    (h : HasAbelianFrattiniRank p r G) : NK.ProfiniteP.frattiniRank p G = r := by
  have hp : p.Prime := Fact.out
  -- The count of index-`p` subgroups of `Abelianization G` is the count of index-`p`
  -- subgroups of the Frattini quotient `G ⧸ Φ_p(G)`.
  have hB : numIndexSubgroups p (Abelianization G) =
      Nat.card {K : Subgroup (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) // K.index = p} := by
    rw [GaloisCorrespondence.numIndexSubgroups_abelianization_eq_natCard_normal_indexPrime
      (G := G) p hp]
    exact natCard_normal_indexP_eq_frattiniQuotient hopen
  -- That count is the number of hyperplanes of `G ⧸ Φ_p(G)` as an `𝔽_p`-vector space.
  have hC : Nat.card {K : Subgroup (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) // K.index = p} =
      (p ^ NK.ProfiniteP.frattiniRank p G - 1) / (p - 1) := by
    have e3 : {K : Subgroup (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) // K.index = p} ≃
        {S : AddSubgroup (Additive (G ⧸ NK.ProfiniteP.frattiniSubgroup p G)) // S.index = p} :=
      Equiv.subtypeEquiv Subgroup.toAddSubgroup.toEquiv fun K => by
        change K.index = p ↔ (Subgroup.toAddSubgroup K).index = p
        constructor
        · intro hh; rwa [Subgroup.index_toAddSubgroup]
        · intro hh; rwa [Subgroup.index_toAddSubgroup] at hh
    have e4 : {S : AddSubgroup (Additive (G ⧸ NK.ProfiniteP.frattiniSubgroup p G)) //
          S.index = p} ≃
        {W : Submodule (ZMod p) (Additive (G ⧸ NK.ProfiniteP.frattiniSubgroup p G)) //
          W.toAddSubgroup.index = p} :=
      Equiv.subtypeEquiv (AddSubgroup.toZModSubmodule p).toEquiv fun S => by
        change S.index = p ↔ (AddSubgroup.toZModSubmodule p S).toAddSubgroup.index = p
        rw [AddSubgroup.toZModSubmodule_toAddSubgroup]
    rw [Nat.card_congr (e3.trans e4),
      natCard_indexP_submodule (p := p) (Additive (G ⧸ NK.ProfiniteP.frattiniSubgroup p G)),
      ← NK.ProfiniteP.frattiniRank_def p G]
  have h1 : HasFrattiniRank p r (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) := by
    unfold HasFrattiniRank numIndexSubgroups
    rw [← hB]
    exact h
  have h2 : HasFrattiniRank p (NK.ProfiniteP.frattiniRank p G)
      (G ⧸ NK.ProfiniteP.frattiniSubgroup p G) := by
    unfold HasFrattiniRank numIndexSubgroups
    exact hC
  exact (eq_of_hasFrattiniRank hp h1 h2).symm

end NK.LocalAnabelian.Bridge
