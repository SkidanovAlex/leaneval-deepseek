/-
  WilG2 : the left inverse law of the bijection between decorated ordered finpartitions of
  `Fin m` and (size datum of `m`, permutation of `Fin m`).

  `invData x.sizeData x.perm` has first component `ofp x.sizeData x.perm = x.1`
  (`ofp_sizeData_perm`) and second component's order of the parts
  `sigma x.sizeData x.perm = x.2.1` (`sigma_sizeData_perm`).  The remaining content -- the
  internal orderings of the parts -- is the substance of this file: the `j`-th chunk of
  `(x.sizeData, x.perm)` is the part `x.2.1 j`, and its internal order `tau`, which enumerates the
  chunk in the order in which `x.perm` lists it, is the internal decoration `x.2.2` transported
  along the identification of `Fin ((chunk ... j).card)` with `Fin (x.1.partSize (x.2.1 j))`.
-/
import Mathlib
import Submission.Work.WilG2.Bijection

set_option autoImplicit false
noncomputable section

namespace Work.WilG2.InvData

/-! ### Generic heterogeneous-equality tools -/

/-- Heterogeneous equality of pairs, from heterogeneous equalities of the components. -/
lemma leftInv_heq_prod {α β α' β' : Type} {a : α} {a' : α'} {b : β} {b' : β'}
    (ha : HEq a a') (hb : HEq b b') : HEq (a, b) (a', b') := by
  cases ha
  cases hb
  exact HEq.rfl

/-- Two values of a dependent function at equal indices are heterogeneously equal. -/
lemma leftInv_heq_of_apply_eq {α : Type} {β : α → Type} {a b : α} (h : a = b) (f : (i : α) → β i) :
    HEq (f a) (f b) := by
  cases h
  exact HEq.rfl

/-- Conjugation by a `finCongr` is heterogeneously equal to the identity. -/
lemma leftInv_conj_heq {n₁ n₂ : ℕ} (h : n₁ = n₂) (g : Equiv.Perm (Fin n₂)) :
    HEq ((finCongr h).trans (g.trans (finCongr h).symm)) g := by
  cases h
  rw [heq_iff_eq]
  ext u
  simp [finCongr]

/-- `Fin.cast` and its inverse cancel. -/
lemma leftInv_cast_symm_cast {n m : ℕ} (h : n = m) (u : Fin n) :
    Fin.cast h.symm (Fin.cast h u) = u :=
  Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-! ### The enumeration of a chunk -/

/-- The increasing enumeration of the `j`-th chunk of `(x.sizeData, x.perm)` is the enumeration
of the part `x.2.1 j` of `x`, transported along the identification `chunk x.sizeData x.perm j =
Finset.image (x.1.emb (x.2.1 j)) Finset.univ` of cardinalities. -/
lemma leftInv_orderEmbOfFin_chunk (m : ℕ) (x : OFPData m) (j : Fin x.1.length) :
    ⇑((chunk x.sizeData x.perm j).orderEmbOfFin rfl)
      = fun u : Fin ((chunk x.sizeData x.perm j).card) =>
          x.1.emb (x.2.1 j) (Fin.cast (chunk_card x.sizeData x.perm j) u) := by
  symm
  refine Finset.orderEmbOfFin_unique rfl ?_ ?_
  · intro u
    have h : x.1.emb (x.2.1 j) (Fin.cast (chunk_card x.sizeData x.perm j) u)
        ∈ Finset.image (x.1.emb (x.2.1 j)) Finset.univ :=
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    rwa [← chunk_sizeData_perm x j] at h
  · intro u v huv
    exact (x.1.emb_strictMono (x.2.1 j))
      ((Fin.castOrderIso (chunk_card x.sizeData x.perm j)).strictMono huv)

/-- The position of the `s`-th point of the `j`-th chunk, in the increasing enumeration of that
chunk, is given by the decoration of `x` on the part `x.2.1 j`. -/
lemma leftInv_cast_tau (m : ℕ) (x : OFPData m) (j : Fin x.1.length)
    (s : Fin ((chunk x.sizeData x.perm j).card)) :
    Fin.cast (chunk_card x.sizeData x.perm j) (tau x.sizeData x.perm j s)
      = x.2.2 (x.2.1 j) (Fin.cast (chunk_card x.sizeData x.perm j) s) := by
  apply (x.1.emb_strictMono (x.2.1 j)).injective
  rw [← OFPData.perm_unflat_symm x j (Fin.cast (chunk_card x.sizeData x.perm j) s)]
  rw [← congrFun (leftInv_orderEmbOfFin_chunk m x j) (tau x.sizeData x.perm j s)]
  rw [← Finset.coe_orderIsoOfFin_apply, tau_spec, delta'_apply]

/-! ### The internal order `tau` in terms of the decoration of `x` -/

/-- The internal order of the `j`-th chunk, as an element of `Fin ((chunk ...).card)`, is the
decoration `x.2.2` of the part `x.2.1 j` conjugated by the identification of the two index types. -/
lemma leftInv_tau_eq (m : ℕ) (x : OFPData m) (j : Fin x.1.length) :
    tau x.sizeData x.perm j
      = (finCongr (chunk_card x.sizeData x.perm j)).trans
          ((x.2.2 (x.2.1 j)).trans (finCongr (chunk_card x.sizeData x.perm j)).symm) := by
  refine Equiv.ext (fun s => ?_)
  have h1 : ((finCongr (chunk_card x.sizeData x.perm j)).trans
        ((x.2.2 (x.2.1 j)).trans (finCongr (chunk_card x.sizeData x.perm j)).symm)) s
      = Fin.cast (chunk_card x.sizeData x.perm j).symm
          (x.2.2 (x.2.1 j) (Fin.cast (chunk_card x.sizeData x.perm j) s)) := by
    rw [Equiv.trans_apply, Equiv.trans_apply, finCongr_apply, finCongr_symm, finCongr_apply]
  rw [h1, ← leftInv_cast_tau m x j s]
  exact leftInv_cast_symm_cast (chunk_card x.sizeData x.perm j) (tau x.sizeData x.perm j s)

/-- The reconstructed internal orders are the original decorations of `x`. -/
lemma leftInv_pi_heq (m : ℕ) (x : OFPData m) (i : Fin (ofp x.sizeData x.perm).length) :
    HEq (pi x.sizeData x.perm i) (x.2.2 i) := by
  have hj : x.2.1 ((sigma x.sizeData x.perm).symm i) = i := by
    rw [← sigma_sizeData_perm x]
    exact Equiv.apply_symm_apply _ _
  have h1 : pi x.sizeData x.perm i
      = tau x.sizeData x.perm ((sigma x.sizeData x.perm).symm i) := rfl
  rw [h1, leftInv_tau_eq m x ((sigma x.sizeData x.perm).symm i)]
  exact HEq.trans
    (leftInv_conj_heq (chunk_card x.sizeData x.perm ((sigma x.sizeData x.perm).symm i))
      (x.2.2 (x.2.1 ((sigma x.sizeData x.perm).symm i))))
    (leftInv_heq_of_apply_eq hj x.2.2)

/-! ### The left inverse law -/

theorem left_inv (m : ℕ) (x : OFPData m) : invData x.sizeData x.perm = x := by
  refine Sigma.ext (ofp_sizeData_perm x) ?_
  show HEq (sigma x.sizeData x.perm, pi x.sizeData x.perm) (x.2.1, x.2.2)
  refine leftInv_heq_prod (heq_of_eq (sigma_sizeData_perm x)) ?_
  refine Function.hfunext rfl ?_
  intro i i' hii
  exact HEq.trans (leftInv_pi_heq m x i) (leftInv_heq_of_apply_eq (eq_of_heq hii) x.2.2)

end Work.WilG2.InvData
