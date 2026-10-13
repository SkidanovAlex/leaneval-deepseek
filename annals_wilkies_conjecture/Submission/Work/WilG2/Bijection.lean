/-
  WilG2 : the bijection between decorated ordered finpartitions of `Fin m` and
  (size datum of `m`, permutation of `Fin m`).

  An `OFPData m` is an ordered finpartition of `Fin m` together with an ordering of its parts
  and an ordering of the elements of each part.  Reading the parts in the prescribed order, each
  enumerated in the prescribed way, produces a listing of `Fin m`, i.e. a permutation of `Fin m`,
  while the sizes of the parts give a `SizeData m`; this is the bijection which is the
  combinatorial heart of `ofp_weighted_sum`.

  The two inverse laws are proved separately (see `Submission/Work/WilG2/InvData/`), so that the
  equivalence itself can be assembled on top of them.
-/
import Submission.Work.WilG2.Sorting
import Submission.Work.WilG2.OfpExt
import Submission.Work.WilG2.SizeData
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.WilG2

variable {m : ℕ}

/-! ### Congruence lemmas for the sorting constructions -/

section Congr

variable {k : ℕ}

lemma ofpOfBlocks_congr {B B' : Fin k → Finset (Fin m)} (h : B = B')
    (hne : ∀ i, (B i).Nonempty) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (hcover : ∀ j : Fin m, ∃ i, j ∈ B i) :
    ofpOfBlocks B hne hdisj hcover =
      ofpOfBlocks B' (h ▸ hne) (h ▸ hdisj) (h ▸ hcover) := by
  cases h
  rfl

lemma sortPerm_congr {B B' : Fin k → Finset (Fin m)} (h : B = B')
    (hne : ∀ i, (B i).Nonempty) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) :
    sortPerm B hne hdisj = sortPerm B' (h ▸ hne) (h ▸ hdisj) := by
  cases h
  rfl

end Congr

/-! ### Decorated ordered finpartitions -/

/-- A decorated ordered finpartition of `Fin m`: an ordered finpartition together with an order of
its parts (the first permutation) and an order of the elements inside each part (the second). -/
@[reducible] def OFPData (m : ℕ) : Type :=
  Σ d : OrderedFinpartition m, Equiv.Perm (Fin d.length) ×
    ((i : Fin d.length) → Equiv.Perm (Fin (d.partSize i)))

namespace OFPData

variable (x : OFPData m)

/-- The sizes of the parts, in the prescribed order of the parts. -/
@[reducible] def sizes (x : OFPData m) : Fin x.1.length → ℕ := fun j => x.1.partSize (x.2.1 j)

lemma sizes_pos (x : OFPData m) (j : Fin x.1.length) : 0 < x.sizes j :=
  x.1.partSize_pos (x.2.1 j)

lemma sizes_sum (x : OFPData m) : ∑ j, x.sizes j = m := by
  rw [Fintype.sum_equiv x.2.1 (fun j : Fin x.1.length => x.1.partSize (x.2.1 j))
    (fun i => x.1.partSize i) (fun j => rfl)]
  exact sum_partSize x.1

/-- The size datum of a decorated finpartition: the sizes in the prescribed order of the parts. -/
@[reducible] def sizeData (x : OFPData m) : SizeData m :=
  SizeData.mk x.sizes ⟨x.sizes_pos, x.sizes_sum⟩

@[simp] lemma sizeData_len (x : OFPData m) : SizeData.len x.sizeData = x.1.length := rfl

@[simp] lemma sizeData_sizes (x : OFPData m) : SizeData.sizes x.sizeData = x.sizes := rfl

/-- The unflattening of `Fin m` into the parts, according to the sizes. -/
@[reducible] def unflat (x : OFPData m) : Fin m ≃ (Σ j : Fin x.1.length, Fin (x.sizes j)) :=
  SizeData.unflat x.sizeData

lemma unflat_symm_apply (x : OFPData m) (j : Fin x.1.length) (r : Fin (x.sizes j)) :
    ((x.unflat).symm ⟨j, r⟩ : ℕ) =
      (∑ i : Fin j.val, x.sizes (Fin.castLE j.isLt.le i)) + (r : ℕ) :=
  SizeData.unflat_symm_apply x.sizeData j r

/-- Reading the parts in the prescribed order, each enumerated in the prescribed way, gives a
permutation of `Fin m`. -/
@[reducible] def perm (x : OFPData m) : Equiv.Perm (Fin m) :=
  x.unflat.trans ((Equiv.sigmaCongr x.2.1 (fun j => x.2.2 (x.2.1 j))).trans x.1.equivSigma)

lemma perm_unflat_symm (x : OFPData m) (j : Fin x.1.length) (r : Fin (x.sizes j)) :
    x.perm (x.unflat.symm ⟨j, r⟩) = x.1.emb (x.2.1 j) (x.2.2 (x.2.1 j) r) := by
  rw [perm, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply]
  rfl

end OFPData

/-! ### The inverse construction -/

section Inv

/-- The `j`-th chunk of `Fin m`: the elements which the permutation `ρ` places in the `j`-th
block. -/
@[reducible] def chunk (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) : Finset (Fin m) :=
  Finset.image (fun r : Fin (SizeData.sizes y j) => ρ ((SizeData.unflat y).symm ⟨j, r⟩))
    Finset.univ

lemma chunk_card (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    (chunk y ρ j).card = SizeData.sizes y j := by
  have hinj : Function.Injective (fun r : Fin (SizeData.sizes y j) =>
      ρ ((SizeData.unflat y).symm ⟨j, r⟩)) := by
    intro r r' h
    have h1 : (⟨j, r⟩ : (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i)) = ⟨j, r'⟩ :=
      (SizeData.unflat y).symm.injective (ρ.injective h)
    exact Fin.ext (congrArg
      (fun p : (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i) => (p.2 : ℕ)) h1)
  rw [chunk, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma chunk_nonempty (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    (chunk y ρ j).Nonempty :=
  Finset.card_pos.mp (by rw [chunk_card]; exact SizeData.sizes_pos y j)

lemma chunk_disjoint (y : SizeData m) (ρ : Equiv.Perm (Fin m)) {j j' : Fin (SizeData.len y)}
    (h : j ≠ j') : Disjoint (chunk y ρ j) (chunk y ρ j') := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [chunk, Finset.mem_image] at ha ha'
  obtain ⟨r, -, rfl⟩ := ha
  obtain ⟨r', -, hr'⟩ := ha'
  refine h (congrArg
    (fun p : (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i) => p.1)
    ((SizeData.unflat y).symm.injective (ρ.injective hr'))).symm

lemma chunk_cover (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (a : Fin m) :
    ∃ j, a ∈ chunk y ρ j := by
  refine ⟨((SizeData.unflat y) (ρ.symm a)).1, Finset.mem_image.mpr
    ⟨((SizeData.unflat y) (ρ.symm a)).2, Finset.mem_univ _, ?_⟩⟩
  have hp : (⟨((SizeData.unflat y) (ρ.symm a)).1,
      ((SizeData.unflat y) (ρ.symm a)).2⟩ :
        (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i)) =
      (SizeData.unflat y) (ρ.symm a) := rfl
  rw [hp, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The ordered finpartition reconstructed from a size datum and a permutation: its parts are the
chunks. -/
@[reducible] def ofp (y : SizeData m) (ρ : Equiv.Perm (Fin m)) : OrderedFinpartition m :=
  ofpOfBlocks (chunk y ρ) (chunk_nonempty y ρ) (fun _ _ h => chunk_disjoint y ρ h)
    (chunk_cover y ρ)

/-- The order in which the chunks appear in the reconstructed finpartition. -/
@[reducible] def sigma (y : SizeData m) (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (SizeData.len y)) :=
  sortPerm (chunk y ρ) (chunk_nonempty y ρ) (fun _ _ h => chunk_disjoint y ρ h)

@[simp] lemma length_ofp (y : SizeData m) (ρ : Equiv.Perm (Fin m)) :
    (ofp y ρ).length = SizeData.len y := rfl

@[simp] lemma partSize_ofp (y : SizeData m) (ρ : Equiv.Perm (Fin m))
    (i : Fin (SizeData.len y)) :
    (ofp y ρ).partSize i = (chunk y ρ ((sigma y ρ).symm i)).card := rfl

/-- The enumeration of the `j`-th chunk given by the permutation `ρ`, as a function. -/
@[reducible] def deltaFun (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    Fin (SizeData.sizes y j) → ↥(chunk y ρ j) :=
  fun r => ⟨ρ ((SizeData.unflat y).symm ⟨j, r⟩),
    Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩

lemma deltaFun_injective (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    Function.Injective (deltaFun y ρ j) := by
  intro r r' h
  have h3 : (⟨j, r⟩ : (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i)) = ⟨j, r'⟩ :=
    (SizeData.unflat y).symm.injective (ρ.injective (congrArg Subtype.val h))
  exact Fin.ext (congrArg
    (fun p : (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i) => (p.2 : ℕ)) h3)

/-- The enumeration of the `j`-th chunk given by the permutation `ρ`. -/
@[reducible] def delta (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    Fin (SizeData.sizes y j) ≃ ↥(chunk y ρ j) :=
  Equiv.ofBijective (deltaFun y ρ j)
    ⟨deltaFun_injective y ρ j, by
      intro b
      obtain ⟨r, -, hr⟩ := Finset.mem_image.mp b.2
      exact ⟨r, Subtype.ext hr⟩⟩

/-- The enumeration of the `j`-th chunk given by the permutation `ρ`, as an application. -/
lemma delta_coe (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    ⇑(delta y ρ j) = deltaFun y ρ j := rfl

lemma delta_apply (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y))
    (r : Fin (SizeData.sizes y j)) :
    ((delta y ρ j r : ↥(chunk y ρ j)) : Fin m) = ρ ((SizeData.unflat y).symm ⟨j, r⟩) :=
  congrArg Subtype.val (congrFun (delta_coe y ρ j) r)

/-- The same enumeration, indexed by the cardinality of the chunk. -/
@[reducible] def delta' (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    Fin ((chunk y ρ j).card) ≃ ↥(chunk y ρ j) :=
  (Fin.castOrderIso (chunk_card y ρ j)).toEquiv.trans (delta y ρ j)

lemma delta'_apply (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y))
    (r : Fin ((chunk y ρ j).card)) :
    ((delta' y ρ j r : ↥(chunk y ρ j)) : Fin m) =
      ρ ((SizeData.unflat y).symm ⟨j, Fin.cast (chunk_card y ρ j) r⟩) := by
  rw [delta', Equiv.trans_apply, SizeData.castOrderIso_toEquiv_apply]
  exact delta_apply y ρ j (Fin.cast (chunk_card y ρ j) r)

/-- The internal order of the `j`-th chunk, read off from `ρ`: the `r`-th point of the chunk in
the order given by `ρ` sits at position `r` of its increasing enumeration. -/
@[reducible] def tau (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y)) :
    Equiv.Perm (Fin ((chunk y ρ j).card)) :=
  (delta' y ρ j).trans ((chunk y ρ j).orderIsoOfFin rfl).symm

lemma tau_spec (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (j : Fin (SizeData.len y))
    (r : Fin ((chunk y ρ j).card)) :
    (((chunk y ρ j).orderIsoOfFin rfl) (tau y ρ j r) : ↥(chunk y ρ j)) = delta' y ρ j r :=
  OrderIso.apply_symm_apply ((chunk y ρ j).orderIsoOfFin rfl) (delta' y ρ j r)

/-- The internal orders of the reconstructed decoration: the canonical part `i` is the chunk
indexed by `(sigma y ρ).symm i`, whose internal order is given by `tau`. -/
@[reducible] def pi (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (i : Fin (SizeData.len y)) :
    Equiv.Perm (Fin ((ofp y ρ).partSize i)) :=
  tau y ρ ((sigma y ρ).symm i)

lemma emb_pi (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (i : Fin (SizeData.len y))
    (r : Fin ((ofp y ρ).partSize i)) :
    (ofp y ρ).emb i (pi y ρ i r) =
      ρ ((SizeData.unflat y).symm ⟨(sigma y ρ).symm i,
        Fin.cast (chunk_card y ρ ((sigma y ρ).symm i)) r⟩) := by
  rw [show (ofp y ρ).emb i =
      ((chunk y ρ ((sigma y ρ).symm i)).orderEmbOfFin rfl :
        Fin ((chunk y ρ ((sigma y ρ).symm i)).card) → Fin m) from rfl]
  rw [show pi y ρ i r = tau y ρ ((sigma y ρ).symm i) r from rfl]
  rw [← Finset.coe_orderIsoOfFin_apply, tau_spec, delta'_apply]

/-- The inverse construction: the decorated finpartition reconstructed from a size datum and a
permutation. -/
@[reducible] def invData (y : SizeData m) (ρ : Equiv.Perm (Fin m)) : OFPData m :=
  ⟨ofp y ρ, sigma y ρ, pi y ρ⟩

/-- The chunks of a decorated finpartition are the parts of its ordered finpartition. -/
lemma chunk_sizeData_perm (x : OFPData m) (j : Fin x.1.length) :
    chunk x.sizeData x.perm j = Finset.image (x.1.emb (x.2.1 j)) Finset.univ := by
  ext a
  rw [chunk, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨r, -, rfl⟩
    exact ⟨x.2.2 (x.2.1 j) r, Finset.mem_univ _, (x.perm_unflat_symm j r).symm⟩
  · rintro ⟨r, -, rfl⟩
    refine ⟨(x.2.2 (x.2.1 j)).symm r, Finset.mem_univ _, ?_⟩
    rw [x.perm_unflat_symm j ((x.2.2 (x.2.1 j)).symm r)]
    exact congrArg (x.1.emb (x.2.1 j)) (Equiv.apply_symm_apply (x.2.2 (x.2.1 j)) r)

/-- The reconstructed ordered finpartition is the original one. -/
lemma ofp_sizeData_perm (x : OFPData m) :
    ofp x.sizeData x.perm = x.1 :=
  (ofpOfBlocks_congr (funext fun j => chunk_sizeData_perm x j) _ _ _).trans
    (OfpMax.ofpOfBlocks_image_emb_eq x.1 x.2.1 _ _ _)

/-- The reconstructed part order is the original one. -/
lemma sigma_sizeData_perm (x : OFPData m) :
    sigma x.sizeData x.perm = x.2.1 :=
  (sortPerm_congr (funext fun j => chunk_sizeData_perm x j) _ _).trans
    (OfpMax.sortPerm_image_emb x.1 x.2.1 _ _)

end Inv

/-! ### The forward map and the weights -/

/-- The forward map of the bijection: a decorated finpartition gives its sizes (in the prescribed
order of the parts) and the resulting permutation of `Fin m`. -/
@[reducible] def toMid (x : OFPData m) : SizeData m × Equiv.Perm (Fin m) := (x.sizeData, x.perm)

/-- The weight of a decorated ordered finpartition. -/
@[reducible] def ofpDataWeight (a bg : ℕ → ℝ) (x : OFPData m) : ℝ :=
  bg x.1.length * ∏ i : Fin x.1.length, a (x.1.partSize i)

/-- The weight of the corresponding pair (size datum, permutation). -/
@[reducible] def midWeight (a bg : ℕ → ℝ) (p : SizeData m × Equiv.Perm (Fin m)) : ℝ :=
  bg (SizeData.len p.1) * ∏ i : Fin (SizeData.len p.1), a (SizeData.sizes p.1 i)

lemma ofpDataWeight_eq_midWeight (a bg : ℕ → ℝ) (x : OFPData m) :
    ofpDataWeight a bg x = midWeight a bg (toMid x) := by
  show bg x.1.length * ∏ i : Fin x.1.length, a (x.1.partSize i) =
    bg (SizeData.len x.sizeData) * ∏ i : Fin (SizeData.len x.sizeData),
      a (SizeData.sizes x.sizeData i)
  rw [show (∏ i : Fin (SizeData.len x.sizeData), a (SizeData.sizes x.sizeData i)) =
      ∏ i : Fin x.1.length, a (x.1.partSize i) from
    Equiv.prod_comp x.2.1 (fun i => a (x.1.partSize i))]

/-- The weighted sum over decorated ordered finpartitions, written as the sum over
`OrderedFinpartition` with the factorials. -/
lemma sum_ofpData (a bg : ℕ → ℝ) :
    ∑ x : OFPData m, ofpDataWeight a bg x =
      ∑ c : OrderedFinpartition m,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (bg c.length * ∏ i : Fin c.length, a (c.partSize i)) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  show (∑ _ : Equiv.Perm (Fin c.length),
      ∑ _ : (i : Fin c.length) → Equiv.Perm (Fin (c.partSize i)),
        (bg c.length * ∏ i : Fin c.length, a (c.partSize i))) = _
  have h1 : ∀ σ : Equiv.Perm (Fin c.length),
      (∑ _ : (i : Fin c.length) → Equiv.Perm (Fin (c.partSize i)),
        (bg c.length * ∏ i : Fin c.length, a (c.partSize i))) =
      (∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
        (bg c.length * ∏ i : Fin c.length, a (c.partSize i)) := by
    intro σ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Fintype.card_pi]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [Finset.sum_congr rfl fun σ _ => h1 σ]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  ring

end Work.WilG2
