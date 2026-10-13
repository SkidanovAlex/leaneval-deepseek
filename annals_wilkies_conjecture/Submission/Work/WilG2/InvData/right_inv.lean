/-
  WilG2 : the right inverse law for the bijection of `Bijection.lean`.

  Reading a decorated ordered finpartition of `Fin m` in the prescribed order of its parts, each
  part enumerated in the prescribed way, gives a pair (size datum, permutation of `Fin m`); this is
  `toMid`.  Conversely, `invData y ρ` reconstructs a decorated finpartition from `y` and `ρ` by
  cutting `Fin m` into the chunks `chunk y ρ j` (the set of elements that `ρ` places in the `j`-th
  block), ordering the chunks by the permutation `sigma y ρ` and each chunk internally by `tau`.

  Here we prove that this reconstruction is a right inverse: `toMid (invData y ρ) = (y, ρ)`.
-/
import Mathlib
import Submission.Work.WilG2.Bijection

open Finset

namespace Work.WilG2.InvData

variable {m : ℕ}

/-! ### The size datum of the reconstruction is the original one -/

/-- The sizes of the reconstructed size datum are the original sizes. -/
lemma sizes_invData (y : SizeData m) (ρ : Equiv.Perm (Fin m))
    (i : Fin (SizeData.len (invData y ρ).sizeData)) :
    (invData y ρ).sizeData.sizes i = SizeData.sizes y i := by
  show (ofp y ρ).partSize (sigma y ρ i) = SizeData.sizes y i
  rw [partSize_ofp, Equiv.symm_apply_apply, chunk_card]

/-- The reconstructed size datum is the original one. -/
lemma sizeData_invData (y : SizeData m) (ρ : Equiv.Perm (Fin m)) :
    (invData y ρ).sizeData = y := by
  refine SizeData.eq_of_len_eq_of_sizes_eq' rfl ?_
  intro i
  rw [sizes_invData]
  exact (congrArg y.sizes (Fin.ext (Fin.val_cast _ i))).symm

/-! ### The unflattening of the reconstruction is compatible with the original one -/

/-- The unflattening of the reconstructed size datum agrees with the unflattening of the original
one: the points of the `j`-th chunk occupy, in the reconstruction, exactly the positions that
`(unflat y)` assigns to the `j`-th part. -/
lemma unflat_symm_invData (y : SizeData m) (ρ : Equiv.Perm (Fin m))
    (j : Fin (SizeData.len y)) (r : Fin (SizeData.sizes y j)) :
    (SizeData.unflat ((invData y ρ).sizeData)).symm
        ⟨j, Fin.cast (sizes_invData y ρ j).symm r⟩ =
      (SizeData.unflat y).symm ⟨j, r⟩ := by
  apply Fin.ext
  rw [SizeData.unflat_symm_apply, SizeData.unflat_symm_apply]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  exact sizes_invData y ρ (Fin.castLE j.isLt.le i)

/-! ### The permutation of the reconstruction is the original one -/

/-- A pointwise form of `perm_invData`: reading the reconstruction at `a` gives `ρ a`. -/
lemma perm_invData_apply (y : SizeData m) (ρ : Equiv.Perm (Fin m)) (a : Fin m) :
    (invData y ρ).perm a = ρ a := by
  generalize hU : (SizeData.unflat y) a = U
  obtain ⟨j, r⟩ := U
  have ha : (SizeData.unflat y).symm ⟨j, r⟩ = a := by
    rw [← hU]
    exact (SizeData.unflat y).symm_apply_apply a
  have ha' : a = (SizeData.unflat ((invData y ρ).sizeData)).symm
      ⟨j, Fin.cast (sizes_invData y ρ j).symm r⟩ :=
    (unflat_symm_invData y ρ j r).trans ha |>.symm
  conv_lhs => rw [ha']
  rw [OFPData.perm_unflat_symm, emb_pi]
  show ρ ((SizeData.unflat y).symm ⟨(sigma y ρ).symm (sigma y ρ j),
      Fin.cast (chunk_card y ρ ((sigma y ρ).symm (sigma y ρ j)))
        (Fin.cast (sizes_invData y ρ j).symm r)⟩) = ρ a
  have hk : (sigma y ρ).symm (sigma y ρ j) = j := Equiv.symm_apply_apply (sigma y ρ) j
  have hX : (Fin.cast (chunk_card y ρ ((sigma y ρ).symm (sigma y ρ j)))
      (Fin.cast (sizes_invData y ρ j).symm r)).val = r.val := by simp [Fin.val_cast]
  have hsig : (⟨(sigma y ρ).symm (sigma y ρ j),
      Fin.cast (chunk_card y ρ ((sigma y ρ).symm (sigma y ρ j)))
        (Fin.cast (sizes_invData y ρ j).symm r)⟩ :
      (i : Fin (SizeData.len y)) × Fin (SizeData.sizes y i)) = ⟨j, r⟩ :=
    Sigma.ext hk ((Fin.heq_ext_iff (congrArg (SizeData.sizes y) hk)).mpr hX)
  exact congrArg ρ ((congrArg (SizeData.unflat y).symm hsig).trans ha)

/-- The reconstructed permutation is the original one. -/
lemma perm_invData (y : SizeData m) (ρ : Equiv.Perm (Fin m)) :
    (invData y ρ).perm = ρ :=
  Equiv.ext fun a => perm_invData_apply y ρ a

/-! ### The right inverse law -/

theorem right_inv (m : ℕ) (p : SizeData m × Equiv.Perm (Fin m)) :
    toMid (invData p.1 p.2) = p := by
  obtain ⟨y, ρ⟩ := p
  simp only [toMid, Prod.mk.injEq]
  exact ⟨sizeData_invData y ρ, perm_invData y ρ⟩

end Work.WilG2.InvData
