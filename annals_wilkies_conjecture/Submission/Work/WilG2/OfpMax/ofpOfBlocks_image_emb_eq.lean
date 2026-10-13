import Mathlib
import Submission.Work.WilG2.Sorting
import Submission.Work.WilG2.OfpMax.rankF_emb_last

open Finset

namespace Work.WilG2.OfpMax

/-- The maximum of the image of `univ` under a strictly monotone map is the value at the last
index. -/
lemma image_univ_max'_eq {α : Type*} [DecidableEq α] [LinearOrder α] {n : ℕ} (hn : 0 < n)
    (f : Fin n → α) (hf : StrictMono f) (h : (Finset.image f Finset.univ).Nonempty) :
    (Finset.image f Finset.univ).max' h = f ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩ := by
  rw [Finset.max'_eq_iff]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨⟨n - 1, Nat.sub_one_lt_of_lt hn⟩, Finset.mem_univ _, rfl⟩
  · intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, -, rfl⟩ := hb
    refine hf.monotone ?_
    rw [Fin.le_iff_val_le_val]
    show (a : ℕ) ≤ n - 1
    have := a.isLt
    omega

/-- Heterogeneous equality of the coerced enumerations of a finset with respect to two proofs of
the same cardinality statement. -/
lemma heq_coe_orderEmbOfFin {α : Type*} [LinearOrder α] {s : Finset α} {k : ℕ}
    (h : s.card = k) :
    HEq (⇑(s.orderEmbOfFin (rfl : s.card = s.card))) (⇑(s.orderEmbOfFin h)) := by
  cases h
  exact HEq.rfl

/-- Heterogeneous equality of the coerced enumerations of two equal finsets. -/
lemma heq_coe_orderEmbOfFin_congr {α : Type*} [LinearOrder α] {s t : Finset α} (h : s = t) :
    HEq (⇑(s.orderEmbOfFin (rfl : s.card = s.card)))
      (⇑(t.orderEmbOfFin (rfl : t.card = t.card))) := by
  cases h
  exact HEq.rfl

/-- The enumeration of the image of `univ` under a strictly monotone map is the map itself
(heterogeneous because the cardinality of the image is only propositionally the domain size). -/
lemma heq_coe_orderEmbOfFin_image_univ {α : Type*} [DecidableEq α] [LinearOrder α] {n : ℕ}
    (f : Fin n → α) (hf : StrictMono f) :
    HEq (⇑((Finset.image f Finset.univ).orderEmbOfFin rfl)) f := by
  set s := Finset.image f Finset.univ with hs
  have hcard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  have hf' : f = ⇑(s.orderEmbOfFin hcard) :=
    Finset.orderEmbOfFin_unique hcard
      (fun x => by rw [hs]; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) hf
  exact HEq.trans (heq_coe_orderEmbOfFin hcard) (heq_of_eq hf'.symm)

/-- Sorting a family of blocks of the form `image (d.emb (τ i)) univ` recovers `τ`. -/
lemma sortPerm_image_emb_blocks {m : ℕ} (d : OrderedFinpartition m)
    (τ : Equiv.Perm (Fin d.length))
    (hne : ∀ i, (Finset.image (d.emb (τ i)) Finset.univ).Nonempty)
    (hdisj : ∀ i i', i ≠ i' →
      Disjoint (Finset.image (d.emb (τ i)) Finset.univ) (Finset.image (d.emb (τ i')) Finset.univ)) :
    sortPerm (fun i => Finset.image (d.emb (τ i)) Finset.univ) hne hdisj = τ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [sortPerm_apply]
  have hmx : (fun l => (Finset.image (d.emb (τ l)) Finset.univ).max' (hne l))
      = fun l => d.emb (τ l)
          ⟨d.partSize (τ l) - 1, Nat.sub_one_lt_of_lt (d.partSize_pos (τ l))⟩ := by
    funext l
    exact image_univ_max'_eq (d.partSize_pos (τ l)) (d.emb (τ l)) (d.emb_strictMono (τ l)) (hne l)
  rw [hmx]
  exact rankF_emb_last d τ i

theorem ofpOfBlocks_image_emb_eq {m : ℕ} (d : OrderedFinpartition m) (τ : Equiv.Perm (Fin d.length))
    (hne : ∀ i, (Finset.image (d.emb (τ i)) Finset.univ).Nonempty)
    (hdisj : ∀ i i', i ≠ i' →
      Disjoint (Finset.image (d.emb (τ i)) Finset.univ) (Finset.image (d.emb (τ i')) Finset.univ))
    (hcover : ∀ x : Fin m, ∃ i, x ∈ Finset.image (d.emb (τ i)) Finset.univ) :
    ofpOfBlocks (fun i => Finset.image (d.emb (τ i)) Finset.univ) hne hdisj hcover = d := by
  let B : Fin d.length → Finset (Fin m) := fun i => Finset.image (d.emb (τ i)) Finset.univ
  change ofpOfBlocks B hne hdisj hcover = d
  have hsort : sortPerm B hne hdisj = τ := sortPerm_image_emb_blocks d τ hne hdisj
  have hBp : ∀ p : Fin d.length,
      B ((sortPerm B hne hdisj).symm p) = Finset.image (d.emb p) Finset.univ := by
    intro p
    have h1 : (sortPerm B hne hdisj).symm p = τ.symm p := by rw [hsort]
    rw [h1]
    show Finset.image (d.emb (τ (τ.symm p))) Finset.univ = Finset.image (d.emb p) Finset.univ
    rw [Equiv.apply_symm_apply]
  have hpart : ∀ p : Fin d.length,
      (ofpOfBlocks B hne hdisj hcover).partSize p = d.partSize p := by
    intro p
    change (B ((sortPerm B hne hdisj).symm p)).card = d.partSize p
    rw [hBp p, Finset.card_image_of_injective _ (d.emb_strictMono p).injective, Finset.card_univ,
      Fintype.card_fin]
  have hpart_heq : HEq (ofpOfBlocks B hne hdisj hcover).partSize d.partSize := by
    refine Function.hfunext rfl ?_
    intro p p' hpp
    have hp : p = p' := eq_of_heq hpp
    rw [← hp]
    exact heq_of_eq (hpart p)
  have hemb_heq : HEq (ofpOfBlocks B hne hdisj hcover).emb d.emb := by
    refine Function.hfunext rfl ?_
    intro p p' hpp
    have hp : p = p' := eq_of_heq hpp
    rw [← hp]
    refine HEq.trans ?_ (heq_coe_orderEmbOfFin_image_univ (d.emb p) (d.emb_strictMono p))
    show HEq (⇑((B ((sortPerm B hne hdisj).symm p)).orderEmbOfFin rfl))
      (⇑((Finset.image (d.emb p) Finset.univ).orderEmbOfFin rfl))
    exact heq_coe_orderEmbOfFin_congr (hBp p)
  exact OrderedFinpartition.ext rfl hpart_heq hemb_heq

end Work.WilG2.OfpMax
