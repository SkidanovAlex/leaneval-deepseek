/-
  WilG2 : basic facts about ordered finpartitions in terms of their parts.

  The parts of an `OrderedFinpartition d` of `Fin m` are the images of `d.emb i`, which are
  increasing enumerations of the parts; the parts are ordered by increasing maximal element.
  We also re-export (by importing) the two "sorting" facts proved separately:
  `Work.WilG2.OfpMax.ofpOfBlocks_image_emb_eq` and `Work.WilG2.OfpMax.sortPerm_image_emb`.
-/
import Submission.Work.WilG2.Sorting
import Submission.Work.WilG2.OfpMax.ofpOfBlocks_image_emb_eq
import Submission.Work.WilG2.OfpMax.sortPerm_image_emb
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.WilG2

variable {m : ℕ}

lemma sum_partSize (d : OrderedFinpartition m) : ∑ i, d.partSize i = m := by
  have h := Fintype.card_congr d.equivSigma
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  simpa only [Fintype.card_fin] using h

lemma image_emb_card (d : OrderedFinpartition m) (i : Fin d.length) :
    (Finset.image (d.emb i) Finset.univ).card = d.partSize i := by
  rw [Finset.card_image_of_injective _ (d.emb_strictMono i).injective, Finset.card_univ,
    Fintype.card_fin]

lemma image_emb_nonempty (d : OrderedFinpartition m) (i : Fin d.length) :
    (Finset.image (d.emb i) Finset.univ).Nonempty :=
  Finset.card_pos.mp (by rw [image_emb_card]; exact d.partSize_pos i)

lemma orderEmbOfFin_image_emb (d : OrderedFinpartition m) (i : Fin d.length) :
    d.emb i = ⇑((Finset.image (d.emb i) Finset.univ).orderEmbOfFin (image_emb_card d i)) :=
  Finset.orderEmbOfFin_unique (image_emb_card d i)
    (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) (d.emb_strictMono i)

end Work.WilG2
