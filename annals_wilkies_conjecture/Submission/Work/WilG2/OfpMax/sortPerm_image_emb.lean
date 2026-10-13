import Mathlib
import Submission.Work.WilG2.Sorting
import Submission.Work.WilG2.OfpMax.rankF_emb_last

namespace Work.WilG2.OfpMax

/-- The maximum of the image of `Finset.univ : Finset (Fin n)` under an increasing map is the
image of the greatest element of `Fin n`. -/
lemma max'_image_univ_fin {m n : ℕ} (f : Fin n → Fin m) (hf : Monotone f) (hn : 0 < n)
    (h : (Finset.image f Finset.univ).Nonempty) :
    (Finset.image f Finset.univ).max' h = f ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩ := by
  rw [Finset.max'_eq_iff]
  refine ⟨Finset.mem_image.mpr
    ⟨⟨n - 1, Nat.sub_one_lt_of_lt hn⟩, Finset.mem_univ _, rfl⟩, ?_⟩
  rintro b hb
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hb
  refine hf ?_
  rw [Fin.le_iff_val_le_val]
  show (a : ℕ) ≤ n - 1
  have h := a.isLt
  omega

theorem sortPerm_image_emb {m : ℕ} (d : OrderedFinpartition m) (τ : Equiv.Perm (Fin d.length))
    (hne : ∀ i, (Finset.image (d.emb (τ i)) Finset.univ).Nonempty)
    (hdisj : ∀ i i', i ≠ i' →
      Disjoint (Finset.image (d.emb (τ i)) Finset.univ) (Finset.image (d.emb (τ i')) Finset.univ)) :
    sortPerm (fun i => Finset.image (d.emb (τ i)) Finset.univ) hne hdisj = τ := by
  refine Equiv.ext (fun i => ?_)
  apply Fin.ext
  rw [sortPerm_apply]
  have hfuneq : (fun l => (Finset.image (d.emb (τ l)) Finset.univ).max' (hne l))
      = (fun l => d.emb (τ l) ⟨d.partSize (τ l) - 1,
          Nat.sub_one_lt_of_lt (d.partSize_pos (τ l))⟩) := by
    funext l
    exact max'_image_univ_fin (d.emb (τ l)) (d.emb_strictMono (τ l)).monotone
      (d.partSize_pos (τ l)) (hne l)
  rw [hfuneq]
  exact rankF_emb_last d τ i

end Work.WilG2.OfpMax
