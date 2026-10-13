import Mathlib
import Submission.Work.DSCOH.Norm.Defs
import Submission.Work.DSCOH.Norm.exists_adjacent_repeat
import Submission.Work.DSCOH.Norm.strictMono_del_apply_eq
import Submission.Work.DSCOH.Norm.strictMono_del_congr

universe w

namespace Work.DSCOH.Norm

theorem sum_dite_vanish {ι : Type w} [LinearOrder ι] {M : Type*} [AddCommGroup M] {n : ℕ}
    (x : Fin (n + 2) → ι) (hmono : Monotone x) (hns : ¬ StrictMono x)
    (G : (b : Fin (n + 2)) → StrictMono (Work.DSCOH.Norm.del x b) → M)
    (hG : ∀ (b b' : Fin (n + 2)) (hb : StrictMono (Work.DSCOH.Norm.del x b))
      (hb' : StrictMono (Work.DSCOH.Norm.del x b')), x b = x b' → G b hb = G b' hb') :
    Finset.univ.sum (fun b : Fin (n + 2) => (-1 : ℤ) ^ (b : ℕ) •
        (dite (StrictMono (Work.DSCOH.Norm.del x b)) (G b) (fun _ => 0))) = 0 := by
  classical
  -- A nondecreasing but non-strict tuple has two adjacent equal entries.
  obtain ⟨p, hp⟩ := exists_adjacent_repeat hmono hns
  set a : Fin (n + 2) := p.castSucc with ha
  set b : Fin (n + 2) := p.succ with hb
  have hab_ne : a ≠ b := by rw [ha, hb]; exact (Fin.castSucc_lt_succ (i := p)).ne
  have hxa : x a = x b := by rw [ha, hb]; exact hp
  have hbval : (b : ℕ) = (a : ℕ) + 1 := by
    rw [ha, hb]; simp [Fin.val_succ, Fin.val_castSucc]
  -- Only the two positions `a`, `b` can even have a strictly increasing deletion:
  -- deleting any other position leaves the repetition `x a = x b` intact.
  have hzero : ∀ c ∈ (Finset.univ : Finset (Fin (n + 2))),
      c ∉ ({a, b} : Finset (Fin (n + 2))) →
      (-1 : ℤ) ^ (c : ℕ) •
        (dite (StrictMono (Work.DSCOH.Norm.del x c)) (G c) (fun _ => 0)) = 0 := by
    intro c _ hc
    have hca : c ≠ a := fun h => hc (by simp [h])
    have hcb : c ≠ b := fun h => hc (by simp [h])
    have hnc : ¬ StrictMono (Work.DSCOH.Norm.del x c) := by
      intro hsc
      rcases strictMono_del_apply_eq (b := c) hsc hab_ne hxa with h | h
      · exact hca h
      · exact hcb h
    simp only [dif_neg hnc, smul_zero]
  have key : (Finset.univ : Finset (Fin (n + 2))).sum
      (fun c => (-1 : ℤ) ^ (c : ℕ) •
        (dite (StrictMono (Work.DSCOH.Norm.del x c)) (G c) (fun _ => 0)))
      = ({a, b} : Finset (Fin (n + 2))).sum
        (fun c => (-1 : ℤ) ^ (c : ℕ) •
          (dite (StrictMono (Work.DSCOH.Norm.del x c)) (G c) (fun _ => 0))) :=
    (Finset.sum_subset (Finset.subset_univ _) hzero).symm
  rw [key, Finset.sum_pair hab_ne]
  show (-1 : ℤ) ^ (a : ℕ) • (dite (StrictMono (Work.DSCOH.Norm.del x a)) (G a) (fun _ => 0))
      + (-1 : ℤ) ^ (b : ℕ) • (dite (StrictMono (Work.DSCOH.Norm.del x b)) (G b) (fun _ => 0)) = 0
  by_cases hsa : StrictMono (Work.DSCOH.Norm.del x a)
  · -- Both remaining deletions are strictly increasing; they are equal, as are their `G`-values,
    -- and the signs are opposite.
    have hsb : StrictMono (Work.DSCOH.Norm.del x b) :=
      (strictMono_del_congr hmono hab_ne hxa).mp hsa
    rw [dif_pos hsa, dif_pos hsb, hG a b hsa hsb hxa]
    have hsign : (-1 : ℤ) ^ (b : ℕ) = -(-1 : ℤ) ^ (a : ℕ) := by
      rw [hbval, pow_succ]; ring
    rw [hsign, neg_smul, add_neg_cancel]
  · -- Neither deletion is strictly increasing; both terms vanish.
    have hsb : ¬ StrictMono (Work.DSCOH.Norm.del x b) :=
      fun h => hsa ((strictMono_del_congr hmono hab_ne hxa).mpr h)
    rw [dif_neg hsa, dif_neg hsb, smul_zero, smul_zero, add_zero]

end Work.DSCOH.Norm
