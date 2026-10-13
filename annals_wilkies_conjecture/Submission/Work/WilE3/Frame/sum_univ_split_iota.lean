import Mathlib
import Submission.Work.WilE3.Frame.straighteningDefs

namespace Work.WilE3.Frame

/-- `Fin k` splits as the image of `ι` together with its complement `U k ι`, so a sum over
`Fin k` decomposes into the sum over the (injective) enumeration `ι` and the sum over the
remaining coordinates. -/
lemma sum_univ_split_iota {k j : ℕ} {M : Type*} [AddCommMonoid M] (ι : Fin j → Fin k)
    (hι : Function.Injective ι) (g : Fin k → M) :
    ∑ i : Fin k, g i = (∑ b : Fin j, g (ι b)) + ∑ i : Work.WilE3.Frame.U k ι, g i.1 := by
  classical
  -- the image of `ι`, as a finset of `Fin k`
  have hrange : Finset.univ.filter (fun i : Fin k => i ∈ Set.range ι) = Finset.univ.image ι := by
    ext i
    simp [Finset.mem_image, Set.mem_range]
  -- the sum over the image of `ι` is the sum over `Fin j`
  have hfirst : Finset.sum (Finset.univ.filter (fun i : Fin k => i ∈ Set.range ι)) g
      = Finset.sum Finset.univ (fun b : Fin j => g (ι b)) := by
    rw [hrange, Finset.sum_image (fun a _ b _ h => hι h)]
  -- the sum over the complement of the image is the sum over the subtype `U k ι`
  have hsecond : Finset.sum (Finset.univ.filter (fun i : Fin k => i ∉ Set.range ι)) g
      = Finset.sum Finset.univ (fun i : Work.WilE3.Frame.U k ι => g i.1) :=
    Finset.sum_subtype _ (fun x => by simp) g
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin k => i ∈ Set.range ι) g).symm
  rw [hfirst, hsecond] at hsplit
  exact hsplit

end Work.WilE3.Frame
