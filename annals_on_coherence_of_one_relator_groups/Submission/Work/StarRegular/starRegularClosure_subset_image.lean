import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff
import Submission.Work.ORHughesFree.StarRegular.starRegularChain_mono

namespace Work.StarRegular

theorem starRegularClosure_subset_image {U : Type*} [Ring U] [StarRing U] (A : Work.ORHughesFree.StarSubring U)
    (R : Work.ORHughesFree.StarSubring U) (R' : Work.ORHughesFree.StarSubring ↥A)
    (h : ∀ n, (Work.ORHughesFree.starRegularChain R n : Set U) ⊆
      Subtype.val '' (Work.ORHughesFree.starRegularChain R' n : Set ↥A)) :
    (Work.ORHughesFree.starRegularClosure R : Set U) ⊆
      Subtype.val '' (Work.ORHughesFree.starRegularClosure R' : Set ↥A) := by
  -- The `∗`-regular closure is the union of the approximating chain, so it suffices to
  -- handle the elements of the individual stages, which the hypothesis controls.
  intro x hx
  obtain ⟨n, hn⟩ := (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R x).mp hx
  obtain ⟨y, hy, hyx⟩ := h n hn
  exact ⟨y, (Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff R' y).mpr ⟨n, hy⟩, hyx⟩

end Work.StarRegular
