import Mathlib.Data.Finset.Prod

namespace Commons.Data.Finset

theorem product_filter_fst_card {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) [DecidablePred P] :
    (((s.product t).filter (fun p : α × β => P p.1)).card) =
      ((s.filter P).card) * (t.card) := by
  have hset : (s.product t).filter (fun p : α × β => P p.1) = (s.filter P).product t := by
    ext x
    simp [Finset.mem_product, Finset.mem_filter, and_assoc, and_comm]
  calc
    ((s.product t).filter (fun p : α × β => P p.1)).card = ((s.filter P).product t).card := by
      rw [hset]
    _ = (s.filter P).card * t.card := Finset.card_product _ _

end Commons.Data.Finset