import Mathlib.Data.Fintype.BigOperators

namespace Commons.Data.Fintype

theorem card_pt_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (V : ι → Type*) [∀ i, Fintype (V i)]
    (e : Finset ι) :
    Fintype.card ((i : ι) → V i)
      = Fintype.card ((i : {i // i ∈ e}) → V i.val)
        * Fintype.card ((i : {i // i ∉ e}) → V i.val) := by
  rw [Fintype.card_congr (Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ e) V), Fintype.card_prod]

end Commons.Data.Fintype