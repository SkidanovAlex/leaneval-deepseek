import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- For a finite set `S` of pairs of pairs lying in `F` componentwise, the fibre over a
fixed pair of first coordinates `(i, i')` has at most `(F i).card * (F i').card` elements:
the map `p ↦ (p.1.2, p.2.2)` is injective on the fibre and takes values in `F i ×ˢ F i'`. -/
theorem pair_fiber_card {ι Z : Type} [DecidableEq ι] [DecidableEq Z]
    (F : ι → Finset Z) (S : Finset ((ι × Z) × (ι × Z)))
    (hS : ∀ p ∈ S, p.1.2 ∈ F p.1.1 ∧ p.2.2 ∈ F p.2.1) (i i' : ι) :
    (S.filter (fun p => p.1.1 = i ∧ p.2.1 = i')).card ≤ (F i).card * (F i').card := by
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun p : (ι × Z) × (ι × Z) => (p.1.2, p.2.2)) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product]
    have hpS : p ∈ S := Finset.mem_of_mem_filter p hp
    have hcond : p.1.1 = i ∧ p.2.1 = i' := (Finset.mem_filter.mp hp).2
    have h := hS p hpS
    exact ⟨hcond.1 ▸ h.1, hcond.2 ▸ h.2⟩
  · intro p hp q hq heq
    have hpc : p.1.1 = i ∧ p.2.1 = i' := (Finset.mem_filter.mp hp).2
    have hqc : q.1.1 = i ∧ q.2.1 = i' := (Finset.mem_filter.mp hq).2
    have h1 : p.1.2 = q.1.2 := (Prod.ext_iff.mp heq).1
    have h2 : p.2.2 = q.2.2 := (Prod.ext_iff.mp heq).2
    have hp1 : p.1 = q.1 := Prod.ext (by rw [hpc.1, hqc.1]) h1
    have hp2 : p.2 = q.2 := Prod.ext (by rw [hpc.2, hqc.2]) h2
    exact Prod.ext hp1 hp2

end Work.N8
