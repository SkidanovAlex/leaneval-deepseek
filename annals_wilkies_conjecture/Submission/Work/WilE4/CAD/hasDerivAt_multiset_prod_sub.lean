import Mathlib

namespace Work.WilE4.CAD

theorem hasDerivAt_multiset_prod_sub (m : Multiset ℂ) (z : ℂ) (hz : ∀ a ∈ m, z ≠ a) :
    HasDerivAt (fun w : ℂ => (m.map (fun a => w - a)).prod)
      ((m.map (fun a => z - a)).prod * (m.map (fun a => (z - a)⁻¹)).sum) z := by
  induction m using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | cons a s ih =>
    have hza : z ≠ a := hz a (Multiset.mem_cons_self a s)
    have hzs : ∀ b ∈ s, z ≠ b := fun b hb => hz b (Multiset.mem_cons_of_mem hb)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
    have hmul := h1.mul (ih hzs)
    convert hmul using 1
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    field_simp

end Work.WilE4.CAD
