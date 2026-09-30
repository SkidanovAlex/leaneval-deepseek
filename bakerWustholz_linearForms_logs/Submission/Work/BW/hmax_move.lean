import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Moving the weight across the maximising inequality: if `J` maximises `|Δ_{J'}| ∏_{J'} a` over
all `ρ`-element `J'`, and `i ∉ J`, `c ∈ J`, then `a i · |Δ_{(J\{c})∪{i}}| ≤ a c · |Δ_J|`. -/
theorem hmax_move {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i)
    (J : Finset (Fin r)) (hJ : J.card = ρ)
    (hmax : ∀ (J' : Finset (Fin r)) (hJ' : J'.card = ρ),
      |(minorJ M J' hJ' : ℝ)| * ∏ i ∈ J', a i ≤ |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i)
    {i : Fin r} (hi : i ∉ J) {c : Fin r} (hc : c ∈ J)
    (hcard : (insert i (J.erase c)).card = ρ) :
    a i * |(minorJ M (insert i (J.erase c)) hcard : ℝ)| ≤ a c * |(minorJ M J hJ : ℝ)| := by
  have hi' : i ∉ J.erase c := by simp [Finset.mem_erase, hi]
  have hc' : c ∉ J.erase c := by simp
  -- Split off the moved index and the replaced index from the two products.
  have h1 : ∏ x ∈ insert i (J.erase c), a x = a i * ∏ x ∈ J.erase c, a x :=
    Finset.prod_insert hi'
  have h2 : ∏ x ∈ J, a x = a c * ∏ x ∈ J.erase c, a x := by
    conv_lhs => rw [← Finset.insert_erase hc]
    rw [Finset.prod_insert hc']
  -- Apply maximality to the competitor `(J \ {c}) ∪ {i}`.
  have key := hmax (insert i (J.erase c)) hcard
  rw [h1, h2] at key
  have hp_pos : 0 < ∏ x ∈ J.erase c, a x := Finset.prod_pos (fun x _ => ha x)
  rw [← mul_assoc, ← mul_assoc] at key
  have key2 := (mul_le_mul_iff_of_pos_right hp_pos).mp key
  calc a i * |(minorJ M (insert i (J.erase c)) hcard : ℝ)|
      = |(minorJ M (insert i (J.erase c)) hcard : ℝ)| * a i := by ring
    _ ≤ |(minorJ M J hJ : ℝ)| * a c := key2
    _ = a c * |(minorJ M J hJ : ℝ)| := by ring

end Work.BW
