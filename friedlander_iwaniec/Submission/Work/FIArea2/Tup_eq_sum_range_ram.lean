import Mathlib
import Submission.Work.FIArea2.TsumDefs2
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.ramanujan_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

attribute [local instance] Classical.propDecidable

/-! ## The unit part of the local sum, reindexed by canonical representatives

`Tup p ν a h₁ h₂` is the sum of `ram (p^ν) (h₁ + ρ.val h₂)` over the square roots `ρ` of `a` in
`ZMod (p^ν)`.  The classical representatives `ρ.val ∈ [0, p^ν)` of those roots are exactly the
integers `r` with `p^ν ∣ r² - a`, and this file records that reindexing (`Finset.sum_bij'` along
`ρ ↦ ρ.val`), which is used whenever the unit part is treated as a sum over residues modulo `p^ν`.
-/

/-- **The congruence `ρ² = a` in `ZMod n`, in terms of the canonical representative.**  For
`a : ℤ` and `ρ : ZMod n`, the congruence `ρ² = a` holds exactly when `n ∣ ρ.val² - a`. -/
lemma dvd_val_sq_sub_iff_ram (n : ℕ) [NeZero n] (a : ℤ) (x : ZMod n) :
    ((n : ℤ) ∣ (x.val : ℤ) ^ 2 - a) ↔ x ^ 2 = (a : ZMod n) := by
  have h1 : (((x.val : ℤ) ^ 2 - a : ℤ) : ZMod n) = x ^ 2 - (a : ZMod n) := by
    push_cast
    rw [ZMod.natCast_zmod_val x]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, h1, sub_eq_zero]

/-- The same criterion, phrased for the representatives `r < n` themselves: `n ∣ r² - a` holds
exactly when the image of `r` in `ZMod n` is a square root of `a`. -/
lemma dvd_cast_sq_sub_iff_ram (n : ℕ) [NeZero n] (a : ℤ) {r : ℕ} (hr : r < n) :
    ((n : ℤ) ∣ (r : ℤ) ^ 2 - a) ↔ (r : ZMod n) ^ 2 = (a : ZMod n) := by
  have hv : (((r : ZMod n).val : ℤ)) = (r : ℤ) := by
    rw [ZMod.val_cast_of_lt hr]
  rw [← hv, dvd_val_sq_sub_iff_ram]

/-- **Reindexing the unit part by representatives modulo `p^ν`.**  The square roots `ρ` of `a` in
`ZMod (p^ν)` correspond bijectively, through `ρ ↦ ρ.val`, to the integers `r ∈ [0, p^ν)` with
`p^ν ∣ r² - a`, so `Tup p ν a h₁ h₂` is the sum of `ram (p^ν) (h₁ + r h₂)` over those `r`. -/
theorem Tup_eq_sum_range_ram (p ν : ℕ) (hp : p.Prime) [NeZero (p ^ ν)] (a h1 h2 : ℤ) :
    Tup p ν a h1 h2
      = ∑ r ∈ (Finset.range (p ^ ν)).filter
            (fun r : ℕ => ((p ^ ν : ℕ) : ℤ) ∣ (r : ℤ) ^ 2 - a),
          ram (p ^ ν) (h1 + (r : ℤ) * h2) := by
  unfold Tup
  refine Finset.sum_bij' (fun (ρ : ZMod (p ^ ν)) _ => ρ.val)
    (fun (r : ℕ) _ => (r : ZMod (p ^ ν))) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hρ ⊢
    exact ⟨ZMod.val_lt ρ, (dvd_val_sq_sub_iff_ram (p ^ ν) a ρ).mpr hρ⟩
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hr ⊢
    exact (dvd_cast_sq_sub_iff_ram (p ^ ν) a hr.1).mp hr.2
  · intro ρ _
    exact ZMod.natCast_zmod_val ρ
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    exact ZMod.val_cast_of_lt hr.1
  · intro ρ _
    rfl

end Work.FIArea2
