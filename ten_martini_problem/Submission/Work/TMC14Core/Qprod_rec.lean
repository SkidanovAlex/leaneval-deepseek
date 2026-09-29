import Mathlib
import Submission.Work.TMC14Core.InvSumAux

/-!
# `TMC14Core.Qprod_rec`

The two-parameter recursion satisfied by `Qprod ω a b = ∏_{k=1}^{a} (1 - ω^{b+k})`.

Both auxiliary lemmas are the "split off one factor" identities:
* `Qprod_succ_top` peels the **last** factor `1 - ω^{b+(n+1)}` off the product;
* `Qprod_succ_bot` peels the **first** factor `1 - ω^{b+1}` off, after shifting the
  remaining range, giving the equivalent form `(1 - ω^{b+1}) · Qprod ω n (b+1)`.

Combining them produces the requested recursion.
-/

namespace Work.TMC14Core

open Finset

/-- **Top split.** `Qprod ω (n+1) b` is `Qprod ω n b` times the factor `1 - ω^{b+n+1}`. -/
theorem Qprod_succ_top (ω : ℂ) (n b : ℕ) :
    Qprod ω (n + 1) b = Qprod ω n b * (1 - ω ^ (b + n + 1)) := by
  have h := Finset.prod_Icc_succ_top (a := 1) (b := n)
    (f := fun k => (1 - ω ^ (b + k))) (by omega : 1 ≤ n + 1)
  simp only [Qprod] at h ⊢
  rw [h]
  congr 2

/-- **Bottom shift.** `Qprod ω (n+1) b = (1 - ω^{b+1}) · Qprod ω n (b+1)`. -/
theorem Qprod_succ_bot (ω : ℂ) (n b : ℕ) :
    Qprod ω (n + 1) b = (1 - ω ^ (b + 1)) * Qprod ω n (b + 1) := by
  have hins : Finset.Icc 1 (n + 1) = insert 1 (Finset.Icc 2 (n + 1)) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ n + 1)).symm
  have hmem : (1 : ℕ) ∉ Finset.Icc 2 (n + 1) := by simp
  have hmap : ∏ x ∈ Finset.Icc 2 (n + 1), (1 - ω ^ (b + x)) = Qprod ω n (b + 1) := by
    rw [show Finset.Icc 2 (n + 1) = (Finset.Icc 1 n).map (addRightEmbedding 1) from by
      rw [Finset.map_add_right_Icc]]
    rw [Finset.prod_map]
    simp only [Qprod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp only [addRightEmbedding_apply]
    congr 1
    congr 1
    omega
  simp only [Qprod]
  rw [hins, Finset.prod_insert hmem, hmap]
  simp only [Qprod]

/-- The recursion requested by component C14. -/
theorem Qprod_rec (ω : ℂ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Qprod ω a b = Qprod ω a (b - 1) + ω ^ b * (1 - ω ^ a) * Qprod ω (a - 1) b := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hn : (n + 1) - 1 = n := by omega
  have hb1 : b - 1 + 1 = b := by omega
  rw [hn, Qprod_succ_top ω n b, Qprod_succ_bot ω n (b - 1), hb1]
  have hpow : ω ^ (b + n + 1) = ω ^ b * ω ^ (n + 1) := by
    rw [show b + n + 1 = b + (n + 1) from by omega, pow_add]
  rw [hpow]
  ring

end Work.TMC14Core
