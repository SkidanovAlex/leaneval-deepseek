import Mathlib
import Submission.Work.LinnikBurgess.singleton_defs

namespace Work.LinnikBurgess

open scoped BigOperators

/-- The canonical reduction `ZMod (p^e) → ZMod p` commutes with inversion at every element whose
reduction modulo `p` is nonzero (i.e. which is a `p`-adic unit).  This is the only place where the
junk behaviour of the `ZMod` inverse on non-units could bite, and the hypothesis `hz` rules it out:
the `ZMod` inverse satisfies `z * z⁻¹ = gcd z.val (p^e)`, which is `1` as soon as `p ∤ z.val`, and
`φ z ≠ 0` is exactly `p ∤ z.val`. -/
lemma castHom_inv_eq {p e : ℕ} [Fact p.Prime] (hm : p ∣ p ^ e) (z : ZMod (p ^ e))
    (hz : ZMod.castHom hm (ZMod p) z ≠ 0) :
    ZMod.castHom hm (ZMod p) (z⁻¹) = (ZMod.castHom hm (ZMod p) z)⁻¹ := by
  have hNe : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hcast : ((z.val : ℕ) : ZMod p) = ZMod.castHom hm (ZMod p) z := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  have hndvd : ¬ (p ∣ z.val) := by
    intro h
    have h0 : ((z.val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff z.val p).mpr h
    exact hz (by rw [← hcast]; exact h0)
  have hcop_p : p.Coprime z.val := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hndvd
  have hcop : z.val.Coprime (p ^ e) := hcop_p.symm.pow_right e
  have hz1 : z * z⁻¹ = 1 := by
    rw [ZMod.mul_inv_eq_gcd, Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.cast_one]
  have h2 : ZMod.castHom hm (ZMod p) z * ZMod.castHom hm (ZMod p) (z⁻¹) = 1 := by
    rw [← map_mul, hz1, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm

theorem castHom_ddDefectK_three {p e : ℕ} [Fact p.Prime] (hm : p ∣ p ^ e)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hunit : ∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0) :
    ZMod.castHom hm (ZMod p) (Work.LinnikBurgess.ddDefectK p e a b r 3)
      = (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹ ^ 3)
        - (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹ ^ 3) := by
  have hNe : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  -- The reduction of the lifted shift `((r.val : ZMod (p^e)) + c)` is `r + c`.
  have hshift : ∀ (c : ℕ),
      ZMod.castHom hm (ZMod p) (((r.val : ℕ) : ZMod (p ^ e)) + (c : ℕ))
        = r + (c : ZMod p) := by
    intro c
    rw [map_add, map_natCast, map_natCast, ZMod.natCast_zmod_val]
  unfold Work.LinnikBurgess.ddDefectK
  rw [map_sub, map_sum, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [map_pow, castHom_inv_eq hm _ (by rw [hshift]; exact (hunit l).1), hshift]
  · apply Finset.sum_congr rfl
    intro l _
    rw [map_pow, castHom_inv_eq hm _ (by rw [hshift]; exact (hunit l).2), hshift]

end Work.LinnikBurgess
