import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.succ_le_NN

namespace Work.HP.NA

noncomputable section
open Finset
set_option autoImplicit false
set_option linter.unusedVariables false

/-- Pointwise expansion of `(f a - 1)^2`, summed over a finset. -/
private lemma sum_sub_one_sq {ι : Type*} (f : ι → ℝ) (s : Finset ι) :
    ∑ a ∈ s, (f a - 1) ^ 2 = (∑ a ∈ s, (f a) ^ 2) - 2 * (∑ a ∈ s, f a) + s.card := by
  rw [Finset.sum_congr rfl (fun a _ => by ring : ∀ a ∈ s, (f a - 1) ^ 2 = (f a) ^ 2 - 2 * f a + 1)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp

/-- Real-arithmetic core: from an upper bound on `s2`, the exact value of `s1` and a bound on
`card`, conclude the bound on the variance-like quantity `s2 - 2 s1 + card`.

The two small quantities `x ≤ 1/pn` and `y ≤ 1/pn` control the correction terms coming from the
two Euler factors of `s1`. -/
private lemma arith_key (T C x y pn : ℝ) (hT : 0 ≤ T)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxz : x ≤ 1 / pn) (hyz : y ≤ 1 / pn)
    (s1 s2 card : ℝ) (h2 : s2 ≤ T * (1 + C / pn)) (h1 : s1 = T * (1 - x) * (1 - y))
    (hc : card ≤ T) :
    s2 - 2 * s1 + card ≤ (C + 4) * T / pn := by
  have h1' : T * (1 - x - y) ≤ s1 := by
    rw [h1]
    have hle : (1 - x - y) ≤ (1 - x) * (1 - y) := by nlinarith [mul_nonneg hx hy]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hle hT
  have hstep : s2 - 2 * s1 + card ≤ T * (1 + C / pn) - 2 * (T * (1 - x - y)) + T := by
    linarith
  have hkey : T * (1 + C / pn) - 2 * (T * (1 - x - y)) + T ≤ (C + 4) * T / pn := by
    have hxy : x + y ≤ 2 * (1 / pn) := by linarith
    have hrw : T * (1 + C / pn) - 2 * (T * (1 - x - y)) + T
        = T * (C / pn + 2 * x + 2 * y) := by ring
    rw [hrw]
    calc T * (C / pn + 2 * x + 2 * y) ≤ T * (C / pn + 4 * (1 / pn)) :=
          mul_le_mul_of_nonneg_left (by linarith) hT
      _ = (C + 4) * T / pn := by ring
  linarith

theorem sum_sigQ_sub_one_sq_le (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (Csq : ℝ) (hCsq : 0 < Csq)
    (hmom1 : ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), Work.HP.NA.sigQ d n (p ^ r) a)
        = (p : ℝ) ^ (r * Work.HP.NN d n) * (1 - 1 / (p : ℝ) ^ (n + 1))
            * (1 - 1 / (p : ℝ) ^ (Work.HP.NN d n - 1)))
    (hmom2 : ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), (Work.HP.NA.sigQ d n (p ^ r) a) ^ 2)
        ≤ (p : ℝ) ^ (r * Work.HP.NN d n) * (1 + Csq / (p : ℝ) ^ (n - 1))) :
    ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), (Work.HP.NA.sigQ d n (p ^ r) a - 1) ^ 2)
        ≤ (Csq + 4) * (p : ℝ) ^ (r * Work.HP.NN d n) / (p : ℝ) ^ (n - 1) := by
  intro p r hNe hp hr
  have hA1 := hmom1 p r hp hr
  have hA2 := hmom2 p r hp hr
  rw [sum_sub_one_sq (fun a => Work.HP.NA.sigQ d n (p ^ r) a)
    (Work.HP.NA.primFinset d n (p ^ r))]
  refine arith_key ((p : ℝ) ^ (r * Work.HP.NN d n)) Csq (1 / (p : ℝ) ^ (n + 1))
    (1 / (p : ℝ) ^ (Work.HP.NN d n - 1)) ((p : ℝ) ^ (n - 1)) ?_ ?_ ?_ ?_ ?_ _ _ _ hA2 hA1 ?_
  · positivity
  · positivity
  · positivity
  · have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hpos : (0 : ℝ) < (p : ℝ) ^ (n - 1) := pow_pos (by linarith) _
    exact one_div_le_one_div_of_le hpos (pow_le_pow_right₀ hp1 (by omega))
  · have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hpos : (0 : ℝ) < (p : ℝ) ^ (n - 1) := pow_pos (by linarith) _
    have hN : n - 1 ≤ Work.HP.NN d n - 1 := by
      have := Work.HP.NA.succ_le_NN d n (by omega : 1 ≤ d); omega
    exact one_div_le_one_div_of_le hpos (pow_le_pow_right₀ hp1 hN)
  · have h1 : (Work.HP.NA.primFinset d n (p ^ r)).card ≤ (p ^ r) ^ (Work.HP.NN d n) := by
      have hcard := Finset.card_le_card (Finset.subset_univ (Work.HP.NA.primFinset d n (p ^ r)))
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card] at hcard
      simpa [Work.HP.NN] using hcard
    calc ((Work.HP.NA.primFinset d n (p ^ r)).card : ℝ)
          ≤ ((p ^ r) ^ (Work.HP.NN d n) : ℝ) := by exact_mod_cast h1
      _ = (p : ℝ) ^ (r * Work.HP.NN d n) := by rw [← pow_mul]

end

end Work.HP.NA
