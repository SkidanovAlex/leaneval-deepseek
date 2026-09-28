import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.sum_sigQ_eq
import Submission.Work.HP.NA.sum_sigQ_sq_bound
import Submission.Work.HP.NA.card_Rset_le
import Submission.Work.HP.NA.sigQ_lower_Rset
import Submission.Work.HP.NA.exists_Rset_of_FlocSet
import Submission.Work.HP.NA.rpow_neg_le_quad_small
import Submission.Work.HP.NA.sum_Icc_rpow_fourth
import Submission.Work.HP.NA.succ_le_NN
import Submission.Work.HP.NA.sum_sigQ_sub_one_sq_le
import Submission.Work.HP.NA.gt_arith
import Submission.Work.HP.NA.one_div_pow_le_one_div_rpow
import Submission.Work.HP.NA.rpow_half_div_pow_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `σ ≤ 1/2` and `σ > 1/2` parts of `F^loc(p^r)`

Writing `κ = 1/(4n)` and `σ(a) = σ(a;p^r)`, this file bounds
`∑_{a ∈ F^loc(p^r)} σ(a)^{-κ}` by `p^{rN}(1 + C p^{-5/4})`, `N = N_{d,n}`.

The sum is split according to whether `σ(a) ≤ 1/2`:

* `σ(a) > 1/2` (`sum_Floc_more_rpow_le`): the pointwise quadratic Taylor bound
  `sum_Floc_le_half_rpow_le`-companion `rpow_neg_le_quad_small` together with the first and
  second moments of `σ` (`sum_sigQ_eq`, `sum_sigQ_sq_bound`) give
  `∑_{σ>1/2} σ^{-κ} ≤ p^{rN}(1 + (C+5)p^{-5/4})`;
* `σ(a) ≤ 1/2` (`sum_Floc_le_half_rpow_le`): splitting `F^loc(p^r)` by the vanishing order
  `e` of the gradient (`exists_Rset_of_FlocSet`), the counting bound `card_Rset_le` and the
  lower bound `sigQ_lower_Rset` give `∑_{σ≤1/2} σ^{-κ} ≤ (8C+42) p^{rN-5/4}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace Work.HP.NA

instance instDecidablePredRset (d n p r e : ℕ) :
    DecidablePred (fun a : Mon d n → ZMod (p ^ r) => Rset d n p r e a) :=
  fun _ => Classical.propDecidable _

instance instDecidableRset (d n p r e : ℕ) (a : Mon d n → ZMod (p ^ r)) :
    Decidable (Rset d n p r e a) :=
  Classical.propDecidable _

theorem mem_FlocInset {d n p r : ℕ} [NeZero (p ^ r)] {a : Mon d n → ZMod (p ^ r)} :
    a ∈ FlocInset d n p r ↔ a ∈ primFinset d n (p ^ r) ∧ FlocSet d n p r a := by
  simp [FlocInset, Finset.mem_filter]

theorem mem_primFinset {d n q : ℕ} [NeZero q] {a : Mon d n → ZMod q} :
    a ∈ primFinset d n q ↔ IsPrimGen q a := by
  simp [primFinset, Finset.mem_filter]

theorem sigQ_eq_zero_of_not {d n Q : ℕ} [NeZero Q] (a : Mon d n → ZMod Q)
    (h : ¬ ∃ b : Fin (n + 1) → ZMod Q, IsPrimGen Q b ∧ fev d n a b = 0) :
    sigQ d n Q a = 0 := by
  have hempty : {b : Fin (n + 1) → ZMod Q | Ideal.span (Set.range b) = ⊤ ∧ fev d n a b = 0} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro b hb
    exact h ⟨b, hb.1, hb.2⟩
  unfold sigQ
  rw [hempty]
  simp

theorem sigQ_nonneg {d n Q : ℕ} [NeZero Q] (a : Mon d n → ZMod Q) : 0 ≤ sigQ d n Q a := by
  unfold sigQ
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem rpow_neg_le_of_lower (p : ℝ) (hp : 1 ≤ p) (m : ℕ) (y κ : ℝ) (hκ : 0 ≤ κ)
    (hy : 1 / p ^ m ≤ y) : y ^ (-κ) ≤ p ^ (κ * (m : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hpm : 0 < p ^ m := by positivity
  have hy' : 0 < y := lt_of_lt_of_le (by positivity) hy
  have h1 : y ^ (-κ) ≤ (1 / p ^ m) ^ (-κ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hy (by linarith)
  have hpm_eq : p ^ (-(m : ℝ)) = 1 / p ^ m := by
    rw [Real.rpow_neg (le_of_lt hp0)]
    simp [Real.rpow_natCast, one_div]
  have h2 : (1 / p ^ m) ^ (-κ) = p ^ (κ * (m : ℝ)) := by
    rw [← hpm_eq, ← Real.rpow_mul (le_of_lt hp0)]
    congr 1
    ring
  rwa [h2] at h1

theorem primFinset_card_le {d n Q : ℕ} [NeZero Q] :
    ((primFinset d n Q).card : ℝ) ≤ (Q : ℝ) ^ (NN d n) := by
  have h1 : (primFinset d n Q).card ≤ Q ^ (NN d n) := by
    calc (primFinset d n Q).card ≤ Fintype.card (Mon d n → ZMod Q) := Finset.card_le_univ _
      _ = Q ^ (NN d n) := by rw [Fintype.card_fun, ZMod.card]
  calc ((primFinset d n Q).card : ℝ) ≤ ((Q ^ (NN d n) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (Q : ℝ) ^ (NN d n) := by push_cast; rfl

theorem primFinset_card_le' {d n p r : ℕ} [NeZero (p ^ r)] :
    ((primFinset d n (p ^ r)).card : ℝ) ≤ (p : ℝ) ^ (r * NN d n) := by
  have h := primFinset_card_le (d := d) (n := n) (Q := p ^ r)
  have h2 : ((p ^ r : ℕ) : ℝ) = (p : ℝ) ^ r := by push_cast; ring
  rwa [h2, ← pow_mul] at h

def FlocHalf (d n p r : ℕ) [NeZero (p ^ r)] : Finset (Mon d n → ZMod (p ^ r)) :=
  (FlocInset d n p r).filter (fun a => sigQ d n (p ^ r) a ≤ 1/2)

/-- The locally soluble coefficients `a` with `1/2 < σ(a)`. -/
def FlocMore (d n p r : ℕ) [NeZero (p ^ r)] : Finset (Mon d n → ZMod (p ^ r)) :=
  (FlocInset d n p r).filter (fun a => 1/2 < sigQ d n (p ^ r) a)

/-- The locally soluble coefficients `a` with `σ(a) ≤ 1/2` and gradient vanishing order `e`. -/
def FlocHalfR (d n p r e : ℕ) [NeZero (p ^ r)] : Finset (Mon d n → ZMod (p ^ r)) :=
  (FlocInset d n p r).filter (fun a => sigQ d n (p ^ r) a ≤ 1/2 ∧ Rset d n p r e a)

theorem mem_FlocHalf {d n p r : ℕ} [NeZero (p ^ r)] {a : Mon d n → ZMod (p ^ r)} :
    a ∈ FlocHalf d n p r ↔ a ∈ FlocInset d n p r ∧ sigQ d n (p^r) a ≤ 1/2 := by
  simp [FlocHalf, Finset.mem_filter]

theorem mem_FlocMore {d n p r : ℕ} [NeZero (p ^ r)] {a : Mon d n → ZMod (p ^ r)} :
    a ∈ FlocMore d n p r ↔ a ∈ FlocInset d n p r ∧ 1/2 < sigQ d n (p^r) a := by
  simp [FlocMore, Finset.mem_filter]

theorem mem_FlocHalfR {d n p r e : ℕ} [NeZero (p ^ r)] {a : Mon d n → ZMod (p ^ r)} :
    a ∈ FlocHalfR d n p r e ↔ a ∈ FlocInset d n p r ∧ sigQ d n (p^r) a ≤ 1/2
      ∧ Rset d n p r e a := by
  simp [FlocHalfR, Finset.mem_filter]

theorem FlocHalf_filter_Rset (d n p r e : ℕ) [NeZero (p ^ r)] :
    (FlocHalf d n p r).filter (fun a => Rset d n p r e a) = FlocHalfR d n p r e := by
  ext a
  simp only [FlocHalf, FlocHalfR, Finset.mem_filter]
  tauto

theorem sum_Floc_split (d n p r : ℕ) [NeZero (p ^ r)] (g : (Mon d n → ZMod (p ^ r)) → ℝ) :
    (∑ a ∈ FlocInset d n p r, g a)
      = (∑ a ∈ FlocHalf d n p r, g a) + (∑ a ∈ FlocMore d n p r, g a) := by
  have hf : (FlocInset d n p r).filter (fun a => ¬ (sigQ d n (p^r) a ≤ 1/2)) = FlocMore d n p r := by
    rw [FlocMore]
    exact Finset.filter_congr (fun a _ => by simp only [not_le])
  rw [FlocHalf, ← hf, Finset.sum_filter_add_sum_filter_not]

theorem sum_Floc_le_half_rpow_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (Csq : ℝ) (hCsq : 0 < Csq)
    (hvar : ∀ (p r : ℕ) [NeZero (p^r)], p.Prime → 1 ≤ r →
      (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2)
        ≤ (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1)) :
    ∀ (p r : ℕ) [NeZero (p^r)], p.Prime → 1 ≤ r →
      (∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ (8*Csq+42) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by
  intro p r hNe hp hr
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hpR1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
  have hpR2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact ne_of_gt this
  have h4n0 : 4 * (n:ℝ) ≠ 0 := mul_ne_zero (by norm_num) hn0
  have hκnn : (0:ℝ) ≤ 1/(4*(n:ℝ)) := by positivity
  have hκ2n : (1/(4*(n:ℝ))) * ((2*n : ℕ) : ℝ) = 1/2 := by
    rw [one_div, inv_mul_eq_iff_eq_mul₀ h4n0, Nat.cast_mul]
    push_cast
    ring
  have hκen : ∀ e : ℕ, (1/(4*(n:ℝ))) * (((e+1)*n : ℕ) : ℝ) = ((e:ℝ)+1)/4 := by
    intro e
    rw [one_div, inv_mul_eq_iff_eq_mul₀ h4n0, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hNn : n ≤ NN d n := le_trans (Nat.le_succ n) (succ_le_NN d n (by omega))
  have hNge3 : 3 ≤ NN d n := le_trans hn hNn
  have hP54 : (0:ℝ) < (p:ℝ)^((5:ℝ)/4) := Real.rpow_pos_of_pos hpR _
  have hstep1 : (∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ ∑ e ∈ Finset.range (r+1),
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) := by
    have hint : ∀ a ∈ FlocHalf d n p r,
        (1:ℝ) ≤ ∑ e ∈ Finset.range (r+1), (if Rset d n p r e a then (1:ℝ) else 0) := by
      intro a ha
      have hfl : FlocSet d n p r a := (mem_FlocInset.mp (mem_FlocHalf.mp ha).1).2
      obtain ⟨e, her, hRe⟩ := exists_Rset_of_FlocSet d n p r a hfl
      have hmem : e ∈ Finset.range (r+1) := by
        rw [Finset.mem_range]; exact Nat.lt_succ_of_le her
      have h1 := Finset.single_le_sum
        (f := fun e => (if Rset d n p r e a then (1:ℝ) else 0))
        (fun i _ => by positivity) hmem
      simpa [hRe] using h1
    calc (∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        = ∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) * 1 := by
          simp only [mul_one]
      _ ≤ ∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))
            * (∑ e ∈ Finset.range (r+1), (if Rset d n p r e a then (1:ℝ) else 0)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hint a ha) (Real.rpow_nonneg (sigQ_nonneg a) _)
      _ = ∑ e ∈ Finset.range (r+1),
            ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro e _
          have hpt' : ∀ a : Mon d n → ZMod (p^r),
              (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) * (if Rset d n p r e a then (1:ℝ) else 0)
                = (if Rset d n p r e a then (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) else 0) := by
            intro a; by_cases h : Rset d n p r e a <;> simp [h]
          rw [Finset.sum_congr rfl (fun a _ => hpt' a), ← Finset.sum_filter,
              FlocHalf_filter_Rset]
  have hsplit2 : (∑ e ∈ Finset.range (r+1),
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      = (∑ e ∈ Finset.range 2,
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        + (∑ e ∈ Finset.Icc 2 r,
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))) := by
    have hr2 : (Finset.range (r+1)).filter (fun e => e ≤ 1) = Finset.range 2 := by
      ext e; simp only [Finset.mem_filter, Finset.mem_range]; omega
    have hrc : (Finset.range (r+1)).filter (fun e => ¬ e ≤ 1) = Finset.Icc 2 r := by
      ext e; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (r+1)) (fun e => e ≤ 1)
          (fun e => ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))), hr2, hrc]
  have hEgen : ∀ e : ℕ, e ≤ 1 →
      (∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ 4 * (Csq+4) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by
    intro e he1
    have her : e ≤ r := le_trans he1 hr
    have hpt : ∀ a ∈ FlocHalfR d n p r e,
        (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))
          ≤ (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) * (4 * (sigQ d n (p^r) a - 1)^2) := by
      intro a ha
      obtain ⟨hf, hσle, hR⟩ := mem_FlocHalfR.mp ha
      have hlow := sigQ_lower_Rset d n p r e (by omega) hp hr her a hR
      have h1 : (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))
          ≤ (p:ℝ) ^ ((1/(4*(n:ℝ))) * (((e+1)*n : ℕ):ℝ)) :=
        rpow_neg_le_of_lower (p:ℝ) hpR1 ((e+1)*n) _ _ hκnn hlow
      have h2 : (p:ℝ) ^ ((1/(4*(n:ℝ))) * (((e+1)*n : ℕ):ℝ))
          ≤ (p:ℝ) ^ ((1/(4*(n:ℝ))) * ((2*n : ℕ):ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hpR1
        apply mul_le_mul_of_nonneg_left _ hκnn
        exact_mod_cast (Nat.mul_le_mul_right n (by omega))
      have h4 : (1:ℝ) ≤ 4 * (sigQ d n (p^r) a - 1)^2 := by nlinarith
      calc (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))
          = (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) * 1 := by simp only [mul_one]
        _ ≤ (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) * (4 * (sigQ d n (p^r) a - 1)^2) :=
            mul_le_mul (le_trans h1 h2) h4 (by norm_num) (Real.rpow_nonneg (le_of_lt hpR) _)
    calc (∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ ∑ a ∈ FlocHalfR d n p r e,
            (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) * (4 * (sigQ d n (p^r) a - 1)^2) :=
          Finset.sum_le_sum hpt
      _ = (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ))
            * (4 * ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a - 1)^2) := by
          have hstep2 : (∑ a ∈ FlocHalfR d n p r e,
                (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) * (4 * (sigQ d n (p^r) a - 1)^2))
              = ∑ a ∈ FlocHalfR d n p r e,
                  (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) * 4 * (sigQ d n (p^r) a - 1)^2 := by
            apply Finset.sum_congr rfl
            intro a _; ring
          rw [hstep2, ← Finset.mul_sum]
          ring
      _ ≤ (p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ))
            * (4 * ((Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1))) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left
            · calc (∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a - 1)^2)
                  ≤ ∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2 := by
                    apply Finset.sum_le_sum_of_subset_of_nonneg
                    · intro a ha
                      exact (mem_FlocInset.mp (mem_FlocHalfR.mp ha).1).1
                    · intro a _ _; exact sq_nonneg _
                _ ≤ (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1) := hvar p r hp hr
            · norm_num
          · exact Real.rpow_nonneg (le_of_lt hpR) _
      _ = 4 * (Csq+4) * (p:ℝ)^(r*NN d n)
            * ((p:ℝ)^((1/(4*(n:ℝ))) * ((2*n:ℕ):ℝ)) / (p:ℝ)^(n-1)) := by ring
      _ ≤ 4 * (Csq+4) * (p:ℝ)^(r*NN d n) * (1/(p:ℝ)^((5:ℝ)/4)) := by
          apply mul_le_mul_of_nonneg_left
          · rw [hκ2n]
            exact rpow_half_div_pow_le (p:ℝ) hpR2 n hn
          · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith : (0:ℝ) ≤ Csq + 4))
              (le_of_lt (pow_pos hpR _))
      _ = 4 * (Csq+4) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by ring
  have hE2 : (∑ e ∈ Finset.Icc 2 r,
        ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ 10 * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by
    have hstep : ∀ e ∈ Finset.Icc 2 r,
        (∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
          ≤ (p:ℝ)^(((e:ℝ)+1)/4) * (2 * (p:ℝ)^(r*NN d n - e)) := by
      intro e he
      obtain ⟨he2, her⟩ := Finset.mem_Icc.mp he
      have hcard' : ((FlocHalfR d n p r e).card : ℝ) ≤ ((2 * p ^ (r * NN d n - e) : ℕ) : ℝ) := by
        have h1 : (FlocHalfR d n p r e).card
            ≤ Nat.card {a : Mon d n → ZMod (p^r) // Rset d n p r e a} := by
          calc (FlocHalfR d n p r e).card
              ≤ (Finset.univ.filter (fun a => Rset d n p r e a)).card :=
                Finset.card_le_card (fun a ha => by
                  simp only [Finset.mem_filter] at ha ⊢
                  exact ⟨Finset.mem_univ _, (mem_FlocHalfR.mp ha).2.2⟩)
            _ = Nat.card {a : Mon d n → ZMod (p^r) // Rset d n p r e a} := by
                rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact_mod_cast le_trans h1 (card_Rset_le d n p r e (by omega) hp hr (by omega) her)
      calc (∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
          ≤ ∑ a ∈ FlocHalfR d n p r e,
              (p:ℝ)^((1/(4*(n:ℝ))) * (((e+1)*n:ℕ):ℝ)) := by
            apply Finset.sum_le_sum
            intro a ha
            exact rpow_neg_le_of_lower (p:ℝ) hpR1 ((e+1)*n) _ _ hκnn
              (sigQ_lower_Rset d n p r e (by omega) hp hr her a (mem_FlocHalfR.mp ha).2.2)
        _ = (p:ℝ)^((1/(4*(n:ℝ))) * (((e+1)*n:ℕ):ℝ)) * ((FlocHalfR d n p r e).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (p:ℝ)^((1/(4*(n:ℝ))) * (((e+1)*n:ℕ):ℝ)) * ((2 * p ^ (r*NN d n - e) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hcard' (Real.rpow_nonneg (le_of_lt hpR) _)
        _ = (p:ℝ)^(((e:ℝ)+1)/4) * (2 * (p:ℝ)^(r*NN d n - e)) := by
            rw [hκen e]
            push_cast
            ring
    calc (∑ e ∈ Finset.Icc 2 r,
            ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ ∑ e ∈ Finset.Icc 2 r, (p:ℝ)^(((e:ℝ)+1)/4) * (2 * (p:ℝ)^(r*NN d n - e)) :=
          Finset.sum_le_sum hstep
      _ ≤ 10 * (p:ℝ)^(r * NN d n) / (p:ℝ)^((5:ℝ)/4) :=
          sum_Icc_rpow_fourth p r (NN d n) hp.two_le (by omega)
  calc (∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ ∑ e ∈ Finset.range (r+1),
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))) := hstep1
    _ = (∑ e ∈ Finset.range 2,
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        + (∑ e ∈ Finset.Icc 2 r,
          ∑ a ∈ FlocHalfR d n p r e, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))) := hsplit2
    _ ≤ 8 * (Csq+4) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4)
          + 10 * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by
        apply add_le_add
        · rw [Finset.sum_range_succ, Finset.sum_range_one]
          have h0 := hEgen 0 (by norm_num)
          have h1 := hEgen 1 (by norm_num)
          exact le_trans (add_le_add h0 h1) (le_of_eq (by ring))
        · exact hE2
    _ = (8*Csq+42) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4) := by ring

theorem sum_Floc_more_rpow_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (Csq : ℝ) (hCsq : 0 < Csq)
    (hsqb : ∀ (p r : ℕ) [NeZero (p^r)], p.Prime → 1 ≤ r →
      (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a)^2)
        ≤ (p:ℝ)^(r*NN d n) * (1 + Csq/(p:ℝ)^(n-1))) :
    ∀ (p r : ℕ) [NeZero (p^r)], p.Prime → 1 ≤ r →
      (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ (p:ℝ)^(r*NN d n) * (1 + (Csq+5)/(p:ℝ)^((5:ℝ)/4)) := by
  intro p r hNe hp hr
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hpR1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
  have hpR2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hNn : n ≤ NN d n := le_trans (Nat.le_succ n) (succ_le_NN d n (by omega))
  have hNge3 : 3 ≤ NN d n := le_trans hn hNn
  have hκpos : (0:ℝ) < 1/(4*(n:ℝ)) := by positivity
  have hκ12 : 1/(4*(n:ℝ)) ≤ 1/12 := by
    refine one_div_le_one_div_of_le (show (0:ℝ) < 12 by norm_num) ?_
    linarith
  have hMnn : 0 ≤ (p:ℝ)^(r*NN d n) := by positivity
  have hCsq4 : (0:ℝ) ≤ Csq + 4 := by linarith
  have hP54 : (0:ℝ) < (p:ℝ)^((5:ℝ)/4) := Real.rpow_pos_of_pos hpR _
  have hcard : ((primFinset d n (p^r)).card : ℝ) ≤ (p:ℝ)^(r*NN d n) := primFinset_card_le'
  have hmom1 : (∑ a ∈ primFinset d n (p^r), sigQ d n (p^r) a)
      = (p:ℝ)^(r*NN d n) * (1 - 1/(p:ℝ)^(n+1)) * (1 - 1/(p:ℝ)^(NN d n - 1)) :=
    sum_sigQ_eq d n p r hd (by omega) hp hr
  have hvar : (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2)
      ≤ (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1) :=
    sum_sigQ_sub_one_sq_le d n hd (by omega) Csq hCsq
      (fun p₁ r₁ _ hp₁ hr₁ => sum_sigQ_eq d n p₁ r₁ hd (by omega) hp₁ hr₁)
      (fun p₁ r₁ _ hp₁ hr₁ => hsqb p₁ r₁ hp₁ hr₁) p r hp hr
  have hGOODsub : FlocMore d n p r ⊆ primFinset d n (p^r) := by
    intro a ha
    exact (mem_FlocInset.mp (mem_FlocMore.mp ha).1).1
  have hpt : ∀ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ))))
      ≤ 1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1) + (sigQ d n (p^r) a - 1)^2 := by
    intro a ha
    exact rpow_neg_le_quad_small _ _ hκpos hκ12 (le_of_lt (mem_FlocMore.mp ha).2)
  have hstep1 : (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ (∑ a ∈ primFinset d n (p^r), (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
        + (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2) := by
    calc (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        ≤ (∑ a ∈ FlocMore d n p r, (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
          + (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a - 1)^2) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hpt
      _ ≤ (∑ a ∈ primFinset d n (p^r), (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
          + (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2) := by
          apply add_le_add
          · apply Finset.sum_le_sum_of_subset_of_nonneg hGOODsub
            intro a haP haG
            have hle : sigQ d n (p^r) a ≤ 1/2 := by
              by_cases hF : a ∈ FlocInset d n p r
              · have : ¬ (1/2 < sigQ d n (p^r) a) := by
                  intro hcon
                  exact haG (by rw [FlocMore]; exact Finset.mem_filter.mpr ⟨hF, hcon⟩)
                exact not_lt.mp this
              · have hnot : ¬ FlocSet d n p r a := fun hc => hF (mem_FlocInset.mpr ⟨haP, hc⟩)
                have hz : sigQ d n (p^r) a = 0 := sigQ_eq_zero_of_not a (by
                  rintro ⟨b, hb1, hb2⟩
                  exact hnot ⟨mem_primFinset.mp haP, b, hb1, hb2⟩)
                rw [hz]; norm_num
            have h2 : 1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)
                = 1 + (1/(4*(n:ℝ))) * (1 - sigQ d n (p^r) a) := by ring
            rw [h2]
            have : (0:ℝ) ≤ 1 - sigQ d n (p^r) a := by linarith
            positivity
          · exact Finset.sum_le_sum_of_subset_of_nonneg hGOODsub (fun a _ _ => by positivity)
  have hA : (∑ a ∈ primFinset d n (p^r), (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
      = (1 + (1/(4*(n:ℝ)))) * ((primFinset d n (p^r)).card : ℝ)
          - (1/(4*(n:ℝ))) * (∑ a ∈ primFinset d n (p^r), sigQ d n (p^r) a) := by
    have h1 : (∑ a ∈ primFinset d n (p^r), (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
        = ((primFinset d n (p^r)).card : ℝ)
            - (1/(4*(n:ℝ))) * (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1))
        = (∑ a ∈ primFinset d n (p^r), sigQ d n (p^r) a) - ((primFinset d n (p^r)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, h2]
    ring
  have hX0 : (0:ℝ) ≤ 1/(p:ℝ)^(n+1) := by positivity
  have hY0 : (0:ℝ) ≤ 1/(p:ℝ)^(NN d n - 1) := by positivity
  have hX1 : 1/(p:ℝ)^(n+1) ≤ 1 := by
    have h1 : (1:ℝ) ≤ (p:ℝ)^(n+1) := one_le_pow₀ hpR1
    calc 1/(p:ℝ)^(n+1) ≤ 1/1 := one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by norm_num
  have hY1 : 1/(p:ℝ)^(NN d n - 1) ≤ 1 := by
    have h1 : (1:ℝ) ≤ (p:ℝ)^(NN d n - 1) := one_le_pow₀ hpR1
    calc 1/(p:ℝ)^(NN d n - 1) ≤ 1/1 := one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by norm_num
  have hX54 : 1/(p:ℝ)^(n+1) ≤ 1/p^((5:ℝ)/4) := by
    refine one_div_pow_le_one_div_rpow (p:ℝ) hpR1 (n+1) ((5:ℝ)/4) ?_
    have h44 : (4:ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
      have : 4 ≤ n + 1 := by omega
      exact_mod_cast this
    linarith
  have hY54 : 1/(p:ℝ)^(NN d n - 1) ≤ 1/p^((5:ℝ)/4) := by
    refine one_div_pow_le_one_div_rpow (p:ℝ) hpR1 (NN d n - 1) ((5:ℝ)/4) ?_
    have h2 : (2:ℝ) ≤ ((NN d n - 1 : ℕ) : ℝ) := by
      have : 2 ≤ NN d n - 1 := by omega
      exact_mod_cast this
    linarith
  have hB : 1/(p:ℝ)^(n-1) ≤ 1/p^((5:ℝ)/4) := by
    refine one_div_pow_le_one_div_rpow (p:ℝ) hpR1 (n-1) ((5:ℝ)/4) ?_
    have h2 : (2:ℝ) ≤ ((n-1 : ℕ) : ℝ) := by
      have : 2 ≤ n - 1 := by omega
      exact_mod_cast this
    linarith
  have hBM : (p:ℝ)^(r*NN d n) * (1/(p:ℝ)^(n-1)) ≤ (p:ℝ)^(r*NN d n) * (1/p^((5:ℝ)/4)) :=
    mul_le_mul_of_nonneg_left hB hMnn
  have hXlast : (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1)
      ≤ (Csq+4)*(p:ℝ)^(r*NN d n)/p^((5:ℝ)/4) := by
    calc (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1)
        = (Csq+4)*((p:ℝ)^(r*NN d n) * (1/(p:ℝ)^(n-1))) := by ring
      _ ≤ (Csq+4)*((p:ℝ)^(r*NN d n) * (1/p^((5:ℝ)/4))) := mul_le_mul_of_nonneg_left hBM hCsq4
      _ = (Csq+4)*(p:ℝ)^(r*NN d n)/p^((5:ℝ)/4) := by ring
  calc (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ (∑ a ∈ primFinset d n (p^r), (1 - (1/(4*(n:ℝ))) * (sigQ d n (p^r) a - 1)))
        + (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2) := hstep1
    _ = ((1 + (1/(4*(n:ℝ)))) * ((primFinset d n (p^r)).card : ℝ)
            - (1/(4*(n:ℝ))) * (∑ a ∈ primFinset d n (p^r), sigQ d n (p^r) a))
        + (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2) := by rw [hA]
    _ ≤ ((1 + (1/(4*(n:ℝ)))) * (p:ℝ)^(r*NN d n)
            - (1/(4*(n:ℝ))) * ((p:ℝ)^(r*NN d n)
              * ((1 - 1/(p:ℝ)^(n+1)) * (1 - 1/(p:ℝ)^(NN d n - 1)))))
        + (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1) := by
        apply add_le_add
        · have hsum1 : (∑ a ∈ primFinset d n (p^r), sigQ d n (p^r) a)
              = (p:ℝ)^(r*NN d n) * ((1 - 1/(p:ℝ)^(n+1)) * (1 - 1/(p:ℝ)^(NN d n - 1))) := by
            rw [hmom1]; ring
          rw [hsum1]
          have h2 : (1 + (1/(4*(n:ℝ)))) * ((primFinset d n (p^r)).card : ℝ)
              ≤ (1 + (1/(4*(n:ℝ)))) * (p:ℝ)^(r*NN d n) :=
            mul_le_mul_of_nonneg_left hcard (by positivity)
          linarith
        · exact hvar
    _ ≤ (p:ℝ)^(r*NN d n) * (1 + 1/p^((5:ℝ)/4)) + (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1) := by
        apply add_le_add
        · exact gt_arith (p:ℝ) ((p:ℝ)^(r*NN d n)) (1/(4*(n:ℝ))) (1/(p:ℝ)^(n+1))
            (1/(p:ℝ)^(NN d n - 1)) hpR2 hMnn hκ12 hX0 hX1 hY0 hY1 hX54 hY54
        · exact le_refl _
    _ ≤ (p:ℝ)^(r*NN d n) * (1 + (Csq+5)/p^((5:ℝ)/4)) := by
        calc (p:ℝ)^(r*NN d n) * (1 + 1/p^((5:ℝ)/4)) + (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1)
            ≤ (p:ℝ)^(r*NN d n) * (1 + 1/p^((5:ℝ)/4))
              + (Csq+4)*(p:ℝ)^(r*NN d n)/p^((5:ℝ)/4) := add_le_add (le_refl _) hXlast
          _ = (p:ℝ)^(r*NN d n) * (1 + (Csq+5)/p^((5:ℝ)/4)) := by ring

theorem sum_Floc_sigQ_rpow_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p r : ℕ) [NeZero (p ^ r)], p.Prime → 1 ≤ r →
      (∑ a ∈ Work.HP.NA.FlocInset d n p r,
          (Work.HP.NA.sigQ d n (p ^ r) a) ^ (-(1 / (4 * (n : ℝ)))))
        ≤ (p : ℝ) ^ (r * Work.HP.NN d n) * (1 + C / (p : ℝ) ^ ((5:ℝ)/4)) := by
  classical
  obtain ⟨Csq, hCsqpos, hsqb⟩ := sum_sigQ_sq_bound d n hd (by omega)
  refine ⟨9 * Csq + 100, by positivity, ?_⟩
  intro p r hNe hp hr
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hvar_all : ∀ (p r : ℕ) [NeZero (p^r)], p.Prime → 1 ≤ r →
      (∑ a ∈ primFinset d n (p^r), (sigQ d n (p^r) a - 1)^2)
        ≤ (Csq+4)*(p:ℝ)^(r*NN d n)/(p:ℝ)^(n-1) :=
    sum_sigQ_sub_one_sq_le d n hd (by omega) Csq hCsqpos
      (fun p₁ r₁ _ hp₁ hr₁ => sum_sigQ_eq d n p₁ r₁ hd (by omega) hp₁ hr₁)
      (fun p₁ r₁ _ hp₁ hr₁ => hsqb p₁ r₁ hp₁ hr₁)
  have hle := sum_Floc_le_half_rpow_le d n hd hn Csq hCsqpos hvar_all p r hp hr
  have hgt := sum_Floc_more_rpow_le d n hd hn Csq hCsqpos hsqb p r hp hr
  rw [sum_Floc_split d n p r (fun a => (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))]
  have hP54 : (0:ℝ) < (p:ℝ)^((5:ℝ)/4) := Real.rpow_pos_of_pos hpR _
  calc (∑ a ∈ FlocHalf d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
        + (∑ a ∈ FlocMore d n p r, (sigQ d n (p^r) a) ^ (-(1/(4*(n:ℝ)))))
      ≤ (8*Csq+42) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4)
        + (p:ℝ)^(r*NN d n) * (1 + (Csq+5)/(p:ℝ)^((5:ℝ)/4)) := add_le_add hle hgt
    _ ≤ (p:ℝ)^(r*NN d n) * (1 + (9*Csq+100)/(p:ℝ)^((5:ℝ)/4)) := by
        have hx : 0 ≤ ((p:ℝ)^((5:ℝ)/4))⁻¹ := inv_nonneg.mpr (le_of_lt hP54)
        have hMnn : 0 ≤ (p:ℝ)^(r*NN d n) := by positivity
        have hMx : 0 ≤ (p:ℝ)^(r*NN d n) * ((p:ℝ)^((5:ℝ)/4))⁻¹ := mul_nonneg hMnn hx
        have e1 : (8*Csq+42) * (p:ℝ)^(r*NN d n) / (p:ℝ)^((5:ℝ)/4)
              + (p:ℝ)^(r*NN d n) * (1 + (Csq+5)/(p:ℝ)^((5:ℝ)/4))
            = (p:ℝ)^(r*NN d n)
              + (8*Csq+42)*((p:ℝ)^(r*NN d n)*((p:ℝ)^((5:ℝ)/4))⁻¹)
              + (Csq+5)*((p:ℝ)^(r*NN d n)*((p:ℝ)^((5:ℝ)/4))⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        have e2 : (p:ℝ)^(r*NN d n) * (1 + (9*Csq+100)/(p:ℝ)^((5:ℝ)/4))
            = (p:ℝ)^(r*NN d n)
              + (9*Csq+100)*((p:ℝ)^(r*NN d n)*((p:ℝ)^((5:ℝ)/4))⁻¹) := by
          rw [div_eq_mul_inv]; ring
        rw [e1, e2]
        nlinarith [hMx]

end Work.HP.NA
