import Mathlib
import Submission.Work.FIArea2.R6.WCDefs
import Submission.Work.FIArea2.R6.fibre_card_le
import Submission.Work.FIArea2.R6.uboxSum_le_dsum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `FIArea2/R6/WCcount` — the periodic count for `WC`

In the regime `max(X,Y) ≥ c` the weighted primitive count `WC c r X Y` is bounded by counting,
for each `(h₁,w₁,w₂)`, the number of `h₂` in the box `zPz Y` that satisfy the congruence
`c ∣ w₁h₁² - w₂h₂²`.  That set is the preimage under `h ↦ (h : ZMod c)` of the solution set of
`w₂z² = w₁h₁²` in `ZMod c`, so by `R6/fibre_card_le` it has at most `ρ·(2Y/c + 1)` elements,
where `ρ` is the number of solutions mod `c`.  Summing the weights `1/max(|w₁|,|w₂|)` and using
`R6/LD_lossy` gives

  `WC c r X Y ≤ 64·X·r·τ(c)^5·(2Y/c + 1)`.

Together with `R6/WC_basic` this proves `R6/WC_cube`:

  `c³ ≤ r(X²+Y²)`  ⟹  `WC c r X Y ≤ C·X·Y·r·τ(c)^5/c`.
-/

set_option maxHeartbeats 2000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The periodic count.**  The number of `h` in a bounded set `S` (`|h| ≤ Y`) lying over the
solution set of `b z² = a` in `ZMod c` is at most `ρ · (2Y/c + 1)`. -/
lemma hcount_le (c Y : ℕ) [NeZero c] (a b : ℤ) (S : Finset ℤ)
    (hS : ∀ h ∈ S, h.natAbs ≤ Y) :
    ((S.filter (fun (h : ℤ) => (b : ZMod c) * (h : ZMod c) ^ 2 = (a : ZMod c))).card : ℝ)
      ≤ (((Finset.univ : Finset (ZMod c)).filter
            (fun z => (b : ZMod c) * z ^ 2 = (a : ZMod c))).card : ℝ)
          * (2 * (Y : ℝ) / (c : ℝ) + 1) := by
  set R : Finset (ZMod c) := (Finset.univ : Finset (ZMod c)).filter
    (fun z => (b : ZMod c) * z ^ 2 = (a : ZMod c)) with hR
  set T : Finset ℤ := S.filter
    (fun (h : ℤ) => (b : ZMod c) * (h : ZMod c) ^ 2 = (a : ZMod c)) with hT
  have hTb : ∀ h ∈ T, h.natAbs ≤ Y := by
    intro h hh
    exact hS h (Finset.mem_of_mem_filter h hh)
  have himg : T.image (fun (h : ℤ) => (h : ZMod c)) ⊆ R := by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
  have hfib : ∀ z ∈ T.image (fun (h : ℤ) => (h : ZMod c)),
      ((T.filter (fun (h : ℤ) => (h : ZMod c) = z)).card : ℝ) ≤ 2 * (Y : ℝ) / (c : ℝ) + 1 :=
    fun z _ => fibre_card_le Y c T hTb z
  have key : T.card = ∑ z ∈ T.image (fun (h : ℤ) => (h : ZMod c)),
      (T.filter (fun (h : ℤ) => (h : ZMod c) = z)).card :=
    Finset.card_eq_sum_card_image _ _
  calc ((S.filter (fun (h : ℤ) => (b : ZMod c) * (h : ZMod c) ^ 2 = (a : ZMod c))).card : ℝ)
      = (T.card : ℝ) := rfl
    _ = ((∑ z ∈ T.image (fun (h : ℤ) => (h : ZMod c)),
            (T.filter (fun (h : ℤ) => (h : ZMod c) = z)).card : ℕ) : ℝ) := by rw [key]
    _ = ∑ z ∈ T.image (fun (h : ℤ) => (h : ZMod c)),
          ((T.filter (fun (h : ℤ) => (h : ZMod c) = z)).card : ℝ) := by push_cast; ring
    _ ≤ ∑ z ∈ T.image (fun (h : ℤ) => (h : ZMod c)), (2 * (Y : ℝ) / (c : ℝ) + 1) :=
        Finset.sum_le_sum hfib
    _ = ((T.image (fun (h : ℤ) => (h : ZMod c))).card : ℝ) * (2 * (Y : ℝ) / (c : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (R.card : ℝ) * (2 * (Y : ℝ) / (c : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Finset.card_le_card himg

/-- **The periodic count for `WC`**, conditional on the lossy local-density bound `hLD`
(`= R6/LD_lossy` at `S = r`):

  `WC c r X Y ≤ 64·X·r·τ(c)^5·(2Y/c+1)`. -/
lemma WC_le_periodic (c r X Y : ℕ) [NeZero c]
    (hLD : (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r,
              (((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (v2 : ZMod c) * z ^ 2
                    = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
                / ((max v1.natAbs v2.natAbs : ℕ) : ℝ))
            ≤ 64 * (X : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5) :
    WC c r X Y ≤ 64 * (X : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5
      * (2 * (Y : ℝ) / (c : ℝ) + 1) := by
  set K : ℝ := 2 * (Y : ℝ) / (c : ℝ) + 1 with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
    have : (0 : ℝ) ≤ 2 * (Y : ℝ) / (c : ℝ) := by positivity
    linarith
  have hinner : ∀ h1 ∈ zPz X, ∀ w1 ∈ zPz r, ∀ w2 ∈ zPz r,
      (∑ h2 ∈ zPz Y,
          (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
              ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
            then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0))
        ≤ K * ((((Finset.univ : Finset (ZMod c)).filter
              (fun z => (w2 : ZMod c) * z ^ 2
                = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
            / ((max w1.natAbs w2.natAbs : ℕ) : ℝ)) := by
    intro h1 _ w1 _ w2 _
    have hmc0 : (0 : ℝ) ≤ ((max w1.natAbs w2.natAbs : ℕ) : ℝ) := by positivity
    have hQsub : ((zPz Y).filter (fun (h2 : ℤ) => w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
          ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2))
        ⊆ ((zPz Y).filter (fun (h2 : ℤ) => (w2 : ZMod c) * (h2 : ZMod c) ^ 2
              = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)) := by
      intro h2 hh
      rw [Finset.mem_filter] at hh ⊢
      refine ⟨hh.1, ?_⟩
      have hd : (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2 := hh.2.2
      have hz : (((w1 * h1 ^ 2 - w2 * h2 ^ 2 : ℤ)) : ZMod c) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd (w1 * h1 ^ 2 - w2 * h2 ^ 2) c]; exact hd
      have hcast : ((w1 * h1 ^ 2 : ℤ) : ZMod c) = ((w2 * h2 ^ 2 : ℤ) : ZMod c) := by
        have h := hz
        rw [Int.cast_sub] at h
        exact sub_eq_zero.mp h
      push_cast at hcast ⊢
      exact hcast.symm
    have hpt : ∀ h2 : ℤ, (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
            ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0)
        ≤ (if w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0 ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0) := by
      intro h2
      by_cases hP : Int.gcd w1 w2 = 1 <;> by_cases hQ : w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
        ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2 <;>
        simp [hP, hQ, one_div_nonneg, hmc0]
    calc (∑ h2 ∈ zPz Y,
          (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
              ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
            then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0))
        ≤ ∑ h2 ∈ zPz Y,
            (if w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0 ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
              then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0) :=
          Finset.sum_le_sum (fun h2 _ => hpt h2)
      _ = (1 / ((max w1.natAbs w2.natAbs : ℕ) : ℝ))
            * ((((zPz Y).filter (fun (h2 : ℤ) => w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
                  ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2)).card : ℕ) : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (1 / ((max w1.natAbs w2.natAbs : ℕ) : ℝ))
            * ((((zPz Y).filter (fun (h2 : ℤ) => (w2 : ZMod c) * (h2 : ZMod c) ^ 2
                  = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℕ) : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact_mod_cast Finset.card_le_card hQsub
      _ ≤ (1 / ((max w1.natAbs w2.natAbs : ℕ) : ℝ))
            * (((((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (w2 : ZMod c) * z ^ 2
                    = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℕ) : ℝ) * K) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hh := hcount_le c Y (w1 * h1 ^ 2) w2 (zPz Y)
            (fun h hh => natAbs_le_of_mem_zPz hh)
          rw [hKdef]
          simpa using hh
      _ = K * ((((Finset.univ : Finset (ZMod c)).filter
              (fun z => (w2 : ZMod c) * z ^ 2
                = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
            / ((max w1.natAbs w2.natAbs : ℕ) : ℝ)) := by
          rw [mul_comm]; ring
  have hperm : (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r,
        (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
            ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0))
      = ∑ h1 ∈ zPz X, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r, ∑ h2 ∈ zPz Y,
        (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
            ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl; intro h1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w1 _
    exact Finset.sum_comm
  have hbound : (∑ h1 ∈ zPz X, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r, ∑ h2 ∈ zPz Y,
        (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
            ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0))
      ≤ K * (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r,
              (((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (v2 : ZMod c) * z ^ 2
                    = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
                / ((max v1.natAbs v2.natAbs : ℕ) : ℝ)) := by
    calc (∑ h1 ∈ zPz X, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r, ∑ h2 ∈ zPz Y,
          (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
              ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
            then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0))
        ≤ ∑ h1 ∈ zPz X, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r,
            K * ((((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (w2 : ZMod c) * z ^ 2
                    = (w1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
                / ((max w1.natAbs w2.natAbs : ℕ) : ℝ)) :=
          Finset.sum_le_sum (fun h1 hh1 => Finset.sum_le_sum (fun w1 hw1 =>
            Finset.sum_le_sum (fun w2 hw2 => hinner h1 hh1 w1 hw1 w2 hw2)))
      _ = K * (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r,
              (((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (v2 : ZMod c) * z ^ 2
                    = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
                / ((max v1.natAbs v2.natAbs : ℕ) : ℝ)) := by
          simp only [Finset.mul_sum]
  calc WC c r X Y
      = (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r,
        (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
            ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
          then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0)) := rfl
    _ = _ := hperm
    _ ≤ K * (∑ h1 ∈ zPz X, ∑ v1 ∈ zPz r, ∑ v2 ∈ zPz r,
              (((Finset.univ : Finset (ZMod c)).filter
                  (fun z => (v2 : ZMod c) * z ^ 2
                    = (v1 : ZMod c) * ((h1 : ZMod c)) ^ 2)).card : ℝ)
                / ((max v1.natAbs v2.natAbs : ℕ) : ℝ)) := hbound
    _ ≤ K * (64 * (X : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5) :=
        mul_le_mul_of_nonneg_left hLD hK0
    _ = 64 * (X : ℝ) * (r : ℝ) * ((c.divisors.card : ℝ)) ^ 5 * K := by ring

end

end Work.FIArea2.R6
