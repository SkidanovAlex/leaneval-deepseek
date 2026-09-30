import Mathlib
import Submission.Work.BMF.mertens.integral_Ici_indicator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mertens

open MeasureTheory intervalIntegral

/-- `∫ t in p..x, t ^ (-(1+ε)) = (p^(-ε) - x^(-ε))/ε` for `0 < p ≤ x`, `ε > 0`. -/
theorem integral_rpow_neg_one_sub {p x ε : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hε : 0 < ε) :
    ∫ t in p..x, t ^ (-(1 + ε)) = (p ^ (-ε) - x ^ (-ε)) / ε := by
  have h3 : (0 : ℝ) ∉ Set.uIcc p x := by
    rw [Set.uIcc_of_le hpx, Set.mem_Icc]
    intro h; linarith [h.1]
  have hne : (-(1 + ε)) ≠ -1 := by linarith
  have hεne : ε ≠ 0 := ne_of_gt hε
  rw [integral_rpow (Or.inr ⟨hne, h3⟩), show -(1 + ε) + 1 = -ε by ring]
  field_simp
  try ring

/-- The partial sum of reciprocal primes is a step function on `(-∞, x]`. -/
theorem primesLE_sum_step {x t : ℝ} (ht0 : 0 ≤ t) (htx : t ≤ x) :
    (∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
      = ∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ t then 1 else 0) := by
  have hle : ⌊t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono htx
  have hF : (⌊t⌋₊).primesLE = ((⌊x⌋₊).primesLE).filter (fun p => p ≤ ⌊t⌋₊) := by
    ext p
    rw [Nat.mem_primesLE, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · intro h
      exact ⟨⟨le_trans h.1 hle, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  rw [hF, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : (p : ℝ) ≤ t
  · rw [if_pos (Nat.le_floor h), if_pos h, mul_one]
  · rw [if_neg (fun hc => h (le_trans (by exact_mod_cast hc) (Nat.floor_le ht0))), if_neg h,
      mul_zero]

/-- Integrability of an `Ici`-indicator of a function continuous on `[a,b]`. -/
theorem intervalIntegrable_Ici_indicator {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) :
    IntervalIntegrable (fun t => Set.indicator (Set.Ici c) g t) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (le_trans hac hcb)]
  have hgc : ContinuousOn g (Set.Icc c b) := hg.mono (Set.Icc_subset_Icc hac le_rfl)
  have hint : IntegrableOn g (Set.Icc c b) volume :=
    ContinuousOn.integrableOn_compact (f := g) isCompact_Icc hgc
  have hind : IntegrableOn (fun t => Set.indicator (Set.Icc c b) g t) (Set.Ioc a b) volume :=
    (hint.integrable_indicator measurableSet_Icc).integrableOn
  refine IntegrableOn.congr_fun hind ?_ measurableSet_Ioc
  intro t ht
  rw [Set.mem_Ioc] at ht
  simp only [Set.indicator_apply, Set.mem_Icc, Set.mem_Ici]
  by_cases hct : c ≤ t
  · rw [if_pos ⟨hct, ht.2⟩, if_pos hct]
  · rw [if_neg (fun h => hct h.1), if_neg hct]

theorem primeRpow_abel {x ε : ℝ} (hx : 2 ≤ x) (hε : 0 < ε) :
    (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ) ^ (1 + ε)) =
      x ^ (-ε) * (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) +
        ε * ∫ t in (2 : ℝ)..x, t ^ (-(1 + ε)) * (∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / p) := by
  have hx0 : 0 < x := by linarith
  set P : Finset ℕ := (⌊x⌋₊).primesLE with hP
  have hPmem : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesLE (hP ▸ hp)
  have hPle : ∀ p ∈ P, (p : ℝ) ≤ x := fun p hp =>
    le_trans (by exact_mod_cast (Nat.mem_primesLE.mp (hP ▸ hp)).1) (Nat.floor_le hx0.le)
  have hP2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (hPmem p hp).two_le
  have hPpos : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => lt_of_lt_of_le (by norm_num) (hP2 p hp)
  -- Rewrite the left hand side.
  have hLHS : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ (1 + ε))
      = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (p : ℝ) ^ (-ε) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 := hPpos p hp
    rw [Real.rpow_add hp0, Real.rpow_one, Real.rpow_neg (le_of_lt hp0)]
    simp only [one_div, mul_inv]
  -- The step-function identity.
  have hstep : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      (∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ t then 1 else 0) := by
    intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have h := primesLE_sum_step (x := x) (t := t) (by linarith [ht.1]) ht.2
    rw [h, ← hP]
  -- Evaluation of the integral.
  have hInt : ∫ t in (2 : ℝ)..x, t ^ (-(1 + ε)) * (∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
      = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)) / ε := by
    have h1 : ∫ t in (2 : ℝ)..x, t ^ (-(1 + ε)) * (∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
        = ∫ t in (2 : ℝ)..x,
            t ^ (-(1 + ε)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ t then 1 else 0)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hstep t ht]
    have hInt0 : ∀ p ∈ P, IntervalIntegrable
        (fun t => (1 : ℝ) / (p : ℝ) * (t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0)))
        volume (2 : ℝ) x := by
      intro p hp
      have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 + ε))) (Set.Icc (2 : ℝ) x) :=
        ContinuousOn.rpow_const continuousOn_id
          (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)))
      have hbase : IntervalIntegrable
          (fun t => Set.indicator (Set.Ici (p : ℝ)) (fun t => t ^ (-(1 + ε))) t)
          volume (2 : ℝ) x :=
        intervalIntegrable_Ici_indicator (hP2 p hp) (hPle p hp) hcont
      refine IntervalIntegrable.congr ?_ (hbase.const_mul ((1 : ℝ) / (p : ℝ)))
      intro t ht
      simp only [Set.indicator_apply, Set.mem_Ici, mul_boole]
    have h2 : ∫ t in (2 : ℝ)..x,
          t ^ (-(1 + ε)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ t then 1 else 0))
        = ∑ p ∈ P, ∫ t in (2 : ℝ)..x,
            (1 : ℝ) / (p : ℝ) * (t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0)) := by
      rw [show (fun t => t ^ (-(1 + ε)) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ t then 1 else 0)))
            = (fun t => ∑ p ∈ P,
                (1 : ℝ) / (p : ℝ) * (t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0))) from by
          funext t
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p hp => by ring)]
      exact intervalIntegral.integral_finsetSum hInt0
    have h3 : ∑ p ∈ P, ∫ t in (2 : ℝ)..x,
            (1 : ℝ) / (p : ℝ) * (t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0))
        = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)) / ε := by
      apply Finset.sum_congr rfl
      intro p hp
      have hinner : ∫ t in (2 : ℝ)..x, (t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0))
          = ((p : ℝ) ^ (-ε) - x ^ (-ε)) / ε := by
        rw [show (fun t => t ^ (-(1 + ε)) * (if (p : ℝ) ≤ t then 1 else 0))
              = (fun t => if (p : ℝ) ≤ t then t ^ (-(1 + ε)) else 0) from by
            funext t; rw [mul_boole]]
        rw [integral_Ici_indicator ⟨hP2 p hp, hPle p hp⟩]
        exact integral_rpow_neg_one_sub (hPpos p hp) (hPle p hp) hε
      rw [intervalIntegral.integral_const_mul, hinner, mul_div_assoc]
    exact h1.trans (h2.trans h3)
  -- Final algebra.
  rw [hLHS, hInt]
  have hkey : x ^ (-ε) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
      + ε * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)) / ε)
      = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (p : ℝ) ^ (-ε) := by
    have h1 : ε * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)) / ε)
        = ∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (hPpos p hp)
      have hεne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h2 : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)))
        = (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * (p : ℝ) ^ (-ε))
          - x ^ (-ε) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
      have hcongr : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) * ((p : ℝ) ^ (-ε) - x ^ (-ε)))
          = ∑ p ∈ P, ((1 : ℝ) / (p : ℝ) * (p : ℝ) ^ (-ε)
              - (1 : ℝ) / (p : ℝ) * x ^ (-ε)) :=
        Finset.sum_congr rfl (fun p hp => by ring)
      rw [hcongr, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_mul, mul_comm]
    rw [h1, h2]
    ring
  exact hkey.symm

end Work.BMF.mertens
