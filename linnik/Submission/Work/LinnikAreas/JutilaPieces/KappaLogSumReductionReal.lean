import Mathlib
import Submission.Work.LinnikAreas.Density4.mu_kappa_log_sum

namespace Work.LinnikAreas.JutilaPieces

open Finset BigOperators
open Work.LinnikAreas.Density4
open scoped BigOperators

noncomputable section

/-- The inner sum evaluation for **real** `Q`: for `1 ≤ d`,
`Σ_{m ≤ ⌊Q⌋/d, (dm,t)=1} μ(dm)·β(d)·log(Q/(dm))/(dm)`
`   = [d squarefree, (d,t)=1]·Π(d)·selTheta(Q/d, d·t)`. -/
lemma inner_selTheta_real (Q : ℝ) (d t : ℕ) (hd : 1 ≤ d) :
    (∑ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime (d*m) t),
        (ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
          Real.log (Q / ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ))
    = (if Squarefree d ∧ Nat.Coprime d t then (1:ℝ) else 0) *
        (prodKappa d * selTheta (Q / (d:ℝ)) (d*t)) := by
  classical
  have hQd : ⌊Q/(d:ℝ)⌋₊ = ⌊Q⌋₊ / d := Nat.floor_div_natCast Q d
  have hsel : selTheta (Q/(d:ℝ)) (d*t)
      = ∑ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m (d*t)),
          (ArithmeticFunction.moebius m : ℝ) * Real.log ((Q/(d:ℝ))/(m:ℝ)) / (m:ℝ) := by
    simp only [selTheta]
    rw [hQd]
  let C : ℝ := betaFun d * (ArithmeticFunction.moebius d : ℝ) / (d:ℝ)
  by_cases hdt : Nat.Coprime d t
  · by_cases hds : Squarefree d
    · rw [if_pos ⟨hds, hdt⟩, one_mul]
      have hfil : (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime (d*m) t)
          = (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m t) := by
        refine Finset.filter_congr (fun m _ => ?_)
        rw [Nat.coprime_mul_iff_left]
        exact ⟨fun h => h.2, fun h => ⟨hdt, h⟩⟩
      rw [hfil]
      have hpt : ∀ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m t),
          (ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            Real.log (Q / ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)
          = (if Nat.Coprime d m then (1:ℝ) else 0) *
            (C * ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ))) := by
        intro m hm
        obtain ⟨hmIcc, -⟩ := Finset.mem_filter.mp hm
        rw [moebius_mul_eq d m]
        by_cases hcm : Nat.Coprime d m
        · rw [if_pos hcm, if_pos hcm, Nat.cast_mul]
          have hm0 : (m:ℝ) ≠ 0 := by
            have : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
            positivity
          simp only [C]
          field_simp
        · rw [if_neg hcm, if_neg hcm, zero_mul]
          simp
      rw [Finset.sum_congr rfl hpt]
      have hpt2 : ∀ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m t),
          (if Nat.Coprime d m then (1:ℝ) else 0) *
            (C * ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ)))
          = (if Nat.Coprime m (d*t) then
              C * ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ)) else 0) := by
        intro m hm
        have hmt : Nat.Coprime m t := (Finset.mem_filter.mp hm).2
        have hiff : Nat.Coprime d m ↔ Nat.Coprime m (d*t) := by
          rw [Nat.coprime_mul_iff_right]
          exact ⟨fun h => ⟨h.symm, hmt⟩, fun h => h.1.symm⟩
        by_cases h : Nat.Coprime d m
        · rw [if_pos h, if_pos (hiff.mp h), one_mul]
        · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), zero_mul]
      rw [Finset.sum_congr rfl hpt2, ← Finset.sum_filter, Finset.filter_filter]
      have hfil2 : (Finset.Icc 1 (⌊Q⌋₊ / d)).filter
            (fun m => Nat.Coprime m t ∧ Nat.Coprime m (d*t))
          = (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m (d*t)) := by
        refine Finset.filter_congr (fun m _ => ?_)
        rw [Nat.coprime_mul_iff_right]
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨h.2, h⟩
      rw [hfil2]
      calc (∑ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m (d*t)),
              C * ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ)))
          = C * ∑ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m (d*t)),
              ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ)) := by
            rw [Finset.mul_sum]
        _ = prodKappa d * ∑ m ∈ (Finset.Icc 1 (⌊Q⌋₊ / d)).filter (fun m => Nat.Coprime m (d*t)),
              ((ArithmeticFunction.moebius m : ℝ) *
                Real.log (Q / ((d*m:ℕ):ℝ)) / (m:ℝ)) := by
            rw [show C = prodKappa d from prodKappa_eq d hds]
        _ = prodKappa d * selTheta (Q/(d:ℝ)) (d*t) := by
            rw [hsel]
            congr 1
            refine Finset.sum_congr rfl (fun m hm => ?_)
            have hlog : Real.log (Q / ((d*m:ℕ):ℝ)) = Real.log ((Q/(d:ℝ))/(m:ℝ)) := by
              rw [Nat.cast_mul, div_div]
            rw [hlog]
    · rw [if_neg (fun h => hds h.1), zero_mul]
      refine Finset.sum_eq_zero (fun m hm => ?_)
      simp [betaFun, hds]
  · rw [if_neg (fun h => hdt h.2), zero_mul]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    obtain ⟨-, hcm⟩ := Finset.mem_filter.mp hm
    exact absurd (hcm.coprime_dvd_left (Nat.dvd_mul_right d m)) hdt

/-- The exact reduction of the `κ`-weighted coprime log-weighted Möbius sum to a `d`-sum of
`selTheta`-values, for **real** `Q ≥ 1`.  This is the real-`Q` version of
`Work.LinnikAreas.Density4.kappa_log_sum_reduction` (proved for `Q : ℕ` in
`Submission/Work/LinnikAreas/Density4/mu_kappa_log_sum.lean`); the same proof goes through verbatim
(use `Nat.floor_div_natCast` for `⌊Q⌋₊ / d = ⌊Q / d⌋₊` and `Real.log_div`/`Real.log_mul` for
`log Q - log (d*m) = log ((Q/d)/m)`). -/
theorem KappaLogSumReductionReal (Q : ℝ) (t : ℕ) (hQ : 1 ≤ Q) :
    (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (ArithmeticFunction.moebius n : ℝ) * Work.LinnikAreas.Density4.kappaW n *
          Real.log (Q / (n : ℝ)) / (n : ℝ))
      = ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          Work.LinnikAreas.Density4.prodKappa d *
            Work.LinnikAreas.Density4.selTheta (Q / (d : ℝ)) (d * t) := by
  classical
  have h1 : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => Nat.Coprime n t),
        (ArithmeticFunction.moebius n : ℝ) * kappaW n *
          Real.log (Q / (n : ℝ)) / (n : ℝ))
      = ∑ n ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ d ∈ n.divisors,
          (if Nat.Coprime n t then (1:ℝ) else 0) *
            ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
              Real.log (Q / (n : ℝ)) / (n : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hnt : Nat.Coprime n t
    · rw [if_pos hnt, if_pos hnt, ← sum_betaFun_eq_kappaW n hn1]
      have hstep : (ArithmeticFunction.moebius n : ℝ) * (∑ d ∈ n.divisors, betaFun d) *
            Real.log (Q / (n : ℝ)) / (n : ℝ)
          = ∑ d ∈ n.divisors, (1:ℝ) * ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
              Real.log (Q / (n : ℝ)) / (n : ℝ)) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl (fun d hd => ?_)
        ring
      rw [hstep]
    · rw [if_neg hnt, if_neg hnt]
      simp
  rw [h1, sum_Icc_swap_divisors ⌊Q⌋₊
    (fun d n => (if Nat.Coprime n t then (1:ℝ) else 0) *
      ((ArithmeticFunction.moebius n : ℝ) * betaFun d *
        Real.log (Q / (n : ℝ)) / (n : ℝ)))]
  have h2 : ∀ d ∈ Finset.Icc 1 ⌊Q⌋₊,
      (∑ m ∈ Finset.Icc 1 (⌊Q⌋₊/d),
          (if Nat.Coprime (d*m) t then (1:ℝ) else 0) *
            ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
              Real.log (Q / ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)))
        = (if Squarefree d ∧ Nat.Coprime d t then
            (prodKappa d * selTheta (Q/(d:ℝ)) (d*t)) else 0) := by
    intro d hd
    obtain ⟨hd1, -⟩ := Finset.mem_Icc.mp hd
    have hite : ∀ m : ℕ, (if Nat.Coprime (d*m) t then (1:ℝ) else 0) *
          ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            Real.log (Q / ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ))
        = (if Nat.Coprime (d*m) t then
          ((ArithmeticFunction.moebius (d*m) : ℝ) * betaFun d *
            Real.log (Q / ((d*m:ℕ):ℝ)) / ((d*m:ℕ):ℝ)) else 0) := by
      intro m; rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl (fun m _ => hite m), ← Finset.sum_filter,
      inner_selTheta_real Q d t hd1]
    by_cases h : Squarefree d ∧ Nat.Coprime d t
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]

end

end Work.LinnikAreas.JutilaPieces
