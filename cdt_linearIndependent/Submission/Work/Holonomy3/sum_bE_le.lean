import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.threshold_sum_eval

open Finset
open scoped BigOperators

namespace Work.Holonomy3

/-- The algebraic core of the denominator estimate for the lcm cap: for `m ∣ d`, `m ≤ d` and exponents `E i s ≤ i·D + s·mD/d + 3mεD`, the weighted total `Σ_{i,s,h} b_{i,h}·E_{i,s}` is at most `(m·d·D/2)·τ♭(b) - (D/2)·Σ_i σ_i + 3·d·D·ε·Σ_i σ_i`, where `σ_i = rowSum b i`. -/
theorem sum_bE_le {m r d D : ℕ} (hm : 0 < m) (hmd : m ∣ d) (hdm : m ≤ d)
    (b : Fin m → Fin r → ℕ) (ε : ℝ) (E : Fin m → Fin (d / m) → ℕ)
    (hE : ∀ i s, (E i s : ℝ) ≤ (i.1 : ℝ) * D + (s.1 : ℝ) * m * D / d + 3 * m * ε * D) :
    (∑ i, ∑ s, ∑ h, ((b i h * E i s : ℕ) : ℝ))
      ≤ ((m : ℝ) * d * D / 2) * Submission.CDTPlan.tauFlat b
        - (D / 2) * (∑ i, (Submission.CDTPlan.rowSum b i : ℝ))
        + 3 * d * D * ε * (∑ i, (Submission.CDTPlan.rowSum b i : ℝ)) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hd0 : (0:ℝ) < (d:ℝ) := by
    have : 0 < d := lt_of_lt_of_le hm hdm
    exact_mod_cast this
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hd0
  have hKcast : ((d/m : ℕ) : ℝ) = (d:ℝ)/(m:ℝ) :=
    Nat.cast_div hmd (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hm))
  have hKm : ((d/m : ℕ) : ℝ) * (m:ℝ) = (d:ℝ) := by
    have h : d/m * m = d := Nat.div_mul_cancel hmd
    calc ((d/m : ℕ) : ℝ) * (m:ℝ) = ((d/m * m : ℕ) : ℝ) := by push_cast; ring
      _ = (d:ℝ) := by rw [h]
  set S : ℝ := ∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) with hS
  set T : ℝ := ∑ i : Fin m, (i.1 : ℝ) * (Submission.CDTPlan.rowSum b i : ℝ) with hT
  set A : ℝ := ∑ s : Fin (d/m), (s.1 : ℝ) with hA
  have hAval : A = ((d/m:ℕ):ℝ) * (((d/m:ℕ):ℝ) - 1) / 2 := by
    rw [hA, Fin.sum_univ_eq_sum_range (fun i => (i:ℝ)) (d/m)]
    exact Work.Holonomy3.sum_range_cast_real (d/m)
  -- LHS rewrite
  have hLHS : (∑ i, ∑ s, ∑ h, ((b i h * E i s : ℕ) : ℝ))
      = ∑ i, (Submission.CDTPlan.rowSum b i : ℝ) * (∑ s, (E i s : ℝ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : (∑ s : Fin (d/m), ∑ h, ((b i h * E i s : ℕ) : ℝ))
        = ∑ s : Fin (d/m), (Submission.CDTPlan.rowSum b i : ℝ) * (E i s : ℝ) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have h2 : (∑ h, ((b i h * E i s : ℕ) : ℝ)) = ∑ h, (b i h : ℝ) * (E i s : ℝ) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        push_cast; ring
      rw [h2, ← Finset.sum_mul]
      congr 1
      rw [Submission.CDTPlan.rowSum, Nat.cast_sum]
    rw [h1, Finset.mul_sum]
  -- weighted sum identity
  have hW : (∑ i : Fin m, (2 * (i:ℝ) + 1) * (Submission.CDTPlan.rowSum b i : ℝ)) = 2*T + S := by
    have h1 : (∑ i : Fin m, (2 * (i:ℝ) + 1) * (Submission.CDTPlan.rowSum b i : ℝ))
        = ∑ i : Fin m, (2 * ((i:ℝ) * (Submission.CDTPlan.rowSum b i : ℝ)) + (Submission.CDTPlan.rowSum b i : ℝ)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← hT, ← hS]
  -- per-row bound
  have hbound : ∀ i : Fin m, (∑ s, (E i s : ℝ))
      ≤ ((d/m:ℕ):ℝ) * ((i.1:ℝ)*(D:ℝ)) + ((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ))
        + ((m:ℝ)*(D:ℝ)/(d:ℝ)) * A := by
    intro i
    have e1 : (∑ s : Fin (d/m), ((i.1:ℝ)*(D:ℝ))) = ((d/m:ℕ):ℝ) * ((i.1:ℝ)*(D:ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e2 : (∑ s : Fin (d/m), ((s.1:ℝ)*(m:ℝ)*(D:ℝ)/(d:ℝ))) = ((m:ℝ)*(D:ℝ)/(d:ℝ)) * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_); ring
    have e3 : (∑ s : Fin (d/m), (3*(m:ℝ)*ε*(D:ℝ))) = ((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (∑ s, (E i s : ℝ))
        ≤ ∑ s : Fin (d/m), ((i.1:ℝ)*(D:ℝ) + (s.1:ℝ)*(m:ℝ)*(D:ℝ)/(d:ℝ) + 3*(m:ℝ)*ε*(D:ℝ)) :=
          Finset.sum_le_sum (fun s _ => hE i s)
      _ = ((d/m:ℕ):ℝ) * ((i.1:ℝ)*(D:ℝ)) + ((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ)) + ((m:ℝ)*(D:ℝ)/(d:ℝ)) * A := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3]
          ring
  -- assembly
  have hC : (∑ i, (Submission.CDTPlan.rowSum b i : ℝ) * (∑ s, (E i s : ℝ)))
      ≤ ((d/m:ℕ):ℝ) * (D:ℝ) * T + ((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ)) * S
        + ((m:ℝ)*(D:ℝ)/(d:ℝ)) * A * S := by
    have g1 : (∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) * (((d/m:ℕ):ℝ) * ((i.1:ℝ)*(D:ℝ)))) = ((d/m:ℕ):ℝ)*(D:ℝ)*T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have g2 : (∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) * (((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ)))) = ((d/m:ℕ):ℝ)*(3*(m:ℝ)*ε*(D:ℝ))*S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have g3 : (∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) * (((m:ℝ)*(D:ℝ)/(d:ℝ))*A)) = ((m:ℝ)*(D:ℝ)/(d:ℝ))*A*S := by
      rw [← Finset.sum_mul, mul_comm, ← hS]
    calc (∑ i, (Submission.CDTPlan.rowSum b i : ℝ) * (∑ s, (E i s : ℝ)))
        ≤ ∑ i : Fin m, (Submission.CDTPlan.rowSum b i : ℝ) *
            (((d/m:ℕ):ℝ) * ((i.1:ℝ)*(D:ℝ)) + ((d/m:ℕ):ℝ) * (3*(m:ℝ)*ε*(D:ℝ)) + ((m:ℝ)*(D:ℝ)/(d:ℝ)) * A) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg _))
      _ = ((d/m:ℕ):ℝ)*(D:ℝ)*T + ((d/m:ℕ):ℝ)*(3*(m:ℝ)*ε*(D:ℝ))*S + ((m:ℝ)*(D:ℝ)/(d:ℝ))*A*S := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [g1, g2, g3]
  -- final arithmetic identity
  have hfin : ((m:ℝ)*(d:ℝ)*(D:ℝ)/2) * Submission.CDTPlan.tauFlat b - ((D:ℝ)/2)*S + 3*(d:ℝ)*(D:ℝ)*ε*S
      = ((d/m:ℕ):ℝ)*(D:ℝ)*T + ((d/m:ℕ):ℝ)*(3*(m:ℝ)*ε*(D:ℝ))*S + ((m:ℝ)*(D:ℝ)/(d:ℝ))*A*S := by
    rw [Submission.CDTPlan.tauFlat, hW, hAval, hKcast]
    field_simp
    ring
  rw [hLHS]
  calc (∑ i, (Submission.CDTPlan.rowSum b i : ℝ) * (∑ s, (E i s : ℝ)))
      ≤ ((d/m:ℕ):ℝ)*(D:ℝ)*T + ((d/m:ℕ):ℝ)*(3*(m:ℝ)*ε*(D:ℝ))*S + ((m:ℝ)*(D:ℝ)/(d:ℝ))*A*S := hC
    _ = ((m:ℝ)*(d:ℝ)*(D:ℝ)/2) * Submission.CDTPlan.tauFlat b - ((D:ℝ)/2)*S + 3*(d:ℝ)*(D:ℝ)*ε*S := hfin.symm

end Work.Holonomy3
