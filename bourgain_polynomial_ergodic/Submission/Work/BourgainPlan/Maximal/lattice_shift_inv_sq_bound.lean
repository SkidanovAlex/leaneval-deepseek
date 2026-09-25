import Mathlib
import Submission.Work.BourgainPlan.Maximal.tsum_int_eq_tsum_sub_add_tsum_add
import Submission.Work.BourgainPlan.Maximal.nat_inv_sq_shift_tail

namespace Work.BourgainPlan.Maximal

/-- If `n ≥ 0` and `n ≤ |p|` then `1/(p²+c²) ≤ 2/(n+c)²` for `c > 0`. -/
private lemma inv_sq_add_le_of_abs (p n c : ℝ) (hc : 0 < c) (hn : 0 ≤ n) (hp : n ≤ |p|) :
    1 / (p ^ 2 + c ^ 2) ≤ 2 / (n + c) ^ 2 := by
  have hden1 : (0:ℝ) < p ^ 2 + c ^ 2 := by positivity
  have hden2 : (0:ℝ) < (n + c) ^ 2 := by
    have : 0 < n + c := by linarith
    positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hp2 : n ^ 2 ≤ p ^ 2 := by
    have h1 : n ^ 2 ≤ |p| ^ 2 := by nlinarith [abs_nonneg p]
    rwa [sq_abs] at h1
  nlinarith [sq_nonneg (n - c), hp2, hn, hc]

/-- If the two rays `{…, K-2, K-1}` and `{K, K+1, …}` of a `ℤ`-indexed sequence are
summable, then so is the whole sequence. -/
private lemma summable_int_of_summable_rays (f : ℤ → ℝ) (K : ℤ)
    (h1 : Summable fun n : ℕ => f (K - 1 - (n:ℤ)))
    (h2 : Summable fun n : ℕ => f (K + (n:ℤ))) : Summable f := by
  let e : ℕ ⊕ ℕ ≃ ℤ :=
    ((Equiv.sumComm ℕ ℕ).trans Equiv.intEquivNatSumNat.symm).trans (Equiv.addRight K)
  have he_inl : ∀ n : ℕ, e (Sum.inl n) = K - 1 - (n : ℤ) := fun n => by
    simp only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl]
    show Equiv.intEquivNatSumNat.symm (Sum.inr n) + K = K - 1 - (n : ℤ)
    rw [show Equiv.intEquivNatSumNat.symm (Sum.inr n) = Int.negSucc n from rfl]
    omega
  have he_inr : ∀ n : ℕ, e (Sum.inr n) = K + (n : ℤ) := fun n => by
    simp only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr]
    show Equiv.intEquivNatSumNat.symm (Sum.inl n) + K = K + (n : ℤ)
    rw [show Equiv.intEquivNatSumNat.symm (Sum.inl n) = (n : ℤ) from rfl]
    ring
  have hcomp : Summable (f ∘ ⇑e) := by
    refine Summable.sum (fun x => f (e x)) ?_ ?_
    · exact h1.congr (fun n => by simp only [Function.comp_apply]; rw [he_inl])
    · exact h2.congr (fun n => by simp only [Function.comp_apply]; rw [he_inr])
  exact (Equiv.summable_iff e).mp hcomp

/-- For `c ≥ 1` and any real shift `σ`, the lattice sum `∑_{m ∈ ℤ} 1/((m+σ)² + c²)`
converges and is `O(1/c)`. -/
theorem lattice_shift_inv_sq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c → ∀ σ : ℝ,
      Summable (fun m : ℤ => 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) ∧
      (∑' m : ℤ, 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2)) ≤ C / c := by
  refine ⟨8, by norm_num, ?_⟩
  intro c hc σ
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  -- Split ℤ at the nearest lattice point above `-σ`, so that both rays see a
  -- "square shift" in `[0,1)`.
  set K : ℤ := ⌈-σ⌉ with hK
  set f : ℤ → ℝ := fun m => 1 / (((m : ℝ) + σ) ^ 2 + c ^ 2) with hf
  have hKle : -σ ≤ (K : ℝ) := by simpa [hK] using (Int.le_ceil (-σ))
  have hKlt : (K : ℝ) < -σ + 1 := by simpa [hK] using (Int.ceil_lt_add_one (-σ))
  have hA0 : (0:ℝ) ≤ (K:ℝ) + σ := by linarith
  have hA1 : (K:ℝ) + σ < 1 := by linarith
  -- Pointwise bounds against `2/(n+c)²`.
  have hb2 : ∀ n : ℕ, f (K + (n:ℤ)) ≤ 2 / ((n:ℝ) + c)^2 := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hp : (n:ℝ) ≤ |((K:ℝ) + σ) + (n:ℝ)| := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (K:ℝ) + σ + (n:ℝ))]
      linarith
    have h := inv_sq_add_le_of_abs ((K:ℝ) + σ + (n:ℝ)) (n:ℝ) c hcpos hn0 hp
    have heq : f (K + (n:ℤ)) = 1 / ((((K:ℝ) + σ) + (n:ℝ))^2 + c^2) := by
      simp only [hf]; push_cast; ring
    rw [heq]; exact h
  have hb1 : ∀ n : ℕ, f (K - 1 - (n:ℤ)) ≤ 2 / ((n:ℝ) + c)^2 := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hp : (n:ℝ) ≤ |((K:ℝ) + σ) - 1 - (n:ℝ)| := by
      have h1 : ((K:ℝ) + σ) - 1 - (n:ℝ) = -((n:ℝ) + 1 - ((K:ℝ) + σ)) := by ring
      rw [h1, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) + 1 - ((K:ℝ) + σ))]
      linarith
    have h := inv_sq_add_le_of_abs (((K:ℝ) + σ) - 1 - (n:ℝ)) (n:ℝ) c hcpos hn0 hp
    have heq : f (K - 1 - (n:ℤ)) = 1 / ((((K:ℝ) + σ) - 1 - (n:ℝ))^2 + c^2) := by
      simp only [hf]; push_cast; ring
    rw [heq]; exact h
  have hnn1 : ∀ n : ℕ, (0:ℝ) ≤ f (K - 1 - (n:ℤ)) := by intro n; simp only [hf]; positivity
  have hnn2 : ∀ n : ℕ, (0:ℝ) ≤ f (K + (n:ℤ)) := by intro n; simp only [hf]; positivity
  -- The comparison series `∑ 2/(n+c)²`.
  have htail := nat_inv_sq_shift_tail c hcpos
  have hG : Summable (fun n : ℕ => 2 / ((n:ℝ) + c)^2) := by
    have h0 : Summable (fun n : ℕ => 1 / (c + (n:ℝ))^2) := htail.1
    refine (h0.mul_left 2).congr (fun n => ?_)
    ring
  have hGtsum : (∑' n : ℕ, 2 / ((n:ℝ) + c)^2) ≤ 2 * (1/c + 1/c^2) := by
    have hcongr : (∑' n : ℕ, 2 / ((n:ℝ) + c)^2) = 2 * (∑' n : ℕ, 1 / (c + (n:ℝ))^2) := by
      rw [show (∑' n : ℕ, 2 / ((n:ℝ) + c)^2) = ∑' n : ℕ, 2 * (1 / (c + (n:ℝ))^2) from
            tsum_congr (fun n => by ring)]
      rw [tsum_mul_left]
    rw [hcongr]
    have := htail.2
    linarith
  have hg2s : Summable (fun n : ℕ => f (K + (n:ℤ))) :=
    Summable.of_nonneg_of_le hnn2 hb2 hG
  have hg1s : Summable (fun n : ℕ => f (K - 1 - (n:ℤ))) :=
    Summable.of_nonneg_of_le hnn1 hb1 hG
  have ht1 : (∑' n : ℕ, f (K - 1 - (n:ℤ))) ≤ 2 * (1/c + 1/c^2) :=
    le_trans (Summable.tsum_le_tsum hb1 hg1s hG) hGtsum
  have ht2 : (∑' n : ℕ, f (K + (n:ℤ))) ≤ 2 * (1/c + 1/c^2) :=
    le_trans (Summable.tsum_le_tsum hb2 hg2s hG) hGtsum
  have hc2 : (1:ℝ)/c^2 ≤ 1/c := by
    have : c ≤ c^2 := by nlinarith
    exact one_div_le_one_div_of_le hcpos this
  -- Every linarith step below is phrased with `n * (1/c)` rather than `n/c`, since
  -- `linarith` distinguishes `4/c` and `4 * (1/c)` as atoms.
  have hconst : 2 * (1/c + 1/c^2) ≤ 4 * (1/c) := by linarith
  have ht1' : (∑' n : ℕ, f (K - 1 - (n:ℤ))) ≤ 4 * (1/c) := le_trans ht1 hconst
  have ht2' : (∑' n : ℕ, f (K + (n:ℤ))) ≤ 4 * (1/c) := le_trans ht2 hconst
  constructor
  · exact summable_int_of_summable_rays f K hg1s hg2s
  · rw [tsum_int_eq_tsum_sub_add_tsum_add f K hg1s hg2s]
    rw [show (8:ℝ)/c = 8 * (1/c) by ring]
    linarith [ht1', ht2']

end Work.BourgainPlan.Maximal
