import Mathlib
import Submission.Work.BourgainPlan.Maximal.tsum_int_eq_tsum_sub_add_tsum_add

namespace Work.BourgainPlan.Maximal

/-- **The one-sided quadratic tail at scale `c ≥ 1`.**  `Σ_{n ≥ 0} 1/(c+n)² ≤ 2/c`, with the
summability, derived from the termwise bound `1/(c+n+1)² ≤ 1/(c+n) - 1/(c+n+1)`. -/
lemma summable_one_div_sq_add_nat {c : ℝ} (hc : 1 ≤ c) :
    Summable (fun n : ℕ => 1 / (c + (n:ℝ)) ^ 2) ∧
      (∑' n : ℕ, 1 / (c + (n:ℝ)) ^ 2) ≤ 2 / c := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ 1 / (c + (n:ℝ)) ^ 2 := fun n => by positivity
  have htel : ∀ M : ℕ, ∑ i ∈ Finset.range M, (1 / (c + (i:ℝ)) - 1 / (c + ((i:ℝ) + 1)))
      = 1 / c - 1 / (c + (M:ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hterm : ∀ i : ℕ, (1:ℝ) / (c + ((i + 1 : ℕ) : ℝ)) ^ 2
      ≤ 1 / (c + (i:ℝ)) - 1 / (c + ((i:ℝ) + 1)) := by
    intro i
    push_cast
    have hflat : 1 / (c + (i:ℝ)) - 1 / (c + ((i:ℝ) + 1))
        = 1 / ((c + (i:ℝ)) * (c + ((i:ℝ) + 1))) := by field_simp; ring
    rw [hflat]
    apply one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hkey : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1:ℝ) / (c + (i:ℝ)) ^ 2 ≤ 2 / c := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      rw [Finset.sum_range_succ']
      have hzero : (1:ℝ) / (c + ((0:ℕ):ℝ)) ^ 2 = 1 / c ^ 2 := by norm_num
      rw [hzero]
      have hsum_le : ∑ i ∈ Finset.range M, (1:ℝ) / (c + ((i + 1 : ℕ) : ℝ)) ^ 2
          ≤ 1 / c - 1 / (c + (M:ℝ)) := by
        calc ∑ i ∈ Finset.range M, (1:ℝ) / (c + ((i + 1 : ℕ) : ℝ)) ^ 2
            ≤ ∑ i ∈ Finset.range M, (1 / (c + (i:ℝ)) - 1 / (c + ((i:ℝ) + 1))) :=
              Finset.sum_le_sum (fun i _ => hterm i)
          _ = 1 / c - 1 / (c + (M:ℝ)) := htel M
      have hsq : 1 / c ^ 2 ≤ 1 / c := by
        have hle : c ≤ c ^ 2 := by nlinarith
        exact one_div_le_one_div_of_le hc0 hle
      have hpos : 0 ≤ 1 / (c + (M:ℝ)) := by positivity
      have h4 : (1:ℝ) / c - 1 / (c + (M:ℝ)) + 1 / c ≤ 2 / c := by
        have e : (1:ℝ) / c - 1 / (c + (M:ℝ)) + 1 / c = 2 / c - 1 / (c + (M:ℝ)) := by ring
        rw [e]; linarith
      calc ∑ i ∈ Finset.range M, (1:ℝ) / (c + ((i + 1 : ℕ) : ℝ)) ^ 2 + 1 / c ^ 2
          ≤ (1 / c - 1 / (c + (M:ℝ))) + 1 / c := by linarith
        _ ≤ 2 / c := h4
  exact ⟨summable_of_sum_range_le hnonneg hkey, Real.tsum_le_of_sum_range_le hnonneg hkey⟩

/-- **The shifted-lattice quadratic sum.**  For `c ≥ 1` and any shift `s`, the mass of the quadratic
kernel `x ↦ 1/(c+|x|)²` on the shifted lattice `ℤ + s` is `O(1/c)`:

`Σ_{m ∈ ℤ} 1/(c + |m+s|)² ≤ 4/c`.

The lattice is split at `⌈-s⌉`; on the upper ray `|m+s| ≥ m - ⌈-s⌉` and on the lower ray
`|m+s| ≥ ⌈-s⌉ - 1 - m`, so each side is dominated by `Σ_{n≥0} 1/(c+n)² ≤ 2/c`. -/
lemma shifted_lattice_sq_inv_sum {c : ℝ} (hc : 1 ≤ c) (s : ℝ) :
    Summable (fun m : ℤ => 1 / (c + |(m:ℝ) + s|) ^ 2) ∧
      (∑' m : ℤ, 1 / (c + |(m:ℝ) + s|) ^ 2) ≤ 4 / c := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  obtain ⟨hgsum, hgle⟩ := summable_one_div_sq_add_nat hc
  set K : ℤ := ⌈-s⌉ with hK
  set θ : ℝ := (K : ℝ) + s with hθ
  have hθ0 : 0 ≤ θ := by
    have h : -s ≤ ((K : ℤ) : ℝ) := by
      have h' := Int.le_ceil (-s)
      rwa [← hK] at h'
    rw [hθ]; linarith
  have hθ1 : θ < 1 := by
    have h : ((K : ℤ) : ℝ) < -s + 1 := by
      have h' := Int.ceil_lt_add_one (-s)
      rwa [← hK] at h'
    rw [hθ]; linarith
  have hupper : ∀ n : ℕ,
      1 / (c + |(((K + (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2 ≤ 1 / (c + (n:ℝ)) ^ 2 := by
    intro n
    have hcast : (((K + (n:ℤ) : ℤ) : ℝ) + s) = θ + (n:ℝ) := by
      rw [hθ]; push_cast; ring
    rw [hcast, abs_of_nonneg (add_nonneg hθ0 (Nat.cast_nonneg n))]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity)
        (by linarith [hθ0] : c + (n:ℝ) ≤ c + (θ + (n:ℝ))) 2)
  have hlower : ∀ n : ℕ,
      1 / (c + |(((K - 1 - (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2 ≤ 1 / (c + (n:ℝ)) ^ 2 := by
    intro n
    have hcast : (((K - 1 - (n:ℤ) : ℤ) : ℝ) + s) = θ - 1 - (n:ℝ) := by
      rw [hθ]; push_cast; ring
    rw [hcast]
    have hneg : θ - 1 - (n:ℝ) < 0 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    rw [abs_of_neg hneg]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity)
        (by linarith : c + (n:ℝ) ≤ c + -(θ - 1 - (n:ℝ))) 2)
  have hsum_up : Summable (fun n : ℕ => 1 / (c + |(((K + (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hupper hgsum
  have hsum_lo : Summable (fun n : ℕ => 1 / (c + |(((K - 1 - (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlower hgsum
  have hbnd_up : (∑' n : ℕ, 1 / (c + |(((K + (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2) ≤ 2 / c :=
    (Summable.tsum_le_tsum hupper hsum_up hgsum).trans hgle
  have hbnd_lo : (∑' n : ℕ, 1 / (c + |(((K - 1 - (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2) ≤ 2 / c :=
    (Summable.tsum_le_tsum hlower hsum_lo hgsum).trans hgle
  have hsumZ : Summable (fun m : ℤ => 1 / (c + |(m:ℝ) + s|) ^ 2) := by
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
    have hE : Summable (fun x : ℕ ⊕ ℕ => 1 / (c + |((e x : ℤ) : ℝ) + s|) ^ 2) :=
      Summable.sum (fun x : ℕ ⊕ ℕ => 1 / (c + |((e x : ℤ) : ℝ) + s|) ^ 2)
        (by simpa only [Function.comp_def, he_inl] using hsum_lo)
        (by simpa only [Function.comp_def, he_inr] using hsum_up)
    exact (Equiv.summable_iff e).mp hE
  refine ⟨hsumZ, ?_⟩
  have htsum : (∑' m : ℤ, 1 / (c + |(m:ℝ) + s|) ^ 2)
      = (∑' n : ℕ, 1 / (c + |(((K - 1 - (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2)
        + (∑' n : ℕ, 1 / (c + |(((K + (n:ℤ) : ℤ) : ℝ) + s)|) ^ 2) :=
    tsum_int_eq_tsum_sub_add_tsum_add _ K hsum_lo hsum_up
  rw [htsum]
  have h4c : (2:ℝ)/c + 2/c = 4/c := by ring
  rw [← h4c]
  linarith [hbnd_lo, hbnd_up]

/-- **The sampling bound for a quadratically decaying bump transform.**  If
`‖ρ t‖ ≤ A · (1 + |t|)^{−2}` for every `t` (and `A ≥ 0`), then the samples of `ρ` on the shifted
lattice `(ℤ + s)/c` have total mass `O(c)`, uniformly in `c ≥ 1` and `s : ℝ`:

`Σ_{m ∈ ℤ} ‖ρ ((m + s)/c)‖ ≤ K · c`, with `K` depending only on `A`.

Route.  `‖ρ ((m+s)/c)‖ ≤ A (1 + |m+s|/c)^{-2} = A c² / (c + |m+s|)²`, so the whole sum is
`≤ A c² Σ_m (c + |m+s|)^{-2}`.  For every `k ≥ 0` at most two integers `m` satisfy
`|m + s| ∈ [k, k+1)` (each of the two half-open intervals `[k - s, k+1 - s)` and
`(-(k+1) - s, -k - s]` contains at most one integer), so
`Σ_m (c + |m+s|)^{-2} ≤ 2 Σ_{k≥0} (c + k)^{-2} ≤ 2 (1/c² + 1/c) ≤ 4/c` for `c ≥ 1`
(the last `≤` follows from `1/(c+k)² ≤ 1/(c+k-1) - 1/(c+k)` for `k ≥ 1` and telescoping).
Hence the sum is `≤ 4 A c` and `K := 4A + 1` works; summability follows from the same comparison.
(For `c = 1, s = 0` the exact value of `c · Σ_m (c+|m+s|)^{-2}` is `1 + 2(π²/6 − 1) ≈ 2.29 > 2`,
so the `2/c` refinement is *false*; use `4/c`.) -/
theorem profSampling_bound {ρ : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ t : ℝ, ‖ρ t‖ ≤ A * (1 + |t|) ^ (-(2 : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 1 ≤ c → ∀ s : ℝ,
      Summable (fun m : ℤ => ‖ρ ((m + s) / c)‖) ∧
      (∑' m : ℤ, ‖ρ ((m + s) / c)‖) ≤ K * c := by
  refine ⟨4 * A + 1, by linarith, ?_⟩
  intro c hc s
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  obtain ⟨hsum, hbnd⟩ := shifted_lattice_sq_inv_sum hc s
  have hpow : ∀ m : ℤ, (1 + |((m:ℝ) + s)/c|)^(-(2:ℝ)) = c^2 * (1/(c + |(m:ℝ)+s|)^2) := by
    intro m
    rw [Real.rpow_neg (by positivity), Real.rpow_two, abs_div, abs_of_pos hc0]
    have h1 : 1 + |(m:ℝ)+s| / c = (c + |(m:ℝ)+s|) / c := by field_simp
    rw [h1, div_pow, inv_div]
    ring
  have hle : ∀ m : ℤ, ‖ρ ((m + s)/c)‖ ≤ (A * c^2) * (1/(c + |(m:ℝ)+s|)^2) := by
    intro m
    refine (hdec _).trans (le_of_eq ?_)
    rw [hpow m]
    ring
  have hdom : Summable (fun m : ℤ => (A * c^2) * (1/(c + |(m:ℝ)+s|)^2)) := hsum.mul_left _
  have hnonneg : ∀ m : ℤ, (0:ℝ) ≤ ‖ρ ((m + s)/c)‖ := fun m => norm_nonneg _
  refine ⟨Summable.of_nonneg_of_le hnonneg hle hdom, ?_⟩
  calc (∑' m : ℤ, ‖ρ ((m + s)/c)‖)
      ≤ ∑' m : ℤ, (A * c^2) * (1/(c + |(m:ℝ)+s|)^2) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnonneg hle hdom) hdom
    _ = (A * c^2) * (∑' m : ℤ, 1/(c + |(m:ℝ)+s|)^2) := tsum_mul_left
    _ ≤ (A * c^2) * (4 / c) := mul_le_mul_of_nonneg_left hbnd (mul_nonneg hA (sq_nonneg c))
    _ = 4 * A * c := by field_simp
    _ ≤ (4 * A + 1) * c := by nlinarith [hc0]

end Work.BourgainPlan.Maximal
