import Mathlib
import Submission.Work.Chen.SwitchDefs

/-!
# The sharp `q²`-exceptional mass bound (`sqMass_bound_sharp`)

`Submission.sqMassAll x M` is the `θ`-mass of the primes `p ≤ x` whose shift `p + 2` is
`M`-rough and divisible by the square of a prime `q ≥ M`.  We prove the (weaker than
asymptotically optimal, but still `o(x)`) bound

  `sqMassAll x (chenSiftLimit x) · (log x)² ≤ (1/32) · x`  for all large `x`.

The argument is elementary.  Every `p` counted by `sqMassAll x M` has a witness prime
`q ≥ M` with `q² ∣ p + 2`, and for a fixed `q` there are at most `(x+2)/q²` such `p`.
Hence, with `M = chenSiftLimit x ≈ x^{599/8000}`,

  `sqMassAll x M · (log x)² ≤ (x+2) · (Σ_{q ≥ M} 1/q²) · (log x)³
                             ≤ (x+2) · (2/M) · (log x)³`,

which is `≤ x/32` as soon as `M ≥ 96 log³ x` — true eventually because
`log³ x = o(x^{599/8000})`.
-/

namespace Work.NumberTheory.Chen

open Filter Finset
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

/-- Membership in `Submission.s0Set`: the prime is below `x + 1`. -/
private lemma mem_s0Set_of_mem {x M p : ℕ} (hp : p ∈ Submission.s0Set x M) :
    p < x + 1 ∧ p.Prime := by
  rw [Submission.s0Set] at hp
  obtain ⟨h1, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨h2, h3⟩ := Finset.mem_filter.mp h1
  exact ⟨Finset.mem_range.mp h2, h3⟩

/-- For a prime `q`, the numbers `p < x+1` with `q² ∣ p + 2` number at most `(x+2)/q²`. -/
private lemma card_filter_dvd_shift_le (x q : ℕ) (_hq : 0 < q) :
    ((((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card : ℕ) : ℝ)
      ≤ ((x + 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
  have hcard : ((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card
      ≤ (x + 2) / (q * q) := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div (x + 2) (q * q)]
    refine Finset.card_le_card_of_injOn (fun p => p + 2) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
      exact ⟨⟨by omega, by omega⟩, hp.2⟩
    · intro p _ p' _ h
      exact Nat.add_right_cancel h
  calc ((((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card : ℕ) : ℝ)
      ≤ (((x + 2) / (q * q) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ((x + 2 : ℕ) : ℝ) / ((q * q : ℕ) : ℝ) := Nat.cast_div_le
    _ = ((x + 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        congr 1
        rw [inv_inj]
        push_cast
        ring

/-- `x^{599/8000} ≤ chenSiftLimit x`. -/
private lemma chenSiftLimit_ge_rpow (x : ℕ) :
    (x : ℝ) ^ ((599 : ℝ) / 8000) ≤ (Submission.chenSiftLimit x : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hcut : Commons.NumberTheory.Chen.ChenEight.cut (Real.rpow (x : ℝ) (1 / 8)) 1
      = (x : ℝ) ^ ((599 : ℝ) / 8000) := by
    rw [Commons.NumberTheory.Chen.ChenEight.cut, pow_one,
      show Commons.NumberTheory.Chen.ChenEight.sieveAlpha = (599 : ℝ) / 1000 from rfl,
      show Real.rpow (x : ℝ) (1 / 8) = (x : ℝ) ^ ((1 : ℝ) / 8) from rfl,
      ← Real.rpow_mul hx0]
    congr 1
    ring
  rw [Submission.chenSiftLimit, hcut]
  push_cast
  exact le_of_lt (Nat.lt_floor_add_one _)

/-- Every prime of the shifted set with a `q²`-divisible shift is counted by the union bound. -/
private lemma sqMassAll_le (x M : ℕ) (hM : 1 ≤ M) :
    Submission.sqMassAll x M ≤ (((x : ℝ) + 2) * (2 / (M : ℝ))) * Real.log (x : ℝ) := by
  set S : Finset ℕ := (Submission.s0Set x M).filter
      (fun p => ∃ q : ℕ, q.Prime ∧ M ≤ q ∧ q ^ 2 ∣ p + 2) with hSdef
  set T : Finset ℕ := (Finset.Ioo (M - 1) (x + 3)).filter (fun q => q.Prime) with hTdef
  have hsq : Submission.sqMassAll x M = S.sum (fun p => Real.log (p : ℝ)) := by
    simp only [Submission.sqMassAll, hSdef]
  have hlogx : 0 ≤ Real.log (x : ℝ) := by
    rcases x with _ | x
    · simp
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x + 1))
  have hstep1 : S.sum (fun p => Real.log (p : ℝ)) ≤ (S.card : ℝ) * Real.log (x : ℝ) := by
    calc S.sum (fun p => Real.log (p : ℝ)) ≤ S.sum (fun _ => Real.log (x : ℝ)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          rw [hSdef] at hp
          obtain ⟨hpS, _⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpx, hpp⟩ := mem_s0Set_of_mem hpS
          have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          have hpx' : (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : p ≤ x)
          exact Real.log_le_log hp0 hpx'
      _ = (S.card : ℝ) * Real.log (x : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ ((x : ℝ) + 2) * (2 / (M : ℝ)) := by
    have hsub : S ⊆ T.biUnion (fun q => (Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)) := by
      intro p hp
      rw [hSdef] at hp
      obtain ⟨hpS, q, hqp, hMq, hq2dvd⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpx, _⟩ := mem_s0Set_of_mem hpS
      refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
      · rw [hTdef, Finset.mem_filter, Finset.mem_Ioo]
        have h1 : q ^ 2 ≤ p + 2 := Nat.le_of_dvd (by omega) hq2dvd
        have h2 : q ≤ q ^ 2 := by nlinarith [hqp.two_le]
        have hMlt : M - 1 < q := by omega
        have hqle : q ≤ p + 2 := le_trans h2 h1
        have hqx : q < x + 3 := by omega
        exact ⟨⟨hMlt, hqx⟩, hqp⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hpx, by simpa [pow_two] using hq2dvd⟩
    have h1 : S.card ≤ ∑ q ∈ T, ((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have h2 : (S.card : ℝ) ≤
        ∑ q ∈ T, ((((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : (∑ q ∈ T, ((((Finset.range (x + 1)).filter (fun p => q * q ∣ p + 2)).card : ℕ) : ℝ))
        ≤ ∑ q ∈ T, ((x + 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
      refine Finset.sum_le_sum (fun q hq => ?_)
      rw [hTdef, Finset.mem_filter] at hq
      exact card_filter_dvd_shift_le x q hq.2.pos
    have h4 : (∑ q ∈ T, ((x + 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹)
        ≤ ((x : ℝ) + 2) * (2 / (M : ℝ)) := by
      have hTsub : T ⊆ Finset.Ioo (M - 1) (x + 3) := by
        intro q hq
        rw [hTdef, Finset.mem_filter] at hq
        exact hq.1
      have htail : (∑ q ∈ T, ((q : ℝ) ^ 2)⁻¹) ≤ 2 / (M : ℝ) := by
        calc (∑ q ∈ T, ((q : ℝ) ^ 2)⁻¹)
            ≤ ∑ q ∈ Finset.Ioo (M - 1) (x + 3), ((q : ℝ) ^ 2)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => by positivity)
          _ ≤ 2 / (((M - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (M - 1) (x + 3)
          _ = 2 / (M : ℝ) := by
              have hc : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
                rw [Nat.cast_pred (by omega : 0 < M)]
                ring
              rw [hc]
      calc (∑ q ∈ T, ((x + 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹)
          = ((x + 2 : ℕ) : ℝ) * ∑ q ∈ T, ((q : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ ≤ ((x + 2 : ℕ) : ℝ) * (2 / (M : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
        _ = ((x : ℝ) + 2) * (2 / (M : ℝ)) := by push_cast; ring
    exact le_trans h2 (le_trans h3 h4)
  rw [hsq]
  exact le_trans hstep1 (mul_le_mul_of_nonneg_right hcard hlogx)

/-- `log³ x = o(x^{599/8000})`, so `chenSiftLimit x ≥ 96 log³ x` eventually. -/
private lemma eventually_log_cube_le_chenSiftLimit :
    ∀ᶠ x : ℕ in Filter.atTop,
      (96 : ℝ) * (Real.log (x : ℝ)) ^ 3 ≤ (Submission.chenSiftLimit x : ℝ) := by
  have ho : (fun x : ℝ => (Real.log x) ^ 3) =o[atTop] (fun x : ℝ => x ^ ((599 : ℝ) / 8000)) := by
    have := isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 599 / 8000)
    simpa only [Real.rpow_ofNat] using this
  have hlim : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ ((599 : ℝ) / 8000))
      atTop (𝓝 0) := ho.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ 3 / (n : ℝ) ^ ((599 : ℝ) / 8000) ≤ 1 / 96 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 96))
  filter_upwards [hev, eventually_ge_atTop 2] with x hevx hx2
  have hx2r : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hr : 0 < (x : ℝ) ^ ((599 : ℝ) / 8000) := Real.rpow_pos_of_pos hxpos _
  have hMge : (x : ℝ) ^ ((599 : ℝ) / 8000) ≤ (Submission.chenSiftLimit x : ℝ) :=
    chenSiftLimit_ge_rpow x
  have hMpos : 0 < (Submission.chenSiftLimit x : ℝ) := lt_of_lt_of_le hr hMge
  have hinv : ((Submission.chenSiftLimit x : ℝ))⁻¹ ≤ ((x : ℝ) ^ ((599 : ℝ) / 8000))⁻¹ :=
    inv_anti₀ hr hMge
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hcube0 : 0 ≤ (Real.log (x : ℝ)) ^ 3 := pow_nonneg hlog0 3
  have hL3 : (Real.log (x : ℝ)) ^ 3 / (Submission.chenSiftLimit x : ℝ)
      ≤ (Real.log (x : ℝ)) ^ 3 / (x : ℝ) ^ ((599 : ℝ) / 8000) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hcube0
  have hchain : (Real.log (x : ℝ)) ^ 3 / (Submission.chenSiftLimit x : ℝ) ≤ 1 / 96 :=
    le_trans hL3 hevx
  have hred : (Real.log (x : ℝ)) ^ 3 ≤ (1 / 96) * (Submission.chenSiftLimit x : ℝ) :=
    (div_le_iff₀ hMpos).mp hchain
  calc (96 : ℝ) * (Real.log (x : ℝ)) ^ 3
      ≤ (96 : ℝ) * ((1 / 96) * (Submission.chenSiftLimit x : ℝ)) :=
        mul_le_mul_of_nonneg_left hred (by norm_num)
    _ = (Submission.chenSiftLimit x : ℝ) := by ring

/-- `sqMassAll x (chenSiftLimit x) · (log x)² ≤ (1/32) · x` for all large `x`. -/
theorem sqMass_bound_sharp :
    ∀ᶠ x : ℕ in Filter.atTop,
      Submission.sqMassAll x (Submission.chenSiftLimit x) * (Real.log (x : ℝ)) ^ 2
        ≤ (1 / 32 : ℝ) * (x : ℝ) := by
  filter_upwards [eventually_log_cube_le_chenSiftLimit, eventually_ge_atTop 4] with x hg hx4
  have hx4r : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
  have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hM1 : 1 ≤ Submission.chenSiftLimit x := by
    rw [Submission.chenSiftLimit]; omega
  have hMpos : (0 : ℝ) < (Submission.chenSiftLimit x : ℝ) := by
    exact_mod_cast (by omega : 0 < Submission.chenSiftLimit x)
  have hbase := sqMassAll_le x (Submission.chenSiftLimit x) hM1
  -- The union bound gives a factor `log x`; the remaining `log³ x` is absorbed by `M`.
  have hkey : (2 : ℝ) / (Submission.chenSiftLimit x : ℝ) * (Real.log (x : ℝ)) ^ 3 ≤ 1 / 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
    nlinarith [hg]
  have hstep : (((x : ℝ) + 2) * (2 / (Submission.chenSiftLimit x : ℝ)))
      * (Real.log (x : ℝ)) ^ 3 ≤ (1 / 32 : ℝ) * (x : ℝ) := by
    have h1 : ((x : ℝ) + 2)
        * ((2 / (Submission.chenSiftLimit x : ℝ)) * (Real.log (x : ℝ)) ^ 3)
        ≤ ((x : ℝ) + 2) * (1 / 48) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h2 : ((x : ℝ) + 2) * (1 / 48) ≤ (1 / 32 : ℝ) * (x : ℝ) := by
      have hx2 : (2 : ℝ) ≤ (x : ℝ) := by linarith
      linarith
    calc (((x : ℝ) + 2) * (2 / (Submission.chenSiftLimit x : ℝ)))
        * (Real.log (x : ℝ)) ^ 3
        = ((x : ℝ) + 2)
          * ((2 / (Submission.chenSiftLimit x : ℝ)) * (Real.log (x : ℝ)) ^ 3) := by ring
      _ ≤ ((x : ℝ) + 2) * (1 / 48) := h1
      _ ≤ (1 / 32 : ℝ) * (x : ℝ) := h2
  calc Submission.sqMassAll x (Submission.chenSiftLimit x) * (Real.log (x : ℝ)) ^ 2
      ≤ ((((x : ℝ) + 2) * (2 / (Submission.chenSiftLimit x : ℝ))) * Real.log (x : ℝ))
          * (Real.log (x : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
    _ = (((x : ℝ) + 2) * (2 / (Submission.chenSiftLimit x : ℝ)))
          * (Real.log (x : ℝ)) ^ 3 := by ring
    _ ≤ (1 / 32 : ℝ) * (x : ℝ) := hstep

end Work.NumberTheory.Chen
