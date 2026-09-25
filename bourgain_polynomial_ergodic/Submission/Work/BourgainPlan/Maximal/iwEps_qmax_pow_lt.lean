import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp
import Submission.Work.BourgainPlan.Maximal.sigmaN_log_bound

namespace Work.BourgainPlan.Maximal

/-- **(Tao's smallness condition on `ε_N`.)** For every `ρ > 0` and `r, k ≥ 1`, for all large `N`
one has `exp(−N^ρ) · 2r · Q^{2rk} < 1/2`, where `Q = ⌈N^{⌊N^{ρ/2}⌋+1}⌉₊`.  This says that the
threshold `ε_N = exp(−N^ρ)` is small enough for the `(r,1/2)`-goodness condition
`ε · 2r · qmax^{2rk} < 1/2` of Tao's `main` whenever `q ≤ qmax = ⌈N^{⌊N^{ρ/2}⌋+1}⌉₊`.

Route (all asymptotic constants are explicit):
write `m = ⌊N^{ρ/2}⌋₊ + 1`.  For `N ≥ 1`, `Q ≤ (N:ℝ)^{m} + 1 ≤ 2(N:ℝ)^{m}` (as `(N:ℝ)^m ≥ 1`),
hence `Q^{2rk} ≤ 2^{2rk} · ((N:ℝ)^m)^{2rk} = 2^{2rk} · (N:ℝ)^{m·2rk} = 2^{2rk}·exp(m·2rk·log N)`.
Since `m ≤ 2N^{ρ/2}` for `N ≥ 1`, and `exists_log_le_rpow (8rk) (ρ/2)` (in
`Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp`) gives
`log N ≤ N^{ρ/2}/(8rk)` for all large `N`, one gets `m·2rk·log N ≤ N^ρ/2`.  Therefore the left side
is at most `2r·2^{2rk}·exp(−N^ρ/2) < 1/2` as soon as `N^ρ > 2·log(4r·2^{2rk})`, which holds for all
large `N` (`Work.BourgainPlan.Maximal.exists_rpow_ge`). -/
lemma iwEps_qmax_pow_lt (ρ : ℝ) (hρ : 0 < ρ) (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      Real.exp (-((N : ℝ) ^ ρ))
        * (2 * (r : ℝ)
          * (((⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (2 * r * k)))
      < 1 / 2 := by
  have hρ2 : 0 < ρ / 2 := by linarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  -- ### the two thresholds
  -- `8 r k log N ≤ N^{ρ/2}` for large `N`
  obtain ⟨Ca, _hCa3, hCa⟩ :=
    Work.BourgainPlan.IonescuWainger.exists_log_le_rpow
      (8 * (r : ℝ) * (k : ℝ)) (ρ / 2) (by positivity) hρ2
  -- abbreviation `E = 2 r k` (this also rewrites the exponent in the goal)
  set E : ℕ := 2 * r * k with hE
  have hEcast : ((E : ℕ) : ℝ) = 2 * (r : ℝ) * (k : ℝ) := by
    rw [hE]; push_cast; ring
  have hE1 : 1 ≤ (2 : ℝ) ^ E := one_le_pow₀ (by norm_num)
  have hcpos : 0 < 4 * (r : ℝ) * (2 : ℝ) ^ E := by positivity
  -- `2 log (4 r 2^{2rk}) + 1 ≤ N^ρ` for large `N`
  obtain ⟨Cb, hCb⟩ :=
    exists_rpow_ge (s := ρ) (B := 2 * Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E) + 1) hρ
      (by
        have h1 : 1 ≤ 4 * (r : ℝ) * (2 : ℝ) ^ E := by nlinarith [hr1, hE1]
        have h2 : 0 ≤ Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E) := Real.log_nonneg h1
        linarith)
  refine ⟨max 3 (max (Nat.ceil Ca) Cb), fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hCaN : Nat.ceil Ca ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hCbN : Cb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNrpow1 : 1 ≤ (N : ℝ) ^ (ρ / 2) := Real.one_le_rpow hN1 hρ2.le
  have hNrpow0 : 0 ≤ (N : ℝ) ^ (ρ / 2) := le_trans zero_le_one hNrpow1
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hCaNr : Ca ≤ (N : ℝ) := by
    have h1 : ((Nat.ceil Ca : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hCaN
    linarith [Nat.le_ceil Ca]
  have haN : 8 * (r : ℝ) * (k : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) ^ (ρ / 2) := hCa N hCaNr
  have hCbNr : (Cb : ℝ) ≤ (N : ℝ) := by exact_mod_cast hCbN
  have hBN : 2 * Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E) + 1 ≤ (N : ℝ) ^ ρ := hCb N hCbNr
  -- ### abbreviations `m` and `Q`
  set m : ℕ := ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 with hm
  set Q : ℕ := ⌈(N : ℝ) ^ (m : ℝ)⌉₊ with hQ
  -- the goal is now `exp (-(N^ρ)) * (2 r * Q^E) < 1/2`
  -- ### `Q ≤ 2 N^m`
  have hm_eq : (m : ℝ) = ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1 := by
    rw [hm]; push_cast; ring
  have hfl : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (ρ / 2) :=
    Nat.floor_le (by positivity)
  have hm_le : (m : ℝ) ≤ 2 * (N : ℝ) ^ (ρ / 2) := by
    rw [hm_eq]; linarith
  have hQceil : (Q : ℝ) < (N : ℝ) ^ (m : ℝ) + 1 := by
    rw [hQ]
    exact Nat.ceil_lt_add_one (by positivity)
  have hNpowm1 : 1 ≤ (N : ℝ) ^ (m : ℝ) := Real.one_le_rpow hN1 (Nat.cast_nonneg m)
  have hQbound : (Q : ℝ) ≤ 2 * (N : ℝ) ^ (m : ℝ) := by linarith
  -- ### `Q^E ≤ 2^E * exp (N^ρ/2)`
  have hQpow : (Q : ℝ) ^ E ≤ (2 : ℝ) ^ E * (N : ℝ) ^ (m * E) := by
    calc (Q : ℝ) ^ E ≤ (2 * (N : ℝ) ^ (m : ℝ)) ^ E :=
          pow_le_pow_left₀ (by positivity) hQbound E
      _ = (2 : ℝ) ^ E * ((N : ℝ) ^ (m : ℝ)) ^ E := by rw [mul_pow]
      _ = (2 : ℝ) ^ E * (N : ℝ) ^ (m * E) := by
            rw [Real.rpow_natCast, ← pow_mul]
  have hexp_bound : ((m * E : ℕ) : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) ^ ρ / 2 := by
    have h4 : 4 * (r : ℝ) * (k : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) ^ (ρ / 2) / 2 := by
      have h := haN
      linarith
    have hsq : (N : ℝ) ^ (ρ / 2) * (N : ℝ) ^ (ρ / 2) = (N : ℝ) ^ ρ := by
      rw [← Real.rpow_add hNpos, show ρ / 2 + ρ / 2 = ρ from by ring]
    calc ((m * E : ℕ) : ℝ) * Real.log (N : ℝ)
        = (m : ℝ) * (2 * (r : ℝ) * (k : ℝ)) * Real.log (N : ℝ) := by
            push_cast [hEcast]; ring
      _ ≤ (2 * (N : ℝ) ^ (ρ / 2)) * (2 * (r : ℝ) * (k : ℝ)) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hm_le (by positivity)) hlogN0
      _ = 2 * ((2 * (r : ℝ) * (k : ℝ)) * Real.log (N : ℝ)) * (N : ℝ) ^ (ρ / 2) := by ring
      _ ≤ ((N : ℝ) ^ (ρ / 2) / 2) * (N : ℝ) ^ (ρ / 2) := by
            apply mul_le_mul_of_nonneg_right _ hNrpow0
            linarith [h4]
      _ = (N : ℝ) ^ ρ / 2 := by rw [← hsq]; ring
  have hexpQ : (N : ℝ) ^ (m * E) = Real.exp (((m * E : ℕ) : ℝ) * Real.log (N : ℝ)) := by
    rw [Real.exp_nat_mul (Real.log (N : ℝ)) (m * E), Real.exp_log hNpos]
  have hQfinal : (Q : ℝ) ^ E ≤ (2 : ℝ) ^ E * Real.exp ((N : ℝ) ^ ρ / 2) := by
    calc (Q : ℝ) ^ E ≤ (2 : ℝ) ^ E * (N : ℝ) ^ (m * E) := hQpow
      _ = (2 : ℝ) ^ E * Real.exp (((m * E : ℕ) : ℝ) * Real.log (N : ℝ)) := by rw [hexpQ]
      _ ≤ (2 : ℝ) ^ E * Real.exp ((N : ℝ) ^ ρ / 2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_bound) (by positivity)
  -- ### assemble
  have key : Real.exp (-((N : ℝ) ^ ρ)) * (2 * (r : ℝ) * (Q : ℝ) ^ E)
      ≤ (2 * (r : ℝ) * (2 : ℝ) ^ E) * Real.exp (-((N : ℝ) ^ ρ / 2)) := by
    have h1 : Real.exp (-((N : ℝ) ^ ρ)) * (2 * (r : ℝ) * (Q : ℝ) ^ E)
        ≤ Real.exp (-((N : ℝ) ^ ρ))
          * (2 * (r : ℝ) * ((2 : ℝ) ^ E * Real.exp ((N : ℝ) ^ ρ / 2))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hQfinal (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [show Real.exp (-((N : ℝ) ^ ρ)) * (2 * (r : ℝ) * ((2 : ℝ) ^ E * Real.exp ((N : ℝ) ^ ρ / 2)))
        = (2 * (r : ℝ) * (2 : ℝ) ^ E)
          * (Real.exp (-((N : ℝ) ^ ρ)) * Real.exp ((N : ℝ) ^ ρ / 2)) from by ring]
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hexplt : Real.exp (-((N : ℝ) ^ ρ / 2)) < 1 / (4 * (r : ℝ) * (2 : ℝ) ^ E) := by
    have hloglt : Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E) < (N : ℝ) ^ ρ / 2 := by linarith
    have hneg : -((N : ℝ) ^ ρ / 2) < -Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E) := by linarith
    calc Real.exp (-((N : ℝ) ^ ρ / 2))
        < Real.exp (-Real.log (4 * (r : ℝ) * (2 : ℝ) ^ E)) := Real.exp_lt_exp.mpr hneg
      _ = 1 / (4 * (r : ℝ) * (2 : ℝ) ^ E) := by
            rw [Real.exp_neg, Real.exp_log hcpos, one_div]
  have hfin : (2 * (r : ℝ) * (2 : ℝ) ^ E) * Real.exp (-((N : ℝ) ^ ρ / 2)) < 1 / 2 := by
    have hpos : 0 < 2 * (r : ℝ) * (2 : ℝ) ^ E := by positivity
    have hstep := mul_lt_mul_of_pos_left hexplt hpos
    have heqc : (2 * (r : ℝ) * (2 : ℝ) ^ E) * (1 / (4 * (r : ℝ) * (2 : ℝ) ^ E)) = 1 / 2 := by
      have hA : (4 * (r : ℝ) * (2 : ℝ) ^ E) ≠ 0 := ne_of_gt hcpos
      field_simp
      ring
    linarith [hstep, heqc]
  exact lt_of_le_of_lt key hfin

end Work.BourgainPlan.Maximal
