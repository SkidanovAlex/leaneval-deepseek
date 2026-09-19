import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Commons.Analysis.ExpLog.log_le_two_sqrt

open scoped BigOperators

set_option maxHeartbeats 2000000

namespace Commons.Analysis.ExpLog

/-- `log x ≤ (2/u) * x^(u/2)` for `x ≥ 1` and `0 < u`.

Proof: writing `y = x^(u/2) ≥ 1`, `log x = (2/u)·log(x^(u/2)) = (2/u)·log y ≤ (2/u)·y`
since `log y ≤ y` for `0 ≤ y`. -/
private lemma log_le_two_div_u_mul_rpow {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (2 / u) * x ^ (u / 2) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hu2 : 0 < u / 2 := by positivity
  have hxu : 1 ≤ x ^ (u / 2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx hu2.le
    rwa [Real.one_rpow] at h
  have hlog : Real.log (x ^ (u / 2)) = (u / 2) * Real.log x := Real.log_rpow hxpos (u / 2)
  have hle : Real.log (x ^ (u / 2)) ≤ x ^ (u / 2) :=
    Real.log_le_self (zero_le_one.trans hxu)
  calc
    Real.log x = (2 / u) * Real.log (x ^ (u / 2)) := by
      rw [hlog]
      field_simp [hu.ne']
    _ ≤ (2 / u) * x ^ (u / 2) := by
      exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 / u)

/-- Pointwise majorization of the series terms by a `p`-series term:

`log(n+1) / (n+1)^(1+u) ≤ (2/u) · (n+1)^(-(1+u/2))` for every `n` and `0 < u`. -/
private lemma term_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + u)) ≤
      (2 / u) * ((n + 1 : ℝ) ^ (-(1 + u / 2))) := by
  let m : ℝ := (n + 1 : ℝ)
  have hm1 : 1 ≤ m := by
    dsimp [m]
    norm_num
  have hmpos : 0 < m := by positivity
  have h1 : Real.log m ≤ (2 / u) * m ^ (u / 2) := log_le_two_div_u_mul_rpow hu hm1
  have hmcpos : 0 < m ^ (1 + u) := Real.rpow_pos_of_pos hmpos _
  have hexp : u / 2 - (1 + u) = -(1 + u / 2) := by ring
  calc
    Real.log m / m ^ (1 + u) ≤ ((2 / u) * m ^ (u / 2)) / m ^ (1 + u) := by
      exact div_le_div_of_nonneg_right h1 hmcpos.le
    _ = (2 / u) * (m ^ (u / 2) / m ^ (1 + u)) := by ring
    _ = (2 / u) * m ^ (u / 2 - (1 + u)) := by rw [Real.rpow_sub hmpos]
    _ = (2 / u) * m ^ (-(1 + u / 2)) := by rw [hexp]

/-- The series terms are nonnegative. -/
private lemma term_nonneg {u : ℝ} (n : ℕ) :
    0 ≤ Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + u)) := by
  have hlog : 0 ≤ Real.log (n + 1 : ℝ) := by
    exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ (n + 1 : ℝ))
  have hden : 0 ≤ (n + 1 : ℝ) ^ (1 + u) := by
    exact Real.rpow_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) _
  exact div_nonneg hlog hden

/-- For nonpositive exponent `s`, the map `x ↦ x ^ s` is antitone on `[1, ∞)`. -/
private lemma rpow_antitoneOn_Ici_one {s : ℝ} (hs : s ≤ 0) :
    AntitoneOn (fun x : ℝ => x ^ s) (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx)
  exact Real.rpow_le_rpow_of_nonpos hxpos hxy hs

/-- `x ↦ x ^ s` is nonnegative on `(1, ∞)`. -/
private lemma rpow_nonneg_Ioi (s : ℝ) : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ t ^ s := by
  intro t ht
  exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans ht)) s

/-- `x ↦ x ^ s` is integrable on `(1, ∞)` whenever `s < -1`. -/
private lemma integrableOn_Ioi_rpow_neg_one (s : ℝ) (hs : s < -1) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
  exact integrableOn_Ioi_rpow_of_lt hs (by norm_num : (0 : ℝ) < 1)

/-- **Lagarias' elementary-series bound**: for `0 < u ≤ 1` the series
`∑ log(n+1) / (n+1)^(1+u)` converges and its sum is at most `100 / u²`.

Proof. The term at index `n` is at most `(2/u)·(n+1)^(-(1+u/2))` (from
`log y ≤ y`, so `log(n+1) ≤ (2/u)·(n+1)^(u/2)`).  The comparison series
`(2/u)·∑ (n+1)^(-(1+u/2))` is bounded by the integral test: its tail from `n ≥ 2`
is at most `∫₁^∞ x^(-1-u/2) dx = 2/u`, so the whole comparison series is at most
`(2/u)·(1 + 2/u)`, which is `≤ 100/u²` since `0 < u ≤ 1`. -/
theorem log_nat_add_rpow_div_summable_bound :
    ∀ u : ℝ, 0 < u → u ≤ 1 →
      Summable (fun n : ℕ => Real.log (n + 1) / ((n + 1 : ℝ) ^ (1 + u))) ∧
      (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ (1 + u))) ≤ 100 / u ^ 2 := by
  intro u hu hu1
  let s : ℝ := -(1 + u / 2)
  let g : ℝ → ℝ := fun x : ℝ => x ^ s
  have hs : s < -1 := by
    dsimp [s]
    linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ s) (Set.Ici (1 : ℝ)) :=
    rpow_antitoneOn_Ici_one (s := s) (by linarith)
  have hintg : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ s)
      (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
    integrableOn_Ioi_rpow_neg_one s hs
  have hnn : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ (fun x : ℝ => x ^ s) t := by
    intro t ht
    exact rpow_nonneg_Ioi s t ht
  have hf_sum : Summable (fun n : ℕ => g (n : ℝ)) := by
    have h := AntitoneOn.summable_of_integrableOn_Ioi (f := fun x : ℝ => x ^ s) (N := 1)
      (by simpa using hanti) (by simpa using hintg) (by simpa using hnn)
    simpa [g] using h
  have hf_shift : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℝ)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => g (n : ℝ)) 1).2 hf_sum
    simpa using h
  let S : ℕ → ℝ := fun n : ℕ => g ((n + 1 : ℕ) : ℝ)
  let B : ℕ → ℝ := fun n : ℕ => Real.log (n + 1 : ℝ) / ((n + 1 : ℝ) ^ (1 + u))
  let C : ℕ → ℝ := fun n : ℕ => (2 / u) * g ((n + 1 : ℕ) : ℝ)
  have hC_sum : Summable C := by
    dsimp [C]
    exact Summable.mul_left (2 / u) hf_shift
  have hB_nonneg : ∀ n, 0 ≤ B n := by
    intro n
    simpa [B] using (term_nonneg (u := u) n)
  have hB_le_C : ∀ n, B n ≤ C n := by
    intro n
    have hterm := term_le (u := u) hu n
    have hs_eq : s = -(1 + u / 2) := by dsimp [s]
    have hval : ((n + 1 : ℕ) : ℝ) = (n + 1 : ℝ) := by norm_num
    have hgC : g ((n + 1 : ℕ) : ℝ) = (n + 1 : ℝ) ^ s := by
      dsimp [g]
      rw [hval]
    dsimp [B, C]
    rw [hgC, hs_eq]
    exact hterm
  have hB_sum : Summable B := Summable.of_nonneg_of_le hB_nonneg hB_le_C hC_sum
  have htail0 := AntitoneOn.tsum_comp_add_le_integral (f := g) 1
      (by simpa [g] using hanti) (by simpa [g] using hintg) (by simpa [g] using hnn)
  have htail : (∑' n : ℕ, g ((n + 2 : ℕ) : ℝ)) ≤ ∫ x in Set.Ioi (1 : ℝ), g x := by
    simpa [Nat.add_assoc] using htail0
  have hS_decomp : (∑' n : ℕ, S n) = g (1 : ℝ) + (∑' n : ℕ, g ((n + 2 : ℕ) : ℝ)) := by
    have hz := Summable.tsum_eq_zero_add (f := fun n : ℕ => g ((n + 1 : ℕ) : ℝ)) hf_shift
    simpa [S, Nat.cast_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
  have hint_val : (∫ x in Set.Ioi (1 : ℝ), g x) = 2 / u := by
    have hiv := integral_Ioi_rpow_of_lt (a := s) hs (c := 1) (by norm_num : (0 : ℝ) < 1)
    dsimp [g]
    rw [hiv]
    rw [Real.one_rpow]
    dsimp [s]
    field_simp [hu.ne']
    ring
  have hg1 : g (1 : ℝ) = 1 := by
    dsimp [g]
    rw [Real.one_rpow]
  have hS_bound : (∑' n : ℕ, S n) ≤ 1 + 2 / u := by
    calc
      (∑' n : ℕ, S n) = g (1 : ℝ) + (∑' n : ℕ, g ((n + 2 : ℕ) : ℝ)) := hS_decomp
      _ ≤ 1 + (∫ x in Set.Ioi (1 : ℝ), g x) := by
        rw [hg1]
        exact add_le_add le_rfl htail
      _ = 1 + 2 / u := by rw [hint_val]
  have hB_tsum : (∑' n : ℕ, B n) ≤ (2 / u) * (1 + 2 / u) := by
    calc
      (∑' n : ℕ, B n) ≤ ∑' n : ℕ, C n := Summable.tsum_le_tsum hB_le_C hB_sum hC_sum
      _ = (2 / u) * (∑' n : ℕ, S n) := by
        dsimp [C]
        rw [tsum_mul_left]
      _ ≤ (2 / u) * (1 + 2 / u) := by
        exact mul_le_mul_of_nonneg_left hS_bound (by positivity : 0 ≤ 2 / u)
  constructor
  · simpa [B] using hB_sum
  · calc
      (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ (1 + u))) = ∑' n : ℕ, B n := by
        simp [B]
      _ ≤ (2 / u) * (1 + 2 / u) := hB_tsum
      _ ≤ 100 / u ^ 2 := by
        have h1 : (2 / u) * (1 + 2 / u) ≤ 6 / u ^ 2 := by
          field_simp [hu.ne']
          nlinarith [sq_nonneg (u - 1)]
        have h2 : 6 / u ^ 2 ≤ 100 / u ^ 2 := by
          rw [div_le_div_iff₀ (sq_pos_of_pos hu) (sq_pos_of_pos hu)]
          nlinarith [sq_nonneg u]
        exact le_trans h1 h2

end Commons.Analysis.ExpLog
