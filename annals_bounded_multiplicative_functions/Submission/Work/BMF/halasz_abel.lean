import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.abel_inv_integral_cplx

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

/-!
# The Abel (partial summation) identity for `Mf` and `Kf`

`Mf f x = Σ_{n ≤ ⌊x⌋₊} f n` and `Kf f x = Σ_{n ≤ ⌊x⌋₊} f n log n` are the (left) step
functions attached to the Dirichlet series of `f`.  Since `Mf f` is constant, equal to
`Mf f k`, on the half-open unit interval `[k, k+1)`, the interval integral of
`t ↦ Mf f t / t` over `[k, k+1]` is `Mf f k * (log (k+1) - log k)`.  Summing over `k` by
induction gives the classical Abel identity

`Mf f x * log x - Kf f x = ∫_1^x Mf f t / t dt`   (`x ≥ 1`).
-/

/-- `Mf f` depends on `t` only through `⌊t⌋₊`. -/
lemma Mf_floor (f : ℕ → ℂ) (t : ℝ) : Mf f t = Mf f (⌊t⌋₊ : ℝ) := by
  unfold Mf
  rw [Nat.floor_natCast]

/-- `Kf f` depends on `t` only through `⌊t⌋₊`. -/
lemma Kf_floor (f : ℕ → ℂ) (t : ℝ) : Kf f t = Kf f (⌊t⌋₊ : ℝ) := by
  unfold Kf
  rw [Nat.floor_natCast]

/-- `Mf f (n+1) = Mf f n + f (n+1)` for natural arguments. -/
lemma Mf_nat_succ (f : ℕ → ℂ) (n : ℕ) :
    Mf f ((n + 1 : ℕ) : ℝ) = Mf f (n : ℝ) + f (n + 1) := by
  unfold Mf
  rw [Nat.floor_natCast, Nat.floor_natCast,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- `Kf f (n+1) = Kf f n + f (n+1) log (n+1)` for natural arguments. -/
lemma Kf_nat_succ (f : ℕ → ℂ) (n : ℕ) :
    Kf f ((n + 1 : ℕ) : ℝ) = Kf f (n : ℝ) + f (n + 1) * (Real.log (n + 1) : ℂ) := by
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  unfold Kf
  rw [Nat.floor_natCast, Nat.floor_natCast,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), hcast]

/-- `1 ≤ ⌊x⌋₊` for `x ≥ 1`. -/
lemma one_le_floor {x : ℝ} (hx : 1 ≤ x) : 1 ≤ ⌊x⌋₊ :=
  Nat.le_floor (by exact_mod_cast hx : ((1 : ℕ) : ℝ) ≤ x)

/-- `1 ≤ (⌊x⌋₊ : ℝ)` for `x ≥ 1`. -/
lemma one_le_floor_real {x : ℝ} (hx : 1 ≤ x) : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
  exact_mod_cast one_le_floor hx

/-! ## The complex integral of `1/t` and interval integrability -/

/-- `∫_a^b dt/t = log b - log a` for the `ℂ`-valued integrand, `1 ≤ a, b`. -/
lemma integral_inv_cplx {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in a..b, ((t : ℂ))⁻¹ = (Real.log b : ℂ) - (Real.log a : ℂ) := by
  rw [abel_inv_integral_cplx ha hb]
  push_cast
  ring

/-- `t ↦ (t:ℂ)⁻¹` is interval integrable on `[a,b]` for `1 ≤ a, b`. -/
lemma intervalIntegrable_inv_cplx {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun t : ℝ => ((t : ℂ))⁻¹) volume a b := by
  refine (ContinuousOn.inv₀ (f := fun t : ℝ => (t : ℂ))
    Complex.continuous_ofReal.continuousOn ?_).intervalIntegrable
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by
    rcases Set.mem_uIcc.mp hx with h | h
    · exact le_trans ha h.1
    · exact le_trans hb h.1
  exact Complex.ofReal_ne_zero.mpr (by linarith : x ≠ 0)

/-- Pulling a constant out of `∫_a^b c / t dt`. -/
lemma integral_const_div_cplx (c : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in a..b, c / (t : ℂ) = c * ((Real.log b : ℂ) - (Real.log a : ℂ)) := by
  have h : (∫ t in a..b, c / (t : ℂ)) = c * ∫ t in a..b, ((t : ℂ))⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [div_eq_mul_inv]
  rw [h, integral_inv_cplx ha hb]

/-! ## The unit-interval computation -/

/-- On `[k, k+1]` (`k ≥ 1`) the step function `t ↦ Mf f t / t` integrates to
`Mf f k * (log (k+1) - log k)`. -/
lemma step_value (f : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (k : ℝ)..((k : ℝ) + 1), Mf f t / (t : ℂ) =
      Mf f (k : ℝ) * ((Real.log ((k : ℝ) + 1) : ℂ) - (Real.log (k : ℝ) : ℂ)) := by
  have hcongr : (∫ t in (k : ℝ)..((k : ℝ) + 1), Mf f t / (t : ℂ))
      = ∫ t in (k : ℝ)..((k : ℝ) + 1), Mf f (k : ℝ) / (t : ℂ) := by
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_singleton ((k : ℝ) + 1))
    intro t ht
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    rw [Set.mem_singleton_iff]
    by_contra htne
    have htI : t ∈ Set.Ioc (k : ℝ) ((k : ℝ) + 1) := by
      have h := ht.1
      rwa [Set.uIoc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at h
    rw [Set.mem_Ioc] at htI
    have hfloor : ⌊t⌋₊ = k :=
      Nat.floor_eq_on_Ico k t ⟨le_of_lt htI.1, lt_of_le_of_ne htI.2 htne⟩
    exact ht.2 (by rw [Mf_floor f t, hfloor])
  rw [hcongr, integral_const_div_cplx (Mf f (k : ℝ)) (by exact_mod_cast hk)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))]

/-- On `[k, k+1]` (`k ≥ 1`) the integrand `t ↦ Mf f t / t` is interval integrable. -/
lemma step_integrable (f : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    IntervalIntegrable (fun t : ℝ => Mf f t / (t : ℂ)) volume (k : ℝ) ((k : ℝ) + 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => Mf f (k : ℝ) * ((t : ℂ))⁻¹) volume
      (k : ℝ) ((k : ℝ) + 1) :=
    (intervalIntegrable_inv_cplx (a := (k : ℝ)) (b := (k : ℝ) + 1)
      (by exact_mod_cast hk) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))).const_mul _
  refine h1.congr_uIoo fun t ht => ?_
  rw [Set.uIoo_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1), Set.mem_Ioo] at ht
  have hfloor : ⌊t⌋₊ = k := Nat.floor_eq_on_Ico k t ⟨le_of_lt ht.1, ht.2⟩
  rw [Mf_floor f t, hfloor, div_eq_mul_inv]

/-- The integrand is interval integrable on `[1, n]` (`n ≥ 1`). -/
lemma intervalIntegrable_Mf_div (f : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    IntervalIntegrable (fun t : ℝ => Mf f t / (t : ℂ)) volume (1 : ℝ) (n : ℝ) := by
  have h' : IntervalIntegrable (fun t : ℝ => Mf f t / (t : ℂ)) volume ((1 : ℕ) : ℝ)
      ((n : ℕ) : ℝ) :=
    IntervalIntegrable.trans_iterate_Ico (μ := volume)
      (f := fun t : ℝ => Mf f t / (t : ℂ)) (a := fun j : ℕ => (j : ℝ)) hn
      (fun j hj => by
        have hjc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hjc]
        exact step_integrable f j hj.1)
  simpa using h'

/-! ## The tail piece `[⌊x⌋₊, x]` -/

/-- On `[⌊x⌋₊, x]` (`x ≥ 1`) the step function `t ↦ Mf f t / t` integrates to
`Mf f ⌊x⌋₊ * (log x - log ⌊x⌋₊)`. -/
lemma tail_value (f : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (⌊x⌋₊ : ℝ)..x, Mf f t / (t : ℂ) =
      Mf f (⌊x⌋₊ : ℝ) * ((Real.log x : ℂ) - (Real.log (⌊x⌋₊ : ℝ) : ℂ)) := by
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcongr : (∫ t in (⌊x⌋₊ : ℝ)..x, Mf f t / (t : ℂ))
      = ∫ t in (⌊x⌋₊ : ℝ)..x, Mf f (⌊x⌋₊ : ℝ) / (t : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hNx, Set.mem_Icc] at ht
    have hfloor : ⌊t⌋₊ = ⌊x⌋₊ :=
      Nat.floor_eq_on_Ico ⌊x⌋₊ t ⟨ht.1, lt_of_le_of_lt ht.2 hxlt⟩
    rw [Mf_floor f t, hfloor]
  rw [hcongr, integral_const_div_cplx (Mf f (⌊x⌋₊ : ℝ)) (one_le_floor_real hx) hx]

/-- The integrand is interval integrable on `[⌊x⌋₊, x]` (`x ≥ 1`). -/
lemma Mf_tail_integrable (f : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t : ℝ => Mf f t / (t : ℂ)) volume (⌊x⌋₊ : ℝ) x := by
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h1 : IntervalIntegrable (fun t : ℝ => Mf f (⌊x⌋₊ : ℝ) / (t : ℂ)) volume
      (⌊x⌋₊ : ℝ) x := by
    have h2 : IntervalIntegrable (fun t : ℝ => Mf f (⌊x⌋₊ : ℝ) * ((t : ℂ))⁻¹) volume
        (⌊x⌋₊ : ℝ) x :=
      (intervalIntegrable_inv_cplx (one_le_floor_real hx) hx).const_mul _
    exact h2.congr_uIoo fun t _ => by rw [div_eq_mul_inv]
  refine h1.congr_uIoo fun t ht => ?_
  rw [Set.uIoo_of_le hNx, Set.mem_Ioo] at ht
  have hfloor : ⌊t⌋₊ = ⌊x⌋₊ :=
    Nat.floor_eq_on_Ico ⌊x⌋₊ t ⟨le_of_lt ht.1, lt_trans ht.2 hxlt⟩
  rw [Mf_floor f t, hfloor]

/-! ## The identity at natural arguments, by induction -/

/-- Abel identity at natural arguments: `Mf f n * log n - Kf f n = ∫_1^n Mf f t / t dt`. -/
lemma nat_identity (f : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    Mf f (n : ℝ) * (Real.log n : ℂ) - Kf f (n : ℝ) =
      ∫ t in (1 : ℝ)..(n : ℝ), Mf f t / (t : ℂ) := by
  induction n, hn using Nat.le_induction with
  | base => simp [Mf, Kf, Nat.floor_one, Real.log_one]
  | succ k hk ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hMfs : Mf f ((k : ℝ) + 1) = Mf f (k : ℝ) + f (k + 1) := by
      have h := Mf_nat_succ f k
      rw [hcast] at h
      exact h
    have hKfs : Kf f ((k : ℝ) + 1) =
        Kf f (k : ℝ) + f (k + 1) * (Real.log ((k : ℝ) + 1) : ℂ) := by
      have h := Kf_nat_succ f k
      rw [hcast] at h
      exact h
    rw [hMfs, hKfs]
    have hI1 := intervalIntegrable_Mf_div f k hk
    have hI2 := step_integrable f k hk
    have hsplit : (∫ t in (1 : ℝ)..((k : ℝ) + 1), Mf f t / (t : ℂ))
        = (∫ t in (1 : ℝ)..(k : ℝ), Mf f t / (t : ℂ))
          + ∫ t in (k : ℝ)..((k : ℝ) + 1), Mf f t / (t : ℂ) :=
      (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
    rw [hsplit, ← ih, step_value f k hk]
    ring

/-! ## The Abel identity for real `x ≥ 1` -/

/-- Partial-summation (Abel) identity for `Mf`: for `x ≥ 1`,
`Mf f x * log x - Kf f x = ∫_1^x Mf f t / t dt`. -/
theorem halasz_abel (f : ℕ → ℂ) (x : ℝ) (hx : 1 ≤ x) :
    Work.BMF.Mf f x * Real.log x - Work.BMF.Kf f x = ∫ t in (1 : ℝ)..x, Work.BMF.Mf f t / t := by
  have hN1 : 1 ≤ ⌊x⌋₊ := one_le_floor hx
  have hnat := nat_identity f ⌊x⌋₊ hN1
  have htail := tail_value f hx
  have hI1 := intervalIntegrable_Mf_div f ⌊x⌋₊ hN1
  have hI2 := Mf_tail_integrable f hx
  have hsplit : (∫ t in (1 : ℝ)..x, Mf f t / (t : ℂ))
      = (∫ t in (1 : ℝ)..(⌊x⌋₊ : ℝ), Mf f t / (t : ℂ))
        + ∫ t in (⌊x⌋₊ : ℝ)..x, Mf f t / (t : ℂ) :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  rw [Mf_floor f x, Kf_floor f x, hsplit, ← hnat, htail]
  ring

end Work.BMF
