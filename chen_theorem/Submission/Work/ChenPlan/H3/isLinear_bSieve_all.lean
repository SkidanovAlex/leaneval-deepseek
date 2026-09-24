import Mathlib
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.ChenPlan.H3.isLinearRange_bSieve
import Submission.Work.ChenPlan.H3.prod_oddLt_filter_inv_eq
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp

namespace Work.ChenPlan.H3

open Filter
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset Commons.NumberTheory.Chen.ChenEight

/-! ## 0. Monotonicity in the constant `K`

All three conditions (`IsLinear`, `IsLinearRange`, `IsLinearLower`) become *easier* as `K` grows,
so a single constant `max K₁ K₂` can carry them simultaneously. -/

private lemma isLinear_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinear s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinear s z K' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun w hw2 hwz => ?_⟩
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  refine le_trans (h2 w hw2 hwz) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearRange_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearRange s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearRange s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  refine le_trans (h w z' hw2 hwz hz'z) ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz'.le hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

private lemma isLinearLower_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearLower s z K) (hKK : K ≤ K') :
    Submission.ChenPlan.IsLinearLower s z K' := by
  intro w z' hw2 hwz hz'z
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 ≤ Real.log z' := Real.log_nonneg (by linarith)
  refine le_trans ?_ (h w z' hw2 hwz hz'z)
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz' hlogw.le)
  have : K / Real.log w ≤ K' / Real.log w := div_le_div_of_nonneg_right hKK hlogw.le
  linarith

/-! ## 1. Elementary logarithmic estimates -/

/-- `log ⌈z⌉₊ ≤ log z + 1/z`, the price of replacing the real upper limit `z` by its ceiling. -/
private lemma log_ceil_le (z : ℝ) (hz : 0 < z) :
    Real.log (⌈z⌉₊ : ℝ) ≤ Real.log z + 1/z := by
  have h1 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one hz.le
  have h2 : Real.log (⌈z⌉₊ : ℝ) < Real.log (z + 1) :=
    Real.log_lt_log (by exact_mod_cast (Nat.ceil_pos.mpr hz)) h1
  have h3 : Real.log (z + 1) = Real.log z + Real.log (1 + 1/z) := by
    rw [show z + 1 = z * (1 + 1/z) by field_simp, Real.log_mul (ne_of_gt hz) (by positivity)]
  have h4 : Real.log (1 + 1/z) ≤ 1/z := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + 1/z)
    linarith
  linarith

/-! ## 2. The range product identity for `bSieve` -/

/-- For `z' ≤ Y` the odd primes of `oddLt Y` in `[w, z')` are exactly `oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊`. -/
private lemma oddLt_filter_range_eq_sdiff (Y : ℕ) (w z' : ℝ) (hzY : z' ≤ Y) :
    (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z')
      = oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊ := by
  have hmY : ⌈z'⌉₊ ≤ Y := Nat.ceil_le.mpr hzY
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff, Submission.mem_oddLt]
  constructor
  · rintro ⟨⟨hpp, hp3, hpY⟩, hwp, hpz⟩
    exact ⟨⟨hpp, hp3, Nat.lt_ceil.mpr hpz⟩, fun hpn => by
      obtain ⟨-, -, hlt⟩ := hpn
      have : (p:ℝ) < w := Nat.lt_ceil.mp hlt
      linarith⟩
  · rintro ⟨⟨hpp, hp3, hpm⟩, hpn⟩
    exact ⟨⟨hpp, hp3, by omega⟩, by
      by_contra h
      push Not at h
      exact hpn ⟨hpp, hp3, Nat.lt_ceil.mpr h⟩, Nat.lt_ceil.mp hpm⟩

private lemma prod_oddLt_filter_range_inv_eq (Y : ℕ) (w z' : ℝ) (hwz : w < z') (hzY : z' ≤ Y) :
    ∏ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z'), (1 - 1/((p:ℝ)-1))⁻¹
      = VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ := by
  have hnm : ⌈w⌉₊ ≤ ⌈z'⌉₊ := Nat.ceil_mono hwz.le
  have hsub : oddLt ⌈w⌉₊ ⊆ oddLt ⌈z'⌉₊ := oddLt_mono hnm
  rw [oddLt_filter_range_eq_sdiff Y w z' hzY, Finset.prod_inv_distrib]
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - 1/((p:ℝ)-1)))
  have hVw : VsieveOdd ⌈w⌉₊ ≠ 0 := ne_of_gt (VsieveOdd_pos _)
  have hP : (∏ x ∈ oddLt ⌈z'⌉₊ \ oddLt ⌈w⌉₊, (1 - 1/((x:ℝ)-1)))
      = VsieveOdd ⌈z'⌉₊ / VsieveOdd ⌈w⌉₊ := by
    rw [eq_div_iff hVw]
    rw [show (∏ x ∈ oddLt ⌈w⌉₊, (1 - 1/((x:ℝ)-1))) = VsieveOdd ⌈w⌉₊ from rfl,
        show (∏ x ∈ oddLt ⌈z'⌉₊, (1 - 1/((x:ℝ)-1))) = VsieveOdd ⌈z'⌉₊ from rfl] at hsd
    exact hsd
  rw [hP, inv_div]

/-- The range product for `bSieve`: the inverse sieve factors over the odd primes in `[w, z')`
equal `VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊`. -/
private lemma bSieve_prod_range (x M Y : ℕ) (w z' : ℝ) (hwz : w < z') (hzY : z' ≤ Y) :
    ∏ p ∈ (bSieve x M Y).prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p:ℝ) ∧ (p:ℝ) < z'), (1 - (bSieve x M Y).nu p)⁻¹
      = VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ := by
  rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
    Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt,
    ← prod_oddLt_filter_range_inv_eq Y w z' hwz hzY]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  obtain ⟨hpodd, -⟩ := Finset.mem_filter.mp hp
  have hpp : p.Prime := (Finset.mem_filter.mp hpodd).2.1
  rw [show (bSieve x M Y).nu = invTotient from rfl, invTotient_apply,
      Nat.totient_prime hpp, Nat.cast_sub (by have := hpp.two_le; omega : 1 ≤ p)]
  push_cast
  ring

/-! ## 3. The lower half of the sharp two-scale Mertens ratio -/

/-- Relative form of `Vsieve_log_ratio_sharp` at exponent `2`, in the direction needed for
`IsLinearLower`: `VsieveOdd Z · log Z · (1 - c/(log u)²) ≤ VsieveOdd u · log u` for `Y₀ ≤ u ≤ Z`. -/
private lemma vsieveOdd_ratio_sharp_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd Z * Real.log (Z:ℝ) * (1 - c / (Real.log (u:ℝ))^2)
        ≤ VsieveOdd u * Real.log (u:ℝ) := by
  obtain ⟨c, hc, Y₀, h⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp 2 (by norm_num)
  refine ⟨c, hc, Y₀, fun u Z hu huZ => ?_⟩
  have hA : Real.log (u:ℝ) ^ (2:ℝ) = Real.log (u:ℝ) ^ (2:ℕ) := Real.rpow_natCast _ 2
  have h1 : -(c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2)
      ≤ VsieveOdd u * Real.log (u:ℝ) - VsieveOdd Z * Real.log (Z:ℝ) := by
    have h0 := (abs_le.mp (h u Z hu huZ)).1
    simp only [Work.NumberTheory.Chen.APSwitchUpper.Vsieve_eq_VsieveOdd, hA] at h0
    exact h0
  calc VsieveOdd Z * Real.log (Z:ℝ) * (1 - c / (Real.log (u:ℝ))^2)
      = VsieveOdd Z * Real.log (Z:ℝ)
          - c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2 := by ring
    _ ≤ VsieveOdd u * Real.log (u:ℝ) := by linarith

/-! ## 4. `IsLinearLower` for the sieve, given the two Mertens ingredients -/

/-- The lower dimension bound for `bSieve x M Y` at range `Y`, with threshold `T` for the sharp
Mertens ratio and constant `K`.  All hypotheses on `K` are elementary: `K` dominates `log T`, `c`
and `2`. -/
private lemma isLinearLower_bSieve_aux (c : ℝ) (hc : 0 < c)
    (Y₀ T : ℕ) (K : ℝ) (hT4 : 4 ≤ T) (hTY₀ : Y₀ ≤ T)
    (hKlogT : Real.log (T:ℝ) ≤ K) (hKc : c ≤ K) (hK2 : 2 ≤ K)
    (hsharp : ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd Z * Real.log (Z:ℝ) * (1 - c / (Real.log (u:ℝ))^2)
        ≤ VsieveOdd u * Real.log (u:ℝ))
    (x M Y : ℕ) (_hYge : T ≤ Y) :
    Submission.ChenPlan.IsLinearLower (bSieve x M Y) (Y : ℝ) K := by
  intro w z' hw2 hwz hz'z
  have hw2R : (2:ℝ) ≤ w := by exact_mod_cast hw2
  have hwpos : 0 < w := by linarith
  have hz'pos : 0 < z' := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hK2
  rw [bSieve_prod_range x M Y w z' hwz hz'z]
  by_cases hcase : Real.log w ≤ K
  · -- the target factor `1 - K/log w` is nonpositive
    have hKdiv : 1 ≤ K / Real.log w := by
      rw [le_div_iff₀ hlogw]; linarith
    have h1 : (1 : ℝ) - K / Real.log w ≤ 0 := by linarith
    have h2 : (Real.log z' / Real.log w) * (1 - K / Real.log w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlogz'.le hlogw.le) h1
    have h3 : (0:ℝ) ≤ VsieveOdd ⌈w⌉₊ / VsieveOdd ⌈z'⌉₊ :=
      div_nonneg (VsieveOdd_pos _).le (VsieveOdd_pos _).le
    linarith
  · -- sharp regime: `K < log w`
    push Not at hcase
    set u : ℕ := ⌈w⌉₊ with hu
    set Z : ℕ := ⌈z'⌉₊ with hZ
    have huZ : u ≤ Z := by rw [hu, hZ]; exact Nat.ceil_mono hwz.le
    have hlognw : Real.log w ≤ Real.log (u:ℝ) := by
      rw [hu]; exact Real.log_le_log hwpos (Nat.le_ceil w)
    have hKltu : K < Real.log (u:ℝ) := lt_of_lt_of_le hcase hlognw
    have hlogu : 0 < Real.log (u:ℝ) := lt_trans hKpos hKltu
    have hlogZ : 0 < Real.log (Z:ℝ) := by
      rw [hZ]
      exact Real.log_pos (lt_of_lt_of_le (by linarith : (1:ℝ) < z') (Nat.le_ceil z'))
    have hwT : (T:ℝ) < w := by
      have h1 : Real.log (T:ℝ) < Real.log w := lt_of_le_of_lt hKlogT hcase
      exact (Real.log_lt_log_iff (by exact_mod_cast (by omega : 0 < T)) hwpos).mp h1
    have hY₀u : Y₀ ≤ u := by
      rw [hu]
      have h2 : (Y₀:ℝ) ≤ (T:ℝ) := by exact_mod_cast hTY₀
      have h1 : (Y₀:ℝ) < (⌈w⌉₊ : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt h2 hwT) (Nat.le_ceil w)
      have h3 : Y₀ < ⌈w⌉₊ := by exact_mod_cast h1
      omega
    have hsh := hsharp u Z hY₀u huZ
    have hmain : (Real.log (Z:ℝ)/Real.log (u:ℝ)) * (1 - c/(Real.log (u:ℝ))^2)
        ≤ VsieveOdd u / VsieveOdd Z := by
      rw [le_div_iff₀ (VsieveOdd_pos Z)]
      have key : (Real.log (Z:ℝ)/Real.log (u:ℝ)) * (1 - c/(Real.log (u:ℝ))^2) * VsieveOdd Z
          = (VsieveOdd Z * Real.log (Z:ℝ) * (1 - c/(Real.log (u:ℝ))^2))
            / Real.log (u:ℝ) := by
        rw [div_mul_eq_mul_div]
        ring
      rw [key, div_le_iff₀ hlogu]
      exact hsh
    -- numerical comparison of the `K`-factor
    have hnum : (1:ℝ) - K/Real.log w
        ≤ (1 - 1/(w*Real.log w))*(1 - c/(Real.log w)^2) := by
      have h1 : 1/w ≤ 1/4 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4)
        (le_trans (by exact_mod_cast hT4) hwT.le)
      have h2 : c/Real.log w < 1 := by
        rw [div_lt_one hlogw]; linarith
      have hsum : 1/w + c/Real.log w ≤ K := by linarith
      have hsum2 : 1/(w*Real.log w) + c/(Real.log w)^2 ≤ K/Real.log w := by
        rw [le_div_iff₀ hlogw]
        have hkey : (1/(w*Real.log w) + c/(Real.log w)^2) * Real.log w
            = 1/w + c/Real.log w := by field_simp
        rw [hkey]; exact hsum
      have ha0 : 0 ≤ 1/(w*Real.log w) := by positivity
      have hb0 : 0 ≤ c/(Real.log w)^2 := by positivity
      have h2' : 1 - (1/(w*Real.log w) + c/(Real.log w)^2)
          ≤ (1 - 1/(w*Real.log w))*(1 - c/(Real.log w)^2) := by
        nlinarith [mul_nonneg ha0 hb0]
      linarith
    have hZge : Real.log z' ≤ Real.log (Z:ℝ) :=
      Real.log_le_log hz'pos (by rw [hZ]; exact Nat.le_ceil z')
    have hleu : Real.log (u:ℝ) ≤ Real.log w + 1/w := by
      rw [hu]; exact log_ceil_le w hwpos
    have hcbound : 1 - c/(Real.log w)^2 ≤ 1 - c/(Real.log u)^2 := by
      have hh : c/(Real.log (u:ℝ))^2 ≤ c/(Real.log w)^2 :=
        div_le_div_of_nonneg_left hc.le (pow_pos hlogw 2) (by nlinarith [hlognw, hlogw])
      linarith
    have h1mw : 0 ≤ 1 - 1/(w*Real.log w) := by
      rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < w*Real.log w)]
      nlinarith [Real.log_two_gt_d9, hlogw, hw2R]
    have he1 : 0 ≤ 1 - c/(Real.log u)^2 := by
      rw [sub_nonneg, div_le_one (pow_pos hlogu 2)]
      nlinarith [hlogu, hKltu, hKc]
    have hab : 1 - 1/(w*Real.log w) ≤ 1/(1 + 1/(w*Real.log w)) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + 1/(w*Real.log w))]
      nlinarith [sq_nonneg (1/(w*Real.log w))]
    have hratioA : (Real.log z'/Real.log w) * (1 - 1/(w*Real.log w))
        ≤ Real.log (Z:ℝ)/Real.log (u:ℝ) := by
      have hstep1 : (Real.log z'/Real.log w) * (1 - 1/(w*Real.log w))
          ≤ Real.log z'/(Real.log w + 1/w) := by
        rw [show Real.log z'/(Real.log w + 1/w)
            = (Real.log z'/Real.log w) * (1/(1 + 1/(w*Real.log w))) by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          field_simp]
        exact mul_le_mul_of_nonneg_left hab (div_nonneg hlogz'.le hlogw.le)
      have hstep2 : Real.log z'/(Real.log w + 1/w) ≤ Real.log (Z:ℝ)/Real.log (u:ℝ) := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.log w + 1/w) hlogu]
        exact mul_le_mul hZge hleu hlogu.le hlogZ.le
      exact le_trans hstep1 hstep2
    have step1 : (Real.log z'/Real.log w) * (1 - K/Real.log w)
        ≤ (Real.log z'/Real.log w) * ((1 - 1/(w*Real.log w))*(1 - c/(Real.log w)^2)) :=
      mul_le_mul_of_nonneg_left hnum (div_nonneg hlogz'.le hlogw.le)
    have step2 : (Real.log z'/Real.log w) * ((1 - 1/(w*Real.log w))*(1 - c/(Real.log w)^2))
        ≤ (Real.log z'/Real.log w) * ((1 - 1/(w*Real.log w))*(1 - c/(Real.log u)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcbound h1mw)
        (div_nonneg hlogz'.le hlogw.le)
    have step3 : (Real.log z'/Real.log w) * ((1 - 1/(w*Real.log w))*(1 - c/(Real.log u)^2))
        ≤ (Real.log (Z:ℝ)/Real.log (u:ℝ)) * (1 - c/(Real.log (u:ℝ))^2) := by
      rw [show (Real.log z'/Real.log w) * ((1 - 1/(w*Real.log w))*(1 - c/(Real.log u)^2))
          = ((Real.log z'/Real.log w) * (1 - 1/(w*Real.log w))) * (1 - c/(Real.log u)^2) by ring]
      exact mul_le_mul_of_nonneg_right hratioA he1
    exact le_trans step1 (le_trans step2 (le_trans step3 hmain))

/-! ## 5. The theorem -/

theorem isLinear_bSieve_all :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear
          (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K ∧
        Submission.ChenPlan.IsLinearRange
          (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K ∧
        Submission.ChenPlan.IsLinearLower
          (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x))
          (Submission.chenWindowTop x : ℝ) K := by
  obtain ⟨K1, hK1, hEv1⟩ := isLinearRange_bSieve
  obtain ⟨c, hc, Y₀, hsharpLower⟩ := vsieveOdd_ratio_sharp_lower
  set T : ℕ := max Y₀ 4 with hT
  have hT4 : 4 ≤ T := by rw [hT]; exact le_max_right _ _
  have hTY₀ : Y₀ ≤ T := by rw [hT]; exact le_max_left _ _
  set K2 : ℝ := max (Real.log (T:ℝ)) (max c 2) with hK2def
  have hK2logT : Real.log (T:ℝ) ≤ K2 := le_max_left _ _
  have hK2c : c ≤ K2 := le_trans (le_max_left c 2) (le_max_right _ _)
  have hK22 : 2 ≤ K2 := le_trans (le_max_right c 2) (le_max_right _ _)
  refine ⟨max K1 K2, le_trans hK1 (le_max_left _ _), ?_⟩
  have hEv : ∀ᶠ x : ℕ in Filter.atTop, T ≤ Submission.chenWindowTop x := by
    have h1 : ∀ᶠ x : ℕ in Filter.atTop, (T:ℝ) ≤ Real.rpow (x:ℝ) (1/3) :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
        tendsto_natCast_atTop_atTop |>.eventually (Filter.eventually_ge_atTop (T:ℝ))
    filter_upwards [h1] with x hx
    unfold Submission.chenWindowTop
    have : T ≤ ⌊Real.rpow (x:ℝ) (1/3)⌋₊ := Nat.le_floor hx
    omega
  filter_upwards [hEv, hEv1] with x hx hlin
  obtain ⟨hIsLin, hIsLinR⟩ := hlin
  refine ⟨isLinear_mono hIsLin (le_max_left _ _),
          isLinearRange_mono hIsLinR (le_max_left _ _), ?_⟩
  exact isLinearLower_mono
    (isLinearLower_bSieve_aux c hc Y₀ T K2 hT4 hTY₀ hK2logT hK2c hK22 hsharpLower
      x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x) hx)
    (le_max_right _ _)

end

end Work.ChenPlan.H3
