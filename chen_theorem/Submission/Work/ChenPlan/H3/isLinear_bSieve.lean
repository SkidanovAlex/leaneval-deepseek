import Mathlib
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp

/-!
# The `h3` sieve problem is linear

We prove `IsLinear` for the sieve problem `bSieve x M Y` at `M = chenSiftLimitTenth x`,
`Y = chenWindowTop x`: the sifted primes are the odd primes below `Y` and the density is
`ν d = 1/φ(d)`, so the relevant product is

`∏_{w ≤ p < Y} (1 - 1/(p-1))⁻¹ = VsieveOdd ⌈w⌉₊ / VsieveOdd Y`,

which is bounded by `(log Y/log w)(1 + K/log w)` uniformly in `2 ≤ w < Y`:

* for `w` large we use the sharp Mertens ratio
  `VsieveOdd u · log u ≤ VsieveOdd Z · log Z · (1 + c/(log u)^2)` (`u = ⌈w⌉₊`, `Z = Y`),
  a relative form of `Vsieve_log_ratio_sharp` at exponent `2`;
* for the bounded range `w < T` the crude bound `VsieveOdd ⌈w⌉₊/VsieveOdd Y ≤ log Y / cv`
  (Mertens lower bound) is absorbed by taking `K` large.

Everything is uniform in `x`; only `Y = chenWindowTop x → ∞` is used.
-/

namespace Work.ChenPlan.H3

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight

/-! ## 1. Splitting the odd sieve product at a real cut -/

/-- For `w < Y` the odd primes below `Y` that are `≥ w` are exactly the odd primes below `Y`
that are not `< w`; consequently the product of the inverse sieve factors over them is
`VsieveOdd ⌈w⌉₊ / VsieveOdd Y`. -/
private lemma prod_oddLt_filter_inv_eq_aux (Y : ℕ) (w : ℝ) (hw : w < (Y : ℝ)) :
    ∏ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - 1 / ((p:ℝ) - 1))⁻¹
      = VsieveOdd ⌈w⌉₊ / VsieveOdd Y := by
  set n : ℕ := ⌈w⌉₊ with hn
  have hwy : w ≤ (Y:ℝ) := le_of_lt hw
  have hnY : n ≤ Y := by rw [hn]; exact Nat.ceil_le.mpr hwy
  have hcompl : (oddLt Y).filter (fun p : ℕ => ¬ (w ≤ (p : ℝ))) = oddLt n := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpw⟩
      rw [hn]
      simp only [oddLt, Finset.mem_filter, Finset.mem_range] at hp ⊢
      refine ⟨?_, hp.2⟩
      have hlt : (p:ℝ) < w := not_le.mp hpw
      by_contra hcon
      have hcon' : (⌈w⌉₊ : ℕ) ≤ p := by omega
      have : w ≤ (p:ℝ) := le_trans (Nat.le_ceil w) (by exact_mod_cast hcon')
      linarith
    · intro hp
      refine ⟨oddLt_mono hnY hp, ?_⟩
      intro hwp
      have h1 : ⌈w⌉₊ ≤ p := Nat.ceil_le.mpr hwp
      have h2 : p < ⌈w⌉₊ := by
        have h3 : p ∈ Finset.range n := (Finset.mem_filter.mp hp).1
        rw [Finset.mem_range] at h3
        rw [hn] at h3
        exact h3
      omega
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := oddLt Y)
      (p := fun p : ℕ => w ≤ (p:ℝ)) (f := fun p : ℕ => (1 - 1/((p:ℝ)-1)))
  rw [hcompl] at hsplit
  have hVn : VsieveOdd n ≠ 0 := ne_of_gt (VsieveOdd_pos n)
  rw [Finset.prod_inv_distrib]
  have hA : (∏ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - 1/((p:ℝ)-1)))
      = VsieveOdd Y / VsieveOdd n := (eq_div_iff hVn).mpr hsplit
  rw [hA, inv_div]

/-! ## 2. The sharp ratio for `VsieveOdd`, in relative form -/

/-- Relative form of `Vsieve_log_ratio_sharp` for `VsieveOdd` at exponent `2`:
`VsieveOdd u · log u ≤ VsieveOdd Z · log Z · (1 + c/(log u)²)` for `Y₀ ≤ u ≤ Z`. -/
private lemma vsieveOdd_ratio_sharp_aux :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd u * Real.log (u:ℝ) ≤ VsieveOdd Z * Real.log (Z:ℝ) *
        (1 + c / (Real.log (u:ℝ))^2) := by
  obtain ⟨c, hc, Y₀, h⟩ :=
    Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp 2 (by norm_num)
  refine ⟨c, hc, Y₀, fun u Z hu huZ => ?_⟩
  have hA : Real.log (u:ℝ) ^ (2:ℝ) = Real.log (u:ℝ) ^ (2:ℕ) := Real.rpow_natCast _ 2
  have h1 : VsieveOdd u * Real.log (u:ℝ) - VsieveOdd Z * Real.log (Z:ℝ)
      ≤ c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2 := by
    have h0 := (abs_le.mp (h u Z hu huZ)).2
    simp only [Work.NumberTheory.Chen.APSwitchUpper.Vsieve_eq_VsieveOdd, hA] at h0
    exact h0
  calc VsieveOdd u * Real.log (u:ℝ)
      ≤ VsieveOdd Z * Real.log (Z:ℝ)
          + c * (VsieveOdd Z * Real.log (Z:ℝ)) / (Real.log (u:ℝ))^2 :=
        sub_le_iff_le_add'.mp h1
    _ = VsieveOdd Z * Real.log (Z:ℝ) * (1 + c / (Real.log (u:ℝ))^2) := by ring

/-! ## 3. The sieve problem is linear -/

/-- The `IsLinear` condition for `bSieve x M Y` at range `Y`, with constants
`c` (sharp Mertens), `cv` (Mertens lower bound), thresholds `Y₀ ≤ T` and `K`. -/
private lemma isLinear_bSieve_aux (c cv : ℝ) (hc : 0 < c) (hcv : 0 < cv)
    (Y₀ T : ℕ) (K : ℝ) (hT4 : 4 ≤ T) (hTY₀ : Y₀ ≤ T)
    (hK2c : 2*c ≤ K) (hKT : Real.log (T:ℝ) * Real.log (T:ℝ) / cv + 1 ≤ K)
    (hVlow : ∀ Z : ℕ, 4 ≤ Z → cv / Real.log (Z:ℝ) ≤ VsieveOdd Z)
    (hsharp : ∀ u Z : ℕ, Y₀ ≤ u → u ≤ Z →
      VsieveOdd u * Real.log (u:ℝ) ≤ VsieveOdd Z * Real.log (Z:ℝ) *
        (1 + c / (Real.log (u:ℝ))^2))
    (x M Y : ℕ) (hYge : T ≤ Y) :
    Submission.ChenPlan.IsLinear (bSieve x M Y) (Y : ℝ) K := by
  have hKnn : 0 ≤ K := le_trans (by linarith : (0:ℝ) ≤ 2*c) hK2c
  have hY4 : 4 ≤ Y := le_trans hT4 hYge
  have hY1 : 1 < Y := by omega
  have hlogY : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast hY1)
  constructor
  · intro p hp
    have hmem : p ∈ oddLt Y := by
      have h2 : p ∈ (oddPrimLt Y).primeFactors := hp
      rwa [Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt] at h2
    have h3 : p < Y := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
    exact_mod_cast h3
  · intro w hw2 hwz
    set n : ℕ := ⌈w⌉₊ with hn
    have hnY : n ≤ Y := by rw [hn]; exact Nat.ceil_le.mpr (le_of_lt hwz)
    have hsplit : ∏ p ∈ (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - 1/((p:ℝ)-1))⁻¹
        = VsieveOdd n / VsieveOdd Y := by
      rw [hn]; exact prod_oddLt_filter_inv_eq_aux Y w hwz
    have hprod : ∏ p ∈ (bSieve x M Y).prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p:ℝ)), (1 - (bSieve x M Y).nu p)⁻¹
        = VsieveOdd n / VsieveOdd Y := by
      rw [show (bSieve x M Y).prodPrimes = oddPrimLt Y from rfl,
        Work.NumberTheory.Chen.BTermCount.primeFactors_oddPrimLt, ← hsplit]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      obtain ⟨hpodd, -⟩ := Finset.mem_filter.mp hp
      have hpp : p.Prime := (Finset.mem_filter.mp hpodd).2.1
      rw [show (bSieve x M Y).nu = invTotient from rfl, invTotient_apply,
        Nat.totient_prime hpp, Nat.cast_sub (by have := hpp.two_le; omega : 1 ≤ p)]
      push_cast
      ring
    rw [hprod]
    by_cases hwT : w < (T:ℝ)
    · -- bounded range for `w`: crude Mertens bound
      have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
      have hLT : 0 < Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
      have hlogwle : Real.log w ≤ Real.log (T:ℝ) := Real.log_le_log (by linarith) (le_of_lt hwT)
      have hVYpos : 0 < VsieveOdd Y := VsieveOdd_pos Y
      have hVn1 : VsieveOdd n ≤ 1 := VsieveOdd_le_one n
      have hlow := hVlow Y hY4
      have hratio : VsieveOdd n / VsieveOdd Y ≤ Real.log (Y:ℝ) / cv := by
        have h1 : VsieveOdd n / VsieveOdd Y ≤ 1 / VsieveOdd Y := by
          rw [div_le_div_iff_of_pos_right hVYpos]; exact hVn1
        have h2 : 1 / VsieveOdd Y ≤ Real.log (Y:ℝ) / cv := by
          rw [div_le_div_iff₀ hVYpos hcv]
          have h3 : Real.log (Y:ℝ) * (cv / Real.log (Y:ℝ)) = cv := by
            field_simp
          have h4 : cv ≤ Real.log (Y:ℝ) * VsieveOdd Y := by
            have h5 := mul_le_mul_of_nonneg_left hlow hlogY.le
            rwa [h3] at h5
          linarith
        linarith
      have hkey : 1/cv ≤ (1/Real.log w) * (1 + K/Real.log w) := by
        have h1 : 1/Real.log (T:ℝ) ≤ 1/Real.log w :=
          one_div_le_one_div_of_le hlogw hlogwle
        have h2 : 1 + K/Real.log (T:ℝ) ≤ 1 + K/Real.log w := by
          have h3 : K/Real.log (T:ℝ) ≤ K/Real.log w := by
            rw [div_le_div_iff₀ hLT hlogw]
            exact mul_le_mul_of_nonneg_left hlogwle hKnn
          linarith
        have h4 : 1/cv ≤ (1/Real.log (T:ℝ)) * (1 + K/Real.log (T:ℝ)) := by
          have h5 : Real.log (T:ℝ) * Real.log (T:ℝ) / cv ≤ K := by linarith [hKT]
          have h6 : (Real.log (T:ℝ) * Real.log (T:ℝ) / cv) / (Real.log (T:ℝ))^2
              = 1/cv := by
            field_simp
          have h7 : 1/cv ≤ K / (Real.log (T:ℝ))^2 := by
            rw [← h6]
            exact div_le_div_of_nonneg_right h5 (pow_pos hLT 2).le
          have h8 : (1/Real.log (T:ℝ)) * (1 + K/Real.log (T:ℝ))
              = 1/Real.log (T:ℝ) + K/(Real.log (T:ℝ))^2 := by
            field_simp
          have h9 : 0 < (1:ℝ)/Real.log (T:ℝ) := div_pos one_pos hLT
          rw [h8]
          linarith
        calc 1/cv ≤ (1/Real.log (T:ℝ)) * (1 + K/Real.log (T:ℝ)) := h4
          _ ≤ (1/Real.log w) * (1 + K/Real.log w) :=
              mul_le_mul h1 h2 (by linarith [div_nonneg hKnn hLT.le])
                (le_of_lt (div_pos one_pos hlogw))
      have hfinal : Real.log (Y:ℝ)/cv
          ≤ (Real.log (Y:ℝ)/Real.log w) * (1 + K/Real.log w) := by
        have h5 := mul_le_mul_of_nonneg_left hkey hlogY.le
        calc Real.log (Y:ℝ)/cv = Real.log (Y:ℝ) * (1/cv) := by ring
          _ ≤ Real.log (Y:ℝ) * ((1/Real.log w) * (1 + K/Real.log w)) := h5
          _ = (Real.log (Y:ℝ)/Real.log w) * (1 + K/Real.log w) := by ring
      linarith
    · -- `T ≤ w`: the sharp Mertens ratio applies
      rw [not_lt] at hwT
      have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
      have hnge : Y₀ ≤ n := by
        rw [hn]
        have h1 : (Y₀:ℝ) ≤ w := le_trans (by exact_mod_cast hTY₀) hwT
        have h2 : (Y₀:ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans h1 (Nat.le_ceil w)
        exact_mod_cast h2
      have hnpos : 0 < Real.log (n:ℝ) := by
        apply Real.log_pos
        have h1 : (1:ℝ) < (T:ℝ) := by exact_mod_cast (by omega : 1 < T)
        have h2 : (T:ℝ) ≤ (n:ℝ) := le_trans hwT (by rw [hn]; exact Nat.le_ceil w)
        linarith
      have hlognge : Real.log w ≤ Real.log (n:ℝ) :=
        Real.log_le_log (by linarith) (by rw [hn]; exact Nat.le_ceil w)
      have hsh := hsharp n Y hnge hnY
      have hVYpos : 0 < VsieveOdd Y := VsieveOdd_pos Y
      have hln : Real.log (n:ℝ) ≠ 0 := ne_of_gt hnpos
      have hratio : VsieveOdd n / VsieveOdd Y
          ≤ (Real.log (Y:ℝ)/Real.log (n:ℝ)) * (1 + c/(Real.log (n:ℝ))^2) := by
        rw [div_le_iff₀ hVYpos]
        rw [show ((Real.log (Y:ℝ)/Real.log (n:ℝ)) * (1 + c/(Real.log (n:ℝ))^2)) * VsieveOdd Y
            = (VsieveOdd Y * Real.log (Y:ℝ) * (1 + c/(Real.log (n:ℝ))^2))
              / Real.log (n:ℝ) from by
          field_simp]
        rw [le_div_iff₀ hnpos]
        exact hsh
      have hfirst : Real.log (Y:ℝ)/Real.log (n:ℝ) ≤ Real.log (Y:ℝ)/Real.log w :=
        div_le_div_of_nonneg_left hlogY.le hlogw hlognge
      have hsecond : 1 + c/(Real.log (n:ℝ))^2 ≤ 1 + K/Real.log w := by
        have h1 : c/(Real.log (n:ℝ))^2 ≤ c/(Real.log w)^2 :=
          div_le_div_of_nonneg_left hc.le (pow_pos hlogw 2)
            (by nlinarith [hlogw, hlognge])
        have h2 : c/(Real.log w)^2 ≤ K/Real.log w := by
          rw [div_le_div_iff₀ (pow_pos hlogw 2) hlogw]
          have hlog2 : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw2
          have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have h3 : 2*c*Real.log 2 ≤ K * Real.log w :=
            mul_le_mul hK2c hlog2 hlog2pos.le hKnn
          have h5 : c ≤ 2*c*Real.log 2 := by nlinarith [Real.log_two_gt_d9, hc]
          have h6 : c ≤ K * Real.log w := le_trans h5 h3
          nlinarith [h6, hlogw]
        linarith
      calc VsieveOdd n / VsieveOdd Y
          ≤ (Real.log (Y:ℝ)/Real.log (n:ℝ)) * (1 + c/(Real.log (n:ℝ))^2) := hratio
        _ ≤ (Real.log (Y:ℝ)/Real.log w) * (1 + K/Real.log w) :=
            mul_le_mul hfirst hsecond
              (by have := div_pos hc (pow_pos hnpos 2); linarith)
              (div_nonneg hlogY.le hlogw.le)

/-! ## 4. The theorem -/

/-- **The `h3` sieve problem is linear.**  For the sieve `bSieve x M Y` (support `{n - 2 : n ∈ B̄}`,
weights `1`, sifting the odd primes below `Y`, density `ν d = 1/φ(d)`), at
`M = Submission.chenSiftLimitTenth x`, `Y = Submission.chenWindowTop x`, the `IsLinear` condition
holds with the sifting range `z = Y`. -/
theorem isLinear_bSieve :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Submission.ChenPlan.IsLinear
        (Work.ChenPlan.H3.bSieve x (Submission.chenSiftLimitTenth x)
          (Submission.chenWindowTop x))
        (Submission.chenWindowTop x : ℝ) K := by
  obtain ⟨c, hcpos, Y₀, hsharp⟩ := vsieveOdd_ratio_sharp_aux
  obtain ⟨cv, Cv, hcvpos, hCvpos, hVb⟩ := Commons.NumberTheory.Chen.Vsieve_bounds
  have hVlow : ∀ Z : ℕ, 4 ≤ Z → cv / Real.log (Z:ℝ) ≤ VsieveOdd Z := by
    intro Z hZ
    have h := (hVb Z hZ).1
    rwa [Work.NumberTheory.Chen.APSwitchUpper.Vsieve_eq_VsieveOdd] at h
  set T : ℕ := max Y₀ 4 with hT
  have hT4 : 4 ≤ T := by rw [hT]; exact le_max_right _ _
  have hTY₀ : Y₀ ≤ T := by rw [hT]; exact le_max_left _ _
  refine ⟨max (2*c) (Real.log (T:ℝ) * Real.log (T:ℝ) / cv + 1), ?_, ?_⟩
  · exact le_trans (by linarith : (0:ℝ) ≤ 2*c) (le_max_left _ _)
  · have hEv : ∀ᶠ x : ℕ in Filter.atTop, T ≤ Submission.chenWindowTop x := by
      have h1 : ∀ᶠ x : ℕ in Filter.atTop, (T:ℝ) ≤ Real.rpow (x:ℝ) (1/3) :=
        (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp
          tendsto_natCast_atTop_atTop |>.eventually (Filter.eventually_ge_atTop (T:ℝ))
      filter_upwards [h1] with x hx
      unfold Submission.chenWindowTop
      have : T ≤ ⌊Real.rpow (x:ℝ) (1/3)⌋₊ := Nat.le_floor hx
      omega
    filter_upwards [hEv] with x hx
    exact isLinear_bSieve_aux c cv hcpos hcvpos Y₀ T _
      hT4 hTY₀ (le_max_left _ _) (le_max_right _ _) hVlow hsharp
      x (Submission.chenSiftLimitTenth x) (Submission.chenWindowTop x) hx

end

end Work.ChenPlan.H3
