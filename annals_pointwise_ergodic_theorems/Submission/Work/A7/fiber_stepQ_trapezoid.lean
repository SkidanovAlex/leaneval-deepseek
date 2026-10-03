import Mathlib
import Submission.Work.A7.trapezoid_progression
import Submission.Work.A7.sum_class_decomp

namespace Work.A7

open MeasureTheory intervalIntegral

/-!
# The "step `q`" trapezoid comparison along a residue-class fibre

For `V : ℝ → ℂ` of class `C²`, integers `K ≤ N`, a step `q > 0`, a residue `a < q` and a
constant `B ≥ 0` bounding `‖V‖` on `[K,N]`, the sum of `V` over the integers of `(K,N]` that are
congruent to `a` modulo `q` differs from `q⁻¹ ∫_K^N V` by at most

`3 * B + (q/8) * ∫_K^N ‖V''‖`.

The proof splits the interval at the first and last elements `n₁ = a + q m₁`, `n₂ = a + q m₂` of
the class (`m₁ = mFirst`, `m₂ = mLast`), applies the trapezoid comparison `trap_progression_step`
on the progression `n₁, n₁+q, …, n₂` (whose Taylor kernel is bounded by `q/8`), and compares
`∫_{n₁}^{n₂} V` with `∫_K^N V` (`hull_step_bound`), the two end pieces `[K,n₁]`, `[n₂,N]` being of
length `≤ q` and `< q` and hence costing at most `2B` after division by `q`.  When the fibre is
empty the whole interval `(K,N]` is shorter than `q`, and the trivial bound `‖∫‖ ≤ B (N-K)`
suffices.
-/

/-! ## Elementary arithmetic of a residue class in an interval -/

/-- If `(K, N]` contains a full block of `q` consecutive integers then it meets the residue class
`a (mod q)`. -/
private theorem fiber_exists_mod_eq (q K N a : ℕ) (hq : 0 < q) (ha : a < q) (hNK : K + q ≤ N) :
    ∃ n : ℕ, K < n ∧ n ≤ N ∧ n % q = a := by
  rcases le_or_gt a K with haK | hKa
  · refine ⟨a + q * ((K - a) / q + 1), ?_, ?_, ?_⟩
    · have hdivK : q * ((K - a) / q) ≤ K - a := Nat.mul_div_le _ _
      have hmulK : q * ((K - a) / q + 1) = q * ((K - a) / q) + q := by
        rw [Nat.mul_add, Nat.mul_one]
      have hltK : K - a < q * ((K - a) / q + 1) := by
        have h := (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self ((K - a) / q))
        rwa [Nat.mul_comm ((K - a) / q + 1) q] at h
      have hsub : a + (K - a) = K := Nat.add_sub_of_le haK
      omega
    · have hdivK : q * ((K - a) / q) ≤ K - a := Nat.mul_div_le _ _
      have hmulK : q * ((K - a) / q + 1) = q * ((K - a) / q) + q := by
        rw [Nat.mul_add, Nat.mul_one]
      have hsub : a + (K - a) = K := Nat.add_sub_of_le haK
      omega
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · refine ⟨a, hKa, by omega, Nat.mod_eq_of_lt ha⟩

/-- The first index of the class `a (mod q)` above `K` gives a point of `(K, K+q]`. -/
theorem mFirst_bounds (q K a : ℕ) (hq : 0 < q) (ha : a < q) :
    (K : ℝ) < (a : ℝ) + (q : ℝ) * (mFirst q K a : ℝ) ∧
      (a : ℝ) + (q : ℝ) * (mFirst q K a : ℝ) ≤ (K : ℝ) + (q : ℝ) := by
  rcases le_or_gt a K with h | h
  · have hM1 : mFirst q K a = ((((K - a) / q : ℕ) : ℤ) + 1) := by simp [mFirst, h]
    rw [hM1]
    simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
    have hdivK : q * ((K - a) / q) ≤ K - a := Nat.mul_div_le _ _
    have hmulK : q * ((K - a) / q + 1) = q * ((K - a) / q) + q := by
      rw [Nat.mul_add, Nat.mul_one]
    have hltK : K - a < q * ((K - a) / q + 1) := by
      have h2 := (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self ((K - a) / q))
      rwa [Nat.mul_comm ((K - a) / q + 1) q] at h2
    have hsub : a + (K - a) = K := Nat.add_sub_of_le h
    have h1 : K < a + q * ((K - a) / q + 1) := by omega
    have h2 : a + q * ((K - a) / q + 1) ≤ K + q := by omega
    have e1 : (a : ℝ) + (q : ℝ) * ((((K - a) / q : ℕ) : ℝ) + 1)
        = ((a + q * ((K - a) / q + 1) : ℕ) : ℝ) := by push_cast; ring
    have ec : (K : ℝ) + (q : ℝ) = ((K + q : ℕ) : ℝ) := by push_cast; ring
    constructor
    · rw [e1]; exact_mod_cast h1
    · rw [e1, ec]; exact_mod_cast h2
  · have hM1 : mFirst q K a = 0 := by simp [mFirst, not_le.mpr h]
    rw [hM1]
    simp only [Int.cast_zero, mul_zero, add_zero]
    constructor
    · exact_mod_cast h
    · exact_mod_cast (show a ≤ K + q by omega)

/-- The last index of the class `a (mod q)` below `N` gives a point of `(N-q, N]`. -/
theorem mLast_bounds (q N a : ℕ) (hq : 0 < q) (haN : a ≤ N) :
    (N : ℝ) - (q : ℝ) < (a : ℝ) + (q : ℝ) * (mLast q N a : ℝ) ∧
      (a : ℝ) + (q : ℝ) * (mLast q N a : ℝ) ≤ (N : ℝ) := by
  have hM2 : mLast q N a = (((N - a) / q : ℕ) : ℤ) := by simp [mLast, haN]
  rw [hM2]
  simp only [Int.cast_natCast]
  have hdivN : q * ((N - a) / q) ≤ N - a := Nat.mul_div_le _ _
  have hmodN : (N - a) % q < q := Nat.mod_lt _ hq
  have hdec : q * ((N - a) / q) + (N - a) % q = N - a := Nat.div_add_mod (N - a) q
  have hNa : (N : ℝ) = (a : ℝ) + ((N - a : ℕ) : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le haN]
  have hsplit : ((N - a : ℕ) : ℝ)
      = (q : ℝ) * (((N - a) / q : ℕ) : ℝ) + (((N - a) % q : ℕ) : ℝ) := by
    have h3 : ((N - a : ℕ) : ℝ) = ((q * ((N - a) / q) + (N - a) % q : ℕ) : ℝ) := by rw [hdec]
    have h4 : ((q * ((N - a) / q) + (N - a) % q : ℕ) : ℝ)
        = (q : ℝ) * (((N - a) / q : ℕ) : ℝ) + (((N - a) % q : ℕ) : ℝ) := by
      push_cast
      ring
    exact h3.trans h4
  have hm : (((N - a) % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hmodN
  have hle : (q : ℝ) * (((N - a) / q : ℕ) : ℝ) ≤ ((N - a : ℕ) : ℝ) := by
    exact_mod_cast hdivN
  constructor
  · linarith [hNa, hsplit, hm]
  · linarith [hNa, hle]

/-! ## Analytic comparison lemmas -/

/-- Monotonicity of `∫ ‖V''‖` in the interval. -/
theorem integral_norm_iteratedDeriv_le (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w)
    {K N : ℕ} {r₁ r₂ : ℝ} (hKr : (K : ℝ) ≤ r₁) (hr : r₁ ≤ r₂) (hrN : r₂ ≤ (N : ℝ)) :
    (∫ t in r₁..r₂, ‖iteratedDeriv 2 w t‖) ≤ ∫ t in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 w t‖ := by
  have hcont : Continuous (fun t : ℝ => ‖iteratedDeriv 2 w t‖) :=
    (hw.continuous_iteratedDeriv 2 (by norm_num)).norm
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (K : ℝ) (N : ℝ))]
      (fun t : ℝ => ‖iteratedDeriv 2 w t‖) :=
    Filter.Eventually.of_forall (fun t => norm_nonneg _)
  exact intervalIntegral.integral_mono_interval hKr hr hrN hae (hcont.intervalIntegrable _ _)

/-- The trapezoid comparison along a `q`-step arithmetic progression with real base point `A`,
with the endpoint values only bounded by `B`. -/
theorem trap_progression_step (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w) (q : ℕ) (hq : 0 < q)
    (A : ℝ) (m₁ m₂ : ℤ) (hm : m₁ ≤ m₂) {B : ℝ}
    (h₁ : ‖w (A + (q : ℝ) * (m₁ : ℝ))‖ ≤ B)
    (h₂ : ‖w (A + (q : ℝ) * (m₂ : ℝ))‖ ≤ B) :
    ‖(∑ m ∈ Finset.Icc m₁ m₂, w (A + (q : ℝ) * (m : ℝ)))
        - ((q : ℝ))⁻¹ * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)), w t‖
      ≤ B + ((q : ℝ) / 8)
          * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
              ‖iteratedDeriv 2 w t‖ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hcomp : ContDiff ℝ 2 (fun t : ℝ => w (A + (q : ℝ) * t)) := hw.comp (by fun_prop)
  have hkey := ModelApproxCore_trapezoid (fun t : ℝ => w (A + (q : ℝ) * t)) hcomp
    (a := m₁) (b := m₂) hm
  have hI1 : (∫ t in (m₁ : ℝ)..(m₂ : ℝ), w (A + (q : ℝ) * t))
      = ((q : ℝ))⁻¹ * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)), w t := by
    rw [integral_comp_affine w (q : ℝ) hq0 A (m₁ : ℝ) (m₂ : ℝ), Complex.real_smul]
  have hI2 : (∫ t in (m₁ : ℝ)..(m₂ : ℝ),
        ‖iteratedDeriv 2 (fun t : ℝ => w (A + (q : ℝ) * t)) t‖)
      = (q : ℝ) * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
          ‖iteratedDeriv 2 w t‖ := by
    have hpt : ∀ t : ℝ, ‖iteratedDeriv 2 (fun s : ℝ => w (A + (q : ℝ) * s)) t‖
        = (q : ℝ) ^ 2 * ‖iteratedDeriv 2 w (A + (q : ℝ) * t)‖ := by
      intro t
      rw [iteratedDeriv_two_comp_affine w hw A (q : ℝ) t, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (q : ℝ))]
    rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul]
    rw [integral_comp_affine (fun x : ℝ => ‖iteratedDeriv 2 w x‖) (q : ℝ) hq0 A (m₁ : ℝ) (m₂ : ℝ)]
    rw [smul_eq_mul]
    field_simp
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hmR : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm
  have hends : (A + (q : ℝ) * (m₁ : ℝ)) ≤ (A + (q : ℝ) * (m₂ : ℝ)) := by
    have : (q : ℝ) * (m₁ : ℝ) ≤ (q : ℝ) * (m₂ : ℝ) := mul_le_mul_of_nonneg_left hmR hqnn
    linarith
  have hI : 0 ≤ ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
      ‖iteratedDeriv 2 w t‖ :=
    intervalIntegral.integral_nonneg hends (fun t _ => norm_nonneg _)
  have hBbind : (1/2) * (‖w (A + (q : ℝ) * (m₁ : ℝ))‖
      + ‖w (A + (q : ℝ) * (m₂ : ℝ))‖) ≤ B := by linarith
  calc ‖(∑ m ∈ Finset.Icc m₁ m₂, w (A + (q : ℝ) * (m : ℝ)))
        - ((q : ℝ))⁻¹ * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)), w t‖
      = ‖(∑ m ∈ Finset.Icc m₁ m₂, w (A + (q : ℝ) * (m : ℝ)))
        - ∫ t in (m₁ : ℝ)..(m₂ : ℝ), w (A + (q : ℝ) * t)‖ := by rw [hI1]
    _ ≤ (1/2) * (‖w (A + (q : ℝ) * (m₁ : ℝ))‖ + ‖w (A + (q : ℝ) * (m₂ : ℝ))‖)
        + (1/8) * ∫ t in (m₁ : ℝ)..(m₂ : ℝ),
            ‖iteratedDeriv 2 (fun t : ℝ => w (A + (q : ℝ) * t)) t‖ := hkey
    _ = (1/2) * (‖w (A + (q : ℝ) * (m₁ : ℝ))‖ + ‖w (A + (q : ℝ) * (m₂ : ℝ))‖)
        + (1/8) * ((q : ℝ) * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
            ‖iteratedDeriv 2 w t‖) := by rw [hI2]
    _ = (1/2) * (‖w (A + (q : ℝ) * (m₁ : ℝ))‖ + ‖w (A + (q : ℝ) * (m₂ : ℝ))‖)
        + ((q : ℝ) / 8) * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
            ‖iteratedDeriv 2 w t‖ := by ring
    _ ≤ B + ((q : ℝ) / 8) * ∫ t in (A + (q : ℝ) * (m₁ : ℝ))..(A + (q : ℝ) * (m₂ : ℝ)),
            ‖iteratedDeriv 2 w t‖ := by linarith [hBbind]

/-- Comparison of the integral over a subinterval `[r₁,r₂] ⊆ [K,N]` with the integral over the
whole `[K,N]`; the two end pieces have length `≤ q` and `< q`. -/
private theorem hull_step_bound (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w) {B : ℝ} (q : ℕ) (K N : ℕ)
    (r₁ r₂ : ℝ) (hB : ∀ t ∈ Set.Icc (K : ℝ) (N : ℝ), ‖w t‖ ≤ B)
    (hKr : (K : ℝ) ≤ r₁) (hr : r₁ ≤ r₂) (hrN : r₂ ≤ (N : ℝ))
    (hr1 : r₁ ≤ (K : ℝ) + (q : ℝ)) (hr2 : (N : ℝ) - (q : ℝ) < r₂) :
    ‖(∫ t in r₁..r₂, w t) - ∫ t in (K : ℝ)..(N : ℝ), w t‖ ≤ 2 * B * (q : ℝ) := by
  have hcont : Continuous w := hw.continuous
  have hInt : ∀ a b : ℝ, IntervalIntegrable w MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hKN' : (K : ℝ) ≤ (N : ℝ) := le_trans hKr (le_trans hr hrN)
  -- `B ≥ 0` is derivable from the bound at the left endpoint
  have hBnn : 0 ≤ B := le_trans (norm_nonneg (w (K : ℝ))) (hB (K : ℝ) ⟨le_refl _, hKN'⟩)
  have hsplit : (∫ t in (K : ℝ)..(N : ℝ), w t)
      = (∫ t in (K : ℝ)..r₁, w t) + (∫ t in r₁..r₂, w t) + (∫ t in r₂..(N : ℝ), w t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (K : ℝ) r₂) (hInt r₂ (N : ℝ)),
        ← intervalIntegral.integral_add_adjacent_intervals (hInt (K : ℝ) r₁) (hInt r₁ r₂)]
  have hdiff : (∫ t in r₁..r₂, w t) - ∫ t in (K : ℝ)..(N : ℝ), w t
      = -((∫ t in (K : ℝ)..r₁, w t) + ∫ t in r₂..(N : ℝ), w t) := by rw [hsplit]; ring
  have hlen1 : r₁ - (K : ℝ) ≤ (q : ℝ) := by linarith
  have hlen2 : (N : ℝ) - r₂ ≤ (q : ℝ) := by linarith
  have hB1 : ‖∫ t in (K : ℝ)..r₁, w t‖ ≤ B * (q : ℝ) := by
    have h1 : ‖∫ t in (K : ℝ)..r₁, w t‖ ≤ B * (r₁ - (K : ℝ)) := by
      have h : ‖∫ t in (K : ℝ)..r₁, w t‖ ≤ B * |r₁ - (K : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (f := w) (a := (K : ℝ)) (b := r₁) (C := B)
          (fun x hx => by
            rw [Set.uIoc_of_le hKr] at hx
            exact hB x ⟨le_of_lt hx.1, le_trans hx.2 (le_trans hr hrN)⟩)
      rwa [abs_of_nonneg (by linarith)] at h
    exact le_trans h1 (mul_le_mul_of_nonneg_left hlen1 hBnn)
  have hB2 : ‖∫ t in r₂..(N : ℝ), w t‖ ≤ B * (q : ℝ) := by
    have h1 : ‖∫ t in r₂..(N : ℝ), w t‖ ≤ B * ((N : ℝ) - r₂) := by
      have h : ‖∫ t in r₂..(N : ℝ), w t‖ ≤ B * |(N : ℝ) - r₂| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (f := w) (a := r₂) (b := (N : ℝ)) (C := B)
          (fun x hx => by
            rw [Set.uIoc_of_le hrN] at hx
            exact hB x ⟨le_trans (le_trans hKr hr) (le_of_lt hx.1), hx.2⟩)
      rwa [abs_of_nonneg (by linarith)] at h
    exact le_trans h1 (mul_le_mul_of_nonneg_left hlen2 hBnn)
  rw [hdiff, norm_neg]
  calc ‖(∫ t in (K : ℝ)..r₁, w t) + ∫ t in r₂..(N : ℝ), w t‖
      ≤ ‖∫ t in (K : ℝ)..r₁, w t‖ + ‖∫ t in r₂..(N : ℝ), w t‖ := norm_add_le _ _
    _ ≤ B * (q : ℝ) + B * (q : ℝ) := add_le_add hB1 hB2
    _ = 2 * B * (q : ℝ) := by ring

/-! ## The main comparison -/

theorem fiber_stepQ_trapezoid (V : ℝ → ℂ) (hV : ContDiff ℝ 2 V) {K N q a : ℕ}
    (hKN : K ≤ N) (hq : 0 < q) (ha : a < q) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ Set.Icc (K : ℝ) (N : ℝ), ‖V u‖ ≤ B) :
    ‖(∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ))
        - (q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u‖
      ≤ 3 * B + (q / 8) * ∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖ := by
  classical
  set F : Finset ℕ := (Finset.Ioc K N).filter (fun n => n % q = a) with hFdef
  have hKN' : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKN
  have hI0 : 0 ≤ ∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖ :=
    intervalIntegral.integral_nonneg hKN' (fun u _ => norm_nonneg _)
  by_cases hFe : F = ∅
  · -- empty fibre: `N - K < q` and the trivial bound suffices
    have hlt : N - K < q := by
      by_contra hcon
      have hNK : K + q ≤ N := by omega
      obtain ⟨n, hnK, hnN, hna⟩ := fiber_exists_mod_eq q K N a hq ha hNK
      have hmem : n ∈ F := by
        rw [hFdef, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hnK, hnN⟩, hna⟩
      rw [hFe] at hmem
      exact absurd hmem (Finset.notMem_empty n)
    have hsum0 : (∑ n ∈ F, V (n : ℝ)) = 0 := by rw [hFe]; simp
    have hInt : ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ ≤ B * ((N : ℝ) - (K : ℝ)) := by
      have h1 : ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ ≤ B * |(N : ℝ) - (K : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (f := V) (a := (K : ℝ)) (b := (N : ℝ))
          (C := B) (fun x hx => by
            rw [Set.uIoc_of_le hKN'] at hx
            exact hB x ⟨le_of_lt hx.1, hx.2⟩)
      rwa [abs_of_nonneg (by linarith)] at h1
    have hNKle : ((N : ℝ) - (K : ℝ)) ≤ (q : ℝ) := by
      have hcast : (N : ℝ) - (K : ℝ) = ((N - K : ℕ) : ℝ) := by rw [Nat.cast_sub hKN]
      rw [hcast]
      exact_mod_cast le_of_lt hlt
    rw [hsum0, zero_sub, norm_neg]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hkey : (q : ℝ)⁻¹ * (B * (q : ℝ)) = B := by field_simp
    calc ‖(q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u‖
        = (q : ℝ)⁻¹ * ‖∫ u in (K : ℝ)..(N : ℝ), V u‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ (q : ℝ)⁻¹ * (B * ((N : ℝ) - (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ ≤ (q : ℝ)⁻¹ * (B * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNKle hB0) (by positivity)
      _ = B := hkey
      _ ≤ 3 * B + (q / 8) * ∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖ := by
          have h3 : 0 ≤ (q / 8) * ∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖ :=
            mul_nonneg (by positivity) hI0
          linarith [hB0, h3]
  · have hne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
    obtain ⟨n₀, hn₀mem⟩ := hne
    have hn₀ : K < n₀ ∧ n₀ ≤ N ∧ n₀ % q = a := by
      rw [hFdef, Finset.mem_filter, Finset.mem_Ioc] at hn₀mem
      exact ⟨hn₀mem.1.1, hn₀mem.1.2, hn₀mem.2⟩
    have haN : a ≤ N := by
      have h1 : n₀ % q ≤ n₀ := Nat.mod_le n₀ q
      have h2 : n₀ ≤ N := hn₀.2.1
      have h3 : a ≤ n₀ := by rw [← hn₀.2.2]; exact h1
      exact le_trans h3 h2
    have hle : mFirst q K a ≤ mLast q N a :=
      le_trans (mFirst_le_div q hq ha hn₀.2.2 hn₀.1)
        (div_le_mLast q hq ha hn₀.2.2 hn₀.2.1)
    have hreindex : (∑ n ∈ F, V (n : ℝ))
        = ∑ m ∈ Finset.Icc (mFirst q K a) (mLast q N a),
            V ((a : ℝ) + (q : ℝ) * (m : ℝ)) := by
      rw [hFdef]
      have h1 := sum_filter_mod_eq_sum_Icc q hq a ha K N (fun z : ℤ => V (z : ℝ))
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h1
      exact h1
    rw [hreindex]
    set m₁ : ℤ := mFirst q K a with hm₁
    set m₂ : ℤ := mLast q N a with hm₂
    set r₁ : ℝ := (a : ℝ) + (q : ℝ) * (m₁ : ℝ) with hr₁def
    set r₂ : ℝ := (a : ℝ) + (q : ℝ) * (m₂ : ℝ) with hr₂def
    have hmb1 := mFirst_bounds q K a hq ha
    have hmb2 := mLast_bounds q N a hq haN
    have hKr1 : (K : ℝ) ≤ r₁ := le_of_lt hmb1.1
    have hr₁₂ : r₁ ≤ r₂ := by
      have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
      have hmR : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hle
      have h := mul_le_mul_of_nonneg_left hmR hqnn
      linarith
    have hr₂N : r₂ ≤ (N : ℝ) := hmb2.2
    have hr₁q : r₁ ≤ (K : ℝ) + (q : ℝ) := hmb1.2
    have hr₂q : (N : ℝ) - (q : ℝ) < r₂ := hmb2.1
    have hBr1 : ‖V r₁‖ ≤ B := hB r₁ ⟨hKr1, le_trans hr₁₂ hr₂N⟩
    have hBr2 : ‖V r₂‖ ≤ B := hB r₂ ⟨le_trans hKr1 hr₁₂, hr₂N⟩
    have hT := trap_progression_step V hV q hq (a : ℝ) m₁ m₂ hle hBr1 hBr2
    have hH := hull_step_bound V hV (B := B) q K N r₁ r₂ hB hKr1 hr₁₂ hr₂N hr₁q hr₂q
    have hmono := integral_norm_iteratedDeriv_le V hV hKr1 hr₁₂ hr₂N
    have hnorm : ‖(q : ℝ)⁻¹ * ((∫ u in r₁..r₂, V u) - ∫ u in (K : ℝ)..(N : ℝ), V u)‖
        = (q : ℝ)⁻¹ * ‖(∫ u in r₁..r₂, V u) - ∫ u in (K : ℝ)..(N : ℝ), V u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hqinv : (q : ℝ)⁻¹ * (2 * B * (q : ℝ)) = 2 * B := by
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      field_simp
    have hdecomp : (∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)))
          - (q : ℝ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u
        = ((∑ m ∈ Finset.Icc m₁ m₂, V ((a : ℝ) + (q : ℝ) * (m : ℝ)))
            - (q : ℝ)⁻¹ * ∫ u in r₁..r₂, V u)
          + (q : ℝ)⁻¹ * ((∫ u in r₁..r₂, V u) - ∫ u in (K : ℝ)..(N : ℝ), V u) := by
      ring
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) ?_
    rw [hnorm]
    refine le_trans (add_le_add hT (mul_le_mul_of_nonneg_left hH (by positivity))) ?_
    rw [hqinv]
    have h3 : (q : ℝ) / 8 * (∫ u in r₁..r₂, ‖iteratedDeriv 2 V u‖)
        ≤ (q / 8) * ∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith [h3]

end Work.A7
