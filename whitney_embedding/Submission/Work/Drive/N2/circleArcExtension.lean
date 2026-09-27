import Mathlib

noncomputable section

namespace Work.Drive.N2

open scoped ContDiff Topology
open Filter

local notation "Cinf" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 4000000

/-! ## Translate sums -/

/-- The `T`-periodic translate sum of `f`. -/
def caPerSum (T : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℤ, f (x - k * T)

theorem caPerSum_periodic (T : ℝ) (f : ℝ → ℝ) : Function.Periodic (caPerSum T f) T := by
  intro x
  simp only [caPerSum]
  have h := Equiv.tsum_eq (Equiv.addRight (-1 : ℤ)) (fun k : ℤ => f (x - k * T))
  rw [show (fun c : ℤ => f (x - (Equiv.addRight (-1:ℤ)) c * T)) =
      (fun c : ℤ => f (x + T - c*T)) by
    funext c; congr 1; simp [Equiv.addRight]; ring] at h
  exact h

theorem contDiff_caPerSum (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : ContDiff ℝ Cinf f) (hfs : HasCompactSupport f) :
    ContDiff ℝ Cinf (caPerSum T f) := by
  obtain ⟨r, hr⟩ : ∃ r, tsupport f ⊆ Metric.closedBall 0 r :=
    hfs.isBounded.subset_closedBall 0
  have hsupp : ∀ y : ℝ, r < |y| → f y = 0 := by
    intro y hy
    by_contra h
    have h1 : y ∈ Function.support f := Function.mem_support.mpr h
    have h2 := hr (subset_tsupport f h1)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
    exact absurd h2 (not_le.mpr hy)
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (|x₀| + 1 + r)/T < (N:ℝ) := exists_nat_gt _
  have hNT : |x₀| + 1 + r < (N:ℝ) * T := by
    rw [div_lt_iff₀ hT] at hN; linarith
  have hkey : ∀ k : ℤ, (N:ℤ) < |k| → ∀ y ∈ Metric.ball x₀ 1, f (y - k*T) = 0 := by
    intro k hk y hy
    have hy1 : |y| < |x₀| + 1 := by
      have h1 : |y - x₀| < 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hy
        simpa [abs_sub_comm] using hy
      have h2 : |y| - |x₀| ≤ |y - x₀| := abs_sub_abs_le_abs_sub y x₀
      linarith
    apply hsupp
    have hk1 : (N:ℝ) + 1 ≤ |(k:ℝ)| := by
      have h1 : (N:ℤ) + 1 ≤ |k| := by omega
      have h2 : ((N:ℤ) + 1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_abs] at h2
      push_cast at h2
      linarith
    have hkT : (|x₀| + 1 + r) < |(k:ℝ)| * T := by
      have h2 : ((N:ℝ) + 1) * T ≤ |(k:ℝ)| * T :=
        mul_le_mul_of_nonneg_right hk1 (le_of_lt hT)
      have h3 : (N:ℝ) * T < ((N:ℝ) + 1) * T := by linarith
      linarith
    have h3 : |(k:ℝ)| * T - |y| ≤ |y - (k:ℝ)*T| := by
      have h5 : |(k:ℝ) * T| - |y| ≤ |(k:ℝ) * T - y| := abs_sub_abs_le_abs_sub _ _
      have h6 : |(k:ℝ) * T - y| = |y - (k:ℝ) * T| := abs_sub_comm _ _
      have h7 : |(k:ℝ) * T| = |(k:ℝ)| * T := by rw [abs_mul, abs_of_pos hT]
      linarith
    linarith
  have heq : caPerSum T f =ᶠ[nhds x₀]
      (fun x => ∑ k ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f (x - k*T)) := by
    filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ) < 1)] with y hy1
    simp only [caPerSum]
    refine tsum_eq_sum' (s := Finset.Icc (-(N:ℤ)) (N:ℤ)) (fun k hk => ?_)
    refine Finset.mem_Icc.mpr (abs_le.mp ?_)
    by_contra hc
    exact (Function.mem_support.mp hk) (hkey k (not_le.mp hc) y hy1)
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  exact (ContDiff.sum (fun k hk => by fun_prop)).contDiffAt

/-! ## Plateaus and caBumps -/

/-- A smooth caPlat: `1` on `[α+δ, β-δ]` and `0` outside `(α,β)`. -/
def caPlat (α β δ : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - α) / δ) * Real.smoothTransition ((β - x) / δ)

theorem contDiff_caPlat (α β δ : ℝ) : ContDiff ℝ Cinf (caPlat α β δ) := by
  unfold caPlat; fun_prop

theorem caPlat_nonneg (α β δ x : ℝ) : 0 ≤ caPlat α β δ x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem caPlat_le_one (α β δ x : ℝ) : caPlat α β δ x ≤ 1 := by
  have h1 := Real.smoothTransition.le_one ((x - α)/δ)
  have h2 := Real.smoothTransition.nonneg ((x - α)/δ)
  have h3 := Real.smoothTransition.le_one ((β - x)/δ)
  have h4 := Real.smoothTransition.nonneg ((β - x)/δ)
  have h5 : 0 ≤ Real.smoothTransition ((x - α)/δ) * Real.smoothTransition ((β - x)/δ) :=
    mul_nonneg h2 h4
  simp only [caPlat]
  nlinarith

theorem caPlat_eq_one {α β δ x : ℝ} (hδ : 0 < δ) (h1 : α + δ ≤ x) (h2 : x ≤ β - δ) :
    caPlat α β δ x = 1 := by
  have h1' : 1 ≤ (x - α) / δ := by rw [le_div_iff₀ hδ]; linarith
  have h2' : 1 ≤ (β - x) / δ := by rw [le_div_iff₀ hδ]; linarith
  simp [caPlat, Real.smoothTransition.one_of_one_le h1', Real.smoothTransition.one_of_one_le h2']

theorem caPlat_eq_zero_of_le {α β δ x : ℝ} (hδ : 0 < δ) (h : x ≤ α) :
    caPlat α β δ x = 0 := by
  have h1 : (x - α) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)
  simp [caPlat, Real.smoothTransition.zero_of_nonpos h1]

theorem caPlat_eq_zero_of_ge {α β δ x : ℝ} (hδ : 0 < δ) (h : β ≤ x) :
    caPlat α β δ x = 0 := by
  have h1 : (β - x) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)
  simp [caPlat, Real.smoothTransition.zero_of_nonpos h1]

theorem caPlat_pos {α β δ x : ℝ} (hδ : 0 < δ) (h1 : α < x) (h2 : x < β) :
    0 < caPlat α β δ x := by
  have h1' : 0 < (x - α) / δ := div_pos (by linarith) hδ
  have h2' : 0 < (β - x) / δ := div_pos (by linarith) hδ
  exact mul_pos (Real.smoothTransition.pos_of_pos h1') (Real.smoothTransition.pos_of_pos h2')

/-- A smooth caBump: positive on `(α,β)` and zero outside, for `α < β`. -/
def caBump (α β : ℝ) (x : ℝ) : ℝ := caPlat α β ((β - α) / 3) x

theorem contDiff_caBump (α β : ℝ) : ContDiff ℝ Cinf (caBump α β) :=
  contDiff_caPlat α β _

theorem caBump_nonneg (α β x : ℝ) : 0 ≤ caBump α β x := caPlat_nonneg α β _ x

theorem caBump_le_one (α β x : ℝ) : caBump α β x ≤ 1 := caPlat_le_one α β _ x

theorem caBump_pos {α β x : ℝ} (_hαβ : α < β) (h1 : α < x) (h2 : x < β) :
    0 < caBump α β x :=
  caPlat_pos (by linarith) h1 h2

theorem caBump_eq_zero_of_le {α β x : ℝ} (hαβ : α < β) (h : x ≤ α) : caBump α β x = 0 :=
  caPlat_eq_zero_of_le (by linarith) h

theorem caBump_eq_zero_of_ge {α β x : ℝ} (hαβ : α < β) (h : β ≤ x) : caBump α β x = 0 :=
  caPlat_eq_zero_of_ge (by linarith) h

theorem caBump_eq_one {α β x : ℝ} (hαβ : α < β) (h1 : α + (β - α)/3 ≤ x)
    (h2 : x ≤ β - (β - α)/3) : caBump α β x = 1 :=
  caPlat_eq_one (by linarith) h1 h2


theorem caPlat_lt {α β δ x : ℝ} (hδ : 0 < δ) (h : caPlat α β δ x ≠ 0) :
    α < x ∧ x < β := by
  have h1 : Real.smoothTransition ((x - α)/δ) ≠ 0 := fun hc => h (by simp [caPlat, hc])
  have h2 : Real.smoothTransition ((β - x)/δ) ≠ 0 := fun hc => h (by simp [caPlat, hc])
  have h1' : 0 < (x - α)/δ := not_le.mp (fun hh => h1 (Real.smoothTransition.zero_of_nonpos hh))
  have h2' : 0 < (β - x)/δ := not_le.mp (fun hh => h2 (Real.smoothTransition.zero_of_nonpos hh))
  constructor
  · have hh : 0 < (x - α)/δ * δ := mul_pos h1' hδ
    rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at hh
    linarith
  · have hh : 0 < (β - x)/δ * δ := mul_pos h2' hδ
    rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at hh
    linarith

theorem caBump_lt {α β x : ℝ} (hαβ : α < β) (h : caBump α β x ≠ 0) : α < x ∧ x < β :=
  caPlat_lt (by linarith) h

theorem caBump_eq_zero_iff {α β x : ℝ} (hαβ : α < β) : caBump α β x = 0 ↔ x ≤ α ∨ β ≤ x := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd h (ne_of_gt (caBump_pos hαβ hc.1 hc.2))
  · rintro (h | h)
    · exact caBump_eq_zero_of_le hαβ h
    · exact caBump_eq_zero_of_ge hαβ h


theorem caPerSum_eq_zero'' {T s e : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hsupp : ∀ y, f y ≠ 0 → y ∈ Set.Icc s e) (hse : f s = 0) (hee : f e = 0) {x : ℝ}
    (h1 : e ≤ x) (h2 : x ≤ s + T) : caPerSum T f x = 0 := by
  rw [caPerSum]
  have hz : ∀ k : ℤ, f (x - k * T) = 0 := by
    intro k
    rcases le_or_gt k (0:ℤ) with hk | hk
    · have hk1 : (k : ℝ) * T ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk) hT
      have hx1 : e ≤ x - k * T := by linarith
      rcases lt_or_eq_of_le hx1 with h | h
      · by_contra hc
        exact absurd (hsupp _ hc).2 (by linarith)
      · rw [← h]; exact hee
    · have hk1 : T ≤ (k : ℝ) * T := by
        have h3 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
        have := mul_le_mul_of_nonneg_right h3 hT; linarith
      have hx1 : x - k * T ≤ s := by linarith
      rcases lt_or_eq_of_le hx1 with h | h
      · by_contra hc
        exact absurd (hsupp _ hc).1 (by linarith)
      · rw [h]; exact hse
  simp [hz]

theorem caPerSum_eq_self {T s e : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hsupp : ∀ y, f y ≠ 0 → y ∈ Set.Icc s e) {x : ℝ}
    (_h1 : s ≤ x) (_h2 : x ≤ e) (h3 : x - T < s) (h4 : e < x + T) :
    caPerSum T f x = f x := by
  rw [caPerSum]
  rw [tsum_eq_sum' (s := {0}) (fun k hk => ?_)]
  · simp
  · simp only [Finset.mem_coe, Finset.mem_singleton]
    by_contra hk0
    have hmem := hsupp _ (Function.mem_support.mp hk)
    rcases le_or_gt k (0:ℤ) with hk1 | hk1
    · have hk1' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hc : (k : ℝ) * T ≤ -T := by
        have := mul_le_mul_of_nonneg_right hk1' hT; linarith
      linarith [hmem.2]
    · have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
      have hc : T ≤ (k : ℝ) * T := by
        have := mul_le_mul_of_nonneg_right hk1' hT; linarith
      linarith [hmem.1]

theorem caPerSum_eq_shift {T s e : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hsupp : ∀ y, f y ≠ 0 → y ∈ Set.Icc s e) {x : ℝ}
    (_hx1 : s + T ≤ x) (_hx2 : x ≤ e + T) (hx3 : e < x) (hx4 : x < s + 2*T) :
    caPerSum T f x = f (x - T) := by
  rw [caPerSum]
  rw [tsum_eq_sum' (s := {1}) (fun k hk => ?_)]
  · simp
  · simp only [Finset.mem_coe, Finset.mem_singleton]
    by_contra hk1
    have hmem := hsupp _ (Function.mem_support.mp hk)
    rcases lt_or_gt_of_ne hk1 with h | h
    · have hc : (k : ℝ) * T ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (show k ≤ 0 by omega)) hT
      linarith [hmem.2]
    · have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (2:ℤ) ≤ k by omega)
      have hc : 2 * T ≤ (k : ℝ) * T := by
        have := mul_le_mul_of_nonneg_right h2 hT; linarith
      linarith [hmem.1]

theorem caPerSum_eq_zero' {T s e : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hsupp : ∀ y, f y ≠ 0 → y ∈ Set.Icc s e) {x : ℝ}
    (h1 : e < x) (h2 : x < s + T) : caPerSum T f x = 0 := by
  have hz : ∀ k : ℤ, f (x - k * T) = 0 := by
    intro k
    rcases le_or_gt k (0:ℤ) with hk | hk
    · have hc : (k : ℝ) * T ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk) hT
      by_contra hc0
      have hmem := hsupp _ hc0
      linarith [hmem.2]
    · have h2' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
      have hc : T ≤ (k : ℝ) * T := by
        have := mul_le_mul_of_nonneg_right h2' hT; linarith
      by_contra hc0
      have hmem := hsupp _ hc0
      linarith [hmem.1]
  rw [caPerSum]
  rw [tsum_eq_sum' (s := ∅) (fun k hk => ?_)]
  · simp
  · exact absurd (hz k) (Function.mem_support.mp hk)


theorem caIntAdd {f g : ℝ → ℝ} (a b : ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    ∫ x in a..b, (f x + g x) = (∫ x in a..b, f x) + (∫ x in a..b, g x) :=
  intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := a) (b := b) (f := f) (g := g)
    (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)

theorem caIntSplit {f : ℝ → ℝ} (a m b : ℝ) (h : Continuous f) :
    ∫ x in a..b, f x = (∫ x in a..m, f x) + (∫ x in m..b, f x) :=
  (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a := a) (b := m) (c := b) (h.intervalIntegrable a m) (h.intervalIntegrable m b)).symm

/-- Construction of the slope of the extension. -/
theorem exists_quasiPeriodic_slope (a b c d A B C D : ℝ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hdA : d < a + 2 * Real.pi) (_hAB : A < B) (hBC : B < C) (_hCD : C < D)
    (hDA : D < A + 2 * Real.pi) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁sm : ContDiff ℝ Cinf ψ₁) (h₁mono : ∀ x : ℝ, 0 < deriv ψ₁ x)
    (h₂sm : ContDiff ℝ Cinf ψ₂) (h₂mono : ∀ x : ℝ, 0 < deriv ψ₂ x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ Cinf v ∧ (∀ x : ℝ, 0 < v x) ∧
      (∀ x : ℝ, v (x + 2 * Real.pi) = v x) ∧
      (∀ x : ℝ, x ∈ Set.Icc a b → v x = deriv ψ₁ x) ∧
      (∀ x : ℝ, x ∈ Set.Icc c d → v x = deriv ψ₂ x) ∧
      (∫ x in b..c, v x) = C - B ∧
      (∫ x in d..(a + 2 * Real.pi), v x) = A + 2 * Real.pi - D := by
  have hd₁ : ContDiff ℝ Cinf (deriv ψ₁) := (contDiff_infty_iff_deriv.mp h₁sm).2
  have hd₂ : ContDiff ℝ Cinf (deriv ψ₂) := (contDiff_infty_iff_deriv.mp h₂sm).2
  have hd₁c : Continuous (deriv ψ₁) := hd₁.continuous
  have hd₂c : Continuous (deriv ψ₂) := hd₂.continuous
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (a - 1) (d + 1)) hd₁c.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (a - 1) (d + 1)) hd₂c.continuousOn
  set K : ℝ := |C₁| + |C₂| + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKb₁ : ∀ x ∈ Set.Icc (a - 1) (d + 1), |deriv ψ₁ x| ≤ K := by
    intro x hx
    have h := hC₁ x hx
    rw [Real.norm_eq_abs] at h
    have h2 : C₁ ≤ K := by rw [hK]; linarith [le_abs_self C₁, abs_nonneg C₂]
    linarith
  have hKb₂ : ∀ x ∈ Set.Icc (a - 1) (d + 1), |deriv ψ₂ x| ≤ K := by
    intro x hx
    have h := hC₂ x hx
    rw [Real.norm_eq_abs] at h
    have h2 : C₂ ≤ K := by rw [hK]; linarith [le_abs_self C₂, abs_nonneg C₁]
    linarith
  obtain ⟨y₁, _hy₁s, hy₁min⟩ :
      ∃ y ∈ Set.Icc (a - 1) (b + 1), IsMinOn (deriv ψ₁) (Set.Icc (a - 1) (b + 1)) y :=
    isCompact_Icc.exists_isMinOn ⟨a - 1, le_rfl, by linarith⟩ hd₁c.continuousOn
  set m₁ : ℝ := deriv ψ₁ y₁ with hm₁
  have hm₁pos : 0 < m₁ := by rw [hm₁]; exact h₁mono y₁
  have hm₁lo : ∀ x ∈ Set.Icc (a - 1) (b + 1), m₁ ≤ deriv ψ₁ x := by
    intro x hx; rw [hm₁]; exact hy₁min hx
  obtain ⟨y₂, _hy₂s, hy₂min⟩ :
      ∃ y ∈ Set.Icc (c - 1) (d + 1), IsMinOn (deriv ψ₂) (Set.Icc (c - 1) (d + 1)) y :=
    isCompact_Icc.exists_isMinOn ⟨c - 1, le_rfl, by linarith⟩ hd₂c.continuousOn
  set m₂ : ℝ := deriv ψ₂ y₂ with hm₂
  have hm₂pos : 0 < m₂ := by rw [hm₂]; exact h₂mono y₂
  have hm₂lo : ∀ x ∈ Set.Icc (c - 1) (d + 1), m₂ ≤ deriv ψ₂ x := by
    intro x hx; rw [hm₂]; exact hy₂min hx
  -- the small parameter
  have hK1pos : 0 < K + 1 := by linarith
  set s1 : ℝ := min (1/4) ((a + 2*Real.pi - d)/8) with hs1
  set s2 : ℝ := min s1 ((2*Real.pi - (d - a))/4) with hs2
  set s3 : ℝ := min s2 ((2*Real.pi - (d - b))/6) with hs3
  set s4 : ℝ := min s3 ((2*Real.pi - (d - c))/6) with hs4
  set s5 : ℝ := min s4 ((c - b)/8) with hs5
  set s6 : ℝ := min s5 ((C - B)/(1024*(K + 1))) with hs6
  set δ : ℝ := min s6 ((A + 2*Real.pi - D)/(1024*(K + 1))) with hδ
  have hs1pos : 0 < s1 := by rw [hs1]; exact lt_min (by norm_num) (by linarith)
  have hs2pos : 0 < s2 := by rw [hs2]; exact lt_min hs1pos (by linarith)
  have hs3pos : 0 < s3 := by rw [hs3]; exact lt_min hs2pos (by linarith)
  have hs4pos : 0 < s4 := by rw [hs4]; exact lt_min hs3pos (by linarith)
  have hs5pos : 0 < s5 := by rw [hs5]; exact lt_min hs4pos (by linarith)
  have hs6pos : 0 < s6 := by
    rw [hs6]; exact lt_min hs5pos (div_pos (by linarith) (by linarith))
  have hδpos : 0 < δ := by
    rw [hδ]; exact lt_min hs6pos (div_pos (by linarith) (by linarith))
  have hδa1 : δ ≤ 1/4 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ s4 := by rw [hs5]; exact min_le_left _ _
    have h4 : s4 ≤ s3 := by rw [hs4]; exact min_le_left _ _
    have h5 : s3 ≤ s2 := by rw [hs3]; exact min_le_left _ _
    have h6 : s2 ≤ s1 := by rw [hs2]; exact min_le_left _ _
    have h7 : s1 ≤ 1/4 := by rw [hs1]; exact min_le_left _ _
    linarith
  have hδa2 : δ ≤ (a + 2*Real.pi - d)/8 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ s4 := by rw [hs5]; exact min_le_left _ _
    have h4 : s4 ≤ s3 := by rw [hs4]; exact min_le_left _ _
    have h5 : s3 ≤ s2 := by rw [hs3]; exact min_le_left _ _
    have h6 : s2 ≤ s1 := by rw [hs2]; exact min_le_left _ _
    have h7 : s1 ≤ (a + 2*Real.pi - d)/8 := by rw [hs1]; exact min_le_right _ _
    linarith
  have hδa3 : δ ≤ (2*Real.pi - (d - a))/4 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ s4 := by rw [hs5]; exact min_le_left _ _
    have h4 : s4 ≤ s3 := by rw [hs4]; exact min_le_left _ _
    have h5 : s3 ≤ s2 := by rw [hs3]; exact min_le_left _ _
    have h6 : s2 ≤ (2*Real.pi - (d - a))/4 := by rw [hs2]; exact min_le_right _ _
    linarith
  have hδa4 : δ ≤ (2*Real.pi - (d - b))/6 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ s4 := by rw [hs5]; exact min_le_left _ _
    have h4 : s4 ≤ s3 := by rw [hs4]; exact min_le_left _ _
    have h5 : s3 ≤ (2*Real.pi - (d - b))/6 := by rw [hs3]; exact min_le_right _ _
    linarith
  have hδa5 : δ ≤ (2*Real.pi - (d - c))/6 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ s4 := by rw [hs5]; exact min_le_left _ _
    have h4 : s4 ≤ (2*Real.pi - (d - c))/6 := by rw [hs4]; exact min_le_right _ _
    linarith
  have hδa6 : δ ≤ (c - b)/8 := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ s5 := by rw [hs6]; exact min_le_left _ _
    have h3 : s5 ≤ (c - b)/8 := by rw [hs5]; exact min_le_right _ _
    linarith
  have hδa7 : δ ≤ (C - B)/(1024*(K + 1)) := by
    have h1 : δ ≤ s6 := by rw [hδ]; exact min_le_left _ _
    have h2 : s6 ≤ (C - B)/(1024*(K + 1)) := by rw [hs6]; exact min_le_right _ _
    linarith
  have hδa8 : δ ≤ (A + 2*Real.pi - D)/(1024*(K + 1)) := by
    have h1 : δ ≤ (A + 2*Real.pi - D)/(1024*(K + 1)) := by rw [hδ]; exact min_le_right _ _
    exact h1
  have hCBpos : 0 < C - B := by linarith
  have hADpos : 0 < A + 2 * Real.pi - D := by linarith
  have h2δ1 : 2 * δ ≤ 1 := by linarith
  have h2δda : 2 * δ < 2 * Real.pi - (d - a) := by
    have hp : 0 < 2 * Real.pi - (d - a) := by linarith
    linarith [hδa3]
  have h5δda : 5 * δ < 2 * Real.pi - (d - a) := by
    have hp : 0 < 2 * Real.pi - (d - a) := by linarith
    linarith [hδa3]
  have h3δdb : 3 * δ < 2 * Real.pi - (d - b) := by
    have hp : 0 < 2 * Real.pi - (d - b) := by linarith
    linarith [hδa4]
  have h3δdc : 3 * δ < 2 * Real.pi - (d - c) := by
    have hp : 0 < 2 * Real.pi - (d - c) := by linarith
    linarith [hδa5]
  have h2δba : 2 * δ < 2 * Real.pi - (b - a) := by
    have hp : 0 < 2 * Real.pi - (b - a) := by linarith
    linarith [hδa3]
  have h5δad : 5 * δ < a + 2 * Real.pi - d := by
    have hp : 0 < a + 2 * Real.pi - d := by linarith
    linarith [hδa2]
  have h4δcb : 4 * δ < c - b := by
    have hp : 0 < c - b := by linarith
    linarith [hδa6]
  have h4δad : 4 * δ < a + 2 * Real.pi - d := by
    have hp : 0 < a + 2 * Real.pi - d := by linarith
    linarith [hδa2]
  have hδCBK : 8 * δ * K ≤ (C - B)/2 := by
    have h3 : 0 ≤ 8 * K := by linarith [hKpos]
    have h2 : 8 * δ * K ≤ ((C - B)/(1024*(K + 1))) * (8 * K) := by
      calc 8 * δ * K = δ * (8 * K) := by ring
        _ ≤ ((C - B)/(1024*(K + 1))) * (8 * K) := mul_le_mul_of_nonneg_right hδa7 h3
    have h3b : ((C - B)/(1024*(K + 1))) * (8 * K) = (C - B) * (K/(128*(K + 1))) := by
      field_simp <;> ring
    have h4 : K/(128*(K + 1)) ≤ 1/2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 128*(K + 1))]
      linarith
    have h5 : (C - B) * (K/(128*(K + 1))) ≤ (C - B) * (1/2) :=
      mul_le_mul_of_nonneg_left h4 (le_of_lt hCBpos)
    linarith
  have hδADK : 10 * δ * K ≤ A + 2*Real.pi - D := by
    have h3 : 0 ≤ 10 * K := by linarith [hKpos]
    have h2 : 10 * δ * K ≤ ((A + 2*Real.pi - D)/(1024*(K + 1))) * (10 * K) := by
      calc 10 * δ * K = δ * (10 * K) := by ring
        _ ≤ ((A + 2*Real.pi - D)/(1024*(K + 1))) * (10 * K) := mul_le_mul_of_nonneg_right hδa8 h3
    have h3b : ((A + 2*Real.pi - D)/(1024*(K + 1))) * (10 * K)
        = (A + 2*Real.pi - D) * (K/(K + 1)) * (10/1024) := by
      field_simp
    have h4 : K/(K + 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < K + 1)]; linarith
    have h5 : (A + 2*Real.pi - D) * (K/(K + 1)) * (10/1024) ≤ (A + 2*Real.pi - D) * (10/1024) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact mul_le_of_le_one_right (le_of_lt hADpos) h4
    have h6 : (A + 2*Real.pi - D) * (10/1024) ≤ A + 2*Real.pi - D := by nlinarith
    linarith
  clear hδ hs1 hs2 hs3 hs4 hs5 hs6
  -- the constant M
  have hcb_pos : 0 < c - b := by linarith
  have had_pos : 0 < a + 2 * Real.pi - d := by linarith
  set M : ℝ := (min (min m₁ m₂)
    (min ((C - B) / (c - b)) ((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)))) / 2 with hM
  have hMpos : 0 < M := by
    rw [hM]
    apply div_pos _ (by norm_num)
    exact lt_min (lt_min hm₁pos hm₂pos)
      (lt_min (div_pos hCBpos hcb_pos) (div_pos hADpos had_pos))
  have hM₁ : M ≤ m₁ := by
    rw [hM]
    have h : min (min m₁ m₂) (min ((C - B) / (c - b)) ((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)))
        ≤ min m₁ m₂ := min_le_left _ _
    have h2 : min m₁ m₂ ≤ m₁ := min_le_left _ _
    linarith
  have hM₂ : M ≤ m₂ := by
    rw [hM]
    have h : min (min m₁ m₂) (min ((C - B) / (c - b)) ((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)))
        ≤ min m₁ m₂ := min_le_left _ _
    have h2 : min m₁ m₂ ≤ m₂ := min_le_right _ _
    linarith [hm₂pos]
  have hMcb : M * (c - b) ≤ (C - B) / 2 := by
    have h1 : M ≤ ((C - B) / (c - b)) / 2 := by
      rw [hM]
      exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
    have h2 : ((C - B) / (c - b)) / 2 * (c - b) = (C - B) / 2 := by
      field_simp
    calc M * (c - b) ≤ (((C - B) / (c - b)) / 2) * (c - b) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hcb_pos)
      _ = (C - B) / 2 := h2
  have hMad : M * (a + 2 * Real.pi - d) ≤ (A + 2 * Real.pi - D) / 2 := by
    have h1 : M ≤ ((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)) / 2 := by
      rw [hM]
      exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)
    have h2 : ((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)) / 2 * (a + 2 * Real.pi - d) = (A + 2 * Real.pi - D) / 2 := by
      field_simp
    calc M * (a + 2 * Real.pi - d) ≤ (((A + 2 * Real.pi - D) / (a + 2 * Real.pi - d)) / 2) * (a + 2 * Real.pi - d) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt had_pos)
      _ = (A + 2 * Real.pi - D) / 2 := h2
  clear hM
  -- the cutoffs
  have hbc' : b + 2*δ < c - 2*δ := by linarith
  have hdd' : d + 2*δ < d + 3*δ := by linarith
  set χ₁ : ℝ → ℝ := caPlat (a - 2*δ) (b + 2*δ) δ with hχ₁
  set χ₂ : ℝ → ℝ := caPlat (c - 2*δ) (d + 2*δ) δ with hχ₂
  set w₁ : ℝ → ℝ := caBump (b + 2*δ) (c - 2*δ) with hw₁
  set w₂ : ℝ → ℝ := caBump (d + 2*δ) (d + 3*δ) with hw₂
  have hχ₁ne : ∀ x, χ₁ x ≠ 0 → x ∈ Set.Icc (a - 2*δ) (b + 2*δ) := by
    intro x hx
    have h := caPlat_lt hδpos (by rwa [hχ₁] at hx)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hχ₂ne : ∀ x, χ₂ x ≠ 0 → x ∈ Set.Icc (c - 2*δ) (d + 2*δ) := by
    intro x hx
    have h := caPlat_lt hδpos (by rwa [hχ₂] at hx)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hw₁ne : ∀ x, w₁ x ≠ 0 → x ∈ Set.Icc (b + 2*δ) (c - 2*δ) := by
    intro x hx
    have h := caBump_lt hbc' (by rwa [hw₁] at hx)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hw₂ne : ∀ x, w₂ x ≠ 0 → x ∈ Set.Icc (d + 2*δ) (d + 3*δ) := by
    intro x hx
    have h := caBump_lt hdd' (by rwa [hw₂] at hx)
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hχ₁nn : ∀ x, 0 ≤ χ₁ x := by intro x; rw [hχ₁]; exact caPlat_nonneg _ _ _ _
  have hχ₂nn : ∀ x, 0 ≤ χ₂ x := by intro x; rw [hχ₂]; exact caPlat_nonneg _ _ _ _
  have hw₁nn : ∀ x, 0 ≤ w₁ x := by intro x; rw [hw₁]; exact caBump_nonneg _ _ _
  have hw₂nn : ∀ x, 0 ≤ w₂ x := by intro x; rw [hw₂]; exact caBump_nonneg _ _ _
  have hχ₁one : ∀ x ∈ Set.Icc a b, χ₁ x = 1 := by
    intro x hx; rw [hχ₁]
    exact caPlat_eq_one hδpos (by linarith [hx.1]) (by linarith [hx.2])
  have hχ₂one : ∀ x ∈ Set.Icc c d, χ₂ x = 1 := by
    intro x hx; rw [hχ₂]
    exact caPlat_eq_one hδpos (by linarith [hx.1]) (by linarith [hx.2])
  have hχ₁zero : ∀ x, b + 2*δ ≤ x → χ₁ x = 0 := by
    intro x hx; rw [hχ₁]; exact caPlat_eq_zero_of_ge (x := x) hδpos hx
  have hχ₂zerol : ∀ x, x ≤ c - 2*δ → χ₂ x = 0 := by
    intro x hx; rw [hχ₂]; exact caPlat_eq_zero_of_le (x := x) hδpos hx
  have hχ₂zeror : ∀ x, d + 2*δ ≤ x → χ₂ x = 0 := by
    intro x hx; rw [hχ₂]; exact caPlat_eq_zero_of_ge (x := x) hδpos hx
  have hχ₁zerol : ∀ x, x ≤ a - 2*δ → χ₁ x = 0 := by
    intro x hx; rw [hχ₁]; exact caPlat_eq_zero_of_le (x := x) hδpos hx
  have hχ₁zeror : ∀ x, b + 2*δ ≤ x → χ₁ x = 0 := hχ₁zero
  have hw₁zerol : ∀ x, x ≤ b + 2*δ → w₁ x = 0 := by
    intro x hx; rw [hw₁]; exact caBump_eq_zero_of_le (x := x) hbc' hx
  have hw₁zeror : ∀ x, c - 2*δ ≤ x → w₁ x = 0 := by
    intro x hx; rw [hw₁]; exact caBump_eq_zero_of_ge (x := x) hbc' hx
  have hw₂zerol : ∀ x, x ≤ d + 2*δ → w₂ x = 0 := by
    intro x hx; rw [hw₂]; exact caBump_eq_zero_of_le (x := x) hdd' hx
  have hw₂zeror : ∀ x, d + 3*δ ≤ x → w₂ x = 0 := by
    intro x hx; rw [hw₂]; exact caBump_eq_zero_of_ge (x := x) hdd' hx
  have hχ₁sm : ContDiff ℝ Cinf χ₁ := by rw [hχ₁]; exact contDiff_caPlat _ _ _
  have hχ₂sm : ContDiff ℝ Cinf χ₂ := by rw [hχ₂]; exact contDiff_caPlat _ _ _
  have hw₁sm : ContDiff ℝ Cinf w₁ := by rw [hw₁]; exact contDiff_caBump _ _
  have hw₂sm : ContDiff ℝ Cinf w₂ := by rw [hw₂]; exact contDiff_caBump _ _
  -- the pieces
  set f₁ : ℝ → ℝ := fun x => (deriv ψ₁ x - M) * χ₁ x with hf₁
  set f₂ : ℝ → ℝ := fun x => (deriv ψ₂ x - M) * χ₂ x with hf₂
  have hf₁sm : ContDiff ℝ Cinf f₁ := by
    rw [hf₁]; exact (hd₁.sub contDiff_const).mul hχ₁sm
  have hf₂sm : ContDiff ℝ Cinf f₂ := by
    rw [hf₂]; exact (hd₂.sub contDiff_const).mul hχ₂sm
  have hf₁nn : ∀ x, 0 ≤ f₁ x := by
    intro x
    by_cases hx : χ₁ x = 0
    · rw [hf₁]; simp [hx]
    · have h1 := hχ₁ne x hx
      have h2 : x ∈ Set.Icc (a - 1) (b + 1) := ⟨by linarith [h1.1, h2δ1], by linarith [h1.2, h2δ1]⟩
      have h4 : 0 ≤ deriv ψ₁ x - M := by linarith [le_trans hM₁ (hm₁lo x h2)]
      rw [hf₁]; exact mul_nonneg h4 (hχ₁nn x)
  have hf₂nn : ∀ x, 0 ≤ f₂ x := by
    intro x
    by_cases hx : χ₂ x = 0
    · rw [hf₂]; simp [hx]
    · have h1 := hχ₂ne x hx
      have h2 : x ∈ Set.Icc (c - 1) (d + 1) := ⟨by linarith [h1.1, h2δ1], by linarith [h1.2, h2δ1]⟩
      have h4 : 0 ≤ deriv ψ₂ x - M := by linarith [le_trans hM₂ (hm₂lo x h2)]
      rw [hf₂]; exact mul_nonneg h4 (hχ₂nn x)
  have hf₁le : ∀ x, f₁ x ≤ K := by
    intro x
    by_cases hx : χ₁ x = 0
    · rw [hf₁]; simp [hx]; exact hKpos.le
    · have h1 := hχ₁ne x hx
      have h2 : x ∈ Set.Icc (a - 1) (d + 1) := ⟨by linarith [h1.1, h2δ1], by linarith [h1.2, hcd, hδpos]⟩
      have h3 : deriv ψ₁ x ≤ K := by
        have := hKb₁ x h2; rw [abs_le] at this; exact this.2
      have h4 : M ≤ deriv ψ₁ x := le_trans hM₁ (hm₁lo x ⟨by linarith [h1.1, h2δ1], by linarith [h1.2, h2δ1]⟩)
      have h5 : 0 ≤ deriv ψ₁ x - M := by linarith
      have h7 : χ₁ x ≤ 1 := by rw [hχ₁]; exact caPlat_le_one _ _ _ _
      rw [hf₁]
      calc (deriv ψ₁ x - M) * χ₁ x ≤ (deriv ψ₁ x - M) * 1 := mul_le_mul_of_nonneg_left h7 h5
        _ = deriv ψ₁ x - M := by ring
        _ ≤ K := by linarith
  have hf₂le : ∀ x, f₂ x ≤ K := by
    intro x
    by_cases hx : χ₂ x = 0
    · rw [hf₂]; simp [hx]; exact hKpos.le
    · have h1 := hχ₂ne x hx
      have h2 : x ∈ Set.Icc (a - 1) (d + 1) := ⟨by linarith [h1.1, hab, hbc, hcd, hδpos], by linarith [h1.2, h2δ1]⟩
      have h3 : deriv ψ₂ x ≤ K := by
        have := hKb₂ x h2; rw [abs_le] at this; exact this.2
      have h4 : M ≤ deriv ψ₂ x := le_trans hM₂ (hm₂lo x ⟨by linarith [h1.1, h2δ1], by linarith [h1.2, h2δ1]⟩)
      have h5 : 0 ≤ deriv ψ₂ x - M := by linarith
      have h7 : χ₂ x ≤ 1 := by rw [hχ₂]; exact caPlat_le_one _ _ _ _
      rw [hf₂]
      calc (deriv ψ₂ x - M) * χ₂ x ≤ (deriv ψ₂ x - M) * 1 := mul_le_mul_of_nonneg_left h7 h5
        _ = deriv ψ₂ x - M := by ring
        _ ≤ K := by linarith
  have hf₁zero : ∀ x, b + 2*δ ≤ x → f₁ x = 0 := by
    intro x hx; simp [hf₁, hχ₁zero x hx]
  have hf₂zerol : ∀ x, x ≤ c - 2*δ → f₂ x = 0 := by
    intro x hx; simp [hf₂, hχ₂zerol x hx]
  have hf₂zeror : ∀ x, d + 2*δ ≤ x → f₂ x = 0 := by
    intro x hx; simp [hf₂, hχ₂zeror x hx]
  have hf₁zerol : ∀ x, x ≤ a - 2*δ → f₁ x = 0 := by
    intro x hx; simp [hf₁, hχ₁zerol x hx]
  -- the constants
  set I₁ : ℝ := ∫ x in b..c, w₁ x with hI₁
  set I₂ : ℝ := ∫ x in d..(d + 3*δ), w₂ x with hI₂
  set P₀ : ℝ := ∫ x in b..c, (f₁ x + f₂ x) with hP₀
  set Q₀ : ℝ := (∫ x in d..(d + 3*δ), f₂ x) + (∫ x in (a - 2*δ)..a, f₁ x) with hQ₀
  have hI₁pos : 0 < I₁ := by
    rw [hI₁]
    refine intervalIntegral.integral_pos hbc hw₁sm.continuous.continuousOn (fun x _ => hw₁nn x)
      ⟨(b + c)/2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hw₁]; exact caBump_pos hbc' (by linarith) (by linarith)
  have hI₂pos : 0 < I₂ := by
    rw [hI₂]
    refine intervalIntegral.integral_pos (by linarith) hw₂sm.continuous.continuousOn (fun x _ => hw₂nn x)
      ⟨(d + 2*δ + (d + 3*δ))/2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hw₂]; exact caBump_pos hdd' (by linarith) (by linarith)
  have hP₀nn : 0 ≤ P₀ := by
    rw [hP₀]
    exact intervalIntegral.integral_nonneg (le_of_lt hbc) (fun x _ => add_nonneg (hf₁nn x) (hf₂nn x))
  have hP₀le : P₀ ≤ 4 * δ * K := by
    have hA : ∫ x in b..c, f₁ x ≤ 2 * δ * K := by
      have h1 : ∫ x in b..c, f₁ x = ∫ x in b..(b + 2*δ), f₁ x := by
        rw [caIntSplit b (b + 2*δ) c hf₁sm.continuous]
        have h2 : ∫ x in (b + 2*δ)..c, f₁ x = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_),
            intervalIntegral.integral_zero]
          rw [Set.uIcc_of_le (by linarith)] at hx
          exact hf₁zero x hx.1
        rw [h2]; ring
      rw [h1]
      have h2 : ∫ x in b..(b + 2*δ), f₁ x ≤ ∫ x in b..(b + 2*δ), (fun _ => K) x := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hf₁sm.continuous.intervalIntegrable b (b + 2*δ))
          (continuous_const.intervalIntegrable b (b + 2*δ))
        intro x _; exact hf₁le x
      rw [intervalIntegral.integral_const] at h2
      simpa using h2
    have hB : ∫ x in b..c, f₂ x ≤ 2 * δ * K := by
      have h1 : ∫ x in b..c, f₂ x = ∫ x in (c - 2*δ)..c, f₂ x := by
        rw [caIntSplit b (c - 2*δ) c hf₂sm.continuous]
        have h2 : ∫ x in b..(c - 2*δ), f₂ x = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_),
            intervalIntegral.integral_zero]
          rw [Set.uIcc_of_le (by linarith)] at hx
          exact hf₂zerol x hx.2
        rw [h2]; ring
      rw [h1]
      have h2 : ∫ x in (c - 2*δ)..c, f₂ x ≤ ∫ x in (c - 2*δ)..c, (fun _ => K) x := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hf₂sm.continuous.intervalIntegrable (c - 2*δ) c)
          (continuous_const.intervalIntegrable (c - 2*δ) c)
        intro x _; exact hf₂le x
      rw [intervalIntegral.integral_const] at h2
      simpa using h2
    have h1 : ∫ x in b..c, (f₁ x + f₂ x) = (∫ x in b..c, f₁ x) + (∫ x in b..c, f₂ x) :=
      caIntAdd b c hf₁sm.continuous hf₂sm.continuous
    rw [hP₀, h1]; linarith
  have hQ₀nn : 0 ≤ Q₀ := by
    rw [hQ₀]
    exact add_nonneg (intervalIntegral.integral_nonneg (by linarith) (fun x _ => hf₂nn x))
      (intervalIntegral.integral_nonneg (by linarith) (fun x _ => hf₁nn x))
  have hQ₀le : Q₀ ≤ 5 * δ * K := by
    have hA : ∫ x in d..(d + 3*δ), f₂ x ≤ 3 * δ * K := by
      have h2 : ∫ x in d..(d + 3*δ), f₂ x ≤ ∫ x in d..(d + 3*δ), (fun _ => K) x := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hf₂sm.continuous.intervalIntegrable d (d + 3*δ))
          (continuous_const.intervalIntegrable d (d + 3*δ))
        intro x _; exact hf₂le x
      rw [intervalIntegral.integral_const] at h2
      simpa using h2
    have hB : ∫ x in (a - 2*δ)..a, f₁ x ≤ 2 * δ * K := by
      have h2 : ∫ x in (a - 2*δ)..a, f₁ x ≤ ∫ x in (a - 2*δ)..a, (fun _ => K) x := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hf₁sm.continuous.intervalIntegrable (a - 2*δ) a)
          (continuous_const.intervalIntegrable (a - 2*δ) a)
        intro x _; exact hf₁le x
      rw [intervalIntegral.integral_const] at h2
      simpa using h2
    rw [hQ₀]; linarith
  set α : ℝ := (C - B - M*(c - b) - P₀)/I₁ with hα
  set β : ℝ := (A + 2*Real.pi - D - M*(a + 2*Real.pi - d) - Q₀)/I₂ with hβ
  have hαnn : 0 ≤ α := by
    rw [hα]
    apply div_nonneg _ (le_of_lt hI₁pos)
    linarith [hP₀le, hMcb, hδCBK, hP₀nn, hMpos]
  have hβnn : 0 ≤ β := by
    rw [hβ]
    apply div_nonneg _ (le_of_lt hI₂pos)
    linarith [hQ₀le, hMad, hδADK, hQ₀nn, hMpos]
  set W : ℝ → ℝ := fun x => f₁ x + f₂ x + (α * w₁ x + β * w₂ x) with hW
  set v : ℝ → ℝ := fun x => M + caPerSum (2*Real.pi) W x with hv
  have hWnn : ∀ x, 0 ≤ W x := by
    intro x; rw [hW]; simp only []
    linarith [hf₁nn x, hf₂nn x, mul_nonneg hαnn (hw₁nn x), mul_nonneg hβnn (hw₂nn x)]
  have hWne : ∀ x, W x ≠ 0 → x ∈ Set.Icc (a - 2*δ) (d + 3*δ) := by
    intro x hx
    have h1 : f₁ x ≠ 0 ∨ f₂ x ≠ 0 ∨ α * w₁ x ≠ 0 ∨ β * w₂ x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [hW]; simp only []
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; ring
    rcases h1 with h | h | h | h
    · have hχ : χ₁ x ≠ 0 := fun hc => h (by rw [hf₁]; simp only []; rw [hc, mul_zero])
      have h2 := hχ₁ne x hχ
      exact ⟨by linarith [h2.1], by linarith [h2.2, hcd, hδpos]⟩
    · have hχ : χ₂ x ≠ 0 := fun hc => h (by rw [hf₂]; simp only []; rw [hc, mul_zero])
      have h2 := hχ₂ne x hχ
      exact ⟨by linarith [h2.1, hab, hbc, hcd], by linarith [h2.2, hδpos]⟩
    · have h2 := hw₁ne x (fun hc => h (by rw [hc, mul_zero]))
      exact ⟨by linarith [h2.1], by linarith [h2.2, hcd, hδpos]⟩
    · have h2 := hw₂ne x (fun hc => h (by rw [hc, mul_zero]))
      exact ⟨by linarith [h2.1, hab, hbc, hcd], by linarith [h2.2]⟩
  have hWsm : ContDiff ℝ Cinf W := by
    rw [hW]
    exact (hf₁sm.add hf₂sm).add ((contDiff_const.mul hw₁sm).add (contDiff_const.mul hw₂sm))
  have hWcs : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun x hx => hWne x (Function.mem_support.mp hx))
  have h2πpos : 0 < 2 * Real.pi := by positivity
  have h2πnn : 0 ≤ 2 * Real.pi := le_of_lt h2πpos
  have hpWsm : ContDiff ℝ Cinf (fun x => caPerSum (2*Real.pi) W x) :=
    contDiff_caPerSum (2*Real.pi) h2πpos W hWsm hWcs
  have hvsm : ContDiff ℝ Cinf v := by rw [hv]; exact contDiff_const.add hpWsm
  have hvpos : ∀ x, 0 < v x := by
    intro x
    have h1 : 0 ≤ caPerSum (2*Real.pi) W x := tsum_nonneg (fun k => hWnn _)
    rw [hv]; simp only []; linarith
  have hvper : ∀ x, v (x + 2*Real.pi) = v x := by
    intro x
    have h := (caPerSum_periodic (2*Real.pi) W) x
    rw [hv]; simp only []; rw [h]
  have hpsb : ∀ x ∈ Set.Icc b c, caPerSum (2*Real.pi) W x = W x := by
    intro x hx
    exact caPerSum_eq_self h2πnn hWne (by linarith [hx.1, hab]) (by linarith [hx.2, hcd, hδpos])
      (by linarith [hx.2, hbc, hcd, h2δda]) (by linarith [hx.1, hab, h3δdb])
  have hv₁ : ∀ x ∈ Set.Icc a b, v x = deriv ψ₁ x := by
    intro x hx
    have hps : caPerSum (2*Real.pi) W x = W x := caPerSum_eq_self h2πnn hWne
      (by linarith [hx.1]) (by linarith [hx.2, hcd, hδpos])
      (by linarith [hx.2, hab, hbc, hcd, h2δda]) (by linarith [hx.1, h5δad])
    have hWx : W x = deriv ψ₁ x - M := by
      have hc1 : χ₁ x = 1 := hχ₁one x hx
      have hc2 : χ₂ x = 0 := hχ₂zerol x (by linarith [hx.2, hbc])
      have hw1 : w₁ x = 0 := hw₁zerol x (by linarith [hx.2])
      have hw2 : w₂ x = 0 := hw₂zerol x (by linarith [hx.2, hbc, hcd])
      rw [hW]; simp only [hf₁, hf₂, hc1, hc2, hw1, hw2]; ring
    rw [hv]; simp only []; rw [hps, hWx]; ring
  have hv₂ : ∀ x ∈ Set.Icc c d, v x = deriv ψ₂ x := by
    intro x hx
    have hps : caPerSum (2*Real.pi) W x = W x := caPerSum_eq_self h2πnn hWne
      (by linarith [hx.1, hab, hbc]) (by linarith [hx.2, hδpos])
      (by linarith [hx.2, hcd, h2δda]) (by linarith [hx.1, hbc, hcd, h3δdc])
    have hWx : W x = deriv ψ₂ x - M := by
      have hc1 : χ₁ x = 0 := hχ₁zero x (by linarith [hx.1, hbc])
      have hc2 : χ₂ x = 1 := hχ₂one x hx
      have hw1 : w₁ x = 0 := hw₁zeror x (by linarith [hx.1, hbc])
      have hw2 : w₂ x = 0 := hw₂zerol x (by linarith [hx.2, hcd])
      rw [hW]; simp only [hf₁, hf₂, hc1, hc2, hw1, hw2]; ring
    rw [hv]; simp only []; rw [hps, hWx]; ring
  have hvint₁ : (∫ x in b..c, v x) = C - B := by
    have hvc : ∫ x in b..c, v x = ∫ x in b..c, (M + caPerSum (2*Real.pi) W x) := by
      apply intervalIntegral.integral_congr
      intro x _; rw [hv]
    have hstep : ∫ x in b..c, (M + caPerSum (2*Real.pi) W x)
        = M*(c-b) + ∫ x in b..c, caPerSum (2*Real.pi) W x := by
      have h := caIntAdd (f := fun _ : ℝ => M)
        (g := fun x => caPerSum (2*Real.pi) W x) b c continuous_const hpWsm.continuous
      rw [h, intervalIntegral.integral_const]
      simp only [smul_eq_mul]; ring
    rw [hvc, hstep]
    have hps : ∫ x in b..c, caPerSum (2*Real.pi) W x = ∫ x in b..c, W x :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [Set.uIcc_of_le (le_of_lt hbc)] at hx; exact hpsb x hx)
    rw [hps]
    have hWc : ∫ x in b..c, W x = P₀ + α * I₁ := by
      have h1 : ∫ x in b..c, W x
          = ∫ x in b..c, ((f₁ x + f₂ x) + (α * w₁ x + β * w₂ x)) := by
        apply intervalIntegral.integral_congr
        intro x _; rw [hW]
      have h2 : ∫ x in b..c, ((f₁ x + f₂ x) + (α * w₁ x + β * w₂ x))
          = (∫ x in b..c, (f₁ x + f₂ x)) + (∫ x in b..c, (α * w₁ x + β * w₂ x)) :=
        caIntAdd b c ((hf₁sm.add hf₂sm).continuous)
          ((Continuous.mul continuous_const hw₁sm.continuous).add
            (Continuous.mul continuous_const hw₂sm.continuous))
      have h3 : ∫ x in b..c, (f₁ x + f₂ x) = (∫ x in b..c, f₁ x) + (∫ x in b..c, f₂ x) :=
        caIntAdd b c hf₁sm.continuous hf₂sm.continuous
      have h4 : ∫ x in b..c, (α * w₁ x + β * w₂ x)
          = (∫ x in b..c, α * w₁ x) + (∫ x in b..c, β * w₂ x) :=
        caIntAdd b c (Continuous.mul continuous_const hw₁sm.continuous)
          (Continuous.mul continuous_const hw₂sm.continuous)
      have h5 : ∫ x in b..c, α * w₁ x = α * I₁ := by
        rw [intervalIntegral.integral_const_mul, hI₁]
      have h6 : ∫ x in b..c, β * w₂ x = 0 := by
        rw [intervalIntegral.integral_const_mul]
        have hz : ∫ x in b..c, w₂ x = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_),
            intervalIntegral.integral_zero]
          rw [Set.uIcc_of_le (le_of_lt hbc)] at hx
          exact hw₂zerol x (by linarith [hx.2, hbc, hcd])
        rw [hz, mul_zero]
      rw [h1, h2, h3, h4, h5, h6, hP₀, h3]; ring
    rw [hWc]
    have hI₁ne : I₁ ≠ 0 := ne_of_gt hI₁pos
    rw [hα]
    field_simp
    ring
  have hvint₂ : (∫ x in d..(a + 2*Real.pi), v x) = A + 2*Real.pi - D := by
    have hvc : ∫ x in d..(a + 2*Real.pi), v x
        = ∫ x in d..(a + 2*Real.pi), (M + caPerSum (2*Real.pi) W x) := by
      apply intervalIntegral.integral_congr
      intro x _; rw [hv]
    have hstep : ∫ x in d..(a + 2*Real.pi), (M + caPerSum (2*Real.pi) W x)
        = M*(a + 2*Real.pi - d) + ∫ x in d..(a + 2*Real.pi), caPerSum (2*Real.pi) W x := by
      have h := caIntAdd (f := fun _ : ℝ => M)
        (g := fun x => caPerSum (2*Real.pi) W x) d (a + 2*Real.pi) continuous_const hpWsm.continuous
      rw [h, intervalIntegral.integral_const]
      simp only [smul_eq_mul]; ring
    rw [hvc, hstep]
    have hsplit : ∫ x in d..(a + 2*Real.pi), caPerSum (2*Real.pi) W x
        = (∫ x in d..(a + 2*Real.pi - 2*δ), caPerSum (2*Real.pi) W x)
          + (∫ x in (a + 2*Real.pi - 2*δ)..(a + 2*Real.pi), caPerSum (2*Real.pi) W x) :=
      caIntSplit d (a + 2*Real.pi - 2*δ) (a + 2*Real.pi) hpWsm.continuous
    rw [hsplit]
    have hps1 : ∫ x in d..(a + 2*Real.pi - 2*δ), caPerSum (2*Real.pi) W x
        = ∫ x in d..(d + 3*δ), W x := by
      rw [caIntSplit d (d + 3*δ) (a + 2*Real.pi - 2*δ) hpWsm.continuous]
      have hA : ∫ x in d..(d + 3*δ), caPerSum (2*Real.pi) W x = ∫ x in d..(d + 3*δ), W x :=
        intervalIntegral.integral_congr (fun x hx => by
          rw [Set.uIcc_of_le (by linarith)] at hx
          exact caPerSum_eq_self h2πnn hWne (by linarith [hx.1, hab, hbc, hcd]) (by linarith [hx.2])
            (by linarith [hx.2, hδpos]) (by linarith [hx.1, hab, hbc, hcd, h5δad]))
      have hWe : W (d + 3*δ) = 0 := by
        rw [hW]
        have h2 : f₁ (d + 3*δ) = 0 := hf₁zero _ (by linarith [hab, hbc, hcd])
        have h3 : f₂ (d + 3*δ) = 0 := hf₂zeror _ (by linarith)
        have h4 : w₁ (d + 3*δ) = 0 := hw₁zeror _ (by linarith [hbc, hcd])
        have h5 : w₂ (d + 3*δ) = 0 := hw₂zeror _ (by linarith)
        simp only [h2, h3, h4, h5]; ring
      have hWs : W (a - 2*δ) = 0 := by
        rw [hW]
        have h2 : f₁ (a - 2*δ) = 0 := hf₁zerol _ (by linarith)
        have h3 : f₂ (a - 2*δ) = 0 := hf₂zerol _ (by linarith [hab, hbc, hcd])
        have h4 : w₁ (a - 2*δ) = 0 := hw₁zerol _ (by linarith [hab])
        have h5 : w₂ (a - 2*δ) = 0 := hw₂zerol _ (by linarith [hab, hbc, hcd])
        simp only [h2, h3, h4, h5]; ring
      have hB : ∫ x in (d + 3*δ)..(a + 2*Real.pi - 2*δ), caPerSum (2*Real.pi) W x = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x hx => ?_),
          intervalIntegral.integral_zero]
        rw [Set.uIcc_of_le (by linarith)] at hx
        exact caPerSum_eq_zero'' (s := a - 2*δ) (e := d + 3*δ) h2πnn hWne hWs hWe
          (by linarith [hx.1]) (by linarith [hx.2])
      rw [hA, hB]; ring
    rw [hps1]
    have hps2 : ∫ x in (a + 2*Real.pi - 2*δ)..(a + 2*Real.pi), caPerSum (2*Real.pi) W x
        = ∫ x in (a - 2*δ)..a, W x := by
      have h1 : ∫ x in (a + 2*Real.pi - 2*δ)..(a + 2*Real.pi), caPerSum (2*Real.pi) W x
          = ∫ x in (a + 2*Real.pi - 2*δ)..(a + 2*Real.pi), W (x - 2*Real.pi) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        exact caPerSum_eq_shift h2πnn hWne (by linarith [hx.1]) (by linarith [hx.2])
          (by linarith [hx.1, h5δad]) (by linarith [hx.2])
      rw [h1, intervalIntegral.integral_comp_sub_right]
      congr 1 <;> ring
    rw [hps2]
    have hWc1 : ∫ x in d..(d + 3*δ), W x = (∫ x in d..(d + 3*δ), f₂ x) + β * I₂ := by
      have h1 : ∫ x in d..(d + 3*δ), W x = ∫ x in d..(d + 3*δ), (f₂ x + β * w₂ x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith)] at hx
        have h2 : f₁ x = 0 := hf₁zero x (by linarith [hx.1, hab, hbc, hcd])
        have h3 : α * w₁ x = 0 := by rw [hw₁zeror x (by linarith [hx.1, hbc, hcd]), mul_zero]
        rw [hW]; simp only [h2, h3]; ring
      have h4 : ∫ x in d..(d + 3*δ), (f₂ x + β * w₂ x)
          = (∫ x in d..(d + 3*δ), f₂ x) + (∫ x in d..(d + 3*δ), β * w₂ x) :=
        caIntAdd d (d + 3*δ) hf₂sm.continuous
          (Continuous.mul continuous_const hw₂sm.continuous)
      have h5 : ∫ x in d..(d + 3*δ), β * w₂ x = β * I₂ := by
        rw [intervalIntegral.integral_const_mul, hI₂]
      rw [h1, h4, h5]
    have hWc2 : ∫ x in (a - 2*δ)..a, W x = ∫ x in (a - 2*δ)..a, f₁ x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have h2 : f₂ x = 0 := hf₂zerol x (by linarith [hx.2, hab, hbc])
      have h3 : α * w₁ x = 0 := by rw [hw₁zerol x (by linarith [hx.2, hab]), mul_zero]
      have h4 : β * w₂ x = 0 := by rw [hw₂zerol x (by linarith [hx.2, hab, hbc, hcd]), mul_zero]
      rw [hW]; simp only [h2, h3, h4]; ring
    rw [hWc1, hWc2]
    have hI₂ne : I₂ ≠ 0 := ne_of_gt hI₂pos
    have h1 : Q₀ = (∫ x in d..(d + 3*δ), f₂ x) + (∫ x in (a - 2*δ)..a, f₁ x) := hQ₀
    have h2 : β * I₂ = A + 2*Real.pi - D - M * (a + 2*Real.pi - d) - Q₀ := by
      rw [hβ]
      field_simp
    linarith
  exact ⟨v, hvsm, hvpos, hvper, hv₁, hv₂, hvint₁, hvint₂⟩

/-- **Whitney's circle-arc extension lemma.**  Two strictly increasing smooth functions prescribed
on two arcs of length `< 2π` which are `2π`-compatible extend to a smooth, strictly increasing,
`2π`-quasi-periodic function of the line. -/
theorem circleArcExtension (a b c d A B C D : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdA : d < a + 2 * Real.pi)
    (hAB : A < B) (hBC : B < C) (hCD : C < D) (hDA : D < A + 2 * Real.pi)
    (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁)
    (h₁mono : ∀ x : ℝ, 0 < deriv ψ₁ x)
    (h₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₂)
    (h₂mono : ∀ x : ℝ, 0 < deriv ψ₂ x)
    (h₁a : ψ₁ a = A) (h₁b : ψ₁ b = B) (h₂c : ψ₂ c = C) (h₂d : ψ₂ d = D) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ x : ℝ, 0 < deriv Ψ x) ∧
      (∀ x : ℝ, Ψ (x + 2 * Real.pi) = Ψ x + 2 * Real.pi) ∧
      (∀ x : ℝ, x ∈ Set.Icc a b → Ψ x = ψ₁ x) ∧
      (∀ x : ℝ, x ∈ Set.Icc c d → Ψ x = ψ₂ x) := by
  obtain ⟨v, hvsm, hvpos, hvper, hv₁, hv₂, hvint₁, hvint₂⟩ :=
    exists_quasiPeriodic_slope a b c d A B C D hab hbc hcd hdA hAB hBC hCD hDA ψ₁ ψ₂
      h₁sm h₁mono h₂sm h₂mono
  have hvcont : Continuous v := hvsm.continuous
  have hvderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => B + ∫ t in b..x, v t) (v x) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => ∫ t in b..u, v t) (v x) x :=
      intervalIntegral.integral_hasDerivAt_right (hvcont.intervalIntegrable b x)
        (hvcont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)) hvcont.continuousAt
    exact h1.const_add B
  have hderiv_eq : deriv (fun x : ℝ => B + ∫ t in b..x, v t) = v :=
    funext (fun x => (hvderiv x).deriv)
  have hInt1 : ∫ t in a..b, v t = B - A := by
    have hcg : ∫ t in a..b, v t = ∫ t in a..b, deriv ψ₁ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hab)] at ht
      exact hv₁ t ht
    rw [hcg, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (h₁sm.differentiable (by simp)).differentiableAt)
      ((Continuous.intervalIntegrable (h₁sm.continuous_deriv (by simp)) a b))]
    rw [h₁b, h₁a]
  have hInt3 : ∫ t in c..d, v t = D - C := by
    have hcg : ∫ t in c..d, v t = ∫ t in c..d, deriv ψ₂ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hcd)] at ht
      exact hv₂ t ht
    rw [hcg, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (h₂sm.differentiable (by simp)).differentiableAt)
      ((Continuous.intervalIntegrable (h₂sm.continuous_deriv (by simp)) c d))]
    rw [h₂d, h₂c]
  have htotal : ∫ t in a..(a + 2 * Real.pi), v t = 2 * Real.pi := by
    have hsp : ∫ t in a..(a + 2 * Real.pi), v t
        = (∫ t in a..b, v t) + (∫ t in b..c, v t) + (∫ t in c..d, v t)
          + (∫ t in d..(a + 2 * Real.pi), v t) := by
      have s1 := caIntSplit a b (a + 2 * Real.pi) hvcont
      have s2 := caIntSplit b c (a + 2 * Real.pi) hvcont
      have s3 := caIntSplit c d (a + 2 * Real.pi) hvcont
      linarith
    rw [hsp, hInt1, hvint₁, hInt3, hvint₂]; ring
  refine ⟨fun x => B + ∫ t in b..x, v t, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_infty_iff_deriv.mpr
      ⟨fun x => (hvderiv x).differentiableAt, by rw [hderiv_eq]; exact hvsm⟩
  · intro x; rw [(hvderiv x).deriv]; exact hvpos x
  · intro x
    show B + ∫ t in b..(x + 2 * Real.pi), v t = (B + ∫ t in b..x, v t) + 2 * Real.pi
    have h1 : ∫ t in b..(x + 2 * Real.pi), v t
        = (∫ t in b..x, v t) + (∫ t in x..(x + 2 * Real.pi), v t) :=
      caIntSplit b x (x + 2 * Real.pi) hvcont
    have h2 : ∫ t in x..(x + 2 * Real.pi), v t = ∫ t in a..(a + 2 * Real.pi), v t :=
      Function.Periodic.intervalIntegral_add_eq (show Function.Periodic v (2 * Real.pi) from hvper) x a
    rw [h1, h2, htotal]; ring
  · intro x hx
    show B + ∫ t in b..x, v t = ψ₁ x
    have h1 : ∫ t in b..x, v t = -∫ t in x..b, v t := by
      rw [intervalIntegral.integral_symm]
    have hcg : ∫ t in x..b, v t = ∫ t in x..b, deriv ψ₁ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith [hx.2])] at ht
      exact hv₁ t ⟨le_trans hx.1 ht.1, ht.2⟩
    have h2 : ∫ t in x..b, deriv ψ₁ t = ψ₁ b - ψ₁ x :=
      intervalIntegral.integral_deriv_eq_sub
        (fun y _ => (h₁sm.differentiable (by simp)).differentiableAt)
        ((Continuous.intervalIntegrable (h₁sm.continuous_deriv (by simp)) x b))
    rw [h1, hcg, h2, h₁b]; ring
  · intro x hx
    show B + ∫ t in b..x, v t = ψ₂ x
    have h1 : ∫ t in b..x, v t
        = (∫ t in b..c, v t) + (∫ t in c..x, v t) :=
      caIntSplit b c x hvcont
    have hcg : ∫ t in c..x, v t = ∫ t in c..x, deriv ψ₂ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (hx.1)] at ht
      exact hv₂ t ⟨ht.1, le_trans ht.2 hx.2⟩
    have h2 : ∫ t in c..x, deriv ψ₂ t = ψ₂ x - ψ₂ c :=
      intervalIntegral.integral_deriv_eq_sub
        (fun y _ => (h₂sm.differentiable (by simp)).differentiableAt)
        ((Continuous.intervalIntegrable (h₂sm.continuous_deriv (by simp)) c x))
    rw [h1, hvint₁, hcg, h2, h₂c]; ring

end Work.Drive.N2
