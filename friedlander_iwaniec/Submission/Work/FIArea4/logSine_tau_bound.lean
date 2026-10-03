import Mathlib
import Submission.Commons.Analysis.ContDiff.exists_smooth_cutoff_infty

namespace Work.FIArea4

open Filter

/-- `x ∉ [0,1]` iff `x < 0` or `1 < x`. -/
private lemma notMem_Icc_zero_one_iff {x : ℝ} : x ∉ Set.Icc (0 : ℝ) 1 ↔ x < 0 ∨ 1 < x := by
  rw [Set.mem_Icc]
  constructor
  · intro h
    rcases lt_or_ge x 0 with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (lt_of_not_ge fun hle => h ⟨hge, hle⟩)
  · rintro (h | h) ⟨h1, h2⟩ <;> linarith

/-- If a function is eventually equal to a constant at `x`, its derivative there is `0`. -/
private lemma deriv_eq_zero_of_eventuallyEq_const {g : ℝ → ℝ} {x : ℝ} (c : ℝ)
    (hev : g =ᶠ[nhds x] fun _ => c) : deriv g x = 0 := by
  rw [hev.deriv_eq]
  exact deriv_const x c

/-- `τ'` vanishes outside `[0,1]`. -/
private lemma deriv_smoothTransition_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  rcases notMem_Icc_zero_one_iff.mp hx with h | h
  · refine deriv_eq_zero_of_eventuallyEq_const 0 ?_
    filter_upwards [isOpen_Iio.mem_nhds h] with z hz
    exact Real.smoothTransition.zero_of_nonpos hz.le
  · refine deriv_eq_zero_of_eventuallyEq_const 1 ?_
    filter_upwards [isOpen_Ioi.mem_nhds h] with z hz
    exact Real.smoothTransition.one_of_one_le hz.le

/-- `τ''` vanishes outside `[0,1]`. -/
private lemma deriv_deriv_smoothTransition_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  rcases notMem_Icc_zero_one_iff.mp hx with h | h
  · refine deriv_eq_zero_of_eventuallyEq_const 0 ?_
    filter_upwards [isOpen_Iio.mem_nhds h] with z hz
    exact deriv_smoothTransition_eq_zero (by
      rw [notMem_Icc_zero_one_iff]; exact Or.inl hz)
  · refine deriv_eq_zero_of_eventuallyEq_const 0 ?_
    filter_upwards [isOpen_Ioi.mem_nhds h] with z hz
    exact deriv_smoothTransition_eq_zero (by
      rw [notMem_Icc_zero_one_iff]; exact Or.inr hz)

/-- `τ = Real.smoothTransition` is `C^∞`, `0` on `(-∞,0]` and `1` on `[1,∞)`; hence `τ'` and
`τ''` vanish outside `[0,1]` and are bounded. -/
theorem logSine_tau_bound :
    (∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
        |deriv Real.smoothTransition x| ≤ K ∧ |deriv (deriv Real.smoothTransition) x| ≤ K) ∧
    (∀ x : ℝ, x ∉ Set.Icc 0 1 → deriv Real.smoothTransition x = 0) ∧
    (∀ x : ℝ, x ∉ Set.Icc 0 1 → deriv (deriv Real.smoothTransition) x = 0) := by
  have hbdd := Commons.Analysis.ContDiff.exists_bound_iteratedDeriv_of_const_outside
      Real.smoothTransition Real.smoothTransition.contDiff (a := 0) (b := 1) (by norm_num)
      (fun t ht => by rw [Real.smoothTransition.zero_of_nonpos ht, Real.smoothTransition.zero])
      (fun t ht => by rw [Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one])
  obtain ⟨A1, hA1pos, hA1⟩ := hbdd 1
  obtain ⟨A2, hA2pos, hA2⟩ := hbdd 2
  refine ⟨⟨max A1 A2, lt_of_lt_of_le hA1pos (le_max_left _ _), fun x => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · have h := hA1 x
    rw [iteratedDeriv_one] at h
    exact le_trans h (le_max_left _ _)
  · have h := hA2 x
    have h2 : iteratedDeriv 2 Real.smoothTransition
        = deriv (deriv Real.smoothTransition) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2] at h
    exact le_trans h (le_max_right _ _)
  · exact fun x hx => deriv_smoothTransition_eq_zero hx
  · exact fun x hx => deriv_deriv_smoothTransition_eq_zero hx

end Work.FIArea4
