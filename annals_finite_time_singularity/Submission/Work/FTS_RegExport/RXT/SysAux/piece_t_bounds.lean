import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ### Derivative facts about the three angular profiles -/

/-- The constant function has derivative the zero function. -/
theorem deriv_const_fun (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ : ℝ => (0 : ℝ) := by
  funext x
  exact deriv_const x c

/-- `d/dθ (sin θ)² = sin 2θ`. -/
theorem hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2) (Real.sin (2 * θ)) θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  rw [Real.sin_two_mul]
  convert h using 1
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one]
  ring

theorem deriv_sin_sq (θ : ℝ) :
    deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) :=
  (hasDerivAt_sin_sq θ).deriv

theorem deriv_sin_sq_fun :
    deriv (fun y : ℝ => Real.sin y ^ 2) = fun y : ℝ => Real.sin (2 * y) := by
  funext y
  exact deriv_sin_sq y

/-- `d/dθ (sin 2θ)² = 4 sin 2θ cos 2θ`. -/
theorem hasDerivAt_sin_two_sq (θ : ℝ) :
    HasDerivAt (fun η : ℝ => Real.sin (2 * η) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun η : ℝ => Real.sin (2 * η)) (2 * Real.cos (2 * θ)) θ := by
    have h0 : HasDerivAt (fun η : ℝ => Real.sin (2 * η))
        (Real.cos (2 * θ) * (2 * 1)) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
    have h1 : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rwa [h1] at h0
  have h2 : HasDerivAt (fun η : ℝ => Real.sin (2 * η) ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h.pow 2
  have h3 : 2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one]
    ring
  rwa [h3] at h2

theorem deriv_sin_two_sq (θ : ℝ) :
    deriv (fun η : ℝ => Real.sin (2 * η) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two_sq θ).deriv

theorem deriv_sin_two_sq_fun :
    deriv (fun y : ℝ => Real.sin (2 * y) ^ 2)
      = fun y : ℝ => 4 * Real.sin (2 * y) * Real.cos (2 * y) := by
  funext y
  exact deriv_sin_two_sq y

/-- `d/dθ (cos 2θ − sin²θ) = -3 sin 2θ`. -/
theorem hasDerivAt_c2m (θ : ℝ) :
    HasDerivAt Work.Construction.c2m (-3 * Real.sin (2 * θ)) θ := by
  have hc : HasDerivAt (fun η : ℝ => Real.cos (2 * η))
      ((-Real.sin (2 * θ)) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hs : HasDerivAt (fun η : ℝ => Real.sin η ^ 2) (Real.sin (2 * θ)) θ :=
    hasDerivAt_sin_sq θ
  have h : HasDerivAt Work.Construction.c2m
      ((-Real.sin (2 * θ)) * (2 * 1) - Real.sin (2 * θ)) θ := hc.sub hs
  have h2 : (-Real.sin (2 * θ)) * (2 * 1) - Real.sin (2 * θ)
      = -3 * Real.sin (2 * θ) := by ring
  rwa [h2] at h

theorem deriv_c2m (θ : ℝ) :
    deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) :=
  (hasDerivAt_c2m θ).deriv

theorem deriv_c2m_fun :
    deriv Work.Construction.c2m = fun y : ℝ => -3 * Real.sin (2 * y) := by
  funext y
  exact deriv_c2m y

/-- `d/dθ (-3 (sin 2θ)²) = -12 sin 2θ cos 2θ`. -/
theorem deriv_neg3_sin_two_sq (θ : ℝ) :
    deriv (fun x : ℝ => -3 * Real.sin (2 * x) ^ 2) θ
      = -12 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  rw [deriv_const_mul_field, deriv_sin_two_sq]
  ring

theorem deriv_neg3_sin_two_sq_fun :
    deriv (fun x : ℝ => -3 * Real.sin (2 * x) ^ 2)
      = fun x : ℝ => -12 * Real.sin (2 * x) * Real.cos (2 * x) := by
  funext x
  exact deriv_neg3_sin_two_sq x

/-! ### The iterates `TIter i` evaluated on the three profiles -/

/-- Unfolding of `TIter 1`. -/
theorem TIter_one_apply (B : ℝ → ℝ) :
    TIter 1 B = fun x => Real.sin (2 * x) * deriv B x := rfl

/-- Unfolding of `TIter 2`. -/
theorem TIter_two_apply (B : ℝ → ℝ) :
    TIter 2 B = fun x => Real.sin (2 * x) * deriv (fun y => Real.sin (2 * y) * deriv B y) x :=
  rfl

theorem TIter_one_const (θ : ℝ) : TIter 1 (fun _ : ℝ => (1 : ℝ)) θ = 0 := by
  change Real.sin (2 * θ) * deriv (fun _ : ℝ => (1 : ℝ)) θ = 0
  simp [deriv_const]

theorem TIter_one_c2m (θ : ℝ) :
    TIter 1 Work.Construction.c2m θ = -3 * Real.sin (2 * θ) ^ 2 := by
  change Real.sin (2 * θ) * deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) ^ 2
  rw [deriv_c2m]
  ring

theorem TIter_one_sinsq (θ : ℝ) :
    TIter 1 (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) ^ 2 := by
  change Real.sin (2 * θ) * deriv (fun y : ℝ => Real.sin y ^ 2) θ
    = Real.sin (2 * θ) ^ 2
  rw [deriv_sin_sq]
  ring

theorem TIter_two_const (θ : ℝ) : TIter 2 (fun _ : ℝ => (1 : ℝ)) θ = 0 := by
  have h1 : TIter 1 (fun _ : ℝ => (1 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    change Real.sin (2 * x) * deriv (fun _ : ℝ => (1 : ℝ)) x = 0
    simp [deriv_const]
  change Real.sin (2 * θ) * deriv (TIter 1 (fun _ : ℝ => (1 : ℝ))) θ = 0
  rw [h1]
  simp [deriv_const]

theorem TIter_two_c2m (θ : ℝ) :
    TIter 2 Work.Construction.c2m θ = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  have h1 : TIter 1 Work.Construction.c2m = fun x : ℝ => -3 * Real.sin (2 * x) ^ 2 := by
    funext x
    change Real.sin (2 * x) * deriv Work.Construction.c2m x = -3 * Real.sin (2 * x) ^ 2
    rw [deriv_c2m]
    ring
  change Real.sin (2 * θ) * deriv (TIter 1 Work.Construction.c2m) θ
    = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)
  rw [h1, deriv_neg3_sin_two_sq]
  ring

theorem TIter_two_sinsq (θ : ℝ) :
    TIter 2 (fun θ : ℝ => Real.sin θ ^ 2) θ
      = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  have h1 : TIter 1 (fun θ : ℝ => Real.sin θ ^ 2) = fun x : ℝ => Real.sin (2 * x) ^ 2 := by
    funext x
    change Real.sin (2 * x) * deriv (fun y : ℝ => Real.sin y ^ 2) x
      = Real.sin (2 * x) ^ 2
    rw [deriv_sin_sq]
    ring
  change Real.sin (2 * θ) * deriv (TIter 1 (fun θ : ℝ => Real.sin θ ^ 2)) θ
    = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)
  rw [h1, deriv_sin_two_sq]
  ring

/-! ### Bounds on the evaluated profiles -/

theorem abs_c2m_le_twelve (θ : ℝ) : |Work.Construction.c2m θ| ≤ 12 := by
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  rw [Work.Construction.c2m_eq, abs_le]
  constructor <;> linarith

theorem abs_sinsq_le_four (θ : ℝ) : |Real.sin θ ^ 2| ≤ 4 := by
  rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
  nlinarith [Real.sin_sq_le_one θ]

theorem abs_neg3_sin_two_sq_le (θ : ℝ) :
    |(-3 : ℝ) * Real.sin (2 * θ) ^ 2| ≤ 12 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem abs_neg12_sin_two_sq_mul_cos_le (θ : ℝ) :
    |(-12 : ℝ) * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)| ≤ 12 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_four_sin_two_sq_mul_cos_le (θ : ℝ) :
    |4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)| ≤ 4 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The target -/

theorem piece_t_bounds : ∀ i : ℕ, i ≤ 2 → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
    (|TIter i (fun _ : ℝ => 1) θ| ≤ 1) ∧
    (|TIter i Work.Construction.c2m θ| ≤ 12) ∧
    (|TIter i (fun θ : ℝ => Real.sin θ ^ 2) θ| ≤ 4) := by
  intro i hi θ hθ hθ2
  interval_cases i
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · simpa only [TIter_zero] using abs_c2m_le_twelve θ
    · simpa only [TIter_zero] using abs_sinsq_le_four θ
  · refine ⟨?_, ?_, ?_⟩
    · rw [TIter_one_const]; norm_num
    · rw [TIter_one_c2m]; exact abs_neg3_sin_two_sq_le θ
    · rw [TIter_one_sinsq]; exact abs_sinsq_le_four (2 * θ)
  · refine ⟨?_, ?_, ?_⟩
    · rw [TIter_two_const]; norm_num
    · rw [TIter_two_c2m]; exact abs_neg12_sin_two_sq_mul_cos_le θ
    · rw [TIter_two_sinsq]; exact abs_four_sin_two_sq_mul_cos_le θ

end Work.FTS_RegExport.RXT.SysAux
