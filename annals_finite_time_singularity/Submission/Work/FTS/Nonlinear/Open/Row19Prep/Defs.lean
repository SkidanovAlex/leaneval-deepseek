/-
# Row 19 (`N₃^{**} = -2α·V(Φ̃_*)·D_zF_*`): vocabulary for the pointwise `ℋ⁴`-estimates

The piece is `N₃^{**}` (`Work.FTS.Nonlin.N3ss`), whose defining factors are

* the star coefficient `V(Φ̃_*) = Vop (PhiTs α Φs)` (`StarPkgo2.VzW` supplies
  `WlInfMem α 4 (((z+1)/z)·V(Φ̃_*))` with norm `≤ Cs·α` — the *weighted* form, which is exactly
  what makes the row true), and
* the profile `D_zF_* = Gs α = (α/c(α))·Γ(θ)·H(z)`, `H(z) = 2z(1-z)/(1+z)³`
  (`Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz`).

Writing `A := ((z+1)/z)·V(Φ̃_*)` and `V = (z/(1+z))·A` one gets the factorisation

  `V(Φ̃_*)·D_zF_* = (α/c(α)) · A(z,θ) · Γ(θ) · H₂(z)`,
  `H₂(z) := (z/(1+z))·H(z) = 2z²(1-z)/(1+z)⁴`

(the `Hz`-profile multiplied by the `z/(1+z)` of the `A`-decomposition, so that
`H₂ = z²·Ψ` with `Ψ(z) = 2(1-z)/(1+z)⁴ = 4/(1+z)⁴ - 2/(1+z)³` and `H₂` vanishes to order `2`
at the origin, which is exactly what cancels the `z^{-2}` of the weight `w(z) = (1+z)²/z²`).

The two pointwise families that `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open` consumes are

* (`η`-family) `|(1+z)·w(z)·z^m·∂_z^m Z| ≤ C·α·Λ`, `m ≤ 4`;
* (`γ`-family) `|(1+z)·w(z)·z^l·∂_z^l D_θ^i Z| ≤ C·α·Λ·Φ(θ)`, `1 ≤ i`, `l+i ≤ 4`,

for `Z = α·Γ·(A·H₂)`, where `Λ ≥ |A|_{𝒲^{4,∞}}`; the hypotheses produced by the two families are
precisely those of `wtoHQ_of_pointwise_open`, which then yields both the `ℋ⁴`-honesty of
`V(Φ̃_*)·D_zF_*` and its norm bound `≤ 10^10·30·C·α·Λ`.

This file carries the vocabulary and the elementary facts (the two families themselves are
`Row19Prep.EtaPt` / `Row19Prep.GamPt`, and the radial factor bound is
`Row19Prep.H2bBound`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The vocabulary -/

/-- The radial factor `H₂(z) = 2z²(1-z)/(1+z)⁴ = (z/(1+z))·H(z)` of the row-19 piece. -/
def H2b (z : ℝ) : ℝ := 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4

/-- `H₂ = z²·Ψ` with `Ψ(z) = 2(1-z)/(1+z)⁴ = 4/(1+z)⁴ - 2/(1+z)³`; the `z²` is what makes
`H₂·(1+z)·w(z)·z^{m-2}` bounded at the origin. -/
def Psi (z : ℝ) : ℝ := 2 * (1 - z) / (1 + z) ^ 4

/-- The angular weight `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}` of the `γ`-family estimate; it is
`≤ 2` on `Iθ` and is the reciprocal of the `𝒲^{l,∞}`-weight `sin(2θ)^{-α/5}/(α+sin 2θ)`. -/
def PhiA (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- The reciprocal of `PhiA`, i.e. the angular weight of the `𝒲^{l,∞}`-norm. -/
def Wang (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))

/-- The angular factor `Γ` lifted to a function on the quadrant. -/
def GamF (α : ℝ) : ℝ → ℝ → ℝ := fun _ θ => Work.Spaces.Gam α θ

/-- The (un-normalised) row-19 product `α·Γ·(A·H₂)`: `V(Φ̃_*)·D_zF_* = (1/c(α))·Zf α A`. -/
def Zf (α : ℝ) (A : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => α * Work.Spaces.Gam α θ * (A z θ * H2b z)

@[simp] theorem GamF_apply (α z θ : ℝ) : GamF α z θ = Work.Spaces.Gam α θ := rfl

@[simp] theorem Zf_apply (α : ℝ) (A : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Zf α A z θ = α * Work.Spaces.Gam α θ * (A z θ * H2b z) := rfl

/-! ## Elementary facts about the radial factor -/

theorem H2b_eq_sq_mul (z : ℝ) : H2b z = z ^ 2 * Psi z := by
  rw [H2b, Psi]; ring

theorem Psi_eq (z : ℝ) (hz : 1 + z ≠ 0) :
    Psi z = 4 / (1 + z) ^ 4 - 2 / (1 + z) ^ 3 := by
  rw [Psi]
  field_simp
  ring

/-- `|1 - z| ≤ 1 + z` for `z ≥ 0`. -/
theorem abs_one_sub_le {z : ℝ} : |1 - z| ≤ 1 + z ↔ 0 ≤ z := by
  rw [abs_sub_le_iff]
  constructor
  · intro h; linarith [h.1]
  · intro h; exact ⟨by linarith, by linarith⟩

/-- `|H₂(z)| ≤ 2z²/(1+z)³` (the `z²`-vanishing at the origin, and decay `~1/z` at infinity). -/
theorem abs_H2b_le {z : ℝ} (hz : 0 ≤ z) : |H2b z| ≤ 2 * z ^ 2 / (1 + z) ^ 3 := by
  have h1 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have h3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have h2 : |1 - z| ≤ 1 + z := abs_one_sub_le.mpr hz
  have hH : |H2b z| = 2 * z ^ 2 * |1 - z| / (1 + z) ^ 4 := by
    rw [H2b, abs_div, abs_of_pos h1, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (sq_nonneg z)]
  rw [hH]
  have h4 : 2 * z ^ 2 * |1 - z| ≤ 2 * z ^ 2 * (1 + z) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc 2 * z ^ 2 * |1 - z| / (1 + z) ^ 4
      ≤ 2 * z ^ 2 * (1 + z) / (1 + z) ^ 4 := div_le_div_of_nonneg_right h4 h1.le
    _ = 2 * z ^ 2 / (1 + z) ^ 3 := by
        rw [div_eq_div_iff (ne_of_gt h1) (ne_of_gt h3)]
        ring

/-- The weighted bound used at order `0`: `(1+z)·w(z)·|H₂(z)| ≤ 2`. -/
theorem one_add_mul_w_mul_abs_H2b_le {z : ℝ} (hz : 0 < z) :
    (1 + z) * Work.Spaces.w z * |H2b z| ≤ 2 := by
  have h1 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |1 - z| ≤ 1 + z := abs_one_sub_le.mpr hz.le
  have h3 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  have hH : |H2b z| = 2 * z ^ 2 * |1 - z| / (1 + z) ^ 4 := by
    rw [H2b, abs_div, abs_of_pos h1, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (sq_nonneg z)]
  have h4 : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * (2 * z ^ 2 * |1 - z| / (1 + z) ^ 4)
      = 2 * |1 - z| / (1 + z) := by
    field_simp
  rw [h3, hH, h4]
  rw [div_le_iff₀ hz1]
  linarith

theorem Gam_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1

theorem Gam_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem PhiA_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ PhiA α θ := by
  have h1 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  rw [PhiA]
  exact mul_nonneg (by linarith) (Real.rpow_nonneg h1 _)

theorem PhiA_pos {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < PhiA α θ := by
  have h1 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [PhiA]
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos h1 _)

theorem PhiA_le_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    PhiA α θ ≤ 2 := by
  have h1 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have h2 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h3 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one h1 h2 (by linarith)
  have h4 : (Real.sin (2 * θ)) ^ (α / 5) ≥ 0 := Real.rpow_nonneg h1 _
  rw [PhiA]
  nlinarith

theorem Wang_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wang α θ := by
  have h1 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  rw [Wang]
  exact div_nonneg (Real.rpow_nonneg h1 _) (by linarith)

theorem PhiA_mul_Wang {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    PhiA α θ * Wang α θ = 1 := by
  have h1 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h2 : α + Real.sin (2 * θ) ≠ 0 := by linarith
  have h3 : (Real.sin (2 * θ)) ^ (α / 5) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1 _)
  rw [PhiA, Wang]
  field_simp
  rw [← Real.rpow_add h1, show α / 5 + -(α / 5) = 0 by ring, Real.rpow_zero]

/-- `α·Γ(θ) ≤ Φ(θ)`: the factor `α` of `∂_θΓ = (2α/3)·Γ·(cos²-2sin²)` is absorbed by the
`(α + sin 2θ)` of the weight. -/
theorem alpha_mul_Gam_le_PhiA {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : α * Work.Spaces.Gam α θ ≤ PhiA α θ := by
  have h1 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  -- `sin θ cos²θ ≤ sin 2θ`
  have h2 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) := by
    have hm : Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ := by ring
    have hm2 : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
      rw [Real.sin_two_mul]; ring
    have hsc : 0 ≤ Real.sin θ * Real.cos θ := mul_nonneg hs0 hc0
    rw [hm, hm2]
    nlinarith [hsc, hc1, hc0]
  have h3 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by positivity
  have h4 : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 3) := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow h3 h2 (by linarith)
  have h5 : (Real.sin (2 * θ)) ^ (α / 3) ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, Real.zero_rpow (by linarith : α / 3 ≠ 0),
        Real.zero_rpow (by linarith : α / 5 ≠ 0)]
    · exact Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) (by linarith)
  have h6 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg h1 _
  rw [PhiA]
  nlinarith [h4, h5, h6, hα]

/-! ## The two degenerate factors: `z`-derivatives kill a `θ`-only factor, and conversely -/

/-- `∂_z^c` of a function of `θ` alone is `0` for `c ≥ 1`. -/
theorem pzIter_theta_only (a : ℝ → ℝ) (c : ℕ) :
    Work.Spaces.pzIter c (fun z θ => a θ) = fun z θ => if c = 0 then a θ else 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      show deriv (fun z' : ℝ => (if c = 0 then a θ else (0 : ℝ))) z
        = (if c + 1 = 0 then a θ else 0)
      rw [deriv_const]
      simp

/-- `D_θ^{n+1}` of a function of `z` alone is `0`. -/
theorem DthIter_succ_z_only (φ : ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter (n + 1) (fun z θ => φ z) = fun (_ : ℝ) (_ : ℝ) => (0 : ℝ) := by
  induction n with
  | zero =>
      funext z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth]
      simp [deriv_const]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by ring, Work.Spaces.DthIter_succ, ih]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.pth]
      simp [deriv_const]

/-- `D_θ^n` of a function of `z` alone is `0` for `n ≥ 1`. -/
theorem DthIter_z_only (φ : ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => φ z)
      = if n = 0 then (fun z θ => φ z) else fun (_ : ℝ) (_ : ℝ) => (0 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [if_neg (Nat.succ_ne_zero m)]
    exact DthIter_succ_z_only φ m

end Work.FTS.Nonlinear.Open.Row19Prep
