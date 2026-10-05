import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs

/-!
# Definitions and elementary facts for the monotone radius function `rho` (node B5, `exists_rho_per`)

We build the radius function `rho τ x t = r²` of the middle chart on the left half `x ≤ 0` as a
smooth blend of three branches:

* the `ρ_h`-branch `ρe τ t (sig x)` (the level inverse of the chart), used for `x` near `-√2`;
* an explicit affine middle branch `rhoMid x = π²/32 (1 + x + √2)`, used to cross the region where
  `ρh` is no longer controlled;
* the quadratic branch `rhoQuad x = π²/4 (1 + x/√2)²`, used for `x` near `0`.

The blend uses two `Real.smoothTransition` cutoffs `wL` (turning the `ρh`-branch off) and `wR`
(turning the quadratic branch on); hence `wM = 1 - wL - wR ≥ 0`.

The reason the middle branch is needed is that `ρh` is only known to be in `(0, π²/4]` on a
*small* neighbourhood of `σ = 0`, whereas the blend must remain `≤ π²/4`; and the reason the
`ρh`-branch has to be switched off *inside* that small neighbourhood is that its `x`-derivative is
`∂_σ ρh (σ) · x`, which is positive exactly where `ρh` is controlled.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The quadratic target `π²/4·(1 + x/√2)²` of the problem statement. -/
def rhoQuad (x : ℝ) : ℝ := Real.pi ^ 2 / 4 * (1 + x / Real.sqrt 2) ^ 2

/-- The affine middle branch `π²/32·(1 + x + √2)`. -/
def rhoMid (x : ℝ) : ℝ := Real.pi ^ 2 / 32 * (1 + x + Real.sqrt 2)

/-- Left cutoff of the `ρ_h` branch: `1` for `x + √2 ≤ δ`, `0` for `x + √2 ≥ δ_A`
(so the `ρ_h` branch is used precisely on the region where `ρh ∘ sig` is controlled). -/
def wL (δ δA : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((δA - (x + Real.sqrt 2)) / (δA - δ))

/-- Right cutoff of the quadratic branch: `0` for `x + √2 ≤ u₂`, `1` for `x + √2 ≥ √2 - δ`. -/
def wR (δ u₂ : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((x + Real.sqrt 2) - u₂) / (Real.sqrt 2 - δ - u₂))

/-- The middle weight `1 - wL - wR`; it is nonnegative because `wL` and `wR` have disjoint
supports. -/
def wM (δ δA u₂ : ℝ) (x : ℝ) : ℝ := 1 - wL δ δA x - wR δ u₂ x

/-- The assembled radius function `rho τ x t`. -/
def rhoPer (ρe : ℝ → ℝ → ℝ → ℝ) (δ δA u₂ : ℝ) (τ x t : ℝ) : ℝ :=
  wL δ δA x * ρe τ t (sig x) + wM δ δA u₂ x * rhoMid x + wR δ u₂ x * rhoQuad x

/-! ## Elementary facts about the cutoffs -/

theorem wL_contDiff (δ δA : ℝ) : ContDiff ℝ 8 (wL δ δA) := by
  unfold wL; fun_prop

theorem wR_contDiff (δ u₂ : ℝ) : ContDiff ℝ 8 (wR δ u₂) := by
  unfold wR; fun_prop

theorem wM_contDiff (δ δA u₂ : ℝ) : ContDiff ℝ 8 (wM δ δA u₂) := by
  unfold wM
  exact (contDiff_const.sub (wL_contDiff δ δA)).sub (wR_contDiff δ u₂)

theorem wL_nonneg (δ δA x : ℝ) : 0 ≤ wL δ δA x := by
  unfold wL; exact Real.smoothTransition.nonneg _

theorem wR_nonneg (δ u₂ x : ℝ) : 0 ≤ wR δ u₂ x := by
  unfold wR; exact Real.smoothTransition.nonneg _

theorem wL_le_one (δ δA x : ℝ) : wL δ δA x ≤ 1 := by
  unfold wL; exact Real.smoothTransition.le_one _

theorem wR_le_one (δ u₂ x : ℝ) : wR δ u₂ x ≤ 1 := by
  unfold wR; exact Real.smoothTransition.le_one _

theorem wL_eq_one {δ δA x : ℝ} (h : δ < δA) (hx : x + Real.sqrt 2 ≤ δ) :
    wL δ δA x = 1 := by
  unfold wL
  rw [Real.smoothTransition.eq_one_iff_one_le]
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem wR_eq_one {δ u₂ x : ℝ} (h : u₂ < Real.sqrt 2 - δ) (hx : -δ ≤ x) :
    wR δ u₂ x = 1 := by
  unfold wR
  rw [Real.smoothTransition.eq_one_iff_one_le]
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem wL_eq_zero {δ δA x : ℝ} (h : δ < δA) (hx : δA ≤ x + Real.sqrt 2) :
    wL δ δA x = 0 := by
  unfold wL
  rw [Real.smoothTransition.zero_iff_nonpos]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem wR_eq_zero {δ u₂ x : ℝ} (hu : u₂ < Real.sqrt 2 - δ) (hx : x + Real.sqrt 2 ≤ u₂) :
    wR δ u₂ x = 0 := by
  unfold wR
  rw [Real.smoothTransition.zero_iff_nonpos]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem wL_pos_of {δ δA x : ℝ} (h : δ < δA) (hx : x + Real.sqrt 2 < δA) :
    0 < wL δ δA x := by
  unfold wL
  apply Real.smoothTransition.pos_of_pos
  exact div_pos (by linarith) (by linarith)

theorem wR_pos_of {δ u₂ x : ℝ} (hu : u₂ < Real.sqrt 2 - δ) (hx : u₂ < x + Real.sqrt 2) :
    0 < wR δ u₂ x := by
  unfold wR
  apply Real.smoothTransition.pos_of_pos
  exact div_pos (by linarith) (by linarith)

theorem wL_antitone {δ δA : ℝ} (h : δ < δA) : Antitone (wL δ δA) := by
  have hf : Antitone (fun x : ℝ => (δA - (x + Real.sqrt 2)) / (δA - δ)) := by
    intro x y hxy
    rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < δA - δ)]
    linarith
  exact Real.smoothTransition.monotone.comp_antitone hf

theorem wR_monotone {δ u₂ : ℝ} (h : u₂ < Real.sqrt 2 - δ) : Monotone (wR δ u₂) := by
  have hf : Monotone (fun x : ℝ => ((x + Real.sqrt 2) - u₂) / (Real.sqrt 2 - δ - u₂)) := by
    intro x y hxy
    rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < Real.sqrt 2 - δ - u₂)]
    linarith
  exact Real.smoothTransition.monotone.comp hf

/-- The two cutoffs have disjoint supports (when `δ_A < u₂`), so their sum is at most `1`. -/
theorem wL_add_wR_le_one {δ δA u₂ : ℝ} (hδ : δ < δA) (hu : δA < u₂)
    (hu' : u₂ < Real.sqrt 2 - δ) (x : ℝ) :
    wL δ δA x + wR δ u₂ x ≤ 1 := by
  rcases lt_or_ge (x + Real.sqrt 2) δA with hx | hx
  · rw [wR_eq_zero hu' (by linarith)]
    linarith [wL_le_one δ δA x]
  · rw [wL_eq_zero hδ hx]
    linarith [wR_le_one δ u₂ x]

theorem wM_nonneg {δ δA u₂ : ℝ} (hδ : δ < δA) (hu : δA < u₂)
    (hu' : u₂ < Real.sqrt 2 - δ) (x : ℝ) :
    0 ≤ wM δ δA u₂ x := by
  unfold wM
  linarith [wL_add_wR_le_one hδ hu hu' x]

theorem wM_le_one {δ δA u₂ x : ℝ} : wM δ δA u₂ x ≤ 1 := by
  unfold wM
  linarith [wL_nonneg δ δA x, wR_nonneg δ u₂ x]

theorem wM_eq_one {δ δA u₂ x : ℝ} (hδ : δ < δA) (hu : u₂ < Real.sqrt 2 - δ)
    (hu₁ : δA ≤ x + Real.sqrt 2) (hu₂ : x + Real.sqrt 2 ≤ u₂) : wM δ δA u₂ x = 1 := by
  unfold wM
  rw [wL_eq_zero hδ hu₁, wR_eq_zero hu hu₂]
  ring

end Work.RPB.B5
