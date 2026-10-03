import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# The ends of the Écalle cylinder: shared definitions

`MandelDim.FatouEnds` (interface `Submission/Work/Interfaces/Fatou.lean`) is the statement that a
Fatou coordinate `Φ` of a near-translation `F` on Shishikura's region `Qreg b₁ b₂` behaves like
`z/ρ + c` at the two ends `Im z → ±∞`, whenever `F` is exponentially close to the translation
`z ↦ z + ρ` there.

This file fixes the vocabulary of the argument:

* `devFn Φ ρ = Φ · - ·/ρ`: the deviation whose limit is the constant `c`;
* `DiffEst R₁ C₁`: the `C₁`-part of Shishikura's derivative estimate A.2.4(i), with the universal
  constants `R₁, C₁` extracted (so that `Work.FatouCH.fatouEnds` can use the numerical form
  `‖Φ' z - 1/v z‖ ≤ C₁ (1/R² + ‖v' z‖)` without carrying the interface statement around);
* `Kc C₁ M`: the constant in the pointwise bound `psi (Kc C₁ M) κ T` on `‖deriv (devFn Φ ρ) z‖`;
* `psi`, `Psi`: the pointwise bound and its integral bound at height `T`.
-/

namespace Work.FatouCH.Ends

open Set Metric Complex
open scoped Topology

noncomputable section

/-- The deviation of a Fatou coordinate from the linear coordinate `z/ρ`. -/
def devFn (Φ : ℂ → ℂ) (ρ : ℂ) : ℂ → ℂ := fun z => Φ z - z / ρ

@[simp] theorem devFn_apply (Φ : ℂ → ℂ) (ρ : ℂ) (z : ℂ) :
    devFn Φ ρ z = Φ z - z / ρ := rfl

/-- The `C₁`-half of Shishikura's lemma A.2.4(i), with the universal constants made explicit. -/
def DiffEst (R₁ C₁ : ℝ) : Prop :=
  ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R →
    DifferentiableOn ℂ Φ (ball z₀ R) → Set.InjOn Φ (ball z₀ R) →
    DifferentiableOn ℂ v (ball z₀ R) → (∀ z ∈ ball z₀ R, ‖v z - 1‖ < 1 / 4) →
    (∀ z ∈ ball z₀ R, z + v z ∈ ball z₀ R → Φ (z + v z) = Φ z + 1) →
    ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z₀‖)

/-- `MandelDim.FatouDerivEstimate` yields universal `R₁, C₁ > 0` with `DiffEst R₁ C₁`. -/
theorem exists_diffEst (hD : MandelDim.FatouDerivEstimate) :
    ∃ R₁ C₁ : ℝ, 0 < R₁ ∧ 0 < C₁ ∧ DiffEst R₁ C₁ := by
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, -, hmain⟩ := hD
  exact ⟨R₁, C₁, hR₁, hC₁, fun Φ v z₀ R hR hΦ hinj hv hv1 hAbel =>
    (hmain Φ v z₀ R hR hΦ hinj hv hv1 hAbel).1⟩

/-- The constant of the pointwise derivative bound, in terms of `C₁` and the tail amplitude `M`. -/
def Kc (C₁ M : ℝ) : ℝ := 256 * C₁ + 16 * C₁ * |M| + 16 * |M|

theorem Kc_nonneg {C₁ M : ℝ} (hC₁ : 0 ≤ C₁) : 0 ≤ Kc C₁ M := by
  have h : (0 : ℝ) ≤ |M| := abs_nonneg M
  simp only [Kc]
  nlinarith [hC₁, h]

/-- Pointwise bound for `‖deriv (devFn Φ ρ) z‖` at height `T`. -/
def psi (K κ T : ℝ) : ℝ := 2 * K / T ^ 2 + 2 * K * Real.exp (-(κ * T / 8))

/-- The integral bound of `psi` over `[T₁, T₂]`. -/
def Psi (K κ T : ℝ) : ℝ := 2 * K / T + 16 * K / κ * Real.exp (-(κ * T / 8))

/-- The derivative of `devFn Φ ρ`, where `Φ` is differentiable. -/
theorem deriv_devFn {Φ : ℂ → ℂ} {ρ z : ℂ} (hΦ : DifferentiableAt ℂ Φ z) :
    deriv (devFn Φ ρ) z = deriv Φ z - 1 / ρ := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => w / ρ) z :=
    (differentiableAt_id (𝕜 := ℂ) (x := z)).div_const ρ
  have h1 : devFn Φ ρ = Φ - fun w : ℂ => w / ρ := rfl
  rw [h1, deriv_sub (f := Φ) (g := fun w : ℂ => w / ρ) hΦ hg, deriv_div_const]
  simp

/-- The region `MandelDim.Qreg b₁ b₂` is open. -/
theorem isOpen_Qreg (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : IsOpen {z : ℂ | ∀ a ∈ b₁, -|(z - a).im| < (z - a).re} := by
    rcases b₁ with _ | a
    · simp
    · have hc : Continuous (fun z : ℂ => -|(z - a).im| - (z - a).re) := by fun_prop
      have hopen : IsOpen {z : ℂ | -|(z - a).im| - (z - a).re < 0} :=
        isOpen_lt hc continuous_const
      convert hopen using 1
      ext z; simp
  have h2 : IsOpen {z : ℂ | ∀ b ∈ b₂, (z - b).re < |(z - b).im|} := by
    rcases b₂ with _ | b
    · simp
    · have hc : Continuous (fun z : ℂ => (z - b).re - |(z - b).im|) := by fun_prop
      have hopen : IsOpen {z : ℂ | (z - b).re - |(z - b).im| < 0} :=
        isOpen_lt hc continuous_const
      convert hopen using 1
      ext z; simp
  have hfinal : IsOpen (({z : ℂ | ∀ a ∈ b₁, -|(z - a).im| < (z - a).re} : Set ℂ) ∩
      {z : ℂ | ∀ b ∈ b₂, (z - b).re < |(z - b).im|}) := h1.inter h2
  convert hfinal using 1
  ext z; simp [MandelDim.Qreg]

/-- `devFn Φ ρ` is differentiable wherever `Φ` is. -/
theorem differentiableAt_devFn {Φ : ℂ → ℂ} {ρ z : ℂ} (h : DifferentiableAt ℂ Φ z) :
    DifferentiableAt ℂ (devFn Φ ρ) z :=
  h.sub ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const ρ)

/-- Mean value inequality on a segment for a complex function of one variable. -/
theorem segment_bound {B : ℂ → ℂ} {ψ : ℝ} {a b : ℂ}
    (hdiff : ∀ u ∈ segment ℝ a b, DifferentiableAt ℂ B u)
    (hbound : ∀ u ∈ segment ℝ a b, ‖deriv B u‖ ≤ ψ) :
    ‖B b - B a‖ ≤ ψ * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_segment a b)
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

/-- Triangle inequality in the shape needed for a nested decomposition. -/
theorem norm_add_add_le' {E : Type*} [SeminormedAddGroup E] (a b c : E) :
    ‖a + (b + c)‖ ≤ ‖a‖ + (‖b‖ + ‖c‖) := by
  calc ‖a + (b + c)‖ ≤ ‖a‖ + ‖b + c‖ := norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + ‖c‖) := by
        have := norm_add_le b c
        linarith

end

end Work.FatouCH.Ends
