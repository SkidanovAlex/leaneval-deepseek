import Mathlib
import Submission.Work.FatouWindow.fatouDerivSetup

/-!
# Local boundedness of the Fatou coordinate defect on compacta

`Work.FatouWindow.fatouCoord` is holomorphic on the open region `Qreg b₁ b₂`, so on any compact
subset `K ⊆ Qreg b₁ b₂` its first derivative `deriv (fatouCoord)` (hence the defect
`fatouU = deriv (fatouCoord) - 1`) and its second derivative `iteratedDeriv 2 (fatouCoord)`
are bounded.  The proof is the elementary one: `deriv` and `iteratedDeriv 2` are complex
differentiable on the open `Qreg`, hence continuous there, hence bounded on the compact `K`.

This is the compact-strip companion of the a-priori strip bounds (`fatouU_apriori_bound`,
`fatouSecondDerivBound`): it needs no smallness/integrability hypothesis on `F` beyond the
near-translation `L¹` hypothesis that produces `fatouCoord`.
-/

namespace Work.FatouWindow

open Work.FatouL1

open MandelDim Set

/-- **`Qreg b₁ b₂` is open.**  Each defining condition is of the form `0 < f` or `f < 0` for a
continuous `f`, and `b₁`, `b₂` are `Option`s, so only a finitely many of them occur. -/
private theorem isOpen_Qreg_compact (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := fun a =>
    isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := fun b =>
    isOpen_lt (by fun_prop) (by fun_prop)
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · convert isOpen_univ using 1; ext z; simp [MandelDim.Qreg]
  · convert h2 b using 1; ext z; simp [MandelDim.Qreg]
  · convert h1 a using 1; ext z; simp [MandelDim.Qreg]
  · convert (h1 a).inter (h2 b) using 1
    ext z; simp [MandelDim.Qreg]

/-- `iteratedDeriv 2 Φ = deriv (deriv Φ)` for `Φ : ℂ → ℂ`. -/
private theorem iteratedDeriv_two_eq (Φ : ℂ → ℂ) :
    iteratedDeriv 2 Φ = deriv (deriv Φ) := by
  rw [iteratedDeriv_succ', iteratedDeriv_one]

theorem fatouU_compact_bound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ MandelDim.Qreg b₁ b₂) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ B ∧
      ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ B := by
  set Φ := Work.FatouWindow.fatouCoord hadm hF with hΦ
  have hU : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg_compact b₁ b₂
  -- `Φ` is holomorphic on the open `Qreg`, hence so are `deriv Φ` and `deriv (deriv Φ)`.
  have hd : DifferentiableOn ℂ Φ (MandelDim.Qreg b₁ b₂) := (fatouCoord_spec hadm hF).1
  have hd1 : DifferentiableOn ℂ (deriv Φ) (MandelDim.Qreg b₁ b₂) := hd.deriv hU
  have hd2 : DifferentiableOn ℂ (deriv (deriv Φ)) (MandelDim.Qreg b₁ b₂) := hd1.deriv hU
  -- hence continuous, so bounded above on the compact `K`.
  have hc1 : ContinuousOn (fun z => ‖deriv Φ z‖) (MandelDim.Qreg b₁ b₂) :=
    hd1.continuousOn.norm
  have hc2 : ContinuousOn (fun z => ‖deriv (deriv Φ) z‖) (MandelDim.Qreg b₁ b₂) :=
    hd2.continuousOn.norm
  obtain ⟨B₁, hB₁⟩ := hK.bddAbove_image (hc1.mono hKsub)
  obtain ⟨B₂, hB₂⟩ := hK.bddAbove_image (hc2.mono hKsub)
  refine ⟨|B₁| + |B₂| + 1, by positivity, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : ‖deriv Φ z‖ ≤ B₁ := hB₁ (mem_image_of_mem _ hz)
    have hΦ' : Work.FatouWindow.fatouU hadm hF z = deriv Φ z - 1 := rfl
    rw [hΦ']
    have h2 : ‖deriv Φ z - 1‖ ≤ B₁ + 1 := by
      calc ‖deriv Φ z - 1‖ ≤ ‖deriv Φ z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖deriv Φ z‖ + 1 := by simp
        _ ≤ B₁ + 1 := by linarith
    have := le_abs_self B₁
    have := abs_nonneg B₂
    linarith
  · have h2 : ‖deriv (deriv Φ) z‖ ≤ B₂ := hB₂ (mem_image_of_mem _ hz)
    rw [iteratedDeriv_two_eq]
    have := abs_nonneg B₁
    linarith [h2, le_abs_self B₂]

end Work.FatouWindow
