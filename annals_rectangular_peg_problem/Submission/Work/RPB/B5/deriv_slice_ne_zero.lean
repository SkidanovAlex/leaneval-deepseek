import Mathlib
import Submission.Work.RPB.B5.chartLev_inverse
import Submission.Work.RPB.B5.chart_C12

/-!
# The level inverse of the chord chart is a local reparametrisation

`ρh` is the inverse of the `ρ`-slice of the level function `chartLev W τ t ρ = K₀(W τ t ρ) + 1`
of the chord annulus, i.e. `chartLev W τ t (ρh τ t σ) = -σ`.  Differentiating this identity in
`σ` and applying the chain rule,

`deriv (fun ρ => chartLev W τ t ρ) (ρh τ t σ) * deriv (fun s => ρh τ t s) σ = -1`,

so that in particular `deriv (fun s => ρh τ t s) σ ≠ 0`: no derivative is needed of the level
function beyond its mere differentiability, which is the content of this file.
-/

open Set Filter
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The single-variable slice `σ ↦ f (τ, t, σ)` of a `C^n` function on the slab
`Icc 0 1 ×ˢ univ ×ˢ Ioo (-ε) ε` is `C^n` on `Ioo (-ε) ε`. -/
lemma contDiffOn_slice_third {f : ℝ × (ℝ × ℝ) → ℝ} {n : ℕ∞ω} {ε : ℝ}
    (hf : ContDiffOn ℝ n f (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ContDiffOn ℝ n (fun σ : ℝ => f (τ, t, σ)) (Set.Ioo (-ε) ε) := by
  have hφ : ContDiffOn ℝ n (fun s : ℝ => ((τ, t, s) : ℝ × (ℝ × ℝ))) (Set.Ioo (-ε) ε) := by
    fun_prop
  have h := hf.comp hφ (fun s hs => ⟨hτ, Set.mem_univ t, hs⟩)
  exact h.congr (fun σ _ => rfl)

theorem deriv_slice_ne_zero (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ ε δ κ : ℝ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-ε) ε,
      Work.RPB.B5.chartLev W τ t (ρh τ t σ) = -σ)
    (hconf : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Icc (-κ) κ, |ρh τ t σ| < δ)
    (hδρ : δ < ρ₀) (hκε : κ ≤ ε) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      deriv (fun s : ℝ => ρh τ t s) σ ≠ 0 := by
  intro τ hτ t σ hσ
  -- `σ` lies in the interval where the level identity holds
  have hσε : σ ∈ Set.Ioo (-ε) ε :=
    ⟨by linarith [hσ.1, hκε], by linarith [hσ.2, hκε]⟩
  -- and `ρh τ t σ` in the interval where the chart is smooth
  have habs : |ρh τ t σ| < δ :=
    hconf τ hτ t σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  have hρmem : ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀ := by
    rw [Set.mem_Ioo]
    rw [abs_lt] at habs
    exact ⟨by linarith [habs.1, hδρ], by linarith [habs.2, hδρ]⟩
  -- differentiability of the two slices
  have hρh_slice : ContDiffOn ℝ 12 (fun s : ℝ => ρh τ t s) (Set.Ioo (-ε) ε) := by
    have h := contDiffOn_slice_third (f := fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      hρh hτ t
    simpa only using h
  have hlev_slice : ContDiffOn ℝ 12 (fun ρ : ℝ => chartLev W τ t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
    chartLev_slice_contDiffOn_C12 hW τ t hτ
  have hf : DifferentiableAt ℝ (fun s : ℝ => ρh τ t s) σ :=
    (hρh_slice.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hσε)
  have hg : DifferentiableAt ℝ (fun ρ : ℝ => chartLev W τ t ρ) (ρh τ t σ) :=
    (hlev_slice.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hρmem)
  -- the chain rule
  have hchain : HasDerivAt (fun s : ℝ => chartLev W τ t (ρh τ t s))
      (deriv (fun ρ : ℝ => chartLev W τ t ρ) (ρh τ t σ)
        * deriv (fun s : ℝ => ρh τ t s) σ) σ :=
    hg.hasDerivAt.comp σ hf.hasDerivAt
  -- the composition is `-σ` near `σ`
  have heq : (fun s : ℝ => chartLev W τ t (ρh τ t s)) =ᶠ[𝓝 σ] (fun s : ℝ => -s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hσε] with s hs
    exact hρhl τ hτ t s hs
  have h' : HasDerivAt (fun s : ℝ => -s)
      (deriv (fun ρ : ℝ => chartLev W τ t ρ) (ρh τ t σ)
        * deriv (fun s : ℝ => ρh τ t s) σ) σ :=
    hchain.congr_of_eventuallyEq heq.symm
  have huniq : (-1 : ℝ) = deriv (fun ρ : ℝ => chartLev W τ t ρ) (ρh τ t σ)
      * deriv (fun s : ℝ => ρh τ t s) σ :=
    (hasDerivAt_neg σ).unique h'
  intro hzero
  rw [hzero, mul_zero] at huniq
  norm_num at huniq

end Work.RPB.B5

end
