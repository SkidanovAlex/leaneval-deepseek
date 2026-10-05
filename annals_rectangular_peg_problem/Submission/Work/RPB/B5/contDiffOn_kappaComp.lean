import Mathlib
import Submission.Work.RPB.Defs

namespace Work.RPB.B5

open scoped ContDiff
open Manifold Complex Real

set_option autoImplicit false

/-- Smoothness of the reduced-coordinate composition.  If the uncurried chart
`(τ,t,ρ) ↦ W τ t ρ` is `C⁸` on the slab `[0,1] × ℝ × (-ρ₀,ρ₀)`, the level inversion
`(τ,t,σ) ↦ ρh τ t σ` is `C⁸` on `[0,1] × ℝ × (-κ,κ)`, and the latter takes values in the
former's slab, then `z ↦ uproj (W z.1 z.2.1 (ρh z.1 z.2.1 z.2.2))` is `C⁸` on the
`κ`-slab.

`uproj p = e^{i q₂}(p₁ + i q₁)` is `C^∞` on `PS = ℝ⁴`, so the only content is the chain
rule: compose `uproj ∘ W` (on the `ρ₀`-slab) with the `C⁸` map
`z ↦ (z.1, z.2.1, ρh z.1 z.2.1 z.2.2)` (on the `κ`-slab), whose image lies in the
`ρ₀`-slab by `hρhv`. -/
theorem contDiffOn_kappaComp (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (κ : ℝ)
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) :
    ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPV.uproj (W z.1 z.2.1 (ρh z.1 z.2.1 z.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := by
  -- `uproj` is `C⁸`
  have huproj : ContDiff ℝ 8 (fun x : Work.RPV.PS => Work.RPV.uproj x) := by
    unfold Work.RPV.uproj
    have h12 : ContDiff ℝ 8 (fun p : Work.RPV.PS => ((p.1.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.snd)
    have h11 : ContDiff ℝ 8 (fun p : Work.RPV.PS => ((p.1.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.fst)
    have h21 : ContDiff ℝ 8 (fun p : Work.RPV.PS => ((p.2.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.snd.fst)
    exact ((Complex.contDiff_exp.comp (h12.mul contDiff_const))).mul
      (h21.add (h11.mul contDiff_const))
  -- `ρh`, uncurried, is `C⁸` on the `κ`-slab (restated with the projection out front)
  have hρh' : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := hρh
  -- the `C⁸` map `z ↦ (z.1, z.2.1, ρh z.1 z.2.1 z.2.2)`
  have hg : ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1, ρh z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := by
    refine ContDiffOn.prodMk (by fun_prop) (ContDiffOn.prodMk (by fun_prop) ?_)
    · exact hρh'
  -- its image lies in the `ρ₀`-slab
  have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1, ρh z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    rintro ⟨τ, t, σ⟩ ⟨hτ, -, hσ⟩
    exact ⟨hτ, Set.mem_univ _, hρhv τ hτ t σ hσ⟩
  -- hence `W` itself is `C⁸` along that map
  have hinner : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 (ρh z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) :=
    hW.comp hg hmap
  -- and composing with the globally smooth `uproj` gives the claim
  exact huproj.comp_contDiffOn hinner

end Work.RPB.B5
