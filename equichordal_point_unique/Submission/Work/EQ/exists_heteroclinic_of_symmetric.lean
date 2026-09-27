import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_near_A1
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.HeteroConn

/-! ## The curve is a heteroclinic connection (Rychlik L5, Thm 2)

The construction of the connection `Γ` and all its properties are in
`Submission.Work.EQ.HeteroConn`; here they are assembled into the final statement. -/

namespace Work.EQ

open Complex Filter
open scoped Topology

noncomputable section

variable {a : ℝ}

/-- **The curve is a heteroclinic connection (Rychlik L5, Thm 2).** The upper arc of a
symmetric normalised equichordal curve, parametrised by the linearising parameter of any
stable germ, is a real heteroclinic connection. -/
theorem exists_heteroclinic_of_symmetric {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) :
    ∃ Γ : ℝ → ℂ, IsHeteroclinic a h r Γ := by
  obtain ⟨ε, hε, hεc, hε₁, hε₂, hε₃⟩ := germ_threshold ha0 ha1 hC hs₁ hs₂ hh
  refine ⟨heteroGamma a h ε, hh, ?_, ?_, ?_, ?_, ?_⟩
  · exact heteroGamma_continuousOn ha0 ha1 hC hs₁ hs₂ hεc hε hε₁ hε₂ hε₃
  · intro t ht
    exact (heteroGamma_mem_arc ha0 ha1 hC hs₁ hs₂ hε hε₂ hε₃ ht).2
  · intro t ht
    exact heteroGamma_step ha0 ha1 hC hs₁ hs₂ hε hε₁ hε₂ hε₃ ht
  · exact ⟨ε, hε, fun t _ htε => heteroGamma_eq_germPt htε⟩
  · exact heteroGamma_symm ha0 ha1 hC hs₁ hs₂ hh hε hε₁ hε₂ hε₃

end

end Work.EQ
