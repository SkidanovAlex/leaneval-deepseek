import Mathlib
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.chain_v9_geom
import Submission.Work.Repel.exists_local_inv
import Submission.Work.Repel.invFunOn_differentiableOn
import Submission.Work.Repel.exists_open_injOn_of_compact

namespace Work.Repel

open MandelDim Set Metric Filter Topology

/-- **Differentiability of the level-1 source map `(φ₁|Dsm)⁻¹` on the image of `Dsm`.**

`V.uOf = Function.invFunOn V.P₁.φ V.Sm1` is the inverse of the level-1 perturbed Fatou
coordinate `φ₁ = V.P₁.φ` on the closed disc `Sm1 = Dsm (sgn·η₁)`, where `φ₁` is a local
biholomorphism (its derivative is nonvanishing there, `Work.Repel.deriv_phi_ne_zero`) and is
injective (`V.Sm1_injOn`).  The closed disc is not open, so the inverse function theorem is not
applied to `Sm1` directly: by `Work.Repel.exists_open_injOn_of_compact` the injectivity of `φ₁`
on the compact disc extends to an open neighbourhood `U ⊇ Sm1`, and on `φ₁ '' U` the inverse
`Function.invFunOn φ₁ U` is holomorphic (`Work.Repel.invFunOn_differentiableOn`).  On `φ₁ '' Sm1`
that inverse coincides with `uOf` (both are points of `U` mapping to the same value, and `φ₁` is
injective on `U`), which transfers differentiability. -/
theorem uOf_differentiableOn (V : Work.Repel.V10) :
    DifferentiableOn ℂ V.uOf (V.P₁.φ '' V.Sm1) := by
  -- the closed disc `Sm1` is compact
  have hK : IsCompact V.Sm1 := by
    rw [V10.Sm1]
    split <;> exact isCompact_closedBall _ _
  have hzD : ∀ z ∈ V.Sm1, z ∈ MandelDim.Dsm V.η₁ ∪ MandelDim.Dsm (-V.η₁) := by
    intro z hz
    rw [V10.Sm1] at hz
    split at hz
    · exact Or.inl hz
    · exact Or.inr hz
  -- `φ₁` has nonvanishing derivative on the disc
  have hloc : ∀ z ∈ V.Sm1, deriv V.P₁.φ z ≠ 0 :=
    fun z hz => deriv_phi_ne_zero V.P₁ V.hη₁pos (hzD z hz)
  -- injectivity on the compact disc extends to an open neighbourhood
  obtain ⟨U, hUopen, hKU, hUinj⟩ :=
    exists_open_injOn_of_compact V.P₁.Dφ_open hK V.Sm1_sub_Dφ V.P₁.φ_holo V.Sm1_injOn hloc
  set U' : Set ℂ := U ∩ V.P₁.Dφ with hU'def
  have hU'open : IsOpen U' := hUopen.inter V.P₁.Dφ_open
  have hKU' : V.Sm1 ⊆ U' := fun z hz => ⟨hKU hz, V.Sm1_sub_Dφ hz⟩
  have hU'inj : Set.InjOn V.P₁.φ U' := hUinj.mono Set.inter_subset_left
  have hφdiff : DifferentiableOn ℂ V.P₁.φ U' := V.P₁.φ_holo.mono Set.inter_subset_right
  -- the inverse on `U'` is holomorphic on `φ₁ '' U'`
  have hinv : DifferentiableOn ℂ (Function.invFunOn V.P₁.φ U') (V.P₁.φ '' U') :=
    invFunOn_differentiableOn hU'open hU'inj hφdiff
  have himgsub : V.P₁.φ '' V.Sm1 ⊆ V.P₁.φ '' U' := Set.image_mono hKU'
  have hdiffsub : DifferentiableOn ℂ (Function.invFunOn V.P₁.φ U') (V.P₁.φ '' V.Sm1) :=
    hinv.mono himgsub
  -- `uOf` agrees with that inverse on `φ₁ '' Sm1`
  have hEqOn : Set.EqOn V.uOf (Function.invFunOn V.P₁.φ U') (V.P₁.φ '' V.Sm1) := by
    intro y hy
    obtain ⟨z, hzS, rfl⟩ := hy
    have h1 := V.uOf_spec ⟨z, hzS, rfl⟩
    have h2 := Function.invFunOn_pos (s := U') (f := V.P₁.φ)
      ⟨z, ⟨hKU hzS, V.Sm1_sub_Dφ hzS⟩, rfl⟩
    exact hU'inj ⟨hKU h1.1, V.Sm1_sub_Dφ h1.1⟩ h2.1 (by rw [h1.2, h2.2])
  intro ζ hζ
  have heq : V.uOf =ᶠ[𝓝[V.P₁.φ '' V.Sm1] ζ] Function.invFunOn V.P₁.φ U' := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hEqOn hy
  exact (heq.differentiableWithinAt_iff (hEqOn hζ)).mpr (hdiffsub ζ hζ)

end Work.Repel
