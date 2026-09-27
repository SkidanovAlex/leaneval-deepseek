import Mathlib
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.sideGermDefs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The Fréchet derivative of the intrinsically perturbed charted chain

The heart of the richness hypothesis of the lead's **S3**: the derivative in the parameter of

> `t ↦ chr p (Ξ (B t) e)`

(the charted perturbed plane value, with `B : ℝ⁸ →L ℝ⁴` the block projection scaled by the weight) is
the composite of the *surjective* derivative `mfderiv (Ξ (·) e)` with `B`, conjugated by the chart
change of coordinates `tangentCoordChange`.  Since `mfderiv (Ξ (·) e)` is surjective (`ChartPert`'s
third clause) and `B` is onto its block whenever the weight does not vanish, the block map
`shiftBlockCLM` used in `Work.Drive.surjective_fderiv_pairDiff2_of_block` is onto.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

variable {Q : ℂ → CappingSpace}

/-- The differentiability order `⊤` is not zero. -/
lemma Ctop_ne_zero : Ctop ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- The scaled block projection as a continuous linear map. -/
abbrev smulUnpackFst (c : ℝ) : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  c • unpackFst

/-- The manifold derivative of a continuous linear map in the parameter is itself. -/
lemma mfderiv_clm_eq_self (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) :
    mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t = B := by
  have h : (fun t' : EuclideanSpace ℝ (Fin 8) => B t') = ⇑B := rfl
  rw [h, mfderiv_eq_fderiv]
  simpa using B.fderiv (x := t)

/-- **The block map of the derivative**: the chart change of coordinates composed with the derivative
of `Ξ (·) e` at the parameter value `v`. -/
noncomputable abbrev shiftBlockCLM (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (e : CappingSpace) (v : EuclideanSpace ℝ (Fin 4)) (p : CappingSpace) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)).comp
    (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) v)

/-- The map `t ↦ Ξ (B t) e` is `C^∞` for a continuous linear `B`. -/
lemma contMDiff_shift_clm {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace)
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    ContMDiff (𝓡 8) (𝓡 4) Ctop
      (fun t : EuclideanSpace ℝ (Fin 8) => Ξ (B t) e) := by
  have h1 : ContMDiff (𝓡 8) (𝓡 4) Ctop (fun t : EuclideanSpace ℝ (Fin 8) => B t) := B.contMDiff
  have h2 : ContMDiff (𝓡 8) (𝓡 4) Ctop (fun _ : EuclideanSpace ℝ (Fin 8) => e) :=
    contMDiff_const
  exact hΞ.2.1.comp (h1.prodMk h2)

/-- The composed map `(Ξ (·) e) ∘ B`. -/
lemma mfderiv_shift_clm_inner {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace)
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) :
    mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t
      = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)).comp B := by
  have hL : MDifferentiableAt (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t :=
    B.contMDiff.mdifferentiableAt Ctop_ne_zero
  have hG : MDifferentiableAt (𝓡 4) (𝓡 4)
      (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t) := by
    have hsm : ContMDiff (𝓡 4) (𝓡 4) Ctop (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) :=
      hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
    exact hsm.mdifferentiableAt Ctop_ne_zero
  have hcomp : mfderiv (𝓡 8) (𝓡 4)
      ((fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) ∘ (fun t' : EuclideanSpace ℝ (Fin 8) => B t')) t
      = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)).comp
          (mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t) :=
    mfderiv_comp (I := 𝓡 8) (I' := 𝓡 4) (I'' := 𝓡 4)
      (f := fun t' : EuclideanSpace ℝ (Fin 8) => B t')
      (g := fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) t hG hL
  have hfun : mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t
      = mfderiv (𝓡 8) (𝓡 4)
          ((fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) ∘
            (fun t' : EuclideanSpace ℝ (Fin 8) => B t')) t := rfl
  rw [hfun, hcomp]
  ext u
  show (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t))
      ((mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t) u)
    = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)) (B u)
  rw [mfderiv_clm_eq_self B t]
  rfl

/-- **The charted derivative of the perturbed plane value factors through the block map.** -/
lemma chart_comp_mfderiv_shift {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace)
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) (p : CappingSpace) (hsrc : Ξ (B t) e ∈ (chr p).source) :
    (tangentCoordChange (𝓡 4) (Ξ (B t) e) p (Ξ (B t) e)).comp
        (mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t)
      = (shiftBlockCLM Ξ e (B t) p).comp B := by
  rw [mfderiv_shift_clm_inner (Ξ := Ξ) hΞ e B t]
  rw [← ContinuousLinearMap.comp_assoc]

/-- **The derivative of the charted perturbed plane value in the parameter.** -/
lemma hasFDerivAt_chart_clm {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace)
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) (p : CappingSpace) (hsrc : Ξ (B t) e ∈ (chr p).source) :
    HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin 8) => chr p (Ξ (B t') e))
      ((shiftBlockCLM Ξ e (B t) p).comp B) t := by
  have hsm := contMDiff_shift_clm (Ξ := Ξ) hΞ e B
  have hmain := fderiv_chart_comp_hasFDerivAt
    (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) hsm p hsrc
  rw [chart_comp_mfderiv_shift (Ξ := Ξ) hΞ e B t p hsrc] at hmain
  exact hmain

/-- **The block map of the derivative is onto.** -/
lemma surjective_shiftBlockCLM {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace) (v : EuclideanSpace ℝ (Fin 4))
    (p : CappingSpace) (hsrc : Ξ v e ∈ (chr p).source) :
    Function.Surjective (shiftBlockCLM Ξ e v p) := by
  have hinj : Function.Injective (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)) := by
    refine Work.Drive.tangentCoordChange_injective (x := Ξ v e) (y := p) (z := Ξ v e) ⟨?_, ?_⟩
    · exact mem_extChartAt_source _
    · rw [extChartAt_source]; exact hsrc
  have hsurjT : Function.Surjective (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)).toLinearMap) (by simp)).mp hinj
  exact hsurjT.comp (hΞ.2.2 v e)


/-- **The scaled block map is onto**: for every `z` there is `u` with
`shiftBlockCLM (c • u) = z`, as soon as `c ≠ 0`. -/
lemma exists_shiftBlockCLM_smul {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace}
    (hΞ : ChartPert Q 4 Ξ) (e : CappingSpace) (v : EuclideanSpace ℝ (Fin 4))
    (p : CappingSpace) (hsrc : Ξ v e ∈ (chr p).source) (c : ℝ) (hc : c ≠ 0)
    (a : EuclideanSpace ℝ (Fin 4)) :
    ∃ u : EuclideanSpace ℝ (Fin 4), (shiftBlockCLM Ξ e v p) (c • u) = a := by
  obtain ⟨u₀, hu₀⟩ := surjective_shiftBlockCLM (Ξ := Ξ) hΞ e v p hsrc a
  refine ⟨c⁻¹ • u₀, ?_⟩
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [smul_smul, hcc, one_smul]
  exact hu₀

end

end Work.Drive
