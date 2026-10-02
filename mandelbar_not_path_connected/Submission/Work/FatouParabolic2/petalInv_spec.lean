import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic2

open Set Filter
open scoped Topology

set_option linter.unusedVariables false

/-- **The canonical inverse Fatou coordinate of petal data on a horizontal strip tail.**  Let `pd`
be petal data at the parabolic fixed point `z₀` of the holomorphic map `F`, with the strip-image
property `pd.image_strip`.  For every height `B > 0` there is a level `C` such that the inverse
`Φ := Function.invFunOn pd.φa pd.Pa` of the Fatou coordinate satisfies, on the strip tail
`tailStrip C B = {τ | C < τ.re ∧ |τ.im| < B}`: `Φ τ ∈ pd.Pa`, `pd.φa (Φ τ) = τ` (so `Φ` is a right
inverse), the equivariance `F (Φ τ) = Φ (τ + 1)` (from the Abel equation `pd.φa_shift` and the
injectivity `pd.φa_inj`), and `Φ` is complex differentiable at `τ` (it is a local inverse of the
injective holomorphic `pd.φa`, whose derivative does not vanish —
`Work.ELRig.deriv_ne_zero_of_injOn`).  Moreover `Φ` is injective on that strip tail.

This is the direct analogue of `Work.FatouParabolic.Core.exists_petalInverse` together with
`Work.FatouParabolic.Core.petalInv_spec` (in
`Submission/Work/FatouParabolic/Core/exists_isCriticalPoint_in_immBasin.lean`) with the flower
replaced by `PetalData`; those deliverables replay verbatim with `pd.image_strip`,
`pd.φa_shift`, `pd.φa_inj`, `pd.isOpen_Pa`, `pd.φa_diff`.  The injection clause is the argument
already used in the assembly of `Work.FatouParabolic.Core.exists_isCriticalPoint_in_immBasin`
(from `pd.φa_inj` and `Φ τ ∈ pd.Pa`). -/
theorem petalInv_spec {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀)
    (hF : Differentiable ℂ F) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, (∀ τ : ℂ, C < τ.re → |τ.im| < B →
      Function.invFunOn pd.φa pd.Pa τ ∈ pd.Pa ∧
      pd.φa (Function.invFunOn pd.φa pd.Pa τ) = τ ∧
      F (Function.invFunOn pd.φa pd.Pa τ) = Function.invFunOn pd.φa pd.Pa (τ + 1) ∧
      DifferentiableAt ℂ (Function.invFunOn pd.φa pd.Pa) τ) ∧
    Set.InjOn (Function.invFunOn pd.φa pd.Pa) (Work.FatouParabolic.Core.tailStrip C B) := by
  obtain ⟨C, hC⟩ := pd.image_strip B (le_of_lt hB)
  -- the strip-image property in the strict form used below
  have hex : ∀ τ : ℂ, C < τ.re → |τ.im| < B → ∃ z ∈ pd.Pa, pd.φa z = τ :=
    fun τ h1 h2 => hC τ h1 (le_of_lt h2)
  have hmem : ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      Function.invFunOn pd.φa pd.Pa τ ∈ pd.Pa :=
    fun τ h1 h2 => Function.invFunOn_mem (hex τ h1 h2)
  have hφ : ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      pd.φa (Function.invFunOn pd.φa pd.Pa τ) = τ :=
    fun τ h1 h2 => Function.invFunOn_eq (hex τ h1 h2)
  refine ⟨C, ?_, ?_⟩
  · intro τ h1 h2
    have h2' : C < (τ + 1).re ∧ |(τ + 1).im| < B :=
      ⟨by simp only [Complex.add_re, Complex.one_re]; linarith, by simpa using h2⟩
    have hmemτ : Function.invFunOn pd.φa pd.Pa τ ∈ pd.Pa := hmem τ h1 h2
    have hφτ : pd.φa (Function.invFunOn pd.φa pd.Pa τ) = τ := hφ τ h1 h2
    have hmem1 : Function.invFunOn pd.φa pd.Pa (τ + 1) ∈ pd.Pa := hmem (τ + 1) h2'.1 h2'.2
    have hφ1 : pd.φa (Function.invFunOn pd.φa pd.Pa (τ + 1)) = τ + 1 := hφ (τ + 1) h2'.1 h2'.2
    refine ⟨hmemτ, hφτ, ?_, ?_⟩
    · -- equivariance: both sides lie in the petal and have the same Fatou coordinate
      have hmaps : F (Function.invFunOn pd.φa pd.Pa τ) ∈ pd.Pa := pd.mapsTo_Pa hmemτ
      have habel := pd.φa_shift (Function.invFunOn pd.φa pd.Pa τ) hmemτ
      exact pd.φa_inj hmaps hmem1 (by rw [habel, hφτ, hφ1])
    · -- differentiability of the local inverse of the injective holomorphic `pd.φa`
      have hopen : IsOpen pd.Pa := pd.isOpen_Pa
      have hmem_nhds : pd.Pa ∈ 𝓝 (Function.invFunOn pd.φa pd.Pa τ) := hopen.mem_nhds hmemτ
      have hdiffOn : DifferentiableOn ℂ pd.φa pd.Pa := pd.φa_diff
      have hdat : DifferentiableAt ℂ pd.φa (Function.invFunOn pd.φa pd.Pa τ) :=
        hdiffOn.differentiableAt hmem_nhds
      have han : AnalyticAt ℂ pd.φa (Function.invFunOn pd.φa pd.Pa τ) :=
        (hdiffOn.analyticOn hopen).analyticAt hmem_nhds
      have hsd : HasStrictDerivAt pd.φa (deriv pd.φa (Function.invFunOn pd.φa pd.Pa τ))
          (Function.invFunOn pd.φa pd.Pa τ) := han.hasStrictDerivAt
      have hne : deriv pd.φa (Function.invFunOn pd.φa pd.Pa τ) ≠ 0 :=
        Work.ELRig.deriv_ne_zero_of_injOn hdiffOn hopen pd.φa_inj hmemτ
      have hev : ∀ᶠ x in 𝓝 (Function.invFunOn pd.φa pd.Pa τ),
          Function.invFunOn pd.φa pd.Pa (pd.φa x) = x := by
        have hcont : ContinuousAt pd.φa (Function.invFunOn pd.φa pd.Pa τ) := hdat.continuousAt
        have hmemIoi : C < (pd.φa (Function.invFunOn pd.φa pd.Pa τ)).re := by
          rw [hφτ]; exact h1
        have hS1 : ∀ᶠ x in 𝓝 (Function.invFunOn pd.φa pd.Pa τ), C < (pd.φa x).re := by
          have h := (Complex.continuous_re.continuousAt.comp hcont).eventually
            (isOpen_Ioi.mem_nhds hmemIoi)
          simpa only [Function.comp_apply, Set.mem_Ioi] using h
        have himlt : |(pd.φa (Function.invFunOn pd.φa pd.Pa τ)).im| < B := by
          rw [hφτ]; exact h2
        have hS2 : ∀ᶠ x in 𝓝 (Function.invFunOn pd.φa pd.Pa τ), |(pd.φa x).im| < B := by
          have hcontim : ContinuousAt (fun x : ℂ => (pd.φa x).im)
              (Function.invFunOn pd.φa pd.Pa τ) :=
            Complex.continuous_im.continuousAt.comp hcont
          have h := hcontim.eventually
            ((isOpen_lt continuous_abs continuous_const).mem_nhds himlt)
          simpa only [Set.mem_ofPred_eq] using h
        filter_upwards [hmem_nhds, hS1, hS2] with x hxmem hx1 hx2
        exact pd.φa_inj (hmem (pd.φa x) hx1 hx2) hxmem (hφ (pd.φa x) hx1 hx2)
      have hsds : HasStrictDerivAt (Function.invFunOn pd.φa pd.Pa)
          (deriv pd.φa (Function.invFunOn pd.φa pd.Pa τ))⁻¹
          (pd.φa (Function.invFunOn pd.φa pd.Pa τ)) :=
        hsd.to_local_left_inverse hne hev
      have hd : DifferentiableAt ℂ (Function.invFunOn pd.φa pd.Pa)
          (pd.φa (Function.invFunOn pd.φa pd.Pa τ)) := hsds.hasDerivAt.differentiableAt
      rwa [hφτ] at hd
  · -- injectivity on the strip tail: `Φ` is a right inverse of the injective `pd.φa`
    intro τ1 h1 τ2 h2 heq
    rw [Work.FatouParabolic.Core.mem_tailStrip] at h1 h2
    rw [← hφ τ1 h1.1 h1.2, heq, hφ τ2 h2.1 h2.2]

end Work.FatouParabolic2
