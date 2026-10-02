/-
Work.MRMT.Found — the consumer API (§2 of `NOTES_LEAD_mrmt_foundations.md`), in the
`principal μ` vocabulary.

Each item is a corollary of the corresponding `…_of_data`/data-form lemma proved for an
arbitrary `PrincipalData μ`, instantiated at the canonical `principalData μ hμ`.
-/
import Submission.Work.MRMT.Found.Principal
import Submission.Work.MRMT.Found.differentiableOn_comp_principal_symm
import Submission.Work.MRMT.Found.differentiableOn_principal_of_eq_zero
import Submission.Work.MRMT.Found.antiholo_conj
import Submission.Work.MRMT.Found.conj_contDiff
import Submission.Work.MRMT.Found.principalData_beltrami
import Submission.Work.MRMT.Found.tendsto_principal
import Submission.Work.MRMTCont.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function Classical
open scoped ENNReal

namespace Work.MRMT.Found

/-! ## M1 and the Beltrami equation -/

/-- **M1** (restated here for convenience): `principal μ z = z + O(1/‖z‖)`. -/
theorem principal_decay' {μ : ℂ → ℂ} (hμ : Admissible μ) :
    ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖principal μ z - z‖ ≤ C / ‖z‖ :=
  principal_decay hμ

/-- The principal solution satisfies the Beltrami equation a.e. -/
theorem principal_beltrami {μ : ℂ → ℂ} (hμ : Admissible μ) :
    ∀ᵐ z ∂MeasureTheory.volume,
      dzbar (principal μ : ℂ → ℂ) z = μ z * dz (principal μ : ℂ → ℂ) z := by
  have h := principalData_beltrami hμ (principalData μ hμ)
  rwa [← principal_eq_principalData hμ] at h

/-! ## M2, M3, M2′, M2″ -/

/-- **M2.** *Same coefficient ⟹ conformal transition*: if `g` is locally Lipschitz on the
open set `U` and satisfies `∂̄g = μ ∂g` a.e. on `U`, then `g ∘ (principal μ)⁻¹` is
holomorphic.  (`g` need not be injective; this absorbs M5.) -/
theorem principal_comp_symm_differentiableOn {μ : ℂ → ℂ} (hμ : Admissible μ) {U : Set ℂ}
    (hU : IsOpen U) {g : ℂ → ℂ} (hg : LocallyLipschitzOn U g)
    (hrel : ∀ᵐ z ∂MeasureTheory.volume, z ∈ U → dzbar g z = μ z * dz g z) :
    DifferentiableOn ℂ (g ∘ ((principal μ).symm : ℂ → ℂ)) ((principal μ : ℂ → ℂ) '' U) := by
  have h := differentiableOn_comp_principal_symm hμ (principalData μ hμ) hU hg hrel
  rwa [← principal_eq_principalData hμ] at h

/-- **M3.** Where `μ` vanishes, `principal μ` is holomorphic. -/
theorem principal_differentiableOn_of_eq_zero {μ : ℂ → ℂ} (hμ : Admissible μ) {U : Set ℂ}
    (hU : IsOpen U) (h0 : ∀ᵐ z ∂MeasureTheory.volume, z ∈ U → μ z = 0) :
    DifferentiableOn ℂ (principal μ) U := by
  have h := differentiableOn_principal_of_eq_zero hμ (principalData μ hμ) hU h0
  rwa [← principal_eq_principalData hμ] at h

/-- **M2′.** If `μ` is invariant under the antiholomorphic map `f` in the sense of the
stated pullback relation, then the conjugate of `principal μ ∘ f ∘ (principal μ)⁻¹` is
holomorphic. -/
theorem principal_antiholo_conj {μ : ℂ → ℂ} (hμ : Admissible μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f))
    (hinv : ∀ᵐ z ∂MeasureTheory.volume,
      μ z = star (μ (f z)) * dzbar f z / star (dzbar f z)) :
    Differentiable ℂ (star ∘ (principal μ : ℂ → ℂ) ∘ f ∘ ((principal μ).symm : ℂ → ℂ)) := by
  have h := antiholo_conj hμ (principalData μ hμ) hf hinv
  rwa [← principal_eq_principalData hμ] at h

/-- **M2″.** The same for a C¹ orientation-reversing `f` off a discrete set `S`, with the
pull-back coefficient `pullRev μ f`. -/
theorem principal_conj_contDiff {μ : ℂ → ℂ} (hμ : Admissible μ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hS : ∀ z : ℂ, Filter.Eventually (fun w => w ∉ S) (nhdsWithin z {z}ᶜ))
    (hrev : ∀ z ∉ S, ‖dz f z‖ < ‖dzbar f z‖)
    (hinv : ∀ᵐ z ∂MeasureTheory.volume, μ z = pullRev μ f z) :
    Differentiable ℂ (star ∘ (principal μ : ℂ → ℂ) ∘ f ∘ ((principal μ).symm : ℂ → ℂ)) := by
  have h := conj_contDiff hμ (principalData μ hμ) hf hS hrev hinv
  rwa [← principal_eq_principalData hμ] at h

/-! ## M6 -/

/-- **M6.** Continuity of the Ahlfors–Bers map at `μ = 0`: principal solutions for
coefficients supported in a fixed ball with `‖μ_j‖_∞ → 0` converge to the identity locally
uniformly. -/
theorem principal_tendsto {μs : ℕ → ℂ → ℂ} (hμ : ∀ j, Admissible (μs j)) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂MeasureTheory.volume, ‖μs j z‖ ≤ k)
    (h0 : Filter.Tendsto (fun j => MeasureTheory.eLpNorm (μs j) ⊤ MeasureTheory.volume)
      Filter.atTop (nhds 0)) :
    TendstoLocallyUniformly (fun j => (principal (μs j) : ℂ → ℂ)) id Filter.atTop := by
  have h := tendsto_principal hμ (fun j => principalData (μs j) (hμ j)) hk hsupp hb h0
  have hφ : (fun j => (principal (μs j) : ℂ → ℂ))
      = fun j => (((principalData (μs j) (hμ j)).φ : ℂ ≃ₜ ℂ) : ℂ → ℂ) := by
    funext j
    rw [principal_eq_principalData (hμ j)]
  rwa [hφ]

end Work.MRMT.Found
