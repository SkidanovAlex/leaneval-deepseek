import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves.SolFire

set_option autoImplicit false

/-!
# `N₀` only sees the values on the open quadrant

`Work.Construction.N0 α F g` is built from the angular integral `L₁₂ g`, the pointwise
values of `g`, and the pointwise derivatives `∂_θF`, `z∂_zF`, `z∂_zg` of the two profiles.
The first only sees `g` almost everywhere on the angular interval `[0, π/2]` (the two
endpoints are null), and the derivatives only see the values of a function on an open
neighbourhood of the point at which they are evaluated — which, for a point of the open
quadrant `z > 0`, `0 < θ < π/2`, is contained in the open quadrant.

Hence `N₀` is a *local* expression: two pairs `(F, g)` and `(F', g')` that agree on the
open quadrant give the same value of `N₀` at every point of the open quadrant.
-/

/-- On the angular interval `[0, π/2]`, the open interval `(0, π/2)` has full measure:
the two excluded endpoints form a null set. -/
private lemma ae_mem_Ioo_of_mem_Icc :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      0 < θ ∧ θ < Real.pi / 2 := by
  have hne : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 :=
    ((Set.finite_singleton (Real.pi / 2)).insert 0).measure_zero volume
  have hset : {θ : ℝ | ¬ (θ ∉ ({0, Real.pi / 2} : Set ℝ))} = ({0, Real.pi / 2} : Set ℝ) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  have hmem : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]
    exact hne
  filter_upwards [hmem] with θ hθ hθI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  simp only [Set.mem_Icc] at hθI
  exact ⟨lt_of_le_of_ne hθI.1 (fun hh => hθ.1 hh.symm),
    lt_of_le_of_ne hθI.2 hθ.2⟩

/-- The `L₁₂`-density at a point `s > 0` only sees the profile almost everywhere on `Iθ`. -/
private lemma L12dens_congr {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (h : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → a s θ = b s θ) :
    Work.FM.L12dens Work.Spaces.K a s = Work.FM.L12dens Work.Spaces.K b s := by
  simp only [Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [ae_mem_Ioo_of_mem_Icc] with θ hθ hθI
  obtain ⟨h1, h2⟩ := hθ hθI
  rw [h θ h1 h2]

/-- `L₁₂` at a positive radius only sees the values of the profile on the open quadrant. -/
private lemma L12_congr {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  simp only [Work.Construction.L12, Work.FM.L12]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro s hs
  have hs0 : 0 < s := lt_trans hz hs
  exact L12dens_congr fun θ h1 h2 => h s θ hs0 h1 h2

/-- `∂_z` only sees the values of the profile on the open quadrant. -/
private lemma pz_congr {a b : ℝ → ℝ → ℝ}
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz a z θ = Work.Spaces.pz b z θ := by
  intro z θ hz h1 h2
  have heq : (fun z' : ℝ => a z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ hz' h1 h2
  simp only [Work.Spaces.pz]
  exact heq.deriv_eq

/-- `∂_θ` only sees the values of the profile on the open quadrant. -/
private lemma pth_congr {a b : ℝ → ℝ → ℝ}
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth a z θ = Work.Spaces.pth b z θ := by
  intro z θ hz h1 h2
  have heq : (fun θ' : ℝ => a z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => b z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
      with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

theorem N0_congr_of_agreeOnQ {α : ℝ} {F F' g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ') :
    Work.Construction.N0 α F g z θ = Work.Construction.N0 α F' g' z θ := by
  have hL12 : Work.Construction.L12 g z = Work.Construction.L12 g' z := L12_congr hz hg
  have hgpt : g z θ = g' z θ := hg z θ hz hθ hθ2
  have hpthF : Work.Spaces.pth F z θ = Work.Spaces.pth F' z θ := pth_congr hF z θ hz hθ hθ2
  have hpzF : Work.Spaces.pz F z θ = Work.Spaces.pz F' z θ := pz_congr hF z θ hz hθ hθ2
  have hpzg : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ := pz_congr hg z θ hz hθ hθ2
  have hDzF : Work.Spaces.Dz F z θ = Work.Spaces.Dz F' z θ := by
    simp only [Work.Spaces.Dz, hpzF]
  have hDzg : Work.Spaces.Dz g z θ = Work.Spaces.Dz g' z θ := by
    simp only [Work.Spaces.Dz, hpzg]
  simp only [Work.Construction.N0]
  rw [hL12, hgpt, hpthF, hDzF, hDzg]

end Work.FTS_FinalLeaves.SolFire
