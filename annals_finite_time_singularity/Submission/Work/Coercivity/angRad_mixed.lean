/-
Copyright: work module for the Elgindi finite-time singularity project.

# Mixed derivatives of an angular-times-radial function

For `g : ℝ → ℝ` and `R : ℝ → ℝ`, the product `(z,θ) ↦ g θ * R z` has separated variables,
and the two operators `D_θ = sin(2θ) ∂_θ` and `D_z = z ∂_z` act on the two factors
independently: `D_θ` only differentiates the angular factor and `D_z` only the radial one.
Consequently the mixed derivative of order `(j,i)` factors as

  `D_z^j D_θ^i (g θ * R z) = (D_θ^i g)(θ) · (D_z^j R)(z)`

where `D_θ^i g` is `CT.DthIterAng i g` (the iterate of `D_θ` on functions of `θ` alone) and
`D_z^j R` is `CT.DzRIter j R` (the iterate of `D_z` on functions of `z` alone).

Since the statements are about `deriv`, the identities are only valid where the factors are
differentiable: `hg` gives `C^∞`-regularity of `g` on the open interval `(0, π/2)` (an open set,
so every iterate `DthIterAng i g` is again `C^∞` there, by `ContDiffOn.deriv_of_isOpen`), and
`hR` gives differentiability of the radial iterates up to order `j` on `(0,∞)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Coercivity.CTDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.Coercivity

/-- Every iterate of `D_θ = sin(2θ) ∂_θ` is again `C^∞` on an open set on which `g` is `C^∞`.
This is what makes `deriv (DthIterAng n g) θ` the "right" derivative: `DthIterAng (n+1) g` is
literally `sin(2·) · deriv (DthIterAng n g)`. -/
lemma DthIterAng_contDiffOn_Ioo (g : ℝ → ℝ) (hg : ContDiffOn ℝ ⊤ g (Ioo 0 (π / 2))) :
    ∀ n : ℕ, ContDiffOn ℝ ⊤ (CT.DthIterAng n g) (Ioo 0 (π / 2)) := by
  intro n
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [CT.DthIterAng_succ]
    have hd := ih.deriv_of_isOpen isOpen_Ioo (le_top : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
    have hs : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) (Ioo 0 (π / 2)) := by fun_prop
    exact hs.mul hd

/-- `D_θ^i` of the separated product `(z,θ) ↦ g θ * R z` only sees the angular factor. -/
lemma DthIter_ang_mul_rad (g R : ℝ → ℝ) (hg : ContDiffOn ℝ ⊤ g (Ioo 0 (π / 2))) :
    ∀ (n : ℕ) (z θ : ℝ), θ ∈ Ioo 0 (π / 2) →
      Work.Spaces.DthIter n (fun z θ => g θ * R z) z θ = CT.DthIterAng n g θ * R z := by
  intro n
  induction n with
  | zero => intro z θ hθ; rfl
  | succ n ih =>
    intro z θ hθ
    have hcont := DthIterAng_contDiffOn_Ioo g hg n
    have hdiff : DifferentiableAt ℝ (CT.DthIterAng n g) θ :=
      (hcont.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)
    have hev : (fun θ' => Work.Spaces.DthIter n (fun z θ => g θ * R z) z θ')
        =ᶠ[𝓝 θ] (fun θ' => CT.DthIterAng n g θ' * R z) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ) (fun θ' hθ' => ih z θ' hθ')
    rw [show Work.Spaces.DthIter (n + 1) (fun z θ => g θ * R z) z θ
        = Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => g θ * R z) z θ') θ from rfl]
    rw [hev.deriv_eq, deriv_mul_const hdiff, CT.DthIterAng_succ]
    ring

/-- `D_z^j` of a function agreeing on the quadrant `(0,∞) × (0,π/2)` with `(z,θ) ↦ h θ * R z`
only differentiates the radial factor, provided the radial iterates up to order `j` are
differentiable on `(0,∞)`. -/
lemma DzIter_eq_of_eqOn_Ioo (G : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (R : ℝ → ℝ)
    (hG : ∀ z θ, 0 < z → θ ∈ Ioo 0 (π / 2) → G z θ = h θ * R z) :
    ∀ j : ℕ, (∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R) z) →
      ∀ z θ, 0 < z → θ ∈ Ioo 0 (π / 2) →
        Work.Spaces.DzIter j G z θ = h θ * CT.DzRIter j R z := by
  intro j
  induction j with
  | zero => intro hR z θ hz hθ; exact hG z θ hz hθ
  | succ j ih =>
    intro hR z θ hz hθ
    have hR' : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R) z :=
      fun k hk z hz => hR k (le_trans hk (Nat.le_succ j)) z hz
    have ih' := ih hR'
    have hdt : DifferentiableAt ℝ (CT.DzRIter j R) z := hR j (Nat.le_succ j) z hz
    have hev : (fun z' => Work.Spaces.DzIter j G z' θ)
        =ᶠ[𝓝 z] (fun z' => h θ * CT.DzRIter j R z') :=
      eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih' z' θ hz' hθ)
    rw [show Work.Spaces.DzIter (j + 1) G z θ
        = z * deriv (fun z' => Work.Spaces.DzIter j G z' θ) z from rfl]
    rw [hev.deriv_eq, deriv_const_mul (h θ) hdt, CT.DzRIter_succ,
      show CT.DzR (CT.DzRIter j R) z = z * deriv (CT.DzRIter j R) z from rfl]
    ring

theorem angRad_mixed (g : ℝ → ℝ) (R : ℝ → ℝ) (j i : ℕ)
    (hg : ContDiffOn ℝ ⊤ g (Set.Ioo 0 (π / 2)))
    (hR : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (Work.Coercivity.CT.DzRIter k R) z) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed j i (fun z θ => g θ * R z) z θ
        = Work.Coercivity.CT.DthIterAng i g θ * Work.Coercivity.CT.DzRIter j R z := by
  intro z θ hz hθ
  have hG : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.DthIter i (fun z θ => g θ * R z) z θ = CT.DthIterAng i g θ * R z :=
    fun z θ _ hθ => DthIter_ang_mul_rad g R hg i z θ hθ
  exact DzIter_eq_of_eqOn_Ioo _ _ _ hG j hR z θ hz hθ

end Work.Coercivity
