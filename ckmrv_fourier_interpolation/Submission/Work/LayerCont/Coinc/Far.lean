/-
# The far-side API: guarded detour identities and the `resCorr`-free form of the double agreement

The two detour identities of this area come in two equivalent shapes:

* the **ball shape** of `Submission/Work/LayerCont/Coinc/DetourCoinc.lean` and
  `Submission/Work/LayerCont/DetourNoOrbit.lean`, whose hypotheses are quantified over the whole
  hyperbolic ball `B(1 + i t₀, ε)`;
* the **pointwise shape** (`…_pointwise`, written in
  `Submission/Work/LayerCont/Coinc/layerLowCoinc_eq_layerLow_far.lean` and
  `Submission/Work/LayerCont/Coinc/layerLowDouble_eq_layerLowAt_far.lean`), whose hypotheses
  concern a single `τ` — which is all any of the proofs uses.

The ball shape with the *guarded* hypotheses `1 < τ.re` is not a formal consequence of the
unguarded ball shape (the guard cannot be removed from the other points of the ball), so the two
ball-shaped lemmas below are derived from the pointwise ones.  This is the form in which a caller
whose geometric hypotheses are only available on the far side of `Re τ = 1` should use them.

`layerLowDouble_sub_resCorr_eq_layerLowAt_far` records the `resCorr`-free reading of the
double-piece agreement (`layerLowDouble = layerLowAt + sinSqC · resCorr` on the far side, because
there *both* detours are residue-free, whereas on the near side the pole detour contributes
`-resCorr` and cancels the explicit term).
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- **Ball form, guarded by `1 < τ.re`, of the residue-free detour identity at the coincidence.**
Derived from `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc_pointwise`. -/
theorem detourLeftC_eq_interval_of_coinc_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A)
    (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hclean : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ coincℂ τ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      coincℂ τ ∈ openLeftRectℂ c A ξ)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      detourLeftC ℓ d r c A ξ τ
        = ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v :=
  fun τ hτ hre =>
    detourLeftC_eq_interval_of_coinc_pointwise ℓ d hd hA hξ hcA τ
      (hclean τ hτ hre) (hcoinc τ hτ hre) (hdeg τ hτ hre)

/-- **Ball form, guarded by `1 < τ.re`, of the orbit-free detour identity.**
Derived from `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_noOrbit_pointwise`. -/
theorem detourLeftC_eq_interval_of_noOrbit_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect c A ξ z → z ≠ γ • τ) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      detourLeftC ℓ d r c A ξ τ
        = ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v :=
  fun τ hτ hre => detourLeftC_eq_interval_of_noOrbit_pointwise ℓ d hA hξ hcA τ (hcl τ hτ hre)

/-- **The `resCorr`-free form of the far-side double-piece agreement.**

This is the far-side statement of "the pure contour object equals `layerLowAt`": on the far side
both detours are residue-free, so the contour expression
`sinSqC r · (∫_E + detourLeftC(t₀) + detourLeftC(t₀⁻¹))` — which is `layerLowDouble` *without* its
explicit residue term — reproduces `layerLowAt` exactly, and `layerLowDouble` itself differs from
`layerLowAt` by `sinSqC r * resCorr r τ`
(`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`). -/
theorem layerLowDouble_sub_resCorr_eq_layerLowAt_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁) (hξ₁ : 0 < ξ₁)
    (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁) (hhi : t₀ + A₁ ≤ p)
    (hsep : t₀⁻¹ + A₂ < t₀ - A₁) (hA₂inv : A₂ < t₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀⁻¹ A₂ ξ₂ z → (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      coincℂ τ ∈ openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
          ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (onePlusI t₀ ht₀) < ε → 1 < τ.re →
      Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
        - sinSqC r * resCorr r τ = Work.LayerCont.layerLowAt ℓ d p r τ := by
  intro τ hτ hre
  rw [layerLowDouble_eq_layerLowAt_far ℓ d hd ht₀ hA₁ hξ₁ hA₂ hξ₂ hε hlo hhi hsep hA₂inv
    hcl₁ hcl₂ hcoinc hdeg hcleanAll τ hτ hre]
  ring

/-! ## The literal (unguarded) shapes

The two agreements were requested with the geometric hypotheses quantified over the whole ball
`B(1 + i t₀, ε)` and *without* the far-side guard `1 < τ.re`.  Such a hypothesis set is
unsatisfiable on a ball straddling `Re τ = 1` (the coincidence is on the imaginary axis at the
centre), but the *statements* are still meaningful, and they follow from the guarded versions
because the (unguarded) hypothesis `hcoinc` itself forces `1 < τ.re`
(`Work.LayerCont.Coinc.one_lt_re_of_coincℂ_re_neg`).  Both shapes are therefore provided.

Note that for the **double** piece the unguarded statement can only be the *corrected* one
`layerLowDouble = layerLowAt + sinSqC r * resCorr r τ`: on the far side the pole-side detour is
residue-free, so `sinSqC r * resCorr r τ` is no longer cancelled — the unguarded version with
right-hand side exactly `layerLowAt` is *false*. -/

/-- Unguarded (literal) form of `Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_far`. -/
theorem layerLowCoinc_eq_layerLow_far_unguarded (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {t₀ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hε : 0 < ε) (hA₂inv : A₂ < t₀⁻¹) (hI₂low : t₀⁻¹ + A₂ < 1)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀⁻¹ A₂ ξ₂ z → (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      coincℂ τ ∈ openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → Work.Residues.jprime τ ≠ 0)
    (hcleanIoc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) 1) \ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (onePlusI t₀ ht₀) < ε →
      Work.LayerCont.layerLowCoinc ℓ d t₀ A₂ ξ₂ r τ = Work.Asymptotics.layerLow ℓ d τ r := by
  intro τ hτ
  exact layerLowCoinc_eq_layerLow_far ℓ d hd ht₀ hA₂ hξ₂ hε hA₂inv hI₂low
    (fun σ hσ _ => hcl σ hσ) (fun σ hσ _ => hcoinc σ hσ) (fun σ hσ _ => hdeg σ hσ)
    (fun σ hσ _ => hcleanIoc σ hσ) τ hτ
    (one_lt_re_of_coincℂ_re_neg τ (coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc τ hτ)))

/-- Unguarded (literal) form of `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`. -/
theorem layerLowDouble_eq_layerLowAt_far_unguarded (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁)
    (hξ₁ : 0 < ξ₁) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁)
    (hhi : t₀ + A₁ ≤ p) (hsep : t₀⁻¹ + A₂ < t₀ - A₁) (hA₂inv : A₂ < t₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀⁻¹ A₂ ξ₂ z → (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      coincℂ τ ∈ openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
          ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (onePlusI t₀ ht₀) < ε →
      Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
        = Work.LayerCont.layerLowAt ℓ d p r τ
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  intro τ hτ
  exact layerLowDouble_eq_layerLowAt_far ℓ d hd ht₀ hA₁ hξ₁ hA₂ hξ₂ hε hlo hhi hsep hA₂inv
    (fun σ hσ _ => hcl₁ σ hσ) (fun σ hσ _ => hcl₂ σ hσ) (fun σ hσ _ => hcoinc σ hσ)
    (fun σ hσ _ => hdeg σ hσ) (fun σ hσ _ => hcleanAll σ hσ) τ hτ
    (one_lt_re_of_coincℂ_re_neg τ (coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc τ hτ)))

/-- **The `resCorr`-free reading of the unguarded (literal) double-piece agreement**: the pure
contour expression `layerLowDouble - sinSqC r * resCorr r τ` reproduces `layerLowAt` on the far
side, with the hypotheses exactly as originally requested (no `1 < τ.re` guard). -/
theorem layerLowDouble_sub_resCorr_eq_layerLowAt_far_unguarded
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p t₀ A₁ ξ₁ A₂ ξ₂ ε r : ℝ} (ht₀ : 0 < t₀) (hA₁ : 0 < A₁)
    (hξ₁ : 0 < ξ₁) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hε : 0 < ε) (hlo : 0 < t₀ - A₁)
    (hhi : t₀ + A₁ ≤ p) (hsep : t₀⁻¹ + A₂ < t₀ - A₁) (hA₂inv : A₂ < t₀⁻¹)
    (hcl₁ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀ A₁ ξ₁ z → z ≠ γ • τ)
    (hcl₂ : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        leftRect t₀⁻¹ A₂ ξ₂ z → (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      coincℂ τ ∈ openLeftRectℂ t₀⁻¹ A₂ ξ₂)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε → Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ (Set.Ioo (t₀ - A₁) (t₀ + A₁)
          ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (onePlusI t₀ ht₀) < ε →
      Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
        - sinSqC r * resCorr r τ = Work.LayerCont.layerLowAt ℓ d p r τ := by
  intro τ hτ
  rw [layerLowDouble_eq_layerLowAt_far_unguarded ℓ d hd ht₀ hA₁ hξ₁ hA₂ hξ₂ hε hlo hhi hsep
    hA₂inv hcl₁ hcl₂ hcoinc hdeg hcleanAll τ hτ]
  ring

end Work.LayerCont.Coinc
