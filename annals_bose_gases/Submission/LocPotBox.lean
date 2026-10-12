import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.ChiWitness
import Submission.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — FS Lemma `lem:LocPotential` assembled on the N-particle space

FS `final_v2.tex` `lem:LocPotential` (~line 975): with the cell-`u`
localisations `w_u(x,y) := χ_u(x)·W(x−y)·χ_u(y)` (`W := v/(χ⋆χ(·/ℓ))`, i.e.
`wLoc ℓ v u x y`) and `w_{1,u}` built on `W₁ := g/(χ⋆χ(·/ℓ))` (`wLoc ℓ g u x y`),
the original renormalised potential is the `u`-average of the localised ones:

    −μ·Σᵢ ∫g(xᵢ−y)dy + Σ_{i<j} v(xᵢ−xⱼ)
        = ∫_u [ −μ·Σᵢ ∫_y w_{1,u}(xᵢ,y)dy + Σ_{i<j} w_u(xᵢ,xⱼ) ] du .

The per-term localisation identities are already machine-proved in
`Submission/LocPotential.lean`:
  * `locPotential_pair`:  ∫_u w_u(x,y)du = v(x−y)     (pointwise),
  * `locPotential_onebody`: ∫_u∫_y w_{1,u}(x,y)dydu = ∫_y g(x−y)dy,
  * `locPotential_pair_sum` / `locPotential_onebody_sum`: the same over the
    finite index sets `{ij | ij.1 < ij.2}` and `Fin N`.
What remains (this module): the *box* forms with the `u`-integral outside the
finite sums (integral linearity over the Finset and over the `μ`-coefficient),
and the one-body translation constancy
  * `onebody_integral_translate`: `∫_y g(x−y)dy = ∫_y g y` (translation),
used to rewrite the chemical-potential term `−8πaμN` as `−μΣᵢ∫g(xᵢ−·)`.

## Proof route

All the `u`-integrands are continuous functions of `u` with compact support
(`χ_u` factors: `chiU_continuous_u`, `chiU_hasCompactSupport_u` in
`LocPotential`; products with the `u`-independent `wScaled ℓ h (x−y)` term
stay continuous with compact support), so the integral over `u` of each
`wLoc ℓ h u x y` exists (`wLoc_integrable_u`).  The one-body inner
`∫_y wLoc ℓ g u x y` as a function of `u` is integrable by Fubini from the
product-integrability `LocPotential.locPotential_integrable`
(`Integrable.integral_prod_left`, i.e. `locPotential_inner_integrable_u`).
With these integrability facts the Finset/coefficient linearity lemmas apply:
`integral_finsetSum`, `integral_const_mul`, `integral_add`
(from Mathlib's Bochner integral), giving `locPotential_box_pair`,
`locPotential_box_onebody` and the assembled `locPotential_box`.

`chiR0`/`chiR0_half` (`Submission.ChiWitness`) give the standard regime
witness `(r₀ := chiR0, hC := chiR0_half)`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **One-body translation constancy**: `∫_y g(x−y) dy = ∫_y g y` for all `x`
(unconditional, from the measure-preserving substitution `y ↦ x−y`). -/
lemma onebody_integral_translate (g : ℝ³ → ℝ) (x : ℝ³) :
    (∫ y : ℝ³, g (x - y)) = ∫ y : ℝ³, g y := by
  exact integral_comp_sub_left (g := g) x

/-- Finite-sum form of the translation constancy:
`Σᵢ ∫_y g(xᵢ−y) dy = (∑ᵢ ∫_y g y) = N·∫g` (rewritten by the caller). -/
lemma onebody_integral_translate_sum {N : ℕ} (g : ℝ³ → ℝ) (x : X N) :
    (∑ i : Fin N, ∫ y : ℝ³, g (x i - y)) = (∑ i : Fin N, ∫ y : ℝ³, g y) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact onebody_integral_translate g (x i)

/-- For fixed `x,y` the `u ↦ wLoc ℓ h u x y` localised kernel is continuous. -/
lemma wLoc_u_continuous (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    Continuous (fun u : ℝ³ => wLoc ℓ h u x y) := by
  unfold wLoc
  exact ((chiU_continuous_u ℓ x).mul continuous_const).mul (chiU_continuous_u ℓ y)

/-- The support of `u ↦ wLoc ℓ h u x y` is contained in that of `u ↦ χ_u(x)`. -/
lemma wLoc_u_support (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    Function.support (fun u : ℝ³ => wLoc ℓ h u x y) ⊆
      Function.support (fun u : ℝ³ => chiU ℓ u x) := by
  intro u hu
  have hx : chiU ℓ u x ≠ 0 := by
    intro hx0
    apply hu
    dsimp [wLoc]
    simp [hx0]
  simpa using hx

/-- For fixed `x,y`, `u ↦ wLoc ℓ h u x y` is integrable over `u`
(continuous, compactly supported). -/
lemma wLoc_integrable_u (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    Integrable (fun u : ℝ³ => wLoc ℓ h u x y) := by
  have hsupp : HasCompactSupport (fun u : ℝ³ => wLoc ℓ h u x y) := by
    apply HasCompactSupport.mono (chiU_hasCompactSupport_u x ℓ)
    exact wLoc_u_support ℓ h x y
  exact Continuous.integrable_of_hasCompactSupport (wLoc_u_continuous ℓ h x y) hsupp

/-- For fixed `x`, `u ↦ ∫_y w_{1,u}(x,y) dy` is integrable over `u` (Fubini
from the product integrability of the kernel). -/
lemma locPotential_inner_integrable_u {g : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g)
    (hgsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : ℝ³) :
    Integrable (fun u : ℝ³ => ∫ y : ℝ³, wLoc ℓ g u x y) := by
  have hInt : Integrable (fun p : ℝ³ × ℝ³ => wLoc ℓ g p.1 x p.2) (volume.prod volume) :=
    locPotential_integrable hℓ hg hgsupp hRℓ hC x
  simpa [Function.uncurry] using hInt.integral_prod_left

/-- Integral linearity for the chemical-potential combination:
`∫_u (−μ·A(u) + B(u)) = −μ·∫_u A(u) + ∫_u B(u)` for integrable `A, B`. -/
lemma integral_neg_const_mul_add (μ : ℝ) {A B : ℝ³ → ℝ} (hA : Integrable A)
    (hB : Integrable B) :
    (∫ u : ℝ³, (-μ) * A u + B u) = (-μ) * (∫ u : ℝ³, A u) + (∫ u : ℝ³, B u) := by
  calc
    (∫ u : ℝ³, (-μ) * A u + B u)
        = (∫ u : ℝ³, (-μ) * A u) + (∫ u : ℝ³, B u) := by
          exact MeasureTheory.integral_add
            (f := fun u : ℝ³ => (-μ) * A u) (g := fun u : ℝ³ => B u)
            (by simpa using hA.const_mul (-μ)) hB
    _ = (-μ) * (∫ u : ℝ³, A u) + (∫ u : ℝ³, B u) := by
          rw [MeasureTheory.integral_const_mul (-μ) A]

/-- **lem:LocPotential (pair, box form)**: the `u`-integral of the localised
pair potential over the pairs `i<j` equals the original pair potential sum. -/
lemma locPotential_box_pair {N : ℕ} {v : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hv : ∀ x : ℝ³, R ≤ ‖x‖ → v x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : X N) :
    (∫ u : ℝ³,
        ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2)) =
      ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2) := by
  let T := {ij : Fin N × Fin N | ij.1 < ij.2}
  calc
    (∫ u : ℝ³, ∑ ij : T, wLoc ℓ v u (x ij.1.1) (x ij.1.2))
        = ∑ ij : T, (∫ u : ℝ³, wLoc ℓ v u (x ij.1.1) (x ij.1.2)) := by
          refine MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset T))
            (f := fun ij u => wLoc ℓ v u (x ij.1.1) (x ij.1.2)) ?_
          intro ij hij
          exact wLoc_integrable_u ℓ v (x ij.1.1) (x ij.1.2)
    _ = (∑ ij : T, v (x ij.1.1 - x ij.1.2)) := by
          simpa [T] using locPotential_pair_sum hℓ hv hR hr₀ hRℓ hC x

/-- **lem:LocPotential (one-body, box form)**: the `u`-integral of the sum of
the localised one-body potentials equals the original one-body sum. -/
lemma locPotential_box_onebody {N : ℕ} {g : ℝ³ → ℝ} {ℓ R r₀ : ℝ} (hℓ : 0 < ℓ)
    (hg : MeasureTheory.Integrable g)
    (hgs : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0) (hR : 0 ≤ R)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : X N) :
    (∫ u : ℝ³,
        ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y) =
      ∑ i : Fin N, ∫ y : ℝ³, g (x i - y) := by
  calc
    (∫ u : ℝ³, ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y)
        = ∑ i : Fin N, (∫ u : ℝ³, ∫ y : ℝ³, wLoc ℓ g u (x i) y) := by
          refine MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset (Fin N)))
            (f := fun i u => ∫ y : ℝ³, wLoc ℓ g u (x i) y) ?_
          intro i hi
          exact locPotential_inner_integrable_u hℓ hg hgs hRℓ hC (x i)
    _ = ∑ i : Fin N, ∫ y : ℝ³, g (x i - y) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact locPotential_onebody hℓ hg hgs hR hr₀ hRℓ hC (x i)

/-- **lem:LocPotential (FS, full form)** — the potential part of the
`μ`-renormalised big-box operator (`−μΣᵢ∫g(xᵢ−·) + Σ_{i<j}v(xᵢ−xⱼ)`) is the
`u`-average of the localised potentials (`−μΣᵢ∫_y w_{1,u}(xᵢ,·) +
Σ_{i<j}w_u(xᵢ,xⱼ)`), as functions on `(ℝ³)^N`. -/
lemma locPotential_box {N : ℕ} {v g : ℝ³ → ℝ} {ℓ R r₀ μ : ℝ} (hℓ : 0 < ℓ)
    (hv : ∀ x : ℝ³, R ≤ ‖x‖ → v x = 0) (hR : 0 ≤ R)
    (hg : MeasureTheory.Integrable g)
    (hgs : ∀ x : ℝ³, R ≤ ‖x‖ → g x = 0)
    (hr₀ : 0 < r₀) (hRℓ : R ≤ ℓ * r₀)
    (hC : ∀ x : ℝ³, ‖x‖ ≤ r₀ → 1 / 2 ≤ conv3 chi chi x) (x : X N) :
    -μ * (∑ i : Fin N, ∫ y : ℝ³, g (x i - y)) +
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) =
      ∫ u : ℝ³,
        (-μ * (∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y) +
          ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2)) := by
  set A : ℝ³ → ℝ := fun u => ∑ i : Fin N, ∫ y : ℝ³, wLoc ℓ g u (x i) y with hAdef
  set B : ℝ³ → ℝ := fun u =>
    ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2) with hBdef
  set C : ℝ := ∑ i : Fin N, ∫ y : ℝ³, g (x i - y) with hCdef
  set D : ℝ := ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2) with hDdef
  change -μ * C + D = ∫ u : ℝ³, (-μ * A u + B u)
  have hA_int : Integrable A := by
    rw [hAdef]
    refine MeasureTheory.integrable_finsetSum (s := (Finset.univ : Finset (Fin N)))
      (f := fun i u => ∫ y : ℝ³, wLoc ℓ g u (x i) y) ?_
    intro i hi
    exact locPotential_inner_integrable_u hℓ hg hgs hRℓ hC (x i)
  have hB_int : Integrable B := by
    rw [hBdef]
    refine MeasureTheory.integrable_finsetSum
      (s := (Finset.univ : Finset {ij : Fin N × Fin N | ij.1 < ij.2}))
      (f := fun ij u => wLoc ℓ v u (x ij.1.1) (x ij.1.2)) ?_
    intro ij hij
    exact wLoc_integrable_u ℓ v (x ij.1.1) (x ij.1.2)
  have hswap : (∫ u : ℝ³, (-μ * A u + B u)) = (-μ) * (∫ u : ℝ³, A u) + (∫ u : ℝ³, B u) :=
    integral_neg_const_mul_add μ hA_int hB_int
  calc
    -μ * C + D = (-μ) * (∫ u : ℝ³, A u) + (∫ u : ℝ³, B u) := by
      rw [hCdef, hDdef, hAdef, hBdef]
      rw [locPotential_box_onebody hℓ hg hgs hR hr₀ hRℓ hC x]
      rw [locPotential_box_pair hℓ hv hR hr₀ hRℓ hC x]
    _ = ∫ u : ℝ³, (-μ * A u + B u) := by
      rw [← hswap]

end BoseGases

end Submission
