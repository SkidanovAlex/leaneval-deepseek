/-
# `Work.FTS.EllSol.EllPkgAux.kernelJensen`

The angular **Jensen/Schur** estimate for the three-image mollification kernel

  `KJ ε θ s = sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - π)`

of the doubly odd extension: there is a universal (i.e. `ε`-independent) constant `K > 0` with

  `∫_{Iθ} σθ(θ) · (∫_{Iθ} KJ ε θ s · g s)² dθ ≤ K · ∫_{Iθ} g s² σθ s ds`

for every `0 < ε ≤ 1/2` and every `g` with `g² σθ ∈ L¹(Iθ)`, where `σθ = thEta = sin(2θ)^{-η}`.

## Proof

* `KJ_pointwise` (in `KernelAux`) gives, for every `θ ∈ Iθ`, the pointwise
  Cauchy–Schwarz bound `(∫ KJ ε θ s · g s)² ≤ 3 ∫ KJ ε θ s · (g s)²`, obtained from
  `‖∫ KJ g‖ ≤ ∫ KJ |g|` and `L²`-Cauchy–Schwarz for `√KJ` against `√KJ · |g|`, together with the
  mass bound `∫_{Iθ} KJ ε θ s ≤ 3` (`KJ_mass`).  No measurability of `g` is needed here: the
  modulus `√(g²)` is measurable as soon as `g² σθ` is integrable, and the Bochner integral of a
  non-integrable integrand is `0`.
* Multiplying by `σθ(θ) ≥ 0` and integrating gives, via `integral_mono_of_nonneg`,
  `∫_{Iθ} σθ(θ)(∫KJ g)² ≤ 3 ∫_{Iθ} σθ(θ) ∫_{Iθ} KJ ε θ s (g s)²`.
* The Fubini/Tonelli swap `kernelSwap` (the iterated integrals are finite because
  `KJ ε θ s ≤ 3 (ε sMass)⁻¹` while `θ ↦ σθ(θ)` and `s ↦ g s²` are integrable) turns this into
  `3 ∫_{Iθ} (g s)² (∫_{Iθ} σθ(θ) KJ ε θ s dθ) ds`.
* The inner integral is the weight comparison `thWeightCmp` (`Work.FTS.EllSol.K5cAux`), which is
  proved for `s ∈ (0, π/2)`; the two endpoints are null, so it holds a.e. (`KJ_schur_ae`), whence
  by `integral_mono_ae` the expression is at most `3 K₁ ∫_{Iθ} (g s)² σθ s ds`.

The constant is `K = 3 K₁` with `K₁` from `thWeightCmp`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux
import Submission.Work.FTS.EllSol.EllPkgAux.kernelSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-- The `L²` Schur bound of `thWeightCmp`, in the `a.e.` form over `Iθ` (the two endpoints of
`Iθ`, where the weight `σθ` vanishes, are null). -/
theorem KJ_schur_ae {K₁ ε : ℝ}
    (hK : ∀ u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ θ in Iθ, σθ θ * KJ ε θ u) ≤ K₁ * σθ u) :
    ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s := by
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hK
  have hμ : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    restrict_Iθ_eq_restrict_Ioo
  rw [← hμ] at h1
  exact h1

theorem kernelJensen : ∃ K : ℝ, 0 < K ∧ ∀ (g : ℝ → ℝ), MeasureTheory.IntegrableOn (fun s : ℝ => g s ^ 2 * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ * (∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * g s) ^ 2) ≤ K * ∫ s in Work.Spaces.Iθ, g s ^ 2 * Work.FTS.EllipticEst.thEta s := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.K5cAux.thWeightCmp
  refine ⟨3 * K₁, by positivity, ?_⟩
  intro g hg ε hε hε2
  change (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s
  have hg2int : IntegrableOn (fun s : ℝ => g s ^ 2) Iθ := integrableOn_sq_of_integrableOn hg
  obtain ⟨hswap_eq, hswap_i1, hswap_i2⟩ := kernelSwap (g := g) hε hg2int
  -- the pointwise bound, integrated
  have hA : IntegrableOn (fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) Iθ :=
    hswap_i1.const_mul 3
  have hmono : (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg (f := fun θ : ℝ =>
        σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      (g := fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) ?_ hA ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have hpt := KJ_pointwise (g := g) (ε := ε) (θ := θ) hε hg hθ
        have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        calc σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2
            ≤ σθ θ * (3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
              mul_le_mul_of_nonneg_left hpt hσ
          _ = 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by ring)
  -- pull out the constant and swap the two integrals
  have hc1 : (∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2))
      = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_const_mul 3 _
  -- the Schur bound, a.e. in `s`
  have hschur : ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    KJ_schur_ae (K₁ := K₁) (ε := ε) (fun u hu => hK₁ ε u hε hε2 hu)
  have hKσ_int : IntegrableOn (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) Iθ :=
    MeasureTheory.Integrable.congr (hg.const_mul K₁) (Filter.Eventually.of_forall (fun s => by
      show K₁ * (g s ^ 2 * σθ s) = g s ^ 2 * (K₁ * σθ s)
      ring))
  have hmono2 : (∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s))
      ≤ ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
    refine MeasureTheory.integral_mono_ae hswap_i2 hKσ_int ?_
    filter_upwards [hschur] with s hs
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg (g s))
  have hKσ_eq : (∫ s in Iθ, g s ^ 2 * (K₁ * σθ s)) = K₁ * ∫ s in Iθ, g s ^ 2 * σθ s := by
    have he : (fun s : ℝ => g s ^ 2 * (K₁ * σθ s))
        = fun s : ℝ => K₁ * (g s ^ 2 * σθ s) := by
      funext s; ring
    rw [he, MeasureTheory.integral_const_mul]
  calc (∫ θ in Iθ, σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := hmono
    _ = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := hc1
    _ = 3 * ∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s) := by rw [hswap_eq]
    _ ≤ 3 * ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
          exact mul_le_mul_of_nonneg_left hmono2 (by norm_num)
    _ = 3 * (K₁ * ∫ s in Iθ, g s ^ 2 * σθ s) := by rw [hKσ_eq]
    _ = (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s := by ring

end Work.FTS.EllSol.EllPkgAux
