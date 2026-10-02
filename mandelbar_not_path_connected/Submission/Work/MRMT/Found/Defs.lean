/-
Work.MRMT.Found — foundations of the principal solution `principal μ` (mandelbar drive).

This replaces the retired `IsQCOn`-vocabulary interface.  The consumer API is in
`Found/Api.lean`; this file holds the underlying definitions (no sorries).

Design (see `Submission/Work/NOTES_LEAD_mrmt_foundations.md`):

* `Admissible μ`: measurable, `‖μ‖ ≤ k < 1` a.e., boundedly supported.
* `PrincipalData μ`: the record produced by the limit construction — a homeomorphism `φ`
  with the decay `φ z = z + O(1/‖z‖)`, together with a sequence of C¹ diffeomorphisms `F n`
  solving the Beltrami equation for smooth coefficients `μ n → μ`, converging to `φ` (and
  their inverses to `φ.symm`) locally uniformly, with `dz (F n)` convergent in `L²_loc`.
* `principal μ`: the homeomorphism of the record (the identity where `μ` is not admissible).
* `translateL2 t`: translation `(τ_t f)(w) = f (w - t)` on `L²(ℂ)`.
* `mulL2 m`: multiplication by an a.e. bounded measurable field on `L²(ℂ)`;
  `hsol μ`: the `L²` solution `h = (1 - M_μ S)⁻¹ μ` of `h = μ (1 + S h)`.
* `pullRev μ f`: the pull-back coefficient of an orientation-reversing C¹ map.
-/
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Beurling.L2
import Submission.Work.MRMT.Beurling.exists_mul_left_L2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Admissible coefficients -/

/-- An **admissible** Beltrami coefficient: measurable, bounded by `k < 1` a.e., with
bounded support. -/
structure Admissible (μ : ℂ → ℂ) : Prop where
  meas : AEStronglyMeasurable μ volume
  bound : ∃ k : ℝ, k < 1 ∧ ∀ᵐ z ∂volume, ‖μ z‖ ≤ k
  bdd : Bornology.IsBounded (Function.support μ)

theorem Admissible.aestronglyMeasurable {μ : ℂ → ℂ} (h : Admissible μ) :
    AEStronglyMeasurable μ volume := h.meas

/-! ## The record produced by the limit construction -/

/-- The data of a principal solution of the Beltrami equation for `μ`: a homeomorphism `φ`
with the normalisation `φ z = z + O(1/‖z‖)`, together with smooth approximating
coefficients `μ n` and C¹ diffeomorphisms `F n` solving the Beltrami equation for `μ n`,
convergent to `φ` (and to `φ.symm` for the inverses) locally uniformly, and whose
Wirtinger derivative `dz (F n)` converges in `L²` on compacts. -/
structure PrincipalData (μ : ℂ → ℂ) where
  /-- the principal solution -/
  φ : ℂ ≃ₜ ℂ
  /-- decay constant -/
  C : ℝ
  /-- threshold for the decay -/
  R : ℝ
  /-- normalisation: `φ z = z + O(1/‖z‖)` -/
  decay : ∀ z : ℂ, R ≤ ‖z‖ → ‖φ z - z‖ ≤ C / ‖z‖
  /-- uniform dilatation bound for the approximants -/
  k : ℝ
  hk : k < 1
  /-- smooth approximating coefficients -/
  μn : ℕ → ℂ → ℂ
  contDiff_μn : ∀ n, ContDiff ℝ 1 (μn n)
  compactSupport_μn : ∀ n, HasCompactSupport (μn n)
  norm_μn : ∀ n z, ‖μn n z‖ ≤ k
  tendsto_μn : ∀ᵐ z ∂volume, Tendsto (fun n => μn n z) atTop (𝓝 (μ z))
  /-- C¹-diffeomorphism approximants solving the Beltrami equation -/
  Fn : ℕ → ℂ ≃ₜ ℂ
  contDiff_Fn : ∀ n, ContDiff ℝ 1 ((Fn n : ℂ → ℂ))
  contDiff_symm_Fn : ∀ n, ContDiff ℝ 1 (((Fn n).symm : ℂ → ℂ))
  beltrami_Fn : ∀ n z, dzbar (Fn n : ℂ → ℂ) z = μn n z * dz (Fn n : ℂ → ℂ) z
  tendsto_Fn : TendstoLocallyUniformly (fun n => ((Fn n : ℂ → ℂ))) (φ : ℂ → ℂ) atTop
  tendsto_symm_Fn :
    TendstoLocallyUniformly (fun n => ((Fn n).symm : ℂ → ℂ)) (φ.symm : ℂ → ℂ) atTop
  /-- `dz (F n)` converges to `D` in `L²` on compact sets.  Measured with `eLpNorm`, which
  is `⊤` for functions that are not a.e. strongly measurable or not square integrable; a
  Bochner integral would instead be the junk value `0` in that case, making the clause
  vacuous. -/
  dz_tendsto : ∃ D : ℂ → ℂ, ∀ K : Set ℂ, IsCompact K →
    Tendsto (fun n => eLpNorm (fun z => dz (Fn n : ℂ → ℂ) z - D z) 2
      (volume.restrict K)) atTop (𝓝 0)

/-! ## The `L²` operators used by the construction -/

/-- Translation on `L²(ℂ)`: `(τ_t f)(w) = f (w - t)`. -/
noncomputable def translateL2 (t : ℂ) : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun w : ℂ => w - t) (measurePreserving_sub_right volume t)
    ).toContinuousLinearMap

/-- Multiplication by an a.e. bounded measurable field on `L²(ℂ)`. -/
noncomputable def mulL2 (m : ℂ → ℂ) (hm : AEStronglyMeasurable m volume)
    (hm1 : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ 1) : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  Classical.choose (Beurling.exists_mul_left_L2 m hm hm1)

theorem mulL2_norm_le (m : ℂ → ℂ) (hm : AEStronglyMeasurable m volume)
    (hm1 : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ 1) : ‖mulL2 m hm hm1‖ ≤ 1 :=
  (Classical.choose_spec (Beurling.exists_mul_left_L2 m hm hm1)).1

theorem mulL2_apply_ae (m : ℂ → ℂ) (hm : AEStronglyMeasurable m volume)
    (hm1 : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ 1) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((mulL2 m hm hm1) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      fun ξ => m ξ * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ :=
  (Classical.choose_spec (Beurling.exists_mul_left_L2 m hm hm1)).2 f

/-- The `L²` solution `h = (1 - M_μ S)⁻¹ μ` of the Ahlfors–Bers equation
`h = μ (1 + S h)` (Neumann series in the Banach algebra of operators on `L²(ℂ)`). -/
noncomputable def hsol (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    (h1 : ∀ᵐ z ∂volume, ‖μ z‖ ≤ 1) (hLp : MemLp μ 2 volume) : Lp ℂ 2 (volume : Measure ℂ) :=
  Ring.inverse (1 - (mulL2 μ hm h1).comp beurlingL2) (hLp.toLp μ)

/-- `hsol` for an admissible coefficient. -/
noncomputable def hsolA (μ : ℂ → ℂ) (hμ : Admissible μ) (hLp : MemLp μ 2 volume) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  hsol μ hμ.meas (by
    obtain ⟨k, hk, hb⟩ := hμ.bound
    filter_upwards [hb] with z hz
    exact le_trans hz hk.le) hLp

/-- `∫⁻_s ‖∂̄g‖`: the `L¹` "size" of `∂̄g` on the set `s`. -/
noncomputable def lintegralAbsDbar (g : ℂ → ℂ) (s : Set ℂ) : ENNReal :=
  ∫⁻ z in s, ENNReal.ofReal ‖dzbar g z‖

/-- `∫⁻_K ‖∂̄H − μ_F ∂H‖ · ‖∂F‖`: the change-of-variables integrand of TL. -/
noncomputable def lintegralAbsBeltrami (H μF F : ℂ → ℂ) (s : Set ℂ) : ENNReal :=
  ∫⁻ z in s, ENNReal.ofReal (‖dzbar H z - μF z * dz H z‖ * ‖dz F z‖)

/-! ## Pull-back coefficient for orientation-reversing maps -/

/-- The complex dilatation of `star ∘ φ^μ ∘ f`, i.e. the coefficient `ν` solving
`∂(star ∘ f) = ν · ∂̄(star ∘ f)`. -/
def pullRev (μ f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (star (dz f z) + star (μ (f z)) * dzbar f z) / (star (dzbar f z) + star (μ (f z)) * dz f z)

end Work.MRMT.Found
