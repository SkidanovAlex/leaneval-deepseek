import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceIntegrable
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBoxIntegrable
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDeriv
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDerivBox
import Submission.Work.FTS.EllipticEst.remov.SourceBound.pzBoxIntegrableOfSlice
import Submission.Work.FTS.EllipticEst.remov.SourceBound.chainZero
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSlicePzIter3
import Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceHonestOfBox
import Submission.Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm
import Submission.Work.FTS.EllipticEst.remov.SourceBound.diffEqAlphaNeg5
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceLzeroHonest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `Lzero1` on a slice vanishes

Target (`sliceMomentIdentity`): for a datum of the weak hypothesis class `EllWeakPos α k F Ψ`
(`k ≥ 2`) and every `z > 0`,

`∫_{Iθ} Lzero1 (fun t => Ψ z t) θ * sinθcos²θ dθ = 0`,

i.e. the `L₀`-moment of the slice `Ψ z ·` vanishes.  Equivalently (when the integral is honest)
the two boundary values of the antiderivative
`G θ = -(deriv (fun t => Ψ z t) θ) * sinθcos²θ + Ψ z θ * (cos θ * cos (2θ))` agree.

## Strategy

* `Lzero1 (Ψ z ·) · sc = F z · · sc + α²z²·(∂_z²Ψ) z · · sc + α(5+α)z·(∂_zΨ) z · · sc` pointwise
  on the open quadrant (definitional form of `bslOp α Ψ = F`).
* If the `Lzero1`-moment at `z₀` is not honest the totalised integral is `0`
  (`MeasureTheory.integral_undef`).
* Otherwise the boundary estimate `∫ |Lzero1 u| sc < ∞ ⟹ ∫ |u| sc < ∞` (for `u` of class `C²`
  on `(0,π/2)`) gives the honesty of the slices of `Ψ`, `∂_zΨ`, `∂_z²Ψ`, and the moment chain
  `Θ(Ψ(w,·)) ≡ 0 ⟹ Θ(∂_zΨ(w,·)) ≡ 0 ⟹ Θ(∂_z²Ψ(w,·)) ≡ 0` (Fubini plus the fundamental theorem
  of calculus in `z`, the joint integrability coming from the `ℋ^k`-bounds) forces the two
  `z`-moments at `z₀` to vanish.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## The moment functional -/

/-- The angular moment `Θ(g)(z) = ∫_{Iθ} g z θ * sinθcos²θ dθ` (totalised integral). -/
def Mom (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, g z θ * Work.Elliptic.sinCos2 θ

/-! ## The algebraic form of the equation on a slice -/

/-- `Lzero` and `Lzero1` agree on the `z`-slice of `Ψ` (definitional identity). -/
theorem Lzero_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero Ψ z θ = Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ := rfl

/-- The elliptic operator computed on a slice: `Work.Elliptic.bslOp_apply` with the angular part
rewritten through `Lzero1`. -/
theorem bslOp_slice_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.bslOp α Ψ z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        + Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ := by
  rw [Work.Elliptic.bslOp_apply, Lzero_slice_eq]

/-- **Decomposition of the `Lzero1`-moment of a slice.**  If the slices of `F`, of `∂_z²Ψ` and of
`Lzero1 (Ψ z ·)` are honest on `Iθ`, then so is that of `∂_zΨ`, and the moment of `Lzero1` is the
sum of the moments of `F`, `α²z²∂_z²Ψ` and `α(5+α)z∂_zΨ`. -/
theorem moment_decomposition {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcoef : α * (5 + α) * z ≠ 0)
    (heq : ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : IntegrableOn (fun θ => F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (h2 : IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (h1 : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          * Work.Elliptic.sinCos2 θ)
        = (∫ θ in Work.Spaces.Iθ, F z θ * Work.Elliptic.sinCos2 θ)
          + α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
  -- the pointwise identity on the open quadrant, coming from the equation
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ
        = F z θ * Work.Elliptic.sinCos2 θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ hθ
    rw [← heq θ hθ.1 hθ.2, bslOp_slice_eq]
    ring
  have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        * Work.Elliptic.sinCos2 θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => F z θ * Work.Elliptic.sinCos2 θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt
  -- integrability of the first two summands and of the whole sum
  have hfirst : IntegrableOn (fun θ => F z θ * Work.Elliptic.sinCos2 θ
      + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ))
      Work.Spaces.Iθ :=
    hF.add (h2.const_mul _)
  have hsum : IntegrableOn (fun θ => F z θ * Work.Elliptic.sinCos2 θ
      + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      + (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun_ae h1 hae
  have hthird : IntegrableOn (fun θ => (α * (5 + α) * z)
      * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun_ae (hsum.sub hfirst) (by
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring)
  -- divide by the (nonzero) coefficient
  have hpz : IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun_ae
      (MeasureTheory.Integrable.const_mul hthird ((α * (5 + α) * z)⁻¹)) (by
        filter_upwards with θ
        rw [inv_mul_cancel_left₀ hcoef])
  refine ⟨hpz, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae]
  rw [MeasureTheory.integral_add hfirst hthird]
  rw [MeasureTheory.integral_add hF (MeasureTheory.Integrable.const_mul h2 _)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## The main theorem -/

/-- Box integrability of `∂_z³Ψ · sinθcos²θ` — the second conjunct of the imported
`weakSlicePzIter3` (proved by an agent in the sibling file). -/
theorem weakSlicePzIter3Box {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a → MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  (weakSlicePzIter3 hk h).2

theorem sliceMomentIdentity {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ) = 0 := by
  intro z₀ hz₀
  -- Case A: the moment at `z₀` is not honest, hence the totalised integral is `0`.
  by_cases hB : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z₀ t) θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ
  swap
  · exact MeasureTheory.integral_undef hB
  -- Case B: the moment at `z₀` is honest.
  have hF0 : MeasureTheory.IntegrableOn
      (fun θ => F z₀ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (weakSliceIntegrable hk h).1 z₀ hz₀
  have hM20 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter 2 Ψ z₀ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (weakSliceIntegrable hk h).2 z₀ hz₀
  -- ## The two degenerate values of `α` where the equation does not determine `∂_zΨ`
  by_cases hdeg : α = 0
  · -- `α = 0`: the elliptic operator is `Lzero` and the moment is that of the source.
    subst hdeg
    have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z₀ t) θ
          * Work.Elliptic.sinCos2 θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => F z₀ θ * Work.Elliptic.sinCos2 θ) :=
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
        show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z₀ t) θ * Work.Elliptic.sinCos2 θ
          = F z₀ θ * Work.Elliptic.sinCos2 θ
        rw [← h.eq z₀ hz₀ θ hθ.1 hθ.2, bslOp_slice_eq]
        ring)
    rw [MeasureTheory.integral_congr_ae hae]
    exact h.orthF z₀ hz₀
  -- From now on `α ≠ 0`.  Split off the degenerate case `α * (5 + α) = 0`.
  by_cases hcoef : α * (5 + α) * z₀ = 0
  · -- `α * (5 + α) = 0` and `α ≠ 0`, hence `α = -5`: the equation does not involve `∂_zΨ`.
    have hzm : z₀ ≠ 0 := ne_of_gt hz₀
    have h5 : 5 + α = 0 := by
      rcases mul_eq_zero.mp hcoef with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hdeg
        · exact h''
      · exact absurd h' hzm
    have hα5 : α = -5 := by linarith
    -- the equation, in the form used below
    have hrel : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
        Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          = F z θ + 25 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
      intro z hz θ hθ1 hθ2
      have h1 := h.eq z hz θ hθ1 hθ2
      rw [bslOp_slice_eq, hα5] at h1
      ring_nf at h1 ⊢
      linarith
    -- the interval and the box integrability of `∂_z²Ψ · sinθcos²θ` and of `∂_z³Ψ · sinθcos²θ`
    obtain ⟨a, b, ha_pos, haz, hzb⟩ : ∃ a b : ℝ, 0 < a ∧ a < z₀ ∧ z₀ < b :=
      ⟨z₀ / 2, z₀ + z₀ / 2, by linarith, by linarith, by linarith⟩
    have hz₀I : z₀ ∈ Set.Ioo a b := ⟨haz, hzb⟩
    have hz₀Icc : z₀ ∈ Set.Icc a b := ⟨le_of_lt haz, le_of_lt hzb⟩
    have hbox2 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz Ψ) z θ
          * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hh := (weakSliceBoxIntegrable hk h) a b ha_pos
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hh
    -- the honesty of the slices of `∂_zΨ` on `[a,b]`, from the commutation of `Lzero1` with
    -- `∂_z` and the differentiated relation `Lzero1 (pz Ψ z ·) = pz F z · + 50z∂_z²Ψ + 25z²∂_z³Ψ`
    have hslpz_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      intro z hz
      have hzpos : 0 < z := lt_of_lt_of_le ha_pos hz.1
      have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
            * Work.Elliptic.sinCos2 θ)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => (Work.Spaces.pz F z θ + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
              + 50 * z * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ) := by
        refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
        show Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
            * Work.Elliptic.sinCos2 θ
          = (Work.Spaces.pz F z θ + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
              + 50 * z * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ
        rw [diffEqAlphaNeg5 hk h hα5 hzpos hθ.1 hθ.2]
      -- the right hand side is honest, hence so is the left one, hence (SliceLzeroHonest) the slice
      have hR : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.pz F z θ + 25 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
              + 50 * z * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pz F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
          (weakSliceDeriv hk h).1 z hzpos
        have h2 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
          (weakSlicePzIter3 hk h).1 z hzpos
        have h3 : MeasureTheory.IntegrableOn
            (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
          (weakSliceIntegrable hk h).2 z hzpos
        refine MeasureTheory.IntegrableOn.congr_fun
          (((h1.add (h2.const_mul (25 * z ^ 2))).add (h3.const_mul (50 * z))))
          (fun θ _ => ?_) measurableSet_Icc
        simp only [Pi.add_apply, Pi.mul_apply]
        ring
      have hL : MeasureTheory.IntegrableOn
          (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
              * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
        MeasureTheory.IntegrableOn.congr_fun_ae hR hae.symm
      have hslice2 : ContDiffOn ℝ 2 (fun t => Work.Spaces.pz Ψ z t) (Set.Ioo 0 (Real.pi / 2)) := by
        have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          fun θ hθ => ⟨hzpos, hθ⟩
        have hsm_pz : ∀ n : ℕ, ContDiffOn ℝ n
            (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun n =>
          contDiffOn_uncurry_pz_of_isOpen (isOpen_Ioi.prod isOpen_Ioo) (h.smooth (n + 1))
        have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
          fun_prop
        have hcomp : ContDiffOn ℝ 2 ((Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ))
            ∘ (fun θ : ℝ => (z, θ))) (Set.Ioo 0 (Real.pi / 2)) :=
          ContDiffOn.comp (hsm_pz 2) hcd hmap
        simpa only [Function.comp_def, Function.uncurry] using hcomp
      exact SliceLzeroHonest hslice2 hL
    -- the honesty of the `Lzero1`-moment of every slice (two honest pieces, no `∂_zΨ` term)
    have hB_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      intro z hz
      have hzpos : 0 < z := lt_of_lt_of_le ha_pos hz.1
      have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
            * Work.Elliptic.sinCos2 θ)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => F z θ * Work.Elliptic.sinCos2 θ
            + 25 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)) := by
        refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
        show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ
          = F z θ * Work.Elliptic.sinCos2 θ
            + 25 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        rw [hrel z hzpos θ hθ.1 hθ.2]
        ring
      exact MeasureTheory.IntegrableOn.congr_fun_ae
        ((((weakSliceIntegrable hk h).1 z hzpos)).add
          (((weakSliceIntegrable hk h).2 z hzpos).const_mul (25 * z ^ 2))) hae.symm
    -- the honesty of the slices of `Ψ`
    have hslice_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      intro z hz
      have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
        have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          fun θ hθ => ⟨lt_of_lt_of_le ha_pos hz.1, hθ⟩
        have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
          fun_prop
        have hcomp : ContDiffOn ℝ 2 ((Function.uncurry Ψ) ∘ (fun θ : ℝ => (z, θ)))
            (Set.Ioo 0 (Real.pi / 2)) := ContDiffOn.comp (h.smooth 2) hcd hmap
        simpa only [Function.comp_def, Function.uncurry] using hcomp
      exact SliceLzeroHonest hslice2 (hB_all z hz)
    -- the chain: the moment of `∂_zΨ` vanishes on `(a,b)`
    have hM1zero_all : ∀ z ∈ Set.Ioo a b,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 :=
      chainZero ha_pos hz₀I h.smooth hslice_all (hslpz_all z₀ hz₀Icc) hbox2
        (fun z hz => h.orthPsi z (lt_of_lt_of_le ha_pos hz.1))
    have hM1zero := hM1zero_all z₀ hz₀I
    -- the second chain: the moment of `∂_z²Ψ` at `z₀`
    have hM2zero : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z₀ θ * Work.Elliptic.sinCos2 θ) = 0 := by
      obtain ⟨a', b', haa', ha'z, hzb', hb'b⟩ :
          ∃ a' b' : ℝ, a < a' ∧ a' < z₀ ∧ z₀ < b' ∧ b' < b :=
        ⟨(a + z₀) / 2, (z₀ + b) / 2, by linarith, by linarith, by linarith, by linarith⟩
      have ha'pos : 0 < a' := lt_trans ha_pos haa'
      have hz₀I' : z₀ ∈ Set.Ioo a' b' := ⟨ha'z, hzb'⟩
      have hsm_pz : ∀ n : ℕ, ContDiffOn ℝ n
          (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun n =>
        contDiffOn_uncurry_pz_of_isOpen (isOpen_Ioi.prod isOpen_Ioo) (h.smooth (n + 1))
      have hbox3 : MeasureTheory.Integrable
          (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz
            (fun z θ => Work.Spaces.pz Ψ z θ)) z θ * Work.Elliptic.sinCos2 θ))
          ((MeasureTheory.volume.restrict (Set.Ioc a' b')).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        have hh := weakSlicePzIter3Box hk h a' b' ha'pos
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hh
      exact chainZero ha'pos hz₀I' hsm_pz
        (fun z hz => hslpz_all z ⟨le_of_lt (lt_of_lt_of_le haa' hz.1),
          le_of_lt (lt_of_le_of_lt hz.2 hb'b)⟩)
        hM20 hbox3 (fun z hz => hM1zero_all z ⟨lt_of_lt_of_le haa' hz.1,
          lt_of_le_of_lt hz.2 hb'b⟩) z₀ hz₀I'
    -- conclusion
    have hae₀ : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z₀ t) θ
          * Work.Elliptic.sinCos2 θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => F z₀ θ * Work.Elliptic.sinCos2 θ
          + 25 * z₀ ^ 2 * (Work.Spaces.pzIter 2 Ψ z₀ θ * Work.Elliptic.sinCos2 θ)) := by
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z₀ t) θ * Work.Elliptic.sinCos2 θ
        = F z₀ θ * Work.Elliptic.sinCos2 θ
          + 25 * z₀ ^ 2 * (Work.Spaces.pzIter 2 Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      rw [hrel z₀ hz₀ θ hθ.1 hθ.2]
      ring
    have hFzero : (∫ θ in Work.Spaces.Iθ, F z₀ θ * Work.Elliptic.sinCos2 θ) = 0 :=
      h.orthF z₀ hz₀
    rw [MeasureTheory.integral_congr_ae hae₀,
      MeasureTheory.integral_add hF0 (hM20.const_mul (25 * z₀ ^ 2)),
      MeasureTheory.integral_const_mul, hFzero, hM2zero]
    ring
  · -- generic case: the equation determines `∂_zΨ` and the moment chain applies.
    -- the interval on which the chain is run
    obtain ⟨a, b, ha_pos, haz, hzb⟩ : ∃ a b : ℝ, 0 < a ∧ a < z₀ ∧ z₀ < b :=
      ⟨z₀ / 2, z₀ + z₀ / 2, by linarith, by linarith, by linarith⟩
    have hz₀I : z₀ ∈ Set.Ioo a b := ⟨haz, hzb⟩
    have hz₀Icc : z₀ ∈ Set.Icc a b := ⟨le_of_lt haz, le_of_lt hzb⟩
    -- box integrability of `∂_z²Ψ · sinθcos²θ`
    have hbox2 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz Ψ) z θ
          * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hh := (weakSliceBoxIntegrable hk h) a b ha_pos
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hh
    -- box integrability of `∂_zΨ · sinθcos²θ`
    have hboxpz : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      pzBoxIntegrableOfSlice ha_pos (le_of_lt (haz.trans hzb)) hz₀Icc h.smooth hbox2
        ((moment_decomposition hz₀ hcoef (h.eq z₀ hz₀) hF0 hM20 hB).1)
    -- the honesty of the `∂_zΨ`-slices on `[a,b]`
    have hslpz_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      pzSliceHonestOfBox ha_pos hz₀Icc h.smooth
        ((moment_decomposition hz₀ hcoef (h.eq z₀ hz₀) hF0 hM20 hB).1) hbox2
    -- the honesty of the `Lzero1`-moment of every slice in `[a,b]`
    have hB_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      intro z hz
      have hzpos : 0 < z := lt_of_lt_of_le ha_pos hz.1
      have hza : α * (5 + α) * z ≠ 0 := by
        intro hcon
        have hzmul : α * (5 + α) * z = (α * (5 + α)) * z := by ring
        rcases mul_eq_zero.mp (hzmul ▸ hcon) with h' | h'
        · exact hcoef (by rw [h']; ring)
        · exact absurd h' (ne_of_gt hzpos)
      -- the a.e. decomposition at `z` and the honesty of its three pieces
      have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
            * Work.Elliptic.sinCos2 θ)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => F z θ * Work.Elliptic.sinCos2 θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
            + (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)) :=
        Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
          show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * Work.Elliptic.sinCos2 θ
            = F z θ * Work.Elliptic.sinCos2 θ
              + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
              + (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
          rw [← h.eq z hzpos θ hθ.1 hθ.2, bslOp_slice_eq]
          ring)
      exact MeasureTheory.IntegrableOn.congr_fun_ae
        ((((weakSliceIntegrable hk h).1 z hzpos).add
            (((weakSliceIntegrable hk h).2 z hzpos).const_mul _)).add
          ((hslpz_all z hz).const_mul _)) hae.symm
    -- the honesty of the slices of `Ψ` on `[a,b]`
    have hslice_all : ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
        (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      intro z hz
      -- the `θ`-slice of `Ψ` at `z` is `C²`: `(h.smooth 2).comp` applied to the map `θ ↦ (z,θ)`
      -- (`Set.MapsTo` since `z ∈ [a,b] ⊆ (0,∞)`).
      have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
        have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          fun θ hθ => ⟨lt_of_lt_of_le ha_pos hz.1, hθ⟩
        have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
          fun_prop
        have hcomp : ContDiffOn ℝ 2 ((Function.uncurry Ψ) ∘ (fun θ : ℝ => (z, θ)))
            (Set.Ioo 0 (Real.pi / 2)) := ContDiffOn.comp (h.smooth 2) hcd hmap
        simpa only [Function.comp_def, Function.uncurry] using hcomp
      exact SliceLzeroHonest hslice2 (hB_all z hz)
    -- the chain: the moment of `∂_zΨ` vanishes on `(a,b)`
    have hM1zero_all : ∀ z ∈ Set.Ioo a b,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0 :=
      chainZero ha_pos hz₀I h.smooth hslice_all
        ((moment_decomposition hz₀ hcoef (h.eq z₀ hz₀) hF0 hM20 hB).1) hbox2
        (fun z hz => h.orthPsi z (lt_of_lt_of_le ha_pos hz.1))
    have hM1zero := hM1zero_all z₀ hz₀I
    -- the second chain: the moment of `∂_z²Ψ` at `z₀`
    have hM2zero : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z₀ θ * Work.Elliptic.sinCos2 θ) = 0 := by
      -- a subinterval strictly inside `(a,b)`, so that the moment of `∂_zΨ` vanishes on it
      obtain ⟨a', b', haa', ha'z, hzb', hb'b⟩ :
          ∃ a' b' : ℝ, a < a' ∧ a' < z₀ ∧ z₀ < b' ∧ b' < b :=
        ⟨(a + z₀) / 2, (z₀ + b) / 2, by linarith, by linarith, by linarith, by linarith⟩
      have ha'pos : 0 < a' := lt_trans ha_pos haa'
      have hz₀I' : z₀ ∈ Set.Ioo a' b' := ⟨ha'z, hzb'⟩
      -- smoothness of `∂_zΨ` on the open quadrant
      have hsm_pz : ∀ n : ℕ, ContDiffOn ℝ n
          (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun n =>
        contDiffOn_uncurry_pz_of_isOpen (isOpen_Ioi.prod isOpen_Ioo) (h.smooth (n + 1))
      -- box integrability of `∂_z³Ψ · sinθcos²θ` on the subinterval
      have hbox3 : MeasureTheory.Integrable
          (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz
            (fun z θ => Work.Spaces.pz Ψ z θ)) z θ * Work.Elliptic.sinCos2 θ))
          ((MeasureTheory.volume.restrict (Set.Ioc a' b')).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        have hh := weakSlicePzIter3Box hk h a' b' ha'pos
        simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hh
      exact chainZero ha'pos hz₀I' hsm_pz
        (fun z hz => hslpz_all z ⟨le_of_lt (lt_of_lt_of_le haa' hz.1), le_of_lt (lt_of_le_of_lt hz.2 hb'b)⟩)
        hM20 hbox3 (fun z hz => hM1zero_all z ⟨lt_of_lt_of_le haa' hz.1, lt_of_le_of_lt hz.2 hb'b⟩) z₀ hz₀I'
    -- conclusion
    have hval := (moment_decomposition hz₀ hcoef (h.eq z₀ hz₀) hF0 hM20 hB).2
    have hFzero : (∫ θ in Work.Spaces.Iθ, F z₀ θ * Work.Elliptic.sinCos2 θ) = 0 :=
      h.orthF z₀ hz₀
    rw [hval, hFzero, hM1zero, hM2zero]
    ring

end Work.FTS.EllipticEst.remov.SourceBound
