import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Clauses.PsiWt.deriv_comp_clamp
import Submission.Work.FTS.FireFix.Clauses.PsiWt.continuousOn_box_of_regPkg
import Submission.Work.FTS.FireFix.Clauses.PsiWt.Dth_sq_sin_rpow_le_HkIntegrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(D_θ (gSlice g τ))² · sin(2|θ|)^{-γ}` on the box `(0,∞) × (-π/2, π/2)`

The clause `PsiWt.integrableOn_Dth_sq_sin_rpow` of the FireFix pressure input.

**The mathematics.**  With `f = gSlice g τ` and `γ = gam (pExp α) = 1 + 3α/10 > 1`, the
integrand is `(D_θf)² · sin(2|θ|)^{-γ} = sin(2|θ|)^{2-γ} · (∂_θf)²` (since `D_θ = sin 2θ · ∂_θ`),
i.e. the angular derivative weighted by the integrability weight of the `ℋ⁴`-norm with the
radial weight `w²` removed.  Since `w(z) = (1+z)²/z² ≥ 1` for `z > 0`, removing it only makes
the integrand *smaller*, and `hH4 : HkMem (pExp α) 4 f` gives, through
`Work.Spaces.sq_le_HkIntegrand_mixed` applied to the slot `(i,j) = (1,0)` (whose base is
`mixed 0 1 f = D_θf`, definitionally), integrability of the dominating `ℋ⁴`-integrand.

**The formal difficulty** is *not* the estimate but the measurability bookkeeping: `HkMem` only
provides integrability of the *angular slices* `θ ↦ HkIntegrand … z θ` for each `z ∈ Iz` and of
the *partially integrated* `z ↦ ∫_θ HkIntegrand … z θ`, and the joint (product-measure) a.e.
strong measurability of the integrand is *not* implied by those two facts alone (see
`Submission/Work/Spaces/Slots/lintegral_DzIter_le_HkSq.lean` for a machine-checked diagnosis of
exactly this gap).  The way out is that the only genuinely `θ`-differentiated quantity occurring
is `D_θf = sin(2θ) ∂_θ (g z · τ)`, and the *parametric* derivative
`(z,θ) ↦ deriv (fun θ' => g z θ' τ) θ` **is** Borel measurable: `g` is `α`-Hölder on the box by
the `Jet` field, so (clamping both variables into the box) it extends to a *continuous* function
on `ℝ²`, and Mathlib's `measurable_deriv_with_param` then gives the measurability of the
parametric derivative.  With joint measurability of the integrand in hand, the
product-integrability criterion `MeasureTheory.integrable_prod_iff` needs exactly the two facts
`HkMem` provides (slice integrability and integrability of the partially integrated majorant) —
in that `z`-outer order, so no one-sided Tonelli exchange is required.  The lower half of the
`θ`-interval is handled by the reflection `θ ↦ -θ`.

**Layout.**  `clampθ` (the clamp into `Iθ`), the delegated `continuousOn_box_of_regPkg` (the
Hölder slice of `g`),
`Gclamp` (`g` clamped into the box, jointly continuous on `ℝ²`), `measurable_param_deriv`,
`deriv_Gclamp_eq_pth` (the parametric derivative computes `pth`), `aesm_Dth_sq` (joint
measurability of the integrand), `slice_bound` (the pointwise domination: its open-quadrant half
is the delegated `Dth_sq_sin_rpow_le_HkIntegrand`, the two endpoints give `0`),
`integrableOn_positive` (product integrability on the upper half `(0,∞) × (0,π/2)` through
`integrable_prod_iff`), `integrableOn_neg_snd_reflect` (the reflection transfer; the sibling
module `…PsiWt.integrableOn_neg_snd` declares the same statement under the requested name), and
the assembly.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal NNReal

namespace Work.FTS.FireFix.Clauses.PsiWt

set_option autoImplicit false

/-! ## Auxiliary measure identities -/

/-- On `ℝ × ℝ` the Lebesgue measure is the product of the two Lebesgue measures, so
restrictions to a product of intervals split. -/
theorem prod_restrict_volume (s t : Set ℝ) :
    (volume.restrict s).prod (volume.restrict t) = volume.restrict (s ×ˢ t) := by
  rw [Measure.prod_restrict, show (volume.prod volume : Measure (ℝ × ℝ)) = volume from rfl]

/-! ## The clamp of `ℝ` into `Iθ = [0, π/2]` -/

/-- The clamp `θ ↦ max 0 (min θ (π/2))`, whose range is `Iθ`. -/
def clampθ (θ : ℝ) : ℝ := max 0 (min θ (Real.pi / 2))

theorem clampθ_mem (θ : ℝ) : clampθ θ ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  exact ⟨le_max_left _ _, max_le (by linarith [Real.pi_pos]) (min_le_right _ _)⟩

theorem clampθ_eq_self {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : clampθ θ = θ := by
  simp only [clampθ, min_eq_left hθ.2.le, max_eq_right hθ.1.le]

theorem continuous_clampθ : Continuous clampθ := by
  unfold clampθ
  exact continuous_const.max (continuous_id.min continuous_const)

/-- The clamp is the identity on a neighbourhood of every interior point, so it can be dropped
under `deriv` there. -/
theorem deriv_comp_clampθ {F : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => F (clampθ θ')) θ = deriv F θ := by
  have h := deriv_comp_clamp (F := F) (θ := θ) hθ
  simpa only [clampθ] using h

/-! ## Measurability of a real power -/

theorem measurable_rpow_const (c : ℝ) : Measurable (fun x : ℝ => x ^ c) := by
  refine measurable_of_continuousOn_compl_singleton (0 : ℝ) fun x hx => ?_
  exact (Real.continuousAt_rpow_const x c (Or.inl (by simpa using hx))).continuousWithinAt

/-! ## Joint continuity of a slice of `g` on the closed box -/

/-! ## The clamped profile and its parametric derivative -/

/-- `g(·,·,τ)` clamped into the closed box `Iz ×ˢ Iθ` in both variables.  On `z > 0`,
`θ ∈ (0, π/2)` it agrees with `g(·,·,τ)` on a neighbourhood of that point. -/
def Gclamp {g : ℝ → ℝ → ℝ → ℝ} (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => g (max z 0) (clampθ θ) τ

theorem continuous_uncurry_Gclamp {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Continuous (Function.uncurry (Gclamp (g := g) τ)) := by
  have hbox := continuousOn_box_of_regPkg h hτ
  have hmap : Continuous fun p : ℝ × ℝ => (max p.1 0, clampθ p.2) :=
    (continuous_fst.max continuous_const).prodMk (continuous_clampθ.comp continuous_snd)
  have hmaps : ∀ p : ℝ × ℝ, (max p.1 0, clampθ p.2) ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    fun p => ⟨by rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_max_right p.1 0,
      clampθ_mem p.2⟩
  have hcomp := hbox.comp_continuous hmap hmaps
  have hfun : (Function.uncurry (Gclamp (g := g) τ))
      = ((fun p : ℝ × ℝ => g p.1 p.2 τ) ∘ fun p : ℝ × ℝ => (max p.1 0, clampθ p.2)) := rfl
  rw [hfun]
  exact hcomp

/-- The parametric derivative of the clamped profile is Borel measurable on `ℝ²`. -/
theorem measurable_param_deriv {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Measurable (fun p : ℝ × ℝ => deriv (fun θ' => Gclamp (g := g) τ p.1 θ') p.2) :=
  measurable_deriv_with_param (𝕜 := ℝ) (f := Gclamp (g := g) τ) (continuous_uncurry_Gclamp h hτ)

/-- On the open quadrant the parametric derivative of the clamped profile is `∂_θ` of the slice
of `g`. -/
theorem deriv_Gclamp_eq_pth {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Gclamp (g := g) τ z θ') θ
      = Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ := by
  have h1 : (fun θ' => Gclamp (g := g) τ z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ' τ) :=
    eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ) (fun θ' hθ' => by
      simp only [Gclamp, max_eq_left hz.le, clampθ_eq_self hθ'])
  rw [h1.deriv_eq]
  rfl

/-! ## Joint measurability of the integrand on the upper half-box -/

/-- The integrand `(D_θf)²·sin(2θ)^{-γ}` (`f = gSlice g τ`) is a.e. strongly measurable for the
product measure on `(0,∞) × (0,π/2)`. -/
theorem aesm_Dth_sq {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    AEStronglyMeasurable (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
  have hD := measurable_param_deriv h hτ
  have hsin : Measurable (fun q : ℝ × ℝ => Real.sin (2 * q.2)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_snd)
  have hnice : Measurable (fun q : ℝ × ℝ =>
      (Real.sin (2 * q.2) * deriv (fun θ' => Gclamp (g := g) τ q.1 θ') q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) :=
    ((hsin.mul hD).pow_const 2).mul ((measurable_rpow_const _).comp hsin)
  refine hnice.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with q hq
  rw [Work.Spaces.Dth, ← deriv_Gclamp_eq_pth (g := g) (τ := τ) hq.1 hq.2]

/-- **The folded angular derivative is a.e. strongly measurable.**  This is the statement of the
sibling clause `PsiWt.aesm_pth_abs` (`∂_θ (gSlice g τ)` folded in `θ`), obtained here from the
parametric-derivative machinery above; it is recorded under this (different) name so that it does
not clash with the sibling module `…PsiWt.aesm_pth_abs` that owns the clause.  Only the line
`q.2 = 0` — the boundary between the two halves of the angular interval — is not covered by
`deriv_Gclamp_eq_pth`, and it is null. -/
theorem aesm_pth_fold {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    AEStronglyMeasurable (fun q : ℝ × ℝ =>
      Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (|q.2|))
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
  have hD := measurable_param_deriv h hτ
  have hfold : Measurable (fun q : ℝ × ℝ =>
      deriv (fun θ' => Gclamp (g := g) τ q.1 θ') (|q.2|)) :=
    hD.comp (continuous_fst.prodMk (continuous_abs.comp continuous_snd)).measurable
  refine hfold.aestronglyMeasurable.congr ?_
  have hz0 : (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod,
      MeasureTheory.measure_singleton, mul_zero]
  have hae0 : ∀ᵐ q ∂(volume.restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))), q.2 ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [Measure.restrict_apply (show MeasurableSet {q : ℝ × ℝ | q.2 = 0} from
      (measurableSet_singleton (0 : ℝ)).preimage measurable_snd)]
    refine measure_mono_null ?_ hz0
    rintro q ⟨hq, -⟩
    exact ⟨trivial, by simpa using hq⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo), hae0] with q hq hq0
  have hlo : -(Real.pi / 2) < q.2 := hq.2.1
  have hhi : q.2 < Real.pi / 2 := hq.2.2
  rcases lt_or_gt_of_ne hq0 with hlt | hgt
  · rw [abs_of_neg hlt]
    exact deriv_Gclamp_eq_pth hq.1 ⟨by linarith, by linarith⟩
  · rw [abs_of_pos hgt]
    exact deriv_Gclamp_eq_pth hq.1 ⟨hgt, hhi⟩

/-! ## The pointwise domination by the `ℋ⁴`-integrand -/

/-- The pointwise domination on the closed interval `[0, π/2]` (the two endpoints give `0`). -/
theorem slice_bound {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      ≤ Work.Spaces.HkIntegrand a 4 f z θ := by
  have hgam : 0 < Work.Spaces.gam a := by rw [Work.Spaces.gam]; linarith
  by_cases hint : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · exact Dth_sq_sin_rpow_le_HkIntegrand ha f hz hint
  · have hfl : θ = 0 ∨ θ = Real.pi / 2 := by
      rw [Set.mem_Ioo, not_and_or] at hint
      rcases hint with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) hθ.1)
      · exact Or.inr (le_antisymm hθ.2 (not_lt.mp h))
    rcases hfl with h | h
    · subst h
      have hzero : (Real.sin (2 * (0 : ℝ))) ^ (-(Work.Spaces.gam a)) = 0 := by
        rw [show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
          Real.zero_rpow (x := -(Work.Spaces.gam a)) (by linarith)]
      rw [hzero, mul_zero]
      exact Work.Spaces.HkIntegrand_nonneg a 4 f z 0
    · subst h
      have hzero : (Real.sin (2 * (Real.pi / 2))) ^ (-(Work.Spaces.gam a)) = 0 := by
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
          Real.zero_rpow (x := -(Work.Spaces.gam a)) (by linarith)]
      rw [hzero, mul_zero]
      exact Work.Spaces.HkIntegrand_nonneg a 4 f z (Real.pi / 2)

/-! ## The product integrability on the upper half-box -/

/-- The integrand `(D_θf)² sin(2θ)^{-γ}` is integrable on `(0,∞) × (0,π/2)`. -/
theorem integrableOn_positive {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hα : 0 < α := h.hα
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hmem := h.hH4 τ hτ
  set F : ℝ × ℝ → ℝ := fun q =>
    (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
      * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))) with hF
  have hν : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hprod : (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Measure.restrict_congr_set hν, prod_restrict_volume]
  have hFnn : ∀ z θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → 0 ≤ F (z, θ) := fun z θ hθ => by
    rw [hF]
    refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have haesm : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hprod]
    exact aesm_Dth_sq h hτ
  have hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ : ℝ => F (z, θ)) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
    have hKs : Integrable (fun θ => Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict Work.Spaces.Iθ) := hmem.1 z hzIz
    have hslice_meas : AEStronglyMeasurable (fun θ : ℝ => F (z, θ))
        (volume.restrict Work.Spaces.Iθ) := by
      have hderiv : Measurable (fun θ : ℝ => deriv
          (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) :=
        measurable_deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ')
      have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.measurable_sin.comp (measurable_const.mul measurable_id)
      have hmeas : Measurable (fun θ : ℝ =>
          (Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) :=
        (((hsin.mul hderiv).pow_const 2)).mul ((measurable_rpow_const _).comp hsin)
      have heq : (fun θ : ℝ => F (z, θ)) = (fun θ : ℝ =>
          (Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) := by
        funext θ
        simp only [hF, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq]
      exact hmeas.aestronglyMeasurable
    refine Integrable.mono' hKs hslice_meas ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (hFnn z θ hθ), hF]
    exact slice_bound hp0 _ hz hθ
  have houter : Integrable (fun z => ∫ θ, ‖F (z, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hA : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict Work.Spaces.Iz) := hmem.2
    have hA' : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      Integrable.mono_measure hA (Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl)
    refine Integrable.mono' hA' (haesm.norm.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg_of_ae (Eventually.of_forall fun θ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _)
      (hmem.1 z hzIz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (hFnn z θ hθ), hF]
    exact slice_bound hp0 _ hz hθ
  have key : Integrable F
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff (f := F) haesm).mpr ⟨hslice, houter⟩
  rw [IntegrableOn, ← hprod]
  exact key

/-! ## Reflection in the angular variable -/

/-- Integrability on the upper half-box transfers to the lower half-box by the reflection
`θ ↦ -θ`. -/
theorem integrableOn_neg_snd_reflect {f : ℝ × ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f p)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f (p.1, -p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) := by
  have hpre : Neg.neg ⁻¹' Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo (-(Real.pi / 2)) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hneg : (volume.restrict (Set.Ioo (-(Real.pi / 2)) 0)).map Neg.neg
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := measurableEmbedding_neg.restrict_map (volume : Measure ℝ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [hpre, Measure.map_neg_eq_self (volume : Measure ℝ)] at h
    exact h.symm
  have he : MeasurableEmbedding (fun p : ℝ × ℝ => (p.1, -p.2)) := by
    have hfun : (fun p : ℝ × ℝ => (p.1, -p.2))
        = (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ) :
            ℝ × ℝ → ℝ × ℝ) := rfl
    rw [hfun]
    exact (MeasurableEquiv.prodCongr _ _).measurableEmbedding
  have hmap : (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)).map
        (fun p : ℝ × ℝ => (p.1, -p.2))
      = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h2 : (fun p : ℝ × ℝ => (p.1, -p.2)) = Prod.map id Neg.neg := rfl
    rw [← prod_restrict_volume (Set.Ioi (0 : ℝ)) (Set.Ioo (-(Real.pi / 2)) 0), h2,
      ← Measure.map_prod_map (volume.restrict (Set.Ioi (0 : ℝ)))
        (volume.restrict (Set.Ioo (-(Real.pi / 2)) 0)) measurable_id measurable_neg,
      Measure.map_id, hneg]
    exact prod_restrict_volume _ _
  have hiff : Integrable f
        (Measure.map (fun p : ℝ × ℝ => (p.1, -p.2))
          (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)))
      ↔ Integrable (fun p : ℝ × ℝ => f (p.1, -p.2))
          (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) :=
    MeasurableEmbedding.integrable_map_iff he
  rw [hmap] at hiff
  exact hiff.mp (by simpa only [IntegrableOn] using h)

/-! ## The target -/

theorem integrableOn_Dth_sq_sin_rpow {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (|q.2|)) ^ 2
        * (Real.sin (2 * |q.2|)) ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  set p := Work.FTS.Regularity.pExp α with hp
  set f₀ := Work.FTS.Regularity.gSlice g τ with hf₀
  set F : ℝ × ℝ → ℝ := fun q =>
    (Work.Spaces.Dth f₀ q.1 (|q.2|)) ^ 2 * (Real.sin (2 * |q.2|)) ^ (-(Work.Spaces.gam p))
    with hF
  have hpos : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth f₀ q.1 q.2) ^ 2 * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam p)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := integrableOn_positive h hτ
  have h1 : MeasureTheory.IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hpos.congr_fun (fun q hq => by simp only [hF]; rw [abs_of_pos hq.2.1])
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hneg : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth f₀ q.1 (-q.2)) ^ 2 * (Real.sin (2 * (-q.2))) ^ (-(Work.Spaces.gam p)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) := integrableOn_neg_snd_reflect hpos
  have h2 : MeasureTheory.IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) :=
    hneg.congr_fun (fun q hq => by simp only [hF]; rw [abs_of_neg hq.2.2])
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hunion : MeasureTheory.IntegrableOn F
      ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
        ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) := h1.union h2
  have hsub : ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
        \ ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
          ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)))
      ⊆ Set.univ ×ˢ ({0} : Set ℝ) := by
    intro q hq
    rw [Set.mem_sdiff] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq1
    refine ⟨trivial, ?_⟩
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hq2 (Or.inr (by
        rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hq1.1, hq1.2.1, hlt⟩))
    · exact hq2 (Or.inl (by
        rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hq1.1, hgt, hq1.2.2⟩))
  have hz : (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod,
      MeasureTheory.measure_singleton, mul_zero]
  have hsub2 : ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
        ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0))
      ⊆ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set (ℝ × ℝ)) := by
    intro q hq
    rw [Set.mem_union, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_prod, Set.mem_Ioi,
      Set.mem_Ioo] at hq
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨h1, by linarith, by linarith⟩
    · exact ⟨h1, by linarith, by linarith⟩
  have hae : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set (ℝ × ℝ))
      =ᵐ[volume]
        ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
          ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨measure_mono_null hsub hz,
      by rw [Set.sdiff_eq_empty.mpr hsub2, measure_empty]⟩
  have hgoal : MeasureTheory.IntegrableOn F
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    rw [IntegrableOn, Measure.restrict_congr_set hae]
    exact hunion
  exact hgoal

end Work.FTS.FireFix.Clauses.PsiWt
