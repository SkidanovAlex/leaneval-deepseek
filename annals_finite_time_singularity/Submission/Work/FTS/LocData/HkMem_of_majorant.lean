/-
# `Work.FTS.LocData.HkMem_of_majorant` — the `𝓗^k`-membership by domination

The `ℋ^k`-integrand of the paper is a finite sum of squares of weighted derivatives, hence
*nonnegative*; this module shows that it is enough to dominate it pointwise, on the whole
quadrant `Iz ×ˢ Iθ`, by a function `M` whose slices `θ ↦ M z θ` are integrable on `Iθ` and
whose `θ`-integral `z ↦ ∫_θ M z θ` is integrable on `Iz`: then `f ∈ ℋ^k`
(`Work.Spaces.HkMem α k f`), i.e. all the weighted derivatives occurring in `HkSq` give honest
iterated integrals.

The two ingredients beyond nonnegativity and the domination are

* **measurability**: `HkIntegrand α k f` involves `deriv` with a parameter, and is *not*
  a.e.-strongly measurable for an arbitrary `f : ℝ → ℝ → ℝ` (a non-measurable dependence on `θ`
  of a `z`-linear profile survives differentiation in `z`).  This is exactly where the
  hypothesis `hcont` — continuity of the integrand on the open quadrant `(0,∞) × (0,π/2)` — is
  used.  It is applied twice: to the `θ`-slices (via `continuousOn_slice_theta`) and, through
  Fubini's measurability theorem `AEStronglyMeasurable.integral_prod_right'`, to the `z`-integral
  of the slices.
* **the endpoints are null sets**: the domain is the *closed* quadrant, while `hcont` only holds
  on the open one; all the statements are therefore first proved on the open sets
  `Ioo 0 (π/2)` resp. `Ioi 0` and transported along the a.e.-equalities
  `Ioo 0 (π/2) =ᵐ Iθ`, `Ioi 0 =ᵐ Iz` (`MeasureTheory.Ioo_ae_eq_Icc`,
  `MeasureTheory.restrict_Ioi_eq_restrict_Ici`).

The motivating instance (`HkMem_hLoc`, `HkMem_zfar_Fstar`, …) is
`M z θ = C · angMaj α θ / (1+z)^2` with `angMaj` the angular majorant of the chapter: its
`θ`-slices are integrable (`angMaj_mem`) and `z ↦ 1/(1+z)^2` is integrable on `Iz`, so
`hMslice` and `hMz` are available.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- The `θ`-slice of a function continuous on the open quadrant is continuous on `(0,π/2)`.

Stated for a *variable* curried function `G`, so that the composition `G ∘ (z, ·)` is performed
in the abstract (where the reduction `((z,θ)).1 = z` is all that is needed); instantiating `G` at
a concrete partially applied integrand such as `Work.Spaces.HkIntegrand α k f` then costs
nothing, whereas inlining the composition at the concrete integrand forces the elaborator to
unfold the (large) definition of the integrand. -/
theorem continuousOn_slice_theta {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z : ℝ} (hz : 0 < z) : ContinuousOn (fun θ => G z θ) (Set.Ioo 0 (π / 2)) := by
  have h2 : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (π / 2)) :=
    continuousOn_const.prodMk
      (continuousOn_id : ContinuousOn (fun θ : ℝ => θ) (Set.Ioo 0 (π / 2)))
  refine hG.comp h2 ?_
  intro θ hθ
  exact ⟨hz, hθ⟩

/-- **The `ℋ^k`-integrand vanishes on the axis `z = 0`** (the radial weight `w z = (1+z)²/z²`
is `0` there, by the junk value of Lean's division, and every term of the integrand carries a
factor `w z`). -/
theorem HkIntegrand_zero_fst (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]

/-- **Membership in `ℋ^k` by domination.**  If the `ℋ^k`-integrand of `f` is continuous on the
open quadrant, is dominated by `M` on the closed quadrant, and `M` has integrable `θ`-slices and
integrable slice-integral, then `f ∈ ℋ^k`. -/
theorem HkMem_of_majorant (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc
  -- Step 1: the `θ`-slices of the integrand are integrable on `Iθ`.
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (HkIntegrand_zero_fst α k f θ).symm
    · -- `z > 0`: domination by the (integrable) slice of `M`, plus continuity of the slice
      refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      have hbnd : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
          ‖Work.Spaces.HkIntegrand α k f z θ‖ ≤ M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo]
        refine Filter.Eventually.of_forall fun θ hθ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
        exact hle z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      exact hbnd
  -- Step 2: the `z`-integral of the slices is integrable on `Iz`.
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hle_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α k f z θ ≤ M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
        exact Filter.Eventually.of_forall fun θ hθ => hle z hz θ hθ
      exact MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        (hMslice z hz) hle_ae
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · -- measurability of the slice-integral, by Fubini on the open quadrant
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · -- the a.e. domination by `∫_θ M z θ`
      have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        refine Filter.Eventually.of_forall fun z hz => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
        exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

end Work.FTS.LocData
