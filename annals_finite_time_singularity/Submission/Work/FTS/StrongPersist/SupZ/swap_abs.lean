/-
Copyright: work module for the Elgindi finite-time singularity project.

# Swapping the two integrations of `|Φ s θ · Φ' s θ|`

The target lemma `Work.FTS.StrongPersist.SupZ.swap_abs` exchanges the order of the
`θ`-integration over `Iθ = [0,π/2]` with the `s`-integration over the interval `[a,b]`,
`0 < a ≤ b`, for the nonnegative integrand `|Φ s θ · Φ' s θ|`.

The measure-theoretic content is Fubini for a *nonnegative* integrand: it suffices to know
that the integrand is integrable on the product
`(volume.restrict (a,b]) ⊗ (volume.restrict Iθ)`, and for this we dominate

  `|Φ s θ · Φ' s θ| ≤ Φ s θ ^ 2 + Φ' s θ ^ 2`

and show that each square is integrable on the product.  The hypotheses give exactly this,
in the following way.  Write `u(s) = ∫ θ in Iθ, Φ s θ ^ 2`:

* `hFin` makes each angular slice integrable, so that `u(s)` is the honest (nonnegative)
  integral for every `s > 0`;
* `hFint` says that `s ↦ u(s)/s` is integrable over `(0,∞)`, and on `(a,b]` (where `s ≤ b`)
  one has the exact identity `u(s) = s · (u(s)/s)`, so `u` is integrable on `(a,b]`;
* `hGin`/`hGint` play the same role for `Φ'`, using `s ↦ u'(s)·s` and `s ≥ a` on `(a,b]`.

Joint a.e. strong measurability of the integrand comes from the continuity hypotheses
(`hcont`, `hcont'`) on the open quadrant, which differs from the closed box `(a,b] × Iθ`
by a null set.  The results are combined with
`Work.Spaces.integrable_prod_of_iterated` (Tonelli for a nonnegative function whose slices
and iterated integral are integrable) and Fubini's theorem for interval integrals
(`MeasureTheory.intervalIntegral_integral_swap`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.HkSqSwap

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SupZ

set_option autoImplicit false

/-! ## A.e. strong measurability on the box `(a,b] × Iθ` -/

/-- A function continuous on the open quadrant `(0,∞) × (0,π/2)` is almost everywhere
strongly measurable for the product of the restrictions of Lebesgue measure to `(a,b]`
(with `0 < a`) and to `[0,π/2]`.  Indeed `(a,b] ⊆ (0,∞)` by `0 < a`, and `(a,b] × [0,π/2]`
differs from the open box `(a,b) × (0,π/2)` by the null set
`{b} × [0,π/2] ∪ (a,b] × {0,π/2}`; the open box is a subset of the open quadrant, where the
function is continuous. -/
theorem aesm_uncurry_prod_Ioc_aux {g : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) := by
  have hz : (Set.Ioc a b : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo a b :=
    (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume)).symm
  have hθ : (Set.Icc (0 : ℝ) (π / 2) : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo 0 (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have hprod : (Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) (π / 2) : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Ioo a b ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact (hg.mono fun p hp => ⟨lt_trans ha hp.1.1, hp.2⟩).aestronglyMeasurable
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet

/-! ## Integrability of the partially integrated angular squares -/

/-- **Finiteness of `s ↦ ∫ θ in Iθ, Φ s θ ^ 2` on `(a,b]`, from the `1/z`-weighted
integrability of the same quantity.**

If every angular slice `θ ↦ Φ s θ ^ 2` is integrable on `Iθ` for `s > 0` (`hFin`), the
partially integrated function `s ↦ (∫ θ in Iθ, Φ s θ ^ 2) / s` is integrable on `(0,∞)`
(`hFint`), and the joint function is a.e. strongly measurable on the box (`hAE`), then
`s ↦ ∫ θ in Iθ, Φ s θ ^ 2` is integrable on `(a,b]` for `0 < a`.  On `(a,b]` one has
`s ≤ b` and `s > 0`, whence (as real numbers)
`‖∫ θ, Φ s θ ^ 2‖ = s · ‖(∫ θ, Φ s θ ^ 2)/s‖ ≤ b · ‖(∫ θ, Φ s θ ^ 2)/s‖`. -/
theorem integrable_partial_sq_div_aux {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFin : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) (Set.Icc 0 (π / 2)))
    (hFint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Set.Icc 0 (π / 2), Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hAE : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))))) :
    MeasureTheory.Integrable (fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  -- `hFin` is not needed below (the pointwise nonnegativity of the slices suffices); it is
  -- kept because it is part of the intended hypothesis set of the caller.
  have _ := hFin
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
    (g := fun s : ℝ => b * ‖(∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s‖)
    ?_ hAE.integral_prod_right' ?_
  · exact ((hFint.mono_set fun s hs => lt_trans ha hs.1).norm).const_mul b
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans ha hs.1
    have hu0 : 0 ≤ ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hus : 0 ≤ (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s :=
      div_nonneg hu0 (le_of_lt hspos)
    have hbs : 1 ≤ b / s := (one_le_div hspos).mpr hs.2
    rw [Real.norm_of_nonneg hu0, Real.norm_of_nonneg hus]
    calc ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2
        = 1 * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) := by ring
      _ ≤ (b / s) * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) :=
            mul_le_mul_of_nonneg_right hbs hu0
      _ = b * ((∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) / s) := by ring

/-- **Finiteness of `s ↦ ∫ θ in Iθ, Φ s θ ^ 2` on `(a,b]`, from the `z`-weighted
integrability of the same quantity.**

Same as `integrable_partial_sq_div_aux` but starting from the hypothesis that
`z ↦ (∫ θ in Iθ, Φ z θ ^ 2) · z` is integrable on `(0,∞)`.  On `(a,b]` one has `s ≥ a > 0`,
whence `‖∫ θ, Φ s θ ^ 2‖ = (1/s)·‖(∫ θ, Φ s θ ^ 2)·s‖ ≤ (1/a)·‖(∫ θ, Φ s θ ^ 2)·s‖`. -/
theorem integrable_partial_sq_mul_aux {Φ : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hFin : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) (Set.Icc 0 (π / 2)))
    (hGint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Set.Icc 0 (π / 2), Φ z θ ^ 2) * z) (Set.Ioi 0))
    (hAE : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))))) :
    MeasureTheory.Integrable (fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  -- `hFin` is not needed below (the pointwise nonnegativity of the slices suffices); it is
  -- kept because it is part of the intended hypothesis set of the caller.
  have _ := hFin
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2)
    (g := fun s : ℝ => (1 / a) * ‖(∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s‖)
    ?_ hAE.integral_prod_right' ?_
  · exact ((hGint.mono_set fun s hs => lt_trans ha hs.1).norm).const_mul (1 / a)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hspos : 0 < s := lt_trans ha hs.1
    have hsa : a ≤ s := le_of_lt hs.1
    have hu0 : 0 ≤ ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2 :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hus : 0 ≤ (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s :=
      mul_nonneg hu0 (le_of_lt hspos)
    have hza : 1 ≤ s / a := (one_le_div ha).mpr hsa
    rw [Real.norm_of_nonneg hu0, Real.norm_of_nonneg hus]
    calc ∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2
        = 1 * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) := by ring
      _ ≤ (s / a) * (∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) :=
            mul_le_mul_of_nonneg_right hza hu0
      _ = (1 / a) * ((∫ θ in Set.Icc 0 (π / 2), Φ s θ ^ 2) * s) := by ring

/-! ## The target -/

theorem swap_abs {Φ Φ' : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hcont' : ContinuousOn (Function.uncurry Φ') (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn (fun θ : ℝ => Φ z θ ^ 2) Work.Spaces.Iθ)
    (hGin : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn (fun θ : ℝ => Φ' z θ ^ 2) Work.Spaces.Iθ)
    (hFint : MeasureTheory.IntegrableOn (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2) / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Φ' z θ ^ 2) * z) (Set.Ioi 0)) :
    (∫ θ in Work.Spaces.Iθ, ∫ s in a..b, |Φ s θ * Φ' s θ|)
      = ∫ s in a..b, ∫ θ in Work.Spaces.Iθ, |Φ s θ * Φ' s θ| := by
  -- A.e. strong measurability of the uncurried squares.
  have hAEΦ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => Φ s θ ^ 2) (hcont.pow 2)
  have hAEΨ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Φ' p.1 p.2 ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => Φ' s θ ^ 2) (hcont'.pow 2)
  -- The angular slices are integrable for every `s ∈ (a,b]`, hence a.e.
  have hsliceΦ : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => Φ s θ ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hFin s (lt_trans ha hs.1))
  have hsliceΨ : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => Φ' s θ ^ 2)
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2))) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      (fun s hs => hGin s (lt_trans ha hs.1))
  -- The partially integrated squares are integrable.
  have houterΦ := integrable_partial_sq_div_aux (Φ := Φ) ha hFin hFint hAEΦ
  have houterΨ := integrable_partial_sq_mul_aux (Φ := Φ') ha hGin hGint hAEΨ
  -- Tonelli: the uncurried squares are integrable on the product.
  have hIntΦ : MeasureTheory.Integrable (Function.uncurry fun s θ : ℝ => Φ s θ ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))
      (G := fun s θ : ℝ => Φ s θ ^ 2) (fun _ _ => sq_nonneg _) hAEΦ hsliceΦ houterΦ).1
  have hIntΨ : MeasureTheory.Integrable (Function.uncurry fun s θ : ℝ => Φ' s θ ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))
      (G := fun s θ : ℝ => Φ' s θ ^ 2) (fun _ _ => sq_nonneg _) hAEΨ hsliceΨ houterΨ).1
  -- A.e. strong measurability of the integrand `|Φ · Φ'|`.
  have hquad : ContinuousOn (Function.uncurry fun s θ : ℝ => |Φ s θ * Φ' s θ|)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hcont.mul hcont').abs
  have hAEabs : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) :=
    aesm_uncurry_prod_Ioc_aux ha (g := fun s θ : ℝ => |Φ s θ * Φ' s θ|) hquad
  -- Domination `|Φ s θ · Φ' s θ| ≤ Φ s θ ^ 2 + Φ' s θ ^ 2` and integrability on the product.
  have hIntAbs : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |Φ p.1 p.2 * Φ' p.1 p.2|)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict (Set.Icc 0 (π / 2)))) := by
    refine MeasureTheory.Integrable.mono' (hIntΦ.add hIntΨ) hAEabs ?_
    filter_upwards with p
    have h := sq_nonneg (|Φ p.1 p.2| - |Φ' p.1 p.2|)
    have h2 : |Φ p.1 p.2 * Φ' p.1 p.2| ≤ Φ p.1 p.2 ^ 2 + Φ' p.1 p.2 ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_abs (Φ p.1 p.2), sq_abs (Φ' p.1 p.2), h]
    rwa [Real.norm_eq_abs, abs_abs]
  -- Fubini for interval integrals.
  have hIntU : MeasureTheory.Integrable
      (Function.uncurry fun s θ : ℝ => |Φ s θ * Φ' s θ|)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Set.uIoc_of_le hab]
    exact hIntAbs
  exact (MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun s θ : ℝ => |Φ s θ * Φ' s θ|) hIntU).symm

end Work.FTS.StrongPersist.SupZ
