/-
# `Work.FTS.EllSol.EllPkgAux.thMollTransfer2`

The three identities of the angular mollification `thMoll u ε z` and its first two
`θ`-derivatives, for a slice `θ ↦ u z θ` that is continuous on `Iθ = [0, π/2]`, vanishes at
both endpoints, and whose first two `θ`-derivatives exist on the open interval and are
continuous on the closed one.

Writing `ρ := sKer ε` (a smooth bump of support `[-ε, ε]` and mass `1`, `ε ≤ 1/2`),
`g s := u z s`, and

  `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`

(the three images of the doubly odd extension), the identities are

* `thMoll u ε z θ = ∫_{s ∈ Iθ} Kern ρ θ s * g s`  (the fold),
* `deriv (thMoll) θ = ∫_{s ∈ Iθ} (ρ(θ-s) + ρ(θ+s) + ρ(θ+s-π)) * (∂_θg) s`  (an integration
  by parts of the fold; the reflected pieces swap sign),
* `deriv (deriv (thMoll)) θ = ∫_{s ∈ Iθ} Kern ρ θ s * (∂_θ²g) s`  (two integrations by parts;
  the boundary terms cancel pairwise between the three reflected pieces).

The module `ThMollDefs` carries `Qcut` and `Kern`; `Qext_eq_Qcut_combination` (imported)
identifies the doubly odd extension with `Qcut g s - Qcut g (-s) - Qcut g (π - s)` on the
window met by the mollification, which is what produces the signs, and
`hasDerivAt_intervalIntegral_Kern` differentiates a `Kern`-family under the interval integral.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollAux0
import Submission.Work.FTS.EllSol.EllPkgAux.Qext_eq_Qcut_combination
import Submission.Work.FTS.EllSol.EllPkgAux.hasDerivAt_intervalIntegral_Kern
import Submission.Work.FTS.EllSol.EllPkgAux.ibp_kern_first
import Submission.Work.FTS.EllSol.EllPkgAux.integrableOn_pth_pth
import Submission.Work.FTS.EllSol.EllPkgAux.ibp_kern_second

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

/-! ## Boundedness of the derivatives of the bump -/

/-- Change of variables `x ↦ c - x` on the line. -/
theorem integral_comp_sub_eq (F : ℝ → ℝ) (c : ℝ) : (∫ x : ℝ, F (c - x)) = ∫ x : ℝ, F x := by
  calc (∫ x : ℝ, F (c - x))
      = ∫ x : ℝ, (fun y : ℝ => F (-y)) (x - c) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show F (c - x) = F (-(x - c))
        rw [show -(x - c) = c - x by ring]
    _ = ∫ y : ℝ, F (-y) := MeasureTheory.integral_sub_right_eq_self (fun y : ℝ => F (-y)) c
    _ = ∫ y : ℝ, F y := integral_comp_neg_eq F

theorem hasDerivAt_sKer (ε : ℝ) (t : ℝ) : HasDerivAt (sKer ε) (deriv (sKer ε) t) t :=
  ((contDiff_sKer ε (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem continuous_deriv_sKer (ε : ℝ) : Continuous (deriv (sKer ε)) :=
  (contDiff_sKer ε (n := 2)).continuous_deriv (by norm_num)

theorem differentiable_deriv_sKer (ε : ℝ) : Differentiable ℝ (deriv (sKer ε)) :=
  (contDiff_sKer ε (n := 2)).differentiable_deriv_two

theorem hasDerivAt_deriv_sKer (ε : ℝ) (t : ℝ) :
    HasDerivAt (deriv (sKer ε)) (deriv (deriv (sKer ε)) t) t :=
  (differentiable_deriv_sKer ε).differentiableAt.hasDerivAt

theorem contDiff_deriv_sKer (ε : ℝ) : ContDiff ℝ 1 (deriv (sKer ε)) :=
  (contDiff_sKer ε (n := (1 : ℕ∞) + 1)).deriv'

theorem continuous_deriv2_sKer (ε : ℝ) : Continuous (deriv (deriv (sKer ε))) :=
  (contDiff_deriv_sKer ε).continuous_deriv (by norm_num)

/-- The first derivative of the bump vanishes off its support. -/
theorem deriv_sKer_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (h : ε < |t|) :
    deriv (sKer ε) t = 0 := by
  have hev : sKer ε =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    rcases lt_or_ge (0 : ℝ) t with hpos | hnonpos
    · have htε : ε < t := by rwa [abs_of_pos hpos] at h
      filter_upwards [isOpen_Ioi.mem_nhds htε] with u hu
      have hu' : ε ≤ |u| := by
        rw [abs_of_pos (lt_trans hε hu)]
        exact le_of_lt hu
      exact sKer_eq_zero_of_le_abs hε hu'
    · have htε : t < -ε := by
        rw [abs_of_nonpos hnonpos] at h; linarith
      filter_upwards [isOpen_Iio.mem_nhds htε] with u hu
      have hu2 : u < -ε := hu
      have hu0 : u < 0 := by linarith
      have hu' : ε ≤ |u| := by
        rw [abs_of_neg hu0]; linarith
      exact sKer_eq_zero_of_le_abs hε hu'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- The second derivative of the bump vanishes off its support. -/
theorem deriv2_sKer_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (h : ε < |t|) :
    deriv (deriv (sKer ε)) t = 0 := by
  have hev : deriv (sKer ε) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    rcases lt_or_ge (0 : ℝ) t with hpos | hnonpos
    · have htε : ε < t := by rwa [abs_of_pos hpos] at h
      filter_upwards [isOpen_Ioi.mem_nhds htε] with u hu
      exact deriv_sKer_eq_zero_of_lt_abs hε (by rw [abs_of_pos (lt_trans hε hu)]; exact hu)
    · have htε : t < -ε := by
        rw [abs_of_nonpos hnonpos] at h; linarith
      filter_upwards [isOpen_Iio.mem_nhds htε] with u hu
      have hu2 : u < -ε := hu
      have hu0 : u < 0 := by linarith
      exact deriv_sKer_eq_zero_of_lt_abs hε (by rw [abs_of_neg hu0]; linarith)
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- A continuous function vanishing off `[-ε, ε]` is bounded. -/
theorem exists_bound_of_vanishes_off {f : ℝ → ℝ} (hcont : Continuous f) {ε : ℝ}
    (hv : ∀ t : ℝ, ε < |t| → f t = 0) : ∃ C : ℝ, ∀ t : ℝ, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Set.Icc (-ε) ε)
    isCompact_Icc hcont.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases h : |t| ≤ ε
  · refine le_trans ?_ (le_max_left _ _)
    have ht : t ∈ Set.Icc (-ε) ε := by
      rw [Set.mem_Icc]
      exact abs_le.mp h
    simpa only [Real.norm_eq_abs] using hC t ht
  · rw [hv t (not_le.mp h), abs_zero]
    exact le_max_right _ _

theorem exists_bound_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, |deriv (sKer ε) t| ≤ C :=
  exists_bound_of_vanishes_off (continuous_deriv_sKer ε)
    (fun t ht => deriv_sKer_eq_zero_of_lt_abs (t := t) hε ht)

theorem exists_bound_deriv2_sKer {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, |deriv (deriv (sKer ε)) t| ≤ C :=
  exists_bound_of_vanishes_off (continuous_deriv2_sKer ε)
    (fun t ht => deriv2_sKer_eq_zero_of_lt_abs (t := t) hε ht)

/-! ## The fold of the angular mollification -/

/-- **The fold**: the whole-line convolution defining `thMoll` sees the slice only through the
three images of the doubly odd extension, i.e. through `Kern (sKer ε) θ'`. -/
theorem thMoll_fold {u : ℝ → ℝ → ℝ} {ε z θ' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (h0 : u z 0 = 0) (hp : u z (Real.pi / 2) = 0)
    (hgc : ContinuousOn (fun s : ℝ => u z s) Iθ)
    (hθ'1 : -(1 / 4) < θ') (hθ'2 : θ' < Real.pi / 2 + 1 / 4) :
    thMoll u ε z θ' = ∫ s in Iθ, Kern (sKer ε) θ' s * u z s := by
  set g : ℝ → ℝ := fun s => u z s with hg
  have hGint : Integrable (Qcut g) := by
    have hgI : IntegrableOn g Iθ := by
      rw [hg]
      exact hgc.integrableOn_compact isCompact_Icc
    exact hgI.integrable_indicator measurableSet_Icc
  have hGneg : Integrable (fun s : ℝ => Qcut g (-s)) := hGint.comp_neg
  have hGpi : Integrable (fun s : ℝ => Qcut g (Real.pi - s)) := by
    have h2 := hGneg.comp_sub_right Real.pi
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    show Qcut g (-(s - Real.pi)) = Qcut g (Real.pi - s)
    rw [show -(s - Real.pi) = Real.pi - s by ring]
  have hI1 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g s) :=
    integrable_sKer_mul_of_integrable hε hGint
  have hI2 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g (-s)) :=
    integrable_sKer_mul_of_integrable hε hGneg
  have hI3 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g (Real.pi - s)) :=
    integrable_sKer_mul_of_integrable hε hGpi
  -- the pointwise identity
  have hpt : ∀ s : ℝ, sKer ε (θ' - s) * Qext u z s
      = sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)) := by
    intro s
    rw [hg]
    exact Qext_eq_Qcut_combination hε hε1 h0 hp hθ'1 hθ'2
  -- the two change of variables
  have hsub2 : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
      = ∫ s : ℝ, sKer ε (θ' + s) * Qcut g s := by
    have hconv : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
        = ∫ s : ℝ, (fun u : ℝ => sKer ε (θ' + u) * Qcut g u) (-s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [sub_eq_add_neg]
    rw [hconv, integral_comp_neg_eq (fun u : ℝ => sKer ε (θ' + u) * Qcut g u)]
  have hsub3 : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s))
      = ∫ s : ℝ, sKer ε (θ' + s - Real.pi) * Qcut g s := by
    have hconv : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s))
        = ∫ s : ℝ, (fun u : ℝ => sKer ε (θ' + u - Real.pi) * Qcut g u) (Real.pi - s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show sKer ε (θ' - s) * Qcut g (Real.pi - s)
        = sKer ε (θ' + (Real.pi - s) - Real.pi) * Qcut g (Real.pi - s)
      rw [show θ' + (Real.pi - s) - Real.pi = θ' - s by ring]
    rw [hconv, integral_comp_sub_eq (fun u : ℝ => sKer ε (θ' + u - Real.pi) * Qcut g u) Real.pi]
  -- integrability of the reflected pieces
  have hJ2 : Integrable (fun s : ℝ => sKer ε (θ' + s) * Qcut g s) := by
    have h := integrable_sKer_mul_of_integrable (ε := ε) (θ' := -θ') hε hGint
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    show sKer ε (-θ' - s) * Qcut g s = sKer ε (θ' + s) * Qcut g s
    rw [show -θ' - s = -(θ' + s) by ring, sKer_even]
  have hJ3 : Integrable (fun s : ℝ => sKer ε (θ' + s - Real.pi) * Qcut g s) := by
    have h := integrable_sKer_mul_of_integrable (ε := ε) (θ' := Real.pi - θ') hε hGint
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    show sKer ε ((Real.pi - θ') - s) * Qcut g s = sKer ε (θ' + s - Real.pi) * Qcut g s
    rw [show (Real.pi - θ') - s = -(θ' + s - Real.pi) by ring, sKer_even]
  -- assemble
  calc thMoll u ε z θ' = ∫ s : ℝ, sKer ε (θ' - s) * Qext u z s := rfl
    _ = ∫ s : ℝ, sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ s : ℝ, sKer ε (θ' - s) * Qcut g s) - (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
          - (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s)) := by
        have h1 : (∫ s : ℝ, sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)))
            = ∫ s : ℝ, (sKer ε (θ' - s) * Qcut g s - sKer ε (θ' - s) * Qcut g (-s)
                - sKer ε (θ' - s) * Qcut g (Real.pi - s)) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          ring
        rw [h1]
        rw [MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s - sKer ε (θ' - s) * Qcut g (-s))
          (g := fun s : ℝ => sKer ε (θ' - s) * Qcut g (Real.pi - s)) (hI1.sub hI2) hI3]
        rw [MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' - s) * Qcut g (-s)) hI1 hI2]
    _ = (∫ s : ℝ, sKer ε (θ' - s) * Qcut g s) - (∫ s : ℝ, sKer ε (θ' + s) * Qcut g s)
          - (∫ s : ℝ, sKer ε (θ' + s - Real.pi) * Qcut g s) := by rw [hsub2, hsub3]
    _ = ∫ s : ℝ, Kern (sKer ε) θ' s * Qcut g s := by
        rw [← MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' + s) * Qcut g s) hI1 hJ2]
        rw [← MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s - sKer ε (θ' + s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' + s - Real.pi) * Qcut g s) (hI1.sub hJ2) hJ3]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        show sKer ε (θ' - s) * Qcut g s - sKer ε (θ' + s) * Qcut g s
              - sKer ε (θ' + s - Real.pi) * Qcut g s
            = (sKer ε (θ' - s) - sKer ε (θ' + s) - sKer ε (θ' + s - Real.pi)) * Qcut g s
        ring
    _ = ∫ s in Iθ, Kern (sKer ε) θ' s * u z s := by
        show (∫ s : ℝ, Kern (sKer ε) θ' s * Qcut g s)
          = ∫ s in Iθ, Kern (sKer ε) θ' s * g s
        exact integral_mul_Qcut (fun s : ℝ => Kern (sKer ε) θ' s) g

theorem thMollTransfer2 : ∀ (u : ℝ → ℝ → ℝ) {ε z : ℝ}, 0 < ε → ε ≤ 1 / 2 → 0 < z → u z 0 = 0 → u z (Real.pi / 2) = 0 → ContinuousOn (fun θ : ℝ => u z θ) Work.Spaces.Iθ → ContinuousOn (fun θ : ℝ => Work.Spaces.pth u z θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt (fun θ' : ℝ => u z θ') (Work.Spaces.pth u z θ) θ) → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt (fun θ' : ℝ => Work.Spaces.pth u z θ') (Work.Spaces.pth (Work.Spaces.pth u) z θ) θ) → (∀ θ ∈ Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * u z s) ∧ (∀ θ ∈ Work.Spaces.Iθ, deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ') θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth u z s) ∧ (∀ θ ∈ Work.Spaces.Iθ, deriv (deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ')) θ = ∫ s in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s) - Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth (Work.Spaces.pth u) z s) := by
  intro u ε z hε hε1 hz h0 hp hcg hch hint0 hint1 hint2 hder1 hder2
  refine ⟨?_, ?_, ?_⟩
  · -- the value slot
    intro θ hθ
    have h1 : -(1 / 4) < θ := by have := hθ.1; linarith
    have h2 : θ < Real.pi / 2 + 1 / 4 := by have := hθ.2; linarith
    exact thMoll_fold hε hε1 h0 hp hcg h1 h2
  · -- the first derivative slot
    intro θ hθ
    have h1 : -(1 / 4) < θ := by have := hθ.1; linarith
    have h2 : θ < Real.pi / 2 + 1 / 4 := by have := hθ.2; linarith
    have hfold_ev : (fun θ' : ℝ => thMoll u ε z θ') =ᶠ[𝓝 θ]
        (fun θ' : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (sKer ε) θ' s * u z s) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨h1, h2⟩) fun θ' hθ' => ?_
      show thMoll u ε z θ' = ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (sKer ε) θ' s * u z s
      rw [thMoll_fold hε hε1 h0 hp hcg hθ'.1 hθ'.2, setIntegral_Iθ_eq_interval]
    obtain ⟨C, hC⟩ := exists_bound_deriv_sKer hε
    have hA := hasDerivAt_intervalIntegral_Kern (ρ := sKer ε) (ρ' := deriv (sKer ε))
      (g := fun s : ℝ => u z s) (C := C) (a := 0) (b := Real.pi / 2)
      (fun t : ℝ => hasDerivAt_sKer ε t) hC (by
        rw [Set.uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
        exact hcg)
    have hd1 : HasDerivAt (fun θ' : ℝ => thMoll u ε z θ')
        (∫ s in (0 : ℝ)..(Real.pi / 2), Kern (deriv (sKer ε)) θ s * u z s) θ :=
      (hA θ).congr_of_eventuallyEq hfold_ev
    rw [hd1.deriv,
      interval_eq_setIntegral_Iθ (fun s : ℝ => Kern (deriv (sKer ε)) θ s * u z s)]
    exact ibp_kern_first (ρ := sKer ε) (ρ' := deriv (sKer ε))
      (G := fun s : ℝ => u z s) (H := fun s : ℝ => Work.Spaces.pth u z s)
      (fun t : ℝ => hasDerivAt_sKer ε t) (continuous_deriv_sKer ε) hcg hder1 h0 hp hch
  · -- the second derivative slot
    intro θ hθ
    have h1 : -(1 / 4) < θ := by have := hθ.1; linarith
    have h2 : θ < Real.pi / 2 + 1 / 4 := by have := hθ.2; linarith
    have hfold_all : ∀ θ' ∈ Set.Ioo (-(1 / 4)) (Real.pi / 2 + 1 / 4),
        thMoll u ε z θ' = ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (sKer ε) θ' s * u z s := by
      intro θ' hθ'
      rw [thMoll_fold hε hε1 h0 hp hcg hθ'.1 hθ'.2, setIntegral_Iθ_eq_interval]
    obtain ⟨C, hC⟩ := exists_bound_deriv_sKer hε
    obtain ⟨C2, hC2⟩ := exists_bound_deriv2_sKer hε
    have hcontI : ContinuousOn (fun s : ℝ => u z s) (Set.uIcc 0 (Real.pi / 2)) := by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      exact hcg
    have hA1 := hasDerivAt_intervalIntegral_Kern (ρ := sKer ε) (ρ' := deriv (sKer ε))
      (g := fun s : ℝ => u z s) (C := C) (a := 0) (b := Real.pi / 2)
      (fun t : ℝ => hasDerivAt_sKer ε t) hC hcontI
    have hA2 := hasDerivAt_intervalIntegral_Kern (ρ := deriv (sKer ε))
      (ρ' := deriv (deriv (sKer ε))) (g := fun s : ℝ => u z s) (C := C2)
      (a := 0) (b := Real.pi / 2)
      (fun t : ℝ => hasDerivAt_deriv_sKer ε t) hC2 hcontI
    have hderiv_ev : (fun θ' : ℝ => deriv (fun θ'' : ℝ => thMoll u ε z θ'') θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
            ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (sKer ε) θ'' s * u z s) θ') := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨h1, h2⟩) fun θ' hθ' => ?_
      exact Filter.EventuallyEq.deriv_eq
        (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ') hfold_all)
    have hderiv_ev2 : (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
          ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (sKer ε) θ'' s * u z s) θ')
        = fun θ' : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2),
            Kern (deriv (sKer ε)) θ' s * u z s := by
      funext θ'
      exact (hA1 θ').deriv
    have hEv : (fun θ' : ℝ => deriv (fun θ'' : ℝ => thMoll u ε z θ'') θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ =>
            ∫ s in (0 : ℝ)..(Real.pi / 2), Kern (deriv (sKer ε)) θ' s * u z s) :=
      hderiv_ev.trans (Filter.Eventually.of_forall fun θ' => congrFun hderiv_ev2 θ')
    have hmain : deriv (deriv (fun θ' : ℝ => thMoll u ε z θ')) θ
        = ∫ s in (0 : ℝ)..(Real.pi / 2),
            Kern (deriv (deriv (sKer ε))) θ s * u z s := by
      rw [Filter.EventuallyEq.deriv_eq hEv]
      exact (hA2 θ).deriv
    rw [hmain,
      interval_eq_setIntegral_Iθ
        (fun s : ℝ => Kern (deriv (deriv (sKer ε))) θ s * u z s)]
    have hv1 : sKer ε (θ + Real.pi / 2) = 0 := by
      refine sKer_eq_zero_of_le_abs hε ?_
      rw [abs_of_pos (by linarith [hθ.1, Real.pi_pos])]
      linarith [hθ.1, hε1, Real.pi_gt_three]
    have hv2 : sKer ε (θ - Real.pi) = 0 := by
      refine sKer_eq_zero_of_le_abs hε ?_
      rw [abs_of_neg (by linarith [hθ.2, Real.pi_pos])]
      linarith [hθ.2, hε1, Real.pi_gt_three]
    exact ibp_kern_second (ρ := sKer ε) (ρ' := deriv (sKer ε))
      (ρ'' := deriv (deriv (sKer ε))) (G := fun s : ℝ => u z s)
      (H := fun s : ℝ => Work.Spaces.pth u z s)
      (H2 := fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z s)
      (fun t : ℝ => hasDerivAt_sKer ε t) (fun t : ℝ => hasDerivAt_deriv_sKer ε t)
      (continuous_deriv_sKer ε) (continuous_deriv2_sKer ε)
      hcg hder1 h0 hp hch (integrableOn_pth_pth hint2 hder2) hder2 hv1 hv2

end Work.FTS.EllSol.EllPkgAux
