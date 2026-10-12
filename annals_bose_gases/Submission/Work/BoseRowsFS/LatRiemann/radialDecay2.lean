import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.RadialIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.radialDecay2`

The tail integral of the radial weight `((1+‖p‖)²‖p‖²)⁻¹` on `ℝ³`:

    `∫_{‖p‖ ≥ L} ((1+‖p‖)²‖p‖²)⁻¹ dp = 4π/(1+L)`   (`L ≥ 0`),

which in particular gives the integrability of the integrand and the bound
`4 * π / (1 + L)`.

The value is *exact*: the polar-coordinate identity
`Submission.BoseGases.integral_fun_norm_r3` reduces the integral to

    `4π ∫_L^∞ r² * ((1+r)²r²)⁻¹ dr = 4π ∫_L^∞ (1+r)^{-2} dr = 4π/(1+L)`,

the last integral being computed from the antiderivative `r ↦ -(1+r)^{-1}`
by the fundamental theorem of calculus on `(L, ∞)`
(`integral_Ioi_of_hasDerivAt_of_tendsto'`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseRowsFS.LatRiemann

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `r ↦ (1 + r)^{-2}` is integrable on `(0, ∞)`. -/
lemma integrableOn_one_add_sq_inv :
    IntegrableOn (fun r : ℝ => ((1 + r) ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
    (by norm_num) (by norm_num)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change (x + 1) ^ (-2 : ℝ) = ((1 + x) ^ 2)⁻¹
  have hx1 : (0 : ℝ) < x + 1 := by have : (0 : ℝ) < x := hx; linarith
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx1),
    Real.rpow_natCast]
  rw [show x + 1 = 1 + x from add_comm x 1]

/-- `∫_{(L, ∞)} (1 + r)^{-2} dr = 1/(1 + L)` for `L ≥ 0`. -/
lemma integral_Ioi_one_add_sq_inv (L : ℝ) (hL : 0 ≤ L) :
    (∫ r in Set.Ioi L, ((1 + r) ^ 2)⁻¹) = 1 / (1 + L) := by
  have hint : IntegrableOn (fun r : ℝ => ((1 + r) ^ 2)⁻¹) (Set.Ioi L) :=
    integrableOn_one_add_sq_inv.mono_set (Set.Ioi_subset_Ioi hL)
  have hderiv : ∀ x ∈ Set.Ici L,
      HasDerivAt (fun r : ℝ => -((1 + r)⁻¹)) (((1 + x) ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : 1 + x ≠ 0 := by have : L ≤ x := hx; linarith
    have hbase : HasDerivAt (fun r : ℝ => 1 + r) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h := (hbase.inv hx0).neg
    have hfun : (-(fun r : ℝ => 1 + r)⁻¹ : ℝ → ℝ) = fun r => -((1 + r)⁻¹) := by
      funext r; simp
    rw [hfun] at h
    have hder : -((-1) / (1 + x) ^ 2) = (((1 + x) ^ 2)⁻¹) := by
      rw [neg_div, neg_neg, one_div]
    rwa [hder] at h
  have htend : Tendsto (fun r : ℝ => -((1 + r)⁻¹)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => (1 + r)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h1.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  rw [zero_sub, neg_neg, one_div]

theorem radialDecay2 (L : ℝ) (hL : 0 ≤ L) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) else 0)
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3),
          (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) else 0))
          ≤ 4 * Real.pi / (1 + L) := by
  let g : ℝ → ℝ := fun r => if L ≤ r then 1 / ((1 + r) ^ 2 * r ^ 2) else 0
  -- the pointwise reduction of the radial weight, away from the single point `r = L`
  have hpt : ∀ r : ℝ, r ≠ L →
      r ^ 2 * g r = (Set.Ioi L).indicator (fun r : ℝ => ((1 + r) ^ 2)⁻¹) r := by
    intro r hrL
    dsimp only [g]
    rcases lt_or_gt_of_ne hrL with hlt | hgt
    · have hnot : ¬ (L ≤ r) := not_le.mpr hlt
      rw [if_neg hnot]
      have hR : (Set.Ioi L).indicator (fun y : ℝ => ((1 + y) ^ 2)⁻¹) r = 0 := by
        simp [Set.notMem_Ioi.mpr (le_of_lt hlt)]
      rw [hR, mul_zero]
    · have hr0 : r ≠ 0 := by
        have : (0 : ℝ) < r := lt_of_le_of_lt hL hgt
        positivity
      rw [if_pos (le_of_lt hgt)]
      have hR : (Set.Ioi L).indicator (fun y : ℝ => ((1 + y) ^ 2)⁻¹) r = ((1 + r) ^ 2)⁻¹ := by
        simp [hgt]
      rw [hR, one_div, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr0), one_mul]
  -- the radial weight agrees with the indicator function almost everywhere
  have hae : (fun r : ℝ => r ^ 2 * g r) =ᵐ[volume]
      (fun r : ℝ => (Set.Ioi L).indicator (fun y : ℝ => ((1 + y) ^ 2)⁻¹) r) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (by simp : (volume : Measure ℝ) {L} = 0)
    intro r hr
    by_contra hne
    exact hr (hpt r hne)
  have haeB : (fun r : ℝ => (Set.Ioi L).indicator (fun y : ℝ => ((1 + y) ^ 2)⁻¹) r)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun r : ℝ => r ^ 2 * g r) := by
    filter_upwards [ae_restrict_of_ae hae] with r hr
    exact hr.symm
  have hInt : Integrable (fun p : ℝ³ => g ‖p‖) := by
    rw [Submission.BoseGases.integrable_radial_r3]
    exact (integrableOn_one_add_sq_inv.indicator measurableSet_Ioi).congr_fun_ae haeB
  have hstep : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = (∫ r in Set.Ioi L, ((1 + r) ^ 2)⁻¹) := by
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioi L = Set.Ioi L := by
      ext r
      constructor
      · rintro ⟨h1, h2⟩
        exact h2
      · intro hx
        exact ⟨lt_of_le_of_lt hL hx, hx⟩
    calc (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
        = ∫ r in Set.Ioi (0 : ℝ),
            (Set.Ioi L).indicator (fun r : ℝ => ((1 + r) ^ 2)⁻¹) r :=
          integral_congr_ae (ae_restrict_of_ae hae)
      _ = ∫ r in Set.Ioi (0 : ℝ) ∩ Set.Ioi L, ((1 + r) ^ 2)⁻¹ :=
          setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Ioi L)
            (f := fun r : ℝ => ((1 + r) ^ 2)⁻¹) measurableSet_Ioi
      _ = ∫ r in Set.Ioi L, ((1 + r) ^ 2)⁻¹ := by rw [hset]
  have hval : (∫ p : ℝ³, g ‖p‖) = 4 * Real.pi / (1 + L) := by
    rw [Submission.BoseGases.integral_fun_norm_r3 (g := g), hstep,
      integral_Ioi_one_add_sq_inv L hL]
    ring
  constructor
  · exact hInt
  · have hfun : (∫ p : ℝ³,
        (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) else 0)) = ∫ p : ℝ³, g ‖p‖ := rfl
    rw [hfun, hval]

end Work.BoseRowsFS.LatRiemann
