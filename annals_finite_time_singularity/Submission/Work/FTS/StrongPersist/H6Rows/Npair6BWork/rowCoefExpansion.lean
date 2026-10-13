import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The Fubini bridge for `slotPairing`

`slotPairing ρ a b u v` is defined as the iterated set integral
`∫ z in Iz, ∫ θ in Iθ, ρ z θ * D_z^bD_θ^a u z θ * D_z^bD_θ^a v z θ`.  The right-hand side
of the row expansion uses the integral against the *product* of the two restricted measures
`(volume.restrict Iz).prod (volume.restrict Iθ)`, so the two descriptions must be identified.
This is `MeasureTheory.integral_prod`. -/

/-- `slotPairing` is also the integral against the product measure, for an integrable
integrand. -/
private theorem slotPairing_eq_prod (ρ u v : ℝ → ℝ → ℝ) (a b : ℕ)
    (h : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a u p.1 p.2
        * Work.Spaces.mixed b a v p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b u v
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
          * Work.Spaces.mixed b a v p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.TransportS.slotPairing]
  exact (MeasureTheory.integral_prod
    (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
      * Work.Spaces.mixed b a v p.1 p.2) h).symm

/-! ## Almost everywhere statements on the closed quadrant -/

/-- Almost every `z` of the closed half line `Iz = [0,∞)` is positive (`0` is null). -/
private lemma ae_mem_Iz_pos :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  have h : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))))
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-- Almost every `θ` of the closed interval `Iθ = [0,π/2]` is interior. -/
private lemma ae_mem_Iθ_interior :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2)))
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost every point of the product of the two closed intervals is in the *open* quadrant
`(0,∞) × (0,π/2)`, the domain on which the Leibniz rule `leibniz_open_mixed` holds. -/
private lemma ae_prod_mem_openQuadrant :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} := by
    have hset : ({p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2} : Set (ℝ × ℝ))
        = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := rfl
    rw [hset]
    exact (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  refine (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).mpr ?_
  filter_upwards [ae_mem_Iz_pos] with z hz
  filter_upwards [ae_mem_Iθ_interior] with θ hθ
  exact ⟨hz, hθ.1, hθ.2⟩

/-! ## The pointwise Leibniz expansion of the slot -/

/-- On the open quadrant, `D_z^bD_θ^a (A·Q)` expands binomially.  This is the pointwise
identity behind the row expansion, in the exact shape of the right-hand side of
`rowCoefExpansion`. -/
private theorem mixed_mul_leibniz_pointwise {A Q : ℝ → ℝ → ℝ} {a b : ℕ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    {ρ f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ
        * Work.Spaces.mixed b a f z θ
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * Work.Spaces.mixed b₁ a₁ A z θ
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q z θ
                * Work.Spaces.mixed b a f z θ) := by
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a A Q hA hQ z θ hz hθ0 hθ1]
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a₁ _ => ?_)
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b₁ _ => ?_)
  ring

/-! ## The row expansion -/

theorem rowCoefExpansion {A Q f ρ : ℝ → ℝ → ℝ} {a b : ℕ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hQ : Work.FTS.EllipticEst.SmoothOpen Q)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ)
    (hterm : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Q z θ) f
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- the a.e. Leibniz identity, transported from the open quadrant
  have hae : (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2)) := by
    filter_upwards [ae_prod_mem_openQuadrant] with p hp
    exact mixed_mul_leibniz_pointwise hA hQ hp.1 hp.2.1 hp.2.2
  -- integrability of each summand, from `hterm`
  have hsummand : ∀ a₁ ∈ Finset.range (a + 1), ∀ b₁ ∈ Finset.range (b + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro a₁ ha₁ b₁ hb₁
    have ha' : a₁ ≤ a := by
      have h := Finset.mem_range.mp ha₁; omega
    have hb' : b₁ ≤ b := by
      have h := Finset.mem_range.mp hb₁; omega
    exact (hterm a₁ ha' b₁ hb').const_mul _
  -- integrability of the summed integrand
  have hint_sum : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integrable_finsetSum (Finset.range (a + 1)) (fun a₁ ha₁ => ?_)
    exact MeasureTheory.integrable_finsetSum (Finset.range (b + 1)) (fun b₁ hb₁ => hsummand a₁ ha₁ b₁ hb₁)
  -- integrability of the left-hand integrand
  have hint_lhs : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint_sum.congr hae.symm
  -- Fubini: the slot pairing is the product-measure integral
  rw [slotPairing_eq_prod ρ (fun z θ => A z θ * Q z θ) f a b hint_lhs]
  -- replace the integrand by the Leibniz sum
  rw [MeasureTheory.integral_congr_ae hae]
  -- pull the two finite sums out of the integral
  trans ∑ a₁ ∈ Finset.range (a + 1),
      ∫ p, ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
  · exact MeasureTheory.integral_finsetSum (Finset.range (a + 1))
      (fun a₁ ha₁ => MeasureTheory.integrable_finsetSum (Finset.range (b + 1))
        (fun b₁ hb₁ => hsummand a₁ ha₁ b₁ hb₁))
  · refine Finset.sum_congr rfl (fun a₁ ha₁ => ?_)
    trans ∑ b₁ ∈ Finset.range (b + 1),
        ∫ p, ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) Q p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    · exact MeasureTheory.integral_finsetSum (Finset.range (b + 1))
        (fun b₁ hb₁ => hsummand a₁ ha₁ b₁ hb₁)
    · refine Finset.sum_congr rfl (fun b₁ hb₁ => ?_)
      rw [MeasureTheory.integral_const_mul]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
