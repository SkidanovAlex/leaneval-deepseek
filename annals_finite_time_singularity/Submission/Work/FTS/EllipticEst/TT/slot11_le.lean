import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.slice_step4
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.TT.Slot11.sliceStep4Shift
import Submission.Work.FTS.EllipticEst.TT.Slot11.srcBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The `(1,1)`-slot of `∂_θθΨ` as the shifted Step-4 quantity

The target `slot11_le` bounds the `(1,1)`-mixed slot of `B := ∂_θ²Ψ`,
`L2Sq (D_zD_θB · Wt)`, by the pure (`D_z`-only) slots of `B`, by `HkSq α 2 F` and by the
`α⁴`-multiple of the `(1,1)`-slot of `A := z²∂_z²Ψ`.

On the open quadrant `D_zD_θB = sin(2θ)·∂_θ³(D_zΨ)`, so the slot integrand becomes
`w²·(∂_θ³(D_zΨ))²·sin(2θ)^{2-γ}` — exactly the shifted Step-4 quantity of the slice
`u = θ ↦ D_zΨ(z,θ)`.  This file contains that rewriting and the final assembly; the two
analytic ingredients are proved in the sibling files
`FTS/EllipticEst/TT/Slot11/sliceStep4Shift` and `FTS/EllipticEst/TT/Slot11/srcBound`. -/

/-- On the open quadrant, `mixed 1 1 (∂_θ²f) = sin(2θ)·∂_θ³(D_zf)`.

(`D_z` and `D_θ` commute, and `∂_θ²` commutes with `D_z`.) -/
theorem mixed11_pth2_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ
        = Real.sin (2 * θ) * Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ := by
  intro z θ hz hθ hθ'
  have hpt : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  -- `D_z` and `D_θ` commute at `(z,θ)`
  have hc1 : Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.DthIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 f)) z θ :=
    (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      (fun n => (Work.FTS.EllipticEst.remov.SmoothOpen_pthIter_local hf 2).forall n)
      1 1 hpt).symm
  calc Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.DthIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 f)) z θ := hc1
    _ = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 f))
          z θ := rfl
    _ = Real.sin (2 * θ) * Work.Spaces.pth
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 f)) z θ := by
        rw [Work.Spaces.pth_congr_of_isOpen (f := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 f))
          (f' := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 f))
          Work.FTS.EllipticEst.isOpen_Q0
          (fun p hp => (Work.EllipticEst.H2W.pthIter2_DzIter_comm hf 1 hp).symm) hpt]
    _ = Real.sin (2 * θ) * Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ := rfl

/-- The squared slot identity:
`(mixed 1 1 (∂_θ²f) · Wt α)² = w(z)²·(∂_θ³(D_zf))²·sin(2θ)^{2-γ}` on the open quadrant. -/
theorem mixed11_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  intro z θ hz hθ hθ'
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ', Real.pi_pos])
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hA : s * s ^ (-(Work.Spaces.gam α / 2)) = s ^ (1 - Work.Spaces.gam α / 2) := by
    have h := Real.rpow_add hs (1 : ℝ) (-(Work.Spaces.gam α / 2))
    rw [show (1 : ℝ) + (-(Work.Spaces.gam α / 2)) = 1 - Work.Spaces.gam α / 2 by ring] at h
    rw [h, Real.rpow_one]
  have hB : (s ^ (1 - Work.Spaces.gam α / 2)) ^ 2 = s ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_natCast (s ^ (1 - Work.Spaces.gam α / 2)) 2, ← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [mixed11_pth2_eq hf z θ hz hθ hθ']
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, hsdef.symm]
  rw [show (s * Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ
        * (Work.Spaces.w z * s ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * (s * s ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring]
  rw [show (s * s ^ (-(Work.Spaces.gam α / 2))) ^ 2 = s ^ (2 - Work.Spaces.gam α) by
    rw [hA, hB]]
  ring

/-- The left-hand side of `slot11_le`, rewritten as the `z`-integral of the shifted Step-4
quantity of the slice `u = θ ↦ D_zΨ(z,θ)`. -/
theorem LHS_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ =>
        (Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) 0 θ * Work.Spaces.Wt α 0 θ) ^ 2)
        = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Work.Spaces.Dz]
      ring
    rw [hzero, MeasureTheory.integral_zero]
    simp [Work.Spaces.w]
  · have hae : ∀ᵐ θ ∂(volume : Measure ℝ),
        θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp
        Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo
    rw [show (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) from
      MeasureTheory.setIntegral_congr_ae measurableSet_Icc
        (hae.mono fun θ hp hIθ =>
          mixed11_sq_eq hΨ z θ hzpos (hp hIθ).1 (hp hIθ).2)]
    rw [MeasureTheory.integral_const_mul]

/-- The weight algebra of the `D_z`-slots: `(A·(w/s^{η/2}))² = A²·w²·s^{-η}`. -/
theorem slot_sq_eq {η A wv s : ℝ} (hs : 0 ≤ s) :
    (A * (wv / s ^ (η / 2))) ^ 2 = A ^ 2 * wv ^ 2 * s ^ (-η) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg hs (η / 2)]
  rw [show (A * (wv * s ^ (-(η / 2)))) ^ 2 = A ^ 2 * wv ^ 2 * (s ^ (-(η / 2))) ^ 2 from by ring]
  rw [show (s ^ (-(η / 2))) ^ 2 = s ^ (-η) from by
    rw [← Real.rpow_natCast (s ^ (-(η / 2))) 2, ← Real.rpow_mul hs]
    congr 1
    ring]

/-- The two slot functions `∫_θ (∂_θ²(D_zΨ))²·sEta` and `∫_θ (D_z(∂_θ²Ψ)·(w/s^{η/2}))²`
agree after multiplication by `w²` (Clairaut + the weight algebra). -/
theorem p1_eq_S {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : 0 < z) :
    (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [← MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
    (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ)]
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp
      Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
    (hae.mono fun θ hp hIθ => ?_)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hp hIθ
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le
  have hpt : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEq : Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ :=
    (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1 hpt).symm
  rw [hEq]
  simp only [Work.FTS.EllipticEst.sEta]
  rw [slot_sq_eq (η := Work.Spaces.eta) (A := Work.Spaces.pthIter 2
        (Work.Spaces.DzIter 1 Ψ) z θ) (wv := Work.Spaces.w z) (s := Real.sin (2 * θ)) hsin]
  ring

/-- The two `L²`-squares of the `j = 1` pure slot of `∂_θ²Ψ` agree (Clairaut on the open
quadrant). -/
theorem L2Sq_Dz_pth_congr {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.integral_congr_ae ?_
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
      (MeasureTheory.measure_singleton 0)
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_Ici] at hx
    push_neg at hx
    exact le_antisymm hx.2 hx.1
  filter_upwards [hae] with z hz
  have hae2 : ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Work.Spaces.Iθ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp
      Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc
    (hae2.mono fun θ hp hIθ => ?_)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hp hIθ
  have hpt : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEq : Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ :=
    (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1 hpt).symm
  rw [hEq]

end Work.FTS.EllipticEst.TT

namespace Work.FTS.EllipticEst.TT

/-- **The assembly**: the two analytic pieces (the a.e.-in-`z` Step-4 estimate for the shifted
slice, and the bound of the `z`-integral of the source) give the target. -/
theorem slot11_core
    (hSlice : ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          ≤ K * ((∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α (Work.Spaces.DzIter 1 F)
                  (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)))
    (hSrc : ∃ K : ℝ, 0 < K ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
                (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Work.Spaces.Iz
        ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α
                (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z t) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
          ≤ K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
                  Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
              + Work.Spaces.HkSq α 2 F
              + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
                  Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                    * Work.Spaces.Wt α z θ))) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F
            + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                  * Work.Spaces.Wt α z θ)) := by
  obtain ⟨K, hKpos, hK⟩ := hSlice
  obtain ⟨K2, hK2pos, hK2⟩ := hSrc
  have hKnn : 0 ≤ K := hKpos.le
  have hK2nn : 0 ≤ K2 := hK2pos.le
  refine ⟨K * (K2 + 1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨ 2
  -- the pieces, as functions of `z`
  set G : ℝ → ℝ → ℝ := fun z θ => Work.FTS.EllipticEst.Mine.Gsrc α
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) z θ with hG
  set sig : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hsig
  set ℓ : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sig θ with hℓ
  set src : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (deriv (fun t => G z t) θ) ^ 2 * sig θ with hsrc
  set p1 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ with hp1
  set Sf : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 with hSf
  set M : ℝ → ℝ := fun z => K * ((Work.Spaces.w z) ^ 2 * src z + Sf z) with hM
  set RHS : ℝ := (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      + Work.Spaces.HkSq α 2 F
      + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ) with hRHS
  -- `L²`-squares are nonnegative
  have hL2nn : ∀ (g : ℝ → ℝ → ℝ), 0 ≤ Work.Spaces.L2Sq g := fun g => by
    rw [Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- the a.e. positivity of `z`
  have hae_pos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
      (MeasureTheory.measure_singleton 0)
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_Ici] at hx
    push_neg at hx
    exact le_antisymm hx.2 hx.1
  -- ## the a.e. pointwise domination
  have hMono : (fun z => (Work.Spaces.w z) ^ 2 * ℓ z)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] M := by
    filter_upwards [hK α F Ψ hα hα4 h, hae_pos] with z hz1 hz2
    have h1 : ℓ z ≤ K * (src z + p1 z) := by
      simp only [hℓ, hsrc, hp1, hsig, hG]
      exact hz1 hz2
    have h2 : (Work.Spaces.w z) ^ 2 * p1 z = Sf z := by
      simp only [hp1, hSf]
      exact p1_eq_S hΨ hz2
    have hw : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc (Work.Spaces.w z) ^ 2 * ℓ z
        ≤ (Work.Spaces.w z) ^ 2 * (K * (src z + p1 z)) := mul_le_mul_of_nonneg_left h1 hw
      _ = K * ((Work.Spaces.w z) ^ 2 * src z + (Work.Spaces.w z) ^ 2 * p1 z) := by ring
      _ = M z := by rw [hM, h2]
  -- ## integrability
  have hIntSrc : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * src z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hK2 α F Ψ hα hα4 h).1
  have hIntS : MeasureTheory.Integrable Sf
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.integrableOn_slice_Iz α 2 hB h.memB 1 (by norm_num)
  have hIntM : MeasureTheory.Integrable M
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hIntSrc.add hIntS).const_mul K
  -- ## the integrated comparison
  have hMain : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ℓ z)
      ≤ ∫ z in Work.Spaces.Iz, M z :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (by
        simp only [hℓ]
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
          mul_nonneg (sq_nonneg _) (by
            simp only [hsig]
            exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)))
      hIntM hMono
  -- ## the value of `∫ M`
  have hMint : (∫ z in Work.Spaces.Iz, M z)
      = K * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * src z)
          + ∫ z in Work.Spaces.Iz, Sf z) := by
    show (∫ z in Work.Spaces.Iz, K * ((Work.Spaces.w z) ^ 2 * src z + Sf z)) = _
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hIntSrc hIntS]
  -- ## the two bounds
  have hSrcBd : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * src z) ≤ K2 * RHS :=
    (hK2 α F Ψ hα hα4 h).2
  have hSfBd : (∫ z in Work.Spaces.Iz, Sf z) ≤ RHS := by
    have hL1 : (∫ z in Work.Spaces.Iz, Sf z)
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
      show Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) = _
      exact L2Sq_Dz_pth_congr hΨ
    rw [hL1, hRHS]
    have hsingle : Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :=
      Finset.single_le_sum
        (f := fun j => Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        (fun j _ => hL2nn _) (by norm_num : (1 : ℕ) ∈ Finset.range 3)
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :=
      Finset.sum_nonneg fun j _ => hL2nn _
    have hQ_nn : 0 ≤ Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ) := hL2nn _
    have hH_nn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
    have ha4 : 0 ≤ α ^ 4 := by positivity
    linarith [hsingle, hsum_nn, hH_nn, mul_nonneg ha4 hQ_nn]
  have hRHSnn : 0 ≤ RHS := by
    rw [hRHS]
    refine add_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => hL2nn _)
      (Work.Spaces.HkSq_nonneg α 2 F)) (mul_nonneg (by positivity) (hL2nn (fun z θ =>
        Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * Work.Spaces.Wt α z θ)))
  -- ## assembly
  have hLHS : Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ) = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ℓ z := by
    show _ = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
    exact LHS_eq hΨ
  calc Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
        * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ℓ z := hLHS
    _ ≤ ∫ z in Work.Spaces.Iz, M z := hMain
    _ = K * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * src z)
          + ∫ z in Work.Spaces.Iz, Sf z) := hMint
    _ ≤ K * (K2 * RHS + RHS) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        linarith [hSrcBd, hSfBd]
    _ ≤ (K * (K2 + 1) + 1) * RHS := by
        have h1 : K * (K2 * RHS + RHS) = K * (K2 + 1) * RHS := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (by linarith) hRHSnn

end Work.FTS.EllipticEst.TT

namespace Work.FTS.EllipticEst.TT

theorem slot11_le : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Work.Spaces.pthIter 2 Ψ) z θ
          * Work.Spaces.Wt α z θ)
        ≤ C * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F
            + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                  * Work.Spaces.Wt α z θ)) :=
  slot11_core Work.FTS.EllipticEst.TT.Slot11.sliceStep4Shift
    Work.FTS.EllipticEst.TT.Slot11.srcBound

end Work.FTS.EllipticEst.TT
