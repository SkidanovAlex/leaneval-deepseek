/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Prop.levelTopSlotsTwoAux`: verified pieces of `Prop.levelTopSlotsTwo`

See `Submission/Work/FTS/EllipticEst/Prop/NOTES_levelTopSlotsTwo.md` for the route and the
remaining gaps.  This file contains, `sorry`-free:

* the weight algebra `(D_θ f · Wt α)² ≤ (∂_θ f)² w² sin(2θ)^{-η}` on `Iθ` and the resulting
  reduction `Tk α 1 f ≤ ∫_z w² ∫_θ (∂_θf)² sin(2θ)^{-η}` of the top angular slot;
* `HkSq α 0 g` in the two explicit forms used by the estimates;
* **`bSlotTop_clean`**: the `B`-slot `√(Tk α 1 (∂_θ²Ψ)) ≤ C |F|_{ℋ²}` for a datum of the weak
  class `TT.EllWeakPos α 2 F Ψ`, proved unconditionally from the proved `slot01Bound`
  (`H2W.AngBW`) and the proved clean radial-shift level-`0` slots `ShiftZeroSlots2`.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.EllipticEst.H2W.AngBW.slot01Bound
import Submission.Work.FTS.EllipticEst.TT.slot11_le
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

abbrev Ab (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
abbrev Bb (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(w / s^{η/2})² = w² · s^{-η}` (`η = Work.Spaces.eta`), for `s > 0`. -/
theorem div_rpow_half_sq {wv s : ℝ} (hs : 0 < s) :
    (wv / s ^ (Work.Spaces.eta / 2)) ^ 2 = wv ^ 2 * s ^ (-Work.Spaces.eta) := by
  have h1 : (s ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ) = s ^ Work.Spaces.eta := by
    rw [pow_two, ← Real.rpow_add hs,
      show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta from by ring]
  rw [div_eq_mul_inv, mul_pow, inv_pow, h1, ← Real.rpow_neg hs.le Work.Spaces.eta]

/-- `(w / σ^{η/2})² = w² · σ^{-η}` on `Iθ` (including the endpoints, where both sides vanish). -/
theorem div_rpow_half_sq_Iθ {wv θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (wv / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = wv ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
  rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with h | h
  · rw [h.symm, Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      div_zero, Real.zero_rpow (by norm_num [Work.Spaces.eta] : -Work.Spaces.eta ≠ 0)]
    ring
  · exact div_rpow_half_sq h

/-- `(σ · σ^{-γ/2})² = σ^{2-γ}` on the open interval. -/
theorem sq_sin_mul_rpow {γ θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(γ / 2))) ^ 2
      = Real.sin (2 * θ) ^ (2 - γ) := by
  have hs := sin_two_pos_Ioo hθ
  have h1 : (Real.sin (2 * θ) ^ (-(γ / 2))) ^ (2 : ℕ) = Real.sin (2 * θ) ^ (-γ) := by
    rw [pow_two, ← Real.rpow_add hs,
      show -(γ / 2) + -(γ / 2) = -γ from by ring]
  rw [mul_pow, h1, ← Real.rpow_natCast (Real.sin (2 * θ)) 2, ← Real.rpow_add hs,
    show ((2 : ℕ) : ℝ) + (-γ) = 2 - γ from by push_cast; ring]

/-- `HkSq α 0 g` is the `L²`-square of `g` against `Zu = w/σ^{η/2}`. -/
theorem HkSq_zero_eq_L2Sq_zu (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = Work.Spaces.L2Sq (fun z θ =>
          g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp [Work.Spaces.HkIntegrand]

/-- `HkSq α 0 g` as an explicit integral against `sEta = sin(2θ)^{-η}`. -/
theorem HkSq_zero_eq_int (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
  rw [HkSq_zero_eq_L2Sq_zu α g, Work.Spaces.L2Sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
    measurableSet_Icc)] with θ hθ
  rw [mul_pow, div_rpow_half_sq_Iθ hθ]
  ring

/-- The pointwise bound behind the reduction of the `A`-slot: on the open interval,
`(D_θ f · Wt α)² ≤ (∂_θ f)² · w² · sEta`. -/
theorem Dth_mul_Wt_sq_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hs := sin_two_pos_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam1 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hkey : (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [Work.Spaces.Dth, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [show (Real.sin (2*θ) * Work.Spaces.pth f z θ
        * (Work.Spaces.w z * Real.sin (2*θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2*θ) * Real.sin (2*θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring]
    rw [sq_sin_mul_rpow hθ]
  rw [hkey]
  have hexp : -Work.Spaces.eta ≤ 2 - Work.Spaces.gam α := by
    have h1 := Work.Spaces.eta_pos
    rw [Work.Spaces.gam] at hgam1 ⊢
    linarith
  have hmono : Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
  exact mul_le_mul_of_nonneg_left hmono (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The pointwise bound on all of `Iθ`. -/
theorem Dth_mul_Wt_sq_le_Iθ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have hnneg : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
    Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
  have hRHS : 0 ≤ (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hnneg
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hLHS : (Work.Spaces.Dth f z 0 * Work.Spaces.Wt α z 0) ^ 2 = 0 := by
      rw [Work.Spaces.Dth, show Real.sin (2 * (0 : ℝ)) = 0 by norm_num [Real.sin_zero]]
      ring
    rw [hLHS]
    exact hRHS
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hLHS : (Work.Spaces.Dth f z (Real.pi / 2) * Work.Spaces.Wt α z (Real.pi / 2)) ^ 2 = 0 := by
        rw [Work.Spaces.Dth, show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]]
        ring
      rw [hLHS]
      exact hRHS
    · exact Dth_mul_Wt_sq_le hα hα4 f ⟨h0, h1⟩

/-- **Reduction of the `A`-top-slot to the `sEta`-slots of the slice.** -/
theorem Tk_le_int {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (f : ℝ → ℝ → ℝ)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 f
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)
        ((hsl z hz).const_mul ((Work.Spaces.w z) ^ 2)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      have h := Dth_mul_Wt_sq_le_Iθ (z := z) hα hα4 f hθ
      rw [show (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring] at h
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero] using h
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1
  rw [Work.FTS.EllipticEst.remov.Step.Tk]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hint ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner


/-- **The `B`-slot `√(Tk α 1 (∂_θ²Ψ)) ≤ C |F|_{ℋ²}`**, unconditionally (from the proved
`slot01Bound` and the proved clean radial-shift level-`0` slots `ShiftZeroSlots2`). -/
theorem bSlotTop_clean :
    (∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) →
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ))
        ≤ C * Work.Spaces.HkNorm α 2 F := by
  intro h0
  obtain ⟨CZ, hCZpos, hZ⟩ := Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2 h0
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.H2W.AngBW.slot01Bound
  refine ⟨Real.sqrt K * Real.sqrt (3 * CZ + 1) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hN : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hmain := hK α F Ψ hα hα4 h
  -- identify the sum of `L2Sq ... Zu` terms with the corresponding `HkSq α 0` terms
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ *
          (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))
      ≤ 3 * (CZ * Work.Spaces.HkSq α 2 F) := by
    have h1 : ∀ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ *
            (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
        ≤ CZ * Work.Spaces.HkSq α 2 F := by
      intro j hj
      have hj2 : j ≤ 2 := by
        have := Finset.mem_range.mp hj; omega
      have hb := hZ α F Ψ hα hα4 h j hj2
      have hnn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ) :=
        mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
      have h2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))
          ≤ CZ * Work.Spaces.HkSq α 2 F := by linarith [hb, hnn]
      rw [HkSq_zero_eq_L2Sq_zu α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))] at h2
      exact h2
    calc (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ *
              (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))
        ≤ ∑ j ∈ Finset.range 3, (CZ * Work.Spaces.HkSq α 2 F) := Finset.sum_le_sum h1
      _ = 3 * (CZ * Work.Spaces.HkSq α 2 F) := by
          rw [Finset.sum_const, Finset.card_range]; norm_num
  -- rewrite the LHS of `slot01Bound` as the `Tk`-slot
  have hTK : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ)
      = Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) := rfl
  rw [hTK]
  -- square roots
  have hstep : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ K * (3 * (CZ * Work.Spaces.HkSq α 2 F) + Work.Spaces.HkSq α 2 F) := by
    calc _ ≤ K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ *
                (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F) := hmain
      _ ≤ K * (3 * (CZ * Work.Spaces.HkSq α 2 F) + Work.Spaces.HkSq α 2 F) := by
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          linarith [hsum]
  have hKnn : (0 : ℝ) ≤ K := hKpos.le
  have hfin : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ K * (3 * CZ + 1) * Work.Spaces.HkSq α 2 F := by
    refine le_trans hstep ?_
    rw [show K * (3 * (CZ * Work.Spaces.HkSq α 2 F) + Work.Spaces.HkSq α 2 F)
        = K * (3 * CZ + 1) * Work.Spaces.HkSq α 2 F from by ring]
  have hnn : (0 : ℝ) ≤ Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  calc Real.sqrt (Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ))
      ≤ Real.sqrt (K * (3 * CZ + 1) * Work.Spaces.HkSq α 2 F) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt K * Real.sqrt (3 * CZ + 1) * Work.Spaces.HkNorm α 2 F := by
        rw [Work.Spaces.HkNorm, Real.sqrt_mul (by positivity), Real.sqrt_mul hKnn]
    _ ≤ (Real.sqrt K * Real.sqrt (3 * CZ + 1) + 1) * Work.Spaces.HkNorm α 2 F := by
        have h1 : (0 : ℝ) ≤ Real.sqrt K * Real.sqrt (3 * CZ + 1) := by positivity
        have h2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 2 F := Work.Spaces.HkNorm_nonneg α 2 F
        linarith [mul_nonneg h1 h2, h2]

end Work.FTS.EllipticEst.Prop
