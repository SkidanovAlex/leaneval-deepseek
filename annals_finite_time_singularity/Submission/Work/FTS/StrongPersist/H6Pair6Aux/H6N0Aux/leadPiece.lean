import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_aux
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

-- `open scoped Real` is needed for the notation `π` in the statement below to mean
-- `Real.pi` (the workspace sets `autoImplicit = false`, so a bare `π` would otherwise be
-- an unknown identifier and the statement would not even elaborate).
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two general auxiliary facts

The whole lemma rests on two elementary facts about the product measure
`μ = (volume|Iz).prod (volume|Iθ)` of the self-similar domain:

* `hkInt_prodIntegrable`: the `ℋ^k`-integrand of a member of `ℋ^k` is product integrable
  (Fubini's criterion `integrable_prod_iff`, using the open-quadrant continuity supplied by
  `SmoothOpen` for the a.e. strong measurability);
* `slot_le_HkIntegrand`: every leaf-weight slot `ρ · (D_z^bD_θ^a f)²` with `a + b ≤ k` is
  pointwise dominated, on the open quadrant, by the `ℋ^k`-integrand of `f`. -/

/-- **The `ℋ^k`-integrand of a member of `ℋ^k` is integrable for the product measure**, as
soon as the datum is `C^∞` on the open quadrant (which makes the integrand a.e. strongly
measurable there, the complement of the quadrant being the coordinate hyperplane `z = 0` and
the two boundary lines `θ = 0`, `θ = π/2`). -/
private theorem hkInt_prodIntegrable (α : ℝ) {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hso.continuousOn_HkIntegrand α k)
  refine (MeasureTheory.integrable_prod_iff haesm).mpr ⟨?_, ?_⟩
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hmem.1 z hz
  · refine hmem.2.congr ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
          show Work.Spaces.HkIntegrand α k F z θ = ‖Work.Spaces.HkIntegrand α k F z θ‖
          rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)])

/-- **The slot domination.**  For a leaf weight `ρ` of the slot `(a,b)` with `a + b ≤ k`, the
weighted square `ρ · (D_z^bD_θ^a f)²` is pointwise dominated on the open quadrant by the
`ℋ^k`-integrand of `f`.

The two cases are `a = 0` (then `ρ` is one of the `η`-weights `w²sin(2θ)^{-η}`, `w²`, and the
slot is the pure radial slot `D_z^b f`) and `a ≥ 1` (then `ρ ≤ w²sin(2θ)^{-γ} = Wt²`, the
weight of the mixed slot). -/
private theorem slot_le_HkIntegrand (α : ℝ) (hα : 0 < α) {F : ℝ → ℝ → ℝ} {k a b : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hab : a + b ≤ k) (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  obtain ⟨-, hρle⟩ := Work.FTS.TransportS.IsLeafW_le α hα hρ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- the pure radial slot: `ρ ≤ w² sin(2θ)^{-η}` and `mixed b 0 F = D_z^b F`
    have hle := hρle z θ hz hθ.1 hθ.2
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ] at hle
    have hkey : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter b F z θ) ^ 2
        = (Work.Spaces.DzIter b F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hsin0 (by norm_num [Work.Spaces.eta])]
      ring
    calc ρ z θ * (Work.Spaces.mixed b 0 F z θ) ^ 2
        = ρ z θ * (Work.Spaces.DzIter b F z θ) ^ 2 := by rw [Work.Spaces.mixed_zero_right]
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b F z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = (Work.Spaces.DzIter b F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hkey
      _ ≤ Work.Spaces.HkIntegrand α k F z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α k F z θ b (by omega)
  · -- the mixed slot: `ρ ≤ w² sin(2θ)^{-γ} = Wt²`
    have hle := hρle z θ hz hθ.1 hθ.2
    rw [Work.FTS.TransportS.slotW_of_pos_eq α (by omega : 1 ≤ a) hθ] at hle
    have hkey : (Work.Spaces.mixed b a F z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a F z θ) ^ 2 := by
      rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθI]
      ring
    calc ρ z θ * (Work.Spaces.mixed b a F z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a F z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = (Work.Spaces.mixed b a F z θ * Work.Spaces.Wt α z θ) ^ 2 := hkey.symm
      _ ≤ Work.Spaces.HkIntegrand α k F z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ a b (by omega) (by omega)

/-- **Slot integrability.**  The weighted square `ρ · (D_z^bD_θ^a f)²` of a slot with
`a + b ≤ k` is integrable for the product measure, by domination against the (integrable)
`ℋ^k`-integrand of `f`. -/
private theorem slot_integrable (α : ℝ) (hα : 0 < α) {F : ℝ → ℝ → ℝ} {k a b : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hab : a + b ≤ k)
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a F p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (hkInt_prodIntegrable α hso hmem).mono' ?_ ?_
  · exact Work.Spaces.aesm_of_continuousOn_Qd _
      ((Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ).mul
        ((hso.mixed b a).continuousOn.pow 2))
  · simpa only [Prod.mk.eta] using
      (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
        (p := fun z θ => ‖ρ z θ * (Work.Spaces.mixed b a F z θ) ^ 2‖
          ≤ Work.Spaces.HkIntegrand α k F z θ)
        (fun θ hθ z hz => by
          rw [Real.norm_of_nonneg (mul_nonneg
            ((Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ.1 hθ.2) (sq_nonneg _))]
          exact slot_le_HkIntegrand α hα hab hρ hz hθ))

theorem leadPiece (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f A : ℝ → ℝ → ℝ}
    {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {K : ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (h6 : Work.Spaces.HkMem α 6 f) (h7 : Work.Spaces.HkMem α 7 f)
    (hK : 0 ≤ K) (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6)
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |A z θ| ≤ K) :
    AEMeasurable (Function.uncurry (Work.Spaces.mixed b a f))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
          * Work.Spaces.mixed b a f p.1 p.2)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the level-six slot `(a,b)`
  have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    slot_integrable α hα hso h6 hab hρ
  -- the level-seven slot `(a,b+1)`: `z ∂_z (D_z^bD_θ^a f) = D_z^{b+1}D_θ^a f`
  have h3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h := slot_integrable (k := 7) (b := b + 1) α hα hso h7 (by omega) hρ
    exact h.congr (Filter.Eventually.of_forall fun p => rfl)
  -- the cross term `ρ · A · (z∂_z m) · m`, by AM–GM and `|A| ≤ K`
  have h4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hXc : ContinuousOn (fun p : ℝ × ℝ =>
        p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      continuousOn_fst.mul ((hso.mixed b a).pz.continuousOn)
    have hYc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hso.mixed b a).continuousOn
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (A p.1 p.2 * ((p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2)
          * Work.Spaces.mixed b a f p.1 p.2)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        ((Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.continuousOn_leaf_Q0 hρ).mul
          (hAso.continuousOn.mul (hXc.mul hYc)))
    have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ => (K / 2)
        * (ρ p.1 p.2 * (p.1 * Work.Spaces.pz (Work.Spaces.mixed b a f) p.1 p.2) ^ 2
          + ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := (h3.add h2).const_mul (K / 2)
    refine hdom.mono' haesm ?_
    simpa only [Prod.mk.eta] using
      (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
        (p := fun z θ => ‖ρ z θ * (A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
            * Work.Spaces.mixed b a f z θ))‖
          ≤ (K / 2) * (ρ z θ * (z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) ^ 2
            + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2))
        (fun θ hθ z hz => by
          have hXn : 0 ≤ ρ z θ :=
            (Work.FTS.TransportS.IsLeafW_le α hα hρ).1 z θ hz hθ.1 hθ.2
          have hA := hAbd z θ hz hθ.1 hθ.2
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hXn]
          have h0 : |A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
              * Work.Spaces.mixed b a f z θ)|
              ≤ K * |(z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
                * Work.Spaces.mixed b a f z θ| := by
            nth_rewrite 1 [abs_mul]
            exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
          have h1 : K * |(z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
                * Work.Spaces.mixed b a f z θ|
              ≤ K * ((1 / 2) * (z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) ^ 2
                + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left
              (Work.FTS.StrongPersist.H6Pair6Aux.abs_mul_le_half _ _) hK
          calc ρ z θ * |A z θ * ((z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
                * Work.Spaces.mixed b a f z θ)|
              ≤ ρ z θ * (K * |(z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ)
                * Work.Spaces.mixed b a f z θ|) := mul_le_mul_of_nonneg_left h0 hXn
            _ ≤ ρ z θ * (K * ((1 / 2) * (z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) ^ 2
                  + (1 / 2) * (Work.Spaces.mixed b a f z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left h1 hXn
            _ = (K / 2) * (ρ z θ * (z * Work.Spaces.pz (Work.Spaces.mixed b a f) z θ) ^ 2
                  + ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring))
  exact ⟨(Work.Spaces.aesm_of_continuousOn_Qd _
      (hso.mixed b a).continuousOn).aemeasurable, h2, h3, h4⟩

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
