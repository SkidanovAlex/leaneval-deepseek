import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.leadPiece =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

/- Bound for the `k = 0` term of the `L₁₂·D_θ` slot expansion.

Context: `Work.FTS.TransportS.slotPairing ρ a b u v = ∫_z∫_θ ρ·(D_z^bD_θ^a u)·(D_z^bD_θ^a v)`;
`IsLeafW α a ρ` says `ρ` is one of the three leaf weights `w(z)²sin(2θ)^{-η}`, `w(z)²`,
`w(z)²sin(2θ)^{-γ}` (the last only for `a ≥ 1`); `HkNorm α k f = √(HkSq α k f)` and `HkSq α k`
is the weighted ℋ^k energy of the paper.

The Leibniz expansion of `slotPairing ρ a b (fun z θ => L₁₂ f z * D_θ f z θ)` (with `L₁₂ f`
radial) produces one term per `k ≤ b`, of which the `k = 0` one is
`∫_z L₁₂ f z·(∫_θ ρ z θ·(D_z^bD_θ^{a+1}f)·(D_z^bD_θ^a f))`; the claim below is that its
absolute value is `≤ C·|f|_{ℋ⁴}·|f|²_{ℋ⁶}`.

Planned route: `ρ = w(z)²·sin(2θ)^{-q}` for `q = η`, `0` or `γ`.  Put
`h := fun z θ => D_z^bD_θ^a f z θ` (`SmoothOpen`, since `f` is) and `Φ z := L₁₂ f z·(w z)²`;
on the open quadrant `D_θ h = D_z^bD_θ^{a+1}f` (commutation of `D_θ` with `D_z^b`, e.g.
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen` for `Q0`), so the
double integral is exactly `Work.Coercivity.wip (fun z θ => Φ z·sin(2θ)^{-q}) (D_θ h) h`, to
which `Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp` applies, giving
`(q-1)·∫_z Φ z·(∫_θ cos(2θ)sin(2θ)^{-q}h²)`.  Since `|q-1| ≤ 1` and `|L₁₂ f z| ≤ C₄|f|_{ℋ⁴}`
for `z > 0` (`L12Sup4` at `k = 0`) while `∫_z w²∫_θ sin(2θ)^{-q}h² = ∫∫ρh² ≤ HkSq α 6 f`
(`leaf_slot_le6`), this is `≤ C₄|f|_{ℋ⁴}·HkSq α 6 f`.  The three `IntegrableOn (Iz×ˢIθ)`
hypotheses of `wip_Dth_ibp` are dominated by `C|f|_{ℋ⁴}·HkIntegrand α 7 f` (resp.
`HkIntegrand α 6 f`), jointly integrable by
`Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen`; the `z = 0` slice is killed by `w 0 = 0`. -/
theorem L12ShiftThetaLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
  -- The constant is the one of `L12Sup4`, the uniform bound `|L₁₂ f z| ≤ C₄|f|_{ℋ⁴}`.
  obtain ⟨C₄, hC₄pos, hC₄⟩ := L12Sup4
  refine ⟨C₄, hC₄pos, ?_⟩
  intro α hαIoc f a b ρ hO hmem6 hmem7 h0 hab hρ
  obtain ⟨hα, hα1⟩ := hαIoc
  -- `z > 0` almost everywhere on `Iz` (only `z = 0` is excluded).
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hEq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- The pointwise bound on `L₁₂ f`, valid on all of `Iz` (`z = 0` uses `L₁₂ f 0 = 0`).
  have hCbound : ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · rw [← h, h0, abs_zero]
      exact mul_nonneg (le_of_lt hC₄pos) (Work.Spaces.HkNorm_nonneg α 4 f)
    · have hh := hC₄ α f hα hα1 hO hmem6 h0 0 (by norm_num) z h
      simpa using hh
  -- The core estimate for an exponent `q` with `σ^{-q}` dominated by the leaf blocks.
  have main : ∀ (q : ℝ) (ρ : ℝ → ℝ → ℝ),
      |q - 1| ≤ 1 → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      ρ = (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
    intro q ρ hqabs hqle hq0 hρq hρlem
    subst hρq
    -- The three integrability hypotheses of the angular integration by parts.
    obtain ⟨hi0, hi1, hi2, _hprod, hout, hslice⟩ :=
      Work.FTS.StrongPersist.H6Pair6Aux.ibp_integrable_fts hα hα1 hO hmem6 hmem7 h0 hab hqle hq0
    -- Step A: pull the radial weight `(w z)²` out of the angular integral.
    have hAint : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ := by
      intro z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    have hA : (∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show Work.Construction.L12 f z *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      rw [hAint z]
      ring
    -- Step B: replace `D_z^bD_θ^{a+1}f` by `D_θ(D_z^bD_θ^a f)` inside the angular integral.
    have hB : (∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ))
        = ∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hzpos] with z hz
      have hinner : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
        have h2 := Work.FTS.StrongPersist.H6Pair6Aux.dth_mixed_eqOn_Q0 (f := f) hO a b
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ.1, hθ.2⟩)
        have h1 : Work.Spaces.mixed b (a + 1) f z θ
            = Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ := h2.symm
        rw [h1]
      show (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
          = (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
      rw [hinner]
    -- Step C: identify the iterated integral with the `ρ`-weighted pairing `wip`.
    have hC : (∫ z in Work.Spaces.Iz,
            (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
          (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ))
        = Work.Coercivity.wip
            (fun z θ => (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-q))
            (Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ))
            (fun z θ => Work.Spaces.mixed b a f z θ) := by
      rw [Work.Coercivity.wip]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) *
            (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          = ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * (fun z θ => Work.Spaces.mixed b a f z θ) z θ
              * ((Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-q))
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- The angular integration by parts.
    have hIBP := Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp
        (h := fun z θ => Work.Spaces.mixed b a f z θ)
        (Φ := fun z => Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) (q := q)
        (hO.mixed b a) hi0 hi1 hi2
    rw [hA, hB, hC, hIBP]
    -- The remaining one-dimensional estimate.
    exact Work.FTS.StrongPersist.H6Pair6Aux.end_bound_fts (f := f) (a := a) (b := b)
      (q := q) (C₄ := C₄) hα hmem6 hab hqabs hCbound hρlem hout hslice
  -- The three leaf weights.
  rcases hρ with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = w²σ^{-η}`
    subst hρ
    exact main Work.Spaces.eta Work.FTS.TransportS.leafEta
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta, Work.Spaces.gam]; linarith) (fun _ => le_rfl) rfl (Or.inl rfl)
  · -- `ρ = w²`
    subst hρ
    refine main 0 Work.FTS.TransportS.leafOne ?_ (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by rw [Work.Spaces.eta]; norm_num) ?_ (Or.inr (Or.inl rfl))
    · rw [zero_sub, abs_neg, abs_one]
    · funext z θ
      simp [Work.FTS.TransportS.leafOne, Real.rpow_zero]
  · -- `ρ = w²σ^{-γ}` (only for `a ≥ 1`)
    subst hρ
    refine main (Work.Spaces.gam α) (Work.FTS.TransportS.leafGam α) ?_ le_rfl ?_ rfl
      (Or.inr (Or.inr ⟨ha1, rfl⟩))
    · rw [Work.Spaces.gam_sub_one, abs_of_nonneg (by linarith : (0 : ℝ) ≤ α / 10)]
      linarith
    · intro ha0; omega

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtw =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem piece_abs_le_zero {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {a b k : ℕ}
    {C4 C6 Cc : ℝ} (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hk : k ≤ b) (hb : b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ)|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hρnn : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hc2 : |Work.Construction.c2m θ| ≤ Cc := hCcbd θ hθI
  have hL : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact hsup4 k h z hz
    · rw [if_neg h]; exact hsup6 k (by omega) z hz
  have hKnn : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · rw [if_neg h]; exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hfac : 0 ≤ ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
      * |Work.Spaces.mixed b a f z θ| :=
    mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _)
  have h1 : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Construction.c2m θ|
        ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
            else C6 * Work.Spaces.HkNorm α 6 f) * Cc :=
    mul_le_mul hL hc2 (abs_nonneg _) hKnn
  have h2 := mul_le_mul_of_nonneg_right h1 hfac
  have hkey : ρ z θ * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Construction.c2m θ| * |Work.Spaces.mixed (b - k + 1) a f z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
    calc ρ z θ * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          * |Work.Construction.c2m θ| * |Work.Spaces.mixed (b - k + 1) a f z θ|
          * |Work.Spaces.mixed b a f z θ|
        = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Construction.c2m θ|)
            * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ ((if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f) * Cc)
            * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := h2
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece, Work.Spaces.DthIter_zero]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
  exact hkey

/-- The pointwise bound on the piece when the `c₂ₘ`-factor carries at least one angular
derivative: then `|D_θ^i c₂ₘ| ≤ Cc·sin(2θ)`, and the `σ`-gain `sigma_mul_leaf_le` upgrades
`sin(2θ)·ρ` to the single weight `w²·sin(2θ)^{-(γ-1)}`. -/
theorem piece_abs_le_pos {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {a b k i : ℕ}
    {C4 C6 Cc : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcg : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter j (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    (hk : k ≤ b) (hb : b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hi1 : 1 ≤ i) (hi8 : i ≤ 8)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ)|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * |Work.Spaces.mixed (b - k + 1) (a - i) f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hc2 : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
      ≤ Cc * Real.sin (2 * θ) := hCcg i hi1 hi8 z θ hθI
  have hL : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact hsup4 k h z hz
    · rw [if_neg h]; exact hsup6 k (by omega) z hz
  have hKnn : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · rw [if_neg h]; exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hsig : Real.sin (2 * θ) * ρ z θ
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.sigma_mul_leaf_le hα hleaf hθ
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  set D : ℝ := |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| with hD
  set Cz : ℝ := |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| with hCz
  set Xx : ℝ := |Work.Spaces.mixed (b - k + 1) (a - i) f z θ| with hXx
  set Yy : ℝ := |Work.Spaces.mixed b a f z θ| with hYy
  have hDnn : 0 ≤ D := by rw [hD]; exact abs_nonneg _
  have hXnn : 0 ≤ Xx := by rw [hXx]; exact abs_nonneg _
  have hYnn : 0 ≤ Yy := by rw [hYy]; exact abs_nonneg _
  have hρ0 : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hc2' : Cz ≤ Cc * Real.sin (2 * θ) := by rw [hCz]; exact hc2
  have hL' : D ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by rw [hD]; exact hL
  -- the three-factor step `ρ·|D_z^kL₁₂|·|D_θ^i c₂ₘ| ≤ (Cc·K)·W`
  have hstep1 : ρ z θ * D * Cz ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f))
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) := by
    have h1 : ρ z θ * Cz ≤ Cc * (Real.sin (2 * θ) * ρ z θ) := by
      calc ρ z θ * Cz ≤ ρ z θ * (Cc * Real.sin (2 * θ)) :=
            mul_le_mul_of_nonneg_left hc2' hρ0
        _ = Cc * (Real.sin (2 * θ) * ρ z θ) := by ring
    have h2 : Cc * (Real.sin (2 * θ) * ρ z θ)
        ≤ Cc * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) :=
      mul_le_mul_of_nonneg_left hsig hCc
    calc ρ z θ * D * Cz = (ρ z θ * Cz) * D := by ring
      _ ≤ (Cc * ((Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)))) * D :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hDnn
      _ ≤ (Cc * ((Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))))
            * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hL' (mul_nonneg hCc hWnn)
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) := by ring
  have hkey : ρ z θ * D * Cz * Xx * Yy
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * Xx * Yy) := by
    calc ρ z θ * D * Cz * Xx * Yy = (ρ z θ * D * Cz) * (Xx * Yy) := by ring
      _ ≤ ((Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))))
            * (Xx * Yy) := mul_le_mul_of_nonneg_right hstep1 (mul_nonneg hXnn hYnn)
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * Xx * Yy) := by ring
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0,
    ← hD, ← hCz, ← hXx, ← hYy]
  exact hkey

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem t5bPiecePtwIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {C4 C6 Cc : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hCsm : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Work.Construction.c2m θ))
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hCcg : ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    {k i : ℕ} (hk : k ≤ b) (hi : i ≤ a) :
    (∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i p|
        ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
            * ((if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f) * Cc)
            * (Work.Spaces.HkIntegrand α 7 f p.1 p.2
                + Work.Spaces.HkIntegrand α 6 f p.1 p.2)) ∧
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set M : ℝ := (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    split_ifs
    · exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hA : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M := by
    intro z hz
    rw [hMdef]
    by_cases hk4 : k ≤ 4
    · rw [if_pos hk4]; exact hsup4 k hk4 z hz
    · rw [if_neg hk4]; exact hsup6 k (by omega) z hz
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |t5bPiece f ρ a b k i (z, θ)| ≤
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
    t5bPiece_abs_le_quad (α := α) (f := f) (a := a) (b := b) (ρ := ρ) (M := M) (Cc := Cc)
      (k := k) (i := i) hα hα1 hab hleaf hMnn hCc hA hCcbd hCcg hk hi
  refine ⟨?_, ?_⟩
  · simpa only [Prod.mk.eta] using
      (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
        (p := fun z θ => |t5bPiece f ρ a b k i (z, θ)| ≤
          ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
            * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (fun θ hθ z hz => hpt z θ hz hθ.1 hθ.2))
  · -- ## integrability
    have hconst : 0 ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg hMnn hCc)
    have hdom_cont : ContinuousOn
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        Work.FTS.EllipticEst.Q0 :=
      (((hso.continuousOn_HkIntegrand α 7).add (hso.continuousOn_HkIntegrand α 6)).const_mul _)
    have hdom_aesm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hdom_cont
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        Integrable (fun θ : ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
        (((hm7.1 z hz).add (hm6.1 z hz)).const_mul
          (((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)))
    have hmarg : Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hbase : Integrable (fun z : ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (hm7.2.add hm6.2).const_mul _
      refine hbase.congr ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => by
        simp only [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hm7.1 z hz) (hm6.1 z hz)]
    have hnorm : Integrable (fun z : ℝ => ∫ θ, ‖((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      refine hmarg.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      refine MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
      exact (Real.norm_of_nonneg (mul_nonneg hconst
        (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)
          (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)))).symm
    have hgint : Integrable
        (fun p : ℝ × ℝ => ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (MeasureTheory.integrable_prod_iff hdom_aesm).mpr ⟨hslice, hnorm⟩
    have hbd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
        ‖t5bPiece f ρ a b k i p‖
          ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
            * (Work.Spaces.HkIntegrand α 7 f p.1 p.2 + Work.Spaces.HkIntegrand α 6 f p.1 p.2) := by
      simpa only [Prod.mk.eta] using
        (Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo
          (p := fun z θ => ‖t5bPiece f ρ a b k i (z, θ)‖
            ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
              * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ))
          (fun θ hθ z hz => by
            rw [Real.norm_eq_abs]
            exact hpt z θ hz hθ.1 hθ.2))
    have hpiece_cont : ContinuousOn (fun p : ℝ × ℝ => t5bPiece f ρ a b k i p)
        Work.FTS.EllipticEst.Q0 := by
      have hAc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) p.1)
          Work.FTS.EllipticEst.Q0 := by
        have hc := continuousOn_DzdIter_L12 hα hα1 hso hm7 (k := k) (by omega)
        exact hc.comp continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
      have hBc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ)
            p.1 p.2) Work.FTS.EllipticEst.Q0 :=
        (hCsm.DthIter i).continuousOn
      have hXc : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.mixed (b - k + 1) (a - i) f p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hso.mixed (b - k + 1) (a - i)).continuousOn
      have hYc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (hso.mixed b a).continuousOn
      have hρc := continuousOn_leaf_Q0 hleaf
      have h := ((((hρc.mul hAc).mul hBc).mul hXc).mul hYc)
      exact h.congr (fun p _ => by simp only [Pi.mul_apply, t5bPiece])
    exact hgint.mono' (Work.Spaces.aesm_of_continuousOn_Qd _ hpiece_cont) hbd

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
end
