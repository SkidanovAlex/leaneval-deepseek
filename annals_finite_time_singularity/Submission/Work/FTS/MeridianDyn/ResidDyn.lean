import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico
import Submission.Work.FTS.Physical.Reconstruction
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.H2.T1Q.IbpCutoff
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.rho_theta_sect =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

/-- **The `(ρ, θ)` coordinates of the point `ρ' (cos θ' e_r + sin θ' e_z)`.**

Writing `y := ρ' • (cos θ' • e_r x + sin θ' • e_z)` for a point `x` off the axis and a positive
radius `ρ'`, the sector `|θ'| < π/2` has all of its `y`-coordinates nonnegative: the radial part
`(y 0, y 1, 0) = ρ' cos θ' • e_r x` carries the factor `ρ' cos θ'` and the axial part is
`ρ' sin θ'`.  Hence `radSq y = (ρ' cos θ')²`, `axial y = ρ' sin θ'` and consequently
`ρ(y) = ρ'`, while `radial y = √(radSq y) = ρ' cos θ' > 0` (here `cos θ' > 0` is exactly the
sector hypothesis), so `θ(y) = arctan (ρ' sin θ' / (ρ' cos θ')) = arctan (tan θ') = θ'`. -/
theorem rho_theta_sect (x : EuclideanSpace ℝ (Fin 3)) (hr : 0 < Work.Cyl.radial x)
    {ρ' θ' : ℝ} (hρ' : 0 < ρ') (hθ' : |θ'| < Real.pi / 2) :
    Work.Cyl.rho (ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ)) = ρ' ∧
      Work.Cyl.theta (ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ)) = θ' := by
  have hth : -(Real.pi / 2) < θ' ∧ θ' < Real.pi / 2 := abs_lt.mp hθ'
  have hcos : 0 < Real.cos θ' := Real.cos_pos_of_mem_Ioo ⟨hth.1, hth.2⟩
  set y := ρ' • (Real.cos θ' • Work.Cyl.eR x + Real.sin θ' • Work.Cyl.eZ) with hy
  have hy0 : y 0 = ρ' * Real.cos θ' * (x 0 / Work.Cyl.radial x) := by
    rw [hy]; simp [Work.Cyl.eR, div_eq_inv_mul]; ring
  have hy1 : y 1 = ρ' * Real.cos θ' * (x 1 / Work.Cyl.radial x) := by
    rw [hy]; simp [Work.Cyl.eR, div_eq_inv_mul]; ring
  have hy2 : y 2 = ρ' * Real.sin θ' := by
    rw [hy]; simp [Work.Cyl.eR]
  have hradSq : Work.Cyl.radSq y = (ρ' * Real.cos θ') ^ 2 := by
    rw [Work.Cyl.radSq, hy0, hy1]
    field_simp
    rw [Work.Cyl.radial_sq, show Work.Cyl.radSq x = x 0 ^ 2 + x 1 ^ 2 from rfl]
  have hradial : Work.Cyl.radial y = ρ' * Real.cos θ' := by
    rw [Work.Cyl.radial, hradSq, Real.sqrt_sq_eq_abs]
    exact abs_of_pos (mul_pos hρ' hcos)
  have hsinCos : (ρ' * Real.cos θ') ^ 2 + (ρ' * Real.sin θ') ^ 2 = ρ' ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ']
  constructor
  · rw [Work.Cyl.rho, Work.Cyl.axial_eq, hradSq, hy2, hsinCos, Real.sqrt_sq_eq_abs]
    exact abs_of_pos hρ'
  · rw [Work.Cyl.theta, Work.Cyl.axial_eq, hy2, hradial]
    have hdiv : ρ' * Real.sin θ' / (ρ' * Real.cos θ') = Real.sin θ' / Real.cos θ' := by
      field_simp
    rw [hdiv, ← Real.tan_eq_sin_div_cos, Real.arctan_tan hth.1 hth.2]

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.transfer_rho_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.FTS.FireFix.Clauses

theorem transfer_rho_theta {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {F : ℝ → ℝ → ℝ}
    (hF : ∀ z θ, 0 ≤ F z θ)
    (hint : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => F q.1 q.2 * q.1 ^ (1 / α - 1) * Real.cos q.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        F (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), F (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x))
        = 2 * Real.pi * B ^ (1 / α) / (3 * α) *
          ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
            F q.1 q.2 * q.1 ^ (1 / α - 1) * Real.cos q.2 := by
  have hVmeas : MeasurableSet Adom := measurableSet_Ioi.prod measurableSet_Ioo
  set c : ℝ := 2 * Real.pi * B ^ (1 / α) / (3 * α) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set w : ℝ × ℝ → ℝ := fun q => q.1 ^ (1 / α - 1) * Real.cos q.2 with hwdef
  set T : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ :=
    fun x => (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x) with hTdef
  have hT : Measurable T := measurable_rhoTheta hα.le
  -- (1) the hypothesis restated with the angular weight `w`
  have hintW : Integrable (fun q : ℝ × ℝ => F q.1 q.2 * w q) (volume.restrict Adom) := by
    refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hwdef]
    ring
  -- (2) the angular weight does not vanish on the domain
  have hwne : ∀ q ∈ Adom, w q ≠ 0 := by
    rintro ⟨r, θ⟩ hq
    obtain ⟨hr, hθ⟩ := hq
    simp only [hwdef]
    exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hr (1 / α - 1)))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo hθ))
  -- (3) the angular weight is nonnegative on the domain
  have hwnonneg : ∀ q ∈ Adom, 0 ≤ w q := by
    rintro ⟨r, θ⟩ hq
    obtain ⟨hr, hθ⟩ := hq
    simp only [hwdef]
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hr (1 / α - 1)))
      (le_of_lt (Real.cos_pos_of_mem_Ioo hθ))
  -- (4) a.e.-measurability of the angular weight
  have hw_aemeas : AEMeasurable w (volume.restrict Adom) := by
    have hs : MeasurableSet {q : ℝ × ℝ | 0 < q.1} := measurableSet_Ioi.preimage measurable_fst
    have hcon : ContinuousOn (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1)) {q : ℝ × ℝ | 0 < q.1} :=
      continuous_fst.continuousOn.rpow_const (fun q hq => Or.inl (ne_of_gt hq))
    have h1 : AEMeasurable (fun q : ℝ × ℝ => q.1 ^ (1 / α - 1))
        ((volume.restrict Adom).restrict {q : ℝ × ℝ | 0 < q.1}) := hcon.aemeasurable hs
    have heq : (volume.restrict Adom).restrict {q : ℝ × ℝ | 0 < q.1} = volume.restrict Adom := by
      rw [Measure.restrict_restrict (μ := (volume : Measure (ℝ × ℝ))) hs,
        Set.inter_eq_right.mpr (fun q hq => hq.1)]
    rw [heq] at h1
    exact h1.mul (Real.continuous_cos.measurable.comp measurable_snd).aemeasurable
  -- (5) a.e.-measurability of `F` on the domain, and a measurable version `F'` of it
  have hFae : AEMeasurable (fun q : ℝ × ℝ => F q.1 q.2) (volume.restrict Adom) := by
    have h1 : AEMeasurable (fun q : ℝ × ℝ => F q.1 q.2 * w q) (volume.restrict Adom) :=
      hintW.aestronglyMeasurable.aemeasurable
    refine (h1.div hw_aemeas).congr ?_
    filter_upwards [self_mem_ae_restrict hVmeas] with q hq
    show (F q.1 q.2 * w q) / w q = F q.1 q.2
    rw [mul_div_cancel_right₀ _ (hwne q hq)]
  obtain ⟨F', hF'meas, hF'ae⟩ := hFae
  -- (6) the change of variables, in the pair form
  have htrans : ∀ G : ℝ × ℝ → ENNReal, Measurable G →
      (∫⁻ x : EuclideanSpace ℝ (Fin 3), G (T x))
        = ENNReal.ofReal c * ∫⁻ q in Adom, ENNReal.ofReal (w q) * G q := by
    intro G hG
    have h := lintegral_transfer (α := α) (B := B) hα hB (g := fun z θ => G (z, θ))
      (show Measurable (fun q : ℝ × ℝ => G (q.1, q.2)) from hG)
    simpa only [hTdef, hcdef] using h
  -- (7) the pushforward of Lebesgue by `T` vanishes on the domains where `F` vanishes a.e.
  have hac : ∀ S : Set (ℝ × ℝ), MeasurableSet S → (volume.restrict Adom) S = 0 →
      (Measure.map T volume) S = 0 := by
    intro S hSmeas hS0
    have h := htrans (S.indicator fun _ => (1 : ENNReal)) (Measurable.indicator measurable_const hSmeas)
    have hL : (∫⁻ x : EuclideanSpace ℝ (Fin 3), S.indicator (fun _ => (1 : ENNReal)) (T x))
        = (Measure.map T volume) S := by
      rw [← lintegral_indicator_one (μ := Measure.map T volume) hSmeas]
      exact (lintegral_map (measurable_const.indicator hSmeas) hT).symm
    have hR : (∫⁻ q in Adom, ENNReal.ofReal (w q) * S.indicator (fun _ => (1 : ENNReal)) q) = 0 := by
      have h1 : (fun q : ℝ × ℝ => ENNReal.ofReal (w q) * S.indicator (fun _ => (1 : ENNReal)) q)
          = S.indicator (fun q => ENNReal.ofReal (w q)) := by
        funext q
        by_cases hq : q ∈ S
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, mul_one]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
      rw [h1, lintegral_indicator hSmeas]
      exact setLIntegral_measure_zero S _ hS0
    rw [← hL, h, hR, mul_zero]
  -- (8) the exceptional set is null
  have hnull : volume {x : EuclideanSpace ℝ (Fin 3) | F (T x).1 (T x).2 ≠ F' (T x)} = 0 := by
    have hN : (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q} = 0 := hF'ae
    have hN' : (volume.restrict Adom)
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) = 0 := by
      rw [measure_toMeasurable]; exact hN
    have hmeasN' : MeasurableSet
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
      measurableSet_toMeasurable _ _
    have h0 : (Measure.map T volume)
        (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) = 0 :=
      hac _ hmeasN' hN'
    refine le_antisymm ?_ zero_le
    calc volume {x : EuclideanSpace ℝ (Fin 3) | F (T x).1 (T x).2 ≠ F' (T x)}
        ≤ volume (T ⁻¹' toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
          measure_mono fun x hx => subset_toMeasurable _ _ hx
      _ = (Measure.map T volume)
            (toMeasurable (volume.restrict Adom) {q : ℝ × ℝ | F q.1 q.2 ≠ F' q}) :=
          (Measure.map_apply hT hmeasN').symm
      _ = 0 := h0
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin 3) ∂volume, F (T x).1 (T x).2 = F' (T x) :=
    (MeasureTheory.ae_iff).mpr hnull
  -- (9) a.e.-strong measurability of `F ∘ T`
  have hFT_aesm : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => F (T x).1 (T x).2) volume := by
    refine ((hF'meas.comp hT).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with x hx
    exact hx.symm
  -- (10) the two lintegral identities
  have hgeJ : 0 ≤ᵐ[volume.restrict Adom] (fun q : ℝ × ℝ => F q.1 q.2 * w q) := by
    filter_upwards [self_mem_ae_restrict hVmeas] with q hq
    exact mul_nonneg (hF q.1 q.2) (hwnonneg q hq)
  have hkey : (∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F q.1 q.2))
      = ENNReal.ofReal (∫ q in Adom, F q.1 q.2 * w q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hintW hgeJ]
    refine setLIntegral_congr_fun hVmeas fun q _ => ?_
    rw [mul_comm, ← ENNReal.ofReal_mul (hF q.1 q.2)]
  have hmain : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F' (T x)))
      = ENNReal.ofReal c * ENNReal.ofReal (∫ q in Adom, F q.1 q.2 * w q) := by
    have h1 := htrans (fun q => ENNReal.ofReal (F' q)) (ENNReal.measurable_ofReal.comp hF'meas)
    have h2 : (∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F' q))
        = ∫⁻ q in Adom, ENNReal.ofReal (w q) * ENNReal.ofReal (F q.1 q.2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF'ae] with q hq
      rw [← hq]
    rw [h1, h2, hkey]
  have hIntEq : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F (T x).1 (T x).2))
      = ∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F' (T x)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  -- (11) integrability
  have hnorm : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ‖F (T x).1 (T x).2‖ₑ)
      = ∫⁻ x : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (F (T x).1 (T x).2) :=
    lintegral_congr fun x => Real.enorm_of_nonneg (hF (T x).1 (T x).2)
  refine ⟨⟨hFT_aesm, ?_⟩, ?_⟩
  · show (∫⁻ x : EuclideanSpace ℝ (Fin 3), ‖F (T x).1 (T x).2‖ₑ) < ∞
    rw [hnorm, hIntEq, hmain, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => hF _ _) hFT_aesm,
      hIntEq, hmain, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hgeJ), hcdef]
    congr 1
    refine setIntegral_congr_fun hVmeas fun q _ => ?_
    simp only [hwdef]
    ring

end Work.FTS.FireFix.Clauses
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Reconstruct =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Physical (physVel)

/-! ## Locality of `C¹` on time strips, with a radius per strip -/

/-- **Locality of `C¹` on time strips.**  If the space-time field `u = physVel ω` is `C¹` on every
compact strip `ℝ³ × [0,S]`, `S < T` — which the space–time Schauder estimate supplies as soon as
each strip carries *some* admissible bundle — then it is `C¹` on the half-open strip
`ℝ³ × [0,T)` demanded by `IsLocalEulerEquationSolution`.

This is `Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico` with the radius allowed to depend on
the strip; its proof is copied from there (that lemma's locality step is private). -/
theorem contDiffOn_Ico_of_strips_existsRadius {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hbun : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
  have hst := (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds (α := α) hα hα1).2.2
  have hstrips : ∀ S ∈ Set.Ioo 0 T,
      ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) := by
    intro S hS
    obtain ⟨R, hb⟩ := hbun S hS
    exact (hst ω R S hS.1 hb).1
  intro x hx
  obtain ⟨a, t⟩ := x
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hx
  set S : ℝ := (t + T) / 2 with hSdef
  have hST : t < S := by simp only [hSdef]; linarith [hx.2]
  have hS : S ∈ Set.Ioo (0 : ℝ) T :=
    ⟨by simp only [hSdef]; linarith [hx.1, hx.2], by simp only [hSdef]; linarith [hx.2]⟩
  have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_of_lt hST⟩
  have hEv : (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      =ᶠ[𝓝 ((a, t) : R3 × ℝ)] (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
    have hmem : (Set.univ ×ˢ Set.Ioo (-1 : ℝ) S) ∈ 𝓝 ((a, t) : R3 × ℝ) := by
      rw [nhds_prod_eq, Filter.prod_mem_prod_iff]
      exact ⟨univ_mem, Ioo_mem_nhds (by linarith [hx.1]) hST⟩
    filter_upwards [hmem] with y hy
    obtain ⟨b, s⟩ := y
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc, Set.mem_Ico] at hy ⊢
    exact propext ⟨fun h' => ⟨h'.1, lt_of_le_of_lt h'.2 hS.2⟩,
      fun h' => ⟨h'.1, le_of_lt hy.2⟩⟩
  exact (hstrips S hS (a, t) ⟨Set.mem_univ _, htS⟩).congr_set hEv

/-! ## The generic reconstruction theorem -/

/-- **THE GENERIC PHYSICAL RECONSTRUCTION (design §5 item 7).**  From a physical vorticity `ω`
whose every strip carries *some* full admissible bundle (`hbun`, a radius per strip), which is the
curl of `u = physVel ω` and whose Biot–Savart velocity is divergence-free, odd, with the local
vorticity equation on `Uax` and the four analytic clauses of the pressure input, and whose
sup-norm dominates `c/(T−t)`, the pair `(u, p)` produced by `PressureReconstructionOn α` is a
finite-time blow-up in node N0's interface `Work.FTS.Top.BlowupAt α T`.

Departures from the delivered `Work.FTS.Physical.blowupAt_of_physical` (design §5 item 7):

* the radius is chosen per strip (`hbun`), so no uniform support hypothesis `hsupp` and no `hR` are
  needed — the datum's decay clause is derived from the bundle at `S = T/2`;
* the honest pressure input `PressureReconstructionOn α` replaces the false
  `Work.LWP.PressureReconstruction`; its four non-derivable hypothesis clauses are the hypotheses
  `hωcont`, `hωderiv`, `hωLI`, `hUax` (verbatim from the design's statement of the pressure
  predicate);
* the Biot–Savart inversion `hcurl`/`hdivu` is taken as a hypothesis here (in the application it is
  `Work.FTS.BSSwirl.BiotSavartSwirl` applied slicewise). -/
noncomputable def blowupAt_of_physical' {α : ℝ≥0} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hbun : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x : R3,
      vorticity (fun y => physVel ω y t) x = ω x t)
    (hdivu : ∀ t ∈ Set.Ico 0 T, div (fun y => physVel ω y t) = 0)
    (hodd : ∀ t ∈ Set.Ico 0 T, IsOdd ((physVel ω) · t))
    (hωcont : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) T))
    (hωderiv : ∀ x : R3, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t)
    (hωLI : ∀ t ∈ Set.Ioo 0 T, LocallyIntegrable (fun x : R3 => fderiv ℝ (ω · t) x))
    (hUax : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Uax,
      ContDiffAt ℝ 2 ((physVel ω) · t) x ∧ ContDiffAt ℝ 1 (ω · t) x ∧
        timeDeriv ω x t + directionalDeriv ω (physVel ω) x t
          = directionalDeriv (physVel ω) ω x t)
    (hcd0 : IsContDiffHolder ℝ α ((physVel ω) · 0))
    (hpress : Work.FTS.PressureOn.PressureReconstructionOn α)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ ⨆ x : R3, ‖ω x t‖) :
    Work.FTS.Top.BlowupAt α T := by
  -- the `C^{1,α}` strips of the reconstructed velocity, and its joint `C¹` on `[0,T)`
  have hstrip : ∀ S ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (physVel ω).uncurry (Set.univ ×ˢ Set.Icc (0 : ℝ) S) := by
    intro S hS
    obtain ⟨R, hb⟩ := hbun S hS
    exact Work.FTS.Physical.isContDiffHolderOn_physVel hα hα1 hS.1 hb
  have hcont1 : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Ico (0 : ℝ) T) :=
    contDiffOn_Ico_of_strips_existsRadius hα hα1 hT hbun
  -- the per-strip support radius (the support clause of the bundle)
  have hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ x : R3, ω x t ≠ 0 → ‖x‖ ≤ R := by
    intro S hS
    obtain ⟨R, ⟨hR, hsuppR, -⟩, -⟩ := hbun S hS
    refine ⟨R, fun t ht x hx => ?_⟩
    have h := hsuppR t ht x hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  -- the pressure, through the design's pressure predicate
  have hex := hpress ω T hstrip hcurl hdivu hsupp hωcont hωderiv hωLI hUax
  -- the decay clause of the datum, from the bundle at `S = T/2`
  have hdecay : ∃ C : ℝ, 0 < C ∧ ∀ x : R3,
      ‖vorticity ((physVel ω) · 0) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1) := by
    obtain ⟨R, ⟨hR0, hsuppR, hbdd, -⟩, -⟩ := hbun (T / 2) ⟨by linarith, by linarith⟩
    obtain ⟨M, hM⟩ := hbdd
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
      (hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) 0)
    refine Work.FTS.Physical.BiotSavart.vorticityDecay_of_support (α := α) (R := R) (M := M)
      hR0.le hM0 ?_ ?_
    · intro x hx
      rw [hcurl 0 ⟨le_rfl, hT⟩ x] at hx
      exact hsuppR 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) x hx
    · intro x
      rw [hcurl 0 ⟨le_rfl, hT⟩ x]
      exact hM 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) x
  refine ⟨physVel ω, hex.choose, hT,
    ⟨hcont1, hex.choose_spec.1, hex.choose_spec.2,
      fun t ht => hdivu t ⟨ht.1.le, ht.2⟩, rfl⟩,
    hdivu 0 ⟨le_rfl, hT⟩, hodd, hcd0, hdecay, hstrip, ?_⟩
  obtain ⟨c, hc, hcl⟩ := hlow
  exact ⟨c, hc, fun t ht => by
    rw [Work.FTS.Physical.vortLInf_physVel_eq hcurl ht]; exact hcl t ht⟩

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are odd in the axial variable `z` *off the axis* `z = 0`
(the hypothesis carriers `z ≠ 0`).  This is the "away from the axis" refinement of
`Work.FTS.MeridianDyn.Odd.meridianResid_odd`, whose hypothesis is global pointwise oddness: for
the applications one only ever knows `W r (-z) t = -W r z t` for `z ≠ 0` (the value at `z = 0` is
an arbitrary junk value of the coordinate chart), and the unconditioned lemma is not applicable
verbatim.

The one new ingredient beyond the sibling file is `deriv_neg_of_odd_ne`: the derivative of a
function that is odd *away from the origin* is even *away from the origin*.  For the derivative at
a point `x ≠ 0` only the germ at `x` matters, and there oddness gives the agreement of `f` with
`-(f ∘ Neg.neg)` on a whole neighbourhood of `x` (which can be taken to avoid `0`), so
`Filter.EventuallyEq.deriv_eq` applies and the chain rule `deriv_comp_neg` finishes.  Global
oddness (hence `deriv_neg_of_odd`) is *not* available here: the value at the origin is unconstrained
and the functions need not satisfy `f 0 = 0`.

The time derivative `∂ₜ`, the radial derivative `∂_r` and the undifferentiated values use only the
pointwise oddness at the *fixed* nonzero axial coordinate, so they need no germ argument; the axial
derivatives `∂_z` are the even ones and are handled by `deriv_neg_of_odd_ne`.

The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, an odd·even / odd·odd
combination of these, hence odd; the factor `1/r` is not differentiated and plays no role beyond
the (harmless) hypothesis `r ≠ 0`.
-/

open scoped Topology

namespace Work.FTS.MeridianDyn.Odd

/-- **The derivative of a function that is odd away from the origin is even away from the
origin**: if `f (-x) = -f x` for every `x ≠ 0`, then `deriv f (-x) = deriv f x` for every
`x ≠ 0`.

No regularity hypothesis is needed: `deriv` is total, so the two sides agree both where `f` is
differentiable (chain rule, `deriv_comp_neg`) and where it is not (both sides are the junk value
`0`, differentiability at `x` and at `-x` being equivalent by oddness).  Since `x ≠ 0`, a
neighbourhood of `x` avoids `0` and on it `f` coincides with `-(f ∘ Neg.neg)`; the derivative only
sees this germ. -/
theorem deriv_neg_of_odd_ne {f : ℝ → ℝ} (hf : ∀ x : ℝ, x ≠ 0 → f (-x) = -f x)
    {x : ℝ} (hx : x ≠ 0) : deriv f (-x) = deriv f x := by
  have hne : (-x) ≠ 0 := neg_ne_zero.mpr hx
  -- near `-x` (which is nonzero) the function `f` agrees with `-(f ∘ Neg.neg)`
  have hev : f =ᶠ[𝓝 (-x)] fun y : ℝ => -f (-y) := by
    filter_upwards [isOpen_ne.mem_nhds hne] with y hy
    exact (by simpa using hf (-y) (by simpa using hy : -y ≠ 0))
  rw [hev.deriv_eq]
  have hcomp : deriv (fun y : ℝ => f (-y)) (-x) = -deriv f x := by
    have h := deriv_comp_neg (f := f) (x := -x)
    simpa using h
  rw [show (fun y : ℝ => -f (-y)) = -(fun y : ℝ => f (-y)) from rfl, deriv.neg, hcomp, neg_neg]


end Work.FTS.MeridianDyn.Odd
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.ResidDyn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-- **The meridian residual of the dynamical ansatz.**  With `Z = ρ(r,z)^p/b(t)`,
`Θ = Θ(r,z)`, amplitude `a`, scale `b` and clock `σ`, and the rates `(1+μ)`, `(1-μ)` of
amplitude and scale together with the clock normalisation `2σ' = a(t)`, the meridian residual is
`a(t)·σ'(t)` times the dynamic profile operator `dynEqLHS` at `(Z,Θ)` with fake-time derivative
`Fτ`:

  `meridianResid (dynVort p a b σ F) (dynPsi p a b σ Φ) r z t
     = a(t)·σ'·(Fτ + (1+μ)F + (1-μ)D_zF + UVR p F Φ)(Z,Θ)`.

The differentiability hypotheses are exactly the joint `C¹` of the two profiles at the point
`(Z,Θ,σ(t))` (`hFc`, `hΦc`) together with the fake-time derivative of `F` along `(Z,Θ)`
(`hFt`). -/
theorem meridianResid_dyn {p : ℝ} {a b σ : ℝ → ℝ} {F Φ : Fam}
    {r z t A' B' sp μa fτ : ℝ}
    (hr : 0 < r) (hbne : b t ≠ 0)
    (ha : HasDerivAt a A' t) (hb : HasDerivAt b B' t) (hσ : HasDerivAt σ sp t)
    (ha' : A' = (1 + μa) * sp * a t) (hb' : B' = -((1 - μa) * sp) * b t)
    (h2s : 2 * sp = a t)
    (hFc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z, σ t))
    (hΦc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Φ q.1 q.2 (σ t))
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z))
    (hFt : HasDerivAt (fun s => F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) s)
      fτ (σ t)) :
    Work.CoreResiduals.meridianResid (dynVort p a b σ F) (dynPsi p a b σ Φ) r z t
      = a t * sp * dynEqLHS p μa (fun Z Θ => F Z Θ (σ t)) (fun Z Θ => Φ Z Θ (σ t))
          (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) fτ := by
  have hρne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  have htan : Real.tan (Work.Cyl.thetaP r z) = z / r := by
    rw [Work.Cyl.thetaP, Real.tan_arctan]
  -- joint differentiability of the two profiles at the point
  have hFd : DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z, σ t) :=
    hFc.differentiableAt (by norm_num)
  -- the `(Z,Θ)`-slices, for the meridian chain rules
  have hF2 : Work.Cyl.DiffAt2 (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) := by
    show DifferentiableAt ℝ
      ((fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
        ∘ fun p : ℝ × ℝ => (p.1, p.2, σ t))
      (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z)
    exact hFd.comp (Work.Cyl.rhoP r z ^ p / b t, Work.Cyl.thetaP r z) (by fun_prop)
  have hΦ2 : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) :=
    hΦc.differentiableAt (by norm_num)
  -- the `(Z,σ)`-slice, for the fake-time chain rule
  have hFs2 : Work.Cyl.DiffAt2 (fun Z s => F Z (Work.Cyl.thetaP r z) s)
      (Work.Cyl.rhoP r z ^ p / b t) (σ t) := by
    show DifferentiableAt ℝ
      ((fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
        ∘ fun p : ℝ × ℝ => (p.1, Work.Cyl.thetaP r z, p.2))
      (Work.Cyl.rhoP r z ^ p / b t, σ t)
    exact hFd.comp (Work.Cyl.rhoP r z ^ p / b t, σ t) (by fun_prop)
  -- the five chain rules
  have htd := Chain.timeDeriv_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) (A' := A') (B' := B') (sp := sp) (fτ := fτ)
    ha hb hσ hbne hFs2 hFt
  have hrd := Chain.pdR_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) hr hbne hF2
  have hzd := Chain.pdZ_dynVort (p := p) (a := a) (b := b) (σ := σ) (F := F)
    (r := r) (z := z) (t := t) hr hbne hF2
  have hrdψ := Chain.pdR_dynPsi (p := p) (a := a) (b := b) (σ := σ) (Φ := Φ)
    (r := r) (z := z) (t := t) hr hbne hΦ2
  have hzdψ := Chain.pdZ_dynPsi (p := p) (a := a) (b := b) (σ := σ) (Φ := Φ)
    (r := r) (z := z) (t := t) hr hbne hΦ2
  -- the algebraic core
  have halg := Algebra.meridianResid_algebra_dyn (p := p) (z := z) (r := r)
    (ρsq := Work.Cyl.rhoP r z ^ 2) (Z := Work.Cyl.rhoP r z ^ p / b t) (a := a t) (sp := sp)
    (κ₁ := 1 + μa) (κ₂ := 1 - μa)
    (f := F (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)) (fτ := fτ)
    (f1 := Work.Cyl.pdR (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (f2 := Work.Cyl.pdZ (fun Z Θ => F Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (g := Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t))
    (g1 := Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (g2 := Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z))
    (ne_of_gt hr) (Work.Cyl.rhoP_sq r z)
  -- the polar expansion of `UVR`
  have hUVR := Work.CoreResiduals.UVR_polar_expand p r z (Work.Cyl.rhoP r z)
    (fun Z Θ => F Z Θ (σ t)) (fun Z Θ => Φ Z Θ (σ t))
    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
    (ne_of_gt hr) hρne (Work.Cyl.sin_thetaP hr z) (Work.Cyl.cos_thetaP hr z) htan
  -- the final assembly: substitute the chain rules, the polar expansion of `UVR` and the
  -- normalisations `ρ² = r²+z²` and `2σ' = a(t)`, then clear denominators and compare.
  unfold Work.CoreResiduals.meridianResid
  rw [htd, hrd, hzd, hrdψ, hzdψ]
  rw [dynVort_apply, dynPsi_apply]
  rw [ha', hb']
  rw [dynEqLHS_apply, hUVR]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Cyl.pdR]
  rw [Work.Cyl.rhoP_sq r z]
  rw [← h2s]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hρne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.FTS.MeridianDyn
end
end
