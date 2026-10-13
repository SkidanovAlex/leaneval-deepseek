/-
Copyright: work module for the Elgindi finite-time singularity project.

# `SlotT2/Basic`: the canonical slot weight and its elementary estimates

The per-slot statement `Work.FTS.TransportS.T2Slot` bounds the pairing

  `slotPairing ρ a b (fun z θ => f z θ * D_z g z θ) g`

for the *leaf* weights `ρ` of the coercive pairing.  Every leaf weight is pointwise (a.e.)
dominated by the canonical weight `canonW q z θ = w(z)² sin(2θ)^{-q}` with `q = η` for the
`D_z`-only slots (`a = 0`) and `q = γ` for the slots carrying a `θ`-derivative (`a ≥ 1`).

This module provides `canonW`, the exponent monotonicity `rpow_neg_mono` (which is what makes
the comparison with the `ℋ⁴`-integrand summands work), the two pointwise slot dominations,
the resulting bounds on the iterated integrals `∫_z∫_θ canonW q · G²` by `HkSq α 4 g`, and the
`θ`-slice integrability / joint measurability of the canonical slot integrands.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.H2.HeasyBlocksId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The canonical slot weight -/

/-- The canonical weight of a slot of the flat pairing: `w(z)² sin(2θ)^{-q}`. -/
def canonW (q : ℝ) (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

theorem canonW_nonneg {q z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ canonW q z θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- At `z = 0` the radial weight vanishes, hence so does `canonW`. -/
theorem canonW_zero_z (q θ : ℝ) : canonW q 0 θ = 0 := by
  simp [canonW, Work.Spaces.w]

/-- `canonW η z θ = Whz z θ ^ 2` on `Iθ`. -/
theorem canonW_eta_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW Work.Spaces.eta z θ = (Work.FTS.H2.Whz z θ) ^ 2 :=
  (Work.FTS.H2.hbi_Whz_sq z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)).symm

/-- `canonW (gam α) z θ = Wt α z θ ^ 2` on `Iθ`. -/
theorem canonW_gam_eq (α z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
  (Work.FTS.H2.hbi_Wm_sq α z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)).symm

/-- For `σ ∈ [0,1]` and `0 < q ≤ q'` the decreasing-exponent estimate `σ^{-q} ≤ σ^{-q'}`. -/
theorem rpow_neg_mono {σ q q' : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hq : 0 < q) (hqq : q ≤ q') :
    σ ^ (-q) ≤ σ ^ (-q') := by
  rcases eq_or_lt_of_le hσ0 with h0 | h0
  · subst h0
    have h1 : (-q : ℝ) ≠ 0 := by linarith
    have h2 : (-q' : ℝ) ≠ 0 := by linarith
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
  · exact Real.rpow_le_rpow_of_exponent_ge h0 hσ1 (by linarith)

/-- `canonW` is monotone in the exponent. -/
theorem canonW_mono {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : canonW q z θ ≤ canonW q' z θ :=
  mul_le_mul_of_nonneg_left
    (rpow_neg_mono (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) (Real.sin_le_one _) hq hqq)
    (sq_nonneg _)

/-! ## Pointwise domination of the canonical slot weights by the summands of `HkIntegrand` -/

/-- For `0 < q ≤ η` the pure-`D_z` slot weight `canonW q` is dominated by the `j`-th summand
weight of `HkIntegrand α 4`. -/
theorem canonW_mul_z_le (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 4) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ j hj

/-- For `0 < q ≤ γ` the mixed slot weight `canonW q` is dominated by the `(i,j)` summand
weight of `HkIntegrand α 4`. -/
theorem canonW_mul_mixed_le (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij

/-! ## Monotonicity lemmas for the two iterated integrals -/

theorem integral_Iθ_mono {f g : ℝ → ℝ} (h : ∀ θ ∈ Work.Spaces.Iθ, f θ ≤ g θ)
    (h0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) (hg : IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ :=
  MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h0) hg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc h)

theorem integral_Iz_mono {f g : ℝ → ℝ} (h : ∀ z ∈ Work.Spaces.Iz, f z ≤ g z)
    (h0 : ∀ z ∈ Work.Spaces.Iz, 0 ≤ f z) (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z :=
  MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici h0) hg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici h)

/-! ## Continuity / measurability of the canonical slot integrands -/

theorem continuousOn_canonW (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simp only [Work.Spaces.w]
    exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt ?_)
    apply Real.sin_pos_of_pos_of_lt_pi
    · show (0 : ℝ) < 2 * p.2; linarith [hp.2.1]
    · show 2 * p.2 < Real.pi; linarith [hp.2.2, Real.pi_pos]
  exact h1.mul h2

/-- Joint a.e. strong measurability of the pure-`D_z` canonical slot integrand. -/
theorem zslot_joint_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.DzIter j g p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.DzIter j).continuousOn.pow 2))

/-- Joint a.e. strong measurability of the mixed canonical slot integrand. -/
theorem mslot_joint_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.mixed j i g p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.mixed j i).continuousOn.pow 2))

/-- A.e. strong measurability of the pure-`D_z` canonical slot integrand on a `θ`-slice. -/
theorem zslot_slice_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.DzIter j).continuousOn.pow 2)) hz

/-- A.e. strong measurability of the mixed canonical slot integrand on a `θ`-slice. -/
theorem mslot_slice_aesm {q : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    ((continuousOn_canonW q).mul ((hg.mixed j i).continuousOn.pow 2)) hz

/-! ## Slot integrability -/

theorem zslot_slice_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ)
    (hj : j ≤ 4) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.DzIter j g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    exact integrableOn_zero
  · refine Integrable.mono' (hmem.1 z hz) (zslot_slice_aesm hg j hz0) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))]
    exact canonW_mul_z_le α g hq0 hq hz0 hθ j hj

theorem mslot_slice_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    exact integrableOn_zero
  · refine Integrable.mono' (hmem.1 z hz) (mslot_slice_aesm hg j i hz0) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))]
    exact canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij

/-! ## The iterated `ℋ⁴`-bounds -/

/-- **The pure-`D_z` slot energy.**  For `0 < q ≤ η`, `j ≤ 4` and `g ∈ ℋ⁴`,
`∫_z∫_θ w² sin(2θ)^{-q} (D_z^j g)² ≤ HkSq α 4 g`. -/
theorem canonW_z_iterated_le (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ) (hj : j ≤ 4) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 g := by
  rw [Work.Spaces.HkSq]
  refine integral_Iz_mono (fun z hz => ?_) (fun z hz => ?_) hmem.2
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * (Work.Spaces.DzIter j g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z, zero_mul]]
      rw [MeasureTheory.integral_zero]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
    · exact integral_Iθ_mono (fun θ hθ => canonW_mul_z_le α g hq0 hq hz0 hθ j hj)
        (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))

/-- **The mixed slot energy.**  For `0 < q ≤ γ`, `1 ≤ i`, `i + j ≤ 4` and `g ∈ ℋ⁴`,
`∫_z∫_θ w² sin(2θ)^{-q} (D_z^j D_θ^i g)² ≤ HkSq α 4 g`. -/
theorem canonW_mixed_iterated_le (α : ℝ) {q : ℝ} (hq : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      ≤ Work.Spaces.HkSq α 4 g := by
  rw [Work.Spaces.HkSq]
  refine integral_Iz_mono (fun z hz => ?_) (fun z hz => ?_) hmem.2
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z, zero_mul]]
      rw [MeasureTheory.integral_zero]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
    · exact integral_Iθ_mono (fun θ hθ => canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij)
        (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)
  · exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))

/-- The marginal of the pure-`D_z` slot is a.e. strongly measurable. -/
theorem zslot_marginal_aesm {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (j : ℕ) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right' (zslot_joint_aesm hg j)

/-- The marginal of the mixed slot is a.e. strongly measurable. -/
theorem mslot_marginal_aesm {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (j i : ℕ) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
  MeasureTheory.AEStronglyMeasurable.integral_prod_right' (mslot_joint_aesm hg j i)

/-- The marginal of the pure-`D_z` slot is integrable. -/
theorem zslot_marginal_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ) (hj : j ≤ 4) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2) Work.Spaces.Iz := by
  refine Integrable.mono' hmem.2 (zslot_marginal_aesm hg j) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  rw [Real.norm_of_nonneg hnn]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.DzIter j g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    rw [MeasureTheory.integral_zero]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
  · exact integral_Iθ_mono (fun θ hθ => canonW_mul_z_le α g hq0 hq hz0 hθ j hj)
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)

/-- The marginal of the mixed slot is integrable. -/
theorem mslot_marginal_integrable {α q : ℝ} {g : ℝ → ℝ → ℝ} (hq : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) Work.Spaces.Iz := by
  refine Integrable.mono' hmem.2 (mslot_marginal_aesm hg j i) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  rw [Real.norm_of_nonneg hnn]
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ => canonW q 0 θ * (Work.Spaces.mixed j i g 0 θ) ^ 2) = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    rw [MeasureTheory.integral_zero]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
  · exact integral_Iθ_mono (fun θ hθ => canonW_mul_mixed_le α g hq hqγ hz0 hθ j i hi hij)
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)

end Work.FTS.TransportS.SlotT2
