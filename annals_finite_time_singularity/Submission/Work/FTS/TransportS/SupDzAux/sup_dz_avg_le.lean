import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-
The uniform-in-`z` bound for the angular average of the pure `D_z`-derivatives of an open-class
`ℋ⁴` datum.  This is one of the two inputs of `Work.FTS.TransportS.sup_dz_le_hk`.

ROUTE (all ingredients are proved in the workspace):
1. `Work.FTS.TransportS.half_line_window_bound`
   (`Submission/Work/FTS/TransportS/SupDzAux/HalfLineWindow.lean`), applied slicewise in the
   angle `σ` to `h := fun x => Work.Spaces.DzIter b f x σ`, with
   `h' := fun x => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ`;
   note `x * h' x = Work.Spaces.DzIter (b+1) f x σ` (by `rfl`, `Work.Spaces.DzIter_succ`).
   Hypotheses of the window lemma, at the fixed angle `σ ∈ (0, π/2)`, a fixed `z > 0` and
   `R₀ ≥ z`:
   * `HasDerivAt` on `[z, 2R₀]`: `Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice_DzIter`;
   * continuity of `h` and of `h'` on those intervals: `SmoothOpen.curry_z`;
   * integrability of `h²` on `[R₀, 2R₀]`: from the continuity of the slice on the compact
     interval `ContinuousOn.integrableOn_Icc`.
2. Pointwise domination on the open quadrant (`z > 0`, `0 < σ < π/2`):
   `(DzIter j f x σ)² * (w x)² ≤ HkIntegrand α 4 f x σ` for `j ≤ 4` is
   `Work.FTS.H2.dzIter_sq_w_le_HkIntegrand`; since `w ≥ 1` on `x > 0` this also gives
   `(DzIter j f x σ)² ≤ HkIntegrand α 4 f x σ` (`avgDzIter_sq_le` below).
3. For almost every `σ ∈ Iθ`, the σ-slice `x ↦ HkIntegrand α 4 f x σ` is integrable on
   `Work.Spaces.Iz`: Tonelli `Work.FTS.H2.swap_iterated_integral_of_nonneg` with the a.e.
   strong measurability supplied by `Work.Spaces.aesm_of_continuousOn_Qd` and
   `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, and the two `HkMem` fields
   (`hmem.1`, `hmem.2`).  It also gives `∫_σ ∫_z HkIntegrand α 4 f = HkSq α 4 f`
   (`avgHkSqSwap` below).
4. Assemble: for a.e. `σ`, `h(z)² ≤ (2 + 2/R₀) * ∫_{x ∈ Iz} HkIntegrand α 4 f x σ`;
   integrate this a.e. inequality in `σ` over `Iθ` (both sides are integrable: the LHS by
   `hmem.1 z ⟨hz.le⟩` plus domination, the RHS by item 3) to get
   `∫_θ (DzIter b f z θ)² ≤ (2 + 2/R₀) * HkSq α 4 f` for every `R₀ ≥ z`; the choice
   `R₀ = max z 2` makes `2 + 2/R₀ ≤ 3`, so `C = 3` works.
-/

/-! ## Two auxiliary lemmas -/

/-- On the open quadrant, `(D_z^j f z θ)² ≤ HkIntegrand α 4 f z θ` for `j ≤ 4`: the plain
`D_z`-slot bound `dzIter_sq_w_le_HkIntegrand`, divided by `w² ≥ 1` at `z > 0`. -/
theorem avgDzIter_sq_le (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) (j : ℕ) (hj : j ≤ 4) :
    (Work.Spaces.DzIter j f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have h := Work.FTS.H2.dzIter_sq_w_le_HkIntegrand (z := z) (θ := θ) α f hsin j hj
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  calc (Work.Spaces.DzIter j f z θ) ^ 2
      = (Work.Spaces.DzIter j f z θ) ^ 2 * 1 := by ring
    _ ≤ (Work.Spaces.DzIter j f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := h

/-- **Tonelli for the `ℋ⁴`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α 4 f`, the iterated integral of `HkIntegrand α 4 f` in the order
`∫_θ ∫_z` equals `HkSq α 4 f`, its partially integrated function is integrable on the angles, and
for almost every angle the radial slice is integrable.  (The `SmoothOpen`-version of
`Work.FTS.H2.HkSqSwap`, whose hypothesis is the stronger, analytic `SmoothNbhd`.) -/
theorem avgHkSqSwap (α : ℝ) (f : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 4)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  exact ⟨by rw [Work.Spaces.HkSq]; exact h1, h2, h3⟩

/-! ## The main estimate -/

theorem sup_dz_avg_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → b ≤ 2 →
      ∀ z : ℝ, 0 < z →
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f b hα hα1 hF hmem hb z hz
  obtain ⟨hswap, hGint, hGslice⟩ := avgHkSqSwap α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π/2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π/2) →
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz →
        (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.DzIter b f x σ)
            (Work.Spaces.pz (Work.Spaces.DzIter b f) x σ) x :=
        fun x hx => hF.hasDerivAt_slice_DzIter b hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.DzIter b f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.DzIter b).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn (fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.DzIter b).pz).curry_z hσ).continuousOn.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : MeasureTheory.IntegrableOn
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.DzIter b f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.DzIter b f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the two relevant slices on the window intervals
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            * Work.Spaces.w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hcontW.pow 2
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Work.Spaces.DzIter b f x σ) ^ 2)
            (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hcont.pow 2
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- pointwise domination of the two window integrands
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hcomm : x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
            = Work.Spaces.DzIter (b + 1) f x σ := rfl
        rw [hcomm, mul_pow]
        exact Work.FTS.H2.dzIter_sq_w_le_HkIntegrand (z := x) (θ := σ) α f hsinσ (b + 1)
          (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Work.Spaces.DzIter b f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ :=
        fun x hx => avgDzIter_sq_le α f (lt_of_lt_of_le hRpos hx.1) hsinσ b (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      calc (Work.Spaces.DzIter b f z σ) ^ 2
          ≤ 2 * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.DzIter b f) x σ
              * Work.Spaces.w x) ^ 2)
            + (2 / R₀) * ∫ x in R₀..(2 * R₀), (Work.Spaces.DzIter b f x σ) ^ 2 := hwin
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
            + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
              (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α 4 f s σ) := by ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine MeasureTheory.Integrable.mono' (hmem.1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz))
        ?_ ?_
      · exact (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
          ((hF.DzIter b).continuousOn) hz).pow 2
      · filter_upwards [Work.FTS.H2.ae_sin_two_pos] with σ hsin
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact avgDzIter_sq_le α f hz hsin b (by omega)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          MeasureTheory.integral_mono_ae hLI (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end Work.FTS.TransportS.SupDzAux
