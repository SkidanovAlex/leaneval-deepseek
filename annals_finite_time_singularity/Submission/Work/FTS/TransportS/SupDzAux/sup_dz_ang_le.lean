import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.H2.HkSqSwap
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Blocks.alphaDz_pth_core_clean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SupDzAux

/-
The uniform-in-`z` bound for the *weighted angular* integral of `∂_θ(D_z^b f)` of an open-class
`ℋ⁴` datum.  This is the second of the two inputs of `Work.FTS.TransportS.sup_dz_le_hk`
(together with `Work.FTS.TransportS.SupDzAux.sup_dz_avg_le`).

ROUTE (the same scheme as `sup_dz_avg_le`, with the angular weight `sin(2θ)^{2-γ}` kept):
1. Apply `Work.FTS.TransportS.half_line_window_bound` slicewise in `σ` to
   `h := fun x => Work.Spaces.pth (Work.Spaces.DzIter b f) x σ`,
   `h' := fun x => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ`.
   The relevant quantity is `x * h' x = ∂_θ(D_z^{b+1} f)(x, σ)`: the `z`-derivative of
   `D_z^bf` is `D_z^{b+1}f = z ∂_z(D_z^b f)`, and `∂_z` commutes with `∂_θ` on the open
   quadrant (`Work.Blocks.pth_DzIter_eqOn_Q0`, `pth_Dz_apply`, or Clairaut for smooth functions).
   Hypotheses: `HasDerivAt` from inspecting the slices of `pth (DzIter b f)`
   (`SmoothOpen.pth` gives `SmoothOpen (pth (DzIter b f))`, then use its `hasDerivAt_slice`),
   continuity from `curry_θ`/`curry_z` at `(x,σ)` with `x > 0`, `0 < σ < π/2`, and the
   integrability of `h²` from the domination below.
2. Multiply the window inequality by `(Real.sin (2*σ)) ^ (2 - Work.Spaces.gam α) ≥ 0` and
   integrate in `σ ∈ Iθ`.  The two resulting double integrals are dominated by `HkSq`:
   * `(∂_θ(D_z^{b+1}f))² w² sin(2σ)^{2-γ} = (mixed (b+1) 1 f)² w² sin(2σ)^{-γ}`
     `= ((mixed (b+1) 1 f) * Work.Spaces.Wt α)² ≤ HkIntegrand α 4 f`
     (`Work.Spaces.sq_le_HkIntegrand_mixed`, needs `(b+1) + 1 ≤ 4`, i.e. `b ≤ 2`);
     the identity uses `mixed j 1 = sin(2σ) · D_z^j(∂_θf)`, i.e. that `∂_θ` commutes with the
     `D_z`-iterates on the open quadrant (`Work.Blocks.pth_DzIter_eqOn_Q0`) and that `sin(2σ)`
     is constant in `z`;
   * `(∂_θ(D_z^bf))² sin(2σ)^{2-γ} = (mixed b 1 f)² sin(2σ)^{-γ} ≤ ((mixed b 1 f) * Wt α)²`
     `≤ HkIntegrand α 4 f`, using `1 ≤ w` on `z > 0` (`Work.FTS.TransportS.one_le_w`).
3. The a.e. `σ`-slice integrability input is `Work.FTS.H2.swap_iterated_integral_of_nonneg`
   (Tonelli) with the a.e. strong measurability from `Work.Spaces.aesm_of_continuousOn_Qd`
   and `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`.
4. Let `R₀ → ∞` exactly as in `sup_dz_avg_le`; `C = 3` works.

The five ingredients of the scheme are isolated in the sibling module `SdaAux.lean`
(`sda_DzIter_const_mul_th`, `sda_mixed_one_eq_sin_pth`, `sda_ang_slice_le`, `sda_ang_slice_le_w`,
`sda_HkSqSwap_open`, the last being the `SmoothOpen`-version of `Work.FTS.H2.HkSqSwap`).
-/
theorem sup_dz_ang_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → b ≤ 2 →
      ∀ z : ℝ, 0 < z →
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f b hα hα1 hF hmem hb z hz
  obtain ⟨hswap, hGint, hGslice⟩ := sda_HkSqSwap_open α f hF hmem
  have hHknn : 0 ≤ Work.Spaces.HkSq α 4 f := by
    rw [Work.Spaces.HkSq]
    exact integral_nonneg fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π/2)] with σ h
    exact fun hmem => h.mpr hmem
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π/2) →
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz →
        (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 ≤ Real.sin (2 * σ) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1])
          (by linarith [hσ.2, Real.pi_pos]))
      have hlamnn : 0 ≤ (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
        Real.rpow_nonneg hsinσ _
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.pth (Work.Spaces.DzIter b f) x σ)
            (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ) x :=
        fun x hx => ((hF.DzIter b).pth).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.pth (Work.Spaces.DzIter b f) x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        (((hF.DzIter b).pth).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn
          (fun x : ℝ => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ)
          (Set.Icc z (2 * R₀)) :=
        ((((hF.DzIter b).pth).pz).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : IntegrableOn
          (fun x : ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2)
          (Set.Icc R₀ (2 * R₀)) :=
        ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.pth (Work.Spaces.DzIter b f) x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ)
        hz hR hderiv hcont hcont' hint
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
            * Work.Spaces.w x) (Set.Icc z (2 * R₀)) := by
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
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                * Work.Spaces.w x) ^ 2) volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                * Work.Spaces.w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact ContinuousOn.mul continuousOn_const (hcontW.pow 2)
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2)
            (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                * Work.Spaces.w x) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have hcomm : x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
            = Work.Spaces.pth (Work.Spaces.DzIter (b + 1) f) x σ := by
          show Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
            = Work.Spaces.pth (Work.Spaces.DzIter (b + 1) f) x σ
          exact (Work.Blocks.pth_Dz_apply (g := Work.Spaces.DzIter b f)
            (Work.Blocks.SmoothOpen.DzIter_contDiffAt_two hF b hx0 hσ.1 hσ.2)).symm
        rw [hcomm]
        exact sda_ang_slice_le_w hα hα1 hF hb hx0 hσ
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ :=
        fun x hx => sda_ang_slice_le hα hα1 hF hb (lt_of_lt_of_le hRpos hx.1) hσ
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Filter.Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hAeq : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                * Work.Spaces.w x) ^ 2)
          = ∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
              * (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                  * Work.Spaces.w x) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hBeq : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2)
          = ∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
          = (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2 := by ring
        _ ≤ (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
              * (2 * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                      * Work.Spaces.w x) ^ 2)
                + (2 / R₀) * ∫ x in R₀..(2 * R₀),
                    (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2) :=
              mul_le_mul_of_nonneg_left hwin hlamnn
        _ = 2 * ((Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
                * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                      * Work.Spaces.w x) ^ 2))
              + (2 / R₀) * ((Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
                * (∫ x in R₀..(2 * R₀),
                    (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2)) := by ring
        _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
                * (x * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter b f)) x σ
                    * Work.Spaces.w x) ^ 2)
              + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
                  * (Work.Spaces.pth (Work.Spaces.DzIter b f) x σ) ^ 2) := by
              rw [hAeq, hBeq]
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
              + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by ring
    have hle : (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hfae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩) _)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          integral_mono_of_nonneg hfae (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  rcases eq_or_lt_of_le hHknn with h0 | hpos
  · have h1 := hbound z le_rfl
    rw [← h0, mul_zero] at h1 ⊢
    exact h1
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    let R₀ : ℝ := max z (2 * Work.Spaces.HkSq α 4 f / ε)
    have hR : z ≤ R₀ := le_max_left _ _
    have hbnd := hbound R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hεH : (2 / R₀) * Work.Spaces.HkSq α 4 f ≤ ε := by
      have h2 : 2 * Work.Spaces.HkSq α 4 f / ε ≤ R₀ := le_max_right _ _
      have h3 : 2 * Work.Spaces.HkSq α 4 f ≤ R₀ * ε := by
        have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt hε)
        rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at h4
      rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
      linarith
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ 2 * Work.Spaces.HkSq α 4 f + ε := by
          refine le_trans hbnd ?_
          rw [show (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f
              = 2 * Work.Spaces.HkSq α 4 f + (2 / R₀) * Work.Spaces.HkSq α 4 f from by ring]
          linarith
      _ ≤ 3 * Work.Spaces.HkSq α 4 f + ε := by linarith

end Work.FTS.TransportS.SupDzAux
