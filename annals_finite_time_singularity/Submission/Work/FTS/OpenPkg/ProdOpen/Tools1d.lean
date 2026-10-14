import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The planar Lebesgue measure restricted to a box is the product of the restrictions of
the Lebesgue measure to the two sides. -/
theorem volume_restrict_box (a b : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ) :=
  (Measure.prod_restrict (Set.Icc a b) Work.Spaces.Iθ).symm

/-- **Box integrability from the angular slices.**  If `g` is continuous on the open quadrant,
nonnegative on the box `[a,b] ×ˢ Iθ` (`0 < a`), has integrable angular slices and an integrable
iterated `θ`-integral over `[a,b]`, then its uncurried version is integrable on the box.

This is the `0 < a`-form of `integrableOn_box_of_slice`, with nonnegativity required only on
the box (which is what the weighted integrands of the elliptic estimates satisfy: the
`sin(2θ)^{-η}` factor is only nonnegative for `θ ∈ Iθ`). -/
theorem integrableOn_box_of_slice_of_nonneg {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Q0)
    (hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ g z θ)
    (hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ))
    (hint : Integrable (fun s => ∫ θ in Work.Spaces.Iθ, g s θ)
      (volume.restrict (Set.Icc a b))) :
    IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- Strong measurability on the box, from continuity on the open quadrant.
  have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
    Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  have hAE : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg).mono_measure hle
  -- Nonnegativity on the box, in the a.e. form needed for the product integral.
  have hnn' : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      ∀ᵐ y ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ g x y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    filter_upwards [ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with y hy
    exact hnn x hx y hy
  have hsl' : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Integrable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hsl s hs
  -- Fubini for the product measure, then the identification of the restricted planar
  -- measure on the box with that product.
  have hbox : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.integrable_prod_ae hnn' hAE hsl' hint
  show Integrable (Function.uncurry g) (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ))
  rw [volume_restrict_box]
  exact hbox

theorem boxIntegrable_DzIter (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_z D_z^j F` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((hF.DzIter j).pz.continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j F) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the `i = j+1` slot of the `ℋ^k`-integrand.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmem.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact le_trans (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hθ)
        (Work.Spaces.sq_le_HkIntegrand_z α k F s θ (j + 1) hj)
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α k F`, whose `z`-integral is finite by `hmem`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F s θ) (volume.restrict (Set.Icc a b)) :=
      hmem.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc a b))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc a b) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact le_trans (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hθ)
          (Work.Spaces.sq_le_HkIntegrand_z α k F s θ (j + 1) hj)
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.moment_relation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option maxHeartbeats 800000

/-! ## Elementary facts about the weight `η` and the angular kernel `sinθcos²θ` -/

private theorem eta_pos : 0 < Work.Spaces.eta := by
  rw [Work.Spaces.eta]
  norm_num

private theorem sinCos2_zero : Work.Elliptic.sinCos2 0 = 0 := by
  rw [Work.Elliptic.sinCos2]
  norm_num

private theorem sinCos2_pi_div_two : Work.Elliptic.sinCos2 (π / 2) = 0 := by
  rw [Work.Elliptic.sinCos2, Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

/-! ## Integrability of `∂_z u · sinθcos²θ` on a bounded box

The weighted square `(∂_z u)² · sin(2θ)^{-η}` dominates `|∂_z u · sinθcos²θ|` on the open
quadrant (`|sinθcos²θ| ≤ 1` and `sin(2θ)^{-η} ≥ 1` there), so the domination hypothesis
`hbox` gives integrability of the product. -/

theorem integrableOn_pz_mul_sinCos2 (u : ℝ → ℝ → ℝ) (hu : SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
      Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  set box : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Work.Spaces.Iθ with hboxdef
  set S : Set (ℝ × ℝ) := box ∩ Q0 with hSdef
  -- ## measurability and finiteness of the box
  have hSmeas : MeasurableSet S := by
    rw [hSdef, hboxdef, Q0]
    exact (measurableSet_Icc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)).inter
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hboxfin : (volume : Measure (ℝ × ℝ)) box ≠ ⊤ := by
    rw [hboxdef, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Work.Spaces.Iθ,
      Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hSfin : (volume : Measure (ℝ × ℝ)) S ≠ ⊤ :=
    ne_top_of_le_ne_top hboxfin (measure_mono (by rw [hSdef]; exact Set.inter_subset_left))
  -- ## the dominating function
  have hg : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) box := by
    have h := hbox a b ha hab
    rw [MeasureTheory.IntegrableOn] at h ⊢
    simpa only [Function.uncurry_def] using h
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))) S := by
    have hmono : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) S :=
      hg.mono_set (by rw [hSdef]; exact Set.inter_subset_left)
    exact MeasureTheory.Integrable.const_mul hmono (1 / 2)
  have h2 : IntegrableOn (fun _ : ℝ × ℝ => (1 / 2 : ℝ)) S :=
    MeasureTheory.integrableOn_const (C := (1 / 2 : ℝ)) hSfin
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2) S :=
    MeasureTheory.IntegrableOn.add h1 h2
  -- ## continuity of the integrand on `S`
  have hsinCos2_cont : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2 := rfl
    rw [hfun]
    exact (Real.continuous_sin.comp continuous_snd).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)
  have hsinOn : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) Q0 :=
    hsinCos2_cont.continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) S :=
    ((hu.pz).continuousOn.mono (by rw [hSdef]; exact Set.inter_subset_right)).mul
      (hsinOn.mono (by rw [hSdef]; exact Set.inter_subset_right))
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) (volume.restrict S) :=
    hcont.aestronglyMeasurable hSmeas
  -- ## the pointwise domination
  have hbound : ∀ᵐ p ∂(volume.restrict S),
      ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with p hp
    have hQ : p ∈ Q0 := hp.2
    rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hQ
    have hspos : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hQ.2.1]) (by linarith [hQ.2.2, Real.pi_pos])
    have hsle : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hpow1 : 1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hspos hsle (by linarith [eta_pos])
    have hsq : (Work.Spaces.pz u p.1 p.2) ^ 2 ≤ (Work.Spaces.pz u p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
      calc (Work.Spaces.pz u p.1 p.2) ^ 2 = (Work.Spaces.pz u p.1 p.2) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.pz u p.1 p.2) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left hpow1 (sq_nonneg _)
    have hsincos : |Work.Elliptic.sinCos2 p.2| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
      calc |Real.sin p.2| * |Real.cos p.2| ^ 2 ≤ 1 * 1 :=
            mul_le_mul (Real.abs_sin_le_one p.2)
              (by nlinarith [Real.abs_cos_le_one p.2, abs_nonneg (Real.cos p.2)])
              (by positivity) (by norm_num)
        _ = 1 := by ring
    calc ‖Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2‖
        = |Work.Spaces.pz u p.1 p.2| * |Work.Elliptic.sinCos2 p.2| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |Work.Spaces.pz u p.1 p.2| * 1 := mul_le_mul_of_nonneg_left hsincos (abs_nonneg _)
      _ = |Work.Spaces.pz u p.1 p.2| := mul_one _
      _ ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2 + 1) := by
          nlinarith [sq_abs (Work.Spaces.pz u p.1 p.2),
            sq_nonneg (|Work.Spaces.pz u p.1 p.2| - 1)]
      _ ≤ (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) + 1) := by linarith
      _ = (1 / 2) * ((Work.Spaces.pz u p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) + 1 / 2 := by ring
  -- ## the box differs from `S` by a null set
  have hnull : (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({(0 : ℝ), π / 2} : Set ℝ)) = 0 := by
    have hN : (volume : Measure ℝ) ({(0 : ℝ), π / 2} : Set ℝ) = 0 :=
      Set.Finite.measure_zero (by simp) volume
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, hN, mul_zero]
  have hae : box =ᵐ[(volume : Measure (ℝ × ℝ))] S := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    apply propext
    rw [hSdef]
    refine ⟨?_, ?_⟩
    · intro hpbox
      rw [hboxdef, Work.Spaces.Iθ] at hpbox
      refine ⟨hpbox, ?_⟩
      have hp1 : 0 < p.1 := lt_of_lt_of_le ha hpbox.1.1
      have hp2 : 0 < p.2 := by
        rcases lt_or_eq_of_le hpbox.2.1 with h | h
        · exact h
        · exact absurd ⟨Set.mem_univ _, by simp [h]⟩ hp
      have hp3 : p.2 < π / 2 := by
        rcases lt_or_eq_of_le hpbox.2.2 with h | h
        · exact h
        · exact absurd ⟨Set.mem_univ _, by simp [h]⟩ hp
      rw [Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hp1, hp2, hp3⟩
    · intro hpS
      exact hpS.1
  -- ## conclusion
  have hFint : IntegrableOn (fun p : ℝ × ℝ =>
      Work.Spaces.pz u p.1 p.2 * Work.Elliptic.sinCos2 p.2) S :=
    MeasureTheory.Integrable.mono' hdom hmeas hbound
  have hres := MeasureTheory.IntegrableOn.congr_set_ae hFint hae
  simpa only [Function.uncurry_def] using hres

/-! ## The fundamental theorem of calculus for the `z`-slice

For every interior angle `θ ∈ (0,π/2)` the slice `z ↦ u z θ` is differentiable on `(0,∞)` with
derivative `pz u · θ`, so on `[a,b]` (with `0 < a < b`) the fundamental theorem of calculus
applies; at the two boundary angles `sinθcos²θ` vanishes. -/

theorem ae_integral_slice_eq (u : ℝ → ℝ → ℝ) (hu : SmoothOpen u)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (fun θ : ℝ => ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
    (fun θ : ℝ => (u b θ - u a θ) * Work.Elliptic.sinCos2 θ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  filter_upwards [MeasureTheory.ae_restrict_mem hIθ] with θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · -- interior angle: the fundamental theorem of calculus
      have hIoo : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h2⟩
      have hderiv : ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun z : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
            (Work.Spaces.pz u x θ * Work.Elliptic.sinCos2 θ) x := by
        intro x hx
        rw [Set.uIcc_of_le hab.le] at hx
        exact (hu.hasDerivAt_slice hIoo (lt_of_lt_of_le ha hx.1)).mul_const _
      have hcont : ContinuousOn (fun s : ℝ =>
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab.le]
        exact (((hu.pz).curry_z hIoo).continuousOn.mono
          (fun x hx => lt_of_lt_of_le ha hx.1)).mul continuousOn_const
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
      rw [intervalIntegral.integral_of_le hab.le] at h
      have hIocIcc : (∫ s in Set.Ioc a b,
            Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
          = ∫ s in Set.Icc a b, Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ :=
        setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
      rw [← hIocIcc, h]
      ring
    · -- right endpoint: `sinθcos²θ = 0`
      rw [h2, sinCos2_pi_div_two]
      simp
  · -- left endpoint: `sinθcos²θ = 0`
    rw [← h0, sinCos2_zero]
    simp

/-! ## The angular moment relation -/

theorem moment_relation (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz u s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Work.Elliptic.Fstar u b = Work.Elliptic.Fstar u a
      + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
  have hb : 0 < b := lt_trans ha hab
  -- ## Fubini for the box `[a,b] × Iθ`
  have hInt : Integrable (Function.uncurry (fun s θ : ℝ =>
      Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h := integrableOn_pz_mul_sinCos2 u hu hbox ha hab
    rw [MeasureTheory.IntegrableOn, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at h
    exact h
  have hswap : (∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc a b,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_integral_swap hInt
  -- ## the inner integral on the angular slices
  have hstep : (∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc a b,
        Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_congr_ae (ae_integral_slice_eq u hu ha hab)
  -- ## the angular moment of the difference
  have hsplit : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
      = Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a := by
    have h1 : (∫ θ in Work.Spaces.Iθ, (u b θ - u a θ) * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ,
          (u b θ * Work.Elliptic.sinCos2 θ - u a θ * Work.Elliptic.sinCos2 θ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
      MeasureTheory.integral_sub (hsl b hb) (hsl a ha)]
  have hmain : Work.Elliptic.Fstar u b - Work.Elliptic.Fstar u a
      = ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz u s θ * Work.Elliptic.sinCos2 θ) := by
    rw [← hsplit, ← hstep, ← hswap]
  rw [← hmain]
  ring

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-! ## Elementary facts on the radial weight -/

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < w z := by
  rw [w]
  positivity

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : (1 : ℝ) ≤ w z := by
  have h2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [w, le_div_iff₀ h2]
  nlinarith [sq_nonneg z]

theorem w_mul_psi_eq' {h' : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    (x * h' x * w x) * (x / (1 + x) ^ 2) = h' x := by
  have h1 : (1 + x) ≠ 0 := ne_of_gt (by linarith)
  have h2 : x ≠ 0 := ne_of_gt hx
  simp only [w]
  field_simp

/-! ## A minimiser of a continuous nonnegative function is at most its mean -/

theorem exists_min_le_mean {φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn φ (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, φ x ≤ (b - a)⁻¹ * ∫ t in a..b, φ t := by
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    ⟨a, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hab.le⟩⟩ hcont
  refine ⟨x₀, hx₀, ?_⟩
  have hint : IntervalIntegrable φ volume a b :=
    (show ContinuousOn φ (Set.uIcc a b) by rwa [Set.uIcc_of_le hab.le]).intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => φ x₀) volume a b := intervalIntegrable_const
  have hmono : ∫ t in a..b, φ x₀ ≤ ∫ t in a..b, φ t :=
    intervalIntegral.integral_mono_on hab.le hconst hint (fun t ht => hmin ht)
  have hval : ∫ t in a..b, φ x₀ = φ x₀ * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hval] at hmono
  have hpos : 0 < b - a := sub_pos.mpr hab
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [hmono]

/-! ## The radial Hardy inequality with a fixed window -/

/-- **The radial Hardy inequality with a mean term.**  For `h` differentiable on `(0,∞)`
whose derivative `h'` is continuous there and whose weighted square is integrable,

  `h(z)² ≤ 2 (∫_{[1,2]} h² + ∫_{0}^{∞} (z h'(z) w(z))² dz)`.

The window `[1,2]` may be replaced by any interval of positive length on which `h²` is
controlled; it is fixed here since it is all the product rule needs. -/
theorem sob_z_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (h h' : ℝ → ℝ) (z : ℝ), 0 < z →
      (∀ x, 0 < x → HasDerivAt h (h' x) x) → ContinuousOn h' (Set.Ioi 0) →
      IntegrableOn (fun x => (x * h' x * w x) ^ 2) Iz →
      (h z) ^ 2 ≤ C * ((∫ x in (1 : ℝ)..2, (h x) ^ 2)
        + ∫ x in Iz, (x * h' x * w x) ^ 2) := by
  refine ⟨2, by norm_num, ?_⟩
  intro h h' z hz hder hcont hint
  -- `h` is continuous on `[1,2]`
  have hdiff : DifferentiableOn ℝ h (Set.Icc 1 2) := fun x hx =>
    (hder x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  have hcontI : ContinuousOn h (Set.Icc 1 2) := hdiff.continuousOn
  -- a minimiser of `h²` on `[1,2]`
  obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
    exists_min_le_mean (φ := fun x => (h x) ^ 2) (a := 1) (b := 2) (by norm_num)
      (hcontI.pow 2)
  have hz₀pos : 0 < z₀ := by linarith [hz₀mem.1]
  have hmin : (h z₀) ^ 2 ≤ ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by
    have h1 : (2 - 1 : ℝ)⁻¹ * ∫ t in (1 : ℝ)..2, (h t) ^ 2
        = ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by norm_num
    rw [← h1]
    exact hz₀min
  -- the weighted square of the derivative is nonnegative, and dominates the interval integral
  set P : ℝ := ∫ x in Iz, (x * h' x * w x) ^ 2 with hP
  have hPnn : 0 ≤ P :=
    setIntegral_nonneg measurableSet_Ici fun x _ => sq_nonneg _
  -- the Cauchy–Schwarz step on the interval between `z₀` and `z`
  have hkey : (h z - h z₀) ^ 2 ≤ P := by
    obtain ⟨a, b, hab, hapos, hcases⟩ :
        ∃ a b : ℝ, a ≤ b ∧ 0 < a ∧ ((a = z ∧ b = z₀) ∨ (a = z₀ ∧ b = z)) := by
      rcases le_total z₀ z with hle | hle
      · exact ⟨z₀, z, hle, hz₀pos, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨z, z₀, hle, hz, Or.inl ⟨rfl, rfl⟩⟩
    -- the derivative of `h` on `[a,b]`
    have hder' : ∀ x ∈ Set.Icc a b, HasDerivAt h (h' x) x := fun x hx =>
      hder x (by linarith [hx.1])
    have hcontI' : ContinuousOn h' (Set.Icc a b) :=
      hcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    have hcontI'' : ContinuousOn h' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
    -- the FTC
    have hFTC : ∫ x in a..b, h' x = h b - h a := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hcontI''.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hder x (by linarith [hx.1])
    -- the Cauchy–Schwarz inequality
    have hcontA : ContinuousOn (fun x => x * h' x * w x) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcontI') ?_
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hcontψ : ContinuousOn (fun x => x / (1 + x) ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hcs := hardyZ_interval_integral_mul_le_sqrt a b hab hcontA hcontψ
    -- rewriting the integrand
    have hcongr : ∫ x in a..b, (x * h' x * w x) * (x / (1 + x) ^ 2) = ∫ x in a..b, h' x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [Set.uIcc_of_le hab] at hx
        exact w_mul_psi_eq' (lt_of_lt_of_le hapos hx.1)
    -- the two factors
    have hA : ∫ x in a..b, (x * h' x * w x) ^ 2 ≤ P := by
      rw [hP]
      refine hardyZ_integral_Ioc_le_integral_Iz hapos.le hab hint fun x _ => sq_nonneg _
    have hB : ∫ x in a..b, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      hardyZ_integral_psi_sq_le_one hapos.le hab
    have hAnn : 0 ≤ ∫ x in a..b, (x * h' x * w x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hBnn : 0 ≤ ∫ x in a..b, (x / (1 + x) ^ 2) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hsq : (∫ x in a..b, h' x) ^ 2 ≤ P := by
      rw [← hcongr, ← sq_abs]
      refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hcs 2) ?_
      rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hBnn]
      nlinarith [hA, hB, hPnn]
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hFTC] at hsq
      nlinarith [hsq]
    · rw [hFTC] at hsq
      exact hsq
  -- assemble
  have h1 : (h z) ^ 2 ≤ 2 * (h z - h z₀) ^ 2 + 2 * (h z₀) ^ 2 := by
    nlinarith [sq_nonneg (h z - 2 * h z₀)]
  calc (h z) ^ 2 ≤ 2 * (h z - h z₀) ^ 2 + 2 * (h z₀) ^ 2 := h1
    _ ≤ 2 * P + 2 * ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by linarith [hkey, hmin]
    _ = 2 * ((∫ x in (1 : ℝ)..2, (h x) ^ 2) + P) := by ring

/-! ## The angular Hardy inequality with a mean term -/

/-- **The angular Hardy inequality with a mean term** (the "`θ`-Sobolev with the mean
term" of the design note `FTS/ELL_H2_LEAD.md` §B1).  For `h` differentiable on the open
interval with continuous derivative,

  `h(θ)² ≤ 204 (∫_{Iθ} h² + (γ-1)⁻¹ ∫_{Iθ} (h')² sin(2·)^{2-γ})`.

The mean term replaces the value `h(θ₀)` at a point where `h` would have to vanish. -/
theorem sob_theta_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ) (θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt h (deriv h x) x) →
      ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      IntegrableOn (fun σ => (h σ) ^ 2) Iθ →
      IntegrableOn (fun σ => (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ →
      (h θ) ^ 2 ≤ C * ((∫ σ in Iθ, (h σ) ^ 2)
        + (gam α - 1)⁻¹ * ∫ σ in Iθ, (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
  refine ⟨204, by norm_num, ?_⟩
  intro α h θ hα hα1 hθ hder hcont hint hint'
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  -- continuity of `h` on `[π/8, 3π/8]`
  have hcont8 : ContinuousOn h (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
    have hdiff : DifferentiableOn ℝ h (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun x hx =>
      (hder x hx).differentiableAt.differentiableWithinAt
    refine hdiff.continuousOn.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1, hπ], by linarith [hx.2, hπ]⟩
  -- a minimiser of `h²` on the middle half of `Iθ`
  obtain ⟨θ₀, hθ₀mem, hmin⟩ :=
    exists_min_le_mean (φ := fun σ => (h σ) ^ 2) (a := Real.pi / 8) (b := 3 * Real.pi / 8)
      (by linarith [hπ]) (hcont8.pow 2)
  have hθ₀Ioo : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ₀mem.1, hπ], by linarith [hθ₀mem.2, hπ]⟩
  -- the minimiser is at most the mean over `Iθ`
  have hmean : (h θ₀) ^ 2 ≤ (4 / Real.pi) * ∫ σ in Iθ, (h σ) ^ 2 := by
    have hsub : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Iθ := by
      intro x hx
      simp only [Iθ, Set.mem_Icc]
      exact ⟨by linarith [hx.1, hπ], by linarith [hx.2, hπ]⟩
    have hmono2 : (∫ σ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8), (h σ) ^ 2)
        ≤ ∫ σ in Iθ, (h σ) ^ 2 :=
      setIntegral_mono_set hint
        (ae_restrict_of_forall_mem measurableSet_Icc fun σ _ => sq_nonneg _)
        (Eventually.of_forall hsub)
    have hconv : (∫ t in Real.pi / 8..3 * Real.pi / 8, (h t) ^ 2)
        = ∫ σ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8), (h σ) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith [hπ]),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hcfg : (3 * Real.pi / 8 - Real.pi / 8)⁻¹ = 4 / Real.pi := by
      rw [show 3 * Real.pi / 8 - Real.pi / 8 = Real.pi / 4 by ring, inv_div]
    have hstep := hmin
    rw [hcfg, hconv] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hmono2 (by positivity))
  -- the oscillation bound
  have huIcc : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, hθ₀Ioo.2]⟩
    · exact ⟨by linarith [hθ₀Ioo.1, h1], by linarith [h2, hθ.2]⟩
  have hder' : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt h (deriv h x) x := fun x hx =>
    hder x (huIcc hx)
  have hcontd : ContinuousOn (deriv h) (Set.uIcc θ θ₀) := hcont.mono huIcc
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 h
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    (Set.mem_Icc.mpr ⟨le_of_lt hθ₀Ioo.1, le_of_lt hθ₀Ioo.2⟩) hder' hcontd hint'
  -- the angular integrand is nonnegative and the mean term is nonnegative
  have hA : 0 ≤ ∫ σ in Iθ, (h σ) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _
  have hB : 0 ≤ ∫ σ in Iθ, (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) _)
  have h8 : 8 / Real.pi ≤ 4 := by
    rw [div_le_iff₀ hπ]; linarith [Real.pi_gt_three]
  -- assemble
  have h1 : (h θ) ^ 2 ≤ 2 * (h θ - h θ₀) ^ 2 + 2 * (h θ₀) ^ 2 := by
    nlinarith [sq_nonneg (h θ - 2 * h θ₀)]
  have h2 : 2 * (h θ - h θ₀) ^ 2
      ≤ (200 / (gam α - 1)) * (∫ σ in Iθ,
          (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
    have hstep2 := mul_le_mul_of_nonneg_left hosc (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * (h θ - h θ₀) ^ 2
        ≤ 2 * (100 / (gam α - 1) * (∫ σ in Iθ,
            (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))) := hstep2
      _ = (200 / (gam α - 1)) * (∫ σ in Iθ,
            (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by ring
  have h3 : 2 * (h θ₀) ^ 2 ≤ (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) := by
    have hstep3 := mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * (h θ₀) ^ 2 ≤ 2 * ((4 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2)) := hstep3
      _ = (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) := by ring
  have h4 : (200 / (gam α - 1)) * (∫ σ in Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      ≤ 204 * ((gam α - 1)⁻¹ * ∫ σ in Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
    rw [div_eq_mul_inv]
    nlinarith [hB, hγ, inv_nonneg.mpr hγ.le]
  have h5 : (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) ≤ 204 * (∫ σ in Iθ, (h σ) ^ 2) := by
    nlinarith [hA, h8]
  nlinarith [h1, h2, h3, h4, h5]

end Work.FTS.OpenPkg.ProdOpen
end
end
