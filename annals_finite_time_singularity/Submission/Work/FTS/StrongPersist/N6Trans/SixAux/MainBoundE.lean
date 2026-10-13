import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the exceptional (`f·D_z g`) term

The top term of the Leibniz expansion of `D_z^bD_θ^a (f·D_z g)`, in which all derivatives fall on
`g`.  For `a + b ≤ 5` it is bounded pointwise (the `g`-block stays inside the level-6 slot); for
`a + b = 6` the second `g`-factor is at level 7, where only the *signed* radial integration by
parts `fluxSix` applies.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The exceptional term of the Leibniz expansion, at weight `q`: bounded by
`max Cf 1 · Kf · |g|²_{ℋ⁶}` where `Cf` is the constant of the signed radial IBP `fluxSix`
(used only when `a + b = 6`) and `Kf` bounds `f` pointwise. -/
theorem main_bound_E {α q Cf Kf : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hgs : Work.FTS.EllipticEst.SmoothOpen g)
    (hgm : Work.Spaces.HkMem α 6 g) (hgm7 : Work.Spaces.HkMem α 7 g)
    (hgd : Work.Spaces.DecayAll 6 g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Kf)
    (hKf0 : 0 ≤ Kf) (hCf0 : 0 ≤ Cf)
    (hflux : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ Cf * (Kf * Work.Spaces.HkSq α 6 g))
    (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α)
    (hqη : a = 0 → q ≤ Work.Spaces.eta) (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) pm ∧
      |∫ p, canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2 ∂pm|
      ≤ max Cf 1 * (Kf * Work.Spaces.HkSq α 6 g) := by
  -- a.e. strong measurability of the signed integrand
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
      * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul hfs.continuousOn).mul
        ((hgs.mixed (b + 1) a).continuousOn)).mul ((hgs.mixed b a).continuousOn))
  -- the pointwise slot pairing of the two `g`-blocks at an arbitrary level `k`
  have hpair : ∀ k : ℕ, a + b + 1 ≤ k → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
        * |Work.Spaces.mixed b a g z θ| ≤ Work.Spaces.HkIntegrand α k g z θ := by
    intro k hk z θ hz hθ hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    have h1 : canonW q z θ * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g z θ := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        simp only [Work.Spaces.mixed_zero_right]
        rw [← Work.Spaces.DzIter_succ]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := q) (g := g) k
          (hqη rfl) hθ hθ2 (by omega)
      · rw [show Work.Spaces.Dz (Work.Spaces.mixed b a g) = Work.Spaces.mixed (b + 1) a g
            from rfl]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α) (q := q) (g := g) k
          hqγ hθ hθ2 ha (by omega)
    have h2 : canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g z θ := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        simp only [Work.Spaces.mixed_zero_right]
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := q) (g := g) k
          (hqη rfl) hθ hθ2 (by omega)
      · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α) (q := q) (g := g) k
          hqγ hθ hθ2 ha (by omega)
    have habs : |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
        * |Work.Spaces.mixed b a g z θ|
        ≤ ((Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
          + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
      rw [← abs_mul]
      exact Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add _ _
    calc canonW q z θ * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
          * |Work.Spaces.mixed b a g z θ|
        = canonW q z θ * (|Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
            * |Work.Spaces.mixed b a g z θ|) := by ring
      _ ≤ canonW q z θ * (((Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2
            + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left habs (canonW_nonneg hθI)
      _ = (canonW q z θ * (Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ) ^ 2) / 2
            + (canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α k g z θ := by linarith [h1, h2]
  by_cases h6 : a + b = 6
  · -- ## the top slot: the signed radial IBP
    have hpt7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |canonW q z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          * Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 7 g z θ := by
      intro z θ hz hθ hθ2
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg hθI)]
      calc canonW q z θ * |f z θ| * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
            * |Work.Spaces.mixed b a g z θ|
          = |f z θ| * (canonW q z θ * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ Kf * Work.Spaces.HkIntegrand α 7 g z θ :=
            mul_le_mul (hf z θ hz hθ hθ2) (hpair 7 (by omega) z θ hz hθ hθ2)
              (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)) hKf0
    have hint7 : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) pm :=
      MeasureTheory.Integrable.mono'
        (((Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hgs hgm7).1).const_mul
          Kf) haesm
        (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
          ‖canonW q p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2‖ ≤ Kf * Work.Spaces.HkIntegrand α 7 g p.1 p.2)
          (fun z θ hz hθ hθ2 => by
            rw [Real.norm_eq_abs]
            exact hpt7 z θ hz hθ hθ2))
    have hfub : (∫ p, canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2 ∂pm)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ :=
      (MeasureTheory.integral_integral (f := fun z θ => canonW q z θ * f z θ
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ) hint7).symm
    refine ⟨hint7, ?_⟩
    rw [hfub]
    exact le_trans hflux (mul_le_mul_of_nonneg_right (le_max_left Cf 1)
      (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 6 g)))
  · -- ## `a + b ≤ 5`: the pointwise bound
    have hpt6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |canonW q z θ * f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          * Work.Spaces.mixed b a g z θ| ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ := by
      intro z θ hz hθ hθ2
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg hθI)]
      calc canonW q z θ * |f z θ| * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
            * |Work.Spaces.mixed b a g z θ|
          = |f z θ| * (canonW q z θ * |Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ Kf * Work.Spaces.HkIntegrand α 6 g z θ :=
            mul_le_mul (hf z θ hz hθ hθ2) (hpair 6 (by omega) z θ hz hθ hθ2)
              (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _)) hKf0
    have hmaj6 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Kf * Work.Spaces.HkIntegrand α 6 g p.1 p.2) pm :=
      ((Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hgs hgm).1).const_mul Kf
    have hint6 : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
        * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) pm :=
      MeasureTheory.Integrable.mono' hmaj6 haesm
        (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
          ‖canonW q p.1 p.2 * f p.1 p.2 * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2‖ ≤ Kf * Work.Spaces.HkIntegrand α 6 g p.1 p.2)
          (fun z θ hz hθ hθ2 => by
            rw [Real.norm_eq_abs]
            exact hpt6 z θ hz hθ hθ2))
    refine ⟨hint6, ?_⟩
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs (μ := pm)) ?_
    have h2 : (∫ p, |canonW q p.1 p.2 * f p.1 p.2
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        = ∫ p, canonW q p.1 p.2 * |f p.1 p.2|
          * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2| ∂pm :=
      MeasureTheory.integral_congr_ae (Work.FTS.TransportS.ae_of_forall_Qd
        (P := fun p : ℝ × ℝ => |canonW q p.1 p.2 * f p.1 p.2
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2
            * Work.Spaces.mixed b a g p.1 p.2|
          = canonW q p.1 p.2 * |f p.1 p.2|
            * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|)
        (fun z θ hz hθ hθ2 => by
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg hθI)]))
    rw [h2]
    have hcomm : (∫ p, canonW q p.1 p.2 * |f p.1 p.2|
          * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ ∫ p, Kf * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂pm := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj6 ?_
      · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
            0 ≤ canonW q p.1 p.2 * |f p.1 p.2|
              * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) (fun z θ hz hθ hθ2 => by
            have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
            exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
              (abs_nonneg _)) (abs_nonneg _))] with p hp
        exact hp
      · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
            canonW q p.1 p.2 * |f p.1 p.2|
              * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2| ≤ Kf * Work.Spaces.HkIntegrand α 6 g p.1 p.2)
            (fun z θ hz hθ hθ2 => by
              have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
              have h := hpt6 z θ hz hθ hθ2
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg hθI)] at h
              exact h)] with p hp
        exact hp
    calc (∫ p, canonW q p.1 p.2 * |f p.1 p.2|
          * |Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ ∫ p, Kf * Work.Spaces.HkIntegrand α 6 g p.1 p.2 ∂pm := hcomm
      _ = Kf * Work.Spaces.HkSq α 6 g := by
        rw [MeasureTheory.integral_const_mul,
          (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hgs hgm).2]
      _ ≤ max Cf 1 * (Kf * Work.Spaces.HkSq α 6 g) := by
        have h := mul_le_mul_of_nonneg_right (le_max_right Cf 1)
          (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 6 g))
        simpa only [one_mul] using h

end Work.FTS.StrongPersist.N6Trans.SixAux
