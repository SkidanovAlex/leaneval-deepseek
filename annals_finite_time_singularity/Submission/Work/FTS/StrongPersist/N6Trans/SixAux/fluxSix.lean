import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.H2.ZibpLimit
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.FluxOpen
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAux
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceBase
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.sliceIbpCanonW
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.trace_slot_ae6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixAux

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- The canonical weight is continuous in `z` on `(0,∞)` at a fixed angle. -/
theorem continuousOn_canonW_z (q θ : ℝ) :
    ContinuousOn (fun z : ℝ => Work.FTS.TransportS.SlotT2.canonW q z θ) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).continuousOn.pow 2).div
        (continuous_id.continuousOn.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    refine (h.pow 2).congr fun z _ => ?_
    simp only [Work.Spaces.w, Pi.pow_apply]
  have h2 : ContinuousOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) (Set.Ioi 0) :=
    hw.mul (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (Real.sin (2 * θ)) ^ (-q)) (Set.Ioi 0))
  refine h2.congr fun z _ => ?_
  rfl

/-- The canonical slot product, written as a product of square roots. -/
theorem abs_canonW_mul_mul_eq {q z θ X Y : ℝ}
    (hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ) :
    |Work.FTS.TransportS.SlotT2.canonW q z θ * X * Y|
      = Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2)
        * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by
  have hs : Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ)
      * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ)
      = Work.FTS.TransportS.SlotT2.canonW q z θ := Real.mul_self_sqrt hρ
  rw [abs_mul, abs_mul, abs_of_nonneg hρ, Real.sqrt_mul hρ, Real.sqrt_mul hρ,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  conv_lhs => rw [← hs]
  ring

/-- `√A √B ≤ (A + B)/2` for nonnegative `A`, `B`. -/
theorem sqrt_mul_sqrt_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt A * Real.sqrt B ≤ (A + B) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt A) (Real.sqrt B)
  rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at h
  linarith

/-- **The pointwise Cauchy–Schwarz bound for the canonical pairing.** -/
theorem abs_mul_canonW_mul_le {q M X Y hh z θ : ℝ}
    (hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ) (hM : 0 ≤ M) (hb : |hh| ≤ M) :
    |hh * (Work.FTS.TransportS.SlotT2.canonW q z θ * X * Y)|
      ≤ (M / 2) * (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by
  rw [abs_mul, abs_canonW_mul_mul_eq hρ]
  calc |hh| * (Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2)
        * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2))
      ≤ M * ((Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) / 2) :=
        mul_le_mul hb
          (sqrt_mul_sqrt_le (mul_nonneg hρ (sq_nonneg _)) (mul_nonneg hρ (sq_nonneg _)))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hM
    _ = (M / 2) * (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by ring

/-! ## The main theorem -/

/-- **The honest level-six top-slot radial integration by parts.**

This is the level-six (`a + b ≤ 6`, `HkMem α 6 g`, `HkMem α 7 g`) transplant of the honest
level-four bound `Work.FTS.StrongPersist.N6Trans.Hon.flux_bound_open` (which ports
`Work.FTS.TransportS.T3BadAux.slot_prod_le`, `Fin 5` → order 6, and removes the `RegQ`-style
trace hypothesis).  Route:

* the surviving slot `mixed b a g` has order `a + b ≤ 6`, and is priced by `slotW6_z` (when
  `a = 0`, `q ≤ η`) resp. `slotW6_mixed` (when `1 ≤ a`, `q ≤ γ`);
* `Dz (mixed b a g)` has order `a+b+1 ≤ 7`; this is what `HkMem α 7 g` is for (integrability of
  the boundary identity), the *bound* being by `HkSq α 6 g`;
* the a.e. boundary trace `z·(mixed b a g · w)² → 0` at `0⁺` and at `∞` is *derived* here:
  at `∞` from `DecayAll 6 g`; at `0⁺` from the `HkMem`-integrability of the radial slices
  (a dominating `z·F`, `F ∈ L¹(dz)`, forces the limit to vanish — `prim_limit_zero`,
  see the level-four version in `N6Trans/Hon/TraceAux.lean`);
* constant `C = 2` suffices. -/
theorem fluxSix : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h g : ℝ → ℝ → ℝ) (a b : ℕ) (q M : ℝ),
    0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
    a + b ≤ 6 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 6 g → Work.Spaces.HkMem α 7 g → Work.Spaces.DecayAll 6 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |h z θ| ≤ M) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz h z θ| ≤ M) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ C * M * Work.Spaces.HkSq α 6 g := by
  refine ⟨2, by norm_num, ?_⟩
  intro α h g a b q M hα hα1 hq0 hqγ hqη hab hsh hsg hm6 hm7 hdec hb hDb
  have hMnn : 0 ≤ M := by
    have h1 := hb 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h1
  -- the a.e. angular data
  have hslice6 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ) Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsg hm6).1
  have hslice7 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ) Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsg hm7).1
  have htrace := trace_slot_ae6 α g a b hα hsg hm6 hm7 hab
  -- the pointwise slot dominations
  have hdom6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ _ hθ hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Work.Spaces.mixed_zero_right]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 6 (hqη ha) hθ hθ2 (by omega)
    · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 6 hqγ hθ hθ2 ha (by omega)
  have hdom7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 g z θ := by
    intro z θ _ hθ hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Work.Spaces.mixed_zero_right]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 7 (hqη ha) hθ hθ2 (by omega)
    · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 7 hqγ hθ hθ2 ha (by omega)
  -- the integrand, as a function on the product
  let F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * h p.1 p.2
      * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
  let Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
  show |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ)|
      ≤ 2 * M * Work.Spaces.HkSq α 6 g
  have hcontF : ContinuousOn F Q := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2) Q :=
      Work.FTS.TransportS.SlotT2.continuousOn_canonW q
    have h2 : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) Q := hsh.continuousOn
    have h3 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2) Q :=
      (hsg.mixed (b + 1) a).continuousOn
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a g p.1 p.2) Q :=
      (hsg.mixed b a).continuousOn
    exact (((h1.mul h2).mul h3).mul h4).congr (fun p _ => rfl)
  have haesmF : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd F hcontF
  have haesmFabs : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    haesmF.norm.congr (Filter.Eventually.of_forall fun p => Real.norm_eq_abs (F p))
  have hcontFabs : ContinuousOn (fun p : ℝ × ℝ => |F p|) Q :=
    continuous_abs.comp_continuousOn hcontF
  -- the pointwise bound on the integrand
  have hFpt : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |F (z, θ)| ≤ (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
        + Work.Spaces.HkIntegrand α 7 g z θ) := by
    intro z θ hz hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0
      have hzero : F ((0 : ℝ), θ) = 0 := by
        show Work.FTS.TransportS.SlotT2.canonW q (0 : ℝ) θ * h (0 : ℝ) θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) (0 : ℝ) θ
          * Work.Spaces.mixed b a g (0 : ℝ) θ = 0
        rw [Work.FTS.TransportS.SlotT2.canonW_zero_z]
        ring
      rw [hzero, abs_zero]
      exact mul_nonneg (div_nonneg hMnn (by norm_num))
        (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ)
          (Work.Spaces.HkIntegrand_nonneg α 7 g 0 θ))
    · have h6 := hdom6 z θ hz0 hθ.1 hθ.2
      have h7 := hdom7 z θ hz0 hθ.1 hθ.2
      have hsplit : F (z, θ) = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ) := by
        show Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ
          = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        ring
      rw [hsplit]
      have hstep := abs_mul_canonW_mul_le (q := q) (M := M)
        (X := Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        (Y := Work.Spaces.mixed b a g z θ) (hh := h z θ) hρ hMnn (hb z θ hz0 hθ.1 hθ.2)
      refine hstep.trans ?_
      have hdz : Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          = Work.Spaces.mixed (b + 1) a g z θ := rfl
      rw [hdz]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ M / 2)
      linarith [h6, h7]
  -- the slice integrability of `|F|` for a.e. radius
  have hnz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hsliceabs : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |F (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hnz] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    refine MeasureTheory.Integrable.mono'
      (((hm6.1 z hzI).add (hm7.1 z hzI)).const_mul (M / 2))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => |F p|) hcontFabs hz) ?_
    refine (Work.FTS.TransportS.ae_mem_Ioo_Iθ).mono (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hFpt z θ hzI hθ
  -- the radial marginal
  have houtabs : MeasureTheory.Integrable
      (fun z => ∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono'
      (((hm6.2).add (hm7.2)).const_mul (M / 2)) ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' haesmFabs
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hzI : z ∈ Work.Spaces.Iz := hz
      have hmaj : MeasureTheory.Integrable
          (fun θ => (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
            + Work.Spaces.HkIntegrand α 7 g z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hm6.1 z hzI).add (hm7.1 z hzI)).const_mul (M / 2)
      have h1 : (∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ ∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => abs_nonneg _) hmaj
          ((Work.FTS.TransportS.ae_mem_Ioo_Iθ).mono fun θ hθ => hFpt z θ hzI hθ)
      have h2 : (∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (M / 2) * ((∫ θ, Work.Spaces.HkIntegrand α 6 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              + ∫ θ, Work.Spaces.HkIntegrand α 7 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hm6.1 z hzI) (hm7.1 z hzI)]
      calc ‖∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
          = ∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
        _ ≤ ∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1
        _ = (M / 2) * ((∫ θ, Work.Spaces.HkIntegrand α 6 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              + ∫ θ, Work.Spaces.HkIntegrand α 7 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := h2
  have hFabsint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => |F (z, θ)|) (fun z θ => abs_nonneg _) haesmFabs hsliceabs houtabs).1
  have hFint : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono' hFabsint haesmF
      (Filter.Eventually.of_forall fun p => le_of_eq (Real.norm_eq_abs (F p)))
  -- the a.e. radial slice bound
  have hE := slotEnergy6 α q g a b hq0 hqγ hqη hab hsg hm6
  have hmono : (fun θ => |∫ z, F (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 2 * M * (∫ z, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))) := by
    filter_upwards [hslice6, hslice7, htrace, Work.FTS.TransportS.ae_mem_Ioo_Iθ]
      with θ hI6 hI7 htr hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hsin.le _
    have hI6' : MeasureTheory.IntegrableOn
        (fun z => Work.Spaces.HkIntegrand α 6 g z θ) (Set.Ioi 0) :=
      (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hI6
    have hI7' : MeasureTheory.IntegrableOn
        (fun z => Work.Spaces.HkIntegrand α 7 g z θ) (Set.Ioi 0) :=
      (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hI7
    -- the two weighted slot slices
    have hYten : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hI6' ?_ ?_
      · exact ((continuousOn_canonW_z q θ).mul
          (((hsg.mixed b a).curry_z hθ).continuousOn.pow 2)).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_of_nonneg
          (mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI) (sq_nonneg _))]
        exact hdom6 z θ hz hθ.1 hθ.2
    have hDten : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hI7' ?_ ?_
      · exact ((continuousOn_canonW_z q θ).mul
          (((hsg.mixed (b + 1) a).curry_z hθ).continuousOn.pow 2)).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_of_nonneg
          (mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI) (sq_nonneg _))]
        exact hdom7 z θ hz hθ.1 hθ.2
    -- the integrand of the radial integration by parts
    have hFsliceTen : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (z * deriv (fun z' => Work.Spaces.mixed b a g z' θ) z)
          * Work.Spaces.mixed b a g z θ) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hDten.add hYten).const_mul (M / 2)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        have h1 := continuousOn_canonW_z q θ
        have h2 : ContinuousOn (fun z : ℝ => h z θ) (Set.Ioi 0) := (hsh.curry_z hθ).continuousOn
        have h3 : ContinuousOn (fun z : ℝ => Work.Spaces.pz (Work.Spaces.mixed b a g) z θ)
            (Set.Ioi 0) := ((hsg.mixed b a).pz.curry_z hθ).continuousOn
        have h4 : ContinuousOn (fun z : ℝ => Work.Spaces.mixed b a g z θ) (Set.Ioi 0) :=
          (hsg.mixed b a).curry_z hθ |>.continuousOn
        exact (((h1.mul h2).mul (continuous_id.continuousOn.mul h3)).mul h4).congr
          (fun z _ => rfl)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs]
        have hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
          Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
        rw [show Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
              * (z * deriv (fun z' => Work.Spaces.mixed b a g z' θ) z)
              * Work.Spaces.mixed b a g z θ
            = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ) from by
            simp only [Work.Spaces.Dz, Work.Spaces.pz]; ring]
        exact abs_mul_canonW_mul_le (q := q) (M := M)
          (X := Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
          (Y := Work.Spaces.mixed b a g z θ) (hh := h z θ) hρ hMnn (hb z θ hz hθ.1 hθ.2)
    -- the two boundary limits
    have hkey : ∀ z : ℝ, 0 < z →
        (z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2)
          = ((Real.sin (2 * θ)) ^ (-q) * h z θ)
            * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2) := by
      intro z _
      rw [Work.FTS.TransportS.SlotT2.canonW]
      ring
    have hlim0 : Filter.Tendsto
        (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (Work.Spaces.mixed b a g z θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcore : Filter.Tendsto
          (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := htr.1
      have hbound : ∀ᶠ z in (nhdsWithin (0 : ℝ) (Set.Ioi 0)),
          ‖z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2‖
          ≤ ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2| := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [Real.norm_eq_abs, hkey z hz, abs_mul]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (mul_nonneg hsnn hMnn)
        rw [abs_mul, abs_of_nonneg hsnn]
        exact mul_le_mul_of_nonneg_left (hb z θ hz hθ.1 hθ.2) hsnn
      have htend : Filter.Tendsto
          (fun z : ℝ => ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h2 : Filter.Tendsto
            (fun z : ℝ => |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
          simpa only [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.mp hcore
        simpa using h2.const_mul ((Real.sin (2 * θ)) ^ (-q) * M)
      exact squeeze_zero_norm' hbound htend
    have hlimT : Filter.Tendsto
        (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (Work.Spaces.mixed b a g z θ) ^ 2)
        Filter.atTop (nhds 0) := by
      have hcore : Filter.Tendsto
          (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
          Filter.atTop (nhds 0) := htr.2
      have hbound : ∀ᶠ z in Filter.atTop,
          ‖z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2‖
          ≤ ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2| := by
        filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with z hz
        rw [Real.norm_eq_abs, hkey z hz, abs_mul]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (mul_nonneg hsnn hMnn)
        rw [abs_mul, abs_of_nonneg hsnn]
        exact mul_le_mul_of_nonneg_left (hb z θ hz hθ.1 hθ.2) hsnn
      have htend : Filter.Tendsto
          (fun z : ℝ => ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
          Filter.atTop (nhds 0) := by
        have h2 : Filter.Tendsto
            (fun z : ℝ => |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
            Filter.atTop (nhds 0) := by
          simpa only [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.mp hcore
        simpa using h2.const_mul ((Real.sin (2 * θ)) ^ (-q) * M)
      exact squeeze_zero_norm' hbound htend
    rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
    exact sliceIbpCanonW (q := q) (M := M) (h := fun z => h z θ)
      (Y := fun z => Work.Spaces.mixed b a g z θ) (θ := θ) hMnn hθ
      (fun z hz => hsh.hasDerivAt_slice hθ hz)
      (fun z hz => (hsg.mixed b a).hasDerivAt_slice hθ hz)
      (fun z hz => hb z θ hz hθ.1 hθ.2)
      (fun z hz => hDb z θ hz hθ.1 hθ.2)
      hYten hFsliceTen hlim0 hlimT
  -- the assembly
  have hFmargint : MeasureTheory.Integrable
      (fun θ => |∫ z, F (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFint.integral_prod_right.abs
  have hGmargint : MeasureTheory.Integrable
      (fun θ => 2 * M * (∫ z, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.2.1.const_mul (2 * M)
  have hFubini : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ) := by
    have h1 := MeasureTheory.integral_integral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => F (z, θ)) hFint
    have h2 := MeasureTheory.integral_integral_swap
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => F (z, θ)) hFint
    exact h2
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ)|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ)| := by rw [hFubini]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |∫ z in Work.Spaces.Iz, F (z, θ)| :=
        MeasureTheory.abs_integral_le_integral_abs
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => ∫ z in Work.Spaces.Iz, F (z, θ))
    _ ≤ ∫ θ in Work.Spaces.Iθ, 2 * M * (∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) :=
        MeasureTheory.integral_mono_ae hFmargint hGmargint hmono
    _ = 2 * M * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ 2 * M * Work.Spaces.HkSq α 6 g :=
        mul_le_mul_of_nonneg_left hE.2.2 (by linarith)

end

end Work.FTS.StrongPersist.N6Trans.SixAux
