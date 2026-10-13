import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.TransportS.T2Sup

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary real tools

These three tools are stated so that they require *no* measurability of the functions
involved; this is what keeps the final assembly free of side conditions. -/

/-- Young's inequality: `a b ≤ (t a² + b²/t)/2` for every `t > 0` (no sign hypothesis). -/
theorem delicate_amgm {a b t : ℝ} (ht : 0 < t) :
    a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have hsq : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  have heq : (t * a ^ 2 + b ^ 2 / t) / 2 = (t ^ 2 * a ^ 2 + b ^ 2) / (2 * t) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  nlinarith [hsq]

/-- If `C ≤ (t A + B/t)/2` for every `t > 0` with `A, B ≥ 0`, then `C ≤ √(A B)`. -/
theorem delicate_le_sqrt_mul {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → C ≤ (t * A + B / t) / 2) : C ≤ Real.sqrt (A * B) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [← hA0, zero_mul, Real.sqrt_zero]
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hspos : 0 < B / (2 * ε) + 1 := by positivity
    have h1 := h (B / (2 * ε) + 1) hspos
    rw [← hA0] at h1
    have hkey : B / (B / (2 * ε) + 1) ≤ 2 * ε := by
      have hden : 0 < B / (2 * ε) + 1 := by positivity
      rw [div_le_iff₀ hden]
      have hmul : (2 * ε) * (B / (2 * ε)) = B := by field_simp
      nlinarith [hmul]
    have h2 : (0 * 0 + B / (B / (2 * ε) + 1)) / 2 ≤ 0 + ε := by linarith
    linarith
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · rw [← hB0, mul_zero, Real.sqrt_zero]
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have hspos : 0 < ε / A := by positivity
      have h1 := h (ε / A) hspos
      rw [← hB0, zero_div, add_zero] at h1
      have hkey : ε / A * A = ε := by field_simp
      have h2 : (ε / A * A + 0) / 2 ≤ ε + 0 := by rw [hkey]; linarith
      linarith
    · have hAsqrt : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have hBsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
      have hspos : 0 < Real.sqrt B / Real.sqrt A := div_pos hBsqrt hAsqrt
      have h1 := h (Real.sqrt B / Real.sqrt A) hspos
      have e1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
        field_simp
        rw [Real.sq_sqrt hA]
      have e2 : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt A * Real.sqrt B := by
        field_simp
        rw [Real.sq_sqrt hB]
      have key : (Real.sqrt B / Real.sqrt A * A + B / (Real.sqrt B / Real.sqrt A)) / 2
          = Real.sqrt (A * B) := by
        rw [e1, e2, Real.sqrt_mul hA]
        ring
      linarith [h1, key]

/-- Cauchy–Schwarz for a set integral of two nonnegative functions: only the integrability of
the two *squares* is needed (no measurability of `f` or `g`). -/
theorem delicate_setIntegral_mul_le_sqrt {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hf2 : MeasureTheory.IntegrableOn (fun x => (f x) ^ 2) s)
    (hg2 : MeasureTheory.IntegrableOn (fun x => (g x) ^ 2) s)
    (hfnn : ∀ x ∈ s, 0 ≤ f x) (hgnn : ∀ x ∈ s, 0 ≤ g x) :
    (∫ x in s, f x * g x)
      ≤ Real.sqrt (∫ x in s, (f x) ^ 2) * Real.sqrt (∫ x in s, (g x) ^ 2) := by
  set A : ℝ := ∫ x in s, (f x) ^ 2 with hA
  set B : ℝ := ∫ x in s, (g x) ^ 2 with hB
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => sq_nonneg (f x))
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact MeasureTheory.setIntegral_nonneg hs (fun x _ => sq_nonneg (g x))
  have hmain : ∀ t : ℝ, 0 < t →
      (∫ x in s, f x * g x) ≤ (t * A + B / t) / 2 := by
    intro t ht
    have hRHS : MeasureTheory.IntegrableOn
        (fun x => (1 / 2) * (t * (f x) ^ 2 + (g x) ^ 2 / t)) s :=
      ((hf2.const_mul t).add (hg2.div_const t)).const_mul (1 / 2)
    have hmono : (∫ x in s, f x * g x)
        ≤ ∫ x in s, (1 / 2) * (t * (f x) ^ 2 + (g x) ^ 2 / t) := by
      refine MeasureTheory.setIntegral_mono_of_nonneg
        (fun x hx => mul_nonneg (hfnn x hx) (hgnn x hx)) (fun x hx => ?_) hRHS
      have h2 := delicate_amgm (a := f x) (b := g x) ht
      linarith
    have hval : (∫ x in s, (1 / 2) * (t * (f x) ^ 2 + (g x) ^ 2 / t))
        = (t * A + B / t) / 2 := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add (hf2.const_mul t) (hg2.div_const t),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_div, hA, hB]
      ring
    rw [← hval]
    exact hmono
  have hfin := delicate_le_sqrt_mul hAnn hBnn hmain
  rwa [Real.sqrt_mul hAnn] at hfin

/-- `σ^{-q} ≤ σ^{-γ}` for `0 < σ ≤ 1` and `q ≤ γ`. -/
theorem delicate_rpow_neg_le {σ q γ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (h : q ≤ γ) :
    σ ^ (-q) ≤ σ ^ (-γ) :=
  Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)

/-- `1 ≤ σ^{-γ}` for `0 < σ ≤ 1` and `0 ≤ γ`. -/
theorem delicate_one_le_rpow_neg {σ γ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hγ : 0 ≤ γ) :
    1 ≤ σ ^ (-γ) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (show -γ ≤ 0 by linarith)
  rwa [Real.rpow_zero] at h

/-- A.e. strong measurability of `θ ↦ σ(θ)^{-γ} v(θ)` on `Iθ` for `v` continuous on the open
interval. -/
theorem delicate_aesm_weight_mul {α : ℝ} {v : ℝ → ℝ}
    (hv : ContinuousOn v (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * v θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine (((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn).rpow_const ?_).mul hv
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by show (0 : ℝ) < 2 * θ; linarith [hθ.1])
      (by show 2 * θ < Real.pi; linarith [hθ.2, Real.pi_pos])))
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hcont.aestronglyMeasurable measurableSet_Ioo

/-- `x^{-β/2}` squared is `x^{-β}` (for `x ≥ 0`). -/
theorem delicate_sq_half_rpow {x β : ℝ} (hx : 0 ≤ x) : (x ^ (-(β) / 2)) ^ 2 = x ^ (-β) := by
  rw [sq]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    rcases eq_or_ne β 0 with hb | hb
    · subst hb
      norm_num
    · have h1 : -(β) / 2 ≠ 0 := by intro h; exact hb (by linarith)
      have h2 : -β ≠ 0 := by intro h; exact hb (by linarith)
      rw [Real.zero_rpow h1, Real.zero_rpow h2, mul_zero]
  · rw [← Real.rpow_add h0]
    ring_nf

/-- A four-factor product bound, all factors nonnegative. -/
theorem delicate_mul_four_le {a a' b b' c c' d d' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (hd : d ≤ d') (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha'0
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha'0 hb'0)
  exact mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha'0 hb'0) hc'0)

/-! ## The angular marginal `Ψ` -/

/-- The `θ`-marginal `Ψ(θ) = ∫_s w(s)² (D_z²D_θ g(s,θ))² ds` is a.e. strongly measurable
(it is the marginal of a function continuous on the open quadrant). -/
theorem delicate_psiTheta_aesm {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ => ∫ s in Work.Spaces.Iz,
        (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.mixed 2 1 g p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      simp only [Work.Spaces.w]
      exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2
    exact h1.mul ((hg.mixed 2 1).continuousOn.pow 2)
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.mixed 2 1 g p.1 p.2) ^ 2) hcont
  have h2 := haesm.prod_swap.integral_prod_right'
  simpa only [Function.uncurry, Prod.swap_prod_mk, Work.Spaces.Iz, Work.Spaces.Iθ] using h2

/-! ## The radial Hardy inequality on the slice `θ ↦ D_zD_θ g(·,θ)` -/

/-- `SmoothQuad` implies `SmoothOpen`. -/
theorem delicate_smoothOpen_of_smoothQuad {g : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad g) : Work.FTS.EllipticEst.SmoothOpen g := by
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    refine Set.mem_prod.mpr ⟨?_, ?_, ?_⟩
    · show (-1 : ℝ) < p.1
      linarith
    · exact hp2
    · exact hp3
  exact h.mono hsub

/-- **The radial Hardy inequality for the slice of `D_zD_θ g`.**  For almost every angle `θ`,
and then for *every* `z > 0`,

  `(D_zD_θ g(z,θ))² ≤ ∫_s w(s)² (D_z²D_θ g(s,θ))² ds`.

This is `Work.FTS.H2.hardyZ_open` applied to the slice `s ↦ D_zD_θg(s,θ)`; the a.e.-ness in
`θ` is what makes the integrability hypothesis of the Hardy inequality honest (`ℋ⁴`-membership
only gives it for a.e. `θ`). -/
theorem delicate_hardyG_ae {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hg : Work.FTS.TransportS.T2SG α g) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (Work.Spaces.mixed 1 1 g z θ) ^ 2
          ≤ ∫ s in Work.Spaces.Iz,
              (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
  have hquad : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hmem : Work.Spaces.HkMem α 4 g := hg.hk4
  have hsm : Work.FTS.EllipticEst.SmoothOpen g := delicate_smoothOpen_of_smoothQuad hquad
  obtain ⟨_hswap, _hmarg, hslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hsm hmem
  have hIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) ∧
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          Work.Spaces.Iz := by
    filter_upwards [hIoo, hslice] with θ hθ hI
    refine ⟨hθ, ?_⟩
    refine hI.mono' ?_ ?_
    · have hcont : ContinuousOn
          (fun s : ℝ => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          (Set.Ioi 0) := by
        have h1 : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi 0) := by
          simp only [Work.Spaces.w]
          exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
            (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))).pow 2
        exact h1.mul (((hquad.mixed 2 1).curry_z hθ).continuousOn.pow 2 |>.mono
          (fun s hs => by simp only [Set.mem_Ioi] at hs ⊢; linarith))
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hspos
      · subst h0
        have hzero : (Work.Spaces.w 0) ^ 2 * (Work.Spaces.mixed 2 1 g 0 θ) ^ 2 = 0 := by
          rw [show Work.Spaces.w 0 = 0 from by simp [Work.Spaces.w]]
          ring
        rw [hzero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
      · have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by show (0 : ℝ) < 2 * θ; linarith [hθ.1])
            (by show 2 * θ < Real.pi; linarith [hθ.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hslot := Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g
          (Work.Spaces.gam_pos hα) le_rfl hspos hθI 2 1 le_rfl (by norm_num)
        have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
            = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθI,
            show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
            Work.FTS.H2.hbi_Wm_sq α s θ (le_of_lt hsin)]
        have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          delicate_one_le_rpow_neg hsin (Real.sin_le_one _) (le_of_lt (Work.Spaces.gam_pos hα))
        calc (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
            ≤ (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              have h0 : 0 ≤ (Work.Spaces.mixed 2 1 g s θ) ^ 2 := sq_nonneg _
              have h1 : (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
                  ≤ (Work.Spaces.w s) ^ 2
                    * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                      * (Work.Spaces.mixed 2 1 g s θ) ^ 2) :=
                mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h0 hone) (sq_nonneg _)
              linarith [h1]
          _ = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              rw [hcanon]
          _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hslot
  filter_upwards [hae] with θ hθ z hz
  obtain ⟨hθIoo, hIint⟩ := hθ
  have hslicecont : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) (Set.Ioi 0) :=
    ((hquad.mixed 1 1).curry_z hθIoo).of_le (by simp [Work.Stability.smoothOrder]) |>.mono
      (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)
  have hdec : Tendsto (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) atTop (𝓝 0) :=
    hg.decay.2 1 1 (by norm_num) θ ⟨le_of_lt hθIoo.1, le_of_lt hθIoo.2⟩
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun s' : ℝ => Work.Spaces.mixed 1 1 g s' θ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using hIint
  have h := Work.FTS.H2.hardyZ_open hslicecont hdec hint z hz
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using h

/-! ## The two `ℋ⁴`-slot bounds for the `g`-factors -/

/-- The `θ`-marginal of the `(2,1)`-slot of `g`: `∫_θ σ^{-γ} ∫_s w²(D_z²D_θ g)² ≤ |g|_{ℋ⁴}²`. -/
theorem delicate_psiMarginal_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hg : Work.FTS.TransportS.T2SG α g) :
    MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hquad : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen g := delicate_smoothOpen_of_smoothQuad hquad
  have hmem : Work.Spaces.HkMem α 4 g := hg.hk4
  set G : ℝ → ℝ → ℝ := fun s θ =>
    Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ * (Work.Spaces.mixed 2 1 g s θ) ^ 2
    with hGdef
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_joint_aesm hsm 2 1
  have hslice : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => G s θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => by
      rw [hGdef]
      exact Work.FTS.TransportS.SlotT2.mslot_slice_integrable hγpos le_rfl hsm hmem 2 1
        le_rfl (by norm_num) hs)
  have hmarg : MeasureTheory.Integrable
      (fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_marginal_integrable hγpos le_rfl hsm hmem 2 1
      le_rfl (by norm_num)
  have hnorm : (fun s => ∫ θ, ‖G s θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext s
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.TransportS.SlotT2.canonW_nonneg (q := Work.Spaces.gam α)
        (z := s) (θ := θ) hθ) (sq_nonneg _))
  have hjoint : MeasureTheory.Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff haesm).mpr
      ⟨hslice, by simpa only [Function.uncurry, hnorm] using hmarg⟩
  have hmargθ : MeasureTheory.Integrable
      (fun θ => ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.integral_prod_right hjoint
  have hswap := MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hjoint
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
        = ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro θ hθ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
        = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθ,
        show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
        Work.FTS.H2.hbi_Wm_sq α s θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
    rw [hGdef]
    simp only
    rw [hcanon]
    ring
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun hmargθ (fun θ hθ => (hpt θ hθ).symm)
      measurableSet_Icc
  · have h1 : (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hpt θ hθ)
    rw [h1]
    rw [← hswap]
    have hslot := Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 2 1 le_rfl (by norm_num)
    simpa only [hGdef] using hslot

/-- The `(3,1)`-slot of `g`: the `θ`-slices are integrable and
`∫_z w² ∫_θ σ^{-γ}(D_z³D_θ g)² ≤ |g|_{ℋ⁴}²`. -/
theorem delicate_qFun_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hg : Work.FTS.TransportS.T2SG α g) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
          Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hquad : Work.FTS.LocData.SmoothQuad g := hg.reg.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen g := delicate_smoothOpen_of_smoothQuad hquad
  have hmem : Work.Spaces.HkMem α 4 g := hg.hk4
  have hθIoo : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hcanon : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    intro z θ hθ
    rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ,
      show Work.Spaces.Wt α z θ = Work.FTS.H2.Wm α z θ from rfl,
      Work.FTS.H2.hbi_Wm_sq α z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hzero : (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
        funext θ
        have hm : Work.Spaces.mixed 3 1 g 0 θ = 0 := by
          show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter 2 (Work.Spaces.DthIter 1 g)) 0 θ = 0
          ring
        rw [hm]
        simp
      rw [hzero]
      exact integrableOn_zero
    · have hcw := Work.FTS.TransportS.SlotT2.mslot_slice_integrable (α := α)
        (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num) hz
      refine hcw.mono' ?_ ?_
      · exact delicate_aesm_weight_mul
          (((hquad.mixed 3 1).curry_θ (by simp only [Set.mem_Ioi]; linarith)).continuousOn.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
          one_le_pow₀ (Work.FTS.TransportS.one_le_w hzpos)
        have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _
        have h0 : 0 ≤ (Work.Spaces.mixed 3 1 g z θ) ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hσnn h0), hcanon z θ hθ]
        have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2) :=
          le_mul_of_one_le_left (mul_nonneg hσnn h0) hw1
        linarith [h1]
  · have hmarg := Work.FTS.TransportS.SlotT2.mslot_marginal_integrable (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num)
    refine MeasureTheory.IntegrableOn.congr_fun hmarg (fun z _ => ?_) measurableSet_Ici
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hcanon z θ hθ]
    ring
  · have hEq : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Work.Spaces.mixed 3 1 g z θ) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hcanon z θ hθ]
      ring
    rw [hEq]
    exact Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 3 1 le_rfl (by norm_num)

theorem delicateBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
      Work.FTS.TransportS.T2SF α f → Work.FTS.TransportS.T2SG α g →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
            * |Work.Spaces.mixed 3 1 g z θ|)
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.Spaces.HkSq α 4 g := by
  obtain ⟨CΦ, hCΦpos, hΦall⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  refine ⟨10 * CΦ + 2, by positivity, ?_⟩
  intro α q f g hα hα1 hq0 hqγ hsf hsg
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ1pos : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hquad : Work.FTS.LocData.SmoothQuad g := hsg.reg.1
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g := delicate_smoothOpen_of_smoothQuad hquad
  -- the auxiliary functions
  set Φ : ℝ → ℝ := fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
    y = |Work.Spaces.DzIter 3 f z θ|} with hΦdef
  set Ψ : ℝ → ℝ := fun θ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2 with hΨdef
  set Q : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2
    with hQdef
  set A : ℝ := ∫ z in Work.Spaces.Iz, (Φ z) ^ 2 * (Work.Spaces.w z) ^ 2 with hAdef
  set I4 : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ with hI4def
  set Bq : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Q z with hBqdef
  set 𝔉 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
    * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
    * |Work.Spaces.mixed 3 1 g z θ| with h𝔉def
  -- nonnegativity
  have hΨnn : ∀ θ, 0 ≤ Ψ θ := by
    intro θ
    rw [hΨdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hQnn : ∀ z, 0 ≤ Q z := by
    intro z
    rw [hQdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
        (sq_nonneg _))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hI4nn : 0 ≤ I4 := by
    rw [hI4def]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
        (hΨnn θ))
  have hBqnn : 0 ≤ Bq := by
    rw [hBqdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun z _ => mul_nonneg (sq_nonneg _) (hQnn z))
  have h𝔉nn : ∀ z, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ 𝔉 z θ := by
    intro z θ hθ
    rw [h𝔉def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _))
      (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  -- the f-side: the angular supremum of `D_z³f`
  obtain ⟨hΦInt, hΦLe⟩ := hΦall α f 3 hα hα1 (le_refl 3) hsf.smoothOpen hsf.hk
  have hΦbdd : ∀ z ∈ Set.Ioi (0 : ℝ), BddAbove {y : ℝ |
      ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} :=
    fun z hz => Work.FTS.TransportS.SlotT2.supOpen_slice_bddAbove hsf.smoothOpen hsf.hk
      hα hα1 (by norm_num) hz
  have hΦge : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DzIter 3 f z θ| ≤ Φ z := by
    intro z hz θ hθ
    rw [hΦdef]
    exact le_csSup (hΦbdd z hz) ⟨θ, hθ, rfl⟩
  have hΦnn : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Φ z := by
    intro z hz
    rw [hΦdef]
    exact le_trans (abs_nonneg _) (le_csSup (hΦbdd z hz)
      ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, rfl⟩)
  have hA0 : A ≤ CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    rw [hAdef]
    simpa only [hΦdef] using hΦLe
  -- the g-side: the Hardy inequality and the two `ℋ⁴`-slots
  have hHardy := delicate_hardyG_ae hα hsg
  obtain ⟨hPsiInt0, hPsiLe0⟩ := delicate_psiMarginal_le hα hsg
  have hPsiInt : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ) Work.Spaces.Iθ := by
    simpa only [hΨdef] using hPsiInt0
  have hI4le : I4 ≤ Work.Spaces.HkSq α 4 g := by
    rw [hI4def]
    simpa only [hΨdef] using hPsiLe0
  obtain ⟨hQslice, hQint, hQle⟩ := delicate_qFun_le hα hsg
  have hBqle : Bq ≤ Work.Spaces.HkSq α 4 g := by
    rw [hBqdef]
    simpa only [hQdef] using hQle
  have hΨaesm : MeasureTheory.AEStronglyMeasurable (fun θ => Real.sqrt (Ψ θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 := delicate_psiTheta_aesm hsmg
    have h1 : (fun θ => Real.sqrt (Ψ θ))
        = fun θ => Real.sqrt (∫ s in Work.Spaces.Iz,
            (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2) := by
      funext θ
      simp only [hΨdef]
    rw [h1]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable h0
  -- the good angles
  have hgoodθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) ∧
        ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Spaces.mixed 1 1 g z θ) ^ 2 ≤ Ψ θ := by
    have hIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hIoo, hHardy] with θ h1 h2
    refine ⟨h1, fun z hz => ?_⟩
    rw [hΨdef]
    exact h2 z hz
  -- the main chain
  have hmain : ∀ t : ℝ, 0 < t →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
        ≤ (t * A + (I4 * Bq) / t) / 2 := by
    intro t ht
    have hPtwise : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
      intro z hz
      have hz0 : (0 : ℝ) < z := hz
      -- the integrability of the Hardy majorant
      have haesmS : MeasureTheory.AEStronglyMeasurable
          (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
            * |Work.Spaces.mixed 3 1 g z θ|)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable
            (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          have h := delicate_aesm_weight_mul (α := α) (v := fun _ : ℝ => (1 : ℝ))
            continuousOn_const
          simpa only [mul_one] using h
        have h3 : MeasureTheory.AEStronglyMeasurable
            (fun θ => |Work.Spaces.mixed 3 1 g z θ|)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          have hcont : ContinuousOn (fun θ => |Work.Spaces.mixed 3 1 g z θ|)
              (Set.Ioo 0 (π / 2)) :=
            ((hquad.mixed 3 1).curry_θ (by
              have hz0 : (0 : ℝ) < z := hz
              simp only [Set.mem_Ioi]
              linarith)).continuousOn.abs
          rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
          exact hcont.aestronglyMeasurable measurableSet_Ioo
        exact (h1.mul hΨaesm).mul h3
      have hdomInt : MeasureTheory.IntegrableOn
          (fun θ => (1 / 2) * ((Work.Spaces.w z) ^ 2 * Φ z)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
              + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2)) Work.Spaces.Iθ :=
        (hPsiInt.add (hQslice z (le_of_lt hz0))).const_mul _
      have hIntM : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.w z) ^ 2 * Φ z
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
              * |Work.Spaces.mixed 3 1 g z θ|)) Work.Spaces.Iθ := by
        refine hdomInt.mono' ?_ ?_
        · refine (haesmS.const_mul ((Work.Spaces.w z) ^ 2 * Φ z)).congr ?_
          filter_upwards with θ
          ring
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hΦnn z hz))
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _) (Real.sqrt_nonneg _))
              (abs_nonneg _)))]
          have hσ0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
          have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
              = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            delicate_sq_half_rpow (x := Real.sin (2 * θ)) (β := Work.Spaces.gam α) hσ0
          have ham := delicate_amgm
            (a := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
            (b := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
              * |Work.Spaces.mixed 3 1 g z θ|) (t := 1) (by norm_num)
          have hrhs : (1 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * Real.sqrt (Ψ θ)) ^ 2
              + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * |Work.Spaces.mixed 3 1 g z θ|) ^ 2 / 1) / 2
              = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
            rw [mul_pow, mul_pow, hsq, Real.sq_sqrt (hΨnn θ), sq_abs]
            ring
          rw [hrhs] at ham
          have hcongr : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|
              = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * |Work.Spaces.mixed 3 1 g z θ|) := by
            rw [← hsq]
            ring
          have hinner : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|
              ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
            rw [hcongr]
            exact ham
          calc (Work.Spaces.w z) ^ 2 * Φ z
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|)
              ≤ (Work.Spaces.w z) ^ 2 * Φ z
                * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                  + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2) :=
                mul_le_mul_of_nonneg_left hinner (mul_nonneg (sq_nonneg _) (hΦnn z hz))
            _ = (1 / 2) * ((Work.Spaces.w z) ^ 2 * Φ z)
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                  + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by ring
      -- step (a): the θ-integral against the Hardy majorant
      have ha : (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (Work.Spaces.w z) ^ 2 * Φ z
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := by
        have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
            𝔉 z θ ≤ (Work.Spaces.w z) ^ 2 * Φ z
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|) := by
          filter_upwards [hgoodθ] with θ hθ
          obtain ⟨hθIoo, hθhardy⟩ := hθ
          have hsin : 0 < Real.sin (2 * θ) :=
            Real.sin_pos_of_pos_of_lt_pi (by show (0 : ℝ) < 2 * θ; linarith [hθIoo.1])
              (by show 2 * θ < Real.pi; linarith [hθIoo.2, Real.pi_pos])
          have hσle : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            delicate_rpow_neg_le hsin (Real.sin_le_one _) hqγ
          have hF : |Work.Spaces.mixed 3 0 f z θ| ≤ Φ z := by
            rw [Work.Spaces.mixed_zero_right]
            exact hΦge z hz θ hθIoo
          have hG : |Work.Spaces.mixed 1 1 g z θ| ≤ Real.sqrt (Ψ θ) := by
            rw [← Real.sqrt_sq_eq_abs]
            exact Real.sqrt_le_sqrt (hθhardy z hz)
          have h1 := delicate_mul_four_le (a := (Real.sin (2 * θ)) ^ (-q))
            (a' := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (b := |Work.Spaces.mixed 3 0 f z θ|) (b' := Φ z)
            (c := |Work.Spaces.mixed 1 1 g z θ|) (c' := Real.sqrt (Ψ θ))
            (d := |Work.Spaces.mixed 3 1 g z θ|) (d' := |Work.Spaces.mixed 3 1 g z θ|)
            hσle hF hG le_rfl (Real.rpow_nonneg (le_of_lt hsin) _) (abs_nonneg _)
            (abs_nonneg _) (abs_nonneg _)
            (Real.rpow_nonneg (le_of_lt hsin) _) (hΦnn z hz) (Real.sqrt_nonneg _)
          have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
          calc 𝔉 z θ = (Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-q) * |Work.Spaces.mixed 3 0 f z θ|
                  * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|) := by
                rw [h𝔉def]; ring
            _ ≤ (Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Φ z
                  * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := h2
            _ = (Work.Spaces.w z) ^ 2 * Φ z
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|) := by ring
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => h𝔉nn z θ hθ)) hIntM hpt
      -- step (b): the angular Cauchy–Schwarz
      have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|)
          ≤ Real.sqrt (I4 * Q z) := by
        refine delicate_le_sqrt_mul hI4nn (hQnn z) (fun r hr => ?_)
        have hdomInt : MeasureTheory.IntegrableOn
            (fun θ => (1 / 2) * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
              + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r)) Work.Spaces.Iθ :=
          ((hPsiInt.const_mul r).add ((hQslice z (le_of_lt hz0)).div_const r)).const_mul (1 / 2)
        have hmono : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|)
            ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2)
              * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) := by
          refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ hθ => ?_) (fun θ hθ => ?_)
            hdomInt
          · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _) (Real.sqrt_nonneg _))
              (abs_nonneg _)
          · have hσ0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
            have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
                = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              delicate_sq_half_rpow (x := Real.sin (2 * θ)) (β := Work.Spaces.gam α) hσ0
            have ham := delicate_amgm
              (a := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
              (b := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * |Work.Spaces.mixed 3 1 g z θ|) (t := r) hr
            have hrhs : (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * Real.sqrt (Ψ θ)) ^ 2
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * |Work.Spaces.mixed 3 1 g z θ|) ^ 2 / r) / 2
                = (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := by
              rw [mul_pow, mul_pow, hsq, Real.sq_sqrt (hΨnn θ), sq_abs]
            rw [hrhs] at ham
            have hcongr : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                    * |Work.Spaces.mixed 3 1 g z θ|) := by
              rw [← hsq]
              ring
            have hinner : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                ≤ (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := by
              rw [hcongr]
              exact ham
            calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                ≤ (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := hinner
              _ = (1 / 2) * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) := by ring
        have hval : (∫ θ in Work.Spaces.Iθ, (1 / 2)
              * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r))
            = (r * I4 + Q z / r) / 2 := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_add (hPsiInt.const_mul r) ((hQslice z (le_of_lt hz0)).div_const r),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_div, hI4def, hQdef]
          ring
        linarith [hmono, hval]
      -- step (c): the radial Young inequality
      have hc : (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z)
          ≤ (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
        have hprod := delicate_amgm
          (a := Work.Spaces.w z * Φ z) (b := Work.Spaces.w z * Real.sqrt (I4 * Q z)) ht
        have e1 : (Work.Spaces.w z * Φ z) ^ 2 = (Φ z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
        have e2 : (Work.Spaces.w z * Real.sqrt (I4 * Q z)) ^ 2
            = I4 * ((Work.Spaces.w z) ^ 2 * Q z) := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hI4nn (hQnn z))]
          ring
        have e3 : (Work.Spaces.w z * Φ z) * (Work.Spaces.w z * Real.sqrt (I4 * Q z))
            = (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z) := by ring
        rwa [e1, e2, e3] at hprod
      calc (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (Work.Spaces.w z) ^ 2 * Φ z
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := ha
        _ ≤ (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z) :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (hΦnn z hz))
        _ ≤ _ := hc
    -- integrate the pointwise-in-`z` bound
    have hIntG : MeasureTheory.IntegrableOn
        (fun z => (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2) Work.Spaces.Iz := by
      have h1 : MeasureTheory.IntegrableOn
          (fun z => t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
        hΦInt.const_mul t
      have h2 : MeasureTheory.IntegrableOn
          (fun z => I4 * ((Work.Spaces.w z) ^ 2 * Q z)) Work.Spaces.Iz :=
        MeasureTheory.IntegrableOn.congr_fun (hQint.const_mul I4)
          (fun z _ => rfl) measurableSet_Ici
      exact (h1.add (h2.div_const t)).div_const 2
    have hzm : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
        ≤ ∫ z in Work.Spaces.Iz, (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z => MeasureTheory.setIntegral_nonneg
          measurableSet_Icc (fun θ hθ => h𝔉nn z θ hθ))) hIntG ?_
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hPtwise z hz
    have hval : (∫ z in Work.Spaces.Iz, (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2) = (t * A + (I4 * Bq) / t) / 2 := by
      have h1 : MeasureTheory.IntegrableOn
          (fun z => t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
        hΦInt.const_mul t
      have h2 : MeasureTheory.IntegrableOn
          (fun z => I4 * ((Work.Spaces.w z) ^ 2 * Q z)) Work.Spaces.Iz :=
        MeasureTheory.IntegrableOn.congr_fun (hQint.const_mul I4)
          (fun z _ => rfl) measurableSet_Ici
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add h1 (h2.div_const t),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
        MeasureTheory.integral_const_mul, ← hAdef, ← hBqdef]
    linarith [hzm, hval]
  -- the final arithmetic
  have hfin2 := delicate_le_sqrt_mul hAnn (mul_nonneg hI4nn hBqnn) hmain
  have hHkg : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hK : 0 ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f :=
    add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.FTS.TransportS.coefTh_nonneg 1 f)
  have hXnK : Work.Spaces.HkNorm α 4 f
      ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f := by
    rw [Work.FTS.Nonlin.Xn]
    linarith [Work.FTS.TransportS.coefTh_nonneg 1 f]
  -- `√(CΦ/(γ-1)) = √(10 CΦ) · α^{-1/2}`
  have hsqα : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) = α ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hα]
    norm_num
  have hsqrtgam : Real.sqrt (CΦ / (Work.Spaces.gam α - 1))
      = Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ)) := by
    rw [Work.Spaces.gam_sub_one]
    have h1 : CΦ / (α / 10)
        = (Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), sq, hsqα, Real.rpow_neg_one]
      field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hsq_le : Real.sqrt (10 * CΦ) ≤ 10 * CΦ + 1 := by
    have h0 : 0 ≤ 10 * CΦ := by positivity
    have h1 : (Real.sqrt (10 * CΦ)) ^ 2 = 10 * CΦ := Real.sq_sqrt h0
    nlinarith [sq_nonneg (Real.sqrt (10 * CΦ) - 1 / 2), Real.sqrt_nonneg (10 * CΦ)]
  -- the `√`-bound
  have hsqrt_le : Real.sqrt (A * (I4 * Bq))
      ≤ Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
        * Work.Spaces.HkSq α 4 g := by
    have h1 : I4 * Bq ≤ Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g :=
      mul_le_mul hI4le hBqle hBqnn hHkg
    have h2 : A * (I4 * Bq) ≤ (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
        * (Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g) :=
      mul_le_mul hA0 h1 (mul_nonneg hI4nn hBqnn)
        (mul_nonneg (div_nonneg hCΦpos.le hγ1pos.le) (Work.Spaces.HkSq_nonneg α 4 f))
    have h3 : (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
        * (Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g)
        = ((CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Work.Spaces.HkSq α 4 g ^ 2) := by ring
    rw [h3] at h2
    calc Real.sqrt (A * (I4 * Bq))
        ≤ Real.sqrt ((CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Work.Spaces.HkSq α 4 g ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Real.sqrt (Work.Spaces.HkSq α 4 g ^ 2) := by
          rw [Real.sqrt_mul (mul_nonneg (div_nonneg hCΦpos.le hγ1pos.le)
            (Work.Spaces.HkSq_nonneg α 4 f))]
      _ = Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g := by
          rw [Real.sqrt_mul (div_nonneg hCΦpos.le hγ1pos.le), Real.sqrt_sq hHkg,
            Work.Spaces.HkNorm]
  -- the remaining arithmetic
  have hstep : Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
        * Work.Spaces.HkSq α 4 g
      ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
    rw [hsqrtgam]
    have h1 : Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g
        ≤ (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
      nlinarith [hsq_le, hrp, Work.Spaces.HkNorm_nonneg α 4 f, hHkg,
        mul_nonneg (mul_nonneg hrp (Work.Spaces.HkNorm_nonneg α 4 f)) hHkg]
    have h2 : (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g
        ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
      have hC1 : 0 ≤ 10 * CΦ + 1 := by positivity
      have hC2 : 0 ≤ 10 * CΦ + 2 := by positivity
      have hle : (10 * CΦ + 1) * Work.Spaces.HkNorm α 4 f ≤ (10 * CΦ + 2)
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
        nlinarith [hXnK, hC1, hC2, Work.Spaces.HkNorm_nonneg α 4 f, hK]
      calc (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g
          = α ^ (-(1 / 2 : ℝ)) * ((10 * CΦ + 1) * Work.Spaces.HkNorm α 4 f)
            * Work.Spaces.HkSq α 4 g := by ring
        _ ≤ α ^ (-(1 / 2 : ℝ)) * ((10 * CΦ + 2)
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f))
            * Work.Spaces.HkSq α 4 g := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hrp) hHkg
        _ = (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
            ring
    linarith [h1, h2]
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
      ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g :=
    le_trans hfin2 (le_trans hsqrt_le hstep)
  simpa only [h𝔉def] using hgoal

end Work.FTS.TransportS.T2Sup
