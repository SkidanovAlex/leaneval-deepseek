import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.iter_swap_compact
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.aeI1Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `zibp_zouter` — the radial integration by parts against the angular weight

`AeI1Fts.zibp_cut` proves, for every fixed `θ ∈ (0,π/2)`, the cut-off radial integration by
parts

  `∫_z χ_n w² Fp u(·,θ) = -∫_z (z χ_n') (z∂_zu)(∂_θθu) w²`,

where `χ_n = EllipticEst.cut n` is supported in `[1/(n+1), 3(n+1)]`.  The target of this module
multiplies that identity by the angular weight `σ θ · χ_ε θ` (`σ = sigE = sin(2θ)^{-η}`,
`χ_ε = SliceMixedAux.cut ε`, supported in `[ε/2, π/2 - ε/2]`), integrates over `θ ∈ (0,π/2)`
and interchanges the two integrations:

  `∫_z χ_n w² ∫_θ σ χ_ε Fp u = -∫_z (z χ_n') w² ∫_θ σ χ_ε (U u · BB u)`.

Both `θ`-integrands are supported in the compact box
`[1/(2(n+1)), 4(n+1)] ×ˢ [ε/2, π/2 - ε/2]` lying in the open quadrant, where they are
continuous (`SmoothOpen u` makes every derivative slot used by `Fp` continuous), so the swap is
`iter_swap_compact`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **Swapping the two integrations, with the angular factor pulled out of the inner integral.**

If the integrand `K z · (ρ θ · f z θ)` vanishes off the box `[a,b] ×ˢ [c,d]` (`0 < a`,
`c ≤ d < π/2`) and is continuous there, then the `z`-outer iterated integral with the `θ`-factor
`ρ` pulled out equals the `θ`-outer one.  This is `iter_swap_compact` followed by the two
`integral_const_mul` pull-outs. -/
theorem iter_swap_pull {K ρ : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 * (ρ p.2 * f p.1 p.2))
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hzero : ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → K z * (ρ θ * f z θ) = 0) :
    (∫ z in Set.Ioi 0, K z * (∫ θ in Set.Ioo 0 (Real.pi / 2), ρ θ * f z θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), ρ θ * (∫ z in Set.Ioi 0, K z * f z θ) := by
  have hswap : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), K z * (ρ θ * f z θ))
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, K z * (ρ θ * f z θ) :=
    iter_swap_compact ha hab hc hcd hd hcont hzero
  rw [show (∫ z in Set.Ioi 0, K z * (∫ θ in Set.Ioo 0 (Real.pi / 2), ρ θ * f z θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), K z * (ρ θ * f z θ) from
    setIntegral_congr_fun measurableSet_Ioi (fun z _ =>
      (MeasureTheory.integral_const_mul (K z) (fun θ => ρ θ * f z θ)).symm)]
  rw [hswap]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [show (∫ z in Set.Ioi 0, K z * (ρ θ * f z θ))
      = ∫ z in Set.Ioi 0, ρ θ * (K z * f z θ) from
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  exact MeasureTheory.integral_const_mul (ρ θ) (fun z => K z * f z θ)

/-! ## Elementary continuity facts on a compact box inside the open quadrant -/

/-- The square of the radial weight is continuous on a compact interval of `(0,∞)`. -/
private theorem continuousOn_wSq_Icc {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) := by
  have h : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1))
  exact h.pow 2

/-- The angular weight `σ = sigE = sin(2θ)^{-η}` is continuous on `[c,d]` for
`0 < c ≤ d < π/2`. -/
private theorem continuousOn_sigE_Icc {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn sigE (Set.Icc c d) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc c d) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine (hsin.rpow_const (p := -(Work.Spaces.eta)) ?_).congr ?_
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hc])
      (by linarith [hθ.2, hd, Real.pi_pos]))
  · intro θ _
    rfl

/-- `Fp u` is continuous on any compact box inside the open quadrant. -/
private theorem continuousOn_fp_Icc {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun p : ℝ × ℝ => Fp u p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hu3 : ContDiffOn ℝ 3 (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hS.forall 3
  have hb : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Dispatch.ftsQd := by
    rintro p ⟨hp1, hp2⟩
    exact ⟨lt_of_lt_of_le ha hp1.1, lt_of_lt_of_le hc hp2.1, lt_of_le_of_lt hp2.2 hd⟩
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pzIter_two hu3).mono hb
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pthIter_two hu3).mono hb
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pz hu3).mono hb
  have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pz_pthIter_two hu3).mono hb
  have hcw : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.cw p.1)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
    show ContinuousOn (fun p : ℝ × ℝ => 2 * (p.1 - 1) / (1 + p.1))
      (Set.Icc a b ×ˢ Set.Icc c d)
    refine ContinuousOn.div (continuousOn_const.mul (continuousOn_fst.sub continuousOn_const))
      (continuousOn_const.add continuousOn_fst) ?_
    intro p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    linarith
  have hU : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.mul h3).congr (fun p _ => rfl)
  have hZ : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.mul h4).congr (fun p _ => rfl)
  have hT1 : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2 * Work.Spaces.pthIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (((continuousOn_fst.pow 2).mul h1).mul h2).congr (fun p _ => rfl)
  have hT2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.EllipticEst.AngSecond.cw p.1 * (p.1 * Work.Spaces.pz u p.1 p.2)
        * Work.Spaces.pthIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((hcw.mul hU).mul h2).congr (fun p _ => rfl)
  have hT3 : ContinuousOn (fun p : ℝ × ℝ =>
      (p.1 * Work.Spaces.pz u p.1 p.2)
        * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 u) p.1 p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hU.mul hZ).congr (fun p _ => rfl)
  refine ((hT1.add hT2).add hT3).congr (fun p _ => ?_)
  simp only [Fp, Pi.add_apply]

/-- `U u · BB u = (z∂_zu)·∂_θθu` is continuous on any compact box inside the open quadrant. -/
private theorem continuousOn_UBB_Icc {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun p : ℝ × ℝ => U u p.1 p.2 * BB u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hu3 : ContDiffOn ℝ 3 (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hS.forall 3
  have hb : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Dispatch.ftsQd := by
    rintro p ⟨hp1, hp2⟩
    exact ⟨lt_of_lt_of_le ha hp1.1, lt_of_lt_of_le hc hp2.1, lt_of_le_of_lt hp2.2 hd⟩
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pz hu3).mono hb
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Work.FTS.EllipticEst.Dispatch.continuousOn_uncurry_pthIter_two hu3).mono hb
  have hU : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.mul h1).congr (fun p _ => rfl)
  exact (hU.mul h2).congr (fun p _ => rfl)

/-! ## Vanishing of the two cut-offs off their bands -/

private theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  simpa using hEq.deriv_eq

private theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  simpa using hEq.deriv_eq

/-! ## The target -/

theorem zibp_zouter {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ Real.pi / 2) :
    (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
            * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = - (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ)) := by
  -- the box supporting both integrands
  set a : ℝ := 1 / (2 * (n + 1 : ℝ)) with ha_def
  set b : ℝ := 4 * (n + 1 : ℝ) with hb_def
  set c : ℝ := ε / 2 with hc_def
  set d : ℝ := Real.pi / 2 - ε / 2 with hd_def
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have ha : 0 < a := by rw [ha_def]; positivity
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (n + 1 : ℝ) := by linarith
    linarith
  have hhalf : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
    one_div_le_one_div_of_le hn (by linarith)
  have hc : 0 < c := by rw [hc_def]; linarith
  have hcd : c ≤ d := by rw [hc_def, hd_def]; linarith
  have hd : d < Real.pi / 2 := by rw [hd_def]; linarith
  -- the cut-offs vanish off their bands
  have hcut_zero : ∀ z : ℝ, z ∉ Set.Icc a b → Work.FTS.EllipticEst.cut n z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · rw [ha_def] at hzlt
      exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (by linarith)
    · rw [hb_def] at hzgt
      exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (by linarith)
  have hderiv_zero : ∀ z : ℝ, z ∉ Set.Icc a b →
      deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
    intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · rw [ha_def] at hzlt
      exact deriv_cut_eq_zero_of_lt n (by linarith)
    · rw [hb_def] at hzgt
      exact deriv_cut_eq_zero_of_gt n (by linarith)
  have hpsi_zero : ∀ θ : ℝ, θ ∉ Set.Icc c d → Work.FTS.EllipticEst.SliceMixedAux.cut ε θ = 0 := by
    intro θ hθ
    simp only [Set.mem_Icc, not_and_or, not_le] at hθ
    rcases hθ with hθlt | hθgt
    · rw [hc_def] at hθlt
      exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_low hε (by linarith)
    · rw [hd_def] at hθgt
      exact Work.FTS.EllipticEst.SliceMixedAux.cut_eq_zero_high hε (by linarith)
  -- continuity of the two integrands on the box
  have hχ : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst)).continuousOn
  have hW : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_wSq_Icc (a := a) (b := b) ha).comp continuousOn_fst (fun p hp => hp.1)
  have hsig : ContinuousOn (fun p : ℝ × ℝ => sigE p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_sigE_Icc hc hd).comp continuousOn_snd (fun p hp => hp.2)
  have hpsi : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    ((Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous.comp
      continuous_snd).continuousOn
  have hρ : ContinuousOn (fun p : ℝ × ℝ =>
      sigE p.2 * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) := hsig.mul hpsi
  have hFp := continuousOn_fp_Icc (a := a) (b := b) (c := c) (d := d) hS ha hc hd
  have hUBB := continuousOn_UBB_Icc (a := a) (b := b) (c := c) (d := d) hS ha hc hd
  have hderivcut : Continuous (deriv (Work.FTS.EllipticEst.cut n)) :=
    ((contDiff_infty_iff_deriv.mp (Work.FTS.EllipticEst.cut_contDiff n)).2).continuous
  have hzd : ContinuousOn (fun p : ℝ × ℝ => p.1 * deriv (Work.FTS.EllipticEst.cut n) p.1)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_fst.mul (hderivcut.comp continuous_fst).continuousOn)
  have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.FTS.EllipticEst.cut n p.1 * (Work.Spaces.w p.1) ^ 2)
        * ((sigE p.2 * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2) * Fp u p.1 p.2))
      (Set.Icc a b ×ˢ Set.Icc c d) := (hχ.mul hW).mul (hρ.mul hFp)
  have hcontG : ContinuousOn (fun p : ℝ × ℝ =>
      ((p.1 * deriv (Work.FTS.EllipticEst.cut n) p.1) * (Work.Spaces.w p.1) ^ 2)
        * ((sigE p.2 * Work.FTS.EllipticEst.SliceMixedAux.cut ε p.2)
            * (U u p.1 p.2 * BB u p.1 p.2)))
      (Set.Icc a b ×ˢ Set.Icc c d) := (hzd.mul hW).mul (hρ.mul hUBB)
  -- the two vanishing statements
  have hzeroF : ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
        * ((sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ) * Fp u z θ) = 0 := by
    intro z θ h
    rcases h with h | h
    · rw [hcut_zero z h]; ring
    · rw [hpsi_zero θ h]; ring
  have hzeroG : ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      (z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2
        * ((sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
            * (U u z θ * BB u z θ)) = 0 := by
    intro z θ h
    rcases h with h | h
    · rw [hderiv_zero z h]; ring
    · rw [hpsi_zero θ h]; ring
  -- the pointwise radial integration by parts
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * Fp u z θ)
        = - (∫ z in Set.Ioi 0,
            ((z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2)
              * (U u z θ * BB u z θ)) := by
    intro θ hθ
    have hz := zibp_cut (hS.forall 3) n hθ
    rw [hz]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    simp only [U, BB]
    ring
  -- the two Fubini swaps
  have hswapF := iter_swap_pull
    (K := fun z => Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
    (f := fun z θ => Fp u z θ) ha hab hc hcd hd hcontF hzeroF
  have hswapG := iter_swap_pull
    (K := fun z => (z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2)
    (ρ := fun θ => sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ)
    (f := fun z θ => U u z θ * BB u z θ) ha hab hc hcd hd hcontG hzeroG
  calc (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
        * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
            * Work.FTS.EllipticEst.AeI1Fts.Fp u z θ)
      = ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
          * (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z
              * (Work.Spaces.w z) ^ 2 * Fp u z θ) := hswapF
    _ = ∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
          * (-(∫ z in Set.Ioi 0,
              ((z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2)
                * (U u z θ * BB u z θ))) := by
          refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
          rw [hpt θ hθ]
    _ = - (∫ θ in Set.Ioo 0 (Real.pi / 2), sigE θ
            * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
            * (∫ z in Set.Ioi 0,
                ((z * deriv (Work.FTS.EllipticEst.cut n) z) * (Work.Spaces.w z) ^ 2)
                  * (U u z θ * BB u z θ))) := by
          rw [← MeasureTheory.integral_neg]
          refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)
    _ = - (∫ z in Set.Ioi 0, (z * deriv (Work.FTS.EllipticEst.cut n) z)
            * (Work.Spaces.w z) ^ 2
          * ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeI1Fts.sigE θ
              * Work.FTS.EllipticEst.SliceMixedAux.cut ε θ
              * (Work.FTS.EllipticEst.AeI1Fts.U u z θ
                  * Work.FTS.EllipticEst.AeI1Fts.BB u z θ)) := by
          rw [hswapG]

end

end Work.FTS.EllipticEst.AeI1Fts
