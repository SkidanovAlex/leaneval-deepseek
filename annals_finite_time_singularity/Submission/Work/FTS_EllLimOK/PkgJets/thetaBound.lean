import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `thetaBound`: the `ℋ⁰`-bound for the singular part `Θ/cos θ`

The target is

```
∃ C > 0, ∀ g, ClassC α g → HkMem α 0 (Θ α g / cos θ) ∧
                              HkSq α 0 (Θ α g / cos θ) ≤ C · (1 + Xn₆ α g)²
```

where `Θ α g z θ = (1/(4α)) sin(2θ) L₁₂(g)(z)` is the singular part of the stream function
(`Work.Construction.Theta`) and `Xn₆ α g = |g|_{ℋ⁶}`.

## The route

Since `Θ α g z θ / cos θ = (1/(4α))·(sin 2θ/cos θ)·L₁₂ g z` factorises as a function of `θ`
times a function of `z`, and since the level-`0` `ℋ`-integrand is the single square

`HkIntegrand α 0 F z θ = (F z θ · w z / sin(2θ)^{η/2})²`,

the whole estimate reduces to a one-dimensional (radial) bound for `L₁₂ g`:

`∫_z (L₁₂ g z)² w(z)² dz ≤ 107 · BK² · HkSq α 4 g`.

This is Elgindi's lemma `|L₁₂(f)w|_{L²} ≤ 4|fw|_{L²}` (paper, §'The singular term'), in the
form proved in the workspace: the two `z`-halves are the weighted Hardy inequalities
`Work.Elliptic.HardyLeftW` / `HardyRightW` (constant `107`), assembled exactly as in
`Work.Elliptic.L12k0`; the angular Cauchy–Schwarz step is
`Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le`, whose constant is `BK² = ∫_θ (K θ sin(2θ)^{η/2})²`.

The two inputs — the analytic facts about `L₁₂ g` (integrability of the density, the derivative,
continuity on `[0,1]`, decay at `∞`) and the angular Cauchy–Schwarz bound for `FK g` — are taken
as hypotheses of `thetaBound_of_facts` and discharged from `ClassC` by the sibling modules
`PkgJets.L12_classC_facts` and `PkgJets.FK_w_sq_bound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false

/-! ## §1  `Qang g 0` is the angular moment `FK g` -/

/-- `Qang g 0 z = ∫_θ K(θ)·g z θ` is the angular moment `FK g z = ∫_θ g z θ·K(θ)`
(the two integrands differ only by the order of the factors). -/
theorem Qang_zero_eq_FK (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang g 0 z = Work.Construction.FK g z := by
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  simp only [Work.Spaces.DzIter_zero]
  rw [show Work.Elliptic.Ktheta = Work.Spaces.K from rfl]
  ring

/-! ## §2  The weighted `L²`-bound for `L₁₂ g` -/

/-- `L₁₂dens g z = FK g z / z` (the angular density is the angular moment divided by `z`). -/
theorem L12dens_eq_FK_div (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.L12dens g z = Work.Construction.FK g z / z := by
  rw [show Work.Construction.L12dens g z = Work.Elliptic.L12dens g z from rfl,
    Work.Elliptic.L12dens_eq_Qang_div, Qang_zero_eq_FK]

/-- **The weighted `L²`-bound for `L₁₂ g`** (Elgindi's lemma `|L₁₂(f)w|_{L²} ≤ C|fw|_{L²}`,
with the constant `107` of the workspace's Hardy inequalities).  This is
`Work.Elliptic.L12k0` with the unused hypotheses dropped and the angular moment written
`Work.Construction.FK`. -/
theorem L12_w_sq_bound {g : ℝ → ℝ → ℝ}
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
      (-(Work.Construction.L12dens g z)) z)
    (hcont : ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Icc 0 1))
    (htend : Filter.Tendsto (fun z => Work.Construction.L12 g z) Filter.atTop (nhds 0))
    (h0 : Work.Construction.L12 g 0 = 0)
    (hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Work.Spaces.Iz,
          (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  have hderivU : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Construction.L12 g z)
        (-((fun z => Work.Construction.FK g z) z / z)) z := by
    intro z hz
    have h := hderiv z hz
    rw [L12dens_eq_FK_div g z] at h
    exact h
  have hderiv01 : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun z => Work.Construction.L12 g z)
        (-((fun z => Work.Construction.FK g z) z / z)) z :=
    fun z hz => hderivU z hz.1
  have hderiv1 : ∀ z ∈ Set.Ioi (1 : ℝ),
      HasDerivAt (fun z => Work.Construction.L12 g z)
        (-((fun z => Work.Construction.FK g z) z / z)) z :=
    fun z hz => hderivU z (lt_trans one_pos hz)
  have hQIoo : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) :=
    hQint.mono_set (show Set.Ioo (0 : ℝ) 1 ⊆ Work.Spaces.Iz from
      fun z hz => show (0 : ℝ) ≤ z from le_of_lt hz.1)
  have hQIoi : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) :=
    hQint.mono_set (show Set.Ioi (1 : ℝ) ⊆ Work.Spaces.Iz from
      fun z hz => show (0 : ℝ) ≤ z from le_of_lt (lt_trans one_pos hz))
  obtain ⟨hIntL, hBoundL⟩ := Work.Elliptic.HardyLeftW (fun z => Work.Construction.FK g z)
    (fun z => Work.Construction.L12 g z) hderiv01 hcont h0 hQIoo
  obtain ⟨hIntR, hBoundR⟩ := Work.Elliptic.HardyRightW (fun z => Work.Construction.FK g z)
    (fun z => Work.Construction.L12 g z) hderiv1 htend hQIoi
  have hae : (Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi 1) =ᵐ[volume] Work.Spaces.Iz :=
    Work.Elliptic.Ioo_union_Ioi_ae_eq_Iz
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ioi 1) :=
    Set.disjoint_left.mpr (fun a ha hb => absurd (lt_trans ha.2 hb) (lt_irrefl a))
  have hvalU : (∫ z in Work.Spaces.Iz, (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1,
          (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1 : ℝ),
            (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIntL hIntR
  have hvalf : (∫ z in Work.Spaces.Iz, (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1,
          (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + ∫ z in Set.Ioi (1 : ℝ),
            (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [← MeasureTheory.setIntegral_congr_set hae]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hQIoo hQIoi
  have hIntAll : MeasureTheory.IntegrableOn
      (fun z => (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.integrableOn_congr_set_ae hae).mp (hIntL.union hIntR)
  refine ⟨hIntAll, ?_⟩
  rw [hvalU, hvalf]
  linarith [hBoundL, hBoundR]

/-! ## §3  The angular factor `sin 2θ / cos θ = 2 sin θ` and its consequences -/

/-- On the angular interval, the squared level-`0` weight factorises into `w²·sin(2θ)^{-η}`. -/
theorem wdivsin_sq_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [div_pow]
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [show (2 : ℕ) = 2 from rfl, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hs]
    ring_nf
  rw [h1, div_eq_mul_inv, ← Real.rpow_neg hs]

/-- `(sin 2θ / cos θ)² ≤ 4` for **every** `θ` (no hypothesis): either `cos θ = 0`, where the
junk value of the division is `0`, or `sin 2θ/cos θ = 2 sin θ`. -/
theorem s2_div_cos_sq_le (θ : ℝ) : (Work.Construction.s2 θ / Real.cos θ) ^ 2 ≤ 4 := by
  rcases eq_or_ne (Real.cos θ) 0 with h | h
  · rw [h, div_zero]
    norm_num
  · rw [← sq_abs, abs_div, div_pow]
    have hb : 0 < |Real.cos θ| := abs_pos.mpr h
    have hnum : |Work.Construction.s2 θ| ≤ 2 * |Real.cos θ| := by
      rw [Work.Construction.s2, Real.sin_two_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have hc : 0 ≤ |Real.cos θ| := abs_nonneg _
      nlinarith
    calc (|Work.Construction.s2 θ|) ^ 2 / (|Real.cos θ|) ^ 2
        ≤ (2 * |Real.cos θ|) ^ 2 / (|Real.cos θ|) ^ 2 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hnum 2) (by positivity)
      _ = 4 := by
          field_simp
          ring

/-- **The pointwise bound for the level-`0` integrand of `Θ α g / cos θ`.** -/
theorem HkIntegrand_zero_le {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ
      ≤ (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [hkIntegrand_zero_eq]
  have hf : Work.Construction.Theta α g z θ / Real.cos θ
      = (1 / (4 * α)) * Work.Construction.L12 g z * (Work.Construction.s2 θ / Real.cos θ) := by
    simp only [Work.Construction.Theta]
    ring
  rw [hf]
  have hX : 0 ≤ (1 / (4 * α)) ^ 2 * (Work.Construction.L12 g z) ^ 2 := by positivity
  have hY : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine mul_nonneg (sq_nonneg _) ?_
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  calc (1 / (4 * α) * Work.Construction.L12 g z * (Work.Construction.s2 θ / Real.cos θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((1 / (4 * α)) ^ 2 * (Work.Construction.L12 g z) ^ 2)
        * (Work.Construction.s2 θ / Real.cos θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [mul_pow, mul_pow, wdivsin_sq_eq hθ]; ring
    _ ≤ ((1 / (4 * α)) ^ 2 * (Work.Construction.L12 g z) ^ 2) * 4
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (s2_div_cos_sq_le θ) hX) hY
    _ = (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-- Continuity of the level-`0` integrand of `Θ α g / cos θ` on the open quadrant. -/
theorem continuousOn_HkIntegrand_theta_div_cos {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hL : ContinuousOn (fun z : ℝ => Work.Construction.L12 g z) (Set.Ioi 0)) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hred : ContinuousOn
      (fun p : ℝ × ℝ => (1 / (2 * α)) * Real.sin p.2 * Work.Construction.L12 g p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · exact (Real.continuous_sin.continuousOn).comp continuousOn_snd
        (fun p _ => Set.mem_univ _)
    · exact hL.comp continuousOn_fst (fun p hp => hp.1)
  have hwt : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hspos : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2),
        0 < Real.sin (2 * p.2) := fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
    refine ContinuousOn.div ?_ ?_ ?_
    · simp only [Work.Spaces.w]
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
    · exact ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hspos p hp)))
    · intro p hp
      exact ne_of_gt (Real.rpow_pos_of_pos (hspos p hp) _)
  refine ((hred.mul hwt).pow 2).congr ?_
  intro p hp
  show Work.Spaces.HkIntegrand α 0
      (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) p.1 p.2
    = (((1 / (2 * α)) * Real.sin p.2 * Work.Construction.L12 g p.1)
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2
  rw [hkIntegrand_zero_eq]
  have hid : Work.Construction.Theta α g p.1 p.2 / Real.cos p.2
      = (1 / (2 * α)) * Real.sin p.2 * Work.Construction.L12 g p.1 := by
    have hcos : Real.cos p.2 ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2, Real.pi_pos]⟩)
    simp only [Work.Construction.Theta, Work.Construction.s2]
    rw [Real.sin_two_mul]
    field_simp
    ring
  rw [hid]

/-! ## §4  The assembly -/

/-- **The main estimate, from the two `ClassC`-inputs.**

`hL12f` is the bundle of analytic facts about `L₁₂ g` (integrability of the density, the
derivative, continuity on `[0,1]`, decay at `∞`) and `hFKf` the angular Cauchy–Schwarz bound for
the moment `FK g`.  Both are discharged from `Work.FTS.ClassC.ClassC α g` by the sibling modules
`PkgJets.L12_classC_facts` and `PkgJets.FK_w_sq_bound`. -/
theorem thetaBound_of_facts {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hL12f : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
        (-(Work.Construction.L12dens g z)) z) ∧
      ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Icc 0 1) ∧
      Filter.Tendsto (fun z => Work.Construction.L12 g z) Filter.atTop (nhds 0))
    (hFKf : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      MeasureTheory.IntegrableOn
        (fun z => (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Construction.FK g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
        ≤ C * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
  have hsinEta : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  set Jη : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hJη
  have hJηnn : 0 ≤ Jη := by
    rw [hJη]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hc0pos : 0 < (1 / (4 * α)) ^ 2 * 4 := by positivity
  refine ⟨(1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2) + 1, by positivity, ?_⟩
  intro g hg
  obtain ⟨hL12int, hderiv, hcont, htend⟩ := hL12f g hg
  obtain ⟨hQint, hFKbound⟩ := hFKf g hg
  have hmem6 : Work.Spaces.HkMem α 6 g := HkMem_mono_le hg.reg (by norm_num) hg.mem
  have hL12 := L12_w_sq_bound hderiv hcont htend hg.l12 hQint
  -- ## the radial bound, with `Xn₆` on the right
  have hX6 : Work.Spaces.HkSq α 4 g ≤ (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
    have h := HkSq_mono_le (α := α) (f := g) (m := 4) (k := 6) (by norm_num) hmem6
    have h6 : Work.Spaces.HkSq α 6 g = (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
      show Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)]
    linarith [h, h6.le]
  have hKey2 : (∫ z in Work.Spaces.Iz, (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (Work.FTS.GalBasis.cc.BK ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) := by
    have hBK : 0 ≤ Work.FTS.GalBasis.cc.BK ^ 2 := sq_nonneg _
    have h2 : 107 * (Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g)
        ≤ 107 * (Work.FTS.GalBasis.cc.BK ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX6 hBK) (by norm_num)
    have h1 : (∫ z in Work.Spaces.Iz, (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g) :=
      le_trans hL12.2 (mul_le_mul_of_nonneg_left hFKbound (by norm_num))
    linarith [h1, h2]
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  -- ## the majorant: slice integrability and the `z`-integral
  have hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    intro z _
    exact hsinEta.const_mul
      ((1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2))
  have hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz := by
    have hval : (fun z => ∫ θ in Work.Spaces.Iθ,
          (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun z => ((1 / (4 * α)) ^ 2 * 4 * Jη)
            * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      funext z
      rw [MeasureTheory.integral_const_mul, ← hJη]
      ring
    rw [hval]
    exact hL12.1.const_mul _
  -- ## membership
  have hLcontIoi : ContinuousOn (fun z : ℝ => Work.Construction.L12 g z) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  have hcontHk := continuousOn_HkIntegrand_theta_div_cos hα hLcontIoi
  refine ⟨Work.FTS.LocData.HkMem_of_majorant α 0 hcontHk hMslice hMz ?_, ?_⟩
  · intro z hz θ hθ
    exact HkIntegrand_zero_le hα g z θ hθ
  -- ## the value bound
  have hJηval : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        (1 / (4 * α)) ^ 2 * 4 * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (1 / (4 * α)) ^ 2 * 4
          * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) * Jη := by
    intro z
    rw [MeasureTheory.integral_const_mul, ← hJη]
  have houter : Work.Spaces.HkSq α 0
      (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
      ≤ ∫ z in Work.Spaces.Iz, (1 / (4 * α)) ^ 2 * 4
          * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) * Jη := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
    · rw [show (fun z => (1 / (4 * α)) ^ 2 * 4
              * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) * Jη)
            = fun z => ((1 / (4 * α)) ^ 2 * 4 * Jη)
              * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) from by
          funext z; ring]
      exact hL12.1.const_mul _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hinner : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
          ≤ ∫ θ in Work.Spaces.Iθ,
              (1 / (4 * α)) ^ 2 * 4
                * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
          (hMslice z hz)
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => HkIntegrand_zero_le hα g z θ hθ))
      rw [hJηval z] at hinner
      exact hinner
  have hstepval : (∫ z in Work.Spaces.Iz, (1 / (4 * α)) ^ 2 * 4
        * ((Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) * Jη)
      = ((1 / (4 * α)) ^ 2 * 4 * Jη)
        * (∫ z in Work.Spaces.Iz, (Work.Construction.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
    ring
  have hbound : Work.Spaces.HkSq α 0
      (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
      ≤ ((1 / (4 * α)) ^ 2 * 4 * Jη)
          * (107 * (Work.FTS.GalBasis.cc.BK ^ 2
            * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2)) := by
    refine le_trans houter ?_
    rw [hstepval]
    refine mul_le_mul_of_nonneg_left hKey2 ?_
    exact mul_nonneg (by positivity) hJηnn
  -- ## the constant comparison
  have hx2 : (Work.FTS.StrongGlobal.Xn6 α g) ^ 2
      ≤ (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by nlinarith [hXnn]
  have h1nn : (0 : ℝ) ≤ (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by positivity
  have hcnn : 0 ≤ (1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2) := by
    positivity
  have hfinal : ((1 / (4 * α)) ^ 2 * 4 * Jη) * (107 * (Work.FTS.GalBasis.cc.BK ^ 2
        * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2))
      ≤ ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2) + 1)
        * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
    have e : ((1 / (4 * α)) ^ 2 * 4 * Jη) * (107 * (Work.FTS.GalBasis.cc.BK ^ 2
          * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2))
        = ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2))
          * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by ring
    rw [e]
    have h1 : ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2))
          * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2
        ≤ ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2))
          * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 :=
      mul_le_mul_of_nonneg_left hx2 hcnn
    have h2 : ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2))
          * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2
        ≤ ((1 / (4 * α)) ^ 2 * 4 * Jη * (107 * Work.FTS.GalBasis.cc.BK ^ 2) + 1)
          * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
      nlinarith [h1nn]
    linarith [h1, h2]
  exact le_trans hbound hfinal

theorem thetaBound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.Spaces.HkMem α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) ∧
      Work.Spaces.HkSq α 0 (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ)
        ≤ C * (1 + Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
  exact thetaBound_of_facts hα hα1
    (fun g hg => L12_classC_facts hg)
    (fun g hg => FK_w_sq_bound hg)

end Work.FTS_EllLimOK.PkgJets
