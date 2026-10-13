/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular-moment chain `F_*(D_z^j Ψ) ≡ 0` (`j ≤ 3`), adapted to the `a.e.` weak class

This module is a self-contained copy of `Submission/Work/FTS/EllipticEst/H2W/Fstar_DzIter_le_Psi.lean`
(namespace `Work.FTS.EllipticEst.H2W`) into the private namespace `Work.H2W.MomentAe`, with the
**base case of the moment induction adapted to the current definition of `TT.EllWeakPos`**, whose two
moment conditions are `a.e.` in `z` rather than pointwise.

The declarations `ae_Ioo_mem` … `level_step` are byte-identical copies of the originals (they never
use the moment conditions); only the final theorem `Fstar_DzIter_le_Psi` is reproved here: the
`j = 0` moment `F_*Ψ` is *continuous* on `(0,∞)` (it is a primitive of the continuous
`F_*(∂_zΨ)`, the `j = 0` chain) and vanishes `a.e.`, hence vanishes pointwise; the induction
`level_step 0/1/2` then propagates the vanishing to `D_zΨ`, `D_z²Ψ`, `D_z³Ψ`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.integrable_prod_sq_restrict_open
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.H2W.SliceMomentLinear

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W

/-- **A continuous function vanishing almost everywhere is zero.**  (The `a.e.` moment
conditions of the current `TT.EllWeakPos` are upgraded to pointwise ones with this.) -/
theorem ae_zero_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), f z = 0) :
    ∀ z, 0 < z → f z = 0 := by
  have h' : f =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)] (fun _ : ℝ => 0) := by
    filter_upwards [h] with z hz
    simpa using hz
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := MeasureTheory.volume) h' isOpen_Ioi hf
    continuousOn_const
  intro z hz
  exact heq hz

end Work.H2W

namespace Work.H2W.MomentAe

open Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-- A point of `Iθ` is almost everywhere interior (the two endpoints are null). -/
theorem ae_Ioo_mem : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    rw [Set.mem_setOf_eq] at hθ
    push_neg at hθ
    obtain ⟨hmem, hnot⟩ := hθ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h0 : θ = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      by_contra hpi
      exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hpi⟩
  · have hset : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton _)

/-! ## 1. Basic identities -/

/-- `F_*(D_z f)(z) = z · F_*(∂_z f)(z)`, for every function `f` and every `z`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * sg θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * sg θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- `z² ∂_z² f = D_z² f − D_z f` on the open quadrant. -/
theorem zsq_pzIter2_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 f z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.Dz f z θ :=
  Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open f hf hz hθ

/-- `D_z^j (z² ∂_z² f) = D_z^{j+2} f − D_z^{j+1} f` on the open quadrant. -/
theorem DzIter_zsq_pzIter2_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ
      = Work.Spaces.DzIter (j + 2) f z θ - Work.Spaces.DzIter (j + 1) f z θ := by
  have h1 := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open f
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n) j 0 hz hθ
  simp only [Work.Spaces.mixed_zero_right] at h1
  have h2 := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Spaces.DzIter j f)
    (hf.DzIter j) hz hθ
  rw [← h1, h2]
  rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter j f) = Work.Spaces.DzIter (j + 2) f from
    (Work.Spaces.DzIter_add_right 2 j f).symm.trans (by rw [Nat.add_comm])]
  rw [show Work.Spaces.Dz (Work.Spaces.DzIter j f) = Work.Spaces.DzIter (j + 1) f from
    (Work.Spaces.DzIter_add_right 1 j f).symm.trans (by rw [Nat.add_comm])]

/-- `D_z³ f = D_z² f + D_z (z² ∂_z² f)` on the open quadrant. -/
theorem DzIter_three_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 3 f z θ
      = Work.Spaces.DzIter 2 f z θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  have h := DzIter_zsq_pzIter2_eq hf 1 hz hθ
  rw [show (1 + 2 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl] at h
  linarith [h]

/-- `z² ∂_z² Ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_zsq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  rw [show Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 from rfl]
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul
    ((hΨ.pzIter 2).forall n)

/-! ## 2. Weighted angular energies and slice integrability -/

/-- `AngSq g u = ∫_θ (g u θ)² sin(2θ)^{-η}`, the `θ`-energy of the slot `g` at radius `u`. -/
def AngSq (g : ℝ → ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ θ in Iθ, (g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

theorem AngSq_nonneg (g : ℝ → ℝ → ℝ) (u : ℝ) : 0 ≤ AngSq g u := by
  rw [AngSq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

/-- The angular slice of a weighted `D_z`-slot of an `ℋ^k`-function, without the radial
weight: `θ ↦ (D_z^i g u θ)² sin(2θ)^{-η}` is integrable on `Iθ` for every `u > 0`. -/
theorem slot_slice_integrableOn {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ := by
  have hI : IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ
      * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hs hm i hi (Set.mem_Ici.mpr hu.le)
  have hwu : Work.Spaces.w u ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.FTS.EllipticEst.one_le_w hu))
  have hWu : (Work.Spaces.w u) ^ 2 ≠ 0 := pow_ne_zero 2 hwu
  refine ((hI.mul_const ((Work.Spaces.w u) ^ 2)⁻¹).congr ?_)
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [div_eq_mul_inv]
  show (Work.Spaces.DzIter i g u θ * Wf u θ) ^ 2 / (Work.Spaces.w u) ^ 2
      = (Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  rw [div_eq_mul_inv, mul_pow, Wf_sq_eq (sin_two_nonneg hθ)]
  rw [show rho θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  field_simp [hwu, hWu]

/-- The `θ`-energy of a slot is `z`-locally integrable, with the extra radial weight
`w²`: `u ↦ (∫_θ (D_z^i g u θ)² sin(2θ)^{-η}) · w(u)²` is integrable on `(a,b]`. -/
theorem slot_Iz_integrableOn {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => AngSq (Work.Spaces.DzIter i g) u * (Work.Spaces.w u) ^ 2)
      (Set.Ioc a b) := by
  have hIz : IntegrableOn (fun u => ∫ θ in Iθ, (Work.Spaces.DzIter i g u θ
      * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz :=
    Work.FTS.EllipticEst.integrableOn_slice_Iz α k hs hm i hi
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun u hu =>
    Set.mem_Ici.mpr (le_of_lt (lt_trans ha hu.1))
  refine (hIz.mono_set hsub).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u _
  rw [AngSq, ← MeasureTheory.integral_mul_const (Work.Spaces.w u ^ 2)
    (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  show (Work.Spaces.DzIter i g u θ * Wf u θ) ^ 2
      = ((Work.Spaces.DzIter i g u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (Work.Spaces.w u) ^ 2
  rw [mul_pow, Wf_sq_eq (sin_two_nonneg hθ)]
  rw [show rho θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  ring

/-- The `θ`-energy `u ↦ AngSq g u` of a function `C^∞` on the open quadrant is a.e. strongly
measurable (Fubini applied to the continuous joint integrand). -/
theorem aesm_AngSq {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun u => AngSq g u) (volume.restrict (Set.Ioc a b)) := by
  have hs : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
    (hs.continuousOn.pow 2).mul hw
  have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont ha).integral_prod_right'
    (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict Iθ)
  simpa only [Function.uncurry_apply_pair, AngSq] using h

/-- The Young/AM--GM bound with the angular weight, in integrated form: `|g|σ` is bounded by
the weighted `L²`-energy of `g` plus an absolute constant. -/
theorem abs_moment_le_energy {g : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict Iθ))
    (hg : IntegrableOn (fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ) :
    IntegrableOn (fun θ => g θ * sg θ) Iθ ∧
      ∫ θ in Iθ, |g θ| * sg θ
        ≤ 1 + ∫ θ in Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hσle : ∀ θ ∈ Iθ, sg θ ≤ 1 := fun θ hθ => by
    show Real.sin θ * Real.cos θ ^ 2 ≤ 1
    have hs := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one θ]
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hs hc (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hσcont : Continuous sg := by unfold Work.Elliptic.sinCos2; fun_prop
  have hσint : IntegrableOn sg Iθ := hσcont.continuousOn.integrableOn_compact isCompact_Icc
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- the `θ`-mass of `Iθ` is `π/2`
  have hvol : ∫ θ in Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    simp
  have hσmass : ∫ θ in Iθ, sg θ ≤ Real.pi / 2 := by
    rw [← hvol]
    exact MeasureTheory.integral_mono_ae hσint hone
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hσle θ hθ))
  -- the pointwise weighted Young bound
  have hpt : ∀ θ ∈ Iθ, |g θ| * sg θ
      ≤ (g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2) + sg θ * (1 / 2) := by
    intro θ hθ
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hs | hs
    · -- `sin(2θ) = 0`: both sides vanish
      have hσ0 : sg θ = 0 := by
        have h3 : Real.sin θ * Real.cos θ = 0 := by
          have h4 := Real.sin_two_mul θ
          rw [← hs] at h4
          linarith
        rcases mul_eq_zero.mp h3 with h | h
        · rw [Work.Elliptic.sinCos2, h]; ring
        · rw [Work.Elliptic.sinCos2, h]; ring
      have hr0 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
        rw [← hs]; exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
      rw [hσ0, hr0]
      simp
    · have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hr1 : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        have h2 := Real.rpow_le_rpow_of_nonpos hs hsle
          (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≤ 0)
        rwa [Real.one_rpow] at h2
      have hσ0 := hσnn θ hθ
      have hσ1 := hσle θ hθ
      have h1 : 2 * (|g θ| * sg θ) ≤ g θ ^ 2 + sg θ ^ 2 := by
        nlinarith [sq_nonneg (|g θ| - sg θ), sq_abs (g θ)]
      have ha : g θ ^ 2 ≤ g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [sq_nonneg (g θ), hr1]
      have hb : sg θ ^ 2 ≤ sg θ := by nlinarith
      linarith
  have hdom : IntegrableOn (fun θ =>
      (g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2) + sg θ * (1 / 2)) Iθ :=
    (hg.mul_const (1 / 2)).add (hσint.mul_const (1 / 2))
  have hsl : IntegrableOn (fun θ => g θ * sg θ) Iθ := by
    refine Integrable.mono' hdom (hgm.mul hσcont.aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]
    exact hpt θ hθ
  refine ⟨hsl, ?_⟩
  have hsl' : Integrable (fun θ => |g θ| * sg θ) (volume.restrict Iθ) :=
    hsl.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have hmono : ∫ θ in Iθ, |g θ| * sg θ
      ≤ ∫ θ in Iθ, ((g θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (1 / 2)
          + sg θ * (1 / 2)) :=
    MeasureTheory.integral_mono_ae hsl' hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hσnn θ hθ))]
        exact hpt θ hθ))
  rw [MeasureTheory.integral_add (hg.mul_const (1 / 2)) (hσint.mul_const (1 / 2)),
    MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const] at hmono
  have hE0 : 0 ≤ ∫ θ in Iθ, (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)))
  linarith [hmono, hσmass, hE0, Real.pi_lt_four]

/-! ## 3. Product integrability of a divided slot from a fibre bound -/

/-- If the fibres `θ ↦ f r θ` are integrable with `∫_θ |f r θ| ≤ B r` and `B` is integrable
on `(s,z]`, then `(r,θ) ↦ f r θ / r` is integrable on `(s,z] × Iθ`. -/
theorem integrable_uncurry_div_of_fibre_bound {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ} {s z : ℝ}
    (hs : 0 < s) (hsz : s ≤ z)
    (hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)))
    (hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ => f r θ) Iθ)
    (hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Iθ, |f r θ| ≤ B r)
    (hB : IntegrableOn B (Set.Ioc s z)) :
    Integrable (Function.uncurry (fun r θ : ℝ => f r θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)) := by
  haveI : SFinite (volume.restrict (Set.Ioc s z)) := inferInstance
  haveI : SFinite (volume.restrict Iθ) := inferInstance
  have hbox : MeasurableSet (Set.Ioc s z ×ˢ Iθ) := measurableSet_Ioc.prod measurableSet_Icc
  have hG : Integrable (Function.uncurry (fun r θ : ℝ => |f r θ / r|))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated (μ := volume.restrict (Set.Ioc s z))
      (ν := volume.restrict Iθ) (G := fun r θ => |f r θ / r|)
      (fun a b => abs_nonneg _) ?_ ?_ ?_).1
    · exact hae.norm.congr (Filter.Eventually.of_forall fun p => by
        simp only [Function.uncurry, Real.norm_eq_abs])
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
      have hr0 : 0 < r := lt_trans hs hr.1
      exact (((hfib r hr).norm.const_mul r⁻¹).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hr0)]
          ring))
    · refine (hB.const_mul s⁻¹).mono' ?_ ?_
      · exact (hae.norm.integral_prod_right'
          (μ := volume.restrict (Set.Ioc s z)) (ν := volume.restrict Iθ)).congr
          (Filter.Eventually.of_forall fun r => by
            simp only [Function.uncurry, Real.norm_eq_abs])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
        have hr0 : 0 < r := lt_trans hs hr.1
        have hBnn : 0 ≤ B r := le_trans (integral_nonneg fun θ => abs_nonneg _) (hle r hr)
        rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
        have h1 : ∫ θ in Iθ, |f r θ / r| = (∫ θ in Iθ, |f r θ|) / r := by
          rw [← MeasureTheory.integral_div]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
          rw [abs_div, abs_of_pos hr0]
        rw [h1]
        have hstep1 : (∫ θ in Iθ, |f r θ|) / r ≤ B r / r :=
          div_le_div_of_nonneg_right (hle r hr) (le_of_lt hr0)
        have hstep2 : B r / r ≤ s⁻¹ * B r := by
          rw [div_eq_mul_inv, mul_comm (B r)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ hs (le_of_lt hr.1)) hBnn
        exact le_trans hstep1 hstep2
  refine (MeasureTheory.integrable_norm_iff hae).mp ?_
  exact hG.congr (Filter.Eventually.of_forall fun p => by
    simp only [Function.uncurry, Real.norm_eq_abs])

/-! ## 4. Slice control at level `i ≤ 2` -/

/-- The bound function for the slices of `D_z^i Ψ`, `i ≤ 2`: the endpoint data at `π/4` and the
weighted `L²`-energy of the second `θ`-derivative (with the constants produced by
`sliceMomentLinear`). -/
def Bnd2 (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
    + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
    + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u

/-- `AngSq (pthIter 2 (D_z^i Ψ)) = AngSq (D_z^i (pthIter 2 Ψ))` for `u > 0` (the two
`θ`-integrands agree off the two endpoints of `Iθ`). -/
theorem AngSq_pthIter2_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (i : ℕ)
    (u : ℝ) (hu : 0 < u) :
    AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u
      = AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u := by
  rw [AngSq, AngSq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  have hcomm := (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i)
    (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθI⟩)
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm]

/-- The angular `L²`-integrability of the second `θ`-derivative of `D_z^i Ψ`, `i ≤ 2`. -/
theorem slice_two_energy {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 2) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ) u θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθ := by
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have h1 := slot_slice_integrableOn hSB hB i hi hu
  refine h1.congr ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  have hcomm := (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ i)
    (show ((u, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hu, hθI⟩)
  simp only [Function.uncurry_apply_pair] at hcomm
  rw [hcomm]

/-- The `θ`-slice of a `C^∞`-on-the-open-quadrant function is `C²` there. -/
theorem contDiffOn_slice_two {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) : ContDiffOn ℝ 2 (fun θ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (hg.curry_θ hu).of_le (by simp [Work.Stability.smoothOrder])

theorem slice_two_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter i Ψ u θ * sg θ) Iθ := fun u hu =>
  (sliceMomentLinear (g := fun θ => Work.Spaces.DzIter i Ψ u θ)
    (contDiffOn_slice_two (hΨ.DzIter i) hu) (slice_two_energy hΨ hB i hi hu)).1

theorem slice_two_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ ≤ Bnd2 Ψ i u := by
  intro u hu
  have h := (sliceMomentLinear (g := fun θ => Work.Spaces.DzIter i Ψ u θ)
    (contDiffOn_slice_two (hΨ.DzIter i) hu) (slice_two_energy hΨ hB i hi hu)).2
  have hmain : ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ
      ≤ 4 + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
        + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
        + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u := by
    simpa only [SliceEnergy, AngSq, Work.Spaces.pth, Work.Spaces.pthIter_succ,
      Work.Spaces.pthIter_zero] using h
  rw [Bnd2]
  linarith [hmain]

theorem Bnd2_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 2) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd2 Ψ i) (Set.Ioc a b) := by
  have hSB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := (hΨ.pth).pth
  have hpi : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcont1 : ContinuousOn (fun u => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|) (Set.Ioi 0) :=
    ((hΨ.DzIter i).curry_z hpi).continuousOn.abs
  have hcont2 : ContinuousOn
      (fun u => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|) (Set.Ioi 0) :=
    (((hΨ.DzIter i).pth).curry_z hpi).continuousOn.abs
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le ha hu.1
  have hint1 : IntegrableOn (fun u => |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|) (Set.Ioc a b) :=
    ((hcont1.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn
      (fun u => |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|) (Set.Ioc a b) :=
    ((hcont2.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have henergy : IntegrableOn
      (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u) (Set.Ioc a b) := by
    have hw : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u
        * (Work.Spaces.w u) ^ 2) (Set.Ioc a b) := slot_Iz_integrableOn hSB hB i hi ha
    have hcongr : IntegrableOn (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u
        * (Work.Spaces.w u) ^ 2) (Set.Ioc a b) :=
      hw.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
        show AngSq (Work.Spaces.DzIter i (Work.Spaces.pthIter 2 Ψ)) u * (Work.Spaces.w u) ^ 2
            = AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u * (Work.Spaces.w u) ^ 2
        rw [AngSq_pthIter2_comm hΨ i u (lt_trans ha hu.1)])
    have haesm : AEStronglyMeasurable
        (fun u => AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u)
        (volume.restrict (Set.Ioc a b)) :=
      (aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSB.DzIter i) n) (le_of_lt ha)).congr
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun u hu =>
          (AngSq_pthIter2_comm hΨ i u (lt_trans ha hu.1)).symm)
    refine hcongr.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
    have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
      have := Work.FTS.EllipticEst.one_le_w (lt_trans ha hu.1)
      nlinarith
    nlinarith [AngSq_nonneg (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u]
  have hone : IntegrableOn (fun _ : ℝ => (4 : ℝ)) (Set.Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun u => (4 : ℝ) + 4 * |Work.Spaces.DzIter i Ψ u (Real.pi / 4)|
      + 4 * |Work.Spaces.pth (Work.Spaces.DzIter i Ψ) u (Real.pi / 4)|
      + 2 * AngSq (Work.Spaces.pthIter 2 (Work.Spaces.DzIter i Ψ)) u) (Set.Ioc a b) :=
    ((hone.add (hint1.const_mul 4)).add (hint2.const_mul 4)).add (henergy.const_mul 2)
  refine hsum.congr (Filter.Eventually.of_forall fun u => ?_)
  rw [Bnd2]

/-! ## 5. Slice control at level `3` -/

/-- The bound function for the slices of `D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)`. -/
def Bnd3 (Ψ : ℝ → ℝ → ℝ) (u : ℝ) : ℝ :=
  Bnd2 Ψ 2 u + (1 + AngSq (Work.Spaces.DzIter 1
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)

theorem slice_three_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    ∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter 3 Ψ u θ * sg θ) Iθ := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter 1).continuousOn hu
  have hAint := (abs_moment_le_energy hm
    (slot_slice_integrableOn hSA hA 1 (by norm_num) hu)).1
  have h := (slice_two_integrableOn hΨ hB 2 le_rfl u hu).add hAint
  refine h.congr ?_
  filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
    with θ hθI _
  simp only [Pi.add_apply]
  rw [DzIter_three_eq hΨ hu hθI]
  ring

theorem slice_three_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter 3 Ψ u θ| * sg θ ≤ Bnd3 Ψ u := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter 1).continuousOn hu
  have hAint := abs_moment_le_energy hm
    (slot_slice_integrableOn hSA hA 1 (by norm_num) hu)
  have h2 := slice_two_integrableOn hΨ hB 2 le_rfl u hu
  have h2b := slice_two_bound hΨ hB 2 le_rfl u hu
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hpt : ∀ᵐ θ ∂(volume.restrict Iθ), |Work.Spaces.DzIter 3 Ψ u θ| * sg θ
      ≤ |Work.Spaces.DzIter 2 Ψ u θ| * sg θ
        + |Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ := by
    filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
      with θ hθI hθ
    rw [DzIter_three_eq hΨ hu hθI]
    calc |Work.Spaces.DzIter 2 Ψ u θ + Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ
        ≤ (|Work.Spaces.DzIter 2 Ψ u θ|
            + |Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ|)
            * sg θ := mul_le_mul_of_nonneg_right (abs_add_le _ _) (hσnn θ hθ)
      _ = _ := by ring_nf
  have h2' : IntegrableOn (fun θ => |Work.Spaces.DzIter 2 Ψ u θ| * sg θ) Iθ :=
    h2.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have hA' : IntegrableOn (fun θ => |Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) Iθ :=
    hAint.1.norm.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hσnn θ hθ)]))
  have h := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
      (fun θ hθ => mul_nonneg (abs_nonneg _) (hσnn θ hθ)))
    (h2'.add hA') hpt
  simp only [Pi.add_apply] at h
  rw [MeasureTheory.integral_add h2' hA'] at h
  rw [Bnd3]
  simp only [AngSq]
  have hfin : (∫ θ in Iθ, |Work.Spaces.DzIter 2 Ψ u θ| * sg θ)
      + ∫ θ in Iθ, |Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ
      ≤ Bnd2 Ψ 2 u + (1 + ∫ θ in Iθ, (Work.Spaces.DzIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    linarith [h2b, hAint.2]
  exact le_trans h hfin

theorem Bnd3_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (Bnd3 Ψ) (Set.Ioc a b) := by
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have h1 : IntegrableOn (Bnd2 Ψ 2) (Set.Ioc a b) := Bnd2_integrableOn hΨ hB 2 le_rfl ha
  have h2 : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc a b) := by
    have hw := slot_Iz_integrableOn hSA hA 1 (by norm_num) (a := a) (b := b) ha
    have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
        (volume.restrict (Set.Ioc a b)) :=
      aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSA.DzIter 1) n) (le_of_lt ha)
    refine hw.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
    have h3 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
      have := Work.FTS.EllipticEst.one_le_w (lt_trans ha hu.1)
      nlinarith
    nlinarith [AngSq_nonneg (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have h3 : IntegrableOn (fun u => Bnd2 Ψ 2 u + (1 + AngSq (Work.Spaces.DzIter 1
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)) (Set.Ioc a b) :=
    h1.add (hone.add h2)
  exact h3.congr (Filter.Eventually.of_forall fun u => by simp only [Bnd3])

/-! ## 6. The uniform level bound -/

/-- The bound function for the slices of `D_z^i Ψ`, `i ≤ 3`. -/
def Bnd (Ψ : ℝ → ℝ → ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  if i ≤ 2 then Bnd2 Ψ i u else Bnd3 Ψ u

theorem level_bound {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (i : ℕ) (hi : i ≤ 3) :
    (∀ u, 0 < u → IntegrableOn (fun θ => Work.Spaces.DzIter i Ψ u θ * sg θ) Iθ) ∧
      (∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.DzIter i Ψ u θ| * sg θ ≤ Bnd Ψ i u) ∧
      (∀ a b, 0 < a → IntegrableOn (Bnd Ψ i) (Set.Ioc a b)) := by
  by_cases h2 : i ≤ 2
  · have h := slice_two_integrableOn hΨ hB i h2
    have h' := slice_two_bound hΨ hB i h2
    have hBeq : Bnd Ψ i = Bnd2 Ψ i := by funext u; simp only [Bnd, if_pos h2]
    refine ⟨h, fun u hu => ?_, fun a b ha => ?_⟩
    · rw [hBeq]; exact h' u hu
    · rw [hBeq]; exact Bnd2_integrableOn hΨ hB i h2 ha
  · have hi3 : i = 3 := by omega
    subst hi3
    have h := slice_three_integrableOn hΨ hA hB
    have h' := slice_three_bound hΨ hA hB
    have hBeq : Bnd Ψ 3 = Bnd3 Ψ := by
      funext u; simp only [Bnd, if_neg (by omega : ¬ (3:ℕ) ≤ 2)]
    refine ⟨h, fun u hu => ?_, fun a b ha => ?_⟩
    · rw [hBeq]; exact h' u hu
    · rw [hBeq]; exact Bnd3_integrableOn hΨ hA hB ha

/-! ## 7. The chain rule and continuity for the moments -/

/-- The fundamental theorem of calculus along a radial slice, for a function `C^∞` on the open
quadrant: `f z θ - f s θ = ∫_s^z ∂_z f (r,θ) dr` for `0 < s ≤ z` and `θ ∈ (0,π/2)`. -/
theorem slice_FTC_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {s z θ : ℝ} (hs : 0 < s) (hsz : s ≤ z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    f z θ - f s θ = ∫ r in s..z, Work.Spaces.pz f r θ := by
  have hcont : ContinuousOn (fun r : ℝ => Work.Spaces.pz f r θ) (Set.uIcc s z) := by
    rw [Set.uIcc_of_le hsz]
    exact ((hf.pz.curry_z hθ).continuousOn).mono (fun r hr => lt_of_lt_of_le hs hr.1)
  have hderiv : ∀ r ∈ Set.uIcc s z,
      HasDerivAt (fun r : ℝ => f r θ) (Work.Spaces.pz f r θ) r := by
    intro r hr
    rw [Set.uIcc_of_le hsz] at hr
    exact hf.hasDerivAt_slice hθ (lt_of_lt_of_le hs hr.1)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable).symm

/-- **The primitive chain rule for the angular moment.**  From the two endpoint slice
integrabilities and the box integrability of `(r,θ) ↦ ∂_z f (r,θ) · sinθcos²θ`, the moment
`F_* f` is an antiderivative of `F_*(∂_z f)`:
`F_* f z − F_* f s = ∫_r in s..z F_*(∂_z f) r` for `0 < s ≤ z`. -/
theorem Fstar_sub_eq_integral {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {s z : ℝ} (hs : 0 < s) (hsz : s ≤ z)
    (hsl_s : IntegrableOn (fun θ => f s θ * sg θ) Iθ)
    (hsl_z : IntegrableOn (fun θ => f z θ * sg θ) Iθ)
    (hbox : MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz f r θ * sg θ))
      ((MeasureTheory.volume.restrict (Set.Ioc s z)).prod
        (MeasureTheory.volume.restrict Iθ))) :
    Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := by
  rcases eq_or_lt_of_le hsz with hsz0 | hszlt
  · rw [← hsz0, sub_self, intervalIntegral.integral_same]
  -- Step 1: the difference of the two moments as a single angular integral
  have h1 : Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Iθ, (f z θ - f s θ) * sg θ := by
    simp only [Work.Elliptic.Fstar]
    rw [show (fun θ : ℝ => (f z θ - f s θ) * sg θ)
        = fun θ => f z θ * sg θ - f s θ * sg θ from by funext θ; ring]
    rw [MeasureTheory.integral_sub hsl_z hsl_s]
  -- Step 2: the radial FTC on the angular slice, for a.e. angle
  have h2 : ∫ θ in Iθ, (f z θ - f s θ) * sg θ
      = ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_Ioo_mem] with θ hθ
    rw [slice_FTC_open hf hs hsz hθ]
  -- Step 3: pull the angular weight out of the radial integral
  have h3 : ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ
      = ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    exact (intervalIntegral.integral_mul_const (sg θ) (fun r => Work.Spaces.pz f r θ)).symm
  -- Step 4: Fubini
  have h4 : ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ
      = ∫ r in s..z, ∫ θ in Iθ, Work.Spaces.pz f r θ * sg θ := by
    refine (MeasureTheory.intervalIntegral_integral_swap (a := s) (b := z)
      (μ := MeasureTheory.volume.restrict Iθ)
      (f := fun r θ => Work.Spaces.pz f r θ * sg θ) ?_).symm
    simpa only [Set.uIoc_of_le hsz] using hbox
  calc Work.Elliptic.Fstar f z - Work.Elliptic.Fstar f s
      = ∫ θ in Iθ, (f z θ - f s θ) * sg θ := h1
    _ = ∫ θ in Iθ, (∫ r in s..z, Work.Spaces.pz f r θ) * sg θ := h2
    _ = ∫ θ in Iθ, ∫ r in s..z, Work.Spaces.pz f r θ * sg θ := h3
    _ = ∫ r in s..z, ∫ θ in Iθ, Work.Spaces.pz f r θ * sg θ := h4
    _ = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz f) r := rfl

/-- `∂_z²(D_z^j Ψ) = D_z^j(z²∂_z²Ψ)/u²` on the open quadrant. -/
theorem pz2_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) {u θ : ℝ}
    (hu : 0 < u) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ
      = Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ / u ^ 2 := by
  have h := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open Ψ
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ n) j 0 hu hθ
  simp only [Work.Spaces.mixed_zero_right] at h
  have hu0 : u ≠ 0 := ne_of_gt hu
  rw [show Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) u θ
      = Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ from rfl] at h
  rw [eq_div_iff (pow_ne_zero 2 hu0), mul_comm]
  exact h

/-- The absolute moment of `∂_z²(D_z^j Ψ)` is controlled by the weighted `L²`-slot of
`z²∂_z²Ψ`. -/
theorem abs_pz2_le_energy {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hAmem : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (j : ℕ) (hj : j ≤ 2) :
    ∀ u, 0 < u → ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ| * sg θ
      ≤ (1 + AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) / u ^ 2 := by
  intro u hu
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ) (volume.restrict Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hu
  have hb := abs_moment_le_energy hm (slot_slice_integrableOn hSA hAmem j hj hu)
  calc ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u θ| * sg θ
      = ∫ θ in Iθ, (|Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) / u ^ 2 := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Ioo_mem, MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
          with θ hθI _
        rw [pz2_eq hΨ j hu hθI, div_eq_mul_inv, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hu) 2))]
        ring
    _ = (∫ θ in Iθ, |Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) u θ| * sg θ) / u ^ 2 :=
        MeasureTheory.integral_div (u ^ 2) _
    _ ≤ (1 + AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) / u ^ 2 :=
        div_le_div_of_nonneg_right hb.2 (by positivity)

theorem level_chain {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) w
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) s
      = ∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r := by
  intro s w hs hsw
  have hSj : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) := hΨ.DzIter j
  have hlevj := level_bound hΨ hA hB j (by omega)
  have hlevj1 := level_bound hΨ hA hB (j + 1) (by omega)
  have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
    unfold Work.Elliptic.sinCos2; fun_prop
  refine Fstar_sub_eq_integral (hf := hSj) hs hsw
    (hlevj.1 s hs) (hlevj.1 w (lt_of_lt_of_le hs hsw)) ?_
  have hae := Work.FTS.EllipticEst.aesm_uncurry_restrict_open
    (fun p : ℝ × ℝ => Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 * sg p.2 / p.1)
    ((((hΨ.DzIter (j + 1)).continuousOn).mul hsg).div continuousOn_fst
      (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
    (a := s) (b := w) (le_of_lt hs)
  refine (integrable_uncurry_div_of_fibre_bound
    (f := fun r θ => Work.Spaces.DzIter (j + 1) Ψ r θ * sg θ) (B := Bnd Ψ (j + 1))
    hs hsw hae (fun r hr => hlevj1.1 r (lt_trans hs hr.1)) (fun r hr => ?_)
    (hlevj1.2.2 s w hs)).congr ?_
  · have heq : ∫ θ in Iθ, |Work.Spaces.DzIter (j + 1) Ψ r θ * sg θ|
        = ∫ θ in Iθ, |Work.Spaces.DzIter (j + 1) Ψ r θ| * sg θ :=
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          have hσ : 0 ≤ sg θ := mul_nonneg
            (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
          simp only [abs_mul, abs_of_nonneg hσ]))
    rw [heq]
    exact hlevj1.2.1 r (lt_trans hs hr.1)
  · rw [MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) (fun p hp => ?_)
    have hp1 : 0 < p.1 := lt_trans hs hp.1.1
    simp only [Function.uncurry]
    rw [show Work.Spaces.DzIter (j + 1) Ψ p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2 from rfl,
      mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt hp1)]

theorem chain_pz_level {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) w
        - Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) s
      = ∫ r in s..w, Work.Elliptic.Fstar
          (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r := by
  intro s w hs hsw
  have hSj : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter j Ψ) := hΨ.DzIter j
  have hlev1 := level_bound hΨ hA hB (j + 1) (by omega)
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  have hslice : ∀ u, 0 < u → IntegrableOn
      (fun θ => Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ * sg θ) Iθ := by
    intro u hu
    refine ((hlev1.1 u hu).div_const u).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
    show Work.Spaces.DzIter (j + 1) Ψ u θ * sg θ / u
        = Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ * sg θ
    rw [show Work.Spaces.DzIter (j + 1) Ψ u θ
        = u * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) u θ from rfl]
    field_simp
  refine Fstar_sub_eq_integral (hf := hSj.pz) hs hsw
    (hslice s hs) (hslice w (lt_of_lt_of_le hs hsw)) ?_
  -- box integrability of `pz (pz (DzIter j Ψ)) * sg`
  have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
    unfold Work.Elliptic.sinCos2; fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2 * sg p.2 / p.1)
      Work.FTS.EllipticEst.Q0 :=
    (((hSA.DzIter j).continuousOn).mul hsg).div continuousOn_fst (fun p hp =>
      ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hae := Work.FTS.EllipticEst.aesm_uncurry_restrict_open
    (fun p : ℝ × ℝ => Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      p.1 p.2 * sg p.2 / p.1 / p.1) (hcont.div continuousOn_fst
        (fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
      (a := s) (b := w) (le_of_lt hs)
  have hint : IntegrableOn (fun r => (1 + AngSq (Work.Spaces.DzIter j
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s) (Set.Ioc s w) := by
    have hw := slot_Iz_integrableOn hSA hA j hj (a := s) (b := w) hs
    have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
        (volume.restrict (Set.Ioc s w)) :=
      aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (hSA.DzIter j) n) (le_of_lt hs)
    have hE : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc s w) := by
      refine hw.mono' haesm ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
      have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
        have := Work.FTS.EllipticEst.one_le_w (lt_trans hs hu.1)
        nlinarith
      nlinarith [AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
    have hIc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc s w) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact ((hE.add hIc).mul_const s⁻¹).congr
      (Filter.Eventually.of_forall fun r => by
        simp only [Pi.add_apply, div_eq_mul_inv]
        ring)
  refine (integrable_uncurry_div_of_fibre_bound
    (f := fun r θ => Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      r θ * sg θ / r) (B := fun r => (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s)
    hs hsw hae (fun r hr => ?_) (fun r hr => ?_) hint).congr ?_
  · -- fibres
    have hr0 : 0 < r := lt_trans hs hr.1
    have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hr0
    exact (((abs_moment_le_energy hm (slot_slice_integrableOn hSA hA j hj hr0)).1.mul_const
      r⁻¹).congr (Filter.Eventually.of_forall fun θ => by
        simp only [div_eq_mul_inv]))
  · -- fibre bound
    have hr0 : 0 < r := lt_trans hs hr.1
    have hm : AEStronglyMeasurable (fun θ => Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hSA.DzIter j).continuousOn hr0
    have hEb := abs_moment_le_energy hm (slot_slice_integrableOn hSA hA j hj hr0)
    have h1 : ∫ θ in Iθ, |Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        r θ * sg θ / r| = (∫ θ in Iθ, |Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r θ| * sg θ) / r := by
      rw [← MeasureTheory.integral_div]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [abs_div, abs_of_pos hr0, abs_mul, abs_of_nonneg (hσnn θ hθ)]
    rw [h1]
    have hnn : 0 ≤ (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) := by
      have := AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r
      linarith
    calc (∫ θ in Iθ, |Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          r θ| * sg θ) / r
        ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / r :=
          div_le_div_of_nonneg_right hEb.2 (le_of_lt hr0)
      _ ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / s :=
          div_le_div_of_nonneg_left hnn hs (le_of_lt hr.1)
  · rw [MeasureTheory.Measure.prod_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod measurableSet_Icc) (fun p hp => ?_)
    have hp1 : 0 < p.1 := lt_trans hs hp.1.1
    simp only [Function.uncurry]
    by_cases hzero : sg p.2 = 0
    · rw [hzero]
      ring
    · have hp2 : p.2 ∈ Set.Icc 0 (Real.pi / 2) := hp.2
      have hpθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
        refine ⟨lt_of_le_of_ne hp2.1 ?_, lt_of_le_of_ne hp2.2 ?_⟩
        · intro h
          exact hzero (by rw [← h]; simp [Work.Elliptic.sinCos2])
        · intro h
          exact hzero (by rw [h]; simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two])
      rw [pz2_eq hΨ j hp1 hpθ]
      ring_nf

theorem level_cont {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun u => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u)
      (Set.Ioi 0) := by
  intro z hz
  rw [Set.mem_Ioi] at hz
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have haz2 : a ≤ z + a := by linarith
  have hSA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := smoothOpen_zsq hΨ
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ sg θ := fun θ hθ => by
    show 0 ≤ Real.sin θ * Real.cos θ ^ 2
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)
  -- integrability of `Fstar (pz (pz (DzIter j Ψ)))` on `(a, z+a]`
  have hWoc : IntegrableOn (fun r => Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.Ioc a (z + a)) := by
    have hdom : IntegrableOn (fun r => (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / a ^ 2) (Set.Ioc a (z + a)) := by
      have hw := slot_Iz_integrableOn hSA hA j hj (a := a) (b := z + a) ha0
      have haesm : AEStronglyMeasurable (fun u => AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u)
          (volume.restrict (Set.Ioc a (z + a))) :=
        aesm_AngSq (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (hSA.DzIter j) n) (le_of_lt ha0)
      have hE : IntegrableOn (fun u => AngSq (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u) (Set.Ioc a (z + a)) := by
        refine hw.mono' haesm ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (AngSq_nonneg _ _)]
        have h1 : 1 ≤ (Work.Spaces.w u) ^ 2 := by
          have := Work.FTS.EllipticEst.one_le_w (lt_trans ha0 hu.1)
          nlinarith
        nlinarith [AngSq_nonneg (Work.Spaces.DzIter j
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) u]
      have hIc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a (z + a)) :=
        integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      refine ((hE.add hIc).div_const (a ^ 2)).congr ?_
      filter_upwards with x
      simp only [Pi.add_apply]
      ring
    have haesm : AEStronglyMeasurable (fun r => Work.Elliptic.Fstar
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r)
        (volume.restrict (Set.Ioc a (z + a))) := by
      have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz
          (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) p.1 p.2 * sg p.2)
          Work.FTS.EllipticEst.Q0 := by
        have hsg : ContinuousOn (fun p : ℝ × ℝ => sg p.2) Work.FTS.EllipticEst.Q0 := by
          unfold Work.Elliptic.sinCos2; fun_prop
        exact ((((hΨ.DzIter j).pz).pz).continuousOn).mul hsg
      have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
        (a := a) (b := z + a) (le_of_lt ha0)).integral_prod_right'
        (μ := volume.restrict (Set.Ioc a (z + a))) (ν := volume.restrict Iθ)
      simpa only [Work.Elliptic.Fstar, Function.uncurry_apply_pair] using h
    refine hdom.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
    have hr0 : 0 < r := lt_trans ha0 hr.1
    have hbound := abs_pz2_le_energy hΨ hA j hj r hr0
    have h1 : (1 + AngSq (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / r ^ 2
        ≤ (1 + AngSq (Work.Spaces.DzIter j
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r) / a ^ 2 := by
      refine div_le_div_of_nonneg_left ?_ (by positivity)
        (by nlinarith [mul_self_le_mul_self ha0.le hr.1.le])
      have := AngSq_nonneg (Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) r
      linarith
    rw [Real.norm_eq_abs]
    refine le_trans ?_ (le_trans hbound h1)
    rw [Work.Elliptic.Fstar]
    calc |∫ θ in Iθ, Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ|
        ≤ ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
              (f := fun θ => Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ * sg θ))
      _ = ∫ θ in Iθ, |Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r θ| * sg θ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
          rw [abs_mul, abs_of_nonneg (hσnn θ hθ)]
  have hWint : IntegrableOn (fun r => Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le haz2]
    exact hWoc.congr_set_ae MeasureTheory.Ioc_ae_eq_Icc.symm
  have hΦ : ContinuousOn (fun x => ∫ r in a..x, Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hWint
  have hU : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le haz2]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x => ∫ r in a..x, Work.Elliptic.Fstar
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) (Set.Ioi 0) z :=
    (hΦ.continuousAt hU).continuousWithinAt
  have hev : (fun x => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) x)
      =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) a
        + ∫ r in a..x, Work.Elliptic.Fstar
            (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rcases le_total a x with h | h
    · have h2 := chain_pz_level hΨ hA hB j hj a x ha0 h
      linarith
    · have h2 := chain_pz_level hΨ hA hB j hj x a (show 0 < x from hx) h
      rw [intervalIntegral.integral_symm] at h2
      linarith
  have hz_e : Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) z
      = Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) a
        + ∫ r in a..z, Work.Elliptic.Fstar
            (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.DzIter j Ψ))) r := by
    have h2 := chain_pz_level hΨ hA hB j hj a z ha0 haz.le
    linarith
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## 8. The induction step and the assembly -/

/-- A continuous function whose integral over every interval `[s,w] ⊆ (0,∞)` vanishes is
zero. -/
theorem eq_zero_of_interval_integral_eq_zero {V : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : ∀ s w, 0 < s → s ≤ w → ∫ r in s..w, V r = 0)
    (hcont : ContinuousOn V (Set.Ioi 0)) : V z = 0 := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hsub : Set.uIcc a z ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le haz.le]
    intro x hx
    exact lt_of_lt_of_le ha0 hx.1
  have hInt : IntervalIntegrable V volume a z := (hcont.mono hsub).intervalIntegrable
  have hsm : StronglyMeasurableAtFilter V (𝓝 z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi 0) (μ := volume) isOpen_Ioi
      (fun x hx => hcont.continuousAt (isOpen_Ioi.mem_nhds hx)) z hz
  have hderiv : HasDerivAt (fun w => ∫ r in a..w, V r) (V z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun w => ∫ r in a..w, V r) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds haz] with w hw
    exact hint a w ha0 (le_of_lt hw)
  have hderiv0 : HasDerivAt (fun w => ∫ r in a..w, V r) 0 z := by
    rw [Filter.EventuallyEq.hasDerivAt_iff hev]
    exact hasDerivAt_const z 0
  exact hderiv.unique hderiv0

/-- One step of the moment induction. -/
theorem level_step {Ψ : ℝ → ℝ → ℝ} (j : ℕ)
    (hchain : ∀ s w, 0 < s → s ≤ w →
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) w
        - Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) s
      = ∫ r in s..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) r)
    (hcont : ContinuousOn (fun u => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) u)
      (Set.Ioi 0))
    (hprev : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) Ψ) z = 0 := by
  intro z hz
  have hV : Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter j Ψ)) z = 0 := by
    refine eq_zero_of_interval_integral_eq_zero hz (fun s w hs hsw => ?_) hcont
    rw [← hchain s w hs hsw, hprev w (lt_of_lt_of_le hs hsw), hprev s hs, sub_self]
  rw [show Work.Spaces.DzIter (j + 1) Ψ = Work.Spaces.Dz (Work.Spaces.DzIter j Ψ) from rfl,
    Fstar_Dz_eq, hV, mul_zero]

/-- **The moment chain, `j ≤ 3`, for the current (`a.e.`) weak class.**  For a datum
`h : EllWeakPos α 2 F Ψ` the angular moments `F_*(D_z^j Ψ)(z) = ∫_θ D_z^j Ψ(z,θ) sinθcos²θ dθ`
vanish for every `j ≤ 3` and every `z > 0`. -/
theorem Fstar_DzIter_le_Psi (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.Spaces.HkMem α 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := h.memA
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  -- ## `F_*Ψ` is continuous on `(0,∞)`
  have hcont0 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hs0 : 0 < z / 2 := by linarith [Set.mem_Ioi.mp hz]
    have hchain0 := level_chain hΨ hA hB 0 (by omega)
    have hcontp := level_cont hΨ hA hB 0 (by omega)
    have hInt : IntervalIntegrable
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r)
        volume (z / 2) (2 * z) :=
      (hcontp.mono (by
        intro u hu
        rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])] at hu
        exact lt_of_lt_of_le hs0 hu.1)).intervalIntegrable
    have hcontprim : ContinuousOn
        (fun w => ∫ r in z / 2..w,
          Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r)
        (Set.uIcc (z / 2) (2 * z)) :=
      intervalIntegral.continuousOn_primitive_interval' hInt (by
        rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])]
        exact ⟨le_rfl, by linarith [Set.mem_Ioi.mp hz]⟩)
    have hmem : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith [Set.mem_Ioi.mp hz])]
      exact Icc_mem_nhds (by linarith [Set.mem_Ioi.mp hz]) (by linarith [Set.mem_Ioi.mp hz])
    have hev : (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) w) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) (z / 2)
          + ∫ r in z / 2..w, Work.Elliptic.Fstar (Work.Spaces.pz (Work.Spaces.DzIter 0 Ψ)) r) := by
      filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith [Set.mem_Ioi.mp hz])] with w hw
      have h1 := hchain0 (z / 2) w hs0 hw.le
      linarith [h1]
    exact ((continuousAt_const.add (hcontprim.continuousAt hmem)).congr hev.symm).continuousWithinAt
  -- ## `F_*Ψ ≡ 0` from the moment hypothesis (in `a.e.` form) and the continuity
  -- NOTE: the two lines of `hae` are the only place where the *form* of the moment field of
  -- `TT.EllWeakPos` is used.  With the current (pointwise) definition of `EllWeakPos` the
  -- derivation below is `fun z hz => h.orthPsi z hz`; if the field is ever relaxed to
  -- `∀ᵐ z ∂(volume.restrict (Ioi 0)), Fstar Ψ z = 0`, then `hae` becomes `h.orthPsi` verbatim.
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun z hz => h.orthPsi z hz)
  have h0 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 0 Ψ) z = 0 := fun z hz =>
    Work.H2W.ae_zero_of_continuousOn hcont0 hae z hz
  have h1 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 :=
    level_step 0 (level_chain hΨ hA hB 0 (by omega)) (level_cont hΨ hA hB 0 (by omega)) h0
  have h2 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0 :=
    level_step 1 (level_chain hΨ hA hB 1 (by omega)) (level_cont hΨ hA hB 1 (by omega)) h1
  have h3 : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z = 0 :=
    level_step 2 (level_chain hΨ hA hB 2 (by omega)) (level_cont hΨ hA hB 2 (by omega)) h2
  intro j hj z hz
  interval_cases j
  · exact h0 z hz
  · exact h1 z hz
  · exact h2 z hz
  · exact h3 z hz

end Work.H2W.MomentAe
