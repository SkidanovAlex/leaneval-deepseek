import Submission.NBody.EulerLagrange
import Submission.Commons.MeasureTheory.Integral.intervalIntegrable_of_lintegral_ofReal_norm_sq_lt_top
import Submission.Commons.Topology.Metric.exists_pos_le_dist_of_continuousOn_ne
import Submission.Commons.Topology.Metric.exists_norm_le_of_contDiff_hasCompactSupport
import Submission.Commons.Topology.Metric.half_le_dist_add_smul_of_norm_le
import Submission.Commons.Analysis.InnerProductSpace.norm_sum_mul_inner_le
import Submission.Commons.Analysis.Calculus.exists_bound_fderiv_pairSum_inv_dist
import Submission.Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
import Mathlib

/-!
# The first variation of the action

This chapter upgrades the weak Euler--Lagrange equation for `h`-minimisers.  The main result is
`weak_first_variation`: if `γ` is an `h`-minimiser on `[a,b]` (and collision free there) then for
every smooth compactly supported perturbation `ξ` supported in `(a,b)`,

    `∫_a^b ( ⟨γ̇, ξ̇⟩ₘ + ⟪∇U(γ), ξ⟫ ) = 0`,

the weak form of Newton's equations.  Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody


omit [InnerProductSpace ℝ E] in
lemma norm_sq_eq_sum_norm_sq (v : EN E N) : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  simpa using PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin N => E) v

omit [InnerProductSpace ℝ E] in
lemma norm_apply_le_norm (v : EN E N) (i : Fin N) : ‖v i‖ ≤ ‖v‖ := by
  simpa using PiLp.norm_apply_le (p := 2) v i

lemma kinetic_ge_norm_sq {m : Fin N → ℝ} {c : ℝ} (_hc : 0 < c) (hmc : ∀ i, c ≤ m i)
    (v : EN E N) : c * ‖v‖ ^ 2 ≤ 2 * kinetic m v := by
  have h : c * ‖v‖ ^ 2 = ∑ i, c * ‖v i‖ ^ 2 := by
    rw [norm_sq_eq_sum_norm_sq, Finset.mul_sum]
  have h2 : (2 : ℝ) * kinetic m v = ∑ i, m i * ‖v i‖ ^ 2 := by
    rw [kinetic]; ring
  rw [h, h2]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmc i) (sq_nonneg _)

lemma ofReal_kinetic_le_lagrangian {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    {x : EN E N} (hx : WithoutCollisions x) (v : EN E N) :
    ENNReal.ofReal (kinetic m v) ≤ lagrangian m h x v := by
  rw [lagrangian, if_pos hx]
  refine ENNReal.ofReal_le_ofReal ?_
  have hU := U_nonneg hm x
  rw [kinetic]
  linarith

/-- On a collision-free interval the real Lagrangian is interval-integrable when the action is
finite. -/
theorem integrable_lagR_of_actionOn_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a ≤ b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) := by
  have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [lagR]
    have hU := U_nonneg hm (γ t)
    have hK := kinetic_nonneg m hm (deriv γ t)
    rw [kinetic] at hK
    linarith
  have hpt : ∀ t ∈ Set.Ioc a b,
      lagrangian m h (γ t) (deriv γ t) = ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    fun t ht => lagrangian_eq_ofReal_lagR (hnc t ⟨ht.1.le, ht.2⟩)
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn, setLIntegral_congr_fun measurableSet_Ioc hpt]
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab] at h
  have hUcont : ContinuousOn (fun t => U m (γ t)) (Set.Icc a b) :=
    continuousOn_U.comp hγcont (fun t ht => hnc t ht)
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hmeas : AEStronglyMeasurable (fun t => lagR m h (γ t) (deriv γ t))
      (volume.restrict (Set.Ioc a b)) := by
    have hK : AEStronglyMeasurable (fun t => kinetic m (deriv γ t))
        (volume.restrict (Set.Ioc a b)) :=
      (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
        (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac).aemeasurable
    have hU : AEStronglyMeasurable (fun t => U m (γ t)) (volume.restrict (Set.Ioc a b)) :=
      (hUcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have hconst : AEStronglyMeasurable (fun _ : ℝ => h) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_const
    have hsum := hK.add (hU.add hconst)
    have hfun : (fun t : ℝ => lagR m h (γ t) (deriv γ t))
        = (fun t : ℝ => kinetic m (deriv γ t)) + ((fun t : ℝ => U m (γ t)) + fun _ => h) := by
      funext t
      simp only [lagR, kinetic, Pi.add_apply]
      ring
    rw [hfun]
    exact hsum
  refine ⟨hmeas, ?_⟩
  have h4 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    lintegral_congr fun t => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn t)]
  have h3 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ) < ⊤ := by
    rw [h4, h1]
    exact hfin
  simpa only [HasFiniteIntegral] using h3



/-! ## Finiteness of the kinetic integral -/

lemma lintegral_ofReal_kinetic_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hfin : actionOn m h γ a b < ⊤) :
    (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (deriv γ t))) < ⊤ := by
  rw [actionOn] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) hfin
  by_cases hc : WithoutCollisions (γ t)
  · exact ofReal_kinetic_le_lagrangian hm hh hc (deriv γ t)
  · rw [lagrangian, if_neg hc]; exact le_top

lemma lintegral_ofReal_norm_sq_deriv_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c : ℝ}
    (hc : 0 < c) (hmc : ∀ i, c ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hfin : actionOn m h γ a b < ⊤) :
    (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) < ⊤ := by
  have hm : ∀ i, 0 ≤ m i := fun i => le_of_lt (hc.trans_le (hmc i))
  have hkin := lintegral_ofReal_kinetic_lt_top hm hh hfin
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hd : AEMeasurable (deriv γ) (volume.restrict (Set.Ioc a b)) :=
    (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
      hac).aemeasurable
  have hK : AEMeasurable (fun t => ENNReal.ofReal (kinetic m (deriv γ t)))
      (volume.restrict (Set.Ioc a b)) :=
    (AEMeasurable.comp_aemeasurable (continuous_kinetic m).aemeasurable hd).ennreal_ofReal
  have hpt : ∀ t, ENNReal.ofReal (‖deriv γ t‖ ^ 2)
      ≤ ENNReal.ofReal (2 / c) * ENNReal.ofReal (kinetic m (deriv γ t)) := by
    intro t
    have h2 : c * ‖deriv γ t‖ ^ 2 ≤ 2 * kinetic m (deriv γ t) := kinetic_ge_norm_sq hc hmc _
    have h3 : ‖deriv γ t‖ ^ 2 ≤ (2 / c) * kinetic m (deriv γ t) := by
      have h4 : (2 / c) * kinetic m (deriv γ t) = (2 * kinetic m (deriv γ t)) / c := by ring
      rw [h4, le_div_iff₀ hc]
      nlinarith [h2]
    calc ENNReal.ofReal (‖deriv γ t‖ ^ 2)
        ≤ ENNReal.ofReal ((2 / c) * kinetic m (deriv γ t)) := ENNReal.ofReal_le_ofReal h3
      _ = ENNReal.ofReal (2 / c) * ENNReal.ofReal (kinetic m (deriv γ t)) :=
          ENNReal.ofReal_mul (by positivity)
  calc (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv γ t‖ ^ 2))
      ≤ ∫⁻ t in Set.Ioc a b,
          ENNReal.ofReal (2 / c) * ENNReal.ofReal (kinetic m (deriv γ t)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 / c)
          * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (deriv γ t)) :=
        lintegral_const_mul'' _ hK
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hkin

lemma intervalIntegrable_deriv_of_actionOn_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i) (hh : 0 ≤ h) (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hfin : actionOn m h γ a b < ⊤) :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
  (Commons.MeasureTheory.Integral.intervalIntegrable_of_lintegral_ofReal_norm_sq_lt_top hab
    (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
      hac)
    (lintegral_ofReal_norm_sq_deriv_lt_top hc hmc hh hac hfin)).norm

/-! ## The action potential is bounded by the integral of the real Lagrangian -/

theorem actionPot_le_ofReal_integral_lagR {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a < b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hInt : Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b))) :
    actionPot m h (γ a) (γ b) ≤ ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t)) := by
  have hle := actionPot_le_of_interval (m := m) (h := h) hab rfl rfl hac
  have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [lagR]
    have hU := U_nonneg hm (γ t)
    have hK := kinetic_nonneg m hm (deriv γ t)
    rw [kinetic] at hK
    linarith
  have hpt : ∀ t ∈ Set.Ioc a b,
      lagrangian m h (γ t) (deriv γ t) = ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    fun t ht => lagrangian_eq_ofReal_lagR (hnc t ⟨ht.1.le, ht.2⟩)
  have hEq : actionOn m h γ a b
      = ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t)) := by
    rw [actionOn, setLIntegral_congr_fun measurableSet_Ioc hpt,
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hnn)).symm,
      ← intervalIntegral.integral_of_le hab.le]
  exact hle.trans (le_of_eq hEq)



omit [FiniteDimensional ℝ E] in
lemma U_eq_dist_sum (m : Fin N → ℝ) :
    U m = fun y : EN E N =>
      ∑ j, ∑ i ∈ Finset.Iio j, m i * m j * (dist (y i) (y j))⁻¹ := by
  funext y
  simp only [U, r]



/-- **Weak first variation of the action.** -/
theorem weak_first_variation {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤)
    {ξ : ℝ → EN E N} (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hξc : HasCompactSupport ξ) (hts : tsupport ξ ⊆ Set.Ioo a b) :
    ∫ t in a..b, (massInner m (deriv γ t) (deriv ξ t)
        + (fderiv ℝ (U m) (γ t)) (ξ t)) = 0 := by
  classical
  have hmnn : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hh0 : 0 ≤ h := hh.le
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    by_cases hN : N = 0
    · subst hN
      exact ⟨1, one_pos, fun i => i.elim0⟩
    · haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
      set sf : Finset ℝ := Finset.univ.image m with hsf
      have hsfne : sf.Nonempty := hsf ▸ (Finset.univ_nonempty (α := Fin N)).image m
      refine ⟨sf.min' hsfne, ?_, ?_⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sf hsfne)
        rw [← hi]; exact hm i
      · intro i
        exact Finset.min'_le sf (m i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have hnc_ne : ∀ t ∈ Set.Icc a b, ∀ i j, i ≠ j → γ t i ≠ γ t j :=
    fun t ht i j hij h => hnc t ht i j hij (by rw [r, h, dist_self])
  have haction : actionOn m h γ a b < ⊤ := hmin ▸ hfin
  have hInt0 : Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) :=
    integrable_lagR_of_actionOn_lt_top hab.le hmnn hh0 hac hnc haction
  have hInt0' : IntervalIntegrable (fun t => lagR m h (γ t) (deriv γ t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hInt0
  have hderiv_int : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    intervalIntegrable_deriv_of_actionOn_lt_top hc hmc hh0 hab.le hac haction
  obtain ⟨δ, hδ, hδle⟩ :=
    Commons.Topology.Metric.exists_pos_le_dist_of_continuousOn_ne hab.le hγcont hnc_ne
  obtain ⟨M₀, hM₀⟩ := hξc.exists_bound_of_continuous hξ.continuous
  have hdξcont : Continuous (deriv ξ) := hξ.continuous_deriv (by decide)
  obtain ⟨M₁, hM₁⟩ := hξc.deriv.exists_bound_of_continuous hdξcont
  let Mξ : ℝ := max M₀ 1
  let Md : ℝ := max M₁ 1
  have hMξ_pos : 0 < Mξ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMd_pos : 0 < Md := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMξ_nn : 0 ≤ Mξ := hMξ_pos.le
  have hMd_nn : 0 ≤ Md := hMd_pos.le
  have hξle : ∀ t, ‖ξ t‖ ≤ Mξ := fun t => (hM₀ t).trans (le_max_left _ _)
  have hdξle : ∀ t, ‖deriv ξ t‖ ≤ Md := fun t => (hM₁ t).trans (le_max_left _ _)
  let rad : ℝ := δ / (4 * Mξ)
  have hr_pos : 0 < rad := by show 0 < δ / (4 * Mξ); positivity
  have hr_eq : rad = δ / (4 * Mξ) := rfl
  let s : Set ℝ := Set.Icc (-rad) rad
  have hs_nhds : s ∈ 𝓝 (0:ℝ) := by
    show Set.Icc (-rad) rad ∈ 𝓝 (0:ℝ)
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hxr_of_mem : ∀ x ∈ s, |x| ≤ rad := by
    intro x hx
    show |x| ≤ rad
    exact abs_le.mpr ⟨hx.1, hx.2⟩
  have hnc_pert_ne : ∀ x ∈ s, ∀ t ∈ Set.Icc a b, ∀ i j, i ≠ j →
      (γ t + x • ξ t) i ≠ (γ t + x • ξ t) j := by
    intro x hx t ht i j hij
    have h3 := Commons.Topology.Metric.half_le_dist_add_smul_of_norm_le (p := γ t i) (q := γ t j)
      (z₁ := ξ t i) (z₂ := ξ t j) hMξ_pos
      ((norm_apply_le_norm (ξ t) i).trans (hξle t))
      ((norm_apply_le_norm (ξ t) j).trans (hξle t)) hδ.le hr_eq (hxr_of_mem x hx)
      (hδle t ht i j hij)
    have h4 : (γ t + x • ξ t) i = γ t i + x • ξ t i := by rw [PiLp.add_apply, PiLp.smul_apply]
    have h5 : (γ t + x • ξ t) j = γ t j + x • ξ t j := by rw [PiLp.add_apply, PiLp.smul_apply]
    rw [h4, h5]
    intro hcontra
    exact absurd (by rw [hcontra, dist_self]) (ne_of_gt (lt_of_lt_of_le (by linarith) h3))
  have hnc_pert : ∀ x ∈ s, ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t + x • ξ t) :=
    fun x hx t ht i j hij => by
      rw [r]
      intro hcontra
      exact hnc_pert_ne x hx t ht i j hij (dist_eq_zero.mp hcontra)
  have hnc_ne_pert : ∀ x ∈ s, ∀ t ∈ Set.Icc a b, ∀ i j, i ≠ j →
      (fun t => γ t + x • ξ t) t i ≠ (fun t => γ t + x • ξ t) t j :=
    fun x hx t ht => hnc_pert_ne x hx t ht
  -- the compact set of perturbed configurations
  let K : Set (EN E N) := (fun p : ℝ × ℝ => γ p.1 + p.2 • ξ p.1) ''
    (Set.Icc a b ×ˢ s)
  have hK_compact : IsCompact K := by
    show IsCompact ((fun p : ℝ × ℝ => γ p.1 + p.2 • ξ p.1) ''
      (Set.Icc a b ×ˢ s))
    refine IsCompact.image_of_continuousOn (isCompact_Icc.prod isCompact_Icc) ?_
    refine ContinuousOn.add ?_ ?_
    · exact hγcont.comp continuousOn_fst (fun p hp => hp.1)
    · exact continuousOn_snd.smul
        (hξ.continuous.continuousOn.comp continuousOn_fst (fun p _ => Set.mem_univ _))
  have hK_nc : ∀ y ∈ K, ∀ i j, i ≠ j → y i ≠ y j := by
    rintro y ⟨p, hp, rfl⟩ i j hij
    exact hnc_pert_ne p.2 hp.2 p.1 hp.1 i j hij
  have hK_mem : ∀ x ∈ s, ∀ t ∈ Set.Icc a b, γ t + x • ξ t ∈ K :=
    fun x hx t ht => ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  have hK_nc' : ∀ y ∈ K, WithoutCollisions y :=
    fun y hy i j hij hd => hK_nc y hy i j hij (dist_eq_zero.mp hd)
  obtain ⟨C₀, hC₀⟩ :=
    Commons.Analysis.Calculus.exists_bound_fderiv_pairSum_inv_dist (m := m) hK_compact hK_nc
  let Cp : ℝ := max C₀ 0
  have hCp_nn : 0 ≤ Cp := le_max_right _ _
  have hCp : ∀ y ∈ K, ‖fderiv ℝ (U m) y‖ ≤ Cp := by
    intro y hy
    exact le_trans (by rw [U_eq_dist_sum m]; exact hC₀ y hy) (le_max_left C₀ 0)
  have hUK : ContinuousOn (U m) K := continuousOn_U.mono hK_nc'
  obtain ⟨CU, hCU⟩ := hK_compact.exists_bound_of_continuousOn hUK
  have hCU' : ∀ y ∈ K, U m y ≤ CU := fun y hy => le_trans (le_abs_self _) (hCU y hy)
  -- the perturbation family, its derivative and the perturbed action
  let F : ℝ → ℝ → ℝ := fun x t =>
    lagR m h (γ t + x • ξ t) (deriv γ t + x • deriv ξ t)
  let F' : ℝ → ℝ → ℝ := fun x t =>
    massInner m (deriv γ t + x • deriv ξ t) (deriv ξ t)
      + (fderiv ℝ (U m) (γ t + x • ξ t)) (ξ t)
  let A : ℝ → ℝ := fun x => ∫ t in a..b, F x t
  let C₁ : ℝ := (∑ i, m i) * Md
  let C₂ : ℝ := (∑ i, m i) * Md * (rad * Md) + Cp * Mξ
  let bound : ℝ → ℝ := fun t => C₁ * ‖deriv γ t‖ + C₂
  -- integrability of the kinetic energy
  have hkin0 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (deriv γ t))) < ⊤ :=
    lintegral_ofReal_kinetic_lt_top hmnn hh0 haction
  have hkinint : Integrable (fun t => kinetic m (deriv γ t)) (volume.restrict (Set.Ioc a b)) := by
    letI : MeasurableSpace (EN E N) := borel (EN E N)
    haveI : BorelSpace (EN E N) := ⟨rfl⟩
    refine ⟨?_, ?_⟩
    · exact (continuous_kinetic m).comp_aestronglyMeasurable
        (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac)
    · rw [HasFiniteIntegral]
      refine lt_of_eq_of_lt ?_ hkin0
      exact lintegral_congr fun t => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (kinetic_nonneg m hmnn (deriv γ t))]
  -- the `C^1` structure of the potential off collisions
  have hUcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (U m)
      {y : EN E N | ∀ i j, i ≠ j → y i ≠ y j} := by
    rw [U_eq_dist_sum m]
    exact (Commons.Analysis.Calculus.contDiffOn_pairSum_inv_dist (E := E) (N := N)
      (m := m)).of_le (by simp)
  have hUfderiv : ContinuousOn (fderiv ℝ (U m))
      {y : EN E N | ∀ i j, i ≠ j → y i ≠ y j} :=
    Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv
      Commons.Analysis.Calculus.isOpen_setOf_pairwise_ne hUcd
  have hξac : AbsolutelyContinuousOnInterval ξ a b :=
    ((hξ.contDiffOn).of_le (by simp)).absolutelyContinuousOnInterval
  -- measurability of the perturbation family
  have hFx_aesm : ∀ x ∈ s, AEStronglyMeasurable (fun t => F x t)
      (volume.restrict (Set.Ioc a b)) := by
    intro x hx
    letI : MeasurableSpace (EN E N) := borel (EN E N)
    haveI : BorelSpace (EN E N) := ⟨rfl⟩
    have hdγ : AEStronglyMeasurable (deriv γ) (volume.restrict (Set.Ioc a b)) :=
      Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
        hac
    have h1 : AEStronglyMeasurable (fun t => deriv γ t + x • deriv ξ t)
        (volume.restrict (Set.Ioc a b)) :=
      hdγ.add (hdξcont.aestronglyMeasurable.const_smul x)
    have h2 : AEStronglyMeasurable (fun t => kinetic m (deriv γ t + x • deriv ξ t))
        (volume.restrict (Set.Ioc a b)) :=
      (continuous_kinetic m).comp_aestronglyMeasurable h1
    have hpert_cont : ContinuousOn (fun t => γ t + x • ξ t) (Set.Icc a b) :=
      hγcont.add ((continuous_const (y := x)).continuousOn.smul hξ.continuous.continuousOn)
    have h3 : AEStronglyMeasurable (fun t => U m (γ t + x • ξ t))
        (volume.restrict (Set.Ioc a b)) :=
      (ContinuousOn.aestronglyMeasurable
        ((continuousOn_U.comp hpert_cont
          (fun t ht => hnc_pert x hx t ht)).mono Set.Ioc_subset_Icc_self)
        measurableSet_Ioc)
    have h4 : AEStronglyMeasurable (fun _ : ℝ => h) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_const
    have hfun : (fun t : ℝ => F x t) = (fun t : ℝ => kinetic m (deriv γ t + x • deriv ξ t))
        + ((fun t : ℝ => U m (γ t + x • ξ t)) + fun _ => h) := by
      funext t
      show (1 / 2) * ∑ i, m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
          + U m (γ t + x • ξ t) + h
        = kinetic m (deriv γ t + x • deriv ξ t) + (U m (γ t + x • ξ t) + h)
      rw [kinetic]; ring
    rw [hfun]
    exact h2.add (h3.add h4)
  have hF_meas : ∀ᶠ x in 𝓝 (0:ℝ), AEStronglyMeasurable (F x)
      (volume.restrict (Set.uIoc a b)) := by
    rw [uIoc_of_le hab.le]
    filter_upwards [hs_nhds] with x hx
    exact hFx_aesm x hx
  have hF_int : IntervalIntegrable (F 0) volume a b := by
    refine hInt0'.congr fun t ht => ?_
    show lagR m h (γ t) (deriv γ t) = lagR m h (γ t + 0 • ξ t) (deriv γ t + 0 • deriv ξ t)
    simp only [zero_smul, add_zero]
  have hF'_meas : AEStronglyMeasurable (F' 0) (volume.restrict (Set.uIoc a b)) := by
    rw [uIoc_of_le hab.le]
    letI : MeasurableSpace (EN E N) := borel (EN E N)
    haveI : BorelSpace (EN E N) := ⟨rfl⟩
    have hdγ : AEStronglyMeasurable (deriv γ) (volume.restrict (Set.Ioc a b)) :=
      Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
        hac
    have hdγi : ∀ i, AEStronglyMeasurable (fun t => (deriv γ t) i)
        (volume.restrict (Set.Ioc a b)) :=
      fun i => (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).comp_aestronglyMeasurable hdγ
    have hdξi : ∀ i, AEStronglyMeasurable (fun t => (deriv ξ t) i)
        (volume.restrict (Set.Ioc a b)) :=
      fun i => (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).comp_aestronglyMeasurable
        hdξcont.aestronglyMeasurable
    have hsum : AEStronglyMeasurable
        (fun t => ∑ i, m i * inner ℝ ((deriv γ t) i) ((deriv ξ t) i))
        (volume.restrict (Set.Ioc a b)) := by
      have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin N))
        (fun i _ => ((hdγi i).inner (hdξi i)).const_mul (m i))
      refine h.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [Finset.sum_apply]
    have hmass : AEStronglyMeasurable (fun t => massInner m (deriv γ t) (deriv ξ t))
        (volume.restrict (Set.Ioc a b)) := by
      rw [show (fun t => massInner m (deriv γ t) (deriv ξ t))
          = (fun t => ∑ i, m i * inner ℝ ((deriv γ t) i) ((deriv ξ t) i)) from by
        funext t; rfl]
      exact hsum
    have hpotcomp : ContinuousOn (fun t => fderiv ℝ (U m) (γ t)) (Set.Icc a b) :=
      hUfderiv.comp hγcont (fun t ht => hnc_ne t ht)
    have happ : Continuous (fun p : (EN E N →L[ℝ] ℝ) × EN E N => p.1 p.2) := by fun_prop
    have hpot : ContinuousOn (fun t => (fderiv ℝ (U m) (γ t)) (ξ t)) (Set.Icc a b) :=
      happ.comp_continuousOn (hpotcomp.prodMk hξ.continuous.continuousOn)
    have hgoal : AEStronglyMeasurable (fun t : ℝ => massInner m (deriv γ t) (deriv ξ t)
        + (fderiv ℝ (U m) (γ t)) (ξ t)) (volume.restrict (Set.Ioc a b)) :=
      hmass.add ((hpot.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    refine hgoal.congr (Filter.Eventually.of_forall fun t => ?_)
    show massInner m (deriv γ t) (deriv ξ t) + (fderiv ℝ (U m) (γ t)) (ξ t)
      = massInner m (deriv γ t + 0 • deriv ξ t) (deriv ξ t)
        + (fderiv ℝ (U m) (γ t + 0 • ξ t)) (ξ t)
    simp only [zero_smul, add_zero]
  -- the pointwise norm bound on the derivative family
  have hbnd : ∀ t ∈ Set.Icc a b, ∀ x ∈ s, ‖F' x t‖ ≤ bound t := by
    intro t ht x hx
    have hu : ‖deriv γ t + x • deriv ξ t‖ ≤ ‖deriv γ t‖ + rad * Md := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [hxr_of_mem x hx, hdξle t, norm_nonneg (deriv γ t), abs_nonneg x, hr_pos.le]
    have hw : ∀ i, ‖(deriv ξ t) i‖ ≤ Md :=
      fun i => (norm_apply_le_norm (deriv ξ t) i).trans (hdξle t)
    have hkin : ‖massInner m (deriv γ t + x • deriv ξ t) (deriv ξ t)‖
        ≤ (∑ i, m i) * ‖deriv γ t + x • deriv ξ t‖ * Md := by
      show ‖∑ i, m i * inner ℝ ((deriv γ t + x • deriv ξ t) i) ((deriv ξ t) i)‖ ≤ _
      exact Commons.Analysis.InnerProductSpace.norm_sum_mul_inner_le hmnn _ _ hMd_nn hw
    have hpot : ‖(fderiv ℝ (U m) (γ t + x • ξ t)) (ξ t)‖ ≤ Cp * Mξ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul (hCp _ (hK_mem x hx t ht)) (hξle t) (norm_nonneg _) hCp_nn
    calc ‖F' x t‖ ≤ ‖massInner m (deriv γ t + x • deriv ξ t) (deriv ξ t)‖
            + ‖(fderiv ℝ (U m) (γ t + x • ξ t)) (ξ t)‖ := by
          show ‖massInner m (deriv γ t + x • deriv ξ t) (deriv ξ t)
              + (fderiv ℝ (U m) (γ t + x • ξ t)) (ξ t)‖ ≤ _
          exact norm_add_le _ _
      _ ≤ (∑ i, m i) * (‖deriv γ t‖ + rad * Md) * Md + Cp * Mξ := by
          refine add_le_add ?_ hpot
          refine hkin.trans ?_
          have hS : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hmnn i
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hS) hMd_nn
      _ = bound t := by
          show _ = (∑ i, m i) * Md * ‖deriv γ t‖ + ((∑ i, m i) * Md * (rad * Md) + Cp * Mξ)
          ring
  have hFx_norm : ∀ x ∈ s, ∀ t ∈ Set.Icc a b,
      ‖F x t‖ ≤ 2 * kinetic m (deriv γ t) + ((∑ i, m i) * (rad * Md) ^ 2 + CU + h) := by
    intro x hx t ht
    have hxr : |x| ≤ rad := hxr_of_mem x hx
    have hnn : 0 ≤ lagR m h (γ t + x • ξ t) (deriv γ t + x • deriv ξ t) := by
      rw [lagR]
      have h1 := U_nonneg hmnn (γ t + x • ξ t)
      have h2 := kinetic_nonneg m hmnn (deriv γ t + x • deriv ξ t)
      rw [kinetic] at h2
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, lagR]
    have hterm : ∀ i : Fin N,
        m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
          ≤ m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2) := by
      intro i
      have h1 : ‖(deriv γ t + x • deriv ξ t) i‖ ≤ ‖(deriv γ t) i‖ + rad * Md := by
        rw [PiLp.add_apply, PiLp.smul_apply]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        have h2 : ‖(deriv ξ t) i‖ ≤ Md := (norm_apply_le_norm (deriv ξ t) i).trans (hdξle t)
        nlinarith [hxr, h2, norm_nonneg ((deriv γ t) i), abs_nonneg x, hMd_nn]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (‖(deriv γ t) i‖ + rad * Md) ^ 2
          ≤ 2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2 := by
        nlinarith [sq_nonneg (‖(deriv γ t) i‖ - rad * Md)]
      refine mul_le_mul_of_nonneg_left (h2.trans h3) (hmnn i)
    have hsum : ∑ i, m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
        ≤ ∑ i, m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2) :=
      Finset.sum_le_sum fun i _ => hterm i
    have hkin : ∑ i, m i * ‖(deriv γ t) i‖ ^ 2 = 2 * kinetic m (deriv γ t) := by
      rw [kinetic]; ring
    have hkey : (1 / 2) * ∑ i, m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
        ≤ 2 * kinetic m (deriv γ t) + (∑ i, m i) * (rad * Md) ^ 2 := by
      have hstep : (1 / 2) * ∑ i, m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2)
          = 2 * kinetic m (deriv γ t) + (∑ i, m i) * (rad * Md) ^ 2 := by
        have hsplit : ∀ i : Fin N, m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2)
            = (2 * (m i * ‖(deriv γ t) i‖ ^ 2)) + m i * (2 * (rad * Md) ^ 2) :=
          fun i => by ring
        have h3 : ∑ i, m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2)
            = ∑ i, ((2 * (m i * ‖(deriv γ t) i‖ ^ 2)) + m i * (2 * (rad * Md) ^ 2)) :=
          Finset.sum_congr rfl fun i _ => hsplit i
        rw [h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hkin]
        ring
      calc (1 / 2) * ∑ i, m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
          ≤ (1 / 2) * ∑ i, m i * (2 * ‖(deriv γ t) i‖ ^ 2 + 2 * (rad * Md) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = 2 * kinetic m (deriv γ t) + (∑ i, m i) * (rad * Md) ^ 2 := hstep
    have hU : U m (γ t + x • ξ t) ≤ CU := hCU' _ (hK_mem x hx t ht)
    calc (1 / 2) * ∑ i, m i * ‖(deriv γ t + x • deriv ξ t) i‖ ^ 2
          + U m (γ t + x • ξ t) + h
        ≤ (2 * kinetic m (deriv γ t) + (∑ i, m i) * (rad * Md) ^ 2) + CU + h := by
          linarith [hkey, hU]
      _ = 2 * kinetic m (deriv γ t) + ((∑ i, m i) * (rad * Md) ^ 2 + CU + h) := by ring
  have hFx_int : ∀ x ∈ s, Integrable (fun t => F x t) (volume.restrict (Set.Ioc a b)) := by
    intro x hx
    have hdom : Integrable (fun t => 2 * kinetic m (deriv γ t)
        + ((∑ i, m i) * (rad * Md) ^ 2 + CU + h)) (volume.restrict (Set.Ioc a b)) :=
      (hkinint.const_mul 2).add (integrable_const _)
    refine hdom.mono' (hFx_aesm x hx) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with t ht
    exact hFx_norm x hx t ⟨ht.1.le, ht.2⟩
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t :=
    Filter.Eventually.of_forall fun t ht x hx => by
      rw [uIoc_of_le hab.le] at ht
      exact hbnd t ⟨ht.1.le, ht.2⟩ x hx
  have hbound_int : IntervalIntegrable bound volume a b := by
    have h1 : IntervalIntegrable (fun t => C₁ * ‖deriv γ t‖) volume a b :=
      hderiv_int.const_mul C₁
    have h2 : IntervalIntegrable (fun _ : ℝ => C₂) volume a b := intervalIntegrable_const
    exact h1.add h2
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ s,
      HasDerivAt (fun x => F x t) (F' x t) x :=
    Filter.Eventually.of_forall fun t ht x hx => by
      rw [uIoc_of_le hab.le] at ht
      show HasDerivAt (fun ε : ℝ => lagR m h (γ t + ε • ξ t) (deriv γ t + ε • deriv ξ t))
        (massInner m (deriv γ t + x • deriv ξ t) (deriv ξ t)
          + (fderiv ℝ (U m) (γ t + x • ξ t)) (ξ t)) x
      exact hasDerivAt_lagR_perturb (q := γ t) (v := deriv γ t) (w := ξ t) (v' := deriv ξ t) x
        (hnc_pert x hx t ⟨ht.1.le, ht.2⟩)
  -- differentiability of the perturbed action
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := 0) (s := s) (a := a) (b := b) (μ := volume) (bound := bound)
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  obtain ⟨hF'_int, hA⟩ := hmain
  -- the endpoints of the perturbation are unchanged
  have hξa : ξ a = 0 := by
    by_contra hcon
    exact absurd (hts (subset_closure (Function.mem_support.mpr hcon))) (by simp)
  have hξb : ξ b = 0 := by
    by_contra hcon
    exact absurd (hts (subset_closure (Function.mem_support.mpr hcon))) (by simp)
  -- minimality
  have hloc : IsLocalMin A 0 := by
    show ∀ᶠ x in 𝓝 (0:ℝ), A 0 ≤ A x
    filter_upwards [hs_nhds] with x hx
    have hderiv_eq : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc a b →
        deriv (fun t => γ t + x • ξ t) t = deriv γ t + x • deriv ξ t :=
      deriv_add_smul_ae (γ := γ) (ξ := ξ) (ε := x) hac (hξ.differentiable (by decide))
    have hA0 : ENNReal.ofReal (A 0) = actionPot m h (γ a) (γ b) := by
      show ENNReal.ofReal (∫ t in a..b, F 0 t) = actionPot m h (γ a) (γ b)
      rw [show (fun t : ℝ => F 0 t) = fun t : ℝ => lagR m h (γ t) (deriv γ t) from by
        funext t
        show lagR m h (γ t + 0 • ξ t) (deriv γ t + 0 • deriv ξ t) = lagR m h (γ t) (deriv γ t)
        simp only [zero_smul, add_zero]]
      rw [← hmin]
      exact (actionOn_eq_ofReal_integral_lagR hab.le hmnn hh0 hac hnc haction).symm
    have hAx : actionPot m h (γ a) (γ b) ≤ ENNReal.ofReal (A x) := by
      have hσac : AbsolutelyContinuousOnInterval (fun t => γ t + x • ξ t) a b :=
        hac.add (AbsolutelyContinuousOnInterval.const_smul x hξac)
      have hσnc : ∀ t ∈ Set.Icc a b, WithoutCollisions ((fun t => γ t + x • ξ t) t) :=
        fun t ht => hnc_pert x hx t ht
      have hσ_int : Integrable (fun t => lagR m h ((fun t => γ t + x • ξ t) t)
          (deriv (fun t => γ t + x • ξ t) t)) (volume.restrict (Set.Ioc a b)) := by
        refine (hFx_int x hx).congr ?_
        change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioc a b),
          F x t = lagR m h ((fun t => γ t + x • ξ t) t) (deriv (fun t => γ t + x • ξ t) t)
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hderiv_eq] with t ht htI
        rw [ht htI]
      have hstep := actionPot_le_ofReal_integral_lagR (m := m) (h := h)
        (γ := fun t => γ t + x • ξ t) hab hmnn hh0 hσac hσnc hσ_int
      rw [show γ a + x • ξ a = γ a from by rw [hξa, smul_zero, add_zero],
          show γ b + x • ξ b = γ b from by rw [hξb, smul_zero, add_zero]] at hstep
      refine hstep.trans (le_of_eq ?_)
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hderiv_eq] with t ht htI
      have htI' : t ∈ Set.Ioc a b := by simpa only [uIoc_of_le hab.le] using htI
      rw [ht htI']
    have hAxnn : 0 ≤ A x := by
      show 0 ≤ ∫ t in a..b, F x t
      exact intervalIntegral.integral_nonneg hab.le fun t ht => by
        show 0 ≤ lagR m h (γ t + x • ξ t) (deriv γ t + x • deriv ξ t)
        rw [lagR]
        have h1 := U_nonneg hmnn (γ t + x • ξ t)
        have h2 := kinetic_nonneg m hmnn (deriv γ t + x • deriv ξ t)
        rw [kinetic] at h2
        linarith
    exact (ENNReal.ofReal_le_ofReal_iff hAxnn).mp (hA0.le.trans hAx)
  have hderiv_zero : deriv A 0 = 0 := hloc.deriv_eq_zero
  have hval : ∫ t in a..b, F' 0 t = 0 := by
    rw [← hA.deriv, hderiv_zero]
  rw [show (fun t : ℝ => massInner m (deriv γ t) (deriv ξ t)
      + (fderiv ℝ (U m) (γ t)) (ξ t)) = fun t : ℝ => F' 0 t from by
    funext t
    show _ = massInner m (deriv γ t + 0 • deriv ξ t) (deriv ξ t)
      + (fderiv ℝ (U m) (γ t + 0 • ξ t)) (ξ t)
    simp only [zero_smul, add_zero]]
  exact hval


/-! ## The scalar (weighted) weak Euler--Lagrange equation -/

/-- Linearity of the mass inner product in its second argument. -/
lemma massInner_smul_right (m : Fin N → ℝ) (v w : EN E N) (c : ℝ) :
    massInner m v (c • w) = c * massInner m v w := by
  simp only [massInner, PiLp.smul_apply, real_inner_smul_right]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The mass inner product is bounded by `‖v‖ * ‖w‖ * ∑ mᵢ`. -/
lemma norm_massInner_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    ‖massInner m v w‖ ≤ (∑ i, m i) * ‖v‖ * ‖w‖ := by
  show ‖∑ i, m i * inner ℝ (v i) (w i)‖ ≤ _
  have hw : ∀ i, ‖w i‖ ≤ ‖w‖ := fun i => norm_apply_le_norm w i
  have := Commons.Analysis.InnerProductSpace.norm_sum_mul_inner_le hm v w (norm_nonneg w) hw
  simpa using this

/-- The gradient of the potential is continuous along a collision-free continuous curve. -/
lemma continuousOn_fderiv_U_comp {m : Fin N → ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hγcont : ContinuousOn γ (Set.Icc a b))
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t)) :
    ContinuousOn (fun t => fderiv ℝ (U m) (γ t)) (Set.Icc a b) := by
  have hWo : ∀ y ∈ {y : EN E N | WithoutCollisions y}, ∀ i j, i ≠ j → y i ≠ y j :=
    fun y hy i j hij hd => hy i j hij (by show dist (y i) (y j) = 0; rw [hd, dist_self])
  have hUcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (U m)
      {y : EN E N | WithoutCollisions y} := by
    have h := Commons.Analysis.Calculus.contDiffOn_pairSum_inv_dist (E := E) (N := N) (m := m)
    rw [U_eq_dist_sum m]
    exact ((h.mono hWo).of_le (by simp))
  have hUopen : IsOpen {y : EN E N | WithoutCollisions y} := by
    rw [show {y : EN E N | WithoutCollisions y}
        = {y : EN E N | ∀ i j, i ≠ j → y i ≠ y j} from by
      ext y
      exact ⟨hWo y, fun h i j hij hd => h i j hij (dist_eq_zero.mp hd)⟩]
    exact Commons.Analysis.Calculus.isOpen_setOf_pairwise_ne
  exact (Commons.Analysis.Calculus.FDeriv.continuousOn_fderiv hUopen hUcd).comp hγcont hnc

/-- The mass-weighted gradient of the potential is continuous along a curve. -/
lemma continuousOn_weightedGrad_comp {m : Fin N → ℝ} {γ : ℝ → EN E N} {s : Set ℝ}
    (h : ContinuousOn (fun t => fderiv ℝ (U m) (γ t)) s) :
    ContinuousOn (fun t => ∇_[m] (U m) (γ t)) s := by
  have hgrad : ContinuousOn (fun t => ∇ (U m) (γ t)) s :=
    ((InnerProductSpace.toDual ℝ (EN E N)).symm.toContinuousLinearEquiv.continuous).comp_continuousOn
      h
  rw [show (fun t => ∇_[m] (U m) (γ t))
      = fun t => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => E)).symm
          (fun i : Fin N => (m i)⁻¹ • (∇ (U m) (γ t)) i) from by
    funext t; rw [PiLp.continuousLinearEquiv_symm_apply]; rfl]
  refine ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => E)).symm.continuous).comp_continuousOn ?_
  refine continuousOn_pi.mpr fun i => ?_
  exact (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).comp_continuousOn hgrad).const_smul
    ((m i)⁻¹))

/-- **The scalar weak Euler--Lagrange equation.**  For an `h`-minimiser `γ` on `[a,b]`, every
smooth compactly supported `ψ` supported in `(a,b)` and every direction `w`,

  `∫_a^b ψ' ⟨γ̇, w⟩ₘ + ∫_a^b ψ ⟪∇ₘU(γ), w⟫ₘ = 0`. -/
theorem weak_first_variation_scalar {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Set.Ioo a b) (w : EN E N) :
    (∫ t in a..b, deriv ψ t * massInner m (deriv γ t) w)
      + ∫ t in a..b, ψ t * massInner m (∇_[m] (U m) (γ t)) w = 0 := by
  classical
  have hmnn : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hh0 : 0 ≤ h := hh.le
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by decide)
  -- finiteness and integrability of `deriv γ`
  have haction : actionOn m h γ a b < ⊤ := hmin ▸ hfin
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    by_cases hN : N = 0
    · subst hN
      exact ⟨1, one_pos, fun i => i.elim0⟩
    · haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
      set sf : Finset ℝ := Finset.univ.image m with hsf
      have hsfne : sf.Nonempty := hsf ▸ (Finset.univ_nonempty (α := Fin N)).image m
      refine ⟨sf.min' hsfne, ?_, ?_⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sf hsfne)
        rw [← hi]; exact hm i
      · intro i
        exact Finset.min'_le sf (m i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hderiv_int : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    intervalIntegrable_deriv_of_actionOn_lt_top hc hmc hh0 hab.le hac haction
  have hfderiv_cont : ContinuousOn (fun t => fderiv ℝ (U m) (γ t)) (Set.Icc a b) :=
    continuousOn_fderiv_U_comp (m := m) (by
      have h := hac.continuousOn
      rwa [uIcc_of_le hab.le] at h) hnc
  have hwg_cont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
    continuousOn_weightedGrad_comp hfderiv_cont
  -- the two summands are interval integrable
  obtain ⟨Mψ, hMψ⟩ := hψc.deriv.exists_bound_of_continuous (hψ.continuous_deriv (by decide))
  have hS : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hmnn i
  have hF : IntervalIntegrable (fun t => deriv ψ t * massInner m (deriv γ t) w) volume a b := by
    have hdom : IntervalIntegrable
        (fun t => (Mψ * ((∑ i, m i) * ‖w‖)) * ‖deriv γ t‖) volume a b :=
      hderiv_int.const_mul _
    refine hdom.mono_fun' ?_ ?_
    · rw [uIoc_of_le hab.le]
      letI : MeasurableSpace (EN E N) := borel (EN E N)
      haveI : BorelSpace (EN E N) := ⟨rfl⟩
      have hdγ : AEStronglyMeasurable (deriv γ) (volume.restrict (Set.Ioc a b)) :=
        Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac
      have hdγi : ∀ i, AEStronglyMeasurable (fun t => (deriv γ t) i)
          (volume.restrict (Set.Ioc a b)) :=
        fun i => (PiLp.continuous_apply 2 (fun _ : Fin N => E) i).comp_aestronglyMeasurable hdγ
      have hwi : ∀ i, AEStronglyMeasurable (fun _ : ℝ => w i) (volume.restrict (Set.Ioc a b)) :=
        fun i => aestronglyMeasurable_const
      have hsum : AEStronglyMeasurable
          (fun t => ∑ i, m i * inner ℝ ((deriv γ t) i) (w i))
          (volume.restrict (Set.Ioc a b)) := by
        have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin N))
          (fun i _ => ((hdγi i).inner (hwi i)).const_mul (m i))
        refine h.congr (Filter.Eventually.of_forall fun t => ?_)
        simp only [Finset.sum_apply]
      have hmass : AEStronglyMeasurable (fun t => massInner m (deriv γ t) w)
          (volume.restrict (Set.Ioc a b)) := by
        rw [show (fun t => massInner m (deriv γ t) w)
            = (fun t => ∑ i, m i * inner ℝ ((deriv γ t) i) (w i)) from by
          funext t; rfl]
        exact hsum
      exact ((hψ.continuous_deriv (by decide)).aestronglyMeasurable).mul hmass
    · filter_upwards with t
      have h1' : |massInner m (deriv γ t) w| ≤ (∑ i, m i) * ‖deriv γ t‖ * ‖w‖ := by
        rw [← Real.norm_eq_abs]; exact norm_massInner_le hmnn _ _
      have h4 : |deriv ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t
      have hMψnn : 0 ≤ Mψ := le_trans (abs_nonneg _) h4
      have h3 : ‖deriv ψ t * massInner m (deriv γ t) w‖
          = |deriv ψ t| * |massInner m (deriv γ t) w| := by
        simp only [Real.norm_eq_abs, abs_mul]
      rw [h3]
      calc |deriv ψ t| * |massInner m (deriv γ t) w|
          ≤ Mψ * ((∑ i, m i) * ‖deriv γ t‖ * ‖w‖) :=
            mul_le_mul h4 h1' (abs_nonneg _) hMψnn
        _ = (Mψ * ((∑ i, m i) * ‖w‖)) * ‖deriv γ t‖ := by ring
  have hG : IntervalIntegrable (fun t => ψ t * massInner m (∇_[m] (U m) (γ t)) w) volume a b := by
    have happ : Continuous (fun p : ℝ × (EN E N →L[ℝ] ℝ) => p.1 * (p.2 w)) := by fun_prop
    have hcont : ContinuousOn (fun t => ψ t * (fderiv ℝ (U m) (γ t)) w) (Set.Icc a b) :=
      happ.comp_continuousOn (hψ.continuous.continuousOn.prodMk hfderiv_cont)
    have hthis : IntervalIntegrable (fun t => ψ t * (fderiv ℝ (U m) (γ t)) w) volume a b :=
      (show ContinuousOn (fun t => ψ t * (fderiv ℝ (U m) (γ t)) w) (Set.uIcc a b) from by
        rw [uIcc_of_le hab.le]; exact hcont).intervalIntegrable
    refine IntervalIntegrable.congr (f := fun t => ψ t * (fderiv ℝ (U m) (γ t)) w)
      (g := fun t => ψ t * massInner m (∇_[m] (U m) (γ t)) w) ?_ hthis
    intro t ht
    have ht' : t ∈ Set.Icc a b := by
      rw [uIoc_of_le hab.le] at ht
      exact ⟨ht.1.le, ht.2⟩
    show ψ t * (fderiv ℝ (U m) (γ t)) w = ψ t * massInner m (∇_[m] (U m) (γ t)) w
    rw [fderiv_U_eq_massInner (fun i => ne_of_gt (hm i)) (γ t) (hnc t ht')]
  -- apply the vector-valued weak equation to `ψ • w`
  have hξC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ψ t • w) := hψ.smul_const w
  have hξcs : HasCompactSupport (fun t : ℝ => ψ t • w) :=
    hψc.smul_right (f' := fun _ : ℝ => w)
  have hξts : tsupport (fun t : ℝ => ψ t • w) ⊆ Set.Ioo a b :=
    (tsupport_smul_subset_left ψ (fun _ : ℝ => w)).trans hts
  have h0 := weak_first_variation (m := m) (h := h) (γ := γ) hm hh hab hac hnc hmin hfin
    hξC hξcs hξts
  have heq : (∫ t in a..b, (massInner m (deriv γ t) (deriv (fun t : ℝ => ψ t • w) t)
        + (fderiv ℝ (U m) (γ t)) ((fun t : ℝ => ψ t • w) t)))
      = ∫ t in a..b, (deriv ψ t * massInner m (deriv γ t) w
          + ψ t * massInner m (∇_[m] (U m) (γ t)) w) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t htI
    have htI' : t ∈ Set.Icc a b := by
      rw [uIoc_of_le hab.le] at htI
      exact ⟨htI.1.le, htI.2⟩
    rw [deriv_smul_const (hψd t) w,
      fderiv_U_eq_massInner (fun i => ne_of_gt (hm i)) (γ t) (hnc t htI'),
      massInner_smul_right, massInner_smul_right]
  rw [heq, intervalIntegral.integral_add hF hG] at h0
  exact h0

end Submission.NBody
