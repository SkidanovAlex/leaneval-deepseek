/-
# `Work.FQC.muQC_admissible_pg` — the deformation coefficient is admissible

The Beltrami coefficient `muQC d fl hfl.Pg t` of the quasiconformal deformation of the attracting
Écalle cylinder is *admissible* in the sense of `Work.MRMT.Found.Admissible`: measurable,
bounded by a constant `< 1` a.e., and of bounded support.

* **Measurability.**  The coefficient is defined as a pull-back along the dynamics from the
  fundamental domain `Pg` (the `Nat.find` first-entry time); writing it as the countable sum of
  the *disjoint* pieces `A n = {z | (T_c)^[n] z ∈ Pg ∧ ∀ k < n, (T_c)^[k] z ∉ Pg}` exhibits it as
  a countable sum of measurable functions (`AEStronglyMeasurable.tsum`), each piece carrying the
  fixed iterate `pullAntiIter (T_c) n`.
* **Bound.**  `pullHolo`/`pullAnti` never increase the modulus, and the modulus of the twist
  `ℓ_t` is `|t|/√(1+t²) < 1` everywhere (`Work.FQC.beltramiOf_ell_le`), so the coefficient is
  bounded by `|t|/√(1+t²)` pointwise.
* **Support.**  The support is contained in the parabolic basin of `Pg`.  A point of `Pa` has a
  convergent orbit under `F c = (T_c)^[10]`, hence a bounded orbit under `T_c`; the escape
  criterion (`BoundedOrbit ⟹ ‖·‖ ≤ max 2 ‖c‖`) then bounds the whole forward orbit of `Pg` by
  `max 2 ‖c‖`, and each backwards step `‖w‖² - ‖c‖ ≤ ‖T_c w‖` propagates this bound to the whole
  basin.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Ell
import Submission.Work.FQC.muQC_aux_beltrami
import Submission.Work.Escape.isCompact_filledJulia

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The pull-backs do not increase the modulus -/

private theorem norm_mul_div_star_le (a b : ℂ) : ‖a * b / star b‖ ≤ ‖a‖ := by
  rw [norm_div, norm_mul, norm_star, mul_div_assoc]
  exact mul_le_of_le_one_right (norm_nonneg a) (div_self_le_one ‖b‖)

private theorem norm_pullAnti_le (μ f : ℂ → ℂ) (z : ℂ) : ‖pullAnti μ f z‖ ≤ ‖μ (f z)‖ := by
  have h := norm_mul_div_star_le (star (μ (f z))) (MRMT.dzbar f z)
  rw [pullAnti]
  simpa only [norm_star] using h

private theorem norm_pullHolo_le (ν φ : ℂ → ℂ) (z : ℂ) : ‖pullHolo ν φ z‖ ≤ ‖ν (φ z)‖ := by
  have h := norm_mul_div_star_le (ν (φ z)) (star (deriv φ z))
  rw [pullHolo]
  simpa only [star_star] using h

private theorem norm_pullAntiIter_le (f : ℂ → ℂ) (n : ℕ) (μ : ℂ → ℂ) (z : ℂ) :
    ‖pullAntiIter f n μ z‖ ≤ ‖μ ((f^[n]) z)‖ := by
  induction n generalizing z with
  | zero => simpa [pullAntiIter]
  | succ n ih =>
      rw [pullAntiIter_succ]
      calc ‖pullAnti (pullAntiIter f n μ) f z‖ ≤ ‖pullAntiIter f n μ (f z)‖ :=
            norm_pullAnti_le _ _ _
        _ ≤ ‖μ ((f^[n]) (f z))‖ := ih (f z)
        _ = ‖μ ((f^[n+1]) z)‖ := by rw [Function.iterate_succ_apply]

private theorem norm_pullHoloOn_le (ν φ : ℂ → ℂ) (P : Set ℂ) (z : ℂ) :
    ‖pullHoloOn ν φ P z‖ ≤ ‖ν (φ z)‖ := by
  unfold pullHoloOn
  split
  · exact norm_pullHolo_le ν φ z
  · simp

/-- The modulus of the dilatation of the twist `ℓ_t` is `< 1`. -/
private theorem abs_div_sqrt_lt_one (t : ℝ) : |t| / Real.sqrt (1 + t^2) < 1 := by
  have h2 : 0 < Real.sqrt (1 + t^2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_one h2, ← Real.sqrt_sq_eq_abs, Real.sqrt_lt_sqrt_iff (by positivity)]
  nlinarith [sq_nonneg t]

/-- The pointwise bound on the deformation coefficient. -/
private theorem muQC_norm_le {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) (z : ℂ) :
    ‖muQC d fl hfl.Pg t z‖ ≤ |t| / Real.sqrt (1 + t^2) := by
  by_cases h : ∃ n : ℕ, (Tantibar c)^[n] z ∈ hfl.Pg
  · rw [muQC_of_mem d (show z ∈ basin d hfl.Pg from h)]
    calc ‖pullAntiIter (Tantibar c) (Nat.find h)
            (pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z‖
        ≤ ‖pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg ((Tantibar c)^[Nat.find h] z)‖ :=
          norm_pullAntiIter_le _ _ _ _
      _ ≤ ‖MRMT.beltramiOf (ell t) (fl.φa ((Tantibar c)^[Nat.find h] z))‖ :=
          norm_pullHoloOn_le _ _ _ _
      _ ≤ |t| / Real.sqrt (1 + t^2) := beltramiOf_ell_le t _
  · rw [muQC_of_notMem d h]
    simpa using div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)

/-! ## 2. Bounded support -/

private theorem norm_Tantibar_le (c w : ℂ) : ‖Tantibar c w‖ ≤ ‖w‖^2 + ‖c‖ := by
  have h : Tantibar c w = (starRingEnd ℂ w)^2 + c := rfl
  rw [h]
  calc ‖(starRingEnd ℂ w)^2 + c‖ ≤ ‖(starRingEnd ℂ w)^2‖ + ‖c‖ := norm_add_le _ _
    _ = ‖w‖^2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]

/-- An explicit bound for the `r`-th iterate of a point of norm `≤ B`: the recursion
`x ↦ x² + ‖c‖`. -/
private def orbitBound (c : ℂ) (B : ℝ) : ℕ → ℝ
  | 0 => max B 1
  | (r+1) => (orbitBound c B r)^2 + ‖c‖

private theorem orbitBound_one_le (c : ℂ) (B : ℝ) : ∀ r, 1 ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_max_right B 1
  | succ r ih =>
      have hc0 : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
      show 1 ≤ (orbitBound c B r)^2 + ‖c‖
      nlinarith [sq_nonneg (orbitBound c B r), ih]

private theorem orbitBound_step_le (c : ℂ) (B : ℝ) (r : ℕ) :
    orbitBound c B r ≤ orbitBound c B (r+1) := by
  have hc0 : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : 1 ≤ orbitBound c B r := orbitBound_one_le c B r
  show orbitBound c B r ≤ (orbitBound c B r)^2 + ‖c‖
  nlinarith

private theorem orbitBound_mono (c : ℂ) (B : ℝ) : Monotone (orbitBound c B) := by
  intro r s hrs
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih => exact le_trans ih (orbitBound_step_le c B s)

private theorem norm_iterate_le_orbitBound (c : ℂ) (w : ℂ) {B : ℝ} (hB : ‖w‖ ≤ B) :
    ∀ r, ‖(Tantibar c)^[r] w‖ ≤ orbitBound c B r := by
  intro r
  induction r with
  | zero => exact le_trans hB (le_max_left B 1)
  | succ r ih =>
      have hstep : ‖(Tantibar c)^[r+1] w‖ ≤ ‖(Tantibar c)^[r] w‖^2 + ‖c‖ := by
        rw [Function.iterate_succ_apply']
        exact norm_Tantibar_le c _
      have hmono : ‖(Tantibar c)^[r] w‖^2 ≤ (orbitBound c B r)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) ih 2
      show ‖(Tantibar c)^[r+1] w‖ ≤ (orbitBound c B r)^2 + ‖c‖
      linarith

/-- A point whose orbit under the holomorphic return map `F c = (T_c)^[10]` converges (to the
parabolic point) has a bounded orbit under `T_c` itself. -/
private theorem orbit_bounded_of_tendsto_F {c z : ℂ} {w : ℂ}
    (h : Tendsto (fun q : ℕ => (F c)^[q] z) atTop (nhds w)) :
    Work.ParamRays.BoundedOrbit c z := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ q : ℕ, ‖(F c)^[q] z‖ ≤ B := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto (fun q : ℕ => (F c)^[q] z) h
      ).subset_closedBall (0:ℂ)
    exact ⟨R, fun q => by
      have h1 := hR (Set.mem_range_self q)
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1⟩
  refine ⟨orbitBound c B 9, fun n => ?_⟩
  show ‖(Tantibar c)^[n] z‖ ≤ orbitBound c B 9
  set q := n / 10 with hq
  set r := n % 10 with hr
  have hr10 : r ≤ 9 := by omega
  have hkey : (Tantibar c)^[n] z = (Tantibar c)^[r] ((F c)^[q] z) := by
    have hn : n = r + 10 * q := by omega
    rw [hn, Function.iterate_add_apply, Function.iterate_mul, ← F_eq_iterate c]
  rw [hkey]
  exact le_trans (norm_iterate_le_orbitBound c _ (hB q) r) (orbitBound_mono c B hr10)

/-- All points of the attracting petal have bounded orbits under `T_c`. -/
private theorem pa_boundedOrbit {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) {z : ℂ}
    (hz : z ∈ fl.Pa) : Work.ParamRays.BoundedOrbit c z :=
  orbit_bounded_of_tendsto_F (fl.tendsto_Pa z hz)

/-- The forward orbit of a point of the fundamental domain `Pg` is bounded by the escape radius
`max 2 ‖c‖`. -/
private theorem mem_Pg_norm_iterate_le {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) {z : ℂ} (hz : z ∈ hfl.Pg) (n : ℕ) :
    ‖(Tantibar c)^[n] z‖ ≤ max 2 ‖c‖ :=
  Work.ParamRays.norm_le_max_of_bounded c _
    (Work.ParamRays.BoundedOrbit.shift (pa_boundedOrbit d fl (hfl.Pg_sub hz)) n)

/-- The backwards step: if `‖T_c w‖ ≤ max 2 ‖c‖` then also `‖w‖ ≤ max 2 ‖c‖`. -/
private theorem norm_le_max2_of_norm_Tantibar_le {c w : ℂ}
    (h : ‖Tantibar c w‖ ≤ max 2 ‖c‖) : ‖w‖ ≤ max 2 ‖c‖ := by
  have hN : (0:ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left 2 ‖c‖)
  have h4 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left 2 ‖c‖
  have h2 : ‖c‖ ≤ max 2 ‖c‖ := le_max_right 2 ‖c‖
  have h3 : max 2 ‖c‖ + ‖c‖ ≤ (max 2 ‖c‖)^2 := by nlinarith [norm_nonneg c]
  have hsq : ‖w‖^2 ≤ (max 2 ‖c‖)^2 := by
    have h1 := Work.ParamRays.norm_sq_sub_le_norm_Tantibar c w
    nlinarith [norm_nonneg w]
  have h5 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg hN] at h5

/-- The parabolic basin of `Pg` is bounded by the escape radius. -/
private theorem basin_subset_closedBall {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) (hfl : PetalInput d fl) :
    basin d hfl.Pg ⊆ Metric.closedBall 0 (max 2 ‖c‖) := by
  intro z hz
  obtain ⟨n, hn⟩ := hz
  have hmain : ∀ j, j ≤ n → ‖(Tantibar c)^[n - j] z‖ ≤ max 2 ‖c‖ := by
    intro j
    induction j with
    | zero => intro _; simpa using mem_Pg_norm_iterate_le d fl hfl hn 0
    | succ j ih =>
        intro hj
        have hj' : j ≤ n := by omega
        have hk : n - j = (n - (j+1)) + 1 := by omega
        have hT : (Tantibar c)^[n - j] z = Tantibar c ((Tantibar c)^[n - (j+1)] z) := by
          rw [hk, Function.iterate_succ_apply']
        exact norm_le_max2_of_norm_Tantibar_le (by rw [← hT]; exact ih hj')
  have hfin := hmain n le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at hfin
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]

private theorem support_muQC_subset_basin {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    Function.support (muQC d fl hfl.Pg t) ⊆ basin d hfl.Pg := by
  intro z hz
  by_contra h
  exact hz (muQC_of_notMem d h)

private theorem isBounded_support_muQC {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    Bornology.IsBounded (Function.support (muQC d fl hfl.Pg t)) :=
  Metric.isBounded_closedBall.subset
    (Subset.trans (support_muQC_subset_basin d fl hfl t) (basin_subset_closedBall d fl hfl))

/-! ## 3. Measurability -/

private theorem measurable_dz (f : ℂ → ℂ) : Measurable fun z => MRMT.dz f z := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ f z) (1:ℂ) := measurable_fderiv_apply_const ℝ f 1
  have h2 : Measurable fun z : ℂ => (fderiv ℝ f z) Complex.I :=
    measurable_fderiv_apply_const ℝ f Complex.I
  have h : Measurable fun z : ℂ =>
      ((fderiv ℝ f z) (1:ℂ) - Complex.I * (fderiv ℝ f z) Complex.I) / 2 :=
    (h1.sub (measurable_const.mul h2)).div_const 2
  unfold MRMT.dz
  exact h

private theorem measurable_dzbar (f : ℂ → ℂ) : Measurable fun z => MRMT.dzbar f z := by
  have h1 : Measurable fun z : ℂ => (fderiv ℝ f z) (1:ℂ) := measurable_fderiv_apply_const ℝ f 1
  have h2 : Measurable fun z : ℂ => (fderiv ℝ f z) Complex.I :=
    measurable_fderiv_apply_const ℝ f Complex.I
  have h : Measurable fun z : ℂ =>
      ((fderiv ℝ f z) (1:ℂ) + Complex.I * (fderiv ℝ f z) Complex.I) / 2 :=
    (h1.add (measurable_const.mul h2)).div_const 2
  unfold MRMT.dzbar
  exact h

private theorem measurable_beltramiOf (f : ℂ → ℂ) :
    Measurable fun z => MRMT.beltramiOf f z := by
  have h : Measurable fun z : ℂ => MRMT.dzbar f z / MRMT.dz f z :=
    (measurable_dzbar f).div (measurable_dz f)
  unfold MRMT.beltramiOf
  exact h

private theorem measurable_pullAnti {μ f : ℂ → ℂ} (hμ : Measurable μ) (hf : Measurable f) :
    Measurable (pullAnti μ f) := by
  have h1 : Measurable fun z : ℂ => star (μ (f z)) :=
    Complex.continuous_conj.measurable.comp (hμ.comp hf)
  have h2 : Measurable fun z : ℂ => MRMT.dzbar f z := measurable_dzbar f
  have h3 : Measurable fun z : ℂ => star (MRMT.dzbar f z) :=
    Complex.continuous_conj.measurable.comp h2
  have h : Measurable fun z : ℂ => star (μ (f z)) * MRMT.dzbar f z / star (MRMT.dzbar f z) :=
    (h1.mul h2).div h3
  unfold pullAnti
  exact h

private theorem measurable_pullAntiIter {μ f : ℂ → ℂ} (hμ : Measurable μ) (hf : Measurable f) :
    ∀ n : ℕ, Measurable (pullAntiIter f n μ) := by
  intro n
  induction n with
  | zero => simpa [pullAntiIter] using hμ
  | succ n ih => rw [pullAntiIter_succ]; exact measurable_pullAnti ih hf

private theorem measurable_pullHoloOn {ν φ : ℂ → ℂ} {P : Set ℂ} (hν : Measurable ν)
    (hφ : Measurable (P.indicator φ)) (hP : MeasurableSet P) :
    Measurable (pullHoloOn ν φ P) := by
  have hfun : pullHoloOn ν φ P = fun z => if z ∈ P then
      ν ((P.indicator φ) z) * star (deriv φ z) / deriv φ z else 0 := by
    funext z
    by_cases hz : z ∈ P
    · rw [Set.indicator_of_mem hz]
      simp only [pullHoloOn, hz, ite_true]
    · simp [pullHoloOn, hz]
  rw [hfun]
  refine Measurable.ite hP ?_ measurable_const
  have h1 : Measurable fun z : ℂ => ν ((P.indicator φ) z) := hν.comp hφ
  have h2 : Measurable fun z : ℂ => star (deriv φ z) :=
    Complex.continuous_conj.measurable.comp (measurable_deriv φ)
  exact (h1.mul h2).div (measurable_deriv φ)

/-- **Measurability of the deformation coefficient.**  `muQC` is the sum of the disjoint pieces
on which the first-entry time into `Pg` is a fixed `n`; on such a piece it is the fixed pull-back
`pullAntiIter (T_c) n` of the coefficient on `Pg`. -/
private theorem muQC_aestronglyMeasurable {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hfl : PetalInput d fl) (t : ℝ) :
    AEStronglyMeasurable (muQC d fl hfl.Pg t) volume := by
  have hnu : Measurable fun z : ℂ => MRMT.beltramiOf (ell t) z := measurable_beltramiOf (ell t)
  have hfT : Measurable (Tantibar c) :=
    ((Complex.continuous_conj.pow 2).add continuous_const).measurable
  have hPmeas : MeasurableSet hfl.Pg := hfl.Pg_open.measurableSet
  have hν0 : Measurable (pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) :=
    measurable_pullHoloOn hnu hfl.indicator_measurable hPmeas
  have hμn : ∀ n : ℕ, AEStronglyMeasurable
      (pullAntiIter (Tantibar c) n (pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg)) volume :=
    fun n => (measurable_pullAntiIter hν0 hfT n).aestronglyMeasurable
  let A : ℕ → Set ℂ := fun n => {z : ℂ | (Tantibar c)^[n] z ∈ hfl.Pg ∧
    ∀ k : ℕ, k < n → (Tantibar c)^[k] z ∉ hfl.Pg}
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    have h1 : MeasurableSet {z : ℂ | (Tantibar c)^[n] z ∈ hfl.Pg} :=
      hPmeas.preimage (hfT.iterate n)
    have h2 : MeasurableSet {z : ℂ | ∀ k : ℕ, k < n → (Tantibar c)^[k] z ∉ hfl.Pg} := by
      have hb := Set.Finite.measurableSet_biInter
        (f := fun k : ℕ => {z : ℂ | (Tantibar c)^[k] z ∉ hfl.Pg}) (Set.finite_Iio n)
        (fun k hk => (hPmeas.preimage (hfT.iterate k)).compl)
      convert hb using 1
      ext z
      simp [Set.mem_iInter]
    exact h1.inter h2
  have htsum : AEStronglyMeasurable
      (fun z : ℂ => ∑' n : ℕ, (A n).indicator (fun z => pullAntiIter (Tantibar c) n
        (pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z) z) volume :=
    MeasureTheory.AEStronglyMeasurable.tsum (fun n => (hμn n).indicator (hAmeas n))
  refine htsum.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ basin d hfl.Pg
  · have hnm : (Tantibar c)^[Nat.find hz] z ∈ hfl.Pg := Nat.find_spec hz
    have hmin : ∀ k : ℕ, k < Nat.find hz → (Tantibar c)^[k] z ∉ hfl.Pg :=
      fun k hk => Nat.find_min hz hk
    have hmemA : z ∈ A (Nat.find hz) := ⟨hnm, hmin⟩
    rw [tsum_eq_single (Nat.find hz) ?_, Set.indicator_of_mem hmemA]
    · exact (muQC_of_mem d hz).symm
    · intro n hn
      refine Set.indicator_of_notMem ?_ _
      intro hzA
      have hnf : Nat.find hz = n := (Nat.find_eq_iff hz).mpr ⟨hzA.1, hzA.2⟩
      exact hn hnf.symm
  · rw [muQC_of_notMem d hz]
    have h0 : ∀ n : ℕ, (A n).indicator (fun z => pullAntiIter (Tantibar c) n
        (pullHoloOn (MRMT.beltramiOf (ell t)) fl.φa hfl.Pg) z) z = 0 := by
      intro n
      refine Set.indicator_of_notMem ?_ _
      intro hzA
      exact hz ⟨n, hzA.1⟩
    simp [h0]

/-! ## 4. The coefficient is admissible -/

theorem muQC_admissible_pg {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁) (hfl : Work.FQC.PetalInput d fl) (t : ℝ) : Work.MRMT.Found.Admissible (Work.FQC.muQC d fl hfl.Pg t) := by
  refine ⟨muQC_aestronglyMeasurable d fl hfl t, ?_, isBounded_support_muQC d fl hfl t⟩
  refine ⟨|t| / Real.sqrt (1 + t^2), abs_div_sqrt_lt_one t, ?_⟩
  exact Filter.Eventually.of_forall fun z => muQC_norm_le d fl hfl t z

end Work.FQC
