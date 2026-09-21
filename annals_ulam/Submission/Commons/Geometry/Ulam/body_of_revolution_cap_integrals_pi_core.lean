import Mathlib
import Submission.Commons.Geometry.Ulam.sum_Ioi_fin_succ
import Submission.Commons.Geometry.Ulam.integral_fin_ball_coord_zero
import Submission.Commons.Geometry.Ulam.mem_closedBall_zero_sqrt_iff
import Submission.Commons.Geometry.Ulam.integral_fin_ball_section_coord_zero
import Submission.Commons.Geometry.Ulam.integral_fin_ball_section_affine_not_integrable
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

private lemma cap_on_measurableSet_fin_ball_le {m : ℕ} (c : ℝ) :
    MeasurableSet {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ c} := by
  have hsum : Measurable (fun y : Fin m → ℝ => ∑ j : Fin m, (y j)^2) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
    intro j hj
    exact (measurable_pi_apply j).pow measurable_const
  exact measurableSet_le hsum measurable_const

private lemma cap_on_measurableSet_section {m : ℕ} (L R : ℝ) :
    MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2} := by
  have h1 : MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ≤ L} := by
    exact measurableSet_le (measurable_fst) measurable_const
  have h2 : MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2} := by
    have hz : Measurable (fun q : ℝ × (Fin m → ℝ) => q.1 ^ 2) :=
      (measurable_fst.pow measurable_const)
    have hsum : Measurable (fun q : ℝ × (Fin m → ℝ) => ∑ j : Fin m, (q.2 j)^2) := by
      refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
      intro j hj
      have hpj : Measurable (fun q : ℝ × (Fin m → ℝ) => q.2 j) :=
        (measurable_pi_apply j).comp measurable_snd
      exact hpj.pow measurable_const
    exact measurableSet_le (hz.add hsum) measurable_const
  exact h1.inter h2

private lemma cap_on_sq_lt_sq_of_lt_neg {R z : ℝ} (hR : 0 ≤ R) (hz : z < -R) :
    R ^ 2 < z ^ 2 := by
  have hz_neg : z < 0 := by linarith
  have hR_lt_negz : R < -z := by linarith
  rw [sq_lt_sq]
  simpa [abs_of_nonneg hR, abs_of_neg hz_neg] using hR_lt_negz

private lemma cap_on_sq_lt_sq_of_lt_of_nonneg_left {R z : ℝ} (hR : 0 ≤ R) (h : R < z) :
    R ^ 2 < z ^ 2 := by
  have hz_pos : 0 < z := lt_of_le_of_lt hR h
  rw [sq_lt_sq]
  simpa [abs_of_nonneg hR, abs_of_nonneg hz_pos.le] using h

private lemma cap_on_fin_ball_le_empty_of_lt_neg {m : ℕ} {R z : ℝ} (hR : 0 ≤ R) (hz : z < -R) :
    {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2} = ∅ := by
  have hz_sq_gt : R ^ 2 < z ^ 2 := cap_on_sq_lt_sq_of_lt_neg hR hz
  have hneg : R ^ 2 - z ^ 2 < 0 := by nlinarith
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy' : ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2 := by simpa using hy
  have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
    exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
  nlinarith

private lemma cap_on_section_integral_eq {m : ℕ} {L R : ℝ} {φt : ℝ → ℝ} {ψ : (Fin m → ℝ) → ℝ}
    (hR : 0 ≤ R) {z : ℝ} (hz : z ≠ -R) :
    (∫ y : Fin m → ℝ,
      ({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}.indicator
        (fun q => φt q.1 * ψ q.2)) (z, y))
    = (Set.Ioc (-R) (min R L)).indicator
        (fun w => φt w * ∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}, ψ y) z := by
  classical
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}
  let B : ℝ → Set (Fin m → ℝ) := fun w => {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}
  let I : Set ℝ := Set.Ioc (-R) (min R L)
  by_cases hzI : z ∈ I
  · have hzI' : -R < z ∧ z ≤ min R L := by simpa [I] using hzI
    have hzL : z ≤ L := by
      have hmin : min R L ≤ L := min_le_right R L
      exact le_trans hzI'.2 hmin
    have hzR : z ≤ R := by
      have hmin : min R L ≤ R := min_le_left R L
      exact le_trans hzI'.2 hmin
    have hz_lower : -R ≤ z := le_of_lt hzI'.1
    have hB_meas : MeasurableSet (B z) := by
      dsimp [B]
      exact cap_on_measurableSet_fin_ball_le (R ^ 2 - z ^ 2)
    have hmem_iff : ∀ y : Fin m → ℝ, ((z, y) ∈ T ↔ y ∈ B z) := by
      intro y
      constructor
      · intro hq
        rcases hq with ⟨hz_le, hsum_le⟩
        dsimp [B]
        nlinarith
      · intro hy
        dsimp [B] at hy
        constructor
        · exact hzL
        · nlinarith
    have hfun_eq : (fun y : Fin m → ℝ => T.indicator (fun q => φt q.1 * ψ q.2) (z, y))
        = fun y => (B z).indicator (fun y => φt z * ψ y) y := by
      ext y
      by_cases hyB : y ∈ B z
      · have hq : (z, y) ∈ T := (hmem_iff y).mpr hyB
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hyB]
      · have hq : (z, y) ∉ T := by
          intro hq; exact hyB ((hmem_iff y).mp hq)
        rw [Set.indicator_apply, if_neg hq, Set.indicator_apply, if_neg hyB]
    calc
      ∫ y : Fin m → ℝ, T.indicator (fun q => φt q.1 * ψ q.2) (z, y)
          = ∫ y : Fin m → ℝ, (B z).indicator (fun y => φt z * ψ y) y := by
                rw [hfun_eq]
      _ = ∫ y : Fin m → ℝ in B z, φt z * ψ y := by
                rw [MeasureTheory.integral_indicator hB_meas]
      _ = φt z * ∫ y : Fin m → ℝ in B z, ψ y := by
                rw [MeasureTheory.integral_const_mul]
      _ = I.indicator (fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y) z := by
                rw [Set.indicator_of_mem hzI]
  · have h_left_zero : (∫ y : Fin m → ℝ, T.indicator (fun q => φt q.1 * ψ q.2) (z, y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with y
      by_cases hzL : z ≤ L
      · by_cases hz_le_neg : z ≤ -R
        · have hz_lt_neg : z < -R := lt_of_le_of_ne hz_le_neg hz
          have hz_sq_gt : R ^ 2 < z ^ 2 := cap_on_sq_lt_sq_of_lt_neg hR hz_lt_neg
          have hnot : (z, y) ∉ T := by
            intro hq
            rcases hq with ⟨_, hle⟩
            have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
              exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
            nlinarith
          rw [Set.indicator_apply, if_neg hnot]
          simp
        · have hlt : -R < z := lt_of_not_ge hz_le_neg
          have hz_not_min : ¬ z ≤ min R L := by
            intro hmin
            exact hzI (by simpa [I] using And.intro hlt hmin)
          have hmin_lt : min R L < z := lt_of_not_ge hz_not_min
          have hz_gt_R : R < z := by
            by_cases hRL : R ≤ L
            · have hmin_eq : min R L = R := min_eq_left hRL
              linarith
            · have hLR : L < R := lt_of_not_ge hRL
              have hmin_eq : min R L = L := min_eq_right (le_of_lt hLR)
              linarith
          have hz_sq_gt : R ^ 2 < z ^ 2 := cap_on_sq_lt_sq_of_lt_of_nonneg_left hR hz_gt_R
          have hnot : (z, y) ∉ T := by
            intro hq
            rcases hq with ⟨_, hle⟩
            have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
              exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
            nlinarith
          rw [Set.indicator_apply, if_neg hnot]
          simp
      · have hz_gt_L : L < z := lt_of_not_ge hzL
        have hnot : (z, y) ∉ T := by
          intro hq
          rcases hq with ⟨hz_le, _⟩
          linarith
        rw [Set.indicator_apply, if_neg hnot]
        simp
    have h_right_zero : I.indicator (fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y) z = 0 := by
      rw [Set.indicator_apply, if_neg hzI]
    rw [h_left_zero, h_right_zero]

private lemma cap_on_integral_section_eq_interval {m : ℕ} [Nonempty (Fin m)] {L R : ℝ} {φt : ℝ → ℝ}
    {ψ : (Fin m → ℝ) → ℝ}
    (hR : 0 ≤ R)
    (h_int : Integrable (({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}).indicator (fun q : ℝ × (Fin m → ℝ) => φt q.1 * ψ q.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) :
    (∫ q : ℝ × (Fin m → ℝ) in {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2},
        φt q.1 * ψ q.2
      ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))
    = ∫ z in (-R)..(min R L),
        φt z * (∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2}, ψ y) := by
  classical
  let μℝ : Measure ℝ := volume
  let μy : Measure (Fin m → ℝ) := volume
  let ν : Measure (ℝ × (Fin m → ℝ)) := μℝ.prod μy
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}
  let F : ℝ × (Fin m → ℝ) → ℝ := fun q => φt q.1 * ψ q.2
  let B : ℝ → Set (Fin m → ℝ) := fun w => {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}
  let G : ℝ → ℝ := fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y
  let I : Set ℝ := Set.Ioc (-R) (min R L)
  have hT_meas : MeasurableSet T := by
    simpa [T] using cap_on_measurableSet_section (m := m) L R
  have hF_ind_int : Integrable (T.indicator F) ν := by
    simpa [T, ν, μℝ, μy, F] using h_int
  have hFub := MeasureTheory.integral_prod (μ := μℝ) (ν := μy) (T.indicator F) hF_ind_int
  have hset_int : (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q, T.indicator F q ∂ν := by
    rw [MeasureTheory.integral_indicator hT_meas]
  have h_all : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) =
      ∫ z : ℝ, ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy ∂μℝ := by
    simpa [ν, μℝ, μy, F] using hFub
  have h_ae : (fun z => ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy) =ᵐ[μℝ] I.indicator G := by
    filter_upwards [Measure.ae_ne μℝ (-R)] with z hz
    have hsec := cap_on_section_integral_eq (m := m) (L := L) (R := R) (φt := φt) (ψ := ψ) hR hz
    simpa [T, F, B, G, I, μℝ, μy] using hsec
  have h_zint : (∫ z : ℝ, ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy ∂μℝ) =
      ∫ z : ℝ, I.indicator G z ∂μℝ := by
    exact integral_congr_ae h_ae
  have h_Iint : (∫ z : ℝ, I.indicator G z ∂μℝ) = ∫ z : ℝ in I, G z ∂μℝ := by
    rw [MeasureTheory.integral_indicator]
    exact measurableSet_Ioc
  have h_all_I : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) = ∫ z : ℝ in I, G z ∂μℝ := by
    rw [h_all, h_zint, h_Iint]
  by_cases hle : -R ≤ min R L
  · have h_interval : (∫ z in (-R)..(min R L), G z) = ∫ z : ℝ in I, G z ∂μℝ := by
      rw [intervalIntegral.integral_of_le hle]
    calc
      (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν := hset_int
      _ = ∫ z : ℝ in I, G z ∂μℝ := h_all_I
      _ = ∫ z in (-R)..(min R L), G z := h_interval.symm
      _ = ∫ z in (-R)..(min R L), φt z * (∫ y : Fin m → ℝ in B z, ψ y) := by rfl
  · have hgt : min R L < -R := lt_of_not_ge hle
    have hI_empty : I = ∅ := by
      dsimp [I]
      exact Set.Ioc_eq_empty_of_le hgt.le
    have h_all_zero : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) = 0 := by
      rw [h_all_I, hI_empty, MeasureTheory.setIntegral_empty]
    have h_interval_zero : (∫ z in (-R)..(min R L), G z) = 0 := by
      rw [intervalIntegral.integral_of_ge hgt.le]
      have hset : (∫ z : ℝ in Set.Ioc (min R L) (-R), G z ∂μℝ) = 0 := by
        apply setIntegral_eq_zero_of_ae_eq_zero
        filter_upwards [Measure.ae_ne μℝ (-R)] with z hzne hzmem
        have hzmem' : min R L < z ∧ z ≤ -R := Set.mem_Ioc.mp hzmem
        have hz_lt : z < -R := lt_of_le_of_ne hzmem'.2 hzne
        have hB_empty : B z = ∅ := by
          dsimp [B]
          exact cap_on_fin_ball_le_empty_of_lt_neg hR hz_lt
        dsimp [G]
        rw [hB_empty]
        simp
      have hset_vol : (∫ z : ℝ in Set.Ioc (min R L) (-R), G z) = 0 := by
        simpa [μℝ] using hset
      simp [hset_vol]
    calc
      (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν := hset_int
      _ = 0 := h_all_zero
      _ = ∫ z in (-R)..(min R L), G z := h_interval_zero.symm
      _ = ∫ z in (-R)..(min R L), φt z * (∫ y : Fin m → ℝ in B z, ψ y) := by rfl

private lemma cap_on_measurableSet_target_S {m : ℕ} {a b s h : ℝ} {f : ℝ → ℝ}
    (hf_meas : Measurable f) :
    let S : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}
    MeasurableSet S := by
  intro S
  dsimp [S]
  have h1 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b} := by
    exact (measurableSet_Icc : MeasurableSet (Set.Icc (a : ℝ) b)).preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.2.1 ≤ s * p.1 + h} := by
    apply measurableSet_le
    · exact measurable_fst.comp measurable_snd
    · exact (measurable_const.mul measurable_fst).add measurable_const
  have h3 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) |
      p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2} := by
    apply measurableSet_le
    · have hz : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.1 ^ 2) :=
        (measurable_fst.comp measurable_snd).pow measurable_const
      have hsum : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => ∑ j : Fin m, (p.2.2 j)^2) := by
        refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
        intro j hj
        have hpj : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) :=
          (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
        exact hpj.pow measurable_const
      exact hz.add hsum
    · exact (hf_meas.comp measurable_fst).pow measurable_const
  exact h1.inter (h2.inter h3)


lemma integral_fin_ball_section_on {m : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ}
    {φ : ℝ → ℝ → ℝ} {ψ : (Fin m → ℝ) → ℝ}
    (hab : a ≤ b) (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f)
    (hφ_meas : Measurable (fun p : ℝ × ℝ => φ p.1 p.2))
    (hψ_meas : Measurable ψ)
    (h_int : Integrable (({p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}).indicator (fun p : ℝ × (ℝ × (Fin m → ℝ)) => φ p.1 p.2.1 * ψ p.2.2))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))) :
    let S : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}
    ∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S,
        φ p.1 p.2.1 * ψ p.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        φ t z * (∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y) := by
  classical
  intro S
  let μℝ : Measure ℝ := volume
  let μy : Measure (Fin m → ℝ) := volume
  let ν : Measure (ℝ × (Fin m → ℝ)) := μℝ.prod μy
  let P : Measure (ℝ × (ℝ × (Fin m → ℝ))) := μℝ.prod ν
  let g : ℝ × (ℝ × (Fin m → ℝ)) → ℝ := fun p => φ p.1 p.2.1 * ψ p.2.2
  let H : ℝ → ℝ := fun t => ∫ q : ℝ × (Fin m → ℝ), S.indicator g (t, q) ∂ν
  let K : ℝ → ℝ := fun t => ∫ z in (-f t)..(min (f t) (s * t + h)),
      φ t z * (∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y)
  have hS_meas : MeasurableSet S := by
    exact cap_on_measurableSet_target_S (m := m) (a := a) (b := b) (s := s) (h := h) (f := f) hf_meas
  have hg_ind_int : Integrable (S.indicator g) P := by
    simpa [P, ν, μℝ, μy, g, S, Set.mem_Icc] using h_int
  have hFub := MeasureTheory.integral_prod (μ := μℝ) (ν := ν) (S.indicator g) hg_ind_int
  have hLHS_ind : (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, g p ∂P) = ∫ p, S.indicator g p ∂P := by
    rw [MeasureTheory.integral_indicator hS_meas]
  have h_main : (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, g p ∂P) = ∫ t, H t ∂μℝ := by
    calc
      (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, g p ∂P) = ∫ p, S.indicator g p ∂P := hLHS_ind
      _ = ∫ t : ℝ, ∫ q : ℝ × (Fin m → ℝ), S.indicator g (t, q) ∂ν ∂μℝ := by
            simpa [P, ν, μℝ, μy, g, H] using hFub
  have hH_zero_compl : ∀ t : ℝ, t ∉ Set.Icc a b → H t = 0 := by
    intro t ht
    dsimp [H]
    apply integral_eq_zero_of_ae
    filter_upwards with q
    have hnot : (t, q) ∉ S := by
      intro hp
      rcases hp with ⟨htIcc, _⟩
      exact ht htIcc
    rw [Set.indicator_apply, if_neg hnot]
    simp
  have h_full_to_Icc : (∫ t : ℝ, H t ∂μℝ) = ∫ t : ℝ in Set.Icc a b, H t ∂μℝ := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc a b) (μ := μℝ)
      (f := H) hH_zero_compl
  have h_sections_int : ∀ᵐ t ∂μℝ, Integrable (fun q : ℝ × (Fin m → ℝ) => S.indicator g (t, q)) ν := by
    have h := hg_ind_int.prod_right_ae (μ := μℝ) (ν := ν)
    simpa [g] using h
  have hH_eq_K_ae : ∀ᵐ t ∂μℝ, t ∈ Set.Icc a b → H t = K t := by
    filter_upwards [h_sections_int] with t ht_int htIcc
    have hR : 0 ≤ f t := hf_nonneg t htIcc
    let L : ℝ := s * t + h
    let Tt : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ f t ^ 2}
    have hT_meas : MeasurableSet Tt := by
      simpa [Tt, L] using cap_on_measurableSet_section (m := m) L (f t)
    have hmem_iff : ∀ q : ℝ × (Fin m → ℝ), ((t, q) ∈ S ↔ q ∈ Tt) := by
      intro q
      constructor
      · intro hp
        exact ⟨hp.2.1, hp.2.2⟩
      · intro hq
        exact ⟨htIcc, hq.1, hq.2⟩
    have hH_T : H t = ∫ q : ℝ × (Fin m → ℝ) in Tt, (fun q => φ t q.1 * ψ q.2) q ∂ν := by
      dsimp [H]
      have hfun_eq : (fun q : ℝ × (Fin m → ℝ) => S.indicator g (t, q))
          = Tt.indicator (fun q : ℝ × (Fin m → ℝ) => φ t q.1 * ψ q.2) := by
        ext q
        by_cases hq : q ∈ Tt
        · have hp : (t, q) ∈ S := (hmem_iff q).mpr hq
          rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
        · have hp : (t, q) ∉ S := fun hp => hq ((hmem_iff q).mp hp)
          rw [Set.indicator_apply, if_neg hp, Set.indicator_apply, if_neg hq]
      rw [hfun_eq]
      rw [MeasureTheory.integral_indicator hT_meas]
    have hfun_eq_sect : (fun q : ℝ × (Fin m → ℝ) => S.indicator g (t, q))
        = Tt.indicator (fun q : ℝ × (Fin m → ℝ) => φ t q.1 * ψ q.2) := by
      ext q
      by_cases hq : q ∈ Tt
      · have hp : (t, q) ∈ S := (hmem_iff q).mpr hq
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
      · have hp : (t, q) ∉ S := fun hp => hq ((hmem_iff q).mp hp)
        rw [Set.indicator_apply, if_neg hp, Set.indicator_apply, if_neg hq]
    have h_int_t : Integrable (Tt.indicator (fun q : ℝ × (Fin m → ℝ) => φ t q.1 * ψ q.2)) ν := by
      exact ht_int.congr (MeasureTheory.ae_of_all ν (by intro q; exact hfun_eq_sect ▸ rfl))
    have hsec := cap_on_integral_section_eq_interval (m := m) (L := L) (R := f t)
      (φt := fun z => φ t z) (ψ := ψ) hR h_int_t
    have hH_K : H t = ∫ z in (-f t)..(min (f t) (s * t + h)),
        φ t z * (∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y) := by
      rw [hH_T]
      simpa [Tt, L] using hsec
    simpa [K] using hH_K
  have h_Icc_eq : (∫ t : ℝ in Set.Icc a b, H t ∂μℝ) = ∫ t : ℝ in Set.Icc a b, K t ∂μℝ := by
    exact setIntegral_congr_ae measurableSet_Icc hH_eq_K_ae
  have h_Icc_to_Ioc : (∫ t : ℝ in Set.Icc a b, K t ∂μℝ) = ∫ t : ℝ in Set.Ioc a b, K t ∂μℝ := by
    exact setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (α := ℝ) (μ := μℝ)).symm
  have h_interval : (∫ t : ℝ in Set.Ioc a b, K t ∂μℝ) = ∫ t in a..b, K t := by
    rw [intervalIntegral.integral_of_le hab]
  have h_outer : (∫ t : ℝ, H t ∂μℝ) = ∫ t in a..b, K t := by
    rw [h_full_to_Icc, h_Icc_eq, h_Icc_to_Ioc, h_interval]
  calc
    (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S,
        φ p.1 p.2.1 * ψ p.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))))
        = ∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, g p ∂P := by
              simp [g, P, ν, μℝ, μy]
    _ = ∫ t : ℝ, H t ∂μℝ := h_main
    _ = ∫ t in a..b, K t := h_outer
    _ = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        φ t z * (∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y) := by
              rfl


/-! ## The main theorem -/

lemma body_of_revolution_cap_integrals_pi_core {d n : ℕ} [NeZero d] {a b s h : ℝ}
    {f : ℝ → ℝ} (hdn : d = 2 * n + 1) (hn : 1 ≤ n) (hab : a ≤ b)
    (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f) :
    let last : Fin d := ⟨d - 1, by omega⟩
    let K : Set (Fin d → ℝ) :=
      {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    let H : Set (Fin d → ℝ) := {x | x last ≤ s * x 0 + h}
    let W : ℝ → ℝ → ℝ := fun t z =>
      (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
    let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
    volume.real (K ∩ H) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z ∧
    (∫ x in K ∩ H, x 0) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z ∧
    (∫ x in K ∩ H, x last) =
      c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z ∧
    (∀ i : Fin d, i ≠ 0 → i ≠ last → (∫ x in K ∩ H, x i) = 0) := by
  classical
  intro last K H W c
  let lastF : Fin d := ⟨d - 1, by omega⟩
  have hlast : last = lastF := rfl
  let KP : Set (Fin d → ℝ) := {x | x 0 ∈ Set.Icc a b ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  let HP : Set (Fin d → ℝ) := {x | x lastF ≤ s * x 0 + h}
  have hK : K = KP := by dsimp [K, KP]
  have hH : H = HP := by dsimp [H, HP, lastF]
  have h2 : 2 ≤ d := by omega
  let e : (Fin d → ℝ) ≃ᵐ ℝ × (ℝ × (Fin (d - 2) → ℝ)) := coordDecomp d h2
  let P : Measure (ℝ × (ℝ × (Fin (d - 2) → ℝ))) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin (d - 2) → ℝ)))
  let S : Set (ℝ × (ℝ × (Fin (d - 2) → ℝ))) :=
    {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
      p.2.1 ^ 2 + ∑ j : Fin (d - 2), (p.2.2 j)^2 ≤ f p.1 ^ 2}
  have hpre : KP ∩ HP = e ⁻¹' S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxK, hxH⟩
      refine ⟨?_, ?_, ?_⟩
      · have hx0 : x 0 ∈ Set.Icc a b := hxK.1
        change (coordDecomp d h2 x).1 ∈ Set.Icc a b
        rw [coordDecomp_fst]
        exact hx0
      · have hxH' : x lastF ≤ s * x 0 + h := by simpa [HP] using hxH
        change (coordDecomp d h2 x).2.1 ≤ s * (coordDecomp d h2 x).1 + h
        rw [coordDecomp_fst, coordDecomp_snd_fst]
        exact hxH'
      · have hsum := hxK.2
        rw [sum_Ioi_eq_last_add_middle h2 x] at hsum
        change (coordDecomp d h2 x).2.1 ^ 2 + ∑ j : Fin (d - 2), ((coordDecomp d h2 x).2.2 j)^2 ≤ f ((coordDecomp d h2 x).1)^2
        rw [coordDecomp_fst, coordDecomp_snd_fst]
        simp [coordDecomp_snd_snd]
        exact hsum
    · intro hx
      rcases hx with ⟨hx0, hxlast, hxsum⟩
      constructor
      · constructor
        · have hx0' : x 0 ∈ Set.Icc a b := by
            change (coordDecomp d h2 x).1 ∈ Set.Icc a b at hx0
            rwa [coordDecomp_fst] at hx0
          exact hx0'
        · have hsum' : (x lastF)^2 + ∑ j : Fin (d - 2), (x (middleIndex d h2 j))^2 ≤ f (x 0)^2 := by
            change (coordDecomp d h2 x).2.1 ^ 2 + ∑ j : Fin (d - 2), ((coordDecomp d h2 x).2.2 j)^2 ≤ f ((coordDecomp d h2 x).1)^2 at hxsum
            rw [coordDecomp_fst, coordDecomp_snd_fst] at hxsum
            simpa [coordDecomp_snd_snd, lastF, lastFin] using hxsum
          rwa [sum_Ioi_eq_last_add_middle h2 x]
      · have hxlast' : x lastF ≤ s * x 0 + h := by
          change (coordDecomp d h2 x).2.1 ≤ s * (coordDecomp d h2 x).1 + h at hxlast
          rwa [coordDecomp_fst, coordDecomp_snd_fst] at hxlast
        simpa [HP] using hxlast'
  have hS_meas : MeasurableSet S := by
    exact cap_on_measurableSet_target_S (m := d - 2) (a := a) (b := b) (s := s) (h := h) (f := f) hf_meas
  let m : ℕ := d - 2
  have hm_nonempty : Nonempty (Fin m) := by
    have hm_pos : 0 < m := by omega
    exact Fin.pos_iff_nonempty.mp hm_pos
  have hball_volume : ∀ t ∈ Set.Icc a b, ∀ z,
      volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2} = c * W t z := by
    intro t ht z
    let R : ℝ := Real.sqrt (f t ^ 2 - z ^ 2)
    have hf_nonneg_t : 0 ≤ f t := hf_nonneg t ht
    by_cases hnonneg : 0 ≤ f t ^ 2 - z ^ 2
    · have hR2 : R ^ 2 = f t ^ 2 - z ^ 2 := by
        dsimp [R]
        rw [Real.sq_sqrt hnonneg]
      have hset : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2} =
          {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R ^ 2} := by
        ext y; simp [hR2]
      have hvol := volume_real_fin_ball_pow (m := m) R (Real.sqrt_nonneg _)
      have hc : volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) = c := by
        dsimp [c, m]
      have hpow_R : R ^ m = W t z := by
        dsimp [R, W]
        have hm_eq : m = 2 * n - 1 := by omega
        rw [hm_eq]
        have hcalc : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
        rw [hcalc]
        rw [pow_succ]
        rw [pow_mul]
        rw [Real.sq_sqrt hnonneg]
      rw [hset]
      rw [hvol]
      rw [hc]
      rw [hpow_R]
    · have hBempty : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2} = ∅ := by
        have hneg : f t ^ 2 - z ^ 2 < 0 := lt_of_not_ge hnonneg
        ext y
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hy
        have hy' : ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2 := by simpa using hy
        have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by positivity
        nlinarith
      have hW_zero : W t z = 0 := by
        dsimp [W]
        have hsqrt : Real.sqrt (f t ^ 2 - z ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge hnonneg))
        rw [hsqrt, mul_zero]
      rw [hBempty, MeasureTheory.measureReal_empty]
      rw [hW_zero, mul_zero]
  have h_affine_integral : ∀ A B C : ℝ,
      (∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, (A * p.1 + B * p.2.1 + C) ∂P) =
        ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
          (A * t + B * z + C) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
    intro A B C
    let φ : ℝ → ℝ → ℝ := fun t z => A * t + B * z + C
    let ψ : (Fin (d - 2) → ℝ) → ℝ := fun _ => 1
    by_cases h_int : Integrable (S.indicator (fun p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) => A * p.1 + B * p.2.1 + C)) P
    · have hsec := integral_fin_ball_section_on (m := d - 2) (a := a) (b := b) (s := s) (h := h)
        (f := f) (φ := φ) (ψ := ψ) hab hf_nonneg hf_meas (by fun_prop) (by fun_prop)
        (by simpa [S, φ, ψ] using h_int)
      have hinner : ∀ t z, (∫ y : Fin (d - 2) → ℝ in {y | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y) =
          volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
        intro t z
        simp [ψ, setIntegral_const]
      calc
        (∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, (A * p.1 + B * p.2.1 + C) ∂P)
            = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
                φ t z * (∫ y : Fin (d - 2) → ℝ in {y | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2}, ψ y) := by
                  simpa [S, P, φ, ψ, Set.mem_Icc] using hsec
        _ = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
                (A * t + B * z + C) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
                  apply intervalIntegral.integral_congr
                  intro t ht
                  apply intervalIntegral.integral_congr
                  intro z hz
                  simp [φ, hinner t z]
    · have hnot := integral_fin_ball_section_affine_not_integrable (m := d - 2) (a := a) (b := b)
        (s := s) (h := h) (f := f) (A := A) (B := B) (C := C) hab hf_nonneg hf_meas
        (by simpa [S] using h_int)
      rw [hnot.1, hnot.2]
  have hvol_transfer : volume.real (K ∩ H) = P.real S := by
    rw [hK, hH, hpre]
    exact Commons.Geometry.Ulam.MeasurePreserving.measureReal_preimage_emb (coordDecomp_measurePreserving d h2) S
  have hvol_set : P.real S = ∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, (1 : ℝ) ∂P := by
    simp [setIntegral_const]
  have hvol_rhs : (∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, (1 : ℝ) ∂P) =
      ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        (1 : ℝ) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
    simpa using h_affine_integral 0 0 1
  have hvol_rhs' : (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
        (1 : ℝ) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
      = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z := by
    have hintegrand : ∀ t ∈ Set.Icc a b, ∀ z,
        (1 : ℝ) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} = c * W t z := by
      intro t ht z
      rw [hball_volume t ht z]
      ring
    calc
      (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
          (1 : ℝ) * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
          = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), c * W t z := by
              apply intervalIntegral.integral_congr
              intro t ht
              apply intervalIntegral.integral_congr
              intro z hz
              have ht' : t ∈ Set.Icc a b := by
                simpa [Set.uIcc_of_le hab] using ht
              exact hintegrand t ht' z
      _ = ∫ t in a..b, c * ∫ z in (-f t)..(min (f t) (s * t + h)), W t z := by
              apply intervalIntegral.integral_congr
              intro t ht
              change (∫ z in (-f t)..(min (f t) (s * t + h)), c * W t z) =
                c * ∫ z in (-f t)..(min (f t) (s * t + h)), W t z
              rw [intervalIntegral.integral_const_mul]
      _ = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), W t z := by
              rw [intervalIntegral.integral_const_mul]
  constructor
  · rw [hvol_transfer, hvol_set, hvol_rhs, hvol_rhs']
  · constructor
    · have hx0_transfer : (∫ x : Fin d → ℝ in K ∩ H, x 0) =
          ∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, p.1 ∂P := by
        rw [hK, hH, hpre]
        have h := Commons.Geometry.Ulam.MeasurePreserving.setIntegral_comp' (coordDecomp_measurePreserving d h2) (fun p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) => p.1) S hS_meas
        simpa [e, coordDecomp_fst] using h
      have hx0_rhs : (∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, p.1 ∂P) =
          ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
            t * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
        simpa using h_affine_integral 1 0 0
      have hx0_rhs' : (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
            t * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
          = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z := by
        have hintegrand : ∀ t ∈ Set.Icc a b, ∀ z,
            t * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} = c * (t * W t z) := by
          intro t ht z
          rw [hball_volume t ht z]
          ring
        calc
          (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
              t * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
              = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), c * (t * W t z) := by
                  apply intervalIntegral.integral_congr
                  intro t ht
                  apply intervalIntegral.integral_congr
                  intro z hz
                  have ht' : t ∈ Set.Icc a b := by
                    simpa [Set.uIcc_of_le hab] using ht
                  exact hintegrand t ht' z
          _ = ∫ t in a..b, c * ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z := by
                  apply intervalIntegral.integral_congr
                  intro t ht
                  change (∫ z in (-f t)..(min (f t) (s * t + h)), c * (t * W t z)) =
                    c * ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z
                  rw [intervalIntegral.integral_const_mul]
          _ = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), t * W t z := by
                  rw [intervalIntegral.integral_const_mul]
      rw [hx0_transfer, hx0_rhs, hx0_rhs']
    · constructor
      · have hlast_transfer : (∫ x : Fin d → ℝ in K ∩ H, x lastF) =
            ∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, p.2.1 ∂P := by
          rw [hK, hH, hpre]
          have h := Commons.Geometry.Ulam.MeasurePreserving.setIntegral_comp' (coordDecomp_measurePreserving d h2) (fun p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) => p.2.1) S hS_meas
          simpa [e, coordDecomp_snd_fst, lastF, lastFin] using h
        have hlast_rhs : (∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, p.2.1 ∂P) =
            ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
              z * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} := by
          simpa using h_affine_integral 0 1 0
        have hlast_rhs' : (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
              z * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
            = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z := by
          have hintegrand : ∀ t ∈ Set.Icc a b, ∀ z,
              z * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2} = c * (z * W t z) := by
            intro t ht z
            rw [hball_volume t ht z]
            ring
          calc
            (∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)),
                z * volume.real {y : Fin (d - 2) → ℝ | ∑ j : Fin (d - 2), (y j)^2 ≤ f t ^ 2 - z ^ 2})
                = ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), c * (z * W t z) := by
                    apply intervalIntegral.integral_congr
                    intro t ht
                    apply intervalIntegral.integral_congr
                    intro z hz
                    have ht' : t ∈ Set.Icc a b := by
                      simpa [Set.uIcc_of_le hab] using ht
                    exact hintegrand t ht' z
            _ = ∫ t in a..b, c * ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z := by
                    apply intervalIntegral.integral_congr
                    intro t ht
                    change (∫ z in (-f t)..(min (f t) (s * t + h)), c * (z * W t z)) =
                      c * ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z
                    rw [intervalIntegral.integral_const_mul]
            _ = c * ∫ t in a..b, ∫ z in (-f t)..(min (f t) (s * t + h)), z * W t z := by
                    rw [intervalIntegral.integral_const_mul]
        rw [hlast]
        rw [hlast_transfer, hlast_rhs, hlast_rhs']
      · intro i hi0 hilast
        let j : Fin (d - 2) := ⟨i.val - 1, by
          have hi_lt : i.val < d := i.isLt
          have hi_pos : 1 ≤ i.val := Nat.succ_le_iff.mpr (Fin.pos_iff_ne_zero.mpr hi0)
          have hilast_val : i.val ≠ d - 1 := by
            intro hval
            apply hilast
            apply Fin.ext
            rw [hlast]
            simpa [lastF] using hval
          omega⟩
        have hi_pos : 1 ≤ i.val := Nat.succ_le_iff.mpr (Fin.pos_iff_ne_zero.mpr hi0)
        have hij : i = middleIndex d h2 j := by
          apply Fin.ext
          change i.val = j.val + 1
          simp [j]
          omega
        have hmid_transfer : (∫ x : Fin d → ℝ in K ∩ H, x i) =
            ∫ p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) in S, p.2.2 j ∂P := by
          rw [hK, hH, hpre]
          have h := Commons.Geometry.Ulam.MeasurePreserving.setIntegral_comp' (coordDecomp_measurePreserving d h2) (fun p : ℝ × (ℝ × (Fin (d - 2) → ℝ)) => p.2.2 j) S hS_meas
          simpa [e, coordDecomp_snd_snd, hij] using h
        have hzero := integral_fin_ball_section_coord_zero (m := d - 2) (a := a) (b := b) (s := s) (h := h) (f := f) hab hf_nonneg hf_meas j
        rw [hmid_transfer]
        simpa [S] using hzero

end

end Commons.Geometry.Ulam
