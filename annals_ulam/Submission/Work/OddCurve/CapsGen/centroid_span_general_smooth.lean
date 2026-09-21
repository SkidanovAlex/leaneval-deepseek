import Mathlib
import Submission.Work.OddCurve.CapsGen.Defs
import Submission.Work.Geometry.Ulam.odd_profile_cap_centroid_span_helpers
import Submission.Work.Geometry.Ulam.norm_odd_cap_zW_slice_integral_le_general
import Submission.Work.Geometry.Ulam.norm_odd_cap_tW_slice_integral_le_general
import Submission.Work.Geometry.Ulam.odd_profile_cap_volume_half_general
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals
import Submission.Work.Geometry.Ulam.profile_measurable_smooth_general_inf
import Submission.Work.OddCurve.CapsGen.moment_eq_gen_smooth

/-!
# The odd cap centroid-span identity on a general interval, smooth regularity

Same statement as `Work.OddCurve.CapsGen.centroid_span_general_smooth` (i.e. the smooth analogue
of `Commons.Geometry.Ulam.odd_profile_cap_centroid_span_general`), proved by re-running the
general-interval proof with the analytic regularity hypothesis `ContDiffOn ℝ (⊤ : WithTop ℕ∞)`
replaced by the smooth one `ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`.  The analytic ingredients are
replaced by the smooth copies proved in this directory (`moment_eq_gen_smooth` and its two
dependencies, `profile_measurable_smooth_general_inf`); the analytic regularity of `f` was used
in that proof only to obtain `Measurable f`, so nothing else changes.
-/

namespace Work.OddCurve.CapsGen

open Commons.Geometry.Ulam
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem centroid_span_general_smooth {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n + 1) (hn : 1 ≤ n)
    {A B C : ℝ} (hAB : A < B) {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc A B)
    (hf_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo A B))
    (hf_conc : ConcaveOn ℝ (Set.Icc A B) f)
    (hf_left : f A = 0) (hf_right : f B = 0)
    (hf_pos : ∀ t ∈ Set.Ioo A B, 0 < f t)
    (hh_cont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hxy_inside : ∀ s : ℝ, 0 < s → -x s ∈ Set.Ioo A B ∧ y s ∈ Set.Ioo A B)
    (h_moment : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        C / Real.sqrt (1 + s ^ 2))
    (h_center : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) *
          (t + deriv h s)) = 0)
    (hvol : ∀ s : ℝ, 0 < s →
      MeasureTheory.volume.real ({z : EuclideanSpace ℝ (Fin d) |
          z 0 ∈ Set.Icc A B ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (z i) ^ 2 ≤ f (z 0) ^ 2} ∩
        {z : EuclideanSpace ℝ (Fin d) | z ⟨d - 1, by omega⟩ ≤ s * z 0 + h s}) =
      MeasureTheory.volume.real {z : EuclideanSpace ℝ (Fin d) |
          z 0 ∈ Set.Icc A B ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (z i) ^ 2 ≤ f (z 0) ^ 2} / 2) :
    Work.OddCurve.CapsGen.CentroidSpanGeneral' d A B f h  := by
  unfold Work.OddCurve.CapsGen.CentroidSpanGeneral'
  classical
  intro K s hs
  let last : Fin d := lastFin d
  let e0 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (1:ℝ)
  let elast : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (lastFin d) (1:ℝ)
  let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x (lastFin d) ≤ s * x 0 + h s}
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h s))
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hdpos : 2 ≤ d := by omega
  have hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t :=
    profile_nonneg_Icc_general (a := A) (b := B) hAB.le hf_conc hf_left hf_right
  have hf_meas : Measurable f :=
    profile_measurable_smooth_general_inf (a := A) (b := B) hAB.le hf_support hf_cont hf_left hf_right
  have hlast0_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  have hcap_body := body_of_revolution_cap_integrals (d := d) (n := n) (a := A) (b := B)
    (s := s) (h := h s) hdn hn hAB.le hf_nonneg hf_meas
  rcases hcap_body with ⟨hVcap, hI0cap, hIlastcap, hmidcap⟩
  have hW_zero_of_le_neg : ∀ t, ∀ z : ℝ, z ≤ -f t → W t z = 0 := by
    intro t z hz
    dsimp [W]
    apply odd_weight_eq_zero_of_not_active (n := n) (f := f t) (L := z)
    · by_cases ht : t ∈ Set.Icc A B
      · exact hf_nonneg t ht
      · have hf0 : f t = 0 := by
          rw [Function.support_subset_iff'] at hf_support
          exact hf_support t ht
        rw [hf0]
    · intro hact
      linarith
  have hI0cap' : (∫ x in K ∩ H, x 0) = c * ∫ t in A..B, ∫ z in (-f t)..(U t), t * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hbody0 := hI0cap
    -- hI0cap has min; convert to max pointwise
    have houter : (∫ t in A..B, ∫ z in (-f t)..(min (f t) (s * t + h s)), t * W t z) =
        ∫ t in A..B, ∫ z in (-f t)..(U t), t * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply odd_inner_integral_min_eq_max
      intro z hz
      have hz_le : z ≤ -f t := hz.2
      rw [hW_zero_of_le_neg t z hz_le]
      simp
    have hbody0' : (∫ x in K ∩ H, x 0) =
        c * ∫ t in A..B, t * ∫ z in (-f t)..(min (f t) (s * t + h s)), W t z := by
      simpa [K, H, hlast0_eq] using hbody0
    have hbody0'' : (∫ x in K ∩ H, x 0) =
        c * ∫ t in A..B, ∫ z in (-f t)..(min (f t) (s * t + h s)), t * W t z := by
      rw [hbody0']
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      exact (intervalIntegral.integral_const_mul t (fun z => W t z)).symm
    simpa [K, W, U, c, hlast0_eq] using hbody0''.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlastcap' : (∫ x in K ∩ H, x (lastFin d)) = c * ∫ t in A..B, ∫ z in (-f t)..(U t), z * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hbody := hIlastcap
    have houter : (∫ t in A..B, ∫ z in (-f t)..(min (f t) (s * t + h s)), z * W t z) =
        ∫ t in A..B, ∫ z in (-f t)..(U t), z * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply odd_inner_integral_min_eq_max
      intro z hz
      have hz_le : z ≤ -f t := hz.2
      rw [hW_zero_of_le_neg t z hz_le]
      simp
    simpa [K, W, U, c, hlast0_eq] using hbody.trans (congrArg (fun q : ℝ => c * q) houter)
  have hmidcap' : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K ∩ H, x i) = 0 := by
    intro i hi0 hilast
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    have hilast0 : i ≠ (⟨d - 1, by omega⟩ : Fin d) := by
      intro h
      apply hilast
      simpa [hlast0_eq] using h
    simpa [K, W, U, c] using hmidcap i hi0 hilast0

  -- total body integrals with a large halfspace containing K
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc A B) :=
    concaveOn_Icc_bounded hAB.le hf_conc
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc A B, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc A B, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hf_le_R : ∀ t ∈ Set.Icc A B, f t ≤ R := by
    intro t ht
    exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt)
  have hK_subset_R : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} := by
    simpa [K] using K_subset_H_large_general (d := d) (a := A) (b := B) (f := f) (M := M) (R := R)
      hAB.le hdpos hR_gt hf_nonneg hf_le_M
  have hK_inter_R : K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} = K := by
    exact Set.inter_eq_left.mpr hK_subset_R
  have htotal_body := body_of_revolution_cap_integrals (d := d) (n := n) (a := A) (b := B)
    (s := 0) (h := R) hdn hn hAB.le hf_nonneg hf_meas
  rcases htotal_body with ⟨hVtot0, hI0tot0, hIlasttot0, hmidtot0⟩
  have hI0tot0' : (∫ x in K, x 0) = c * ∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z := by
    rw [← hK_inter_R]
    have houter : (∫ t in A..B, ∫ z in (-f t)..(min (f t) (0 * t + R)), t * W t z) =
        ∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), t * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc A B := by
        simpa [Set.uIcc_of_le hAB.le] using ht
      have hmin : min (f t) (0 * t + R) = f t := by
        simp [min_eq_left (hf_le_R t htIcc)]
      have hmax : max (-f t) (min (f t) (0 * t + R)) = f t := by
        rw [hmin]
        exact max_eq_right (by linarith [hf_nonneg t htIcc])
      change (∫ z in (-f t)..(min (f t) (0 * t + R)), t * W t z) =
        ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), t * W t z
      rw [hmax, hmin]
    simpa [K, W, c] using hI0tot0.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlasttot0' : (∫ x in K, x (⟨d - 1, by omega⟩ : Fin d)) = c * ∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z := by
    rw [← hK_inter_R]
    have houter : (∫ t in A..B, ∫ z in (-f t)..(min (f t) (0 * t + R)), z * W t z) =
        ∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), z * W t z := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc A B := by
        simpa [Set.uIcc_of_le hAB.le] using ht
      have hmin : min (f t) (0 * t + R) = f t := by
        simp [min_eq_left (hf_le_R t htIcc)]
      have hmax : max (-f t) (min (f t) (0 * t + R)) = f t := by
        rw [hmin]
        exact max_eq_right (by linarith [hf_nonneg t htIcc])
      change (∫ z in (-f t)..(min (f t) (0 * t + R)), z * W t z) =
        ∫ z in (-f t)..(max (-f t) (min (f t) (0 * t + R))), z * W t z
      rw [hmax, hmin]
    simpa [K, W, c] using hIlasttot0.trans (congrArg (fun q : ℝ => c * q) houter)
  have hIlasttot : (∫ x in K, x (lastFin d)) = 0 := by
    have h := hIlasttot0'
    have hinner : ∀ t ∈ Set.Icc A B,
        (∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      intro t ht
      have hmax : max (-f t) (min (f t) R) = f t := by
        exact max_min_eq_of_nonneg_le (hf_nonneg t ht) (hf_le_R t ht)
      rw [hmax]
      have hodd : (∫ z in (-f t)..(f t), z * W t z) = 0 := by
        let g : ℝ → ℝ := fun z => z * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))
        have hcomp := intervalIntegral.integral_comp_neg (a := -f t) (b := f t) (f := g)
        have hneg : (∫ z in (-f t)..(f t), g (-z)) = - ∫ z in (-f t)..(f t), g z := by
          have hfun : (fun z => g (-z)) = (fun z => - g z) := by
            ext z
            dsimp [g]
            ring_nf
          rw [hfun, intervalIntegral.integral_neg]
        have hsame : (∫ z in (-f t)..(f t), g (-z)) = ∫ z in (-f t)..(f t), g z := by
          simpa [g] using hcomp
        linarith
      simpa [W] using hodd
    have hI0tot_full : (∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      calc
        (∫ t in A..B, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z)
            = ∫ t in A..B, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              have htIcc : t ∈ Set.Icc A B := by
                simpa [Set.uIcc_of_le hAB.le] using ht
              change (∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = (0 : ℝ)
              rw [hinner t htIcc]
        _ = 0 := by simp
    rw [← hlast0_eq]
    rw [hIlasttot0']
    rw [hI0tot_full]
    simp
  have hmidtot : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → (∫ x in K, x i) = 0 := by
    intro i hi0 hilast
    have hilast0 : i ≠ (⟨d - 1, by omega⟩ : Fin d) := by
      intro h
      apply hilast
      simpa [hlast0_eq] using h
    rw [← hK_inter_R]
    simpa [K, W, c] using hmidtot0 i hi0 hilast0

  -- moment relation from the odd centroid moment lemma
  have hmoment : (∫ t in A..B, ∫ z in (-f t)..(U t), (t + s * z) * W t z) =
      (1 / 2 : ℝ) * ∫ t in A..B, ∫ z in (-f t)..(f t), t * W t z := by
    simpa [W, U] using
      (odd_profile_cap_centroid_moment_eq_general_smooth (n := n) hn (C := C) (A := A) (B := B) hAB hf_support hf_cont hf_conc hf_left hf_right hf_pos
        hh_cont h0 hxy hxy_inside h_moment h_center s hs)

  have hI0tot_full : (∫ x in K, x 0) = c * ∫ t in A..B, ∫ z in (-f t)..(f t), t * W t z := by
    rw [hI0tot0']
    apply congrArg (fun q : ℝ => c * q)
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc A B := by
      simpa [Set.uIcc_of_le hAB.le] using ht
    have hmax : max (-f t) (min (f t) R) = f t := by
      exact max_min_eq_of_nonneg_le (hf_nonneg t htIcc) (hf_le_R t htIcc)
    change (∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z) =
      ∫ z in (-f t)..(f t), t * W t z
    rw [hmax]

  have hA_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume A B := by
    rw [intervalIntegrable_iff]
    have hL_meas : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => t * W t z)) := by
      dsimp [W]
      fun_prop
    have hA_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
    let T : ℝ := max |A| |B|
    have hT : ∀ t ∈ Set.Icc A B, |t| ≤ T := by
      intro t ht
      exact abs_le_max_abs_of_mem_Icc ht
    let Bint : ℝ := T * (2 * M) * Wbase
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint, Wbase]; positivity
    have hbnd' := norm_odd_cap_tW_slice_integral_le_general (n := n) (f := f) (h := h) (M := M) (A := A) (B := B) (T := T) hAB hT
      hf_le_M hf_nonneg (le_of_lt hMpos) s
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc A B)),
        ‖∫ z in (-f t)..(U t), t * W t z‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have hbound_t := ht htIoc
      simpa [U, Bint, Wbase] using hbound_t
    have hvol_fin : volume (Set.uIoc A B) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), t * W t z) (Set.uIoc A B) volume := by
      exact IntegrableOn.of_bound hvol_fin hA_ae.restrict Bint h_bound
    exact hIntOn
  have hB_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume A B := by
    rw [intervalIntegrable_iff]
    have hL_meas : Measurable (fun t : ℝ => -f t) := by fun_prop
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => z * W t z)) := by
      dsimp [W]
      fun_prop
    have hB_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    let Wbase : ℝ := (M ^ 2) ^ (n - 1) * M
    let Bint : ℝ := M * (2 * M) * Wbase
    have hBint_nonneg : 0 ≤ Bint := by dsimp [Bint, Wbase]; positivity
    have hbnd' := norm_odd_cap_zW_slice_integral_le_general (n := n) (f := f) (h := h) (M := M) (A := A) (B := B) hAB
      hf_le_M hf_nonneg (le_of_lt hMpos) s
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc A B)),
        ‖∫ z in (-f t)..(U t), z * W t z‖ ≤ Bint := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hbnd'] with t ht
      intro htIoc
      have htIoc' : t ∈ Set.Ioc A B := by
        simpa [Set.uIoc_of_le hAB.le] using htIoc
      have htcc : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self htIoc'
      have hbound_t := ht htIoc
      simpa [U, Bint, Wbase] using hbound_t
    have hvol_fin : volume (Set.uIoc A B) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), z * W t z) (Set.uIoc A B) volume := by
      exact IntegrableOn.of_bound hvol_fin hB_ae.restrict Bint h_bound
    exact hIntOn
  have hinner_add : ∀ t : ℝ,
      (∫ z in (-f t)..(U t), t * W t z) + s * (∫ z in (-f t)..(U t), z * W t z) =
        ∫ z in (-f t)..(U t), (t + s * z) * W t z := by
    intro t
    have hc1 : IntervalIntegrable (fun z => t * W t z) volume (-f t) (U t) := by
      have hcont : Continuous (fun z => t * W t z) := by
        dsimp [W]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun z => z * W t z) volume (-f t) (U t) := by
      have hcont : Continuous (fun z => z * W t z) := by
        dsimp [W]
        fun_prop
      exact hcont.intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul]
    have hc2s : IntervalIntegrable (fun z => s * (z * W t z)) volume (-f t) (U t) :=
      hc2.const_mul s
    rw [← intervalIntegral.integral_add hc1 hc2s]
    apply intervalIntegral.integral_congr
    intro z hz
    ring
  have houter_add : (∫ t in A..B, ∫ z in (-f t)..(U t), t * W t z) +
        s * (∫ t in A..B, ∫ z in (-f t)..(U t), z * W t z) =
      ∫ t in A..B, (∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    rw [← intervalIntegral.integral_const_mul]
    have hB_smul : IntervalIntegrable (fun t => s * (∫ z in (-f t)..(U t), z * W t z)) volume A B :=
      hB_int.const_mul s
    rw [← intervalIntegral.integral_add hA_int hB_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hinner_add t
  have hcap_moment : (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d)) =
      c * (∫ t in A..B, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    calc
      (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))
          = c * (∫ t in A..B, ∫ z in (-f t)..(U t), t * W t z) +
              s * (c * (∫ t in A..B, ∫ z in (-f t)..(U t), z * W t z)) := by
            rw [hI0cap', hIlastcap']
      _ = c * ((∫ t in A..B, ∫ z in (-f t)..(U t), t * W t z) +
              s * (∫ t in A..B, ∫ z in (-f t)..(U t), z * W t z)) := by ring
      _ = c * (∫ t in A..B, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
            rw [houter_add]
  have hrelation : (∫ x in K, x 0) = 2 * ((∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))) := by
    rw [hI0tot_full, hcap_moment, hmoment]
    ring
  have hvolK : volume.real K = volume.real K := rfl
  have hvolcap : volume.real (K ∩ H) = volume.real K / 2 := by
    simpa [K, H, hlast0_eq] using hvol s hs
  let D : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in (K ∩ H), x)
  have hDav : D = (volume.real K)⁻¹ • (∫ x in K, x) - (volume.real (K ∩ H))⁻¹ • (∫ x in K ∩ H, x) := by
    dsimp [D]
    rw [setAverage_eq, setAverage_eq]
  have hD_scale : D = (volume.real K)⁻¹ • ((∫ x in K, x) - 2 • (∫ x in K ∩ H, x)) := by
    rw [hDav, hvolcap]
    module
  have hf_cont_inf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo A B) := hf_cont
  have hK_meas : MeasurableSet K := by
    simpa [K] using body_of_revolution_measurable (d := d) (R₁ := -A) (R₂ := B) (f := f)
      (support_subset_Icc_neg_neg hf_support) (by simpa [neg_neg] using hf_cont_inf) (eq_zero_neg_neg hf_left) hf_right
  have hK_bdd : Bornology.IsBounded K := by
    simpa [K] using body_of_revolution_bounded (d := d) (R₁ := -A) (R₂ := B) (f := f)
      (concaveOn_Icc_neg_neg hf_conc) (eq_zero_neg_neg hf_left) hf_right
  have hH_meas : MeasurableSet H := by
    dsimp [H]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hC_meas : MeasurableSet (K ∩ H) := hK_meas.inter hH_meas
  have hC_bdd : Bornology.IsBounded (K ∩ H) := hK_bdd.subset (by intro x hx; exact hx.1)
  have hAvg0K : ((⨍ x in K, x) 0) = (volume.real K)⁻¹ * (∫ x in K, x 0) := by
    rw [setAverage_id_apply K 0 hK_meas hK_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvg0C : ((⨍ x in K ∩ H, x) 0) = (volume.real (K ∩ H))⁻¹ * (∫ x in K ∩ H, x 0) := by
    rw [setAverage_id_apply (K ∩ H) 0 hC_meas hC_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvgLastK : ((⨍ x in K, x) (lastFin d)) = (volume.real K)⁻¹ * (∫ x in K, x (lastFin d)) := by
    rw [setAverage_id_apply K (lastFin d) hK_meas hK_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  have hAvgLastC : ((⨍ x in K ∩ H, x) (lastFin d)) = (volume.real (K ∩ H))⁻¹ * (∫ x in K ∩ H, x (lastFin d)) := by
    rw [setAverage_id_apply (K ∩ H) (lastFin d) hC_meas hC_bdd]
    rw [setAverage_eq]
    simp [smul_eq_mul]
  let lam : ℝ := -2 * (volume.real K)⁻¹ * (∫ x in K ∩ H, x (lastFin d))
  have hDlast : D (lastFin d) = lam := by
    dsimp [D, lam]
    rw [hAvgLastK, hAvgLastC]
    rw [hIlasttot]
    rw [hvolcap]
    field_simp
    ring
  have hD0 : D 0 = -s * lam := by
    dsimp [D, lam]
    rw [hAvg0K, hAvg0C]
    rw [hvolcap]
    rw [hrelation]
    field_simp
    ring
  have hDmid : ∀ i : Fin d, i ≠ 0 → i ≠ lastFin d → D i = 0 := by
    intro i hi0 hilast
    dsimp [D]
    rw [setAverage_id_apply K i hK_meas hK_bdd]
    rw [setAverage_id_apply (K ∩ H) i hC_meas hC_bdd]
    rw [setAverage_eq, setAverage_eq]
    simp [smul_eq_mul]
    rw [hmidtot i hi0 hilast, hmidcap' i hi0 hilast]
    rw [hvolcap]
    field_simp
    ring
  have hmem := mem_span_e0_elast hdpos s lam hD0 hDlast hDmid
  -- match target's index and vector
  have hlast_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  have hmem' : D ∈ ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) +
        (EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1:ℝ))) := by
    simpa [hlast_eq, last] using hmem
  simpa [D, H, hlast_eq, last] using hmem'

end Work.OddCurve.CapsGen
