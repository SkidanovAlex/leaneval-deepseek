import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.even_profile_cap_volume_half
import Submission.Commons.Geometry.Ulam.odd_floating_of_family
import Submission.Commons.Geometry.Ulam.even_profile_cap_centroid_moment_eq_smooth

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace BigOperators Interval

set_option autoImplicit false
set_option maxHeartbeats 1000000

private lemma mem_span_e0_elast {d : ℕ} [NeZero d] (hd : 2 ≤ d) (s lam : ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (h0 : v 0 = -s * lam) (hlast : v (lastFin d) = lam)
    (hmiddle : ∀ i, i ≠ 0 → i ≠ lastFin d → v i = 0) :
    v ∈ ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
  have hlast_ne : lastFin d ≠ 0 := by
    dsimp [lastFin]
    exact Fin.ne_of_val_ne (by simp; omega)
  rw [Submodule.mem_span_singleton]
  refine ⟨lam, ?_⟩
  ext i
  change (lam • ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) + (EuclideanSpace.single (lastFin d) (1:ℝ)))).ofLp i = v.ofLp i
  by_cases hi0 : i = 0
  · subst i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, h0]
    rw [if_neg (Ne.symm hlast_ne)]
    simp
    ring
  · by_cases hilast : i = lastFin d
    · subst i
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, hlast]
      rw [if_neg hi0]
      simp
    · have hv := hmiddle i hi0 hilast
      rw [hv]
      simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply]
      rw [if_neg hi0, if_neg hilast]
      simp


lemma integral_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    (∫ x in K, x) i = ∫ x in K, x i := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (volume.restrict K) :=
    (integrableOn_id_bounded_measurable (d := d) hK_meas hK_bdd).integrable
  have h := ContinuousLinearMap.integral_comp_comm L hInt
  simpa [L, PiLp.proj_apply] using h.symm

lemma setAverage_id_apply {d : ℕ} [NeZero d] (K : Set (EuclideanSpace ℝ (Fin d))) (i : Fin d)
    (hK_meas : MeasurableSet K) (hK_bdd : Bornology.IsBounded K) :
    ((⨍ x in K, x) i) = ⨍ x in K, (x i) := by
  rw [setAverage_eq, setAverage_eq]
  rw [PiLp.smul_apply]
  rw [integral_id_apply K i hK_meas hK_bdd]

lemma even_profile_cap_centroid_span {d : ℕ} [NeZero d] (n : ℕ) (hdn : d = 2 * n) (hn : 2 ≤ n)
    {h x y f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo (-1) 1))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-1) 1) f)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hh_cont : ContDiffOn ℝ ∞ h Set.univ)
    (h0 : h 0 = 0)
    (hxy : ∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s ∧
      (f (y s)) ^ 2 = (s * y s + h s) ^ 2 ∧
      (f (-x s)) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hI : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hJ : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0)
    (hvol : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}) = volume.real K / 2) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ s : ℝ, 0 < s →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x (lastFin d) ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ ((-s) • (EuclideanSpace.single (0 : Fin d) (1:ℝ)) +
          (EuclideanSpace.single (lastFin d) (1:ℝ))) := by
  classical
  intro K s hs
  let last : Fin d := lastFin d
  let e0 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (1:ℝ)
  let elast : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (lastFin d) (1:ℝ)
  let H : Set (EuclideanSpace ℝ (Fin d)) := {x | x (lastFin d) ≤ s * x 0 + h s}
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1)
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h s))
  let c : ℝ := volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d - 2))) 1)
  have hdpos : 2 ≤ d := by omega
  have hf_nonneg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ f t := by
    intro t ht
    exact even_profile_nonneg_Icc hf_conc hf_left hf_right t ht
  have hf_meas : Measurable f := by
    exact even_profile_measurable_smooth hf_support hf_cont hf_left hf_right
  have hlast0_eq : (⟨d - 1, by omega⟩ : Fin d) = lastFin d := by
    ext; simp [lastFin]
  have hcap_body := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (s := s) (h := h s) hdn hn (by norm_num) hf_nonneg hf_meas
  rcases hcap_body with ⟨hVcap, hI0cap, hIlastcap, hmidcap⟩
  have hI0cap' : (∫ x in K ∩ H, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    simpa [K, W, U, c] using hI0cap
  have hIlastcap' : (∫ x in K ∩ H, x (lastFin d)) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z := by
    have hset : K ∩ H = K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ s * x 0 + h s} := by
      ext x
      simp only [K, H, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [hlast0_eq]
    rw [hset]
    simpa [K, W, U, c, hlast0_eq] using hIlastcap
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
  have hf_bdd : Bornology.IsBounded (f '' Set.Icc (-1 : ℝ) 1) := by
    exact even_profile_bounded hf_conc hf_left hf_right
  rcases hf_bdd.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  have hf_abs_le : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ M := by
    intro t ht
    exact hM (f t) ⟨t, ht, rfl⟩
  have hf_le_M : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ M := by
    intro t ht
    have hnonneg : 0 ≤ f t := hf_nonneg t ht
    simpa [abs_of_nonneg hnonneg] using hf_abs_le t ht
  let R : ℝ := M + 1
  have hR_gt : M < R := by dsimp [R]; linarith
  have hf_le_R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ R := by
    intro t ht
    exact le_of_lt (lt_of_le_of_lt (hf_le_M t ht) hR_gt)
  have hK_subset_R : K ⊆ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} := by
    simpa [K] using K_subset_H_large (d := d) (f := f) (M := M) (R := R) hdpos hR_gt hf_nonneg hf_le_M
  have hK_inter_R : K ∩ {x : EuclideanSpace ℝ (Fin d) | x (⟨d - 1, by omega⟩ : Fin d) ≤ R} = K := by
    exact Set.inter_eq_left.mpr hK_subset_R
  have htotal_body := body_of_revolution_cap_integrals_even (d := d) (n := n) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (s := 0) (h := R) hdn hn (by norm_num) hf_nonneg hf_meas
  rcases htotal_body with ⟨hVtot0, hI0tot0, hIlasttot0, hmidtot0⟩
  have hI0tot0' : (∫ x in K, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z := by
    rw [← hK_inter_R]
    simpa [K, W, c] using hI0tot0
  have hIlasttot0' : (∫ x in K, x (⟨d - 1, by omega⟩ : Fin d)) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z := by
    rw [← hK_inter_R]
    simpa [K, W, c] using hIlasttot0
  have hIlasttot : (∫ x in K, x (lastFin d)) = 0 := by
    have h := hIlasttot0'
    -- rewrite inner upper to f, then z integral odd
    have hinner : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      intro t ht
      have hmax : max (-f t) (min (f t) R) = f t := by
        exact max_min_eq_of_nonneg_le (hf_nonneg t ht) (hf_le_R t ht)
      rw [hmax]
      have hodd : (∫ z in (-f t)..(f t), z * W t z) = 0 := by
        let g : ℝ → ℝ := fun z => z * (f t ^ 2 - z ^ 2) ^ (n - 1)
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
    have hI0tot_full : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z) = 0 := by
      calc
        (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(max (-f t) (min (f t) R)), z * W t z)
            = ∫ t in (-1 : ℝ)..1, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
                simpa [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using ht
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

  -- moment relation from the requested lemma
  have hmoment : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
    simpa [W, U] using
      (even_profile_cap_centroid_moment_eq_smooth hn hf_support hf_cont hf_conc hf_left hf_right hf_pos
        hh_cont h0 hxy hI hJ s hs)

  have hI0tot_full : (∫ x in K, x 0) = c * ∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(f t), t * W t z := by
    rw [hI0tot0']
    apply congrArg (fun q : ℝ => c * q)
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using ht
    have hmax : max (-f t) (min (f t) R) = f t := by
      exact max_min_eq_of_nonneg_le (hf_nonneg t htIcc) (hf_le_R t htIcc)
    change (∫ z in (-f t)..(max (-f t) (min (f t) R)), t * W t z) =
      ∫ z in (-f t)..(f t), t * W t z
    rw [hmax]
  have hU_bounds : ∀ t ∈ Set.Icc (-1 : ℝ) 1, -f t ≤ U t ∧ U t ≤ f t := by
    intro t ht
    constructor
    · dsimp [U]
      exact le_max_left _ _
    · dsimp [U]
      refine max_le ?_ (min_le_left _ _)
      linarith [hf_nonneg t ht]
  have hlen_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |U t - (-f t)| ≤ 2 * M := by
    intro t ht
    rcases hU_bounds t ht with ⟨hUge, hUle⟩
    have hnonneg : 0 ≤ U t - (-f t) := by linarith
    rw [abs_of_nonneg hnonneg]
    have hsub : U t - (-f t) ≤ f t - (-f t) := by linarith
    have : f t - (-f t) = 2 * f t := by ring
    rw [this] at hsub
    exact le_trans hsub (mul_le_mul_of_nonneg_left (hf_le_M t ht) (by norm_num))
  have hA_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume (-1 : ℝ) 1 := by
    have hL_meas : Measurable (fun t : ℝ => -f t) := hf_meas.neg
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => t * W t z)) := by
      dsimp [W]
      fun_prop
    have hA_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), t * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)),
        ‖∫ z in (-f t)..(U t), t * W t z‖ ≤ (M ^ 2) ^ (n - 1) * (2 * M) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [] with t ht
      have hle : (-1 : ℝ) ≤ 1 := by norm_num
      have htIoc : t ∈ Set.Ioc (-1) 1 := by
        simpa [Set.uIoc_of_le hle] using ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
      have hft : 0 ≤ f t := hf_nonneg t htIcc
      have hftM : f t ≤ M := hf_le_M t htIcc
      rcases hU_bounds t htIcc with ⟨hUge, hUle⟩
      have hpoint : ∀ z ∈ Set.uIoc (-f t) (U t), ‖t * W t z‖ ≤ (M ^ 2) ^ (n - 1) := by
        intro z hz
        have hzIoc : z ∈ Set.Ioc (-f t) (U t) := by
          simpa [Set.uIoc_of_le hUge] using hz
        have hzIcc : z ∈ Set.Icc (-f t) (U t) := Set.Ioc_subset_Icc_self hzIoc
        have hzle : z ≤ f t := le_trans hzIcc.2 hUle
        have hzge : -f t ≤ z := hzIcc.1
        have hW : W t z ≤ (M ^ 2) ^ (n - 1) := by
          dsimp [W]
          have hbase_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by nlinarith
          have hbase_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
            have hf2 : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft hftM 2
            nlinarith [sq_nonneg z]
          exact pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
        have hWnonneg : 0 ≤ W t z := by
          dsimp [W]
          exact pow_nonneg (by nlinarith) _
        have habs_t : |t| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [htIcc.1, htIcc.2]
        calc
          ‖t * W t z‖ = |t * W t z| := by rfl
          _ = |t| * |W t z| := by rw [abs_mul]
          _ = |t| * W t z := by rw [abs_of_nonneg hWnonneg]
          _ ≤ 1 * (M ^ 2) ^ (n - 1) := by
            exact mul_le_mul habs_t hW (by positivity) (by positivity)
          _ = (M ^ 2) ^ (n - 1) := by ring
      have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const (a := -f t) (b := U t) (C := (M ^ 2) ^ (n - 1)) (f := fun z => t * W t z) hpoint
      calc
        ‖∫ z in (-f t)..(U t), t * W t z‖ ≤ (M ^ 2) ^ (n - 1) * |U t - (-f t)| := hnorm_int
        _ ≤ (M ^ 2) ^ (n - 1) * (2 * M) := by
          exact mul_le_mul_of_nonneg_left (hlen_bound t htIcc) (by positivity)
    have hvol_fin : volume (Set.uIoc (-1 : ℝ) 1) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), t * W t z) (Set.uIoc (-1 : ℝ) 1) volume := by
      exact IntegrableOn.of_bound hvol_fin hA_ae.restrict ((M ^ 2) ^ (n - 1) * (2 * M)) h_bound
    rw [intervalIntegrable_iff]
    exact hIntOn
  have hB_int : IntervalIntegrable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume (-1 : ℝ) 1 := by
    have hL_meas : Measurable (fun t : ℝ => -f t) := hf_meas.neg
    have hU_meas : Measurable U := by
      dsimp [U]
      fun_prop
    have hF_meas : Measurable (Function.uncurry (fun t z : ℝ => z * W t z)) := by
      dsimp [W]
      fun_prop
    have hB_ae : AEStronglyMeasurable (fun t => ∫ z in (-f t)..(U t), z * W t z) volume := by
      exact aeStronglyMeasurable_intervalIntegral_param hL_meas hU_meas hF_meas
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)),
        ‖∫ z in (-f t)..(U t), z * W t z‖ ≤ (M * (M ^ 2) ^ (n - 1)) * (2 * M) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [] with t ht
      have hle : (-1 : ℝ) ≤ 1 := by norm_num
      have htIoc : t ∈ Set.Ioc (-1) 1 := by
        simpa [Set.uIoc_of_le hle] using ht
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := Set.Ioc_subset_Icc_self htIoc
      have hft : 0 ≤ f t := hf_nonneg t htIcc
      have hftM : f t ≤ M := hf_le_M t htIcc
      rcases hU_bounds t htIcc with ⟨hUge, hUle⟩
      have hpoint : ∀ z ∈ Set.uIoc (-f t) (U t), ‖z * W t z‖ ≤ M * (M ^ 2) ^ (n - 1) := by
        intro z hz
        have hzIoc : z ∈ Set.Ioc (-f t) (U t) := by
          simpa [Set.uIoc_of_le hUge] using hz
        have hzIcc : z ∈ Set.Icc (-f t) (U t) := Set.Ioc_subset_Icc_self hzIoc
        have hzle : z ≤ f t := le_trans hzIcc.2 hUle
        have hzge : -f t ≤ z := hzIcc.1
        have hW : W t z ≤ (M ^ 2) ^ (n - 1) := by
          dsimp [W]
          have hbase_nonneg : 0 ≤ f t ^ 2 - z ^ 2 := by nlinarith
          have hbase_le : f t ^ 2 - z ^ 2 ≤ M ^ 2 := by
            have hf2 : f t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hft hftM 2
            nlinarith [sq_nonneg z]
          exact pow_le_pow_left₀ hbase_nonneg hbase_le (n - 1)
        have hWnonneg : 0 ≤ W t z := by
          dsimp [W]
          exact pow_nonneg (by nlinarith) _
        have hz_abs_le : |z| ≤ M := by
          rw [abs_le]
          constructor
          · have hnegM_le : -M ≤ z := by
              have hneg : -M ≤ -f t := by nlinarith [hftM]
              exact le_trans hneg hzge
            exact hnegM_le
          · exact le_trans hzle hftM
        calc
          ‖z * W t z‖ = |z * W t z| := by rfl
          _ = |z| * |W t z| := by rw [abs_mul]
          _ = |z| * W t z := by rw [abs_of_nonneg hWnonneg]
          _ ≤ M * (M ^ 2) ^ (n - 1) := by
            exact mul_le_mul hz_abs_le hW (by positivity) (by positivity)
      have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const (a := -f t) (b := U t) (C := M * (M ^ 2) ^ (n - 1)) (f := fun z => z * W t z) hpoint
      calc
        ‖∫ z in (-f t)..(U t), z * W t z‖ ≤ (M * (M ^ 2) ^ (n - 1)) * |U t - (-f t)| := hnorm_int
        _ ≤ (M * (M ^ 2) ^ (n - 1)) * (2 * M) := by
          exact mul_le_mul_of_nonneg_left (hlen_bound t htIcc) (by positivity)
    have hvol_fin : volume (Set.uIoc (-1 : ℝ) 1) < ⊤ := by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_lt_top
    have hIntOn : IntegrableOn (fun t => ∫ z in (-f t)..(U t), z * W t z) (Set.uIoc (-1 : ℝ) 1) volume := by
      exact IntegrableOn.of_bound hvol_fin hB_ae.restrict ((M * (M ^ 2) ^ (n - 1)) * (2 * M)) h_bound
    rw [intervalIntegrable_iff]
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
  have houter_add : (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
        s * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z) =
      ∫ t in (-1 : ℝ)..1, (∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    rw [← intervalIntegral.integral_const_mul]
    have hB_smul : IntervalIntegrable (fun t => s * (∫ z in (-f t)..(U t), z * W t z)) volume (-1 : ℝ) 1 :=
      hB_int.const_mul s
    rw [← intervalIntegral.integral_add hA_int hB_smul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hinner_add t
  have hcap_moment : (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d)) =
      c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
    calc
      (∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))
          = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
              s * (c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z)) := by
            rw [hI0cap', hIlastcap']
      _ = c * ((∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), t * W t z) +
              s * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), z * W t z)) := by ring
      _ = c * (∫ t in (-1 : ℝ)..1, ∫ z in (-f t)..(U t), (t + s * z) * W t z) := by
            rw [houter_add]
  have hrelation : (∫ x in K, x 0) = 2 * ((∫ x in K ∩ H, x 0) + s * (∫ x in K ∩ H, x (lastFin d))) := by
    rw [hI0tot_full, hcap_moment, hmoment]
    ring
  have hvolK : volume.real K = volume.real K := rfl
  have hvolcap : volume.real (K ∩ H) = volume.real K / 2 := by
    simpa [K, H] using hvol s hs
  let D : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in (K ∩ H), x)
  have hDav : D = (volume.real K)⁻¹ • (∫ x in K, x) - (volume.real (K ∩ H))⁻¹ • (∫ x in K ∩ H, x) := by
    dsimp [D]
    rw [setAverage_eq, setAverage_eq]
  have hD_scale : D = (volume.real K)⁻¹ • ((∫ x in K, x) - 2 • (∫ x in K ∩ H, x)) := by
    rw [hDav, hvolcap]
    module
  have hK_meas : MeasurableSet K := by
    simpa [K] using body_of_revolution_measurable (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_support hf_cont hf_left hf_right
  have hK_bdd : Bornology.IsBounded K := by
    simpa [K] using body_of_revolution_bounded (d := d) (R₁ := 1) (R₂ := 1) (f := f)
      hf_conc hf_left hf_right
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
  -- choose lam = -2 * (volume.real K)⁻¹ * (∫ x in K ∩ H, x (lastFin d))
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
  exact mem_span_e0_elast hdpos s lam hD0 hDlast hDmid

end Commons.Geometry.Ulam
