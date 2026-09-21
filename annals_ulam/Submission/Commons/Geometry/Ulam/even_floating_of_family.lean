import Mathlib
import Submission.Commons.Geometry.Ulam.odd_floating_of_family

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma even_floating_of_family {d : ℕ} [NeZero d] {R₁ R₂ : ℝ} {f h : ℝ → ℝ}
    (n : ℕ) (hdn : d = 2 * n) (hn : 2 ≤ n)
    (hf_support : Function.support f ⊆ Set.Icc (-R₁) R₂)
    (hf_smooth : ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂))
    (hf_conc : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f)
    (hf_left : f (-R₁) = 0) (hf_right : f R₂ = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-R₁) R₂, 0 < f t)
    (hh_smooth : ContDiff ℝ ∞ h)
    (h0 : h 0 = 0)
    (hfamily_volume : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      volume.real (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}) =
        volume.real K / 2)
    (hfamily_centroid : ∀ s : ℝ, 0 < s →
      let K : Set (EuclideanSpace ℝ (Fin d)) :=
        {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      let nvec : EuclideanSpace ℝ (Fin d) :=
        EuclideanSpace.single (0 : Fin d) (-s) +
          EuclideanSpace.single (⟨d - 1, by omega⟩ : Fin d) (1 : ℝ)
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | x ⟨d - 1, by omega⟩ ≤ s * x 0 + h s}), x) ∈
        ℝ ∙ nvec) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈
        ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d)) := by
  classical
  let last : Fin d := ⟨d - 1, by omega⟩
  let e0 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (1 : ℝ)
  let elast : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single last (1 : ℝ)
  let K : Set (EuclideanSpace ℝ (Fin d)) := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have hd2 : 2 ≤ d := by omega
  change ∀ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, ∀ t : ℝ,
      volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = volume.real K / 2 →
      (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) ∈ ℝ ∙ (ξ : EuclideanSpace ℝ (Fin d))
  by_cases hK0 : volume.real K = 0
  · intro ξ t ht
    have hH0 : volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ t}) = 0 := by
      rw [ht, hK0]
      norm_num
    have hKavg : (⨍ x in K, x) = (0 : EuclideanSpace ℝ (Fin d)) := by
      simp [MeasureTheory.setAverage_eq, hK0]
    have hHavg : (⨍ x in (K ∩ {x | ⟪x, ξ⟫ ≤ t}), x) = (0 : EuclideanSpace ℝ (Fin d)) := by
      simp [MeasureTheory.setAverage_eq, hH0]
    rw [hKavg, hHavg, sub_zero]
    exact Submodule.zero_mem _
  · have hRlt : -R₁ < R₂ := by
      by_contra hnot
      have hzero := body_of_revolution_measure_zero_of_not_lt (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_left hf_right hnot
      exact hK0 (by simpa [K] using hzero)
    have hK_meas : MeasurableSet K := by
      exact body_of_revolution_measurable (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_support hf_smooth hf_left hf_right
    have hK_conv : Convex ℝ K := by
      exact body_of_revolution_convex (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_conc hf_left hf_right
    have hK_bdd : Bornology.IsBounded K := by
      exact body_of_revolution_bounded (d := d) (f := f) (R₁ := R₁) (R₂ := R₂) hf_conc hf_left hf_right
    have hK_finite : volume K < ⊤ := by
      exact hK_bdd.measure_lt_top
    have hf_cont : ContinuousOn f (Set.Ioo (-R₁) R₂) := hf_smooth.continuousOn
    have hK_int : (interior K).Nonempty := by
      simpa [K] using interior_nonempty_body_of_revolution (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) hRlt hf_cont hf_pos
    have hK_vol_pos : 0 < volume.real K := by
      have hU_open : IsOpen (interior K) := isOpen_interior
      have hU_pos : 0 < volume (interior K) := hU_open.measure_pos (μ := volume) hK_int
      have hU_le : volume (interior K) ≤ volume K := measure_mono (μ := volume) interior_subset
      have hU_fin : volume (interior K) < ⊤ := lt_of_le_of_lt hU_le hK_finite
      have hU_real_pos : 0 < volume.real (interior K) := by
        rw [Measure.real]
        exact ENNReal.toReal_pos (ne_of_gt hU_pos) hU_fin.ne
      have hmono : volume.real (interior K) ≤ volume.real K := by
        simpa [Measure.real] using ENNReal.toReal_mono hK_finite.ne hU_le
      exact lt_of_lt_of_le hU_real_pos hmono
    have hhalf_pos : 0 < volume.real K / 2 := by nlinarith
    have hhalf_lt : volume.real K / 2 < volume.real K := by nlinarith
    intro ξ t ht
    let ξv : EuclideanSpace ℝ (Fin d) := ξ
    obtain ⟨R, hR0, a, b, hb_nonneg, hRξ⟩ := exists_tail_linearIsometryEquiv_map_to_last (d := d) hd2 ξv
    let H : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x | ⟪x, ξv⟫ ≤ t}
    have hvolH : volume.real H = volume.real K / 2 := by simpa [H] using ht
    have hRK : R '' K = K := by
      simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) R hR0
    have hRimageH : R '' H = K ∩ {y | ⟪y, R ξv⟫ ≤ t} := by
      calc
        R '' H = R '' K ∩ R '' {x | ⟪x, ξv⟫ ≤ t} := by
          dsimp [H]
          rw [Set.image_inter R.injective]
        _ = K ∩ {y | ⟪y, R ξv⟫ ≤ t} := by
          rw [hRK, halfspace_image_linearIsometryEquiv R ξv t]
    have hvol_image : volume H = volume (R '' H) := by
      have hpre := R.measurePreserving.measure_preimage_emb R.toMeasurableEquiv.measurableEmbedding (R '' H)
      have hpre' : R ⁻¹' (R '' H) = H := Set.preimage_image_eq H R.injective
      rwa [hpre'] at hpre
    have hvolR : volume.real (K ∩ {y | ⟪y, R ξv⟫ ≤ t}) = volume.real K / 2 := by
      have hvol_image_real : volume.real H = volume.real (R '' H) := congrArg ENNReal.toReal hvol_image
      rw [hRimageH] at hvol_image_real
      rw [← hvol_image_real]
      exact hvolH
    have hRavgK : R (⨍ x in K, x) = ⨍ x in K, x := by
      exact setAverage_linearIsometryEquiv_invariant R K hRK
    have hRavgH : R (⨍ x in H, x) = ⨍ y in (K ∩ {y | ⟪y, R ξv⟫ ≤ t}), y := by
      have h1 := average_image_linearIsometryEquiv R H
      simpa [hRimageH] using h1
    have hrot : (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, R ξv⟫ ≤ t}), x) ∈ ℝ ∙ (R ξv) := by
      let η : EuclideanSpace ℝ (Fin d) := R ξv
      let Drot : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, η⟫ ≤ t}), x)
      change Drot ∈ ℝ ∙ η
      have hη : η = a • e0 + b • elast := hRξ
      have hlast_ne : last ≠ 0 := by
        dsimp [last]
        exact Fin.ne_of_val_ne (by simp; omega)
      by_cases hb0 : b = 0
      · have hη_e0 : η = a • e0 := by simpa [hb0] using hη
        have ha_ne : a ≠ 0 := by
          intro ha0
          have hη0 : η = 0 := by simp [hη_e0, ha0]
          have hnormη : ‖η‖ = 0 := by simp [hη0]
          have hnormξ : ‖η‖ = ‖ξv‖ := R.norm_map ξv
          have hξnorm : ‖ξv‖ = 1 := by
            simpa [ξv] using ξ.2
          linarith
        have hsp : ℝ ∙ η = ℝ ∙ e0 := by
          rw [hη_e0, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha_ne) e0]
        let L0 : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := Submodule.reflection (ℝ ∙ e0)
        have hL0e0 : L0 e0 = e0 := by
          exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self e0)
        have hL0K : L0 '' K = K := by
          simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) L0 hL0e0
        have hL0η : L0 η = η := by
          rw [hη_e0, map_smul, hL0e0]
        have hL0half : L0 '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} = {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} := by
          rw [halfspace_image_linearIsometryEquiv L0 η t, hL0η]
        have hL0H : L0 '' (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}) = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} := by
          calc
            L0 '' (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t})
                = L0 '' K ∩ L0 '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} := by rw [Set.image_inter L0.injective]
            _ = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} := by rw [hL0K, hL0half]
        have hL0avgK : L0 (⨍ x in K, x) = ⨍ x in K, x :=
          setAverage_linearIsometryEquiv_invariant L0 K hL0K
        have hL0avgH : L0 (⨍ x in (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}), x) =
            ⨍ x in (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}), x :=
          setAverage_linearIsometryEquiv_invariant L0 (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}) hL0H
        have hL0D : L0 Drot = Drot := by
          dsimp [Drot]
          rw [map_sub, hL0avgK, hL0avgH]
        have hD_mem_e0 : Drot ∈ ℝ ∙ e0 := by
          exact (Submodule.reflection_eq_self_iff (x := Drot)).1 hL0D
        simpa [hsp] using hD_mem_e0
      · have hbpos : 0 < b := lt_of_le_of_ne hb_nonneg (Ne.symm hb0)
        have hdirect_case : ∀ {a' b' : ℝ}, 0 < b' → a' < 0 → ∀ {t' : ℝ},
            volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}) = volume.real K / 2 →
            (⨍ x in K, x) - (⨍ x in (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}), x) ∈
              ℝ ∙ (a' • e0 + b' • elast) := by
          intro a' b' hb' ha' t' hvol'
          let s : ℝ := -a' / b'
          have hs_pos : 0 < s := by
            dsimp [s]
            exact div_pos (neg_pos.mpr ha') hb'
          let c : ℝ := t' / b'
          let n_s : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (-s) + EuclideanSpace.single last (1 : ℝ)
          have hlast_ne : last ≠ 0 := by
            dsimp [last]
            exact Fin.ne_of_val_ne (by simp; omega)
          have hn_s_ne : n_s ≠ 0 := by
            intro h
            have hlast_val : n_s last = 1 := by simp [n_s, hlast_ne]
            have hlast := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v last) h
            simp [hlast_val] at hlast
          have hset_rot : {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} = {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + c} := by
            have hset := halfspace_plane_last_le_slope_intercept (d := d) hd2 (a := a') (b := b') (s := s) (c := c) (t := t') hb' (by dsimp [s]) (by dsimp [c])
            simpa using hset
          have hset_ns : {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + c} = {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c} := by
            exact halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := c)
          have hvol_c : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c}) = volume.real K / 2 := by
            have h1 : K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} = K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + c} := by
              rw [hset_rot]
            have h2 : K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + c} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c} := by
              rw [hset_ns]
            rwa [h1, h2] at hvol'
          have hvol_hs : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s}) = volume.real K / 2 := by
            have hfamvol := hfamily_volume s hs_pos
            have hset := halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := h s)
            have h1 : K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s} := by
              exact congrArg (fun A : Set (EuclideanSpace ℝ (Fin d)) => K ∩ A) hset
            simpa [K] using h1 ▸ hfamvol
          have hc_pos : 0 < volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c}) := by
            rw [hvol_c]; exact hhalf_pos
          have hc_lt : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c}) < volume.real K := by
            rw [hvol_c]; exact hhalf_lt
          have hh_pos : 0 < volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s}) := by
            rw [hvol_hs]; exact hhalf_pos
          have hh_lt : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s}) < volume.real K := by
            rw [hvol_hs]; exact hhalf_lt
          have hc_eq : c = h s := by
            exact Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
              (hK_meas := hK_meas) (hK_conv := hK_conv) (hK_int := hK_int) (hK_finite := hK_finite)
              (hξ := hn_s_ne) (a := c) (b := h s)
              hc_pos hc_lt hh_pos hh_lt (by rw [hvol_c, hvol_hs])
          have hfam_cent : (⨍ x in K, x) - (⨍ x in (K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s}), x) ∈ ℝ ∙ n_s := by
            simpa [K, n_s, e0, elast] using hfamily_centroid s hs_pos
          have hH_eq_fam : K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} := by
            have hset_fam := halfspace_last_le_slope_intercept_eq_inner_single (d := d) hd2 (s := s) (c := h s)
            have h1 : K ∩ {x : EuclideanSpace ℝ (Fin d) | x last ≤ s * x 0 + h s} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s} := by
              exact congrArg (fun A : Set (EuclideanSpace ℝ (Fin d)) => K ∩ A) hset_fam
            have h2 : K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ h s} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c} := by rw [hc_eq]
            have h3 : K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, n_s⟫ ≤ c} = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'} := by
              rw [← hset_ns, ← hset_rot]
            rw [h1, h2, h3]
          have hD_mem_ns : (⨍ x in K, x) - (⨍ x in (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a' • e0 + b' • elast⟫ ≤ t'}), x) ∈ ℝ ∙ n_s := by
            rw [← hH_eq_fam]
            exact hfam_cent
          have ha_eq : a' = -s * b' := by
            dsimp [s]
            field_simp [ne_of_gt hb']
          have hsp : ℝ ∙ (a' • e0 + b' • elast) = ℝ ∙ n_s := by
            have hn : a' • e0 + b' • elast = b' • n_s := by
              rw [ha_eq]
              ext i
              by_cases hi0 : i = 0
              · subst i
                simp [n_s, e0, elast, hlast_ne]
                ring
              · by_cases hilast : i = last
                · subst i
                  simp [n_s, e0, elast, hlast_ne]
                · simp [n_s, e0, elast, hi0, hilast]
            rw [hn, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hb')) n_s]
          simpa [hsp] using hD_mem_ns
        by_cases ha0 : a = 0
        · let c : ℝ := t / b
          let A0 : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0}
          let B0 : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x : EuclideanSpace ℝ (Fin d) | 0 ≤ ⟪x, elast⟫}
          have helast_ne : elast ≠ 0 := by
            intro h
            have hlast := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v last) h
            simp [elast] at hlast
          have hη_eq : η = b • elast := by
            rw [hη, ha0]
            simp
          have hset_c : {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} = {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ c} := by
            ext x
            have hinner : ⟪x, η⟫ = b * ⟪x, elast⟫ := by
              rw [hη_eq]
              rw [inner_smul_right]
            constructor
            · intro hx
              change ⟪x, η⟫ ≤ t at hx
              rw [hinner] at hx
              rw [← le_div_iff₀' hbpos] at hx
              change ⟪x, elast⟫ ≤ c
              simpa [c] using hx
            · intro hx
              change ⟪x, elast⟫ ≤ c at hx
              change ⟪x, η⟫ ≤ t
              rw [hinner]
              rw [← le_div_iff₀' hbpos]
              simpa [c] using hx
          have hvolη : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}) = volume.real K / 2 := by
            simpa [η] using hvolR
          have hvol_c : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ c}) = volume.real K / 2 := by
            rw [← hset_c]
            exact hvolη
          let L0 : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := Submodule.reflection (ℝ ∙ e0)
          have hL0e0 : L0 e0 = e0 := by
            exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self e0)
          have hL0K : L0 '' K = K := by
            simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) L0 hL0e0
          have helast_orth : elast ∈ (ℝ ∙ e0)ᗮ := by
            rw [Submodule.mem_orthogonal_singleton_iff_inner_left, EuclideanSpace.inner_single_left]
            simp [elast, e0, hlast_ne]
          have hL0elast : L0 elast = -elast := by
            exact Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg helast_orth
          have hL0_halfA : L0 '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} = {x : EuclideanSpace ℝ (Fin d) | 0 ≤ ⟪x, elast⟫} := by
            rw [halfspace_image_linearIsometryEquiv L0 elast 0, hL0elast]
            ext x
            constructor
            · intro hx
              change ⟪x, -elast⟫ ≤ 0 at hx
              rw [inner_neg_right] at hx
              change 0 ≤ ⟪x, elast⟫
              linarith
            · intro hx
              change 0 ≤ ⟪x, elast⟫ at hx
              change ⟪x, -elast⟫ ≤ 0
              rw [inner_neg_right]
              linarith
          have hL0A0 : L0 '' A0 = B0 := by
            dsimp [A0, B0]
            calc
              L0 '' (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0})
                  = L0 '' K ∩ L0 '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} := by
                    rw [Set.image_inter L0.injective]
              _ = K ∩ {x : EuclideanSpace ℝ (Fin d) | 0 ≤ ⟪x, elast⟫} := by rw [hL0K, hL0_halfA]
          have hvol_A0_eq : volume.real A0 = volume.real B0 := by
            have hpre := L0.measurePreserving.measure_preimage_emb L0.toMeasurableEquiv.measurableEmbedding (L0 '' A0)
            have hpre' : L0 ⁻¹' (L0 '' A0) = A0 := Set.preimage_image_eq A0 L0.injective
            have himage : volume A0 = volume (L0 '' A0) := by
              rwa [hpre'] at hpre
            have himage_real := congrArg ENNReal.toReal himage
            rwa [hL0A0] at himage_real
          have hsum0 : volume.real A0 + volume.real B0 = volume.real K := by
            simpa [A0, B0] using measureReal_union_halfspaces (K := K) hK_meas hK_finite (η := elast) helast_ne (c := 0)
          have hvol_0 : volume.real A0 = volume.real K / 2 := by
            rw [hvol_A0_eq] at hsum0
            nlinarith
          have hvol_B0 : volume.real B0 = volume.real K / 2 := by
            rw [← hvol_A0_eq, hvol_0]
          have hc_pos : 0 < volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ c}) := by
            rw [hvol_c]
            exact hhalf_pos
          have hc_lt : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ c}) < volume.real K := by
            rw [hvol_c]
            exact hhalf_lt
          have h0_pos : 0 < volume.real A0 := by
            rw [hvol_0]
            exact hhalf_pos
          have h0_lt : volume.real A0 < volume.real K := by
            rw [hvol_0]
            exact hhalf_lt
          have hvol_eq : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ c}) = volume.real A0 := by
            rw [hvol_c, hvol_0]
          have hc_eq0 : c = 0 := by
            exact Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
              (hK_meas := hK_meas) (hK_conv := hK_conv) (hK_int := hK_int) (hK_finite := hK_finite)
              (hξ := helast_ne) (a := c) (b := 0)
              hc_pos hc_lt h0_pos h0_lt hvol_eq
          have hH_eq_A0 : K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t} = A0 := by
            rw [hset_c, hc_eq0]
          have hDrot_eq : Drot = (⨍ x in K, x) - (⨍ x in A0, x) := by
            dsimp [Drot]
            rw [hH_eq_A0]
          have hu_meas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ⟪x, elast⟫) := by
            exact (continuous_id.inner continuous_const).measurable
          have hA0_meas : MeasurableSet A0 := hK_meas.inter (measurableSet_le hu_meas measurable_const)
          have hB0_meas : MeasurableSet B0 := hK_meas.inter (measurableSet_le measurable_const hu_meas)
          have hA0B0_sub : A0 ∩ B0 ⊆ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ = 0} := by
            intro x hx
            rcases hx with ⟨⟨hxK, hxle⟩, hxK', hxge⟩
            exact le_antisymm hxle hxge
          have hA0B0_zero : volume (A0 ∩ B0) = 0 := by
            apply le_antisymm ?_ bot_le
            calc
              volume (A0 ∩ B0) ≤ volume {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ = 0} := measure_mono (μ := volume) hA0B0_sub
              _ = 0 := volume_hyperplane_eq_zero helast_ne 0
          have hA0B0_disj : AEDisjoint volume A0 B0 := by
            rw [AEDisjoint]
            exact hA0B0_zero
          have hA0B0_union : A0 ∪ B0 = K := by
            ext x
            constructor
            · intro hx
              rcases hx with hx | hx <;> exact hx.1
            · intro hxK
              by_cases hle : ⟪x, elast⟫ ≤ 0
              · exact Or.inl ⟨hxK, hle⟩
              · exact Or.inr ⟨hxK, le_of_lt (lt_of_not_ge hle)⟩
          have hA0_fin : volume A0 < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
          have hB0_fin : volume B0 < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
          have hrel0 := setAverage_sub_eq_neg_sub_of_measure_eq_union
            (hK_meas := hK_meas) (hK_bdd := hK_bdd)
            (hA_meas := hA0_meas) (hB_meas := hB0_meas)
            (hAB_disj := hA0B0_disj) (hAB_union := hA0B0_union)
            (hA_fin := hA0_fin) (hB_fin := hB0_fin)
            (hK_vol_pos := hK_vol_pos) (hA_vol := hvol_0) (hB_vol := hvol_B0)
          have hL0avgK : L0 (⨍ x in K, x) = ⨍ x in K, x :=
            setAverage_linearIsometryEquiv_invariant L0 K hL0K
          have hL0avgA0 : L0 (⨍ x in A0, x) = ⨍ x in B0, x := by
            have h1 := average_image_linearIsometryEquiv L0 A0
            simpa [hL0A0] using h1
          have hneg0 : (⨍ x in K, x) - (⨍ x in B0, x) = -((⨍ x in K, x) - (⨍ x in A0, x)) := by
            have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => -v) hrel0
            simpa using h.symm
          have hL0Drot : L0 Drot = -Drot := by
            rw [hDrot_eq]
            rw [map_sub, hL0avgK, hL0avgA0]
            exact hneg0
          have hDrot0 : Drot 0 = 0 := by
            have h1 : ⟪L0 Drot, e0⟫ = ⟪Drot, e0⟫ := by
              have h := LinearIsometryEquiv.inner_map_map L0 Drot e0
              simpa [hL0e0] using h
            have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => ⟪v, e0⟫) hL0Drot
            rw [h1] at h
            rw [inner_neg_left] at h
            have hinner : ⟪Drot, e0⟫ = 0 := by linarith
            have hcoord := coord0_eq_inner_single Drot
            simpa [e0] using hcoord.trans hinner
          have htail_zero : ∀ j : Fin d, j ≠ 0 → j ≠ last → Drot j = 0 := by
            intro j hj0 hjlast
            let Lj : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := Submodule.reflection ((ℝ ∙ EuclideanSpace.single j (1:ℝ))ᗮ)
            have hLj_e0 : Lj e0 = e0 := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := j) (w := e0)
              dsimp [e0]
              rw [EuclideanSpace.inner_single_right]
              simp [hj0]
            have hLj_elast : Lj elast = elast := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := j) (w := elast)
              rw [EuclideanSpace.inner_single_right]
              simp [elast, hjlast]
            have hLjK : Lj '' K = K := by
              simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) Lj hLj_e0
            have hLj_half : Lj '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} = {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} := by
              rw [halfspace_image_linearIsometryEquiv Lj elast 0, hLj_elast]
            have hLjA0 : Lj '' A0 = A0 := by
              dsimp [A0]
              calc
                Lj '' (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0})
                    = Lj '' K ∩ Lj '' {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} := by
                      rw [Set.image_inter Lj.injective]
                _ = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, elast⟫ ≤ 0} := by rw [hLjK, hLj_half]
            have hLjavgK : Lj (⨍ x in K, x) = ⨍ x in K, x :=
              setAverage_linearIsometryEquiv_invariant Lj K hLjK
            have hLjavgA0 : Lj (⨍ x in A0, x) = ⨍ x in A0, x :=
              setAverage_linearIsometryEquiv_invariant Lj A0 hLjA0
            have hLjDrot : Lj Drot = Drot := by
              rw [hDrot_eq]
              rw [map_sub, hLjavgK, hLjavgA0]
            exact coord_eq_zero_of_reflection_hyperplane_fix (j := j) (v := Drot) (by simpa [Lj] using hLjDrot)
          have hDrot_eq_elast : Drot = (Drot last) • elast := by
            ext i
            by_cases hilast : i = last
            · subst i
              simp [elast]
            · by_cases hi0 : i = 0
              · subst i
                rw [hDrot0]
                simp [elast, hlast_ne]
              · have hcoord := htail_zero i hi0 hilast
                rw [hcoord]
                simp [elast, hilast]
          have hD_mem_elast : Drot ∈ ℝ ∙ elast := by
            rw [Submodule.mem_span_singleton]
            exact ⟨Drot last, hDrot_eq_elast.symm⟩
          have hsp_η : ℝ ∙ η = ℝ ∙ elast := by
            rw [hη_eq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hbpos)) elast]
          simpa [hsp_η] using hD_mem_elast
        · by_cases haneg : a < 0
          · have hvolη : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, a • e0 + b • elast⟫ ≤ t}) = volume.real K / 2 := by
              simpa [η, hη] using hvolR
            have hdir := hdirect_case hbpos haneg (t' := t) hvolη
            simpa [Drot, η, hη] using hdir
          · have hapos : 0 < a := lt_of_le_of_ne (le_of_not_gt haneg) (Ne.symm ha0)
            let η' : EuclideanSpace ℝ (Fin d) := (-a) • e0 + b • elast
            let Hpos : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}
            let Hneg : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x : EuclideanSpace ℝ (Fin d) | t ≤ ⟪x, η⟫}
            let Hneg' : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η'⟫ ≤ -t}
            have hη_ne : η ≠ 0 := by
              intro hη0
              have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v last) hη0
              have hη_last : η last = b := by
                rw [hη]
                simp [e0, elast, hlast_ne]
              rw [hη_last] at hcoord
              simp at hcoord
              linarith [hbpos]
            have hvolHpos : volume.real Hpos = volume.real K / 2 := by
              dsimp [Hpos]
              simpa [η] using hvolR
            have hsum : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}) + volume.real Hneg = volume.real K := by
              simpa [Hneg] using measureReal_union_halfspaces (K := K) hK_meas hK_finite (η := η) hη_ne (c := t)
            have hvolHpos' : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ ≤ t}) = volume.real K / 2 := by
              simpa [η] using hvolR
            have hvolcomp : volume.real Hneg = volume.real K / 2 := by
              have hsum' := hsum
              rw [hvolHpos'] at hsum'
              nlinarith
            let Lflip : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) := Submodule.reflection ((ℝ ∙ elast)ᗮ)
            have hLflip_e0 : Lflip e0 = e0 := by
              apply reflection_hyperplane_single_fixes_of_inner_eq_zero (j := last) (w := e0)
              dsimp [e0]
              rw [EuclideanSpace.inner_single_right]
              simp [hlast_ne]
            have hLflip_elast : Lflip elast = -elast := by
              dsimp [Lflip]
              simpa [elast] using (Submodule.reflection_orthogonalComplement_singleton_eq_neg (EuclideanSpace.single last (1:ℝ)))
            have hLflip_inv : Function.Involutive Lflip := Submodule.reflection_involutive ((ℝ ∙ elast)ᗮ)
            have hLflipK : Lflip '' K = K := by
              simpa [K] using body_of_revolution_tail_linearIsometryEquiv_image (d := d) (R₁ := R₁) (R₂ := R₂) (f := f) Lflip hLflip_e0
            have hLflip_η' : Lflip η' = -η := by
              dsimp [η']
              rw [map_add, map_smul, map_smul, hLflip_e0, hLflip_elast, hη]
              ext i
              by_cases hi0 : i = 0
              · subst i
                simp [e0, elast, hlast_ne]
              · by_cases hilast : i = last
                · subst i
                  simp [e0, elast, hlast_ne]
                · simp [e0, elast, hi0, hilast]
            have hset_ge : {x : EuclideanSpace ℝ (Fin d) | t ≤ ⟪x, η⟫} = {x : EuclideanSpace ℝ (Fin d) | ⟪x, -η⟫ ≤ -t} := by
              ext x
              constructor
              · intro hx
                change t ≤ ⟪x, η⟫ at hx
                change ⟪x, -η⟫ ≤ -t
                rw [inner_neg_right]
                linarith
              · intro hx
                change ⟪x, -η⟫ ≤ -t at hx
                rw [inner_neg_right] at hx
                change t ≤ ⟪x, η⟫
                linarith
            have hLflip_negη : Lflip (-η) = η' := by
              have h' := congrArg (fun v : EuclideanSpace ℝ (Fin d) => Lflip v) hLflip_η'
              have h'' : Lflip (Lflip η') = η' := hLflip_inv η'
              simpa [h''] using h'.symm
            have hLflip_half_comp : Lflip '' {x : EuclideanSpace ℝ (Fin d) | t ≤ ⟪x, η⟫} =
                {x : EuclideanSpace ℝ (Fin d) | ⟪x, η'⟫ ≤ -t} := by
              rw [hset_ge, halfspace_image_linearIsometryEquiv Lflip (-η) (-t)]
              simpa [hLflip_negη]
            have hLflipHneg : Lflip '' Hneg = Hneg' := by
              dsimp [Hneg, Hneg']
              calc
                Lflip '' (K ∩ {x : EuclideanSpace ℝ (Fin d) | t ≤ ⟪x, η⟫})
                    = Lflip '' K ∩ Lflip '' {x : EuclideanSpace ℝ (Fin d) | t ≤ ⟪x, η⟫} := by
                      rw [Set.image_inter Lflip.injective]
                _ = K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η'⟫ ≤ -t} := by rw [hLflipK, hLflip_half_comp]
            have hvol_image : volume Hneg = volume (Lflip '' Hneg) := by
              have hpre := Lflip.measurePreserving.measure_preimage_emb Lflip.toMeasurableEquiv.measurableEmbedding (Lflip '' Hneg)
              have hpre' : Lflip ⁻¹' (Lflip '' Hneg) = Hneg := Set.preimage_image_eq Hneg Lflip.injective
              rwa [hpre'] at hpre
            have hvol_image_real : volume.real Hneg = volume.real (Lflip '' Hneg) := congrArg ENNReal.toReal hvol_image
            have hvolHneg' : volume.real Hneg' = volume.real K / 2 := by
              rw [← hLflipHneg]
              rw [← hvol_image_real]
              exact hvolcomp
            have hvol' : volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, (-a) • e0 + b • elast⟫ ≤ -t}) = volume.real K / 2 := by
              simpa [Hneg', η'] using hvolHneg'
            have hneg : -a < 0 := by linarith [hapos]
            have hdir := hdirect_case (a' := -a) (b' := b) hbpos hneg (t' := -t) hvol'
            let Dcomp : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in Hneg', x)
            have hdir_mem : Dcomp ∈ ℝ ∙ η' := by
              simpa [Dcomp, Hneg', η'] using hdir
            have hLflip_avgK : Lflip (⨍ x in K, x) = ⨍ x in K, x :=
              setAverage_linearIsometryEquiv_invariant Lflip K hLflipK
            have hLflip_avgHneg : Lflip (⨍ x in Hneg, x) = ⨍ x in Hneg', x := by
              have h1 := average_image_linearIsometryEquiv Lflip Hneg
              simpa [hLflipHneg] using h1
            let Dneg : EuclideanSpace ℝ (Fin d) := (⨍ x in K, x) - (⨍ x in Hneg, x)
            have hLflipDneg : Lflip Dneg = Dcomp := by
              dsimp [Dneg, Dcomp]
              rw [map_sub, hLflip_avgK, hLflip_avgHneg]
            have hu_meas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ⟪x, η⟫) := by
              exact (continuous_id.inner continuous_const).measurable
            have hHpos_meas : MeasurableSet Hpos := hK_meas.inter (measurableSet_le hu_meas measurable_const)
            have hHneg_meas : MeasurableSet Hneg := hK_meas.inter (measurableSet_le measurable_const hu_meas)
            have hHposHneg_sub : Hpos ∩ Hneg ⊆ {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ = t} := by
              intro x hx
              rcases hx with ⟨⟨hxK, hxle⟩, hxK', hxge⟩
              exact le_antisymm hxle hxge
            have hHposHneg_zero : volume (Hpos ∩ Hneg) = 0 := by
              apply le_antisymm ?_ bot_le
              calc
                volume (Hpos ∩ Hneg) ≤ volume {x : EuclideanSpace ℝ (Fin d) | ⟪x, η⟫ = t} := measure_mono (μ := volume) hHposHneg_sub
                _ = 0 := volume_hyperplane_eq_zero hη_ne t
            have hHposHneg_disj : AEDisjoint volume Hpos Hneg := by
              rw [AEDisjoint]
              exact hHposHneg_zero
            have hHposHneg_union : Hpos ∪ Hneg = K := by
              ext x
              constructor
              · intro hx
                rcases hx with hx | hx <;> exact hx.1
              · intro hxK
                by_cases hle : ⟪x, η⟫ ≤ t
                · exact Or.inl ⟨hxK, hle⟩
                · exact Or.inr ⟨hxK, le_of_lt (lt_of_not_ge hle)⟩
            have hHpos_fin : volume Hpos < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
            have hHneg_fin : volume Hneg < ⊤ := lt_of_le_of_lt (measure_mono (μ := volume) (fun x hx => hx.1)) hK_finite
            have hDneg_rel := setAverage_sub_eq_neg_sub_of_measure_eq_union
              (hK_meas := hK_meas) (hK_bdd := hK_bdd)
              (hA_meas := hHpos_meas) (hB_meas := hHneg_meas)
              (hAB_disj := hHposHneg_disj) (hAB_union := hHposHneg_union)
              (hA_fin := hHpos_fin) (hB_fin := hHneg_fin)
              (hK_vol_pos := hK_vol_pos) (hA_vol := hvolHpos) (hB_vol := hvolcomp)
            have hDneg_eq : Dneg = Lflip Dcomp := by
              have h' := congrArg (fun v : EuclideanSpace ℝ (Fin d) => Lflip v) hLflipDneg
              have h'' : Lflip (Lflip Dneg) = Dneg := hLflip_inv Dneg
              simpa [h''] using h'
            have hDneg_eq' : (⨍ x in K, x) - (⨍ x in Hneg, x) = Lflip Dcomp := by
              simpa [Dneg] using hDneg_eq
            have hDrot_eq : Drot = - Lflip Dcomp := by
              dsimp [Drot]
              have hrel := hDneg_rel
              rw [hDneg_eq'] at hrel
              simpa [Hpos] using hrel
            have hLflipDcomp_mem : Lflip Dcomp ∈ ℝ ∙ (-η) := by
              have hdir_flip : Lflip Dcomp ∈ ℝ ∙ (Lflip η') := by
                rw [Submodule.mem_span_singleton] at hdir_mem ⊢
                rcases hdir_mem with ⟨c, hc⟩
                refine ⟨c, ?_⟩
                have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => Lflip v) hc
                simpa [map_smul] using h
              simpa [hLflip_η'] using hdir_flip
            have hmem_Drot : Drot ∈ ℝ ∙ η := by
              rw [Submodule.mem_span_singleton] at hLflipDcomp_mem ⊢
              rcases hLflipDcomp_mem with ⟨c, hc⟩
              refine ⟨c, ?_⟩
              have hneg' := congrArg (fun v : EuclideanSpace ℝ (Fin d) => -v) hc
              calc
                c • η = - (c • (-η)) := by simp
                _ = - Lflip Dcomp := by rw [hneg']
                _ = Drot := by rw [hDrot_eq]
            exact hmem_Drot
    have hRdiff : R ((⨍ x in K, x) - (⨍ x in H, x)) =
        (⨍ x in K, x) - (⨍ x in (K ∩ {x | ⟪x, R ξv⟫ ≤ t}), x) := by
      rw [map_sub, hRavgK, hRavgH]
    have hmain : (⨍ x in K, x) - (⨍ x in H, x) ∈ ℝ ∙ ξv := by
      have hspan := mem_span_smul_of_linearIsometryEquiv R (v := (⨍ x in K, x) - (⨍ x in H, x)) (ξ := ξv) ?_
      · simpa [hRdiff] using hspan
      · simpa [hRdiff] using hrot
    simpa [H] using hmain

end Commons.Geometry.Ulam
