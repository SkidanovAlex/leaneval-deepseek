import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Convolution.commutator_oscillation_lintegral

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Lipschitz estimate for a `C¹` function on a ball: there is a constant `K ≥ 0` such that
`‖g (x - y) - g x‖ ≤ K * ‖y‖` whenever `‖x‖ ≤ M` and `‖y‖ ≤ 1`. -/
theorem exists_lipschitzOn_closedBall_contDiff_one {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : (Fin d → ℂ) → F)
    (hg : ContDiff ℝ 1 g) (M : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Fin d → ℂ, ‖x‖ ≤ M → ‖y‖ ≤ 1 →
      ‖g (x - y) - g x‖ ≤ K * ‖y‖ := by
  set Rd : ℝ := max M 0 + 1 with hRdef
  have hMle : M ≤ Rd := by
    have h : M ≤ max M 0 := le_max_left _ _
    rw [hRdef]; linarith
  obtain ⟨K, hK⟩ := ContDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0 : Fin d → ℂ) Rd) hg.contDiffOn (n := 1) (by norm_num)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro x y hx hy
  have hxmem : x ∈ Metric.closedBall (0 : Fin d → ℂ) Rd := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact le_trans hx hMle
  have hymem : x - y ∈ Metric.closedBall (0 : Fin d → ℂ) Rd := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    have h2 : M + 1 ≤ Rd := by
      have h : M ≤ max M 0 := le_max_left _ _
      rw [hRdef]; linarith
    linarith
  have h := hK.dist_le_mul x hxmem (x - y) hymem
  rw [dist_eq_norm, dist_eq_norm] at h
  have hsub : x - (x - y) = y := by abel
  rw [hsub] at h
  have h' : ‖g (x - y) - g x‖ ≤ (K : ℝ) * ‖y‖ := by
    rw [norm_sub_rev]; exact h
  simpa using h'

private lemma ae_eq_comp_sub_left_vec {d : ℕ} {f f' : (Fin d → ℂ) → ℝ≥0∞}
    (h : f =ᵐ[(volume : Measure (Fin d → ℂ))] f') (x : Fin d → ℂ) :
    (fun y => f (x - y)) =ᵐ[(volume : Measure (Fin d → ℂ))] (fun y => f' (x - y)) :=
  (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae_eq_comp h

theorem tendsto_lintegral_oscillation_defect_sq_vec {d : ℕ} {ι : Type*} {l : Filter ι}
    (g : Fin d → (Fin d → ℂ) → ℂ) (hg : ∀ j, ContDiff ℝ 1 (g j))
    (κ : (Fin d → ℂ) → ℝ) (hκc : Continuous κ) (hκnn : ∀ x, 0 ≤ κ x)
    (ρ : ι → (Fin d → ℂ) → ℝ) (hρnn : ∀ i x, 0 ≤ ρ i x)
    (hρi : ∀ i, MeasureTheory.Integrable (ρ i) (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) = 1)
    (R : ι → ℝ) (hRpos : ∀ i, 0 ≤ R i) (hR : Filter.Tendsto R l (nhds 0))
    (hRs : ∀ i, ∀ x, R i < ‖x‖ → ρ i x = 0)
    (u : (Fin d → ℂ) → (Fin d → ℂ)) (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))
    (hus : HasCompactSupport u) :
    Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal
      (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) l (nhds 0) := by
  classical
  -- ===== Step 1: support bound for u =====
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℝ, ∀ x, u x ≠ 0 → ‖x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hus.isCompact.isBounded.exists_norm_le
    exact ⟨M, fun x hx => hM x (subset_tsupport u (Function.mem_support.mpr hx))⟩
  set M₁ : ℝ := max M₀ 0 with hM₁def
  have hM₁le : M₀ ≤ M₁ := le_max_left _ _
  have hsupp : ∀ x, u x ≠ 0 → ‖x‖ ≤ M₁ := fun x hx => le_trans (hM₀ x hx) hM₁le
  -- ===== Step 2: joint Lipschitz constant for the vector of g j =====
  have hvec : ContDiff ℝ 1 (fun x : Fin d → ℂ => fun j => g j x) := contDiff_pi.mpr hg
  obtain ⟨K, hKnn, hK⟩ := exists_lipschitzOn_closedBall_contDiff_one
    (fun x : Fin d → ℂ => fun j => g j x) hvec (M₁ + 1)
  have hKj : ∀ j x y, ‖x‖ ≤ M₁ + 1 → ‖y‖ ≤ 1 → ‖g j (x - y) - g j x‖ ≤ K * ‖y‖ := by
    intro j x y hx hy
    exact (norm_le_pi_norm (fun k => g k (x - y) - g k x) j).trans (hK x y hx hy)
  -- ===== Step 3: a bound for κ on the relevant ball =====
  obtain ⟨Cκ₀, hCκ₀⟩ :=
    (isCompact_closedBall (0 : Fin d → ℂ) (M₁ + 1)).exists_bound_of_continuousOn hκc.continuousOn
  set Ck : ℝ := max Cκ₀ 0 with hCkdef
  have hCknn : 0 ≤ Ck := le_max_right _ _
  have hκle_s : ∀ x, x ∈ Metric.closedBall (0 : Fin d → ℂ) (M₁ + 1) → κ x ≤ Ck := by
    intro x hx
    have h := hCκ₀ x hx
    rw [Real.norm_of_nonneg (hκnn x)] at h
    exact le_trans h (le_max_left _ _)
  -- ===== Step 4: finiteness of the L² mass of u =====
  set N : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)
      ∂(volume : Measure (Fin d → ℂ)) with hNdef
  have hNlt : N < ⊤ := by
    rw [hNdef]
    have hsplit : (∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(volume : Measure (Fin d → ℂ)))
        = (eLpNorm u 2 (volume : Measure (Fin d → ℂ))) ^ (2:ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
      rw [← ENNReal.rpow_mul]
      norm_num
    calc (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)))
        = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(volume : Measure (Fin d → ℂ)) :=
          lintegral_congr fun x => by
            rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ = (eLpNorm u 2 (volume : Measure (Fin d → ℂ))) ^ (2:ℝ) := hsplit
      _ < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt hu.eLpNorm_lt_top)
  -- ===== Step 5: the key bound =====
  have key : ∀ i, R i ≤ 1 → (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
          ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
        ∂(volume : Measure (Fin d → ℂ)))
      ≤ ENNReal.ofReal (Ck * (K * (d : ℝ) * R i) ^ 2 * N.toReal) := by
    intro i hRi
    set ω : ℝ := K * (d : ℝ) * R i with hωdef
    have hω : 0 ≤ ω := by
      rw [hωdef]; exact mul_nonneg (mul_nonneg hKnn (Nat.cast_nonneg d)) (hRpos i)
    -- measurable representatives of ρ i and u
    set ρ' : (Fin d → ℂ) → ℝ := (hρi i).aestronglyMeasurable.mk with hρ'def
    set u' : (Fin d → ℂ) → (Fin d → ℂ) := hu.aestronglyMeasurable.mk with hu'def
    have hρ'_meas : Measurable ρ' := by
      rw [hρ'def]; exact (hρi i).aestronglyMeasurable.measurable_mk
    have hu'_meas : Measurable u' := by
      rw [hu'def]; exact hu.aestronglyMeasurable.measurable_mk
    have hρ'_ae : ρ i =ᵐ[(volume : Measure (Fin d → ℂ))] ρ' := by
      rw [hρ'def]; exact (hρi i).aestronglyMeasurable.ae_eq_mk
    have hu'_ae : u =ᵐ[(volume : Measure (Fin d → ℂ))] u' := by
      rw [hu'def]; exact hu.aestronglyMeasurable.ae_eq_mk
    have hρe'_meas : Measurable (fun y => ENNReal.ofReal (ρ' y)) := hρ'_meas.ennreal_ofReal
    have hg'_meas : Measurable (fun z => ENNReal.ofReal (‖u' z‖ ^ 2)) :=
      ((hu'_meas.norm).pow_const 2).ennreal_ofReal
    have hρe_ae : (fun y => ENNReal.ofReal (ρ i y)) =ᵐ[(volume : Measure (Fin d → ℂ))]
        (fun y => ENNReal.ofReal (ρ' y)) := hρ'_ae.fun_comp ENNReal.ofReal
    have hnorm_ae : (fun z => ‖u z‖) =ᵐ[(volume : Measure (Fin d → ℂ))] (fun z => ‖u' z‖) :=
      hu'_ae.fun_comp (fun z => ‖z‖)
    have hsq_ae : (fun z => ‖u z‖ ^ 2) =ᵐ[(volume : Measure (Fin d → ℂ))]
        (fun z => ‖u' z‖ ^ 2) := by
      filter_upwards [hnorm_ae.mul hnorm_ae] with z hz
      simpa [pow_two] using hz
    have hg_ae : (fun z => ENNReal.ofReal (‖u z‖ ^ 2)) =ᵐ[(volume : Measure (Fin d → ℂ))]
        (fun z => ENNReal.ofReal (‖u' z‖ ^ 2)) := hsq_ae.fun_comp ENNReal.ofReal
    have huncurry : Measurable (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
        ENNReal.ofReal (ρ' p.2) * ENNReal.ofReal (‖u' (p.1 - p.2)‖ ^ 2)) :=
      (hρe'_meas.comp measurable_snd).mul (hg'_meas.comp (measurable_fst.sub measurable_snd))
    have hton : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ)) ∂(volume : Measure (Fin d → ℂ))
        = (∫⁻ y, ENNReal.ofReal (ρ' y) ∂(volume : Measure (Fin d → ℂ))) *
          ∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)) := by
      calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
            ∂(volume : Measure (Fin d → ℂ)) ∂(volume : Measure (Fin d → ℂ))
          = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
            ∂(volume : Measure (Fin d → ℂ)) ∂(volume : Measure (Fin d → ℂ)) :=
            lintegral_lintegral_swap huncurry.aemeasurable
        _ = ∫⁻ y, ENNReal.ofReal (ρ' y) *
              (∫⁻ x, ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)))
            ∂(volume : Measure (Fin d → ℂ)) := by
            refine lintegral_congr (fun y => ?_)
            exact lintegral_const_mul _ (hg'_meas.comp (measurable_id.sub measurable_const))
        _ = ∫⁻ y, ENNReal.ofReal (ρ' y) *
              (∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)))
            ∂(volume : Measure (Fin d → ℂ)) := by
            refine lintegral_congr (fun y => ?_)
            congr 1
            rw [show (fun x : Fin d → ℂ => ENNReal.ofReal (‖u' (x - y)‖ ^ 2))
                  = (fun x => ENNReal.ofReal (‖u' (x + (-y))‖ ^ 2)) by
                  funext x; rw [sub_eq_add_neg]]
            exact lintegral_add_right_eq_self
              (fun x : Fin d → ℂ => ENNReal.ofReal (‖u' x‖ ^ 2)) (-y)
        _ = (∫⁻ y, ENNReal.ofReal (ρ' y) ∂(volume : Measure (Fin d → ℂ))) *
            ∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)) := by
            rw [lintegral_mul_const _ hρe'_meas]
    have hG_eq_pt : ∀ x, (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ)))
        = ∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ)) := by
      intro x
      refine lintegral_congr_ae ?_
      filter_upwards [hρe_ae, ae_eq_comp_sub_left_vec hg_ae x] with y hy1 hy2
      rw [hy1, hy2]
    have hG_eq : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ))) ∂(volume : Measure (Fin d → ℂ))
        = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ))) ∂(volume : Measure (Fin d → ℂ)) :=
      lintegral_congr hG_eq_pt
    have hρe_int : (∫⁻ y, ENNReal.ofReal (ρ i y) ∂(volume : Measure (Fin d → ℂ))) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hρi i) (ae_of_all _ (hρnn i)), hρ1 i]
      simp
    have hρe'_int : (∫⁻ y, ENNReal.ofReal (ρ' y) ∂(volume : Measure (Fin d → ℂ))) = 1 := by
      rw [lintegral_congr_ae hρe_ae.symm, hρe_int]
    have hg'_int : (∫⁻ x, ENNReal.ofReal (‖u' x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)))
        = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)) := by
      rw [lintegral_congr_ae hg_ae.symm]
    have hG_eq' : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ))) ∂(volume : Measure (Fin d → ℂ)) = N := by
      rw [hG_eq, hton, hρe'_int, hg'_int, one_mul, hNdef]
    have hgu_int : Integrable (fun x : Fin d → ℂ => ‖u x‖ ^ 2) (volume : Measure (Fin d → ℂ)) :=
      hu.integrable_norm_pow (by norm_num)
    have hg_lt_top : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂(volume : Measure (Fin d → ℂ)) < ⊤ :=
      hgu_int.lintegral_lt_top
    have hG'_meas : Measurable (fun x => ∫⁻ y, ENNReal.ofReal (ρ' y) *
        ENNReal.ofReal (‖u' (x - y)‖ ^ 2) ∂(volume : Measure (Fin d → ℂ))) :=
      huncurry.lintegral_prod_right
    have hGfin : ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)),
        (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ))) < ⊤ := by
      have h1 : ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)),
          (∫⁻ y, ENNReal.ofReal (ρ' y) * ENNReal.ofReal (‖u' (x - y)‖ ^ 2)
            ∂(volume : Measure (Fin d → ℂ))) < ⊤ :=
        ae_lt_top hG'_meas (by rw [hton, hρe'_int, one_mul, hg'_int]; exact ne_of_lt hg_lt_top)
      filter_upwards [h1] with x hx
      rwa [hG_eq_pt x]
    -- ===== pointwise estimate =====
    have hpt : ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), ENNReal.ofReal
          (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
            ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
        ≤ ENNReal.ofReal (Ck * ω ^ 2) *
          (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
            ∂(volume : Measure (Fin d → ℂ))) := by
      filter_upwards [hGfin] with x hx
      by_cases hxs : x ∈ Metric.closedBall (0 : Fin d → ℂ) (M₁ + 1)
      · have hxM : ‖x‖ ≤ M₁ + 1 := by
          rw [Metric.mem_closedBall, dist_zero_right] at hxs; exact hxs
        -- oscillation bound
        have hosc : ∀ y, ρ i y ≠ 0 →
            ‖(∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖ ≤ ω * ‖u (x - y)‖ := by
          intro y hρy
          have hyR : ‖y‖ ≤ R i := by
            by_contra hcon
            exact hρy (hRs i y (lt_of_not_ge hcon))
          have hy1 : ‖y‖ ≤ 1 := le_trans hyR hRi
          have hb1 : ‖(∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖
              ≤ ∑ j, ‖g j (x - y) - g j x‖ * ‖(u (x - y)) j‖ := by
            refine (norm_sum_le Finset.univ
              (fun j => (g j (x - y) - g j x) * (u (x - y)) j)).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl (fun j _ => norm_mul _ _)
          have hb2 : ∑ j, ‖g j (x - y) - g j x‖ * ‖(u (x - y)) j‖
              ≤ ∑ j, (K * ‖y‖) * ‖(u (x - y)) j‖ := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact mul_le_mul_of_nonneg_right (hKj j x y hxM hy1) (norm_nonneg _)
          have hb3 : ∑ j, (K * ‖y‖) * ‖(u (x - y)) j‖
              ≤ (K * ‖y‖) * ((d : ℝ) * ‖u (x - y)‖) := by
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKnn (norm_nonneg _))
            calc ∑ j : Fin d, ‖(u (x - y)) j‖ ≤ ∑ _j : Fin d, ‖u (x - y)‖ :=
                  Finset.sum_le_sum (fun j _ => norm_le_pi_norm _ j)
              _ = (d : ℝ) * ‖u (x - y)‖ := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          calc ‖(∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖
              ≤ ∑ j, ‖g j (x - y) - g j x‖ * ‖(u (x - y)) j‖ := hb1
            _ ≤ ∑ j, (K * ‖y‖) * ‖(u (x - y)) j‖ := hb2
            _ ≤ (K * ‖y‖) * ((d : ℝ) * ‖u (x - y)‖) := hb3
            _ = K * (d : ℝ) * ‖y‖ * ‖u (x - y)‖ := by ring
            _ ≤ K * (d : ℝ) * R i * ‖u (x - y)‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hyR (mul_nonneg hKnn (Nat.cast_nonneg d))
            _ = ω * ‖u (x - y)‖ := by rw [hωdef]
        set Ax : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal ‖u (x - y)‖
          ∂(volume : Measure (Fin d → ℂ)) with hAxdef
        set Gx : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
          ∂(volume : Measure (Fin d → ℂ)) with hGxdef
        have hx' : Gx < ⊤ := by rw [hGxdef]; exact hx
        have hf_aem : AEMeasurable (fun y => ENNReal.ofReal (ρ i y))
            (volume : Measure (Fin d → ℂ)) :=
          (hρi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
        have hh_aem : AEMeasurable (fun y => ENNReal.ofReal ‖u (x - y)‖)
            (volume : Measure (Fin d → ℂ)) :=
          (hu.aemeasurable.norm.ennreal_ofReal).comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
        have hA_aem : AEMeasurable
            (fun y => ENNReal.ofReal (ρ i y) * ENNReal.ofReal ‖u (x - y)‖)
            (volume : Measure (Fin d → ℂ)) := hf_aem.mul hh_aem
        have hCS : Ax ^ 2 ≤ Gx := by
          have h := sq_lintegral_mul_le_mul_lintegral_mul_sq hf_aem hh_aem
          have hfac : (fun y => ENNReal.ofReal (ρ i y) * (ENNReal.ofReal ‖u (x - y)‖) ^ 2)
              = (fun y => ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)) := by
            funext y; rw [ENNReal.ofReal_pow (norm_nonneg _)]
          rw [hfac, hρe_int, one_mul, ← hAxdef, ← hGxdef] at h
          exact h
        have hL_le_B : (∫⁻ y, ENNReal.ofReal
              ‖ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖
              ∂(volume : Measure (Fin d → ℂ)))
            ≤ ∫⁻ y, ENNReal.ofReal (ρ i y * ω * ‖u (x - y)‖)
              ∂(volume : Measure (Fin d → ℂ)) := by
          refine lintegral_mono (fun y => ?_)
          refine ENNReal.ofReal_le_ofReal ?_
          by_cases hρy : ρ i y = 0
          · rw [hρy, zero_smul, norm_zero]
            positivity
          · have hnorm_eq : ‖ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖
                = ρ i y * ‖(∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖ := by
              rw [norm_smul, Real.norm_of_nonneg (hρnn i y)]
            rw [hnorm_eq]
            calc ρ i y * ‖(∑ j, (g j (x - y) - g j x) * (u (x - y)) j)‖
                ≤ ρ i y * (ω * ‖u (x - y)‖) :=
                  mul_le_mul_of_nonneg_left (hosc y hρy) (hρnn i y)
              _ = ρ i y * ω * ‖u (x - y)‖ := by ring
        have hB_eq : (∫⁻ y, ENNReal.ofReal (ρ i y * ω * ‖u (x - y)‖)
            ∂(volume : Measure (Fin d → ℂ))) = ENNReal.ofReal ω * Ax := by
          have hpt2 : ∀ y, ENNReal.ofReal (ρ i y * ω * ‖u (x - y)‖)
              = ENNReal.ofReal ω * (ENNReal.ofReal (ρ i y) * ENNReal.ofReal ‖u (x - y)‖) := by
            intro y
            rw [ENNReal.ofReal_mul (mul_nonneg (hρnn i y) hω), ENNReal.ofReal_mul (hρnn i y)]
            ring
          rw [hAxdef]
          simp only [hpt2]
          rw [lintegral_const_mul'' (ENNReal.ofReal ω) hA_aem]
        have hAx_ne_top : Ax ≠ ⊤ := by
          intro h
          have h2 : Ax ^ 2 = ⊤ := by rw [h]; simp
          have htop : Gx = ⊤ := top_le_iff.mp (by rw [← h2]; exact hCS)
          exact absurd htop (ne_of_lt hx')
        have hB_ne_top : (∫⁻ y, ENNReal.ofReal (ρ i y * ω * ‖u (x - y)‖)
            ∂(volume : Measure (Fin d → ℂ))) ≠ ⊤ := by
          rw [hB_eq]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAx_ne_top
        have hnorm_le : ‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
            ∂(volume : Measure (Fin d → ℂ)))‖ ≤ ω * Ax.toReal := by
          have h1 := (norm_integral_le_lintegral_norm
            (fun y => ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j))).trans
            (ENNReal.toReal_mono hB_ne_top hL_le_B)
          rwa [hB_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal hω] at h1
        have hp : (Ax ^ 2).toReal = Ax.toReal ^ 2 := by rw [pow_two, pow_two, ENNReal.toReal_mul]
        have hkey : ‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
            ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 ≤ ω ^ 2 * Gx.toReal := by
          calc ‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
                ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2
              ≤ (ω * Ax.toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
            _ = ω ^ 2 * (Ax ^ 2).toReal := by rw [hp]; ring
            _ ≤ ω ^ 2 * Gx.toReal := by
                refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ω)
                exact ENNReal.toReal_mono (ne_of_lt hx') hCS
        have hstep : ENNReal.ofReal
              (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
                ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
            ≤ ENNReal.ofReal (Ck * ω ^ 2) * Gx := by
          calc ENNReal.ofReal
                (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
                  ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
              ≤ ENNReal.ofReal
                  (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
                    ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2) * ENNReal.ofReal (Ck) := by
                  rw [ENNReal.ofReal_mul (sq_nonneg _)]
                  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hκle_s x hxs))
            _ ≤ ENNReal.ofReal (ω ^ 2 * Gx.toReal) * ENNReal.ofReal Ck := by
                  refine mul_le_mul' (ENNReal.ofReal_le_ofReal hkey) le_rfl
            _ = ENNReal.ofReal (ω ^ 2) * ENNReal.ofReal Gx.toReal * ENNReal.ofReal Ck := by
                  rw [ENNReal.ofReal_mul (sq_nonneg ω)]
            _ ≤ ENNReal.ofReal (ω ^ 2) * Gx * ENNReal.ofReal Ck := by
                  refine mul_le_mul' (mul_le_mul' le_rfl ENNReal.ofReal_toReal_le) le_rfl
            _ = ENNReal.ofReal (ω ^ 2 * Ck) * Gx := by
                  rw [ENNReal.ofReal_mul (sq_nonneg ω)]; ring
            _ = ENNReal.ofReal (Ck * ω ^ 2) * Gx := by rw [mul_comm (ω ^ 2) Ck]
        rw [hGxdef]; exact hstep
      · -- x outside the ball: the whole integrand vanishes
        have hxM : M₁ + 1 < ‖x‖ := by
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hxs; exact hxs
        have hzero : (fun y : Fin d → ℂ =>
            ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)) = fun _ => (0 : ℂ) := by
          funext y
          by_cases hρy : ρ i y = 0
          · rw [hρy, zero_smul]
          · have hyR : ‖y‖ ≤ R i := by
              by_contra hcon
              exact hρy (hRs i y (lt_of_not_ge hcon))
            have hux : u (x - y) = 0 := by
              by_contra hne
              have h1 : ‖x - y‖ ≤ M₁ := hsupp _ hne
              have h2 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
                calc ‖x‖ = ‖(x - y) + y‖ := by ring_nf
                  _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
              have hy1 : ‖y‖ ≤ 1 := le_trans hyR hRi
              linarith
            rw [hux]; simp
        have hV0 : (∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
            ∂(volume : Measure (Fin d → ℂ))) = 0 := by
          rw [hzero]; simp
        rw [hV0]; simp
    -- ===== final assembly for this i =====
    calc ∫⁻ x, ENNReal.ofReal
          (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
            ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x) ∂(volume : Measure (Fin d → ℂ))
        ≤ ∫⁻ x, ENNReal.ofReal (Ck * ω ^ 2) *
            (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
              ∂(volume : Measure (Fin d → ℂ))) ∂(volume : Measure (Fin d → ℂ)) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (Ck * ω ^ 2) *
            ∫⁻ x, (∫⁻ y, ENNReal.ofReal (ρ i y) * ENNReal.ofReal (‖u (x - y)‖ ^ 2)
              ∂(volume : Measure (Fin d → ℂ))) ∂(volume : Measure (Fin d → ℂ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Ck * ω ^ 2) * N := by rw [hG_eq']
      _ = ENNReal.ofReal (Ck * ω ^ 2) * ENNReal.ofReal N.toReal :=
          congrArg (fun t => ENNReal.ofReal (Ck * ω ^ 2) * t)
            (ENNReal.ofReal_toReal (ne_of_lt hNlt)).symm
      _ = ENNReal.ofReal (Ck * ω ^ 2 * N.toReal) :=
          (ENNReal.ofReal_mul (mul_nonneg hCknn (sq_nonneg ω))).symm
      _ = ENNReal.ofReal (Ck * (K * (d : ℝ) * R i) ^ 2 * N.toReal) := by
          congr 1
  -- ===== Step 6: conclude =====
  have hRle1 : ∀ᶠ i in l, R i ≤ 1 :=
    hR.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have hev : ∀ᶠ i in l, (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • (∑ j, (g j (x - y) - g j x) * (u (x - y)) j)
          ∂(volume : Measure (Fin d → ℂ)))‖ ^ 2 * κ x)
        ∂(volume : Measure (Fin d → ℂ)))
      ≤ ENNReal.ofReal (Ck * (K * (d : ℝ)) ^ 2 * N.toReal * (R i) ^ 2) := by
    filter_upwards [hRle1] with i hi
    refine (key i hi).trans (le_of_eq ?_)
    congr 1
    ring
  have hcont : Continuous fun r : ℝ => Ck * (K * (d : ℝ)) ^ 2 * N.toReal * r ^ 2 := by
    continuity
  have h1 : Filter.Tendsto (fun i => Ck * (K * (d : ℝ)) ^ 2 * N.toReal * (R i) ^ 2) l (nhds 0) := by
    have h := hcont.continuousAt.tendsto.comp hR
    rw [Function.comp_def] at h
    have h0 : Ck * (K * (d : ℝ)) ^ 2 * N.toReal * (0 : ℝ) ^ 2 = 0 := by ring
    rw [h0] at h
    exact h
  have hg2 : Filter.Tendsto
      (fun i => ENNReal.ofReal (Ck * (K * (d : ℝ)) ^ 2 * N.toReal * (R i) ^ 2)) l (nhds 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [Function.comp_def, ENNReal.ofReal_zero] at h
    exact h
  rw [ENNReal.tendsto_nhds_zero] at hg2 ⊢
  intro ε hε
  filter_upwards [hev, hg2 ε hε] with i h2 h3
  exact le_trans h2 h3

end Commons.Analysis.Convolution