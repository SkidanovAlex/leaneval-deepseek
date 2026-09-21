import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Abel.continuousOn_abel_K
import Submission.Commons.Analysis.Abel.volterra_double_integral
import Submission.Commons.Analysis.Abel.volterra_integral_hasDerivAt

noncomputable section

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Commons.Analysis.Abel

set_option linter.unusedVariables false

lemma hasDerivAt_Q_affine_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b x t : ℝ} {Q : ℝ → E}
    (hQ_cont : ContDiffOn ℝ 2 Q (Set.Icc a b))
    (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun y : ℝ => Q (y + (b - y) * t^2))
      ((1 - t^2) • deriv Q (x + (b - x) * t^2)) x := by
  let p : ℝ := x + (b - x) * t^2
  have hp_mem : p ∈ Set.Ioo a b := by
    constructor
    · have hp_gt_x : x ≤ p := by
        dsimp [p]
        have hnonneg : 0 ≤ (b - x) * t^2 := mul_nonneg (sub_nonneg.mpr (le_of_lt hx.2)) (sq_nonneg t)
        linarith
      exact lt_of_lt_of_le hx.1 hp_gt_x
    · have ht2_lt1 : t^2 < 1 := by
        have ht0 : 0 < t := ht.1
        have ht1 : t < 1 := ht.2
        nlinarith
      have hpos : 0 < b - x := sub_pos.mpr hx.2
      have hmul_lt : (b - x) * t^2 < b - x := by
        simpa [mul_comm] using mul_lt_mul_of_pos_left ht2_lt1 hpos
      dsimp [p]
      linarith
  have h_open : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h_nhds : Set.Ioo a b ∈ 𝓝 p := h_open.mem_nhds hp_mem
  have h_sub : Set.Ioo a b ⊆ Set.Icc a b := by
    intro y hy; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hS_nhds : Set.Icc a b ∈ 𝓝 p := mem_of_superset h_nhds h_sub
  have hQdiff : DifferentiableAt ℝ Q p := by
    have hcont := hQ_cont.contDiffAt (s := Set.Icc a b) hS_nhds
    exact hcont.differentiableAt (by norm_num)
  have hγ : HasDerivAt (fun y : ℝ => y + (b - y) * t^2) (1 - t^2) x := by
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hlin : HasDerivAt (fun y : ℝ => b - y) (-1) x := (hasDerivAt_id x).const_sub b
    have hmul0 : HasDerivAt (fun y : ℝ => t^2 * (b - y)) (t^2 * -1) x := hlin.const_mul (t^2)
    have hmul : HasDerivAt (fun y : ℝ => t^2 * (b - y)) (-(t^2)) x := by
      exact hmul0.congr_deriv (by ring)
    have hmul' : HasDerivAt (fun y : ℝ => (b - y) * t^2) (-(t^2)) x := by
      simpa [mul_comm] using hmul
    have hsum := h1.add hmul'
    have hderiv : 1 + -(t^2) = 1 - t^2 := by ring
    exact hsum.congr_deriv hderiv
  have hcomp := HasDerivAt.scomp (x := x) hQdiff.hasDerivAt hγ
  have hfun : (fun y : ℝ => Q (y + (b - y) * t^2)) = Q ∘ (fun y : ℝ => y + (b - y) * t^2) := by rfl
  simpa [p, hfun] using hcomp

lemma mem_Ioo_of_convex_sq {a b s u : ℝ} (hs : s ∈ Set.Ioo a b) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    s + (b - s) * u ∈ Set.Ioo a b := by
  constructor
  · have hnonneg : 0 ≤ (b - s) * u := mul_nonneg (sub_nonneg.mpr (le_of_lt hs.2)) hu0
    have hs_le : s ≤ s + (b - s) * u := by linarith
    exact lt_of_lt_of_le hs.1 hs_le
  · have hpos : 0 < b - s := sub_pos.mpr hs.2
    have hmul_lt : (b - s) * u < b - s := by
      simpa [mul_comm] using mul_lt_mul_of_pos_left hu1 hpos
    linarith

lemma differentiableAt_intervalIntegral_invSqrt_Q
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b s : ℝ} (hab : a < b)
    {Q : ℝ → E}
    (hQ_cont : ContDiffOn ℝ 2 Q (Set.Icc a b))
    (hQb : Q b = 0)
    (hs : s ∈ Set.Ioo a b) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) s := by
  let R : ℝ → E := fun x => ∫ t in (0:ℝ)..(1:ℝ), Q (x + (b - x) * t^2)
  let φ : ℝ → E := fun x => (2 * Real.sqrt (b - x)) • R x
  have hsubst : ∀ x ∈ Set.Ioo a b,
      (fun u => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) x = φ x := by
    intro x hx
    have hxb : x ≤ b := le_of_lt hx.2
    have h := intervalIntegral_abel_subst (E := E) hxb (fun _ σ => Q σ)
    simpa [φ, R] using h
  have hφ_diff : DifferentiableAt ℝ φ s := by
    have hscalar : DifferentiableAt ℝ (fun x : ℝ => 2 * Real.sqrt (b - x)) s := by
      have hlin : HasDerivAt (fun x : ℝ => b - x) (-1) s := (hasDerivAt_id s).const_sub b
      have hsqrt_arg_pos : 0 < b - s := sub_pos.mpr hs.2
      have hsqrt_ne : b - s ≠ 0 := ne_of_gt hsqrt_arg_pos
      have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (b - s))) (b - s) :=
        Real.hasDerivAt_sqrt hsqrt_ne
      have hcomp := HasDerivAt.scomp (x := s) hsqrt hlin
      have hscalar' : HasDerivAt (fun x : ℝ => 2 * Real.sqrt (b - x))
          (2 * ((-1) * (1 / (2 * Real.sqrt (b - s))))) s := by
        simpa [mul_assoc] using hcomp.const_mul 2
      exact hscalar'.differentiableAt
    have hR_diff : DifferentiableAt ℝ R s := by
      let F : ℝ → ℝ → E := fun x t => Q (x + (b - x) * t^2)
      let F' : ℝ → E := fun t => (1 - t^2) • derivWithin Q (Set.Icc a b) (s + (b - s) * t^2)
      let δ : ℝ := min (s - a) (b - s) / 2
      have hδpos : 0 < δ := by
        dsimp [δ]
        exact half_pos (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))
      let U : Set ℝ := Metric.ball s δ
      have hU_nhds : U ∈ 𝓝 s := by dsimp [U]; exact Metric.ball_mem_nhds s hδpos
      have hU_mem : ∀ x ∈ U, x ∈ Set.Ioo a b := by
        intro x hx
        have hdist : |x - s| < δ := by
          simpa [U, Metric.mem_ball, dist_eq_norm, Real.dist_eq] using hx
        have hδ_lt_sa : δ < s - a := by
          dsimp [δ]
          exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_left _ _)
        have hδ_lt_bs : δ < b - s := by
          dsimp [δ]
          exact lt_of_lt_of_le (half_lt_self (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2))) (min_le_right _ _)
        have h1 : |x - s| < s - a := lt_trans hdist hδ_lt_sa
        have h2 : |x - s| < b - s := lt_trans hdist hδ_lt_bs
        constructor
        · have h' : -(s - a) < x - s ∧ x - s < s - a := abs_lt.mp h1
          linarith
        · have h' : -(b - s) < x - s ∧ x - s < b - s := abs_lt.mp h2
          linarith
      have hQ_contOn : ContinuousOn Q (Set.Icc a b) := hQ_cont.continuousOn
      have hQ_unique : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
      have hderivWithin_cont : ContinuousOn (fun x => derivWithin Q (Set.Icc a b) x) (Set.Icc a b) := by
        have h := hQ_cont.derivWithin hQ_unique (by norm_num : (0:WithTop ℕ∞) + 1 ≤ 2)
        exact h.continuousOn
      obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hderivWithin_cont.norm
      let Cq : ℝ := max C0 0
      have hCq_nonneg : 0 ≤ Cq := by dsimp [Cq]; exact le_max_right _ _
      have hCq_bound : ∀ x ∈ Set.Icc a b, ‖derivWithin Q (Set.Icc a b) x‖ ≤ Cq := by
        intro x hx
        exact le_trans (by simpa using hC0 x hx) (by dsimp [Cq]; exact le_max_left _ _)
      have hderiv_bound : ∀ x ∈ Set.Ioo a b, ‖deriv Q x‖ ≤ Cq := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
        have hsub : Set.Ioo a b ⊆ Set.Icc a b := by
          intro y hy; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
        have hWithin : derivWithin Q (Set.Icc a b) x = deriv Q x := by
          exact derivWithin_of_mem_nhds (mem_of_superset (isOpen_Ioo.mem_nhds hx) hsub)
        simpa [hWithin] using hCq_bound x hxIcc
      let Cqnn : NNReal := Real.toNNReal Cq
      have hCqnn_coe : (Cqnn : ℝ) = Cq := Real.coe_toNNReal Cq hCq_nonneg
      have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (F x) (volume.restrict (Ι (0:ℝ) 1)) := by
        filter_upwards [hU_nhds] with x hx
        have hx' := hU_mem x hx
        have hcont : ContinuousOn (fun t : ℝ => Q (x + (b - x) * t^2)) (Set.uIcc (0:ℝ) 1) := by
          have hpath_cont : ContinuousOn (fun t : ℝ => x + (b - x) * t^2) (Set.uIcc (0:ℝ) 1) := by
            fun_prop
          have hpath_mem : Set.MapsTo (fun t : ℝ => x + (b - x) * t^2) (Set.uIcc (0:ℝ) 1)
              (Set.Icc a b) := by
            intro t ht
            have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
              simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
            have ht_sq_mem : t^2 ∈ Set.Icc (0:ℝ) 1 := by
              constructor
              · exact sq_nonneg t
              · have ht0 : 0 ≤ t := ht'.1
                have ht1 : t ≤ 1 := ht'.2
                nlinarith
            have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
            have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
            have hbIcc : b ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hx'.1 hx'.2), le_rfl⟩
            have hmem := hconv.add_smul_sub_mem hxIcc hbIcc ht_sq_mem
            simpa [Algebra.smul_def, smul_eq_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmem
          exact hQ_contOn.comp' hpath_cont hpath_mem
        have hAE := hcont.aestronglyMeasurable_of_subset_isCompact (μ := volume) isCompact_uIcc measurableSet_uIoc
          Set.uIoc_subset_uIcc
        simpa [F] using hAE
      have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
        have hcont : ContinuousOn (fun t : ℝ => Q (s + (b - s) * t^2)) (Set.uIcc (0:ℝ) 1) := by
          have hpath_cont : ContinuousOn (fun t : ℝ => s + (b - s) * t^2) (Set.uIcc (0:ℝ) 1) := by
            fun_prop
          have hpath_mem : Set.MapsTo (fun t : ℝ => s + (b - s) * t^2) (Set.uIcc (0:ℝ) 1)
              (Set.Icc a b) := by
            intro t ht
            have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
              simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
            have ht_sq_mem : t^2 ∈ Set.Icc (0:ℝ) 1 := by
              constructor
              · exact sq_nonneg t
              · have ht0 : 0 ≤ t := ht'.1
                have ht1 : t ≤ 1 := ht'.2
                nlinarith
            have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
            have hsIcc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
            have hbIcc : b ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hs.1 hs.2), le_rfl⟩
            have hmem := hconv.add_smul_sub_mem hsIcc hbIcc ht_sq_mem
            simpa [Algebra.smul_def, smul_eq_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmem
          exact hQ_contOn.comp' hpath_cont hpath_mem
        exact hcont.intervalIntegrable
      have hF'_meas : AEStronglyMeasurable F' (volume.restrict (Ι (0:ℝ) 1)) := by
        have hcont : ContinuousOn
            (fun t : ℝ => (1 - t^2) • derivWithin Q (Set.Icc a b) (s + (b - s) * t^2)) (Set.uIcc (0:ℝ) 1) := by
          have hscalar_cont : ContinuousOn (fun t : ℝ => 1 - t^2) (Set.uIcc (0:ℝ) 1) := by fun_prop
          have hpath_cont : ContinuousOn (fun t : ℝ => s + (b - s) * t^2) (Set.uIcc (0:ℝ) 1) := by
            fun_prop
          have hpath_mem : Set.MapsTo (fun t : ℝ => s + (b - s) * t^2) (Set.uIcc (0:ℝ) 1)
              (Set.Icc a b) := by
            intro t ht
            have ht' : t ∈ Set.Icc (0:ℝ) 1 := by
              simpa [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
            have ht_sq_mem : t^2 ∈ Set.Icc (0:ℝ) 1 := by
              constructor
              · exact sq_nonneg t
              · have ht0 : 0 ≤ t := ht'.1
                have ht1 : t ≤ 1 := ht'.2
                nlinarith
            have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
            have hsIcc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
            have hbIcc : b ∈ Set.Icc a b := ⟨le_of_lt (lt_trans hs.1 hs.2), le_rfl⟩
            have hmem := hconv.add_smul_sub_mem hsIcc hbIcc ht_sq_mem
            simpa [Algebra.smul_def, smul_eq_mul, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmem
          exact hscalar_cont.smul (hderivWithin_cont.comp' hpath_cont hpath_mem)
        have hAE := hcont.aestronglyMeasurable_of_subset_isCompact (μ := volume) isCompact_uIcc measurableSet_uIoc
          Set.uIoc_subset_uIcc
        simpa [F'] using hAE
      have h_bound_lip : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 →
          LipschitzOnWith Cqnn (fun x => F x t) U := by
        filter_upwards with t ht
        have ht' : t ∈ Set.Ioc (0:ℝ) 1 := by
          simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
        by_cases ht1 : t = 1
        · subst t
          have hconst : (fun x => F x 1) = fun _ => Q b := by
            funext x; simp [F]
          have hlip : LipschitzOnWith Cqnn (fun x => F x 1) U := by
            rw [hconst]
            intro x hx y hy
            simp
          exact hlip
        · have ht_oo : t ∈ Set.Ioo (0:ℝ) 1 := ⟨ht'.1, lt_of_le_of_ne ht'.2 ht1⟩
          have hder : ∀ x ∈ U, HasDerivAt (fun x => F x t) ((1 - t^2) • deriv Q (x + (b - x) * t^2)) x := by
            intro x hx
            have hx' := hU_mem x hx
            exact hasDerivAt_Q_affine_sq (E := E) hQ_cont hx' ht_oo
          have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (fun x => F x t) x := by
            intro x hx; exact (hder x hx).differentiableAt
          have hbound : ∀ x ∈ U, ‖deriv (fun x => F x t) x‖₊ ≤ Cqnn := by
            intro x hx
            have hd := hder x hx
            have hx' := hU_mem x hx
            have hp_mem : x + (b - x) * t^2 ∈ Set.Ioo a b := by
              exact mem_Ioo_of_convex_sq hx' (sq_nonneg t) (by
                have ht0 : 0 < t := ht_oo.1
                have ht1 : t < 1 := ht_oo.2
                nlinarith)
            have hderiv_val := hd.deriv
            have hnorm_real : ‖deriv (fun x => F x t) x‖ ≤ Cq := by
              rw [hderiv_val]
              have hnorm : ‖(1 - t^2) • deriv Q (x + (b - x) * t^2)‖ ≤ Cq := by
                calc
                  ‖(1 - t^2) • deriv Q (x + (b - x) * t^2)‖
                      = |1 - t^2| * ‖deriv Q (x + (b - x) * t^2)‖ := norm_smul _ _
                  _ ≤ 1 * Cq := by
                    apply mul_le_mul
                    · have ht0 : 0 < t := ht_oo.1
                      have ht1 : t < 1 := ht_oo.2
                      have hsq : 0 ≤ t^2 := sq_nonneg t
                      rw [abs_of_nonneg (sub_nonneg.mpr (by nlinarith))]
                      nlinarith
                    · exact hderiv_bound _ hp_mem
                    · exact norm_nonneg _
                    · exact zero_le_one
                  _ = Cq := one_mul Cq
              exact hnorm
            have hnorm_nn : ‖deriv (fun x => F x t) x‖₊ ≤ Cqnn := by
              rw [← NNReal.coe_le_coe]
              simp [coe_nnnorm, hCqnn_coe]
              exact hnorm_real
            exact hnorm_nn
          have hconvexU : Convex ℝ U := by simpa [U] using convex_ball s δ
          exact hconvexU.lipschitzOnWith_of_nnnorm_deriv_le hdiff hbound
      have h_lip_dom : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 →
          LipschitzOnWith (Real.nnabs ((Cqnn : ℝ))) (fun x => F x t) U := by
        filter_upwards [h_bound_lip] with t ht hmem
        have h1 : LipschitzOnWith Cqnn (fun x => F x t) U := ht hmem
        have hnn : Real.nnabs (Cqnn : ℝ) = Cqnn := by
          rw [Real.nnabs_of_nonneg (show 0 ≤ (Cqnn : ℝ) by exact_mod_cast Cqnn.property)]
          exact Real.toNNReal_coe
        simpa [hnn] using h1
      have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → HasDerivAt (fun x => F x t) (F' t) s := by
        filter_upwards with t ht
        have ht' : t ∈ Set.Ioc (0:ℝ) 1 := by
          simpa [Set.uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
        by_cases ht1 : t = 1
        · subst t
          have hconst : (fun x => F x 1) = fun _ => Q b := by funext x; simp [F]
          have hder : HasDerivAt (fun x => F x 1) (F' 1) s := by
            rw [hconst]
            simp [F']
            exact hasDerivAt_const s (Q b)
          simpa using hder
        · have ht_oo : t ∈ Set.Ioo (0:ℝ) 1 := ⟨ht'.1, lt_of_le_of_ne ht'.2 ht1⟩
          have hd := hasDerivAt_Q_affine_sq (E := E) hQ_cont hs ht_oo
          have hp_mem : s + (b - s) * t^2 ∈ Set.Ioo a b := by
            exact mem_Ioo_of_convex_sq hs (sq_nonneg t) (by
              have ht0 : 0 < t := ht_oo.1
              have ht1 : t < 1 := ht_oo.2
              nlinarith)
          have hwithin : derivWithin Q (Set.Icc a b) (s + (b - s) * t^2) = deriv Q (s + (b - s) * t^2) := by
            have hsub : Set.Ioo a b ⊆ Set.Icc a b := by
              intro y hy; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
            exact derivWithin_of_mem_nhds (mem_of_superset (isOpen_Ioo.mem_nhds hp_mem) hsub)
          have hF'eq : F' t = (1 - t^2) • deriv Q (s + (b - s) * t^2) := by
            dsimp [F']; rw [hwithin]
          simpa [F, hF'eq] using hd
      have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
        (𝕜 := ℝ) (μ := volume) (E := E) (a := (0:ℝ)) (b := (1:ℝ))
        (F := F) (F' := F') (x₀ := s) (s := U) (bound := fun _ => (Cqnn : ℝ))
        hU_nhds hF_meas hF_int hF'_meas h_lip_dom
        (by simpa using intervalIntegrable_const) h_diff
      exact hdom.2.differentiableAt
    exact hscalar.smul hR_diff
  have hevent : (fun u => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) =ᶠ[𝓝 s] φ := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx using hsubst x hx
  exact hφ_diff.congr_of_eventuallyEq hevent

lemma abel_transform_injective_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {f g : ℝ → E}
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ s ∈ Set.Ioo a b,
      (∫ x in s..b, (Real.sqrt (x - s))⁻¹ • f x) =
      (∫ x in s..b, (Real.sqrt (x - s))⁻¹ • g x)) :
    ∀ x ∈ Set.Ioo a b, f x = g x := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let I : ℝ := ∫ τ in (0:ℝ)..(1:ℝ), w τ
  have hKf_cont : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Set.Icc a b ×ˢ Set.Icc a b) := by
    exact hf.comp continuous_snd.continuousOn (by intro p hp; exact hp.2)
  have hKg_cont : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Set.Icc a b ×ˢ Set.Icc a b) := by
    exact hg.comp continuous_snd.continuousOn (by intro p hp; exact hp.2)
  intro x hx
  -- use s=x in the integral equality after applying double Abel
  let F : ℝ → E := fun s => ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • f v
  let G : ℝ → E := fun s => ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • g v
  have hFG : ∀ s ∈ Set.Ioo a b, F s = G s := by
    intro s hs
    exact h s hs
  have hbeta_f : ∀ s ∈ Set.Ioo a b,
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • F v = I • (∫ v in s..b, f v) := by
    intro s hs
    -- Use volterra_double_integral with K := fun p => f p.2
    have hvol := volterra_double_integral (E := E) hab (K := fun _ σ => f σ) (by simpa using hKf_cont) s hs
    -- hvol : ∫ σ in s..b, ∫ τ in 0..1, w τ • f σ = ∫ v in s..b, (√(v-s))⁻¹ • ∫ σ in v..b, (√(σ-v))⁻¹ • f σ
    -- right side is ∫ v, (√(v-s))⁻¹ • F v
    have hright : (∫ v in s..b, (Real.sqrt (v - s))⁻¹ • F v) =
        ∫ v in s..b, (Real.sqrt (v - s))⁻¹ •
          (∫ σ in v..b, (Real.sqrt (σ - v))⁻¹ • f σ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
      intro v hv
      rfl
    have hleft : (∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • f σ) =
        I • (∫ v in s..b, f v) := by
      calc
        (∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • f σ)
            = ∫ σ in s..b, (∫ τ in (0:ℝ)..(1:ℝ), w τ • f σ) := rfl
        _ = ∫ σ in s..b, (∫ τ in (0:ℝ)..(1:ℝ), w τ) • f σ := by
            apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
            intro σ hσ
            simp [w]
        _ = I • (∫ σ in s..b, f σ) := by
            dsimp [I]
            rw [intervalIntegral.integral_smul]
    calc
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • F v
          = ∫ v in s..b, (Real.sqrt (v - s))⁻¹ •
              (∫ σ in v..b, (Real.sqrt (σ - v))⁻¹ • f σ) := hright
      _ = ∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • f σ := hvol.symm
      _ = I • (∫ v in s..b, f v) := hleft
  have hbeta_g : ∀ s ∈ Set.Ioo a b,
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • G v = I • (∫ v in s..b, g v) := by
    intro s hs
    have hvol := volterra_double_integral (E := E) hab (K := fun _ σ => g σ) (by simpa using hKg_cont) s hs
    have hright : (∫ v in s..b, (Real.sqrt (v - s))⁻¹ • G v) =
        ∫ v in s..b, (Real.sqrt (v - s))⁻¹ •
          (∫ σ in v..b, (Real.sqrt (σ - v))⁻¹ • g σ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
      intro v hv
      rfl
    have hleft : (∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • g σ) =
        I • (∫ v in s..b, g v) := by
      calc
        (∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • g σ)
            = ∫ σ in s..b, (∫ τ in (0:ℝ)..(1:ℝ), w τ • g σ) := rfl
        _ = ∫ σ in s..b, (∫ τ in (0:ℝ)..(1:ℝ), w τ) • g σ := by
            apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
            intro σ hσ
            simp [w]
        _ = I • (∫ σ in s..b, g σ) := by
            dsimp [I]
            rw [intervalIntegral.integral_smul]
    calc
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • G v
          = ∫ v in s..b, (Real.sqrt (v - s))⁻¹ •
              (∫ σ in v..b, (Real.sqrt (σ - v))⁻¹ • g σ) := hright
      _ = ∫ σ in s..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • g σ := hvol.symm
      _ = I • (∫ v in s..b, g v) := hleft
  have hdouble_eq : ∀ s ∈ Set.Ioo a b,
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • F v =
      ∫ v in s..b, (Real.sqrt (v - s))⁻¹ • G v := by
    intro s hs
    apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2)
    intro v hv
    have hv' : v ∈ Set.Ioo a b := ⟨lt_trans hs.1 hv.1, hv.2⟩
    exact congrArg (fun z => (Real.sqrt (v - s))⁻¹ • z) (hFG v hv')
  have hI_pos : 0 < I := by
    dsimp [I, w]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (by simpa [w] using intervalIntegrable_invSqrt_weight)
      (by intro x hx; exact inv_pos.mpr (Real.sqrt_pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2))))
      (by norm_num)
  have hI_ne : I ≠ 0 := ne_of_gt hI_pos
  have h_int_eq : ∀ s ∈ Set.Ioo a b, ∫ v in s..b, f v = ∫ v in s..b, g v := by
    intro s hs
    have hb_f := hbeta_f s hs
    have hb_g := hbeta_g s hs
    have hEq1 : I • (∫ v in s..b, f v) = I • (∫ v in s..b, g v) := by
      rw [← hb_f, ← hb_g]
      exact hdouble_eq s hs
    exact (smul_right_injective (M := E) hI_ne) hEq1
  -- Differentiate the equality of integrals at x
  have hf_int : IntervalIntegrable f volume x b := by
    have hcont : ContinuousOn f (Set.uIcc x b) := by
      have hsub : Set.uIcc x b ⊆ Set.Icc a b := by
        rw [Set.uIcc_of_le (le_of_lt hx.2)]
        intro y hy
        exact ⟨le_trans (le_of_lt hx.1) hy.1, hy.2⟩
      exact hf.mono hsub
    exact hcont.intervalIntegrable
  have hg_int : IntervalIntegrable g volume x b := by
    have hcont : ContinuousOn g (Set.uIcc x b) := by
      have hsub : Set.uIcc x b ⊆ Set.Icc a b := by
        rw [Set.uIcc_of_le (le_of_lt hx.2)]
        intro y hy
        exact ⟨le_trans (le_of_lt hx.1) hy.1, hy.2⟩
      exact hg.mono hsub
    exact hcont.intervalIntegrable
  have hf_cts : ContinuousAt f x := by
    exact hf.continuousAt (by
      apply mem_of_superset (isOpen_Ioo.mem_nhds hx)
      intro y hy
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hg_cts : ContinuousAt g x := by
    exact hg.continuousAt (by
      apply mem_of_superset (isOpen_Ioo.mem_nhds hx)
      intro y hy
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  have hf_smeas : StronglyMeasurableAtFilter f (𝓝 x) volume := by
    exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono (by intro y hy; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩)) x hx
  have hg_smeas : StronglyMeasurableAtFilter g (𝓝 x) volume := by
    exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono (by intro y hy; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩)) x hx
  have hder_f := intervalIntegral.integral_hasDerivAt_left (a := x) (b := b) (f := f) hf_int hf_smeas hf_cts
  have hder_g := intervalIntegral.integral_hasDerivAt_left (a := x) (b := b) (f := g) hg_int hg_smeas hg_cts
  have hEqFun_event : (fun y : ℝ => ∫ v in y..b, f v) =ᶠ[𝓝 x] (fun y : ℝ => ∫ v in y..b, g v) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact h_int_eq y hy
  have hder_f' := hder_f.congr_of_eventuallyEq hEqFun_event.symm
  have hneg : -f x = -g x := by
    rw [← hder_f'.deriv, hder_g.deriv]
  exact neg_injective hneg

lemma tendsto_volterra_double_integral_nhdsWithin_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E}
    (hK_cont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b)) :
    Tendsto (fun u : ℝ => ∫ σ in u..b, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) (𝓝[<] b) (𝓝 0) := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let I0 : ℝ := ∫ τ in (0:ℝ)..(1:ℝ), w τ
  have hw_int : IntervalIntegrable w volume (0:ℝ) 1 := by
    simpa [w] using intervalIntegrable_invSqrt_weight
  have hmeas_w : Measurable w := by unfold w; fun_prop
  have hw_nonneg : ∀ τ, 0 ≤ w τ := by intro τ; unfold w; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hS_compact : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hK_cont.norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc a b, ‖K p.1 p.2‖ ≤ C := by
    intro p hp
    exact le_trans (by simpa using hC0 p hp) (by dsimp [C]; exact le_max_left _ _)
  refine squeeze_zero_norm' (a := fun u => C * I0 * (b - u)) ?_ ?_
  · have hIoo_nhds : Set.Ioo a b ∈ 𝓝[<] b := by
      have hmem : Set.Iio b ∩ Set.Ioi a ∈ 𝓝[<] b :=
        inter_mem_nhdsWithin (s := Set.Iio b) (t := Set.Ioi a) (isOpen_Ioi.mem_nhds hab)
      have hset : Set.Iio b ∩ Set.Ioi a = Set.Ioo a b := by
        ext x
        constructor
        · intro hx; exact ⟨hx.2, hx.1⟩
        · intro hx; exact ⟨hx.2, hx.1⟩
      simpa [hset] using hmem
    filter_upwards [hIoo_nhds] with u hu
    have hu_Icc : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hcd_sub : Set.Icc u b ⊆ Set.Icc a b := by
      intro σ hσ; exact ⟨le_trans (le_of_lt hu.1) hσ.1, hσ.2⟩
    have hG_cont : ContinuousOn (fun σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ)
        (Set.Icc u b) := by
      have h := continuousOn_intervalIntegral_weighted_smul_affine
        (E := E) (w := w) (ρ := fun _ : ℝ => (1:ℝ)) (H := K)
        (a := a) (b := b) (v := u) (c := u) (d := b)
        hw_int hmeas_w hw_nonneg continuousOn_const
        (by intro τ hτ; simp) hK_cont hu_Icc hcd_sub
      simpa [one_smul] using h
    have hG_int : IntervalIntegrable (fun σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ) volume u b := by
      have hcont_u : ContinuousOn (fun σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ)
          (Set.uIcc u b) := by
        simpa [Set.uIcc_of_le (le_of_lt hu.2)] using hG_cont
      exact hcont_u.intervalIntegrable
    have hnorm_le : ‖∫ σ in u..b, ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ‖ ≤
        ∫ σ in u..b, ‖∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ‖ :=
      intervalIntegral.norm_integral_le_integral_norm (le_of_lt hu.2)
    have hinner_bound : ∀ σ ∈ Set.Icc u b,
        ‖∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ‖ ≤ C * I0 := by
      intro σ hσ
      have hσ_ab : σ ∈ Set.Icc a b := hcd_sub hσ
      have hle := norm_invSqrt_weighted_affine_le (E := E) hK_cont hC_nonneg hC_bound hu_Icc hσ_ab
      simpa [w, I0] using hle
    have hnorm_int : IntervalIntegrable (fun σ => ‖∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ‖) volume u b :=
      hG_int.norm
    have hconst_int : IntervalIntegrable (fun _ : ℝ => C * I0) volume u b := intervalIntegrable_const
    have hmono : (∫ σ in u..b, ‖∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ‖) ≤
        ∫ σ in u..b, C * I0 := by
      apply intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hu.2) hnorm_int hconst_int
      intro σ hσ
      have hσ_cc : σ ∈ Set.Icc u b := by
        simpa [Set.uIcc_of_le (le_of_lt hu.2)] using hσ
      exact hinner_bound σ hσ_cc
    have hconst_val : (∫ σ in u..b, C * I0) = C * I0 * (b - u) := by
      rw [intervalIntegral.integral_const]
      ring
    exact le_trans hnorm_le (le_trans hmono (by simpa [hconst_val]))
  · have htend : Tendsto (fun u : ℝ => C * I0 * (b - u)) (𝓝[<] b) (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 (b - b)) := by
        exact Tendsto.sub tendsto_const_nhds (tendsto_id.mono_left inf_le_left)
      have h1' : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 0) := by
        simpa using h1
      simpa using h1'.const_mul (C * I0)
    exact htend

lemma tendsto_intervalIntegral_invSqrt_Q_nhdsWithin_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {Q : ℝ → E}
    (hQ_cont : ContinuousOn Q (Set.Icc a b)) (hQb : Q b = 0) :
    Tendsto (fun u : ℝ => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) (𝓝[<] b) (𝓝 0) := by
  have hS_compact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨C0, hC0⟩ := hS_compact.exists_bound_of_continuousOn hQ_cont.norm
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := by dsimp [C]; exact le_max_right _ _
  have hC_bound : ∀ x ∈ Set.Icc a b, ‖Q x‖ ≤ C := by
    intro x hx
    exact le_trans (by simpa using hC0 x hx) (by dsimp [C]; exact le_max_left _ _)
  refine squeeze_zero_norm' (a := fun u => C * (2 * Real.sqrt (b - u))) ?_ ?_
  · have hIoo_nhds : Set.Ioo a b ∈ 𝓝[<] b := by
      have hmem : Set.Iio b ∩ Set.Ioi a ∈ 𝓝[<] b :=
        inter_mem_nhdsWithin (s := Set.Iio b) (t := Set.Ioi a) (isOpen_Ioi.mem_nhds hab)
      have hset : Set.Iio b ∩ Set.Ioi a = Set.Ioo a b := by
        ext x
        constructor
        · intro hx; exact ⟨hx.2, hx.1⟩
        · intro hx; exact ⟨hx.2, hx.1⟩
      simpa [hset] using hmem
    filter_upwards [hIoo_nhds] with u hu
    have hu_lt : u < b := hu.2
    have hw_int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹) volume u b := by
      simpa using intervalIntegrable_invSqrt_sub (a := u) (b := b) hu_lt
    have hQ_cont_u : ContinuousOn Q (Set.uIcc u b) := by
      have hsub : Set.uIcc u b ⊆ Set.Icc a b := by
        rw [Set.uIcc_of_le (le_of_lt hu_lt)]
        intro x hx
        exact ⟨le_trans (le_of_lt hu.1) hx.1, hx.2⟩
      exact hQ_cont.mono hsub
    have h_int : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume u b :=
      hw_int.smul_continuousOn hQ_cont_u
    have hnorm_le : ‖∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v‖ ≤
        ∫ v in u..b, ‖(Real.sqrt (v - u))⁻¹ • Q v‖ :=
      intervalIntegral.norm_integral_le_integral_norm (le_of_lt hu_lt)
    have hnorm_int : IntervalIntegrable (fun v : ℝ => ‖(Real.sqrt (v - u))⁻¹ • Q v‖) volume u b := h_int.norm
    have hbound_int : IntervalIntegrable (fun v : ℝ => C * (Real.sqrt (v - u))⁻¹) volume u b :=
      hw_int.const_mul C
    have hmono : (∫ v in u..b, ‖(Real.sqrt (v - u))⁻¹ • Q v‖) ≤
        ∫ v in u..b, C * (Real.sqrt (v - u))⁻¹ := by
      apply intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hu_lt) hnorm_int hbound_int
      intro v hv
      have hv_cc : v ∈ Set.Icc u b := by
        simpa [Set.uIcc_of_le (le_of_lt hu_lt)] using hv
      have hQv : ‖Q v‖ ≤ C := hC_bound v (by
        have hsub : Set.Icc u b ⊆ Set.Icc a b := by
          intro x hx; exact ⟨le_trans (le_of_lt hu.1) hx.1, hx.2⟩
        exact hsub hv_cc)
      have hw_nonneg : 0 ≤ (Real.sqrt (v - u))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      calc
        ‖(Real.sqrt (v - u))⁻¹ • Q v‖ = |(Real.sqrt (v - u))⁻¹| * ‖Q v‖ := norm_smul _ _
        _ = (Real.sqrt (v - u))⁻¹ * ‖Q v‖ := by rw [abs_of_nonneg hw_nonneg]
        _ ≤ (Real.sqrt (v - u))⁻¹ * C := mul_le_mul_of_nonneg_left hQv hw_nonneg
        _ = C * (Real.sqrt (v - u))⁻¹ := mul_comm _ _
    have hconst_val : (∫ v in u..b, C * (Real.sqrt (v - u))⁻¹) =
        C * (2 * Real.sqrt (b - u)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact integral_invSqrt_sub (a := u) (b := b) hu_lt
    exact le_trans hnorm_le (le_trans hmono (by simpa [hconst_val]))
  · have h1 : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 0) := by
      have h : Tendsto (fun u : ℝ => b - u) (𝓝[<] b) (𝓝 (b - b)) := by
        exact Tendsto.sub tendsto_const_nhds (tendsto_id.mono_left inf_le_left)
      simpa using h
    have hsqrt : Tendsto (fun u : ℝ => Real.sqrt (b - u)) (𝓝[<] b) (𝓝 (Real.sqrt 0)) :=
      h1.sqrt
    have hsqrt0 : Tendsto (fun u : ℝ => Real.sqrt (b - u)) (𝓝[<] b) (𝓝 0) := by
      simpa using hsqrt
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsqrt0.const_mul (C * 2)

lemma volterra_equivalence_full
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a b : ℝ} (hab : a < b)
    {K : ℝ → ℝ → E} {Q : ℝ → E}
    (hK_cont : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a b ×ˢ Set.Icc a b))
    (hQ_cont : ContDiffOn ℝ 2 Q (Set.Icc a b))
    (hQb : Q b = 0) :
    (∀ s ∈ Set.Ioo a b, (∫ σ in s..b, (Real.sqrt (σ - s))⁻¹ • K s σ) = Q s) ↔
    (∀ s ∈ Set.Ioo a b,
      - (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s) +
        (∫ σ in s..b, deriv (fun u : ℝ =>
          ∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s) =
        deriv (fun u : ℝ => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v) s) := by
  let w : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹
  let G : ℝ → ℝ → E := fun u σ => ∫ τ in (0:ℝ)..(1:ℝ), w τ • K (u + τ * (σ - u)) σ
  let H : ℝ → E := fun u => ∫ σ in u..b, G u σ
  let A : ℝ → E := fun x => ∫ σ in x..b, (Real.sqrt (σ - x))⁻¹ • K x σ
  let P : ℝ → E := fun u => ∫ v in u..b, (Real.sqrt (v - u))⁻¹ • Q v
  constructor
  · intro hEq s hs
    have hvol := volterra_integral_hasDerivAt (E := E) hab hK_cont s hs
    have hHP : ∀ x ∈ Set.Ioo a b, H x = P x := by
      intro x hx
      have hfwd := volterra_double_integral (E := E) hab hK_cont.continuousOn x hx
      calc
        H x = ∫ y in x..b, (Real.sqrt (y - x))⁻¹ •
            (∫ σ in y..b, (Real.sqrt (σ - y))⁻¹ • K y σ) := by
          simpa [H, G, w] using hfwd
        _ = ∫ y in x..b, (Real.sqrt (y - x))⁻¹ • Q y := by
          apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hx.2)
          intro y hy
          have hy' : y ∈ Set.Ioo a b := ⟨lt_trans hx.1 hy.1, hy.2⟩
          have hAQ : A y = Q y := by simpa [A] using hEq y hy'
          simpa [A] using (congrArg (fun z => (Real.sqrt (y - x))⁻¹ • z) hAQ)
        _ = P x := by simp [P]
    have hmain : H =ᶠ[𝓝 s] P := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx using hHP x hx
    have hPder : HasDerivAt P
        (- (∫ τ in (0 : ℝ)..(1 : ℝ), w τ • K s s) +
          ∫ σ in s..b, deriv (fun u : ℝ => G u σ) s) s :=
      hvol.congr_of_eventuallyEq hmain.symm
    simpa [G, w] using hPder.deriv.symm
  · intro hEq s hs
    have hHder : ∀ x ∈ Set.Ioo a b, HasDerivAt H
        ((- (∫ τ in (0 : ℝ)..(1 : ℝ), w τ • K x x)) +
          ∫ σ in x..b, deriv (fun u : ℝ => G u σ) x) x := by
      intro x hx
      simpa [H, G, w] using volterra_integral_hasDerivAt (E := E) hab hK_cont x hx
    have hPdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ P x := by
      intro x hx
      exact differentiableAt_intervalIntegral_invSqrt_Q (E := E) hab hQ_cont hQb hx
    have hder_eq : Set.EqOn (deriv H) (deriv P) (Set.Ioo a b) := by
      intro x hx
      have hHx := hHder x hx
      have hEqx := hEq x hx
      rw [hHx.deriv]
      simpa [G, w] using hEqx
    have hdiffH : DifferentiableOn ℝ H (Set.Ioo a b) := by
      intro x hx
      exact (hHder x hx).differentiableAt.differentiableWithinAt
    have hdiffP : DifferentiableOn ℝ P (Set.Ioo a b) := by
      intro x hx
      exact (hPdiff x hx).differentiableWithinAt
    obtain ⟨c, hc⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hdiffH hdiffP hder_eq
    have hHlim : Tendsto H (𝓝[<] b) (𝓝 0) := by
      simpa [H, G, w] using tendsto_volterra_double_integral_nhdsWithin_lt (E := E) hab hK_cont.continuousOn
    have hPlim : Tendsto P (𝓝[<] b) (𝓝 0) := by
      simpa [P] using tendsto_intervalIntegral_invSqrt_Q_nhdsWithin_lt (E := E) hab hQ_cont.continuousOn hQb
    have hIoo_nhds : Set.Ioo a b ∈ 𝓝[<] b := by
      have hmem : Set.Iio b ∩ Set.Ioi a ∈ 𝓝[<] b :=
        inter_mem_nhdsWithin (s := Set.Iio b) (t := Set.Ioi a) (isOpen_Ioi.mem_nhds hab)
      have hset : Set.Iio b ∩ Set.Ioi a = Set.Ioo a b := by
        ext x
        constructor
        · intro hx
          exact ⟨hx.2, hx.1⟩
        · intro hx
          exact ⟨hx.2, hx.1⟩
      simpa [hset] using hmem
    have hEq_event : H =ᶠ[𝓝[<] b] (fun x => P x + c) := by
      filter_upwards [hIoo_nhds] with x hx using hc hx
    have hPc_lim : Tendsto (fun x => P x + c) (𝓝[<] b) (𝓝 (0 + c)) :=
      hPlim.add tendsto_const_nhds
    have hHlim' : Tendsto (fun x => P x + c) (𝓝[<] b) (𝓝 0) :=
      Filter.Tendsto.congr' hEq_event hHlim
    have hc0 : 0 = 0 + c := tendsto_nhds_unique hHlim' hPc_lim
    have hc_zero : c = 0 := by simpa using hc0.symm
    have hHP : ∀ x ∈ Set.Ioo a b, H x = P x := by
      intro x hx
      have hxeq := hc hx
      rw [hxeq, hc_zero]
      simp
    have hAbel : ∀ s ∈ Set.Ioo a b,
        (∫ x in s..b, (Real.sqrt (x - s))⁻¹ • A x) =
        (∫ x in s..b, (Real.sqrt (x - s))⁻¹ • Q x) := by
      intro t ht
      have hfwd := volterra_double_integral (E := E) hab hK_cont.continuousOn t ht
      calc
        (∫ x in t..b, (Real.sqrt (x - t))⁻¹ • A x) = H t := by
          simpa [H, G, w, A] using hfwd.symm
        _ = P t := hHP t ht
        _ = ∫ x in t..b, (Real.sqrt (x - t))⁻¹ • Q x := by simp [P]
    have hA_cont : ContinuousOn A (Set.Icc a b) := by
      simpa [A] using continuousOn_abel_K (E := E) hab hK_cont
    have hQ_contOn : ContinuousOn Q (Set.Icc a b) := hQ_cont.continuousOn
    have hinj := abel_transform_injective_on (E := E) hab hA_cont hQ_contOn hAbel
    simpa [A] using hinj s hs

end Commons.Analysis.Abel