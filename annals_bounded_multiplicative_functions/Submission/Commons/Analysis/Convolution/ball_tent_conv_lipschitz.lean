import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Convolution.integrableOn_Ioi_rpow_max_one
import Submission.Commons.Analysis.Convolution.integral_Ioi_rpow_max_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Convolution

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

private lemma infDist_ball_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ℝ} (hρ : 0 < ρ) (x : E) :
    Metric.infDist x (Metric.ball (0 : E) ρ) = max 0 (‖x‖ - ρ) := by
  have hne : (Metric.ball (0 : E) ρ).Nonempty := ⟨0, by simp [hρ]⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense (fun c hc => ?_)
    have hcpos : 0 < c := lt_of_le_of_lt (le_max_left (0 : ℝ) _) hc
    refine le_of_lt ((Metric.infDist_lt_iff hne).2 ?_)
    rcases lt_or_ge ‖x‖ ρ with h | h
    · exact ⟨x, by simp [Metric.mem_ball, dist_zero_right, h], by simpa using hcpos⟩
    · have hcx : ‖x‖ - ρ < c := lt_of_le_of_lt (le_max_right _ _) hc
      have hρx : 0 < ‖x‖ := lt_of_lt_of_le hρ h
      set δ : ℝ := min (ρ / 2) ((c - (‖x‖ - ρ)) / 2) with hδ
      have hδpos : 0 < δ := by
        rw [hδ]; exact lt_min (by linarith) (by linarith)
      have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      refine ⟨((ρ - δ) / ‖x‖) • x, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hρx]
        nlinarith [hρx]
      · rw [dist_eq_norm]
        have h1 : x - ((ρ - δ) / ‖x‖) • x = (1 - (ρ - δ) / ‖x‖) • x := by
          rw [sub_smul, one_smul]
        rw [h1, norm_smul, Real.norm_eq_abs]
        have h2 : (0 : ℝ) ≤ 1 - (ρ - δ) / ‖x‖ := by
          rw [sub_nonneg, div_le_one hρx]; linarith
        rw [abs_of_nonneg h2]
        have h3 : (1 - (ρ - δ) / ‖x‖) * ‖x‖ = ‖x‖ - ρ + δ := by
          field_simp; ring
        rw [h3]
        have : δ ≤ (c - (‖x‖ - ρ)) / 2 := min_le_right _ _
        linarith
  · rw [Metric.le_infDist hne]
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have h1 : ‖x‖ - ρ ≤ dist x y := by
      have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      rw [dist_eq_norm]; linarith
    exact max_le dist_nonneg h1

private lemma one_add_max_zero_sub_one (t : ℝ) : 1 + max 0 (t - 1) = max 1 t := by
  by_cases h : 1 ≤ t
  · rw [max_eq_right (by linarith : 0 ≤ t - 1), max_eq_right h]; ring
  · rw [max_eq_left (by linarith : t - 1 ≤ 0), add_zero, max_eq_left (by linarith)]

private lemma max_zero_div (a b : ℝ) (hb : 0 < b) : max 0 a / b = max 0 (a/b) := by
  rw [← max_div_div_right hb.le (0:ℝ) a, zero_div]

private lemma max_zero_sub_div (a : ℝ) {b : ℝ} (hb : 0 < b) :
    max 0 (a - b)/b = max 0 (a/b - 1) := by
  rw [max_zero_div _ _ hb, show (a - b)/b = a/b - 1 by rw [sub_div, div_self hb.ne']]

private lemma norm_inv_smul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (w : E) : ‖R⁻¹ • w‖ = ‖w‖ / R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), inv_mul_eq_div]

private lemma half_div_rpow_neg (t A : ℝ) (ht : 0 < t) :
    (t / 2) ^ (-A) = 2 ^ A * t ^ (-A) := by
  have h2 : (2 : ℝ)⁻¹ ^ (-A) = 2 ^ A := by
    rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [show t / 2 = t * (2 : ℝ)⁻¹ by ring,
    Real.mul_rpow ht.le (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹), h2]
  ring

private lemma tail_bound (n : ℕ) (hn : 1 ≤ n) (A' : ℝ) (hA' : (n:ℝ) < A') {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Set.Ioi ρ, t^(n-1) * (max 1 t)^(-A') ≤ ρ ^ ((n:ℝ) - A') / (A' - (n:ℝ)) := by
  set a : ℝ := (n:ℝ) - 1 - A' with hadef
  have ha : a < -1 := by rw [hadef]; linarith
  have hintg : IntegrableOn (fun t : ℝ => t ^ a) (Set.Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt ha hρ
  have hval : ∫ t in Set.Ioi ρ, t ^ a = ρ ^ ((n:ℝ) - A') / (A' - (n:ℝ)) := by
    rw [integral_Ioi_rpow_of_lt ha hρ]
    have hb : a + 1 = -((A' - (n:ℝ))) := by rw [hadef]; ring
    rw [hb, neg_div_neg_eq]
    rw [show -((A' - (n:ℝ))) = (n:ℝ) - A' by ring]
  rw [← hval]
  refine setIntegral_mono_of_nonneg ?_ ?_ hintg
  · intro t ht
    exact mul_nonneg (pow_nonneg (le_of_lt (lt_trans hρ ht)) _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  · intro t ht
    have ht0 : 0 < t := lt_trans hρ ht
    have hle : (max 1 t) ^ (-A') ≤ t ^ (-A') :=
      Real.rpow_le_rpow_of_nonpos ht0 (le_max_right 1 t) (by linarith)
    calc t^(n-1) * (max 1 t)^(-A') ≤ t^(n-1) * t^(-A') :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg ht0.le _)
      _ = t^a := by
          rw [← Real.rpow_natCast t (n-1), ← Real.rpow_add ht0]
          congr 1
          rw [hadef, Nat.cast_sub hn]; ring

private lemma one_dim_bound (n : ℕ) (hn : 1 ≤ n) (A A' : ℝ) (hA : 0 < A)
    (hA' : A + (n : ℝ) < A')
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (hmass : ∫ t in Set.Ioi (0:ℝ), t ^ (n-1) * (max 1 t) ^ (-A') = 1/(n:ℝ) + 1/(A' - (n:ℝ)))
    (htail : ∀ ρ : ℝ, 0 < ρ →
        ∫ t in Set.Ioi ρ, t ^ (n-1) * (max 1 t) ^ (-A') ≤ ρ ^ ((n:ℝ) - A') / (A' - (n:ℝ)))
    (hint : IntegrableOn (fun t : ℝ => t ^ (n-1) * (max 1 t) ^ (-A')) (Set.Ioi (0:ℝ))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ G : ℝ, 0 ≤ G →
      (∫ t in Set.Ioi (0:ℝ), t ^ (n-1) * (max 1 t) ^ (-A') * (max 1 (G - C₀ * t)) ^ (-A))
        ≤ C' * (max 1 G) ^ (-A) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set β : ℝ := A' - (n:ℝ) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  have hAβ : A ≤ β := by rw [hβdef]; linarith
  set M : ℝ := 1/(n:ℝ) + 1/β with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact add_pos (one_div_pos.mpr hnpos) (one_div_pos.mpr hβpos)
  have hC0pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have h2pos : (0:ℝ) < 2 := by norm_num
  set C' : ℝ := (2:ℝ) ^ A * M + ((2:ℝ)*C₀) ^ β / β with hC'def
  have h2Apos : (0:ℝ) < (2:ℝ) ^ A := Real.rpow_pos_of_pos h2pos A
  have h2Cpos : (0:ℝ) < ((2:ℝ)*C₀) ^ β := Real.rpow_pos_of_pos (mul_pos h2pos hC0pos) β
  have hC'pos : 0 < C' := by
    rw [hC'def]; exact add_pos (mul_pos h2Apos hMpos) (div_pos h2Cpos hβpos)
  refine ⟨C', hC'pos, ?_⟩
  intro G hG
  set m : ℝ := max 1 G with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  set ρ : ℝ := m / ((2:ℝ)*C₀) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos hmpos (mul_pos h2pos hC0pos)
  have hC₀ρ : C₀ * ρ = m / 2 := by rw [hρdef]; field_simp
  set gfun : ℝ → ℝ := fun t => t ^ (n-1) * (max 1 t) ^ (-A') with hgfun
  set f1 : ℝ → ℝ := fun t => t ^ (n-1) * (max 1 t) ^ (-A') * (max 1 (G - C₀ * t)) ^ (-A)
    with hf1
  set H : ℝ → ℝ := fun t => (2:ℝ) ^ A * m ^ (-A) * gfun t + (Set.Ioi ρ).indicator gfun t
    with hHdef
  have hg_nonneg : ∀ t, 0 < t → 0 ≤ gfun t := by
    intro t ht
    rw [hgfun]
    exact mul_nonneg (pow_nonneg ht.le _)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hf1_nonneg : ∀ t, 0 < t → 0 ≤ f1 t := by
    intro t ht
    rw [hf1]
    exact mul_nonneg (hg_nonneg t ht)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left (1:ℝ) (G - C₀ * t))) (-A))
  have hmm : ∀ t, 0 < t → t ≤ ρ → m / 2 ≤ max 1 (G - C₀ * t) := by
    intro t ht htρ
    rcases lt_or_ge (2:ℝ) m with hm2 | hm2
    · have hG2 : 2 < G := (lt_max_iff.mp hm2).resolve_left (by norm_num)
      have hmG : m = G := max_eq_right (le_of_lt (by linarith))
      have hCt : C₀ * t ≤ m / 2 := by
        rw [← hC₀ρ]; exact mul_le_mul_of_nonneg_left htρ hC0pos.le
      have : G - C₀ * t ≥ m / 2 := by rw [hmG]; linarith
      exact le_trans this (le_max_right 1 _)
    · exact le_trans (by linarith) (le_max_left 1 (G - C₀ * t))
  have hfac_le : ∀ t, 0 < t → t ≤ ρ →
      (max 1 (G - C₀ * t)) ^ (-A) ≤ (2:ℝ) ^ A * m ^ (-A) := by
    intro t ht htρ
    have hb : 0 < m / 2 := by linarith
    have hle := Real.rpow_le_rpow_of_nonpos hb (hmm t ht htρ) (show -A ≤ 0 by linarith)
    rwa [half_div_rpow_neg m A hmpos] at hle
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), f1 t ≤ H t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hgnn : 0 ≤ gfun t := hg_nonneg t ht0
    rcases lt_or_ge ρ t with htr | htr
    · have hind : (Set.Ioi ρ).indicator gfun t = gfun t := Set.indicator_of_mem htr gfun
      have hfac1 : (max 1 (G - C₀ * t)) ^ (-A) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_max_left 1 _) (show -A ≤ 0 by linarith)
      have hle : gfun t * (max 1 (G - C₀ * t)) ^ (-A) ≤ gfun t := by
        calc gfun t * (max 1 (G - C₀ * t)) ^ (-A) ≤ gfun t * 1 :=
              mul_le_mul_of_nonneg_left hfac1 hgnn
          _ = gfun t := mul_one _
      calc f1 t = gfun t * (max 1 (G - C₀ * t)) ^ (-A) := by rw [hf1, hgfun]
        _ ≤ gfun t := hle
        _ ≤ (2:ℝ) ^ A * m ^ (-A) * gfun t + gfun t := by
              have := mul_nonneg (mul_nonneg (Real.rpow_nonneg h2pos.le A)
                (Real.rpow_nonneg hmpos.le (-A))) hgnn
              linarith
        _ = H t := by simp only [hHdef, hind]
    · have hind : (Set.Ioi ρ).indicator gfun t = 0 := by
        rw [Set.indicator_of_notMem]
        rw [Set.mem_Ioi, not_lt]; exact htr
      have hfac := hfac_le t ht0 htr
      calc f1 t = gfun t * (max 1 (G - C₀ * t)) ^ (-A) := by rw [hf1, hgfun]
        _ ≤ gfun t * ((2:ℝ) ^ A * m ^ (-A)) := mul_le_mul_of_nonneg_left hfac hgnn
        _ = (2:ℝ) ^ A * m ^ (-A) * gfun t := by ring
        _ ≤ (2:ℝ) ^ A * m ^ (-A) * gfun t + 0 := by linarith
        _ = H t := by simp only [hHdef, hind, add_zero]
  have hHint : IntegrableOn H (Set.Ioi (0:ℝ)) := by
    rw [hHdef]
    have h1 : IntegrableOn (fun t => (2:ℝ) ^ A * m ^ (-A) * gfun t) (Set.Ioi (0:ℝ)) :=
      hint.const_mul _
    have h2 : IntegrableOn ((Set.Ioi ρ).indicator gfun) (Set.Ioi (0:ℝ)) :=
      (hint.indicator measurableSet_Ioi : IntegrableOn ((Set.Ioi ρ).indicator gfun) (Set.Ioi (0:ℝ)))
    exact h1.add h2
  have hJle : ∫ t in Set.Ioi (0:ℝ), f1 t ≤ ∫ t in Set.Ioi (0:ℝ), H t :=
    setIntegral_mono_of_nonneg (fun t ht => hf1_nonneg t ht) (fun t ht => hpt t ht) hHint
  have hInt_g : ∫ t in Set.Ioi (0:ℝ), gfun t = M := by rw [hgfun]; exact hmass
  have hInt_ind : ∫ t in Set.Ioi (0:ℝ), (Set.Ioi ρ).indicator gfun t = ∫ t in Set.Ioi ρ, gfun t := by
    rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hρpos.le]
  have hHval : ∫ t in Set.Ioi (0:ℝ), H t = (2:ℝ) ^ A * m ^ (-A) * M + ∫ t in Set.Ioi ρ, gfun t := by
    have h1 : IntegrableOn (fun t => (2:ℝ) ^ A * m ^ (-A) * gfun t) (Set.Ioi (0:ℝ)) :=
      hint.const_mul _
    have h2 : IntegrableOn ((Set.Ioi ρ).indicator gfun) (Set.Ioi (0:ℝ)) :=
      (hint.indicator measurableSet_Ioi : IntegrableOn ((Set.Ioi ρ).indicator gfun) (Set.Ioi (0:ℝ)))
    rw [hHdef, integral_add h1 h2, integral_const_mul, hInt_g, hInt_ind]
  have htailval : ∫ t in Set.Ioi ρ, gfun t ≤ ((2:ℝ)*C₀) ^ β * m ^ (-β) / β := by
    have h1 := htail ρ hρpos
    have hρpow : ρ ^ ((n:ℝ) - A') = ((2:ℝ)*C₀) ^ β * m ^ (-β) := by
      rw [show (n:ℝ) - A' = -β by rw [hβdef]; ring, hρdef,
        Real.div_rpow hmpos.le (mul_pos h2pos hC0pos).le, div_eq_mul_inv,
        Real.rpow_neg (mul_pos h2pos hC0pos).le, inv_inv]
      ring
    rw [hρpow] at h1
    rw [hβdef] at h1
    exact h1
  have hfin : (2:ℝ) ^ A * m ^ (-A) * M + ((2:ℝ)*C₀) ^ β * m ^ (-β) / β ≤ C' * m ^ (-A) := by
    have hmβ : m ^ (-β) ≤ m ^ (-A) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    have hkey : ((2:ℝ)*C₀) ^ β * m ^ (-β) / β ≤ ((2:ℝ)*C₀) ^ β * m ^ (-A) / β := by
      apply div_le_div_of_nonneg_right _ hβpos.le
      exact mul_le_mul_of_nonneg_left hmβ h2Cpos.le
    rw [hC'def]
    have e1 : (2:ℝ) ^ A * m ^ (-A) * M = (2:ℝ) ^ A * M * m ^ (-A) := by ring
    have e2 : ((2:ℝ) ^ A * M + ((2:ℝ)*C₀) ^ β / β) * m ^ (-A)
        = (2:ℝ) ^ A * M * m ^ (-A) + ((2:ℝ)*C₀) ^ β / β * m ^ (-A) := by ring
    have e3 : ((2:ℝ)*C₀) ^ β * m ^ (-A) / β = ((2:ℝ)*C₀) ^ β / β * m ^ (-A) := by ring
    rw [e1, e2]
    linarith [hkey, e3]
  calc ∫ t in Set.Ioi (0:ℝ), f1 t ≤ ∫ t in Set.Ioi (0:ℝ), H t := hJle
    _ = (2:ℝ) ^ A * m ^ (-A) * M + ∫ t in Set.Ioi ρ, gfun t := hHval
    _ ≤ (2:ℝ) ^ A * m ^ (-A) * M + ((2:ℝ)*C₀) ^ β * m ^ (-β) / β := by linarith [htailval]
    _ ≤ C' * m ^ (-A) := hfin

theorem ball_tent_conv_lipschitz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (A A' : ℝ) (hA : 0 < A) (hA' : A + (Module.finrank ℝ E : ℝ) < A') (C₀ : ℝ)
    (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R G : ℝ), 0 < R → 0 ≤ G →
      (MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure E)
        (fun w : E => ((MeasureTheory.volume (Metric.ball (0 : E) R)).toReal)⁻¹
          * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
          * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)))
        ≤ C * (max 1 G) ^ (-A) := by
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hA'' : A + ((Module.finrank ℝ E : ℕ) : ℝ) < A' := hA'
  have hA''' : ((Module.finrank ℝ E : ℕ) : ℝ) < A' := by linarith
  obtain ⟨C', hC'pos, hC'bdd⟩ := one_dim_bound (Module.finrank ℝ E) hn A A' hA hA'' C₀ hC₀
      (integral_Ioi_rpow_max_one _ hn A' hA''') (fun ρ hρ => tail_bound _ hn A' hA''' hρ)
      (integrableOn_Ioi_rpow_max_one _ hn A' hA''')
  refine ⟨(Module.finrank ℝ E : ℝ) * C', ?_, ?_⟩
  · have hfpos : (0:ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast Module.finrank_pos
    positivity
  · intro R G hR hG
    set v : ℝ := (MeasureTheory.volume (Metric.ball (0:E) 1)).toReal with hv_def
    have hvpos : 0 < v := by
      rw [hv_def]
      have h := Metric.measure_ball_pos (μ := (MeasureTheory.volume : MeasureTheory.Measure E))
          (0:E) (show (0:ℝ) < 1 by norm_num)
      exact ENNReal.toReal_pos h.ne' (measure_ball_lt_top.ne)
    set cR : ℝ := ((MeasureTheory.volume (Metric.ball (0:E) R)).toReal)⁻¹ with hcR_def
    set Psi : E → ℝ := fun u => (1 + Metric.infDist u (Metric.ball (0:E) 1)) ^ (-A')
        * (max 1 (G - C₀ * ‖u‖)) ^ (-A) with hPsi_def
    set J : ℝ := ∫ t in Set.Ioi (0:ℝ), t ^ (Module.finrank ℝ E - 1) * (max 1 t) ^ (-A')
        * (max 1 (G - C₀ * t)) ^ (-A) with hJ_def
    have hpt2 : ∀ w : E, cR * (1 + Metric.infDist w (Metric.ball (0:E) R)/R)^(-A')
          * (max 1 (G - C₀ * ‖w‖/R))^(-A) = cR * Psi (R⁻¹ • w) := by
      intro w
      have h1 : 1 + Metric.infDist w (Metric.ball (0:E) R)/R
          = 1 + Metric.infDist (R⁻¹ • w) (Metric.ball (0:E) 1) := by
        rw [infDist_ball_zero hR w, infDist_ball_zero zero_lt_one (R⁻¹ • w),
          norm_inv_smul' hR w, max_zero_sub_div (‖w‖) hR]
      have h2 : G - C₀ * ‖w‖/R = G - C₀ * ‖R⁻¹ • w‖ := by
        rw [norm_inv_smul' hR w]; ring
      rw [h1, h2]
      simp only [hPsi_def]
      ring
    have hvolR : (MeasureTheory.volume (Metric.ball (0:E) R)).toReal
        = R ^ (Module.finrank ℝ E) * v := by
      rw [MeasureTheory.Measure.addHaar_ball (μ := (MeasureTheory.volume : MeasureTheory.Measure E))
        (x := (0:E)) hR.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
    have hcRv : cR * R ^ (Module.finrank ℝ E) = v⁻¹ := by
      rw [hcR_def, hvolR, mul_inv_rev, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ hR.ne'), mul_one]
    have stepA : ∫ w, cR * (1 + Metric.infDist w (Metric.ball (0:E) R)/R)^(-A')
          * (max 1 (G - C₀ * ‖w‖/R))^(-A) = v⁻¹ * ∫ u, Psi u := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => hpt2 w)), integral_const_mul,
        MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
          (μ := (MeasureTheory.volume : MeasureTheory.Measure E)) Psi hR.le]
      change cR • (R ^ (Module.finrank ℝ E) • (∫ x, Psi x)) = v⁻¹ * ∫ u, Psi u
      rw [smul_smul, hcRv, smul_eq_mul]
    have stepB : ∫ u, Psi u = (Module.finrank ℝ E : ℝ) * v * J := by
      set f : ℝ → ℝ := fun t => (max 1 t)^(-A') * (max 1 (G - C₀*t))^(-A) with hf_def
      have hPsif : ∀ u, Psi u = f (‖u‖) := by
        intro u
        change (1 + Metric.infDist u (Metric.ball (0:E) 1)) ^ (-A')
          * (max 1 (G - C₀ * ‖u‖)) ^ (-A) = f (‖u‖)
        rw [infDist_ball_zero zero_lt_one u, one_add_max_zero_sub_one]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => hPsif u)),
        MeasureTheory.integral_fun_norm_addHaar]
      rw [MeasureTheory.measureReal_def,
        show (MeasureTheory.volume (Metric.ball (0:E) 1)).toReal = v from hv_def.symm]
      have hJeq : (∫ y in Set.Ioi (0:ℝ), y ^ (Module.finrank ℝ E - 1) • f y) = J := by
        rw [hJ_def, hf_def]
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro t ht
        simp only [smul_eq_mul]
        ring
      rw [hJeq, nsmul_eq_mul, smul_eq_mul]
      ring
    have hJbdd : J ≤ C' * (max 1 G) ^ (-A) := by
      rw [hJ_def]; exact hC'bdd G hG
    have hcalc : MeasureTheory.integral (MeasureTheory.volume : MeasureTheory.Measure E)
        (fun w : E => cR * (1 + Metric.infDist w (Metric.ball (0:E) R)/R)^(-A')
          * (max 1 (G - C₀ * ‖w‖/R))^(-A)) = (Module.finrank ℝ E : ℝ) * J := by
      rw [stepA, stepB]
      field_simp
    rw [hcalc]
    calc (Module.finrank ℝ E : ℝ) * J
        ≤ (Module.finrank ℝ E : ℝ) * (C' * (max 1 G) ^ (-A)) :=
          mul_le_mul_of_nonneg_left hJbdd (by positivity)
      _ = ((Module.finrank ℝ E : ℝ) * C') * (max 1 G) ^ (-A) := by ring


end

end Commons.Analysis.Convolution