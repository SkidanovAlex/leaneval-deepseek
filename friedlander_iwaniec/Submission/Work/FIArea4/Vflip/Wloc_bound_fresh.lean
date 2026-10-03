import Mathlib
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.Vflip.KK_fourier
import Submission.Work.FIArea4.Vflip.parseval_zmod_le
import Submission.Work.FIArea4.Vflip.cCoef_bound
import Submission.Work.FIArea4.Wloc_eq_classSum
import Submission.Work.FIArea4.Vflip.tau_decay_sum
import Submission.Work.FIArea4.Vflip.tau_class_decay_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Work.FIArea4.Vflip

open Finset BigOperators

noncomputable section

/-! ## Summability of the sampled function `F` -/

lemma summable_nat_linear (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => ((1:ℝ) + c * (n:ℝ)) ^ (-(2:ℝ))) := by
  have hbase0 : Summable (fun m : ℕ => ((m:ℝ))⁻¹^2) := by
    have h : Summable (fun m : ℕ => ((m:ℝ)^(2:ℝ))⁻¹) := Real.summable_nat_rpow_inv.mpr (by norm_num)
    convert h using 2 with m
    rw [Real.rpow_two, inv_pow]
  have hbase : Summable (fun n : ℕ => (((n+1:ℕ):ℝ))⁻¹^2) :=
    (summable_nat_add_iff (f := fun m : ℕ => ((m:ℝ))⁻¹^2) 1).mpr hbase0
  have hbase' : Summable (fun n : ℕ => (((n:ℝ)+1))⁻¹^2) := by
    simpa [Nat.cast_add, Nat.cast_one] using hbase
  have hF : Summable (fun n : ℕ => (min (1:ℝ) c)⁻¹^2 * (((n:ℝ)+1))⁻¹^2) := hbase'.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hF
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h1 : min (1:ℝ) c * ((n:ℝ)+1) ≤ 1 + c*(n:ℝ) := by
    by_cases hc1 : (1:ℝ) ≤ c
    · rw [min_eq_left hc1]; nlinarith
    · push Not at hc1; rw [min_eq_right hc1.le]; nlinarith
  have hposm : 0 < min (1:ℝ) c * ((n:ℝ)+1) := by positivity
  have hpos : 0 < 1 + c*(n:ℝ) := by positivity
  have hinv : (1 + c*(n:ℝ))⁻¹ ≤ (min (1:ℝ) c * ((n:ℝ)+1))⁻¹ := inv_anti₀ hposm h1
  have hsq : ((1 + c*(n:ℝ))⁻¹)^2 ≤ ((min (1:ℝ) c * ((n:ℝ)+1))⁻¹)^2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  rw [show ((1:ℝ) + c * (n:ℝ)) ^ (-(2:ℝ)) = ((1 + c*(n:ℝ))⁻¹)^2 by
      rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_two, inv_pow]]
  calc ((1 + c*(n:ℝ))⁻¹)^2 ≤ ((min (1:ℝ) c * ((n:ℝ)+1))⁻¹)^2 := hsq
    _ = (min (1:ℝ) c)⁻¹^2 * (((n:ℝ)+1))⁻¹^2 := by rw [mul_inv, mul_pow]

lemma summable_int_abs (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => ((1:ℝ) + c * |(k:ℝ)|) ^ (-(2:ℝ))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_nat_linear c hc
  · have h := summable_nat_linear c hc
    have hh : (fun n : ℕ => ((1:ℝ) + c * |((-↑n : ℤ) : ℝ)|) ^ (-(2:ℝ)))
        = (fun n : ℕ => ((1:ℝ) + c * (n:ℝ)) ^ (-(2:ℝ))) := by
      funext n
      have hc1 : ((-↑n : ℤ) : ℝ) = -(n:ℝ) := by push_cast; ring
      rw [hc1, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hh]; exact h

lemma summable_abs_div (σ : ℝ) (q : ℕ) (hσ : 0 < σ) (hq : 1 ≤ q) :
    Summable (fun k : ℤ => ((1:ℝ) + σ * |(k:ℝ)|/(q:ℝ)) ^ (-(2:ℝ))) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have h := summable_int_abs (σ/(q:ℝ)) (div_pos hσ hqpos)
  convert h using 1
  ext k
  rw [div_mul_eq_mul_div]

lemma summable_sampled (F : ℝ → ℂ) (C₀ σ : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hC₀ : 0 ≤ C₀) (hσ : 0 < σ)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ))) :
    Summable (fun k : ℤ => F ((k:ℝ)/q)) := by
  have hg : Summable (fun k : ℤ => ((1:ℝ) + σ * |(k:ℝ)|/(q:ℝ)) ^ (-(2:ℝ))) :=
    summable_abs_div σ q hσ hq
  have hg2 : Summable (fun k : ℤ => C₀ * σ * ((1:ℝ) + σ * |(k:ℝ)|/(q:ℝ)) ^ (-(2:ℝ))) :=
    hg.mul_left _
  refine Summable.of_norm_bounded hg2 (fun k => ?_)
  have h := hF ((k:ℝ)/q)
  have habs : |(k:ℝ)/(q:ℝ)| = |(k:ℝ)|/(q:ℝ) := by rw [abs_div]; simp only [abs_of_nonneg (show (0:ℝ) ≤ (q:ℝ) from Nat.cast_nonneg q)]
  rw [habs] at h
  convert h using 3
  ring


/-! ## Summability of the coefficient sequence `c_m` -/

lemma summable_natAbs_rpow (δ μ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μ) :
    Summable (fun m : ℤ => (m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ))) := by
  have hs : (1:ℝ) < 2 - δ := by linarith
  have hbase : Summable (fun m : ℤ => (1:ℝ) / |(m:ℝ)| ^ (2-δ)) := by
    have h := (Real.summable_one_div_int_add_rpow 0 (2-δ)).mpr hs
    simpa using h
  have hg : Summable (fun m : ℤ => μ^2 * ((1:ℝ) / |(m:ℝ)| ^ (2-δ))) := hbase.mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) ?_
  intro m hm
  rw [Set.mem_ofPred_eq] at hm
  simp only [not_le, Set.mem_singleton_iff] at hm ⊢
  by_contra hm0
  have hna : |(m:ℝ)| = (m.natAbs : ℝ) := by simp
  have hnpos : (0:ℝ) < (m.natAbs : ℝ) := by
    rw [← hna]; exact abs_pos.mpr (by exact_mod_cast hm0)
  have hb : ‖(m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ))‖
      ≤ μ^2 * ((1:ℝ) / |(m:ℝ)| ^ (2-δ)) := by
    have ha : (0:ℝ) < (m.natAbs : ℝ) := hnpos
    have hp : 0 < (m.natAbs:ℝ)/μ := div_pos ha hμ
    have hA : (0:ℝ) ≤ (m.natAbs:ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m.natAbs) δ)
        (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hA, hna]
    have h1 : (1 + (m.natAbs:ℝ)/μ) ^ (-(2:ℝ)) = ((1 + (m.natAbs:ℝ)/μ)^2)⁻¹ := by
      rw [show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [h1]
    have hle : (m.natAbs:ℝ)/μ ≤ 1 + (m.natAbs:ℝ)/μ := by linarith
    have hinv : ((1 + (m.natAbs:ℝ)/μ)^2)⁻¹ ≤ (((m.natAbs:ℝ)/μ)^2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le hle 2)
    have hkey : (m.natAbs:ℝ)^δ * (((m.natAbs:ℝ)/μ)^2)⁻¹ = μ^2 * (1 / (m.natAbs:ℝ)^(2-δ)) := by
      have hpow : (m.natAbs:ℝ)^(2-δ) = (m.natAbs:ℝ)^2/(m.natAbs:ℝ)^δ := by
        rw [eq_div_iff (Real.rpow_pos_of_pos ha δ).ne', ← Real.rpow_add ha,
            show (2 - δ) + δ = (2:ℝ) by ring, Real.rpow_two]
      rw [div_pow, inv_div, hpow]
      field_simp
    calc (m.natAbs:ℝ)^δ * ((1 + (m.natAbs:ℝ)/μ)^2)⁻¹
        ≤ (m.natAbs:ℝ)^δ * (((m.natAbs:ℝ)/μ)^2)⁻¹ := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = μ^2 * (1 / (m.natAbs:ℝ)^(2-δ)) := hkey
  linarith [hm, hb]

lemma summable_cCoef (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (F : ℝ → ℂ) (C₀ σ : ℝ) (R : ℕ) (d1 d2 : ℕ) (hC₀ : 0 < C₀) (hσ : 1 ≤ σ)
    (hR : 1 ≤ R) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ))) :
    Summable (fun m : ℤ => Work.FIArea4.cCoef F R d1 d2 m) := by
  obtain ⟨C₃, hC₃, hbound⟩ := cCoef_bound δ hδ0
  have hμ : (0:ℝ) < (Nat.lcm d1 d2 : ℝ) * R / σ := by
    have h1 : (0:ℝ) < (Nat.lcm d1 d2 : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega)))
    have h2 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
    positivity
  have hg : Summable (fun m : ℤ => (C₃*C₀*σ) *
      ((m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/((Nat.lcm d1 d2:ℝ)*R/σ)) ^ (-(2:ℝ)))) :=
    (summable_natAbs_rpow δ ((Nat.lcm d1 d2:ℝ)*R/σ) hδ0 hδ1 hμ).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) ?_
  intro m hm
  rw [Set.mem_ofPred_eq] at hm
  simp only [not_le, Set.mem_singleton_iff] at hm ⊢
  by_contra hm0
  have hb := hbound F C₀ σ R d1 d2 m hC₀ hσ hR hd1 hd2 hF hm0
  have harg : (1 + σ * |(m:ℝ)| / ((Nat.lcm d1 d2:ℝ) * R))
      = (1 + |(m:ℝ)|/((Nat.lcm d1 d2:ℝ)*R/σ)) := by
    have hsub : σ * |(m:ℝ)| / ((Nat.lcm d1 d2:ℝ) * R)
        = |(m:ℝ)| / (((Nat.lcm d1 d2:ℝ)*R)/σ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, inv_div]
      ring
    rw [hsub]
  rw [harg] at hb
  have hb2 : ‖Work.FIArea4.cCoef F R d1 d2 m‖ ≤
      (C₃*C₀*σ) * ((m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/((Nat.lcm d1 d2:ℝ)*R/σ)) ^ (-(2:ℝ))) :=
    le_trans hb (le_of_eq (by ring))
  linarith [hm, hb2]

lemma cCoef_zero_eq (F : ℝ → ℂ) (R d1 d2 : ℕ) :
    Work.FIArea4.cCoef F R d1 d2 0
      = F 0 * ∑ r ∈ (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ) := by
  unfold Work.FIArea4.cCoef Work.FIArea4.wChar
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [if_pos (dvd_zero _)]
  have hF0 : ((((0:ℤ) / (r:ℤ) : ℤ) : ℝ) / ((Nat.lcm d1 d2):ℝ)) = 0 := by simp
  rw [hF0]
  by_cases h : Nat.Coprime r (d1*d2)
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

lemma cCoef_zero_le (F : ℝ → ℂ) (C₀ σ : ℝ) (R d1 d2 : ℕ) (hC₀ : 0 < C₀) (hσ : 1 ≤ σ)
    (hF : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ))) :
    ‖Work.FIArea4.cCoef F R d1 d2 0‖
      ≤ C₀ * σ * ‖∑ r ∈ (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)‖ := by
  rw [cCoef_zero_eq, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h0 := hF 0
  have hone : (1 + σ * |(0:ℝ)|) ^ (-(2:ℝ)) = 1 := by
    rw [abs_zero, mul_zero, add_zero]; exact Real.one_rpow _
  rw [hone, mul_one] at h0
  exact h0

/-- The main local-variance bound. -/
theorem Wloc_bound_fresh : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (σ : ℝ) (hσ : 1 ≤ σ) (F : ℝ → ℂ) (C₀ : ℝ) (hC₀ : 0 < C₀),
        (∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * σ * (1 + σ * |ξ|) ^ (-(2:ℝ))) →
        ∀ (R : ℕ) (hR : 1 ≤ R) (d1 d2 : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2),
          Work.FIArea4.Wloc F R d1 d2 ≤ C * C₀ ^ 2 *
            (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * σ ^ 2 *
               Complex.normSq (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
                 (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
             + (R + σ) * R) * (((Nat.lcm d1 d2 : ℕ) : ℝ) * R) ^ ε := by
  intro ε hε
  set δ : ℝ := min (ε/4) (1/4) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ2 : 2 * δ ≤ ε := by
    have h := min_le_left (ε/4) (1/4 : ℝ); rw [hδdef]; linarith
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := tau_decay_sum δ hδ0 hδ1
  obtain ⟨C₂, hC₂pos, hC₂b⟩ := tau_class_decay_sum δ hδ0 hδ1
  obtain ⟨C₃, hC₃pos, hC₃b⟩ := cCoef_bound δ hδ0
  refine ⟨2 + 2*C₃^2*C₁*C₂, by positivity, ?_⟩
  intro σ hσ F C₀ hC₀ hF R hR d1 d2 hd1 hd2
  have hσ0 : (0:ℝ) < σ := by linarith
  set q : ℕ := Nat.lcm d1 d2 with hq
  have hq1 : 1 ≤ q := by
    rw [hq]; exact Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
  have hqR' : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  set μ : ℝ := (q:ℝ)*R/σ with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  have hFsum : Summable (fun k : ℤ => F ((k:ℝ)/(q:ℝ))) :=
    summable_sampled F C₀ σ q hq1 hC₀.le hσ0 hF
  set c : ℤ → ℂ := Work.FIArea4.cCoef F R d1 d2 with hcdef
  have hsum_c : Summable c := summable_cCoef δ hδ0 hδ1 F C₀ σ R d1 d2 hC₀ hσ hR hd1 hd2 hF
  have hsum_cn : Summable (fun m : ℤ => ‖c m‖) := summable_norm_iff.mpr hsum_c
  set c' : ℤ → ℂ := fun m => if m = 0 then 0 else c m with hc'def
  have hc'm : ∀ m : ℤ, c' m = if m = 0 then 0 else c m := fun m => by rw [hc'def]
  have hsum_c' : Summable c' := by
    rw [← summable_norm_iff]
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      rw [hc'm]; by_cases h : m = 0 <;> simp [h]) hsum_cn
  have hmu_eq : ∀ m : ℤ, (1 + σ*|(m:ℝ)|/((q:ℝ)*R)) = (1 + |(m:ℝ)|/μ) := by
    intro m
    rw [hμdef]
    have hsub : σ * |(m:ℝ)| / ((q:ℝ)*R) = |(m:ℝ)| / (((q:ℝ)*R)/σ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, inv_div]; ring
    rw [hsub]
  set g : ℤ → ℝ := fun m => C₃*C₀*σ*((m.natAbs:ℝ)^δ*(1+|(m:ℝ)|/μ)^(-(2:ℝ))) with hgdef
  have hgsum : Summable g := (summable_natAbs_rpow δ μ hδ0 hδ1 hμpos).mul_left _
  have hble : ∀ m : ℤ, ‖c' m‖ ≤ g m := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [hc'm, if_pos rfl, norm_zero, hgdef]
      positivity
    · rw [hc'm, if_neg hm, hcdef, hgdef]
      have h := hC₃b F C₀ σ R d1 d2 m hC₀ hσ hR hd1 hd2 hF hm
      rw [hmu_eq m] at h
      calc ‖Work.FIArea4.cCoef F R d1 d2 m‖
          ≤ C₃ * C₀ * σ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ)) * (m.natAbs:ℝ)^δ := h
        _ = C₃*C₀*σ*((m.natAbs:ℝ)^δ*(1+|(m:ℝ)|/μ)^(-(2:ℝ))) := by ring
  have hsum_cn' : Summable (fun m : ℤ => ‖c' m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hble hgsum
  -- total bound
  have htotal : (∑' m : ℤ, ‖c' m‖) ≤ C₃*C₀*σ*C₁*μ^(1+δ) := by
    have h1 : (∑' m : ℤ, ‖c' m‖) ≤ ∑' m : ℤ, g m := Summable.tsum_le_tsum hble hsum_cn' hgsum
    rw [hgdef] at h1
    rw [tsum_mul_left] at h1
    refine h1.trans ?_
    have h2 := hC₁b μ hμpos
    calc C₃ * C₀ * σ * (∑' m : ℤ, (m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ)))
        ≤ C₃ * C₀ * σ * (C₁ * μ^(1+δ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C₃*C₀*σ*C₁*μ^(1+δ) := by ring
  -- class bound
  have hclass : ∀ n : ZMod q, (∑' m : ℤ, (if (m : ZMod q) = n then ‖c' m‖ else 0))
      ≤ C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ) := by
    intro n
    obtain ⟨n₀, rfl⟩ := ZMod.intCast_surjective n
    have hitenn : ∀ m : ℤ, 0 ≤ (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then ‖c' m‖ else 0) := by
      intro m; split_ifs with h
      · positivity
      · simp
    have hitele : ∀ m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then ‖c' m‖ else 0) ≤ ‖c' m‖ := by
      intro m; split_ifs with h
      · exact le_refl _
      · positivity
    have hsum_ite : Summable (fun m : ℤ => (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then ‖c' m‖ else 0)) :=
      Summable.of_nonneg_of_le hitenn hitele hsum_cn'
    have hitenn_g : ∀ m : ℤ, 0 ≤ (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then g m else 0) := by
      intro m; split_ifs with h
      · rw [hgdef]; positivity
      · simp
    have hitele_g : ∀ m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then g m else 0) ≤ g m := by
      intro m; split_ifs with h
      · exact le_refl _
      · rw [hgdef]; positivity
    have hsum_ite_g : Summable (fun m : ℤ => (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then g m else 0)) :=
      Summable.of_nonneg_of_le hitenn_g hitele_g hgsum
    have h1 : (∑' m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then ‖c' m‖ else 0))
        ≤ ∑' m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then g m else 0) := by
      refine Summable.tsum_le_tsum (fun m => ?_) hsum_ite hsum_ite_g
      by_cases h : (m : ZMod q) = ((n₀:ℤ) : ZMod q)
      · rw [if_pos h, if_pos h]; exact hble m
      · simp [h]
    refine h1.trans ?_
    have heq : (∑' m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then g m else 0))
        = C₃*C₀*σ * (∑' m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then
              (m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ)) else 0)) := by
      rw [hgdef, ← tsum_mul_left]
      apply tsum_congr; intro m
      by_cases h : (m:ZMod q) = ((n₀:ℤ):ZMod q) <;> simp [h]
    rw [heq]
    have h2 := hC₂b μ hμpos q hq1 n₀
    calc C₃*C₀*σ * (∑' m : ℤ, (if (m : ZMod q) = ((n₀:ℤ) : ZMod q) then
              (m.natAbs : ℝ)^δ * (1 + |(m:ℝ)|/μ) ^ (-(2:ℝ)) else 0))
        ≤ C₃*C₀*σ * (C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ) := by ring
  have hM0 : 0 ≤ C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ) := by positivity
  -- Parseval
  have hparseval : (∑ a ∈ Finset.range q, Complex.normSq (∑' m : ℤ, c' m *
        Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))))
      ≤ (q:ℝ) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (∑' m : ℤ, ‖c' m‖) :=
    parseval_zmod_le q hq1 c' _ hM0 hsum_c' hclass
  -- norm of the character
  have hE : ∀ (m:ℤ) (a:ℕ), ‖Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))‖ = 1 := by
    intro m a
    have hz : 2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)
        = ((2*Real.pi*(m:ℝ)*(a:ℝ)/(q:ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hz, Complex.norm_exp_ofReal_mul_I]
  -- summability of c m * E
  have hsum_cE : ∀ a : ℕ, Summable (fun m : ℤ => c m *
      Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))) := by
    intro a
    refine Summable.of_norm_bounded hsum_cn (fun m => ?_)
    rw [norm_mul, hE m a, mul_one]
  -- the Fourier expansion of KK
  have hKK : ∀ a : ℕ, Work.FIArea4.KK F R d1 d2 a
      = (1/(q:ℝ)) * ∑' m : ℤ, c m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) := by
    intro a
    have := KK_fourier F R d1 d2 a hd1 hd2 hFsum
    rw [show Nat.lcm d1 d2 = q from hq.symm] at this
    simpa [hcdef] using this
  have hsplit : ∀ a : ℕ, (∑' m : ℤ, c m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)))
      = c 0 + ∑' m : ℤ, c' m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) := by
    intro a
    rw [Summable.tsum_eq_add_tsum_ite (hsum_cE a) 0]
    have hE0 : Complex.exp (2*Real.pi*Complex.I*((0:ℤ):ℝ)*(a:ℝ)/(q:ℝ)) = 1 := by simp
    rw [hE0, mul_one]
    congr 1
    apply tsum_congr; intro m
    rw [hc'm]; by_cases h : m = 0 <;> simp [h]
  -- bound on normSq of KK
  have hKKbound : ∀ a : ℕ, Complex.normSq (Work.FIArea4.KK F R d1 d2 a)
      ≤ (2/(q:ℝ)^2) * (Complex.normSq (c 0) +
          Complex.normSq (∑' m : ℤ, c' m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)))) := by
    intro a
    set Y : ℂ := ∑' m : ℤ, c' m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) with hYdef
    rw [hKK a, hsplit a, Complex.normSq_mul]
    have hqfac : Complex.normSq ((1:ℂ) / (((q:ℕ):ℝ) : ℂ)) = (1/(q:ℝ))^2 := by
      rw [Complex.normSq_eq_norm_sq]
      have hnorm : ‖((1:ℂ) / (((q:ℕ):ℝ) : ℂ))‖ = 1/(q:ℝ) := by
        rw [norm_div, norm_one]
        have : ‖(((q:ℕ):ℝ) : ℂ)‖ = (q:ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [this]
      rw [hnorm]
    rw [hqfac]
    have h3 : Complex.normSq (c 0 + Y)
        ≤ 2*Complex.normSq (c 0) + 2*Complex.normSq Y := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (c 0) Y) 2
      nlinarith [hle, sq_nonneg (‖c 0‖ - ‖Y‖)]
    have hfin := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (1/(q:ℝ))^2)
    refine hfin.trans (le_of_eq ?_)
    ring_nf
  -- summability of E-sum
  have hnorm_bound : (∑' m : ℤ, ‖c' m‖) ≤ C₃*C₀*σ*C₁*μ^(1+δ) := htotal
  have hc0 : Complex.normSq (c 0) ≤ (C₀*σ)^2 *
      Complex.normSq (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)) := by
    have h := cCoef_zero_le F C₀ σ R d1 d2 hC₀ hσ hF
    rw [hcdef]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    calc ‖Work.FIArea4.cCoef F R d1 d2 0‖^2
        ≤ (C₀ * σ * ‖∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = (C₀*σ)^2 * ‖∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
            (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)‖^2 := by ring
  -- assemble
  have hW : Work.FIArea4.Wloc F R d1 d2
      ≤ (2/(q:ℝ)) * Complex.normSq (c 0)
        + (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (∑' m : ℤ, ‖c' m‖) := by
    rw [Work.FIArea4.Wloc]
    calc (∑ a ∈ Finset.range q, Complex.normSq (Work.FIArea4.KK F R d1 d2 a))
        ≤ ∑ a ∈ Finset.range q, ((2/(q:ℝ)^2) * (Complex.normSq (c 0) +
            Complex.normSq (∑' m : ℤ, c' m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ))))) :=
          Finset.sum_le_sum (fun a _ => hKKbound a)
      _ = (2/(q:ℝ)^2) * ((q:ℝ) * Complex.normSq (c 0)
            + ∑ a ∈ Finset.range q, Complex.normSq (∑' m : ℤ, c' m * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2/(q:ℝ)^2) * ((q:ℝ) * Complex.normSq (c 0)
            + (q:ℝ) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (∑' m : ℤ, ‖c' m‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add (le_refl _) hparseval
      _ = (2/(q:ℝ)) * Complex.normSq (c 0)
            + (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (∑' m : ℤ, ‖c' m‖) := by
          field_simp
  refine hW.trans ?_
  -- final arithmetic
  set N : ℝ := Complex.normSq (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)) with hNdef
  have hqr1 : (1:ℝ) ≤ (q:ℝ)*R := by
    have h1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have h2 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    nlinarith
  have hqr0 : (0:ℝ) ≤ (q:ℝ)*R := by positivity
  have hexp1 : (1:ℝ) ≤ ((q:ℝ)*R)^ε := Real.one_le_rpow hqr1 hε.le
  have hqrE : (0:ℝ) ≤ ((q:ℝ)*R)^ε := Real.rpow_nonneg hqr0 ε
  have hμle : μ ≤ (q:ℝ)*R := by
    rw [hμdef]; exact div_le_self (by positivity) hσ
  have hμ2 : μ^(2*δ) ≤ ((q:ℝ)*R)^ε := by
    calc μ^(2*δ) ≤ ((q:ℝ)*R)^(2*δ) := Real.rpow_le_rpow hμpos.le hμle (by linarith [hδ0])
      _ ≤ ((q:ℝ)*R)^ε := Real.rpow_le_rpow_of_exponent_le hqr1 hδ2
  have hA2 : (2/(q:ℝ)) * ((C₀*σ)^2 * N) ≤ 2*C₀^2 * ((q:ℝ)⁻¹ * σ^2 * N) * ((q:ℝ)*R)^ε := by
    have h1 : (2/(q:ℝ)) * ((C₀*σ)^2 * N) = 2*C₀^2 * ((q:ℝ)⁻¹ * σ^2 * N) := by
      rw [inv_eq_one_div]; ring
    rw [h1]
    have ha : (0:ℝ) ≤ 2*C₀^2*((q:ℝ)⁻¹*σ^2*N) := by
      apply mul_nonneg (by positivity)
      apply mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Complex.normSq_nonneg _)
    nlinarith [hexp1, ha]
  have hB2 : (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (C₃*C₀*σ*C₁*μ^(1+δ))
      ≤ 2*C₃^2*C₁*C₂*C₀^2 * ((R+σ)*R) * ((q:ℝ)*R)^ε := by
    have hfac : (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (C₃*C₀*σ*C₁*μ^(1+δ))
        = 2*C₃^2*C₁*C₂*C₀^2 * (σ^2*μ^(2+2*δ)/(q:ℝ)^2 + σ^2*μ^(1+2*δ)/(q:ℝ)) := by
      rw [show μ^(2+2*δ) = μ^(1+δ)*μ^(1+δ) by rw [← Real.rpow_add hμpos]; congr 1; ring,
          show μ^(1+2*δ) = μ^(1+δ)*μ^δ by rw [← Real.rpow_add hμpos]; congr 1; ring]
      field_simp
    rw [hfac]
    have hid : (σ^2*μ^(2+2*δ)/(q:ℝ)^2 + σ^2*μ^(1+2*δ)/(q:ℝ)) = (R^2 + σ*R)*μ^(2*δ) := by
      rw [show μ^(2+2*δ) = μ^2*μ^(2*δ) by rw [Real.rpow_add hμpos, Real.rpow_two],
          show μ^(1+2*δ) = μ*μ^(2*δ) by rw [Real.rpow_add hμpos, Real.rpow_one],
          hμdef]
      field_simp
    rw [hid]
    have hcoef : (0:ℝ) ≤ 2*C₃^2*C₁*C₂*C₀^2 := by positivity
    have hRS : (0:ℝ) ≤ (R+σ)*R := by positivity
    have h1 : 2*C₃^2*C₁*C₂*C₀^2 * ((R^2+σ*R)*μ^(2*δ))
        ≤ 2*C₃^2*C₁*C₂*C₀^2 * ((R+σ)*R * ((q:ℝ)*R)^ε) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      rw [show R^2+σ*R = (R+σ)*R by ring]
      exact mul_le_mul_of_nonneg_left hμ2 hRS
    refine h1.trans (le_of_eq ?_)
    ring
  have hstep1 : (2/(q:ℝ)) * Complex.normSq (c 0) ≤ (2/(q:ℝ)) * ((C₀*σ)^2 * N) :=
    mul_le_mul_of_nonneg_left hc0 (by positivity)
  have hstep2 : (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (∑' m : ℤ, ‖c' m‖)
      ≤ (2/(q:ℝ)) * (C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ) + μ^δ)) * (C₃*C₀*σ*C₁*μ^(1+δ)) :=
    mul_le_mul_of_nonneg_left hnorm_bound (by positivity)
  have hfin : (2/(q:ℝ))*((C₀*σ)^2*N) + (2/(q:ℝ))*(C₃*C₀*σ*C₂*(μ^(1+δ)/(q:ℝ)+μ^δ))*(C₃*C₀*σ*C₁*μ^(1+δ))
      ≤ (2 + 2*C₃^2*C₁*C₂) * C₀^2 * (((q:ℝ)⁻¹*σ^2*N) + (R+σ)*R) * ((q:ℝ)*R)^ε := by
    have htarget : (2 + 2*C₃^2*C₁*C₂) * C₀^2 * (((q:ℝ)⁻¹*σ^2*N) + (R+σ)*R) * ((q:ℝ)*R)^ε
        = (2 + 2*C₃^2*C₁*C₂) * C₀^2 * ((q:ℝ)⁻¹*σ^2*N) * ((q:ℝ)*R)^ε
          + (2 + 2*C₃^2*C₁*C₂) * C₀^2 * ((R+σ)*R) * ((q:ℝ)*R)^ε := by ring
    have hNnn : (0:ℝ) ≤ (q:ℝ)⁻¹*σ^2*N := by
      apply mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Complex.normSq_nonneg _)
    have h1 : 2*C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε
        ≤ (2 + 2*C₃^2*C₁*C₂)*C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε := by
      have hle : (2:ℝ) ≤ 2+2*C₃^2*C₁*C₂ := by
        linarith [show (0:ℝ) ≤ 2*C₃^2*C₁*C₂ by positivity]
      have ha : (0:ℝ) ≤ C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε :=
        mul_nonneg (mul_nonneg (by positivity) hNnn) hqrE
      rw [show 2*C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε
            = 2*(C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε) by ring,
          show (2 + 2*C₃^2*C₁*C₂)*C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε
            = (2 + 2*C₃^2*C₁*C₂)*(C₀^2*((q:ℝ)⁻¹*σ^2*N)*((q:ℝ)*R)^ε) by ring]
      exact mul_le_mul_of_nonneg_right hle ha
    have h2 : 2*C₃^2*C₁*C₂*C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε
        ≤ (2+2*C₃^2*C₁*C₂)*C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε := by
      have hle : (2:ℝ)*C₃^2*C₁*C₂ ≤ 2+2*C₃^2*C₁*C₂ := by
        linarith [show (0:ℝ) ≤ 2*C₃^2*C₁*C₂ by positivity]
      have ha : (0:ℝ) ≤ C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε :=
        mul_nonneg (mul_nonneg (by positivity) (by positivity)) hqrE
      rw [show 2*C₃^2*C₁*C₂*C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε
            = (2*C₃^2*C₁*C₂)*(C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε) by ring,
          show (2+2*C₃^2*C₁*C₂)*C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε
            = (2+2*C₃^2*C₁*C₂)*(C₀^2*((R+σ)*R)*((q:ℝ)*R)^ε) by ring]
      exact mul_le_mul_of_nonneg_right hle ha
    refine (add_le_add hA2 hB2).trans ?_
    rw [htarget]
    exact add_le_add h1 h2
  exact (add_le_add hstep1 hstep2).trans hfin
end

end Work.FIArea4.Vflip
