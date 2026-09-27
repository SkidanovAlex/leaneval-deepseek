import Mathlib
import Submission.Work.EQ.TailGlueDefs
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.H0_section_local

namespace Work.EQ.Chart

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The first coordinate of an analytic pair-valued function is analytic. -/
lemma tailGlueFam_analyticOnNhd_fst {f : ℂ → ℂ × ℂ} {s : Set ℂ} (h : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ (fun a => (f a).1) s :=
  fun x hx => (analyticAt_fst (p := f x)).comp (h x hx)

/-- The second coordinate of an analytic pair-valued function is analytic. -/
lemma tailGlueFam_analyticOnNhd_snd {f : ℂ → ℂ × ℂ} {s : Set ℂ} (h : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ (fun a => (f a).2) s :=
  fun x hx => (analyticAt_snd (p := f x)).comp (h x hx)

/-- A function meromorphic at `0` which is analytic on the punctured ball of radius `ρ` is
meromorphic on the whole ball. -/
lemma tailGlueFam_meromorphicOn_ball {f : ℂ → ℂ} {ρ : ℝ}
    (h0 : MeromorphicAt f 0) (han : AnalyticOnNhd ℂ f (Metric.ball 0 ρ \ {0})) :
    MeromorphicOn f (Metric.ball 0 ρ) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0; exact h0
  · exact (han x ⟨hx, by simpa using hx0⟩).meromorphicAt

/-- **Forward tail, analyticity.**  For `j ≥ dep` the forward coordinate
`germC a h (λ^j (z₀ + t^(2^(2 dep))))` is analytic on the disc `ball 0 ρ`: the inner map is a
polynomial and its values lie in the disc of analyticity of `germC`, because the hypothesis is
stated at `λ^dep` and `0 < λ < 1`. -/
theorem tailGlue_fwd_coord_analytic_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {z₀ : ℂ} {dep : ℕ} {ρ ρt : ℝ} (_hρ : 0 < ρ)
    (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρt))
    (hft : ∀ t : ℂ, ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))‖ < ρt)
    {j : ℤ} (hj : (dep : ℤ) ≤ j) :
    AnalyticOnNhd ℂ
      (fun t : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep)))))
      (Metric.ball 0 ρ) := by
  have hlamne : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  have hzpow : ((eqLam a : ℝ) : ℂ) ^ j
      = ((eqLam a : ℝ) : ℂ) ^ (j - (dep : ℤ)) * ((eqLam a : ℝ) : ℂ) ^ dep := by
    rw [show ((eqLam a : ℝ) : ℂ) ^ dep = ((eqLam a : ℝ) : ℂ) ^ (dep : ℤ) by
        rw [zpow_natCast], ← zpow_add₀ hlamne]
    congr 1
    ring
  have hg : AnalyticOnNhd ℂ
      (fun t : ℂ => ((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep))))
      (Metric.ball 0 ρ) :=
    fun t _ => (analyticAt_const (v := ((eqLam a : ℝ) : ℂ) ^ j) (x := t)).mul
      ((analyticAt_const (v := z₀) (x := t)).add (analyticAt_pow_id (2 ^ (2 * dep))))
  refine hgerm.comp hg ?_
  intro t ht
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  have hD : ((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep)))
      = ((eqLam a : ℝ) : ℂ) ^ (j - (dep : ℤ)) *
        (((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))) := by
    rw [hzpow, mul_assoc]
  have hexp : (0 : ℤ) ≤ j - (dep : ℤ) := by omega
  calc ‖((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep)))‖
      = ‖((eqLam a : ℝ) : ℂ) ^ (j - (dep : ℤ)) *
          (((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep))))‖ := by rw [hD]
    _ = ‖((eqLam a : ℝ) : ℂ) ^ (j - (dep : ℤ))‖ *
          ‖((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))‖ := norm_mul _ _
    _ ≤ 1 * ‖((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))‖ :=
        mul_le_mul_of_nonneg_right (win_norm_eqLamC_zpow_le_one ha0 ha1 hexp) (norm_nonneg _)
    _ = ‖((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))‖ := one_mul _
    _ < ρt := hft t ht

/-- **Backward tail, analyticity.**  For `j < -dep` the backward coordinate
`ugermC a h (λ^{-j} (cc/(z₀ + t^(2^(2 dep)))))` is analytic on `ball 0 ρ`: the inner map is
analytic there (`hden` keeps the denominator away from `0`) and the bound at `λ^dep` transfers to
`λ^{-j}`, `0 < λ < 1`. -/
theorem tailGlue_bwd_coord_analytic_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {cc z₀ : ℂ} {dep : ℕ} {ρ ρt : ℝ} (_hρ : 0 < ρ)
    (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρt))
    (hden : ∀ t : ℂ, ‖t‖ < ρ → z₀ + t ^ (2 ^ (2 * dep)) ≠ 0)
    (hbk : ∀ t : ℂ, ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖ < ρt)
    {j : ℤ} (hj : j < -((dep : ℤ))) :
    AnalyticOnNhd ℂ
      (fun t : ℂ =>
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep))))))
      (Metric.ball 0 ρ) := by
  have hlamne : ((eqLam a : ℝ) : ℂ) ≠ 0 := win_eqLamC_ne_zero ha0 ha1
  have hD : AnalyticOnNhd ℂ (fun t : ℂ => z₀ + t ^ (2 ^ (2 * dep))) (Metric.ball 0 ρ) :=
    fun t _ => (analyticAt_const (v := z₀) (x := t)).add (analyticAt_pow_id (2 ^ (2 * dep)))
  have hden' : ∀ t ∈ Metric.ball (0 : ℂ) ρ, z₀ + t ^ (2 ^ (2 * dep)) ≠ 0 :=
    fun t ht => hden t (by rwa [Metric.mem_ball, dist_zero_right] at ht)
  have hψ : AnalyticOnNhd ℂ
      (fun t : ℂ => ((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep)))))
      (Metric.ball 0 ρ) :=
    (analyticOnNhd_const (v := ((eqLam a : ℝ) : ℂ) ^ (-j))).mul
      ((analyticOnNhd_const (v := cc)).div hD hden')
  refine analyticOnNhd_ugermC_comp (a := a) hgerm hψ ?_
  intro t ht
  have htlt : ‖t‖ < ρ := by
    have h := ht; rwa [Metric.mem_ball, dist_zero_right] at h
  have hfac : ((eqLam a : ℝ) : ℂ) ^ (-j)
      = ((eqLam a : ℝ) : ℂ) ^ (-j - (dep : ℤ)) * ((eqLam a : ℝ) : ℂ) ^ dep := by
    rw [show ((eqLam a : ℝ) : ℂ) ^ dep = ((eqLam a : ℝ) : ℂ) ^ (dep : ℤ) by
        rw [zpow_natCast], ← zpow_add₀ hlamne]
    congr 1
    ring
  have hexp : (0 : ℤ) ≤ -j - (dep : ℤ) := by omega
  have hrepr : ((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep))))
      = ((eqLam a : ℝ) : ℂ) ^ (-j - (dep : ℤ)) *
        (((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))) := by
    rw [hfac, mul_assoc]
  rw [Metric.mem_ball, dist_zero_right]
  show ‖((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖ < ρt
  rw [hrepr, norm_mul]
  calc ‖((eqLam a : ℝ) : ℂ) ^ (-j - (dep : ℤ))‖ *
        ‖((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖
      ≤ 1 * ‖((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖ :=
        mul_le_mul_of_nonneg_right (win_norm_eqLamC_zpow_le_one ha0 ha1 hexp) (norm_nonneg _)
    _ = ‖((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖ := one_mul _
    _ < ρt := hbk t htlt

theorem tailGlue_family_props {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {cc z₀ : ℂ} {dep : ℕ} {σ : Fin (2 * dep) → Bool}
    (hAdm : Adm a (endFun a h dep) z₀ 1 σ)
    (hend : AnalyticOnNhd ℂ (endFun a h dep) (Metric.ball z₀ 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ rhoFin' a (endFun a h dep) z₀ 1 (2 * dep))
    {ρt : ℝ} (hρt : 0 < ρt) (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρt))
    (hden : ∀ t : ℂ, ‖t‖ < ρ → z₀ + t ^ (2 ^ (2 * dep)) ≠ 0)
    (hft : ∀ t : ℂ, ‖t‖ < ρ → ‖((eqLam a : ℝ) : ℂ) ^ dep * (z₀ + t ^ (2 ^ (2 * dep)))‖ < ρt)
    (hbk : ∀ t : ℂ, ‖t‖ < ρ →
      ‖((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep))))‖ < ρt) :
    ContinuousOn (fun t : ℂ => tailGlue a h cc z₀ dep σ t) {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} ∧
      (∀ n : ℤ, MeromorphicOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 n).1) (Metric.ball 0 ρ) ∧
        MeromorphicOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 n).2) (Metric.ball 0 ρ)) ∧
      MeromorphicOn (fun t : ℂ => (tailGlue a h cc z₀ dep σ t).2.2) (Metric.ball 0 ρ) := by
  classical
  have hsub : {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} ⊆ Metric.ball (0 : ℂ) ρ :=
    fun t ht => by rw [Metric.mem_ball, dist_zero_right]; exact ht.2
  have hsub' : {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} ⊆ Metric.ball (0 : ℂ) ρ \ {0} :=
    fun t ht => ⟨hsub ht, by simpa using (norm_pos_iff.mp ht.1)⟩
  have key : ∀ j : ℤ,
      MeromorphicOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).1) (Metric.ball 0 ρ) ∧
      MeromorphicOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).2) (Metric.ball 0 ρ) ∧
      ContinuousOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).1)
        {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} ∧
      ContinuousOn (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).2)
        {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < ρ} := by
    intro j
    by_cases hjf : (dep : ℤ) ≤ j
    · -- forward tail
      have hAn := tailGlue_fwd_coord_analytic_local ha0 ha1 hρ hgerm hft hjf
      have hEq1 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).1)
          = (fun t : ℂ =>
              (germC a h (((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep))))).1) := by
        funext t; rw [tailGlue_fwd hjf]
      have hEq2 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).2)
          = (fun t : ℂ =>
              (germC a h (((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep))))).2) := by
        funext t; rw [tailGlue_fwd hjf]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hEq1]; exact (tailGlueFam_analyticOnNhd_fst hAn).meromorphicOn
      · rw [hEq2]; exact (tailGlueFam_analyticOnNhd_snd hAn).meromorphicOn
      · rw [hEq1]; exact (tailGlueFam_analyticOnNhd_fst hAn).continuousOn.mono hsub
      · rw [hEq2]; exact (tailGlueFam_analyticOnNhd_snd hAn).continuousOn.mono hsub
    · by_cases hjb : -((dep : ℤ)) ≤ j
      · -- middle segment
        set jj : Fin (2 * dep + 1) := ⟨(j + (dep : ℤ)).toNat, by
          have hpos : (0 : ℤ) ≤ j + (dep : ℤ) := by omega
          rw [Int.toNat_lt hpos]
          have hlt : j + (dep : ℤ) < ((2 * dep + 1 : ℕ) : ℤ) := by
            have h1 := hjf; push_cast at h1 ⊢; omega
          exact hlt⟩ with hjj
        have hAnM := branchPt_analytic (a := a) (c := endFun a h dep) (u₀ := z₀) (R := 1)
          (σ := σ) one_pos hend hAdm jj
        have hmono1 : AnalyticOnNhd ℂ
            (fun t : ℂ => (branchPt a (endFun a h dep) z₀ 1 σ t jj).1)
            (Metric.ball (0 : ℂ) ρ \ {0}) :=
          hAnM.1.mono (fun z hz => ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩)
        have hmono2 : AnalyticOnNhd ℂ
            (fun t : ℂ => (branchPt a (endFun a h dep) z₀ 1 σ t jj).2)
            (Metric.ball (0 : ℂ) ρ \ {0}) :=
          hAnM.2.mono (fun z hz => ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩)
        have h0m := branchPt_meromorphic (a := a) (c := endFun a h dep) (u₀ := z₀) (R := 1)
          (N := 2 * dep) (σ := σ) one_pos hend hAdm jj
        have hEq1 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).1)
            = (fun t : ℂ => (branchPt a (endFun a h dep) z₀ 1 σ t jj).1) := by
          funext t; rw [tailGlue_mid hjf hjb]
        have hEq2 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).2)
            = (fun t : ℂ => (branchPt a (endFun a h dep) z₀ 1 σ t jj).2) := by
          funext t; rw [tailGlue_mid hjf hjb]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hEq1]; exact tailGlueFam_meromorphicOn_ball h0m.1 hmono1
        · rw [hEq2]; exact tailGlueFam_meromorphicOn_ball h0m.2 hmono2
        · rw [hEq1]; exact hmono1.continuousOn.mono hsub'
        · rw [hEq2]; exact hmono2.continuousOn.mono hsub'
      · -- backward tail
        have hbwd : j < -((dep : ℤ)) := not_le.mp hjb
        have hAn := tailGlue_bwd_coord_analytic_local ha0 ha1 hρ hgerm hden hbk hbwd
        have hEq1 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).1)
            = (fun t : ℂ =>
                (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) *
                  (cc / (z₀ + t ^ (2 ^ (2 * dep)))))).1) := by
          funext t; rw [tailGlue_bwd hbwd]
        have hEq2 : (fun t : ℂ => ((tailGlue a h cc z₀ dep σ t).1 j).2)
            = (fun t : ℂ =>
                (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) *
                  (cc / (z₀ + t ^ (2 ^ (2 * dep)))))).2) := by
          funext t; rw [tailGlue_bwd hbwd]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hEq1]; exact (tailGlueFam_analyticOnNhd_fst hAn).meromorphicOn
        · rw [hEq2]; exact (tailGlueFam_analyticOnNhd_snd hAn).meromorphicOn
        · rw [hEq1]; exact (tailGlueFam_analyticOnNhd_fst hAn).continuousOn.mono hsub
        · rw [hEq2]; exact (tailGlueFam_analyticOnNhd_snd hAn).continuousOn.mono hsub
  -- the unstable parameter `ψ₂ = cc / (z₀ + t^(2^(2 dep)))` is analytic on the ball
  have hDan : AnalyticOnNhd ℂ (fun t : ℂ => z₀ + t ^ (2 ^ (2 * dep))) (Metric.ball (0 : ℂ) ρ) :=
    fun t _ => (analyticAt_const (v := z₀) (x := t)).add (analyticAt_pow_id (2 ^ (2 * dep)))
  have hden' : ∀ t ∈ Metric.ball (0 : ℂ) ρ, z₀ + t ^ (2 ^ (2 * dep)) ≠ 0 :=
    fun t ht => hden t (by rwa [Metric.mem_ball, dist_zero_right] at ht)
  have hAn3 : AnalyticOnNhd ℂ (fun t : ℂ => cc / (z₀ + t ^ (2 ^ (2 * dep))))
      (Metric.ball (0 : ℂ) ρ) :=
    (analyticOnNhd_const (v := cc)).div hDan hden'
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ ?_)
    · rw [continuousOn_pi]
      intro j
      exact ContinuousOn.prodMk (key j).2.2.1 (key j).2.2.2
    · have hψ1c : Continuous (fun t : ℂ => z₀ + t ^ (2 ^ (2 * dep))) := by fun_prop
      simpa only [tailGlue_psi1] using hψ1c.continuousOn
    · simpa only [tailGlue_psi2] using hAn3.continuousOn.mono hsub
  · intro n
    exact ⟨(key n).1, (key n).2.1⟩
  · simpa only [tailGlue_psi2] using hAn3.meromorphicOn

end

end Work.EQ.Chart
