import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_sep
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.step_w
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanTri.radicand_pos
import Submission.Work.EQ.germCHelpers

set_option maxHeartbeats 4000000

/-!
# Uniform (first order) fan estimates

`Work.EQ.FanUniform.fan_uniform_estimates`: on a single disc `B(0,δ)`, uniformly in the branch
word `ε`, the stable fan `fan a h ε` is holomorphic and its two coordinates are bounded to
*first order* in `‖u‖`: the abscissa deviation from the (axis) centre by `Ke ‖u‖` and the second
coordinate by `Lam ‖u‖ ‖x - a/2‖`.

The proof is the majorant induction of `Work.EQ.fan_sep` (Rychlik's proof of Theorem 7(1) /
Lemma 14) with two additions: analyticity is carried along in the induction, using
`FanTri.analytic_invBranch` (holomorphy of the inverse branch where the radicand has positive
real part) and `FanTri.radicand_pos` (the radicand of the *next* fan point has positive real
part, which follows from the semi-projective bound and the centre arithmetic).
-/

namespace Work.EQ.FanUniform

open Work.EQ Complex Metric Filter
open scoped Topology

noncomputable section

/-- Invariant of the uniform fan induction: the fan is analytic on `B(0,ρ)`, its centre lies on
the axis at a point of `-1/2 + 2ℤ`, the abscissa deviation from the centre is `≤ P‖v‖` and the
second coordinate is `≤ Q ρ ‖v‖ ‖x - a/2‖`. -/
def FanGoodU (a : ℝ) (h : ℂ → ℂ) (P : ℝ) (Q : ℝ → ℝ) (ρ : ℝ) (ε : List Bool) : Prop :=
  (∀ v : ℂ, ‖v‖ < ρ → AnalyticAt ℂ (fan a h ε) v) ∧
  (fan a h ε 0).2 = 0 ∧ (∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k) ∧
  (∀ v : ℂ, ‖v‖ < ρ → ‖(fan a h ε v).1 - (fan a h ε 0).1‖ ≤ P * ‖v‖) ∧
  (∀ v : ℂ, ‖v‖ < ρ →
    ‖(fan a h ε v).2‖ ≤ Q ρ * ‖v‖ * ‖(fan a h ε v).1 - ((a / 2 : ℝ) : ℂ)‖)

theorem fan_uniform_estimates {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ Ke Lam : ℝ, 0 < δ ∧ 0 < Ke ∧ 0 < Lam ∧ ∀ ε : List Bool,
      AnalyticOnNhd ℂ (Work.EQ.fan a h ε) (Metric.ball (0 : ℂ) δ) ∧
      ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
        ‖(Work.EQ.fan a h ε u).1 - (Work.EQ.fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
        ‖(Work.EQ.fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(Work.EQ.fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
  -- ============================ inputs ============================
  obtain ⟨δg, pg, qg, hδgpos, hpgpos, hqgpos, hgerm⟩ := FanSep.germ_lip ha0 ha1 hh
  obtain ⟨ρg, hρgpos, hganC⟩ := Work.EQ.germC_analytic ha0 ha1 hh
  obtain ⟨haxis_branch, haxis2⟩ := FanSep.axis_walk ha0 ha1 hh
  obtain ⟨hcn_dist, hcn_ext⟩ := FanSep.centre_numbers ha0 ha1
  obtain ⟨Cx, hCxpos, hCx⟩ := FanSep.step_x ha0 ha1
  obtain ⟨hstepw1, CA, hCApos, hstepw2⟩ := FanSep.step_w ha0 ha1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have h1mlam : 0 < 1 - eqLam a := by linarith only [hlam1]
  have h1a : 0 < 1 - a := by linarith only [ha1]
  -- ============================ constants ============================
  set P : ℝ := pg + 1 with hPdef
  have hPpos : 0 < P := by rw [hPdef]; linarith only [hpgpos]
  have hPgP : pg ≤ P := by rw [hPdef]; linarith only
  set K : ℝ := CA * P * eqLam a / (1 - eqLam a) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (le_of_lt (mul_pos (mul_pos hCApos hPpos) hlam0)) (le_of_lt h1mlam)
  set Qf : ℝ → ℝ := fun t => qg * Real.exp (K * t) with hQfdef
  have hQfpos : ∀ t, 0 < Qf t := fun t => by
    change 0 < qg * Real.exp (K * t)
    exact mul_pos hqgpos (Real.exp_pos _)
  have hQf_qg : ∀ t, 0 ≤ t → qg ≤ Qf t := by
    intro t ht
    change qg ≤ qg * Real.exp (K * t)
    have h1 : (1 : ℝ) ≤ Real.exp (K * t) := by
      rw [Real.one_le_exp_iff]; exact mul_nonneg hK0 ht
    calc qg = qg * 1 := by ring
      _ ≤ qg * Real.exp (K * t) := mul_le_mul_of_nonneg_left h1 (le_of_lt hqgpos)
  have hQf_le1 : ∀ t, t ≤ 1 → Qf t ≤ Qf 1 := by
    intro t ht
    change qg * Real.exp (K * t) ≤ qg * Real.exp (K * 1)
    have h1 : K * t ≤ K * 1 := by
      simpa using mul_le_mul_of_nonneg_left ht hK0
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) (le_of_lt hqgpos)
  have hQf_step : ∀ t : ℝ, Qf (eqLam a * t) * (1 + CA * P * (eqLam a * t)) ≤ Qf t := by
    intro t
    change qg * Real.exp (K * (eqLam a * t)) * (1 + CA * P * (eqLam a * t)) ≤
      qg * Real.exp (K * t)
    have hexp : 1 + CA * P * (eqLam a * t) ≤ Real.exp (CA * P * (eqLam a * t)) := by
      have := Real.add_one_le_exp (CA * P * (eqLam a * t)); linarith only [this]
    have harg : K * (eqLam a * t) + CA * P * (eqLam a * t) = K * t := by
      rw [hKdef]; field_simp; ring
    have hq0 : (0 : ℝ) ≤ qg := le_of_lt hqgpos
    have hep : (0 : ℝ) < Real.exp (K * (eqLam a * t)) := Real.exp_pos _
    calc qg * Real.exp (K * (eqLam a * t)) * (1 + CA * P * (eqLam a * t))
        ≤ qg * Real.exp (K * (eqLam a * t)) * Real.exp (CA * P * (eqLam a * t)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hq0 (le_of_lt hep))
      _ = qg * (Real.exp (K * (eqLam a * t)) * Real.exp (CA * P * (eqLam a * t))) := by ring
      _ = qg * Real.exp (K * (eqLam a * t) + CA * P * (eqLam a * t)) := by rw [Real.exp_add]
      _ = qg * Real.exp (K * t) := by rw [harg]
  set Qbar : ℝ := Qf 1 with hQbardef
  have hQbarpos : 0 < Qbar := by rw [hQbardef]; exact hQfpos 1
  -- ============================ the radius ============================
  set δ : ℝ := min δg (min ρg (min 1 (min ((1 - eqLam a) * P / (4 * Cx * Qbar ^ 2))
      (min ((1 - a) / (16 * P)) (eqLam a / (8 * Qbar)))))) with hδdef
  have hδ_le_δg : δ ≤ δg := by rw [hδdef]; exact min_le_left _ _
  have hδ_le_ρg : δ ≤ ρg := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_1 : δ ≤ 1 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_A : δ ≤ (1 - eqLam a) * P / (4 * Cx * Qbar ^ 2) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_le_B : δ ≤ (1 - a) / (16 * P) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδ_le_C : δ ≤ eqLam a / (8 * Qbar) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min hδgpos (lt_min hρgpos (lt_min one_pos (lt_min ?_ (lt_min ?_ ?_))))
    · exact div_pos (mul_pos h1mlam hPpos) (by positivity)
    · exact div_pos h1a (by positivity)
    · exact div_pos hlam0 (by positivity)
  have hCxQbarδ : Cx * Qbar ^ 2 * δ ≤ (1 - eqLam a) * P := by
    have hpos : (0 : ℝ) < 4 * Cx * Qbar ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hδ_le_A (le_of_lt hpos)
    rw [show 4 * Cx * Qbar ^ 2 * ((1 - eqLam a) * P / (4 * Cx * Qbar ^ 2))
          = (1 - eqLam a) * P by field_simp] at h
    have hX : 0 ≤ Cx * Qbar ^ 2 * δ := by positivity
    nlinarith only [h, hX]
  have hPδ16 : P * δ ≤ (1 - a) / 16 := by
    have h := mul_le_mul_of_nonneg_left hδ_le_B (le_of_lt hPpos)
    rw [show P * ((1 - a) / (16 * P)) = (1 - a) / 16 by field_simp] at h
    exact h
  have hQbarδ : Qbar * δ ≤ eqLam a / 8 := by
    have h := mul_le_mul_of_nonneg_left hδ_le_C (le_of_lt hQbarpos)
    rw [show Qbar * (eqLam a / (8 * Qbar)) = eqLam a / 8 by field_simp] at h
    exact h
  -- ============================ the induction ============================
  have key : ∀ ε : List Bool, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → FanGoodU a h P Qf ρ ε := by
    intro ε
    induction ε with
    | nil =>
      intro ρ hρ0 hρδ
      have hρρg : ρ ≤ ρg := le_trans hρδ hδ_le_ρg
      have hρδg : ρ ≤ δg := le_trans hρδ hδ_le_δg
      have hval0 : fan a h ([] : List Bool) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := by
        rw [Work.EQ.fan_nil]
        exact Work.EQ.germC_value ha0 ha1 hh
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- analyticity
        intro v hv
        have hv' : v ∈ Metric.ball (0 : ℂ) ρg := by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero]
          exact lt_of_lt_of_le hv hρρg
        have hfun : fan a h ([] : List Bool) = germC a h := rfl
        rw [hfun]
        exact hganC v hv'
      · rw [hval0]
      · refine ⟨0, ?_⟩
        rw [hval0]
        norm_num
      · -- abscissa deviation
        intro v hv
        have hgb := hgerm v (lt_of_lt_of_le hv hρδg)
        have h0 : (germC a h 0).1 = ((-1 / 2 : ℝ) : ℂ) := by
          rw [Work.EQ.germC_value ha0 ha1 hh]
          norm_num
        change ‖(germC a h v).1 - (germC a h 0).1‖ ≤ P * ‖v‖
        rw [h0]
        calc ‖(germC a h v).1 - ((-1 / 2 : ℝ) : ℂ)‖ ≤ pg * ‖v‖ := hgb.1
          _ ≤ P * ‖v‖ := mul_le_mul_of_nonneg_right hPgP (norm_nonneg v)
      · -- semi-projective coordinate
        intro v hv
        have hgb := hgerm v (lt_of_lt_of_le hv hρδg)
        change ‖(germC a h v).2‖ ≤
          Qf ρ * ‖v‖ * ‖(germC a h v).1 - ((a / 2 : ℝ) : ℂ)‖
        calc ‖(germC a h v).2‖ ≤ qg * ‖v‖ * ‖(germC a h v).1 - ((a / 2 : ℝ) : ℂ)‖ := hgb.2
          _ ≤ Qf ρ * ‖v‖ * ‖(germC a h v).1 - ((a / 2 : ℝ) : ℂ)‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_right (hQf_qg ρ (le_of_lt hρ0)) (norm_nonneg v)
    | cons s ε' ih =>
      intro ρ hρ0 hρδ
      have hlamρ0 : 0 < eqLam a * ρ := mul_pos hlam0 hρ0
      have hlamρδ : eqLam a * ρ ≤ δ :=
        mul_le_of_le_one (le_of_lt hlam1) (le_of_lt hρ0) hρδ
      obtain ⟨hAn', hzε', hck', hbX', hbW'⟩ := ih (eqLam a * ρ) hlamρ0 hlamρδ
      obtain ⟨k, hk⟩ := hck'
      set c : ℝ := -1 / 2 + 2 * (k : ℝ) with hcdef
      have hcentre : (fan a h ε' 0).1 = (c : ℂ) := by
        rw [hcdef]; push_cast; rw [hk]
      have hc_b : (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact (hcn_dist k).1
      have hc_b2 : (1 - a) / 2 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact (hcn_dist k).2
      have hc_ext : eqLam a * ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ ≤
          ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact hcn_ext k
      have hcc_pos : 0 < ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by linarith only [hc_b, h1a]
      -- the centre of the new word
      set c' : ℝ := -c + sgnB s * sgnR (c + a / 2) with hc'def
      have hxne : c + a / 2 ≠ 0 := by
        intro hcon
        have h2 : ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ = 0 := by
          rw [← Complex.ofReal_add, hcon, Complex.ofReal_zero, norm_zero]
        linarith only [hcc_pos, h2]
      have hnew0 : (fan a h (s :: ε') 0).1 = ((c' : ℝ) : ℂ) := by
        rw [Work.EQ.fan_cons, mul_zero,
          show fan a h ε' 0 = ((c : ℂ), (0 : ℂ)) from Prod.ext hcentre hzε']
        have hb := congrArg Prod.fst (FanSep.invBranch_axis a s hxne)
        rw [hb, hc'def, Work.EQ.axStep]
      obtain ⟨hznew, hcknew⟩ := haxis2 (s :: ε')
      -- ============================ the step ============================
      have main : ∀ v : ℂ, ‖v‖ < ρ →
          AnalyticAt ℂ (fan a h (s :: ε')) v ∧
          ‖(fan a h (s :: ε') v).1 - (fan a h (s :: ε') 0).1‖ ≤ P * ‖v‖ ∧
          ‖(fan a h (s :: ε') v).2‖ ≤ Qf ρ * ‖v‖ *
            ‖(fan a h (s :: ε') v).1 - ((a / 2 : ℝ) : ℂ)‖ := by
        intro v hv
        have hw_norm : ‖(eqLam a : ℂ) * v‖ = eqLam a * ‖v‖ := by
          rw [norm_mul, show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from
            RCLike.norm_ofReal (K := ℂ) (eqLam a), abs_of_pos hlam0]
        have hw_lt : ‖(eqLam a : ℂ) * v‖ < eqLam a * ρ := by
          rw [hw_norm]; exact mul_lt_mul_of_pos_left hv hlam0
        have hw_lt' : ‖(eqLam a : ℂ) * v‖ < eqLam a * ρ := hw_lt
        set G : ℂ × ℂ := fan a h ε' ((eqLam a : ℂ) * v) with hGdef
        have hvF : fan a h (s :: ε') v = invBranch a s G := by
          rw [Work.EQ.fan_cons, ← hGdef]
        have hGX : ‖G.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖v‖) := by
          have h := hbX' ((eqLam a : ℂ) * v) hw_lt'
          rw [← hGdef, hw_norm, hcentre] at h
          exact h
        have hGW : ‖G.2‖ ≤ Qf (eqLam a * ρ) * (eqLam a * ‖v‖) *
            ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ := by
          have h := hbW' ((eqLam a : ℂ) * v) hw_lt'
          rw [← hGdef, hw_norm] at h
          exact h
        have hu_rho : ‖v‖ ≤ ρ := le_of_lt hv
        have hu_del : ‖v‖ ≤ δ := le_trans hu_rho hρδ
        have hGXle : ‖G.1 - (c : ℂ)‖ ≤ P * ‖v‖ := by
          calc ‖G.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖v‖) := hGX
            _ ≤ P * ‖v‖ := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hPpos)
                calc eqLam a * ‖v‖ ≤ 1 * ‖v‖ :=
                      mul_le_mul_of_nonneg_right (le_of_lt hlam1) (norm_nonneg v)
                  _ = ‖v‖ := one_mul _
        have hρP : P * ‖v‖ ≤ (1 - a) / 16 := by
          calc P * ‖v‖ ≤ P * δ := mul_le_mul_of_nonneg_left hu_del (le_of_lt hPpos)
            _ ≤ (1 - a) / 16 := hPδ16
        have hQ1 : ‖G.1 - (c : ℂ)‖ ≤ (1 - a) / 8 := by
          calc ‖G.1 - (c : ℂ)‖ ≤ P * ‖v‖ := hGXle
            _ ≤ (1 - a) / 16 := hρP
            _ ≤ (1 - a) / 8 := by linarith only [h1a]
        have hQb_pos : 0 < ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by
          have heq : ((c : ℂ) + ((a / 2 : ℝ) : ℂ)) =
              (G.1 + ((a / 2 : ℝ) : ℂ)) - (G.1 - (c : ℂ)) := by ring
          have h1 : ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ ≤
              ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ + ‖G.1 - (c : ℂ)‖ := by
            rw [heq]; exact norm_sub_le _ _
          linarith only [h1, hc_b, hQ1, h1a]
        have hQb_ne' : G.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
          intro hcon
          have hlt := hQb_pos
          rw [hcon, norm_zero] at hlt
          exact lt_irrefl 0 hlt
        set qw : ℝ := Qf ρ * ‖v‖ with hqwdef
        have hqw0 : 0 ≤ qw := by
          rw [hqwdef]; exact mul_nonneg (le_of_lt (hQfpos ρ)) (norm_nonneg v)
        have hqw_le : qw ≤ Qbar * ‖v‖ := by
          rw [hqwdef]
          exact mul_le_mul_of_nonneg_right (hQf_le1 ρ (le_trans hρδ hδ_le_1)) (norm_nonneg v)
        have hqw12 : qw ≤ 1 / 2 := by
          calc qw ≤ Qbar * ‖v‖ := hqw_le
            _ ≤ Qbar * δ := mul_le_mul_of_nonneg_left hu_del (le_of_lt hQbarpos)
            _ ≤ eqLam a / 8 := hQbarδ
            _ ≤ 1 / 2 := by linarith only [hlam1]
        have hcorr : ‖G.1 - (c : ℂ)‖ ≤ P * (eqLam a * ρ) := by
          calc ‖G.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖v‖) := hGX
            _ ≤ P * (eqLam a * ρ) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_rho (le_of_lt hlam0))
                  (le_of_lt hPpos)
        have hlam_ratio : eqLam a * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
            ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) ≤ 1 := by
          rw [← mul_div_assoc]
          exact (div_le_one hcc_pos).mpr hc_ext
        have hQ2 : ‖G.2‖ ≤ qw * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by
          rw [hqwdef]
          have hdiv : ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
              (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 + CA * ‖G.1 - (c : ℂ)‖) * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by
            have hkey := hstepw2 hc_b hc_b2 hQ1
            have h2 := mul_le_mul_of_nonneg_right hkey
              (by positivity : (0 : ℝ) ≤ 1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)
            have e1 : (‖G.1 - ((a / 2 : ℝ) : ℂ)‖ * ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                  (1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) =
                ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ := by
              field_simp
            have e2 : (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ *
                  ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ * (1 + CA * ‖G.1 - (c : ℂ)‖)) *
                  (1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) =
                (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                  (1 + CA * ‖G.1 - (c : ℂ)‖) * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by
              field_simp
              try ring
            rw [e1, e2] at h2
            exact h2
          have hfac : 0 ≤ Qf (eqLam a * ρ) * (eqLam a * ‖v‖) :=
            mul_nonneg (le_of_lt (hQfpos _)) (mul_nonneg (le_of_lt hlam0) (norm_nonneg v))
          have hW : 0 ≤ ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := norm_nonneg _
          have hr0 : 0 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ :=
            div_nonneg (norm_nonneg _) (le_of_lt hcc_pos)
          have hA : 1 + CA * ‖G.1 - (c : ℂ)‖ ≤ 1 + CA * (P * (eqLam a * ρ)) := by
            have := mul_le_mul_of_nonneg_left hcorr (le_of_lt hCApos)
            linarith only [this]
          have hB2 : Qf (eqLam a * ρ) * (1 + CA * (P * (eqLam a * ρ))) ≤ Qf ρ := by
            simpa only [mul_assoc] using hQf_step ρ
          have hB : eqLam a * ‖v‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
              ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) ≤ ‖v‖ := by
            calc eqLam a * ‖v‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                    ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)
                = ‖v‖ * (eqLam a * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                    ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)) := by ring
              _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left hlam_ratio (norm_nonneg v)
              _ = ‖v‖ := mul_one _
          have hdiv' : ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
              ((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 + CA * (P * (eqLam a * ρ)))) * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ :=
            le_trans hdiv (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hr0) hW)
          have hstep1 : Qf (eqLam a * ρ) * (eqLam a * ‖v‖) * ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
              Qf (eqLam a * ρ) * (eqLam a * ‖v‖) *
                (((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                  (1 + CA * (P * (eqLam a * ρ)))) * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hdiv' hfac
          refine le_trans (le_trans hGW hstep1) ?_
          calc Qf (eqLam a * ρ) * (eqLam a * ‖v‖) *
                (((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                  (1 + CA * (P * (eqLam a * ρ)))) * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖)
              = (eqLam a * ‖v‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                  ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)) *
                  (Qf (eqLam a * ρ) * (1 + CA * (P * (eqLam a * ρ)))) *
                    ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
            _ ≤ ‖v‖ * Qf ρ * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by
                refine mul_le_mul ?_ (le_refl _) hW ?_
                · exact mul_le_mul hB hB2 (le_of_lt (mul_pos (hQfpos _) (by positivity)))
                    (norm_nonneg v)
                · positivity
            _ = Qf ρ * ‖v‖ * ‖G.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
        have hstepx := hCx s c G qw hc_b hQ1 hQ2 hqw12
        have hstepw := hstepw1 (Q := G) (qw := qw) s hQb_ne' hqw0 hqw12 hQ2
        have hstepx' : ‖(invBranch a s G).1 - ((c' : ℝ) : ℂ)‖ ≤
            ‖G.1 - (c : ℂ)‖ + Cx * qw ^ 2 := by
          have h := hstepx
          rw [← hc'def] at h
          exact h
        -- positivity of the radicand of `G` (so that `invBranch` is analytic there)
        have hGsubR : G.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
          have h3 : ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ ≤
              ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ + ‖G.1 - (c : ℂ)‖ := by
            have heq : ((c : ℂ) - ((a / 2 : ℝ) : ℂ)) =
                (G.1 - ((a / 2 : ℝ) : ℂ)) - (G.1 - (c : ℂ)) := by ring
            rw [heq]; exact norm_sub_le _ _
          intro hcon
          have h4 : ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
          linarith only [h3, hc_b2, hGXle, hρP, h4, h1a]
        have hGsub : G.1 - (a / 2 : ℂ) ≠ 0 := by simpa using hGsubR
        have hτg : Qbar * ‖v‖ ≤ eqLam a / 8 := by
          calc Qbar * ‖v‖ ≤ Qbar * δ := mul_le_mul_of_nonneg_left hu_del (le_of_lt hQbarpos)
            _ ≤ eqLam a / 8 := hQbarδ
        have hPwR : ‖G.2 / (G.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ Qbar * ‖v‖ := by
          rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hGsubR)]
          calc ‖G.2‖ ≤ Qf (eqLam a * ρ) * (eqLam a * ‖v‖) *
                ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ := hGW
            _ ≤ Qbar * ‖v‖ * ‖G.1 - ((a / 2 : ℝ) : ℂ)‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                calc Qf (eqLam a * ρ) * (eqLam a * ‖v‖) ≤ Qbar * (eqLam a * ‖v‖) := by
                      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                      exact hQf_le1 (eqLam a * ρ)
                        (le_trans (mul_le_of_le_one (le_of_lt hlam1) (le_of_lt hρ0) hρδ) hδ_le_1)
                  _ ≤ Qbar * ‖v‖ := by
                      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQbarpos)
                      calc eqLam a * ‖v‖ ≤ 1 * ‖v‖ :=
                            mul_le_mul_of_nonneg_right (le_of_lt hlam1) (norm_nonneg v)
                        _ = ‖v‖ := one_mul _
        have hPw : ‖G.2 / (G.1 - (a / 2 : ℂ))‖ ≤ Qbar * ‖v‖ := by simpa using hPwR
        have hGrad : 0 < (((G.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + G.2 ^ 2)).re :=
          FanTri.radicand_pos (a := a) (c := c) (P := G) (ρ := P * ‖v‖) (τ := Qbar * ‖v‖)
            ha0 ha1 ⟨k, by rw [hcdef]⟩ (by positivity) (by positivity) hρP hτg hGXle hGsub hPw
        have hAnInner : AnalyticAt ℂ (fun u : ℂ => fan a h ε' ((eqLam a : ℂ) * u)) v :=
          AnalyticAt.comp (g := fan a h ε') (f := fun u : ℂ => (eqLam a : ℂ) * u) (x := v)
            (hAn' ((eqLam a : ℂ) * v) hw_lt') (analyticAt_const.mul analyticAt_id)
        have hAnC : AnalyticAt ℂ (invBranch a s) G := FanTri.analytic_invBranch hGrad
        have hcomp : AnalyticAt ℂ (fun u : ℂ => invBranch a s (fan a h ε' ((eqLam a : ℂ) * u))) v :=
          AnalyticAt.comp (g := invBranch a s)
            (f := fun u : ℂ => fan a h ε' ((eqLam a : ℂ) * u)) (x := v) hAnC hAnInner
        refine ⟨?_, ?_, ?_⟩
        · have hfun : fan a h (s :: ε') =
              fun u : ℂ => invBranch a s (fan a h ε' ((eqLam a : ℂ) * u)) := rfl
          rw [hfun]
          exact hcomp
        · rw [hvF, hnew0]
          have hCx_bound : Cx * qw ^ 2 ≤ (1 - eqLam a) * P * ‖v‖ := by
            have h1 : qw ^ 2 ≤ (Qbar * ‖v‖) ^ 2 := pow_le_pow_left₀ hqw0 hqw_le 2
            have h4 : ‖v‖ ^ 2 ≤ δ * ‖v‖ := sq_le_mul_self (norm_nonneg v) hu_del
            calc Cx * qw ^ 2 ≤ Cx * (Qbar * ‖v‖) ^ 2 :=
                  mul_le_mul_of_nonneg_left h1 (le_of_lt hCxpos)
              _ = Cx * Qbar ^ 2 * ‖v‖ ^ 2 := by ring
              _ ≤ Cx * Qbar ^ 2 * (δ * ‖v‖) := mul_le_mul_of_nonneg_left h4 (by positivity)
              _ = (Cx * Qbar ^ 2 * δ) * ‖v‖ := by ring
              _ ≤ ((1 - eqLam a) * P) * ‖v‖ :=
                  mul_le_mul_of_nonneg_right hCxQbarδ (norm_nonneg v)
          calc ‖(invBranch a s G).1 - ((c' : ℝ) : ℂ)‖
              ≤ ‖G.1 - (c : ℂ)‖ + Cx * qw ^ 2 := hstepx'
            _ ≤ P * (eqLam a * ‖v‖) + (1 - eqLam a) * P * ‖v‖ := add_le_add hGX hCx_bound
            _ = P * ‖v‖ := by ring
        · rw [hvF]
          calc ‖(invBranch a s G).2‖ ≤ qw * ‖(invBranch a s G).1 - ((a / 2 : ℝ) : ℂ)‖ := hstepw
            _ = Qf ρ * ‖v‖ * ‖(invBranch a s G).1 - ((a / 2 : ℝ) : ℂ)‖ := by rw [hqwdef]
      exact ⟨fun v hv => (main v hv).1, hznew, hcknew, fun v hv => (main v hv).2.1,
        fun v hv => (main v hv).2.2⟩
  -- ============================ conclusion ============================
  refine ⟨δ, P, Qbar, hδpos, hPpos, hQbarpos, ?_⟩
  intro ε
  obtain ⟨hAn, -, -, hbX, hbW⟩ := key ε δ hδpos le_rfl
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' : ‖z‖ < δ := by
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    exact hAn z hz'
  · intro u hu
    have hu' : ‖u‖ < δ := by
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    refine ⟨hbX u hu', ?_⟩
    have hQle : Qf δ ≤ Qbar := by
      rw [hQbardef]; exact hQf_le1 δ hδ_le_1
    calc ‖(fan a h ε u).2‖ ≤ Qf δ * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := hbW u hu'
      _ ≤ Qbar * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right hQle (norm_nonneg u)

end

end Work.EQ.FanUniform
