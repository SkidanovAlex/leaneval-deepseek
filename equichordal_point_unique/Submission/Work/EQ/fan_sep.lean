import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.step_w
import Submission.Work.EQ.FanSep.step_x

namespace Work.EQ

open Complex

set_option maxHeartbeats 1000000

noncomputable section

/-- The stable fan restated one letter at a time (definitional unfolding). -/
lemma fan_nil (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : fan a h [] u = germC a h u := rfl

lemma fan_cons (a : ℝ) (h : ℂ → ℂ) (s : Bool) (ε : List Bool) (u : ℂ) :
    fan a h (s :: ε) u = invBranch a s (fan a h ε ((eqLam a : ℂ) * u)) := rfl

/-- `‖x‖ - ‖y‖ ≤ ‖x + y‖`. -/
lemma norm_sub_le_norm_add (x y : ℂ) : ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
  have h := norm_sub_le (x + y) y
  rw [add_sub_cancel_right] at h
  linarith

/-- `l ≤ 1`, `0 ≤ r`, `r ≤ d` give `l * r ≤ d`. -/
lemma mul_le_of_le_one {l r d : ℝ} (hl : l ≤ 1) (hr : 0 ≤ r) (hrd : r ≤ d) : l * r ≤ d := by
  have h1 : l * r ≤ 1 * r := mul_le_mul_of_nonneg_right hl hr
  rw [one_mul] at h1
  linarith

/-- `0 ≤ x ≤ d` gives `x ^ 2 ≤ d * x`. -/
lemma sq_le_mul_self {x d : ℝ} (hx : 0 ≤ x) (h : x ≤ d) : x ^ 2 ≤ d * x := by
  nlinarith [mul_le_mul_of_nonneg_right h hx]

/-- **Uniform fan separation (Rychlik Theorem 7(1) / Lemma 14, the piece needed by
`H0_invParam_ge`).**

`Work.EQ.fan a h ε u` is Rychlik's stable fan (`fan a h [] u = germC a h u`,
`fan a h (s :: ε) u = invBranch a s (fan a h ε (eqLam a * u))`, see `DefsCore.lean`); `a ∈ (0,1)`
and `h` is a stable germ (`IsStableGerm a h r`: holomorphic near `0`, `h 0 = 0`, `h' 0 = -1`,
real on the real axis, solving the equichordal equation `GermFE`).

Claim: there is `δ > 0` such that for every finite branch word `ε` and every `‖u‖ < δ`:
* the fan centre `fan a h ε 0` lies on the real axis (`(·).2 = 0`) and at an axis point of the
  coset `-1/2 + 2ℤ`;
* the whole image of the disc `B(0,δ)` stays within distance `1/4` (first coordinate) of the centre;
* the second coordinate stays within one quarter of the distance to `O₂ = a/2` (the
  semi-projective bound `|w| ≤ 1/4`, `w = y/(x - a/2)`).

Everything is uniform in the word `ε`; no hypothesis on the length of `ε` is allowed, and that
uniformity is the content of the lemma. Reference: Rychlik, *A complete solution of the
Equichordal Point Problem*, Invent. Math. 129 (1997), proof of Theorem 7(1) (pp. 34-36) and
Lemma 14 (§5.14). -/
theorem fan_sep {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δ →
      (fan a h ε 0).2 = 0 ∧ (∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k) ∧
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ 1 / 4 ∧
      ‖(fan a h ε u).2‖ ≤ ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ / 4 := by
  -- ============================ inputs ============================
  obtain ⟨δg, pg, qg, hδgpos, hpgpos, hqgpos, hgerm⟩ := FanSep.germ_lip ha0 ha1 hh
  obtain ⟨haxis1, haxis2⟩ := FanSep.axis_walk ha0 ha1 hh
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
  -- choose δ
  set δ : ℝ := min δg (min 1 (min ((1 - eqLam a) * P / (4 * Cx * Qbar ^ 2))
      (min ((1 - a) / (8 * P)) (min (1 / (4 * P)) (1 / (4 * Qbar)))))) with hδdef
  have hδ_le_δg : δ ≤ δg := by rw [hδdef]; exact min_le_left _ _
  have hδ_le_1 : δ ≤ 1 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_A : δ ≤ (1 - eqLam a) * P / (4 * Cx * Qbar ^ 2) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_B : δ ≤ (1 - a) / (8 * P) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_le_C : δ ≤ 1 / (4 * P) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδ_le_D : δ ≤ 1 / (4 * Qbar) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min hδgpos (lt_min one_pos (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))))
    · exact div_pos (mul_pos h1mlam hPpos) (by positivity)
    · exact div_pos h1a (by positivity)
    · exact div_pos one_pos (by positivity)
    · exact div_pos one_pos (by positivity)
  have hPδ : P * δ ≤ (1 - a) / 8 := by
    have h := mul_le_mul_of_nonneg_left hδ_le_B (le_of_lt hPpos)
    rw [show P * ((1 - a) / (8 * P)) = (1 - a) / 8 by field_simp] at h
    exact h
  have hCxQbarδ : Cx * Qbar ^ 2 * δ ≤ (1 - eqLam a) * P := by
    have hpos : (0 : ℝ) < 4 * Cx * Qbar ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hδ_le_A (le_of_lt hpos)
    rw [show 4 * Cx * Qbar ^ 2 * ((1 - eqLam a) * P / (4 * Cx * Qbar ^ 2))
          = (1 - eqLam a) * P by field_simp] at h
    have hX : 0 ≤ Cx * Qbar ^ 2 * δ := by positivity
    nlinarith only [h, hX]
  have hPδ4 : P * δ ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hδ_le_C (le_of_lt hPpos)
    rw [show P * (1 / (4 * P)) = 1 / 4 by field_simp] at h
    exact h
  have hQδ4 : Qbar * δ ≤ 1 / 4 := by
    have h3 := mul_le_mul_of_nonneg_left hδ_le_D (le_of_lt hQbarpos)
    rw [show Qbar * (1 / (4 * Qbar)) = 1 / 4 by field_simp] at h3
    exact h3
  -- ============================ majorant induction ============================
  have key : ∀ ε : List Bool, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ → ∀ u : ℂ, ‖u‖ < ρ →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ P * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Qf ρ * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
    intro ε
    induction ε with
    | nil =>
      intro ρ hρ0 hρδ u hu
      rw [fan_nil, fan_nil]
      obtain ⟨hg1, hg2⟩ := hgerm u (lt_of_lt_of_le hu (le_trans hρδ hδ_le_δg))
      have h0 : (germC a h 0).1 = ((-1 / 2 : ℝ) : ℂ) := by
        rw [germC_value ha0 ha1 hh]
        norm_num
      rw [h0]
      constructor
      · calc ‖(germC a h u).1 - ((-1 / 2 : ℝ) : ℂ)‖ ≤ pg * ‖u‖ := hg1
          _ ≤ P * ‖u‖ := mul_le_mul_of_nonneg_right hPgP (norm_nonneg u)
      · calc ‖(germC a h u).2‖
            ≤ qg * ‖u‖ * ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ := hg2
          _ ≤ Qf ρ * ‖u‖ * ‖(germC a h u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_right (hQf_qg ρ (le_of_lt hρ0)) (norm_nonneg u)
    | cons s ε' ih =>
      intro ρ hρ0 hρδ u hu
      rw [fan_cons, fan_cons]
      simp only [mul_zero]
      set F : ℂ × ℂ := fan a h ε' ((eqLam a : ℂ) * u) with hFdef
      -- centre data of the shorter word
      obtain ⟨hc2, k, hck⟩ := haxis2 ε'
      set c : ℝ := -1 / 2 + 2 * (k : ℝ) with hcdef
      have hcentre : (fan a h ε' 0).1 = (c : ℂ) := by
        rw [hcdef]; push_cast; rw [hck]
      have hc_b : (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact (hcn_dist k).1
      have hc_b2 : (1 - a) / 2 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact (hcn_dist k).2
      have hc_ext : eqLam a * ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ ≤
          ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
        rw [hcdef]; exact hcn_ext k
      have hcc_pos : 0 < ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ := by
        linarith only [hc_b, h1a]
      have hcc_ne : ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ ≠ 0 := ne_of_gt hcc_pos
      -- IH at the smaller radius
      have hw_norm : ‖(eqLam a : ℂ) * u‖ = eqLam a * ‖u‖ := by
        rw [norm_mul, show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from
          RCLike.norm_ofReal (K := ℂ) (eqLam a), abs_of_pos hlam0]
      have hw_lt : ‖(eqLam a : ℂ) * u‖ < eqLam a * ρ := by
        rw [hw_norm]; exact mul_lt_mul_of_pos_left hu hlam0
      have hlamrho0 : 0 < eqLam a * ρ := mul_pos hlam0 hρ0
      have hlamrhodel : eqLam a * ρ ≤ δ :=
        mul_le_of_le_one (le_of_lt hlam1) (le_of_lt hρ0) hρδ
      obtain ⟨ih1, ih2⟩ := ih (eqLam a * ρ) hlamrho0 hlamrhodel ((eqLam a : ℂ) * u) hw_lt
      rw [← hFdef] at ih1 ih2
      have ih1' : ‖F.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖u‖) := by
        rw [hcentre, hw_norm] at ih1
        exact ih1
      have ih2' : ‖F.2‖ ≤ Qf (eqLam a * ρ) * (eqLam a * ‖u‖) *
          ‖F.1 - ((a / 2 : ℝ) : ℂ)‖ := by
        rw [hw_norm] at ih2
        exact ih2
      -- basic bounds on the point F = fan a h ε' (λ u)
      have hu_rho : ‖u‖ ≤ ρ := le_of_lt hu
      have hu_del : ‖u‖ ≤ δ := le_trans hu_rho hρδ
      have hQ1 : ‖F.1 - (c : ℂ)‖ ≤ (1 - a) / 8 := by
        have h1 : eqLam a * ‖u‖ ≤ δ :=
          mul_le_of_le_one (le_of_lt hlam1) (norm_nonneg u) hu_del
        calc ‖F.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖u‖) := ih1'
          _ ≤ P * δ := mul_le_mul_of_nonneg_left h1 (le_of_lt hPpos)
          _ ≤ (1 - a) / 8 := hPδ
      have hQb_pos : 0 < ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by
        have heq : ((c : ℂ) + ((a / 2 : ℝ) : ℂ)) =
            (F.1 + ((a / 2 : ℝ) : ℂ)) - (F.1 - (c : ℂ)) := by ring
        have h1 : ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ ≤
            ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ + ‖F.1 - (c : ℂ)‖ := by
          rw [heq]; exact norm_sub_le _ _
        linarith only [h1, hc_b, hQ1, h1a]
      have hQb_ne' : F.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        intro hcon
        have hlt := hQb_pos
        rw [hcon, norm_zero] at hlt
        exact lt_irrefl 0 hlt
      -- the semi-projective size
      set qw : ℝ := Qf ρ * ‖u‖ with hqwdef
      have hqw0 : 0 ≤ qw := by
        rw [hqwdef]; exact mul_nonneg (le_of_lt (hQfpos ρ)) (norm_nonneg u)
      have hqw_le : qw ≤ Qbar * ‖u‖ := by
        rw [hqwdef]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
        exact hQf_le1 ρ (le_trans hρδ hδ_le_1)
      have hqw12 : qw ≤ 1 / 2 := by
        calc qw ≤ Qbar * ‖u‖ := hqw_le
          _ ≤ Qbar * δ := mul_le_mul_of_nonneg_left hu_del (le_of_lt hQbarpos)
          _ ≤ 1 / 4 := hQδ4
          _ ≤ 1 / 2 := by norm_num
      -- the transfer of the semi-projective bound
      have hcorr : ‖F.1 - (c : ℂ)‖ ≤ P * (eqLam a * ρ) := by
        calc ‖F.1 - (c : ℂ)‖ ≤ P * (eqLam a * ‖u‖) := ih1'
          _ ≤ P * (eqLam a * ρ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu_rho (le_of_lt hlam0))
                (le_of_lt hPpos)
      have hlam_ratio : eqLam a * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
          ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) ≤ 1 := by
        rw [← mul_div_assoc]
        exact (div_le_one hcc_pos).mpr hc_ext
      have hQ2 : ‖F.2‖ ≤ qw * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by
        rw [hqwdef]
        have hdiv : ‖F.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
            (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
              (1 + CA * ‖F.1 - (c : ℂ)‖) * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by
          have hkey := hstepw2 hc_b hc_b2 hQ1
          have h2 := mul_le_mul_of_nonneg_right hkey
            (by positivity : (0 : ℝ) ≤ 1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)
          have e1 : (‖F.1 - ((a / 2 : ℝ) : ℂ)‖ * ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) =
              ‖F.1 - ((a / 2 : ℝ) : ℂ)‖ := by
            field_simp
          have e2 : (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ *
                ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ * (1 + CA * ‖F.1 - (c : ℂ)‖)) *
                (1 / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) =
              (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 + CA * ‖F.1 - (c : ℂ)‖) * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by
            field_simp
            try ring
          rw [e1, e2] at h2
          exact h2
        have hfac : 0 ≤ Qf (eqLam a * ρ) * (eqLam a * ‖u‖) :=
          mul_nonneg (le_of_lt (hQfpos _)) (mul_nonneg (le_of_lt hlam0) (norm_nonneg u))
        -- abbreviations for the final comparison
        have hW : 0 ≤ ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := norm_nonneg _
        have hr0 : 0 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ :=
          div_nonneg (norm_nonneg _) (le_of_lt hcc_pos)
        have hA : 1 + CA * ‖F.1 - (c : ℂ)‖ ≤ 1 + CA * (P * (eqLam a * ρ)) := by
          have := mul_le_mul_of_nonneg_left hcorr (le_of_lt hCApos)
          linarith only [this]
        have hB2 : Qf (eqLam a * ρ) * (1 + CA * (P * (eqLam a * ρ))) ≤ Qf ρ := by
          simpa only [mul_assoc] using hQf_step ρ
        have hB : eqLam a * ‖u‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
            ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) ≤ ‖u‖ := by
          calc eqLam a * ‖u‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                  ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)
              = ‖u‖ * (eqLam a * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                  ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)) := by ring
            _ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left hlam_ratio (norm_nonneg u)
            _ = ‖u‖ := mul_one _
        -- substitute the corrected ratio bound into the inductive bound
        have hdiv' : ‖F.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
            ((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
              (1 + CA * (P * (eqLam a * ρ)))) * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ :=
          le_trans hdiv (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hr0) hW)
        have hstep1 : Qf (eqLam a * ρ) * (eqLam a * ‖u‖) * ‖F.1 - ((a / 2 : ℝ) : ℂ)‖ ≤
            Qf (eqLam a * ρ) * (eqLam a * ‖u‖) *
              (((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 + CA * (P * (eqLam a * ρ)))) * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hdiv' hfac
        refine le_trans (le_trans ih2' hstep1) ?_
        calc Qf (eqLam a * ρ) * (eqLam a * ‖u‖) *
              (((‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ / ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) *
                (1 + CA * (P * (eqLam a * ρ)))) * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖)
            = (eqLam a * ‖u‖ * (‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ /
                ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)) *
                (Qf (eqLam a * ρ) * (1 + CA * (P * (eqLam a * ρ)))) *
                  ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
          _ ≤ ‖u‖ * Qf ρ * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by
              refine mul_le_mul ?_ (le_refl _) hW ?_
              · exact mul_le_mul hB hB2 (le_of_lt (mul_pos (hQfpos _) (by positivity)))
                  (norm_nonneg u)
              · positivity
          _ = Qf ρ * ‖u‖ * ‖F.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
      -- step lemmas
      have hstepx := hCx s c F qw hc_b hQ1 hQ2 hqw12
      have hstepw := hstepw1 (Q := F) (qw := qw) s hQb_ne' hqw0 hqw12 hQ2
      have hCx_bound : Cx * qw ^ 2 ≤ (1 - eqLam a) * P * ‖u‖ := by
        have h1 : qw ^ 2 ≤ (Qbar * ‖u‖) ^ 2 := pow_le_pow_left₀ hqw0 hqw_le 2
        have h4 : ‖u‖ ^ 2 ≤ δ * ‖u‖ := sq_le_mul_self (norm_nonneg u) hu_del
        calc Cx * qw ^ 2 ≤ Cx * (Qbar * ‖u‖) ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hCxpos)
          _ = Cx * Qbar ^ 2 * ‖u‖ ^ 2 := by ring
          _ ≤ Cx * Qbar ^ 2 * (δ * ‖u‖) := mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = (Cx * Qbar ^ 2 * δ) * ‖u‖ := by ring
          _ ≤ ((1 - eqLam a) * P) * ‖u‖ :=
              mul_le_mul_of_nonneg_right hCxQbarδ (norm_nonneg u)
      have hnew : (invBranch a s (fan a h ε' 0)).1 =
          (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ) := by
        rw [show fan a h ε' 0 = ((c : ℂ), (0 : ℂ)) from Prod.ext hcentre hc2]
        have hne : c + a / 2 ≠ 0 := by
          intro hcon
          have hz : ((c : ℂ) + ((a / 2 : ℝ) : ℂ)) = 0 := by
            rw [← Complex.ofReal_add, hcon, Complex.ofReal_zero]
          have hlt := hcc_pos
          rw [hz, norm_zero] at hlt
          exact lt_irrefl 0 hlt
        have h := haxis1 (s := s) hne
        rw [h]
        rfl
      constructor
      · calc ‖(invBranch a s F).1 - (invBranch a s (fan a h ε' 0)).1‖
            = ‖(invBranch a s F).1 - (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)‖ := by
              rw [hnew]
          _ ≤ ‖F.1 - (c : ℂ)‖ + Cx * qw ^ 2 := hstepx
          _ ≤ P * (eqLam a * ‖u‖) + (1 - eqLam a) * P * ‖u‖ := add_le_add ih1' hCx_bound
          _ = P * ‖u‖ := by ring
      · calc ‖(invBranch a s F).2‖ ≤ qw * ‖(invBranch a s F).1 - ((a / 2 : ℝ) : ℂ)‖ :=
            hstepw
          _ ≤ Qf ρ * ‖u‖ * ‖(invBranch a s F).1 - ((a / 2 : ℝ) : ℂ)‖ :=
              le_of_eq rfl
  -- ============================ conclusion ============================
  refine ⟨δ, hδpos, ?_⟩
  intro ε u hu
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
  obtain ⟨hk1, hk2⟩ := key ε δ hδpos le_rfl u hu
  obtain ⟨hz, k, hk'⟩ := haxis2 ε
  refine ⟨hz, ⟨k, hk'⟩, ?_, ?_⟩
  · calc ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ P * ‖u‖ := hk1
      _ ≤ P * δ := mul_le_mul_of_nonneg_left (le_of_lt hu) (le_of_lt hPpos)
      _ ≤ 1 / 4 := hPδ4
  · calc ‖(fan a h ε u).2‖ ≤ Qf δ * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := hk2
      _ ≤ Qbar * δ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul (hQf_le1 δ hδ_le_1) (le_of_lt hu) (norm_nonneg u)
              (le_of_lt hQbarpos)
      _ ≤ 1 / 4 * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hQδ4 (norm_nonneg _)
      _ = ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ / 4 := by ring

end

end Work.EQ
