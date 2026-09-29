import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMContract.Components
import Submission.Work.TMContract.Gluing.liouville_squeeze
import Submission.Work.TMContract.Gluing.liouville_nearest_int

open Filter Topology Set

namespace Work.TMContract.Gluing

theorem liouville_of_aux (h13 : Work.TMContract.P_FictLip) (h14 : Work.TMContract.P_GapBound)
    (hslope : ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b →
      Set.Ioo a b ⊆ Work.TMContract.amoSpec α lam →
      ∃ c d c₀ : ℝ, a < c ∧ c < d ∧ d < b ∧ 0 < c₀ ∧
        ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, x < y →
          c₀ * (y - x) ≤ Work.TMContract.ids α lam y - Work.TMContract.ids α lam x) :
    Work.TMContract.P_Liouville := by
  intro α b lam hirr hliou hgt hle
  intro hInt
  obtain ⟨a, b₀, hab, hsub⟩ := hInt
  have hlam_pos : 0 < lam := lt_of_lt_of_le (Real.exp_pos _) (le_of_lt hgt)
  have hb_pos : 0 < b := by
    have h1 : Real.exp (-(2 * b)) < Real.exp 0 := by
      calc Real.exp (-(2 * b)) < lam := hgt
        _ ≤ 1 := hle
        _ = Real.exp 0 := by rw [Real.exp_zero]
    have h2 : -(2 * b) < 0 := Real.exp_lt_exp.mp h1
    linarith
  have hloglam : -(2 * b) < Real.log lam := by
    have h1 := Real.log_lt_log (Real.exp_pos (-(2 * b))) hgt
    rwa [Real.log_exp] at h1
  obtain ⟨c, d, c₀, hac, hcd, hdb, hc₀, hslopeB⟩ :=
    hslope α lam a b₀ hirr hlam_pos hle hab hsub
  have hIcc_sub : Set.Icc c d ⊆ Work.TMContract.amoSpec α lam :=
    fun x hx => hsub ⟨lt_of_lt_of_le hac hx.1, lt_of_le_of_lt hx.2 hdb⟩
  obtain ⟨K, hK⟩ := h13 α lam a b₀ hirr hlam_pos hle hab hsub c d hac hdb
  have hK_nonneg : 0 ≤ K := by
    have hc_mem : c ∈ Set.Icc c d := ⟨le_refl c, le_of_lt hcd⟩
    have h0 := hK (α + 1) c hc_mem
    simp only [add_sub_cancel_left, abs_one, mul_one] at h0
    linarith [abs_nonneg (Work.TMContract.ids (α + 1) lam c - Work.TMContract.ids α lam c)]
  set ε : ℝ := (Real.log lam + 2 * b) / 4 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have hbε : Real.exp (-(2 * b) + 2 * ε) < lam := by
    have heq : -(2 * b) + 2 * ε = (Real.log lam - 2 * b) / 2 := by rw [hε_def]; ring
    rw [heq]
    calc Real.exp ((Real.log lam - 2 * b) / 2) < Real.exp (Real.log lam) :=
          Real.exp_lt_exp.mpr (by linarith)
      _ = lam := Real.exp_log hlam_pos
  obtain ⟨δ, hδ_pos, Q, hQ⟩ := h14 α lam c d hirr hlam_pos hle hcd hIcc_sub ε hε_pos
  have hfreq1 := liouville_nearest_int hb_pos hliou hδ_pos Q
  have hfreq2 : ∃ᶠ q : ℕ in Filter.atTop,
      c₀ * Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2) ≤ 2 * K * Real.exp (-(b * q)) := by
    refine hfreq1.mono ?_
    intro q hq
    obtain ⟨hqQ, hqδ, hqb⟩ := hq
    have hq1 : 1 ≤ q := le_trans (le_max_right Q 1) hqQ
    have hQq : Q ≤ q := le_trans (le_max_left Q 1) hqQ
    set p : ℤ := round ((q : ℝ) * α) with hp
    have hpR : (p : ℝ) = (round ((q : ℝ) * α) : ℝ) := by rw [hp]
    have hδq : |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) := by rw [hpR]; exact hqδ
    have hbq : |α - (p : ℝ) / (q : ℝ)| < Real.exp (-(b * q)) / (q : ℝ) := by
      rw [hpR]; exact hqb
    obtain ⟨a', b', hca', hab', hb'd, hineq, heq⟩ := hQ p q hQq hδq
    have ha'mem : a' ∈ Set.Icc c d := ⟨hca', le_trans (le_of_lt hab') hb'd⟩
    have hb'mem : b' ∈ Set.Icc c d := ⟨le_trans hca' (le_of_lt hab'), hb'd⟩
    have hsl := hslopeB a' ha'mem b' hb'mem hab'
    have hLa : |Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam a' - Work.TMContract.ids α lam a'|
        ≤ K * |(p : ℝ) / (q : ℝ) - α| := hK ((p : ℝ) / (q : ℝ)) a' ha'mem
    have hLb : |Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam b' - Work.TMContract.ids α lam b'|
        ≤ K * |(p : ℝ) / (q : ℝ) - α| := hK ((p : ℝ) / (q : ℝ)) b' hb'mem
    have h1 : Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam a' - Work.TMContract.ids α lam a'
        ≤ K * |α - (p : ℝ) / (q : ℝ)| := by
      calc Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam a' - Work.TMContract.ids α lam a'
          ≤ |Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam a' - Work.TMContract.ids α lam a'| :=
            le_abs_self _
        _ ≤ K * |(p : ℝ) / (q : ℝ) - α| := hLa
        _ = K * |α - (p : ℝ) / (q : ℝ)| := by rw [abs_sub_comm]
    have h2 : Work.TMContract.ids α lam b' - Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam b'
        ≤ K * |α - (p : ℝ) / (q : ℝ)| := by
      calc Work.TMContract.ids α lam b' - Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam b'
          = -(Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam b' - Work.TMContract.ids α lam b') := by
            ring
        _ ≤ |Work.TMContract.ids ((p : ℝ) / (q : ℝ)) lam b' - Work.TMContract.ids α lam b'| :=
            neg_le_abs _
        _ ≤ K * |(p : ℝ) / (q : ℝ) - α| := hLb
        _ = K * |α - (p : ℝ) / (q : ℝ)| := by rw [abs_sub_comm]
    have hmid : Work.TMContract.ids α lam b' - Work.TMContract.ids α lam a'
        ≤ 2 * (K * |α - (p : ℝ) / (q : ℝ)|) := by linarith [h1, h2, heq]
    have hstep : 2 * (K * |α - (p : ℝ) / (q : ℝ)|) ≤ 2 * K * Real.exp (-(b * q)) := by
      have hA : K * |α - (p : ℝ) / (q : ℝ)| ≤ K * (Real.exp (-(b * q)) / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hbq) hK_nonneg
      have hB : K * (Real.exp (-(b * q)) / (q : ℝ)) ≤ K * Real.exp (-(b * q)) :=
        mul_le_mul_of_nonneg_left
          (div_le_self (Real.exp_pos (-(b * q))).le (by exact_mod_cast hq1)) hK_nonneg
      calc 2 * (K * |α - (p : ℝ) / (q : ℝ)|) ≤ 2 * (K * (Real.exp (-(b * q)) / (q : ℝ))) := by
            linarith [hA]
        _ ≤ 2 * (K * Real.exp (-(b * q))) := by linarith [hB]
        _ = 2 * K * Real.exp (-(b * q)) := by ring
    calc c₀ * Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2)
        = c₀ * (Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2)) := by ring
      _ ≤ c₀ * (b' - a') := mul_le_mul_of_nonneg_left hineq hc₀.le
      _ ≤ Work.TMContract.ids α lam b' - Work.TMContract.ids α lam a' := hsl
      _ ≤ 2 * (K * |α - (p : ℝ) / (q : ℝ)|) := hmid
      _ ≤ 2 * K * Real.exp (-(b * q)) := hstep
  exact liouville_squeeze hc₀ hlam_pos hε_pos hbε hK_nonneg hfreq2

end Work.TMContract.Gluing
