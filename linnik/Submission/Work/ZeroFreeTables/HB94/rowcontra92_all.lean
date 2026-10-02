import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.P9F.hbLemma9_2_engine
import Submission.Work.ZeroFreeTables.P9F.table9_rows
import Submission.Work.ZeroFreeTables.P9F.table9_top
import Submission.Work.ZeroFreeTables.rowcontra92

namespace Work.ZeroFreeTables.HB94

/-!
# `ZeroFreeTables.HB94.rowcontra92q`

Thresholded (`∀ q ≥ q₀`) port of `Work.ZeroFreeTables.rowcontra92` together with its helper
`Work.ZeroFreeTables.rowcontra_direct`: the log-derivative input `L52Hyp` is only available for
moduli above a threshold `q₀`, and consequently the output threshold is `max q₀ (max qE Qsq)` in
`rowcontra_direct_q` and `q₀` is threaded through the twenty-row dispatch.  All numeric
parameters and the certificates `P9F.rowcontra_*` are unchanged from `rowcontra92`.
-/

open Work.LinnikContract

/-- **The engine-to-contradiction step, thresholded.**

`Work.ZeroFreeTables.rowcontra_direct` with the log-derivative supply `hL52` available only for
`q ≥ q₀`; the returned threshold dominates both `q₀` and the thresholds of the engine and of
`P9F.Qsq`. -/
theorem rowcontra_direct_q (q₀ : ℕ)
    {θ lam k slack a c δ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha2 : a ≤ 2) (hc2 : c ≤ 2)
    (hsl : (k ^ 2 + 4 * k + 3 / 2) * ((1 : ℝ) / 6 + 1 / 1000000) ≤ slack)
    (hcert : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1 / 2) * (P9F.La θ lam la1 - P9F.La θ lam (la1 - laj))
        - 2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack → False)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1 : ℝ) / 6) (1 / 1000000) δ) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
      0 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ a → lamOf q ρ₂ ≤ c → False := by
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T θ lam hθ0 hθπ hlam) k ((1 : ℝ) / 6)
    (1 / 1000000) δ hk (by norm_num) hδ0 hδ1
  refine ⟨max q₀ (max qE P9F.Qsq), le_max_left _ _, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
    hlam1nn hle1 hle2
  have hq0' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqE' : qE ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqS' : P9F.Qsq ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := P9F.sqrt_loglog_ge_two hqS'
  have h2₁ : lamOf q ρ₁ ≤ 2 := by linarith only [ha2, hle1]
  have h2₂ : lamOf q ρ₂ ≤ 2 := by linarith only [hc2, hle2]
  have hE := hqE q hqE' χ₁ χ₂ ρ₁ ρ₂ (fun χ _ hχ => hL52 q hq0' χ hχ)
    hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h2₁ h2₂ hsq
  rw [P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (-(lamOf q ρ₁)),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (lamOf q ρ₂ - lamOf q ρ₁),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam 0] at hE
  simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
  have hf0 : 0 ≤ tf71f θ lam 0 := tf71f_nonneg θ lam hθ0 hθπ hlam 0
  have hcore : 0 ≤ (k ^ 2 + 1 / 2) *
        (P9F.La θ lam (lamOf q ρ₁) - P9F.La θ lam (lamOf q ρ₁ - lamOf q ρ₂))
      - 2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack := by
    linarith only [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl), hf0, hsl]
  exact hcert hlam1nn hle1 hle2 hcore

/-- **Thresholded form of the Lemma 9.2 route** for the Table 10 rows: verbatim
`Work.ZeroFreeTables.rowcontra92` except that the log-derivative input is available only from a
threshold `q₀` (a *global* `∀ q` supply is unavailable in the workspace).  Port the proof of
`Work.ZeroFreeTables.rowcontra92` (`Submission/Work/ZeroFreeTables/rowcontra92.lean`) together with
its helper `Work.ZeroFreeTables.rowcontra_direct`: thread `q₀` through both, taking the threshold
as `max q₀ (max qE P9F.Qsq)` in `rowcontra_direct` and `max q₀ …` in the twenty-row dispatch.  The
certificates `P9F.rowcontra_*` and all the numeric parameters are unchanged. -/
theorem rowcontra92_all (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable10) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
      Work.LinnikContract.IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
      0 ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
      Work.LinnikContract.lamOf q ρ₂ ≤ p.2 → False := by
  simp only [tableR, hbTable10, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    | h14 | h15 | h16 | h17 | h18 | h19
  · -- the row `(34/100, 929/1000)`: the `(9/25, 123/100)` certificate covers it as well
    subst h0
    have hθ00 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ0 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ0 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (21/500:ℝ))
      (k := (407/500:ℝ)) (slack := (338664717947/375000000000:ℝ)) (a := (9/25:ℝ)) (c := (123/100:ℝ))
      hθ00 hθπ0 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_036_123 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ0 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      h0le (by linarith only [hδ0, hδ1, hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h1
    have hθ01 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ1 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ1 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (21/500:ℝ))
      (k := (407/500:ℝ)) (slack := (338664717947/375000000000:ℝ)) (a := (9/25:ℝ)) (c := (123/100:ℝ))
      hθ01 hθπ1 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_036_123 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ1 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h2
    have hθ02 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ2 : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ2 : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (24:ℝ)) (lam := (9/200:ℝ))
      (k := (817/1000:ℝ)) (slack := (1358882154467/1500000000000:ℝ)) (a := (19/50:ℝ)) (c := (1181/1000:ℝ))
      hθ02 hθπ2 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_038_1181 (θ := Real.arctan (24:ℝ)) P9F.arctan24_bounds.1 P9F.arctan24_bounds.2
          htanθ2 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h3
    have hθ03 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ3 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ3 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (11/250:ℝ))
      (k := (41/50:ℝ)) (slack := (3407774843/3750000000:ℝ)) (a := (2/5:ℝ)) (c := (227/200:ℝ))
      hθ03 hθπ3 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_04_1135 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ3 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h4
    have hθ04 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ4 : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ4 : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (24:ℝ)) (lam := (23/500:ℝ))
      (k := (411/500:ℝ)) (slack := (113827579921/125000000000:ℝ)) (a := (21/50:ℝ)) (c := (547/500:ℝ))
      hθ04 hθπ4 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_042_1094 (θ := Real.arctan (24:ℝ)) P9F.arctan24_bounds.1 P9F.arctan24_bounds.2
          htanθ4 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h5
    have hθ05 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ5 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ5 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ))
      (k := (33/40:ℝ)) (slack := (730755329/800000000:ℝ)) (a := (11/25:ℝ)) (c := (211/200:ℝ))
      hθ05 hθπ5 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_044_1055 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ5 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h6
    have hθ06 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ6 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ6 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ))
      (k := (207/250:ℝ)) (slack := (28633458849/31250000000:ℝ)) (a := (23/50:ℝ)) (c := (509/500:ℝ))
      hθ06 hθπ6 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_046_1018 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ6 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h7
    have hθ07 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ7 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ7 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (47/1000:ℝ))
      (k := (104/125:ℝ)) (slack := (21563532323/23437500000:ℝ)) (a := (12/25:ℝ)) (c := (123/125:ℝ))
      hθ07 hθπ7 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_048_0984 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ7 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h8
    have hθ08 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ8 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ8 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (417/500:ℝ)) (slack := (115241590889/125000000000:ℝ)) (a := (1/2:ℝ)) (c := (119/125:ℝ))
      hθ08 hθπ8 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_05_0952 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ8 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h9
    have hθ09 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ9 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ9 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (209/250:ℝ)) (slack := (28869460681/31250000000:ℝ)) (a := (13/25:ℝ)) (c := (461/500:ℝ))
      hθ09 hθπ9 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_052_0922 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ9 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h10
    have hθ010 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ10 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ10 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (419/500:ℝ)) (slack := (347142783683/375000000000:ℝ)) (a := (27/50:ℝ)) (c := (893/1000:ℝ))
      hθ010 hθπ10 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_054_0893 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ10 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h11
    have hθ011 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ11 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ11 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (49/1000:ℝ))
      (k := (21/25:ℝ)) (slack := (72469279/78125000:ℝ)) (a := (14/25:ℝ)) (c := (433/500:ℝ))
      hθ011 hθπ11 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_056_0866 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ11 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h12
    have hθ012 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ12 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ12 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ))
      (k := (421/500:ℝ)) (slack := (116187598241/125000000000:ℝ)) (a := (29/50:ℝ)) (c := (21/25:ℝ))
      hθ012 hθπ12 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_058_084 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ12 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h13
    have hθ013 : 0 < Real.arctan (15:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ13 : Real.arctan (15:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ13 : Real.tan (Real.arctan (15:ℝ)) = (15/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (15:ℝ)) (lam := (41/500:ℝ))
      (k := (211/250:ℝ)) (slack := (87318387563/93750000000:ℝ)) (a := (3/5:ℝ)) (c := (102/125:ℝ))
      hθ013 hθπ13 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_06_0816 (θ := Real.arctan (15:ℝ)) P9F.arctan15_bounds.1 P9F.arctan15_bounds.2
          htanθ13 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h14
    have hθ014 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ14 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ14 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ))
      (k := (847/1000:ℝ)) (slack := (1401362484227/1500000000000:ℝ)) (a := (31/50:ℝ)) (c := (99/125:ℝ))
      hθ014 hθπ14 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_062_0792 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ14 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h15
    have hθ015 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ15 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ15 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (51/1000:ℝ))
      (k := (849/1000:ℝ)) (slack := (468070168801/500000000000:ℝ)) (a := (16/25:ℝ)) (c := (77/100:ℝ))
      hθ015 hθπ15 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_064_077 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ15 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h16
    have hθ016 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ16 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ16 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (213/250:ℝ)) (slack := (29343464369/31250000000:ℝ)) (a := (33/50:ℝ)) (c := (187/250:ℝ))
      hθ016 hθπ16 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_066_0748 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ16 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h17
    have hθ017 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ17 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ17 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (427/500:ℝ)) (slack := (117611609329/125000000000:ℝ)) (a := (17/25:ℝ)) (c := (91/125:ℝ))
      hθ017 hθπ17 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_068_0728 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ17 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h18
    have hθ018 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ18 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ18 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ)) (a := (7/10:ℝ)) (c := (177/250:ℝ))
      hθ018 hθπ18 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_07_0708 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ18 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hle1]) (by linarith only [hδ0, hδ1, hle2])
  · subst h19
    have hθ019 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ19 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ19 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₁, hq₁ge, hq₁⟩ := rowcontra_direct_q q₀ (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ)) (a := (88/125:ℝ)) (c := (88/125:ℝ))
      hθ019 hθπ19 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_0704_0704 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ19 hnn hle hlc hcore)
      hL52
    refine ⟨q₁, hq₁ge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h0le hle1 hle2
    exact hq₁ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith only [h0le]) (by linarith only [hδ0, hδ1, hle1]) (by linarith only [hδ0, hδ1, hle2])


end Work.ZeroFreeTables.HB94
