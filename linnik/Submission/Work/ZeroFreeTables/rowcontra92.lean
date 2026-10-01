/-
# ZeroFreeTables.rowcontra92

The **Lemma 9.2 route** for the Table 10 rows.

Heath-Brown's Lemma 9.2 (in the engine form `hbLemma9_2_engine`) gives, for `χ₁` complex
and `χ₂ ∉ {χ₁^{±1}, χ₁^{±2}}`, the `F`-method inequality

`0 ≤ (k²+1/2){F(−λ₁) − F(λ₂−λ₁)} − 2k F(0) + f(0)(k²+4k+3/2)(c+ε)`.

At the tabulated points of HB's Table 9 the numerical certificates `P9F.rowcontra_*`
show that this inequality **fails**; since the Table 9 values dominate the Table 10
entries entry by entry, the same certificates rule out every Table 10 row with
`λ₁ ≤ p.1` and `λ₂ ≤ p.2`.

`rowcontra_direct` packages the engine + monotonicity + certificate into a single
contradiction; `rowcontra92` performs the (finite) case analysis over the twenty rows
of `hbTable10`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.P9F.hbLemma9_2_engine
import Submission.Work.ZeroFreeTables.P9F.table9_rows
import Submission.Work.ZeroFreeTables.P9F.table9_top
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **The engine-to-contradiction step of the Lemma 9.2 route.**
Given the numerical certificate `hcert` of a Table 9 row (a point `(a,c)` at which the
Lemma 9.2 inequality is contradicted) and the numerical slack inequality `hsl`, the
engine `hbLemma9_2_engine` (applied to HB Lemma 7.1's test function at `θ, lam` and the
budget `k`) yields `False` for every admissible pair with `λ₁ ≤ a`, `λ₂ ≤ c`. -/
theorem rowcontra_direct
    {θ lam k slack a c δ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ha2 : a ≤ 2) (hc2 : c ≤ 2)
    (hsl : (k ^ 2 + 4 * k + 3 / 2) * ((1 : ℝ) / 6 + 1 / 1000000) ≤ slack)
    (hcert : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1 / 2) * (P9F.La θ lam la1 - P9F.La θ lam (la1 - laj))
        - 2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack → False)
    (hL52 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1 : ℝ) / 6) (1 / 1000000) δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
      0 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ a → lamOf q ρ₂ ≤ c → False := by
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T θ lam hθ0 hθπ hlam) k ((1 : ℝ) / 6)
    (1 / 1000000) δ hk (by norm_num) hδ0 hδ1
  refine ⟨max qE P9F.Qsq, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
    hlam1nn hle1 hle2
  have hqE' : qE ≤ q := le_trans (le_max_left _ _) hq
  have hqS' : P9F.Qsq ≤ q := le_trans (le_max_right _ _) hq
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := P9F.sqrt_loglog_ge_two hqS'
  have h2₁ : lamOf q ρ₁ ≤ 2 := by linarith
  have h2₂ : lamOf q ρ₂ ≤ 2 := by linarith
  have hE := hqE q hqE' χ₁ χ₂ ρ₁ ρ₂ (fun χ _ hχ => hL52 q χ hχ)
    hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h2₁ h2₂ hsq
  rw [P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (-(lamOf q ρ₁)),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (lamOf q ρ₂ - lamOf q ρ₁),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam 0] at hE
  simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
  have hf0 : 0 ≤ tf71f θ lam 0 := tf71f_nonneg θ lam hθ0 hθπ hlam 0
  have hcore : 0 ≤ (k ^ 2 + 1 / 2) *
        (P9F.La θ lam (lamOf q ρ₁) - P9F.La θ lam (lamOf q ρ₁ - lamOf q ρ₂))
      - 2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack := by
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  exact hcert hlam1nn hle1 hle2 hcore

/-- The **Lemma 9.2 route** for the Table 10 rows: if the second zero belongs to a character
`χ₂` with `χ₁² ∉ {χ₀, χ₂, χ₂⁻¹}` then HB Lemma 9.2 applies; since Table 9's tabulated values
dominate Table 10's entry by entry, the Table-9 certificates (P9F's `rowcontra_*`) rule out
`λ₂ ≤ p.2`.  `hL52` is the log-derivative input in the form consumed by the engines. -/
theorem rowcontra92 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable10)
    (ha : (36/100 : ℝ) ≤ p.1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → Work.LinnikContract.IsZ χ₁ ρ₁ →
      Work.LinnikContract.IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
      348/1000 ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
      Work.LinnikContract.lamOf q ρ₂ ≤ p.2 → False := by
  simp only [tableR, hbTable10, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    | h14 | h15 | h16 | h17 | h18 | h19
  · subst h0; exfalso; norm_num at ha
  · subst h1
    have hθ01 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ1 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ1 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (21/500:ℝ))
      (k := (407/500:ℝ)) (slack := (338664717947/375000000000:ℝ)) (a := (9/25:ℝ)) (c := (123/100:ℝ))
      hθ01 hθπ1 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_036_123 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ1 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h2
    have hθ02 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ2 : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ2 : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (24:ℝ)) (lam := (9/200:ℝ))
      (k := (817/1000:ℝ)) (slack := (1358882154467/1500000000000:ℝ)) (a := (19/50:ℝ)) (c := (1181/1000:ℝ))
      hθ02 hθπ2 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_038_1181 (θ := Real.arctan (24:ℝ)) P9F.arctan24_bounds.1 P9F.arctan24_bounds.2
          htanθ2 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h3
    have hθ03 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ3 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ3 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (11/250:ℝ))
      (k := (41/50:ℝ)) (slack := (3407774843/3750000000:ℝ)) (a := (2/5:ℝ)) (c := (227/200:ℝ))
      hθ03 hθπ3 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_04_1135 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ3 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h4
    have hθ04 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ4 : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ4 : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (24:ℝ)) (lam := (23/500:ℝ))
      (k := (411/500:ℝ)) (slack := (113827579921/125000000000:ℝ)) (a := (21/50:ℝ)) (c := (547/500:ℝ))
      hθ04 hθπ4 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_042_1094 (θ := Real.arctan (24:ℝ)) P9F.arctan24_bounds.1 P9F.arctan24_bounds.2
          htanθ4 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h5
    have hθ05 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ5 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ5 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ))
      (k := (33/40:ℝ)) (slack := (730755329/800000000:ℝ)) (a := (11/25:ℝ)) (c := (211/200:ℝ))
      hθ05 hθπ5 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_044_1055 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ5 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h6
    have hθ06 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ6 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ6 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ))
      (k := (207/250:ℝ)) (slack := (28633458849/31250000000:ℝ)) (a := (23/50:ℝ)) (c := (509/500:ℝ))
      hθ06 hθπ6 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_046_1018 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ6 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h7
    have hθ07 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ7 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ7 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (47/1000:ℝ))
      (k := (104/125:ℝ)) (slack := (21563532323/23437500000:ℝ)) (a := (12/25:ℝ)) (c := (123/125:ℝ))
      hθ07 hθπ7 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_048_0984 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ7 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h8
    have hθ08 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ8 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ8 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (417/500:ℝ)) (slack := (115241590889/125000000000:ℝ)) (a := (1/2:ℝ)) (c := (119/125:ℝ))
      hθ08 hθπ8 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_05_0952 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ8 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h9
    have hθ09 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ9 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ9 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (209/250:ℝ)) (slack := (28869460681/31250000000:ℝ)) (a := (13/25:ℝ)) (c := (461/500:ℝ))
      hθ09 hθπ9 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_052_0922 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ9 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h10
    have hθ010 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ10 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ10 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ))
      (k := (419/500:ℝ)) (slack := (347142783683/375000000000:ℝ)) (a := (27/50:ℝ)) (c := (893/1000:ℝ))
      hθ010 hθπ10 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_054_0893 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ10 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h11
    have hθ011 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ11 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ11 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (49/1000:ℝ))
      (k := (21/25:ℝ)) (slack := (72469279/78125000:ℝ)) (a := (14/25:ℝ)) (c := (433/500:ℝ))
      hθ011 hθπ11 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_056_0866 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ11 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h12
    have hθ012 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ12 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ12 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ))
      (k := (421/500:ℝ)) (slack := (116187598241/125000000000:ℝ)) (a := (29/50:ℝ)) (c := (21/25:ℝ))
      hθ012 hθπ12 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_058_084 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ12 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h13
    have hθ013 : 0 < Real.arctan (15:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ13 : Real.arctan (15:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ13 : Real.tan (Real.arctan (15:ℝ)) = (15/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (15:ℝ)) (lam := (41/500:ℝ))
      (k := (211/250:ℝ)) (slack := (87318387563/93750000000:ℝ)) (a := (3/5:ℝ)) (c := (102/125:ℝ))
      hθ013 hθπ13 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_06_0816 (θ := Real.arctan (15:ℝ)) P9F.arctan15_bounds.1 P9F.arctan15_bounds.2
          htanθ13 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h14
    have hθ014 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ14 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ14 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ))
      (k := (847/1000:ℝ)) (slack := (1401362484227/1500000000000:ℝ)) (a := (31/50:ℝ)) (c := (99/125:ℝ))
      hθ014 hθπ14 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_062_0792 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ14 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h15
    have hθ015 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ15 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ15 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (51/1000:ℝ))
      (k := (849/1000:ℝ)) (slack := (468070168801/500000000000:ℝ)) (a := (16/25:ℝ)) (c := (77/100:ℝ))
      hθ015 hθπ15 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_064_077 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ15 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h16
    have hθ016 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ16 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ16 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (213/250:ℝ)) (slack := (29343464369/31250000000:ℝ)) (a := (33/50:ℝ)) (c := (187/250:ℝ))
      hθ016 hθπ16 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_066_0748 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ16 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h17
    have hθ017 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ17 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ17 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (427/500:ℝ)) (slack := (117611609329/125000000000:ℝ)) (a := (17/25:ℝ)) (c := (91/125:ℝ))
      hθ017 hθπ17 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_068_0728 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ17 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h18
    have hθ018 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ18 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ18 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ)) (a := (7/10:ℝ)) (c := (177/250:ℝ))
      hθ018 hθπ18 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_07_0708 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ18 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)
  · subst h19
    have hθ019 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ19 : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htanθ19 : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by
      rw [Real.tan_arctan]; norm_num
    obtain ⟨q₀, hq₀⟩ := rowcontra_direct (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ))
      (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ)) (a := (88/125:ℝ)) (c := (88/125:ℝ))
      hθ019 hθπ19 (by norm_num) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num) (by norm_num)
      (fun {la1 laj} hnn hle hlc hcore =>
        P9F.rowcontra_0704_0704 (θ := Real.arctan (25:ℝ)) P9F.arctan25_bounds.1 P9F.arctan25_bounds.2
          htanθ19 hnn hle hlc hcore)
      hL52
    refine ⟨q₀, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE h348 hle1 hle2
    exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ₁ hZ₂ hχ₁ hχ₂ hneA hneB hneC hneD hneE
      (by linarith) (by linarith) (by linarith)

end Work.ZeroFreeTables
