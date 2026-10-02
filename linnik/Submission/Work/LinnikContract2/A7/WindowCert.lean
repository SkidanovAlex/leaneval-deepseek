/-
# LinnikContract2 — `A7/WindowCert.lean`

**The window certificates.**  For each of the five `lam₁`-ranges into which the *window*
`348/1000 ≤ lam₁ < 29/50` is divided, this file proves the §15 bound at the *narrow*
(working-region) minimiser, using `A7/window_step` (the §15 step with the honest zero count) and
the numeric certificates below.  The wide minimiser enters only through `(D2)` (whose hypothesis
is the wide one) and through the `Z3`/`Z4` clauses transferred by `A7/WindowAPI.lean`.

The parameters (`Λ`, the Table 13 column, the number of layers `s`, the count list, the constants
`CST1 = CST2` and the tail) were chosen so that the §15 total is at most `9968/10000`.
-/
import Mathlib
import Submission.Work.LinnikContract2.A7.WindowAPI
import Submission.Work.LinnikContract2.A7.window_step
import Submission.Work.LinnikAreas.A7.NumPoints
import Submission.Work.LinnikAreas.A7.NumExp

open DirichletCharacter Complex
open Work.A7
open Work.LinnikAreas.A7
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace Work.LinnikContract2.A7

private lemma t13_mem {t c t' c' : ℝ} {N : ℕ} (k : ℕ) (hk : k < Work.LinnikContract.table13.length)
    (hget : Work.LinnikContract.table13[k] = (t', c', N)) (ht : t = t') (hc : c = c') :
    (t, c, N) ∈ Work.LinnikContract.table13 := by
  subst ht hc; rw [← hget]; exact List.getElem_mem hk

theorem win_g1 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ lamN : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
        Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u)
    (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁) (hcol : ((348:ℝ)/1000) ≤ lam₁)
    (hnZ : ¬ Work.LinnikContract.IsZ χ₁ ρ₁)
    (hrow0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((1195:ℝ)/1000))
    (hrow2 : Work.LinnikContract.Lam2Bound χ₁ ((870:ℝ)/1000))
    (hrow3 : Work.LinnikContract.Lam3Bound χ₁ ((1134:ℝ)/1000))
    (hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hlam0 : Work.LinnikContract.lamOf q ρ₀ = lamN) (hlamNΛ : lamN ≤ ((6:ℝ)/5))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have hΛ : (0:ℝ) < ((6:ℝ)/5) := by norm_num
  have hlamLe : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hwide χ₀ ρ₀ hnarrow.1.1 hnarrow.1.2.1 (by linarith [hnarrow.1.2.2])
  have hcoln : ((348:ℝ)/1000) ≤ lamN := by
    rw [← hlam0]
    exact le_trans (by rw [hlam1]; exact hcol) hlamLe
  have hN0 : Work.LinnikContract.Ncount q ((6:ℝ)/5) ≤ 111 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 80 (by decide) rfl (by norm_num) (by norm_num))
  have hN1 : Work.LinnikContract.Ncount q ((47:ℝ)/40) ≤ 73 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 75 (by decide) rfl (by norm_num) (by norm_num))
  have hN2 : Work.LinnikContract.Ncount q ((23:ℝ)/20) ≤ 54 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 70 (by decide) rfl (by norm_num) (by norm_num))
  have hCf_l2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (87/100) ≤ ((39434893533:ℝ)/2500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (87/100)) (r := ((39434893533:ℝ)/2500000000000))
      (v_87_100).1 (v_6_5).2.1 (by norm_num) (v_87_100).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCf_l3 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (567/500) ≤ ((59255382137:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (567/500)) (r := ((59255382137:ℝ)/50000000000000))
      (v_567_500).1 (v_6_5).2.1 (by norm_num) (v_567_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL1 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((47:ℝ)/40)) ≤ ((77504832321:ℝ)/200000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((47:ℝ)/40))) (r := ((77504832321:ℝ)/200000000000000))
      (v_47_40).1 (v_6_5).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((23:ℝ)/20)) ≤ ((52975174291:ℝ)/62500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((23:ℝ)/20))) (r := ((52975174291:ℝ)/62500000000000))
      (v_23_20).1 (v_6_5).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have htail : (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw) ≤ ((14885014367:ℝ)/24088887000) :=
    Work.A7.tail_le (L := ((6:ℝ)/5)) (PU := ((444289:ℝ)/100000000)) (WL := ((8029629:ℝ)/100000000)) (r := ((14885014367:ℝ)/24088887000))
      (by norm_num) hεw hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (by norm_num)
  have hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac * ((6:ℝ)/5))) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw)
      + (111:ℝ) + 4 ≤ 1000 := by
    refine Work.A7.etab_le (L := ((6:ℝ)/5)) (E := ((279479:ℝ)/100000000)) (WL := ((8029629:ℝ)/100000000)) (N0 := (111:ℝ))
      (by norm_num) hεw hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num)
    rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
    exact exF_a_6_5
  have hsum : (∑ j ∈ Finset.range 2, ((Nlist [111, 73, 54] j : ℝ) - (Nlist [111, 73, 54] (j+1) : ℝ))
      * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((6:ℝ)/5) - (25:ℝ)/1000 * ((j:ℝ)+1)))
      = (38:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((47:ℝ)/40) + (19:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((23:ℝ)/20) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  have hmx : max 0 ((Nlist [111, 73, 54] 2 : ℝ) - 2) = (52:ℝ) := by norm_num [Nlist]
  have hTOT : (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((39434893533:ℝ)/2500000000000) + 2 * ((39434893533:ℝ)/2500000000000)
      + max 0 ((Nlist [111, 73, 54] 2 : ℝ) - 2) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (min ((1134:ℝ)/1000) ((6:ℝ)/5))
      + ∑ j ∈ Finset.range 2, ((Nlist [111, 73, 54] j : ℝ) - (Nlist [111, 73, 54] (j+1) : ℝ))
        * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((6:ℝ)/5) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ (9968:ℝ)/10000 := by
    rw [hsum, hmx, show min ((1134:ℝ)/1000) ((6:ℝ)/5) = (567/500) from by norm_num]
    linarith only [htail, hCf_l2, hCf_l3, hCfL1, hCfL2, hETAB]
  have hΛ : (0:ℝ) < ((6:ℝ)/5) := by norm_num
  have hlamN : ((870:ℝ)/1000) ≤ lamN := by
    rw [← hlam0]
    exact lamOf_narrow_ge hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hlamN0 : 0 < lamN := lt_of_lt_of_le (by norm_num) hlamN
  have h348 : (348:ℝ)/1000 ≤ lamN := le_trans (by norm_num) hlamN
  have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ lamN :=
    Work.A7.lam0Bound_self hnarrow hlam0
  have hLam2 : Work.LinnikContract.Lam2Bound χ₀ ((870:ℝ)/1000) :=
    lam2Bound_narrow_of_wide hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hLam3 : Work.LinnikContract.Lam3Bound χ₀ ((1134:ℝ)/1000) := by
    have h := lam3Bound_narrow_of_wide hrow0 hrow3 hnarrow hnZ
    rwa [show min (((1195:ℝ)/1000)) (((1134:ℝ)/1000)) = ((1134:ℝ)/1000) from by norm_num] at h
  have hCf_lam : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) lamN ≤ ((39434893533:ℝ)/2500000000000) := by
    have h0 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) lamN ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((87/100)) :=
      Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) hΛ (by norm_num)
        (by have h := hlamN; norm_num at h; exact h)
    linarith [h0, hCf_l2]
  have hcard : (((({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩
      Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ 2 := Work.A7.card_S1_le_two
  have hS1pt : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
      Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((39434893533:ℝ)/2500000000000)
        + (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * Work.LinnikContract.wHB lamN + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_eq_of_isMin1 hq hnarrow rfl]
        rw [h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀ hnarrow.1.1 lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hnarrow.1.1 hz' hb')
    · rw [Finset.mem_singleton.mp h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_inv_eq hq hnarrow rfl]
        rw [Finset.mem_singleton.mp h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      have hne : χ₀⁻¹ ≠ 1 := fun hh => hnarrow.1.1 (inv_eq_one.mp hh)
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀⁻¹ hne lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀⁻¹ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
  have hcred : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (min ((1134:ℝ)/1000) ((6:ℝ)/5)) ≤ ((39434893533:ℝ)/2500000000000) := by
    rw [show min ((1134:ℝ)/1000) ((6:ℝ)/5) = ((567/500)) from by norm_num]
    exact le_trans hCf_l3 (by norm_num)
  have hcred2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((870:ℝ)/1000) ≤ ((39434893533:ℝ)/2500000000000) := by
    rw [show ((870:ℝ)/1000) = ((87/100)) from by norm_num]
    exact le_trans hCf_l2 (by norm_num)
  have hle3 : min ((1134:ℝ)/1000) ((6:ℝ)/5) ≤ ((6:ℝ)/5) - (25:ℝ)/1000 * (2:ℝ) := by norm_num
  have hcount : ∀ j : ℕ, j ≤ 2 → ((Work.LinnikContract.Ncount q (((6:ℝ)/5) - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (Nlist [111, 73, 54] j : ℝ) := by
    intro j hj
    interval_cases j
    · convert hN0 using 2 <;> norm_num [Nlist]
    · convert hN1 using 2 <;> norm_num [Nlist]
    · convert hN2 using 2 <;> norm_num [Nlist]
  have hNdec : ∀ j < 2, Nlist [111, 73, 54] (j+1) ≤ Nlist [111, 73, 54] j := by
    intro j hj
    interval_cases j <;> norm_num [Nlist]
  have hlamSpos : (0:ℝ) < min ((1134:ℝ)/1000) ((6:ℝ)/5) := by norm_num
  exact window_step (q := q) (R := R) (Λ := ((6:ℝ)/5)) (η := η) (εw := εw) (lam₁ := lamN)
    (CST1 := ((39434893533:ℝ)/2500000000000)) (CST2 := ((39434893533:ℝ)/2500000000000)) (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
    (s := 2) (N := fun j => Nlist [111, 73, 54] j) (n₁ := 2) (c₀ := lamN) (l₂ := ((870:ℝ)/1000)) (l₃ := ((1134:ℝ)/1000))
    (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hΛ hη hlamN0 (by norm_num) hnarrow hlam0 h348 hlamNΛ le_rfl
    hLam0 hLam2 hLam3 (by simpa using hcard) hS1pt hS hSiff hD1 hPC hcount hNdec hle3 hlamSpos
    hcred (le_rfl) hcred2 hTOT hETAB

theorem win_g2 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ lamN : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
        Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u)
    (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁) (hcol : ((2:ℝ)/5) ≤ lam₁)
    (hnZ : ¬ Work.LinnikContract.IsZ χ₁ ρ₁)
    (hrow0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((1098:ℝ)/1000))
    (hrow2 : Work.LinnikContract.Lam2Bound χ₁ ((841:ℝ)/1000))
    (hrow3 : Work.LinnikContract.Lam3Bound χ₁ ((1054:ℝ)/1000))
    (hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hlam0 : Work.LinnikContract.lamOf q ρ₀ = lamN) (hlamNΛ : lamN ≤ ((6:ℝ)/5))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have hΛ : (0:ℝ) < ((6:ℝ)/5) := by norm_num
  have hlamLe : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hwide χ₀ ρ₀ hnarrow.1.1 hnarrow.1.2.1 (by linarith [hnarrow.1.2.2])
  have hcoln : ((2:ℝ)/5) ≤ lamN := by
    rw [← hlam0]
    exact le_trans (by rw [hlam1]; exact hcol) hlamLe
  have hN0 : Work.LinnikContract.Ncount q ((6:ℝ)/5) ≤ 81 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 81 (by decide) rfl (by norm_num) (by norm_num))
  have hN1 : Work.LinnikContract.Ncount q ((47:ℝ)/40) ≤ 58 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 76 (by decide) rfl (by norm_num) (by norm_num))
  have hN2 : Work.LinnikContract.Ncount q ((23:ℝ)/20) ≤ 45 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 71 (by decide) rfl (by norm_num) (by norm_num))
  have hN3 : Work.LinnikContract.Ncount q ((9:ℝ)/8) ≤ 36 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 66 (by decide) rfl (by norm_num) (by norm_num))
  have hN4 : Work.LinnikContract.Ncount q ((11:ℝ)/10) ≤ 30 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 61 (by decide) rfl (by norm_num) (by norm_num))
  have hN5 : Work.LinnikContract.Ncount q ((43:ℝ)/40) ≤ 26 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 56 (by decide) rfl (by norm_num) (by norm_num))
  have hCf_l2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (841/1000) ≤ ((191735004569:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (841/1000)) (r := ((191735004569:ℝ)/10000000000000))
      (v_841_1000).1 (v_6_5).2.1 (by norm_num) (v_841_1000).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCf_l3 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (527/500) ≤ ((87657876371:ℝ)/25000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (527/500)) (r := ((87657876371:ℝ)/25000000000000))
      (v_527_500).1 (v_6_5).2.1 (by norm_num) (v_527_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL1 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((47:ℝ)/40)) ≤ ((77504832321:ℝ)/200000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((47:ℝ)/40))) (r := ((77504832321:ℝ)/200000000000000))
      (v_47_40).1 (v_6_5).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((23:ℝ)/20)) ≤ ((52975174291:ℝ)/62500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((23:ℝ)/20))) (r := ((52975174291:ℝ)/62500000000000))
      (v_23_20).1 (v_6_5).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL3 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((9:ℝ)/8)) ≤ ((139113722819:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((9:ℝ)/8))) (r := ((139113722819:ℝ)/100000000000000))
      (v_9_8).1 (v_6_5).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL4 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((11:ℝ)/10)) ≤ ((101526917739:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((11:ℝ)/10))) (r := ((101526917739:ℝ)/50000000000000))
      (v_11_10).1 (v_6_5).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL5 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((43:ℝ)/40)) ≤ ((277997380403:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((6:ℝ)/5)) (x := (((43:ℝ)/40))) (r := ((277997380403:ℝ)/100000000000000))
      (v_43_40).1 (v_6_5).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have htail : (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw) ≤ ((14885014367:ℝ)/24088887000) :=
    Work.A7.tail_le (L := ((6:ℝ)/5)) (PU := ((444289:ℝ)/100000000)) (WL := ((8029629:ℝ)/100000000)) (r := ((14885014367:ℝ)/24088887000))
      (by norm_num) hεw hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (by norm_num)
  have hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac * ((6:ℝ)/5))) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw)
      + (81:ℝ) + 4 ≤ 1000 := by
    refine Work.A7.etab_le (L := ((6:ℝ)/5)) (E := ((279479:ℝ)/100000000)) (WL := ((8029629:ℝ)/100000000)) (N0 := (81:ℝ))
      (by norm_num) hεw hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num)
    rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
    exact exF_a_6_5
  have hsum : (∑ j ∈ Finset.range 5, ((Nlist [81, 58, 45, 36, 30, 26] j : ℝ) - (Nlist [81, 58, 45, 36, 30, 26] (j+1) : ℝ))
      * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((6:ℝ)/5) - (25:ℝ)/1000 * ((j:ℝ)+1)))
      = (23:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((47:ℝ)/40) + (13:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((23:ℝ)/20) + (9:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((9:ℝ)/8) + (6:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((11:ℝ)/10) + (4:ℝ) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((43:ℝ)/40) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  have hmx : max 0 ((Nlist [81, 58, 45, 36, 30, 26] 5 : ℝ) - 2) = (24:ℝ) := by norm_num [Nlist]
  have hTOT : (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((191735004569:ℝ)/10000000000000) + 2 * ((191735004569:ℝ)/10000000000000)
      + max 0 ((Nlist [81, 58, 45, 36, 30, 26] 5 : ℝ) - 2) * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (min ((1054:ℝ)/1000) ((6:ℝ)/5))
      + ∑ j ∈ Finset.range 5, ((Nlist [81, 58, 45, 36, 30, 26] j : ℝ) - (Nlist [81, 58, 45, 36, 30, 26] (j+1) : ℝ))
        * Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (((6:ℝ)/5) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ (9968:ℝ)/10000 := by
    rw [hsum, hmx, show min ((1054:ℝ)/1000) ((6:ℝ)/5) = (527/500) from by norm_num]
    linarith only [htail, hCf_l2, hCf_l3, hCfL1, hCfL2, hCfL3, hCfL4, hCfL5, hETAB]
  have hΛ : (0:ℝ) < ((6:ℝ)/5) := by norm_num
  have hlamN : ((841:ℝ)/1000) ≤ lamN := by
    rw [← hlam0]
    exact lamOf_narrow_ge hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hlamN0 : 0 < lamN := lt_of_lt_of_le (by norm_num) hlamN
  have h348 : (348:ℝ)/1000 ≤ lamN := le_trans (by norm_num) hlamN
  have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ lamN :=
    Work.A7.lam0Bound_self hnarrow hlam0
  have hLam2 : Work.LinnikContract.Lam2Bound χ₀ ((841:ℝ)/1000) :=
    lam2Bound_narrow_of_wide hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hLam3 : Work.LinnikContract.Lam3Bound χ₀ ((1054:ℝ)/1000) := by
    have h := lam3Bound_narrow_of_wide hrow0 hrow3 hnarrow hnZ
    rwa [show min (((1098:ℝ)/1000)) (((1054:ℝ)/1000)) = ((1054:ℝ)/1000) from by norm_num] at h
  have hCf_lam : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) lamN ≤ ((191735004569:ℝ)/10000000000000) := by
    have h0 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) lamN ≤ Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((841/1000)) :=
      Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) hΛ (by norm_num)
        (by have h := hlamN; norm_num at h; exact h)
    linarith [h0, hCf_l2]
  have hcard : (((({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩
      Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ 2 := Work.A7.card_S1_le_two
  have hS1pt : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
      Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((191735004569:ℝ)/10000000000000)
        + (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5)) * Work.LinnikContract.wHB lamN + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_eq_of_isMin1 hq hnarrow rfl]
        rw [h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀ hnarrow.1.1 lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hnarrow.1.1 hz' hb')
    · rw [Finset.mem_singleton.mp h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_inv_eq hq hnarrow rfl]
        rw [Finset.mem_singleton.mp h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      have hne : χ₀⁻¹ ≠ 1 := fun hh => hnarrow.1.1 (inv_eq_one.mp hh)
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀⁻¹ hne lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀⁻¹ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
  have hcred : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) (min ((1054:ℝ)/1000) ((6:ℝ)/5)) ≤ ((191735004569:ℝ)/10000000000000) := by
    rw [show min ((1054:ℝ)/1000) ((6:ℝ)/5) = ((527/500)) from by norm_num]
    exact le_trans hCf_l3 (by norm_num)
  have hcred2 : Work.LinnikAreas.A7.Cf ((6:ℝ)/5) ((841:ℝ)/1000) ≤ ((191735004569:ℝ)/10000000000000) := by
    rw [show ((841:ℝ)/1000) = ((841/1000)) from by norm_num]
    exact le_trans hCf_l2 (by norm_num)
  have hle3 : min ((1054:ℝ)/1000) ((6:ℝ)/5) ≤ ((6:ℝ)/5) - (25:ℝ)/1000 * (5:ℝ) := by norm_num
  have hcount : ∀ j : ℕ, j ≤ 5 → ((Work.LinnikContract.Ncount q (((6:ℝ)/5) - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (Nlist [81, 58, 45, 36, 30, 26] j : ℝ) := by
    intro j hj
    interval_cases j
    · convert hN0 using 2 <;> norm_num [Nlist]
    · convert hN1 using 2 <;> norm_num [Nlist]
    · convert hN2 using 2 <;> norm_num [Nlist]
    · convert hN3 using 2 <;> norm_num [Nlist]
    · convert hN4 using 2 <;> norm_num [Nlist]
    · convert hN5 using 2 <;> norm_num [Nlist]
  have hNdec : ∀ j < 5, Nlist [81, 58, 45, 36, 30, 26] (j+1) ≤ Nlist [81, 58, 45, 36, 30, 26] j := by
    intro j hj
    interval_cases j <;> norm_num [Nlist]
  have hlamSpos : (0:ℝ) < min ((1054:ℝ)/1000) ((6:ℝ)/5) := by norm_num
  exact window_step (q := q) (R := R) (Λ := ((6:ℝ)/5)) (η := η) (εw := εw) (lam₁ := lamN)
    (CST1 := ((191735004569:ℝ)/10000000000000)) (CST2 := ((191735004569:ℝ)/10000000000000)) (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
    (s := 5) (N := fun j => Nlist [81, 58, 45, 36, 30, 26] j) (n₁ := 2) (c₀ := lamN) (l₂ := ((841:ℝ)/1000)) (l₃ := ((1054:ℝ)/1000))
    (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hΛ hη hlamN0 (by norm_num) hnarrow hlam0 h348 hlamNΛ le_rfl
    hLam0 hLam2 hLam3 (by simpa using hcard) hS1pt hS hSiff hD1 hPC hcount hNdec hle3 hlamSpos
    hcred (le_rfl) hcred2 hTOT hETAB

theorem win_g3 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ lamN : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
        Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u)
    (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁) (hcol : ((11:ℝ)/25) ≤ lam₁)
    (hnZ : ¬ Work.LinnikContract.IsZ χ₁ ρ₁)
    (hrow0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((976:ℝ)/1000))
    (hrow2 : Work.LinnikContract.Lam2Bound χ₁ ((401:ℝ)/500))
    (hrow3 : Work.LinnikContract.Lam3Bound χ₁ ((951:ℝ)/1000))
    (hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hlam0 : Work.LinnikContract.lamOf q ρ₀ = lamN) (hlamNΛ : lamN ≤ ((49:ℝ)/40))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have hΛ : (0:ℝ) < ((49:ℝ)/40) := by norm_num
  have hlamLe : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hwide χ₀ ρ₀ hnarrow.1.1 hnarrow.1.2.1 (by linarith [hnarrow.1.2.2])
  have hcoln : ((11:ℝ)/25) ≤ lamN := by
    rw [← hlam0]
    exact le_trans (by rw [hlam1]; exact hcol) hlamLe
  have hN0 : Work.LinnikContract.Ncount q ((49:ℝ)/40) ≤ 97 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 87 (by decide) rfl (by norm_num) (by norm_num))
  have hN1 : Work.LinnikContract.Ncount q ((6:ℝ)/5) ≤ 67 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 82 (by decide) rfl (by norm_num) (by norm_num))
  have hN2 : Work.LinnikContract.Ncount q ((47:ℝ)/40) ≤ 51 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 77 (by decide) rfl (by norm_num) (by norm_num))
  have hN3 : Work.LinnikContract.Ncount q ((23:ℝ)/20) ≤ 40 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 72 (by decide) rfl (by norm_num) (by norm_num))
  have hN4 : Work.LinnikContract.Ncount q ((9:ℝ)/8) ≤ 33 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 67 (by decide) rfl (by norm_num) (by norm_num))
  have hN5 : Work.LinnikContract.Ncount q ((11:ℝ)/10) ≤ 28 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 62 (by decide) rfl (by norm_num) (by norm_num))
  have hN6 : Work.LinnikContract.Ncount q ((43:ℝ)/40) ≤ 24 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 57 (by decide) rfl (by norm_num) (by norm_num))
  have hN7 : Work.LinnikContract.Ncount q ((21:ℝ)/20) ≤ 21 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 52 (by decide) rfl (by norm_num) (by norm_num))
  have hN8 : Work.LinnikContract.Ncount q ((41:ℝ)/40) ≤ 18 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 47 (by decide) rfl (by norm_num) (by norm_num))
  have hN9 : Work.LinnikContract.Ncount q ((1:ℝ)/1) ≤ 16 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 42 (by decide) rfl (by norm_num) (by norm_num))
  have hN10 : Work.LinnikContract.Ncount q ((39:ℝ)/40) ≤ 15 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 37 (by decide) rfl (by norm_num) (by norm_num))
  have hCf_l2 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (401/500) ≤ ((127138903263:ℝ)/5000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (401/500)) (r := ((127138903263:ℝ)/5000000000000))
      (v_401_500).1 (v_49_40).2.1 (by norm_num) (v_401_500).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCf_l3 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (951/1000) ≤ ((930973665879:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (951/1000)) (r := ((930973665879:ℝ)/100000000000000))
      (v_951_1000).1 (v_49_40).2.1 (by norm_num) (v_951_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL1 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((6:ℝ)/5)) ≤ ((340542558081:ℝ)/1000000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((6:ℝ)/5))) (r := ((340542558081:ℝ)/1000000000000000))
      (v_6_5).1 (v_49_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL2 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((47:ℝ)/40)) ≤ ((744852980987:ℝ)/1000000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((47:ℝ)/40))) (r := ((744852980987:ℝ)/1000000000000000))
      (v_47_40).1 (v_49_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL3 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((23:ℝ)/20)) ≤ ((122253692781:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((23:ℝ)/20))) (r := ((122253692781:ℝ)/100000000000000))
      (v_23_20).1 (v_49_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL4 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((9:ℝ)/8)) ≤ ((178451013249:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((9:ℝ)/8))) (r := ((178451013249:ℝ)/100000000000000))
      (v_9_8).1 (v_49_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL5 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((11:ℝ)/10)) ≤ ((244322095833:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((11:ℝ)/10))) (r := ((244322095833:ℝ)/100000000000000))
      (v_11_10).1 (v_49_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL6 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((43:ℝ)/40)) ≤ ((160643815539:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((43:ℝ)/40))) (r := ((160643815539:ℝ)/50000000000000))
      (v_43_40).1 (v_49_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL7 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((21:ℝ)/20)) ≤ ((82194124711:ℝ)/20000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((21:ℝ)/20))) (r := ((82194124711:ℝ)/20000000000000))
      (v_21_20).1 (v_49_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL8 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((41:ℝ)/40)) ≤ ((257608440479:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((41:ℝ)/40))) (r := ((257608440479:ℝ)/50000000000000))
      (v_41_40).1 (v_49_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL9 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((1:ℝ)/(1))) ≤ ((79516613991:ℝ)/12500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((1:ℝ)/(1)))) (r := ((79516613991:ℝ)/12500000000000))
      (v_1_1).1 (v_49_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL10 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((39:ℝ)/40)) ≤ ((77611623259:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((49:ℝ)/40)) (x := (((39:ℝ)/40))) (r := ((77611623259:ℝ)/10000000000000))
      (v_39_40).1 (v_49_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have htail : (Work.LinnikAreas.A7.Phi ((49:ℝ)/40) / Work.LinnikAreas.A7.Wf ((49:ℝ)/40)) * ((67:ℝ)/6 + εw) ≤ ((13096557221:ℝ)/22953840000) :=
    Work.A7.tail_le (L := ((49:ℝ)/40)) (PU := ((390907:ℝ)/100000000)) (WL := ((95641:ℝ)/1250000)) (r := ((13096557221:ℝ)/22953840000))
      (by norm_num) hεw hεw1 (v_49_40).1 (v_49_40).2.2.2.1 (by norm_num) (by norm_num)
  have hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac * ((49:ℝ)/40))) / Work.LinnikAreas.A7.Wf ((49:ℝ)/40)) * ((67:ℝ)/6 + εw)
      + (97:ℝ) + 4 ≤ 1000 := by
    refine Work.A7.etab_le (L := ((49:ℝ)/40)) (E := ((247257:ℝ)/100000000)) (WL := ((95641:ℝ)/1250000)) (N0 := (97:ℝ))
      (by norm_num) hεw hεw1 ?_ (v_49_40).2.2.2.1 (by norm_num) (by norm_num)
    rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
    exact exF_a_49_40
  have hsum : (∑ j ∈ Finset.range 10, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) : ℝ))
      * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((49:ℝ)/40) - (25:ℝ)/1000 * ((j:ℝ)+1)))
      = (30:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((6:ℝ)/5) + (16:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((47:ℝ)/40) + (11:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((23:ℝ)/20) + (7:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((9:ℝ)/8) + (5:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((11:ℝ)/10) + (4:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((43:ℝ)/40) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((21:ℝ)/20) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((41:ℝ)/40) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((1:ℝ)/1) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((39:ℝ)/40) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  have hmx : max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 10 : ℝ) - 2) = (13:ℝ) := by norm_num [Nlist]
  have hTOT : (Work.LinnikAreas.A7.Phi ((49:ℝ)/40) / Work.LinnikAreas.A7.Wf ((49:ℝ)/40)) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((127138903263:ℝ)/5000000000000) + 2 * ((127138903263:ℝ)/5000000000000)
      + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 10 : ℝ) - 2) * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (min ((951:ℝ)/1000) ((49:ℝ)/40))
      + ∑ j ∈ Finset.range 10, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) : ℝ))
        * Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (((49:ℝ)/40) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ (9968:ℝ)/10000 := by
    rw [hsum, hmx, show min ((951:ℝ)/1000) ((49:ℝ)/40) = (951/1000) from by norm_num]
    linarith only [htail, hCf_l2, hCf_l3, hCfL1, hCfL2, hCfL3, hCfL4, hCfL5, hCfL6, hCfL7, hCfL8, hCfL9, hCfL10, hETAB]
  have hΛ : (0:ℝ) < ((49:ℝ)/40) := by norm_num
  have hlamN : ((401:ℝ)/500) ≤ lamN := by
    rw [← hlam0]
    exact lamOf_narrow_ge hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hlamN0 : 0 < lamN := lt_of_lt_of_le (by norm_num) hlamN
  have h348 : (348:ℝ)/1000 ≤ lamN := le_trans (by norm_num) hlamN
  have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ lamN :=
    Work.A7.lam0Bound_self hnarrow hlam0
  have hLam2 : Work.LinnikContract.Lam2Bound χ₀ ((401:ℝ)/500) :=
    lam2Bound_narrow_of_wide hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hLam3 : Work.LinnikContract.Lam3Bound χ₀ ((951:ℝ)/1000) := by
    have h := lam3Bound_narrow_of_wide hrow0 hrow3 hnarrow hnZ
    rwa [show min (((976:ℝ)/1000)) (((951:ℝ)/1000)) = ((951:ℝ)/1000) from by norm_num] at h
  have hCf_lam : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) lamN ≤ ((127138903263:ℝ)/5000000000000) := by
    have h0 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) lamN ≤ Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((401/500)) :=
      Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) hΛ (by norm_num)
        (by have h := hlamN; norm_num at h; exact h)
    linarith [h0, hCf_l2]
  have hcard : (((({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩
      Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ 2 := Work.A7.card_S1_le_two
  have hS1pt : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
      Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((127138903263:ℝ)/5000000000000)
        + (Work.LinnikAreas.A7.Phi ((49:ℝ)/40) / Work.LinnikAreas.A7.Wf ((49:ℝ)/40)) * Work.LinnikContract.wHB lamN + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_eq_of_isMin1 hq hnarrow rfl]
        rw [h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀ hnarrow.1.1 lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hnarrow.1.1 hz' hb')
    · rw [Finset.mem_singleton.mp h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_inv_eq hq hnarrow rfl]
        rw [Finset.mem_singleton.mp h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      have hne : χ₀⁻¹ ≠ 1 := fun hh => hnarrow.1.1 (inv_eq_one.mp hh)
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀⁻¹ hne lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀⁻¹ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
  have hcred : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) (min ((951:ℝ)/1000) ((49:ℝ)/40)) ≤ ((127138903263:ℝ)/5000000000000) := by
    rw [show min ((951:ℝ)/1000) ((49:ℝ)/40) = ((951/1000)) from by norm_num]
    exact le_trans hCf_l3 (by norm_num)
  have hcred2 : Work.LinnikAreas.A7.Cf ((49:ℝ)/40) ((401:ℝ)/500) ≤ ((127138903263:ℝ)/5000000000000) := by
    rw [show ((401:ℝ)/500) = ((401/500)) from by norm_num]
    exact le_trans hCf_l2 (by norm_num)
  have hle3 : min ((951:ℝ)/1000) ((49:ℝ)/40) ≤ ((49:ℝ)/40) - (25:ℝ)/1000 * (10:ℝ) := by norm_num
  have hcount : ∀ j : ℕ, j ≤ 10 → ((Work.LinnikContract.Ncount q (((49:ℝ)/40) - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) := by
    intro j hj
    interval_cases j
    · convert hN0 using 2 <;> norm_num [Nlist]
    · convert hN1 using 2 <;> norm_num [Nlist]
    · convert hN2 using 2 <;> norm_num [Nlist]
    · convert hN3 using 2 <;> norm_num [Nlist]
    · convert hN4 using 2 <;> norm_num [Nlist]
    · convert hN5 using 2 <;> norm_num [Nlist]
    · convert hN6 using 2 <;> norm_num [Nlist]
    · convert hN7 using 2 <;> norm_num [Nlist]
    · convert hN8 using 2 <;> norm_num [Nlist]
    · convert hN9 using 2 <;> norm_num [Nlist]
    · convert hN10 using 2 <;> norm_num [Nlist]
  have hNdec : ∀ j < 10, Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) ≤ Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j := by
    intro j hj
    interval_cases j <;> norm_num [Nlist]
  have hlamSpos : (0:ℝ) < min ((951:ℝ)/1000) ((49:ℝ)/40) := by norm_num
  exact window_step (q := q) (R := R) (Λ := ((49:ℝ)/40)) (η := η) (εw := εw) (lam₁ := lamN)
    (CST1 := ((127138903263:ℝ)/5000000000000)) (CST2 := ((127138903263:ℝ)/5000000000000)) (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
    (s := 10) (N := fun j => Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j) (n₁ := 2) (c₀ := lamN) (l₂ := ((401:ℝ)/500)) (l₃ := ((951:ℝ)/1000))
    (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hΛ hη hlamN0 (by norm_num) hnarrow hlam0 h348 hlamNΛ le_rfl
    hLam0 hLam2 hLam3 (by simpa using hcard) hS1pt hS hSiff hD1 hPC hcount hNdec hle3 hlamSpos
    hcred (le_rfl) hcred2 hTOT hETAB

theorem win_g4 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ lamN : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
        Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u)
    (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁) (hcol : ((1:ℝ)/2) ≤ lam₁)
    (hnZ : ¬ Work.LinnikContract.IsZ χ₁ ρ₁)
    (hrow0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((844:ℝ)/1000))
    (hrow2 : Work.LinnikContract.Lam2Bound χ₁ ((379:ℝ)/500))
    (hrow3 : Work.LinnikContract.Lam3Bound χ₁ ((856:ℝ)/1000))
    (hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hlam0 : Work.LinnikContract.lamOf q ρ₀ = lamN) (hlamNΛ : lamN ≤ ((5:ℝ)/4))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have hΛ : (0:ℝ) < ((5:ℝ)/4) := by norm_num
  have hlamLe : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hwide χ₀ ρ₀ hnarrow.1.1 hnarrow.1.2.1 (by linarith [hnarrow.1.2.2])
  have hcoln : ((1:ℝ)/2) ≤ lamN := by
    rw [← hlam0]
    exact le_trans (by rw [hlam1]; exact hcol) hlamLe
  have hN0 : Work.LinnikContract.Ncount q ((5:ℝ)/4) ≤ 104 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  have hN1 : Work.LinnikContract.Ncount q ((49:ℝ)/40) ≤ 71 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  have hN2 : Work.LinnikContract.Ncount q ((6:ℝ)/5) ≤ 54 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  have hN3 : Work.LinnikContract.Ncount q ((47:ℝ)/40) ≤ 42 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  have hN4 : Work.LinnikContract.Ncount q ((23:ℝ)/20) ≤ 35 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  have hN5 : Work.LinnikContract.Ncount q ((9:ℝ)/8) ≤ 29 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  have hN6 : Work.LinnikContract.Ncount q ((11:ℝ)/10) ≤ 25 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  have hN7 : Work.LinnikContract.Ncount q ((43:ℝ)/40) ≤ 22 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  have hN8 : Work.LinnikContract.Ncount q ((21:ℝ)/20) ≤ 19 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  have hN9 : Work.LinnikContract.Ncount q ((41:ℝ)/40) ≤ 17 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  have hN10 : Work.LinnikContract.Ncount q ((1:ℝ)/1) ≤ 15 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  have hN11 : Work.LinnikContract.Ncount q ((39:ℝ)/40) ≤ 14 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  have hN12 : Work.LinnikContract.Ncount q ((19:ℝ)/20) ≤ 12 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  have hN13 : Work.LinnikContract.Ncount q ((37:ℝ)/40) ≤ 11 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))
  have hN14 : Work.LinnikContract.Ncount q ((9:ℝ)/10) ≤ 10 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 23 (by decide) rfl (by norm_num) (by norm_num))
  have hN15 : Work.LinnikContract.Ncount q ((7:ℝ)/8) ≤ 9 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 18 (by decide) rfl (by norm_num) (by norm_num))
  have hN16 : Work.LinnikContract.Ncount q ((17:ℝ)/20) ≤ 9 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 13 (by decide) rfl (by norm_num) (by norm_num))
  have hCf_l2 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (379/500) ≤ ((10643898013:ℝ)/312500000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (379/500)) (r := ((10643898013:ℝ)/312500000000))
      (v_379_500).1 (v_5_4).2.1 (by norm_num) (v_379_500).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCf_l3 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (211/250) ≤ ((200849604103:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (211/250)) (r := ((200849604103:ℝ)/10000000000000))
      (v_211_250).1 (v_5_4).2.1 (by norm_num) (v_211_250).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL1 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((49:ℝ)/40)) ≤ ((59853701899:ℝ)/200000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((49:ℝ)/40))) (r := ((59853701899:ℝ)/200000000000000))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL2 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((6:ℝ)/5)) ≤ ((327293516039:ℝ)/500000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((6:ℝ)/5))) (r := ((327293516039:ℝ)/500000000000000))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL3 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((47:ℝ)/40)) ≤ ((6714990717:ℝ)/6250000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((47:ℝ)/40))) (r := ((6714990717:ℝ)/6250000000000))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL4 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((23:ℝ)/20)) ≤ ((156831891991:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((23:ℝ)/20))) (r := ((156831891991:ℝ)/100000000000000))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL5 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((9:ℝ)/8)) ≤ ((21472972257:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((9:ℝ)/8))) (r := ((21472972257:ℝ)/10000000000000))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL6 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((11:ℝ)/10)) ≤ ((141190818463:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((11:ℝ)/10))) (r := ((141190818463:ℝ)/50000000000000))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL7 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((43:ℝ)/40)) ≤ ((72242389451:ℝ)/20000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((43:ℝ)/40))) (r := ((72242389451:ℝ)/20000000000000))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL8 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((21:ℝ)/20)) ≤ ((113211852211:ℝ)/25000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((21:ℝ)/20))) (r := ((113211852211:ℝ)/25000000000000))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL9 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((41:ℝ)/40)) ≤ ((559137748283:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((41:ℝ)/40))) (r := ((559137748283:ℝ)/100000000000000))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL10 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((1:ℝ)/(1))) ≤ ((341096784551:ℝ)/50000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((1:ℝ)/(1)))) (r := ((341096784551:ℝ)/50000000000000))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL11 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((39:ℝ)/40)) ≤ ((25763019839:ℝ)/3125000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((39:ℝ)/40))) (r := ((25763019839:ℝ)/3125000000000))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL12 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((19:ℝ)/20)) ≤ ((61784212331:ℝ)/6250000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((19:ℝ)/20))) (r := ((61784212331:ℝ)/6250000000000))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL13 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((37:ℝ)/40)) ≤ ((117770127953:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((37:ℝ)/40))) (r := ((117770127953:ℝ)/10000000000000))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL14 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((9:ℝ)/10)) ≤ ((5581732439:ℝ)/400000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((9:ℝ)/10))) (r := ((5581732439:ℝ)/400000000000))
      (v_9_10).1 (v_5_4).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL15 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((7:ℝ)/8)) ≤ ((82289427299:ℝ)/5000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((7:ℝ)/8))) (r := ((82289427299:ℝ)/5000000000000))
      (v_7_8).1 (v_5_4).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL16_pt : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((163:ℝ)/200)) ≤ ((240864595171:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((5:ℝ)/4)) (x := (((163:ℝ)/200))) (r := ((240864595171:ℝ)/10000000000000))
      (v_163_200).1 (v_5_4).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL16 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((17:ℝ)/20)) ≤ ((240864595171:ℝ)/10000000000000) :=
    le_trans (Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) (by norm_num)
      (by norm_num) (by norm_num)) hCfL16_pt
  have htail : (Work.LinnikAreas.A7.Phi ((5:ℝ)/4) / Work.LinnikAreas.A7.Wf ((5:ℝ)/4)) * ((67:ℝ)/6 + εw) ≤ ((2304637867:ℝ)/4374084000) :=
    Work.A7.tail_le (L := ((5:ℝ)/4)) (PU := ((68789:ℝ)/20000000)) (WL := ((364507:ℝ)/5000000)) (r := ((2304637867:ℝ)/4374084000))
      (by norm_num) hεw hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (by norm_num)
  have hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac * ((5:ℝ)/4))) / Work.LinnikAreas.A7.Wf ((5:ℝ)/4)) * ((67:ℝ)/6 + εw)
      + (104:ℝ) + 4 ≤ 1000 := by
    refine Work.A7.etab_le (L := ((5:ℝ)/4)) (E := ((7:ℝ)/3200)) (WL := ((364507:ℝ)/5000000)) (N0 := (104:ℝ))
      (by norm_num) hεw hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num)
    rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
    exact exF_a_5_4
  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] (j+1) : ℝ))
      * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((5:ℝ)/4) - (25:ℝ)/1000 * ((j:ℝ)+1)))
      = (33:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((49:ℝ)/40) + (17:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((6:ℝ)/5) + (12:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((47:ℝ)/40) + (7:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((23:ℝ)/20) + (6:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((9:ℝ)/8) + (4:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((11:ℝ)/10) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((43:ℝ)/40) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((21:ℝ)/20) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((41:ℝ)/40) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((1:ℝ)/1) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((39:ℝ)/40) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((19:ℝ)/20) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((37:ℝ)/40) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((9:ℝ)/10) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((7:ℝ)/8) + (0:ℝ) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((17:ℝ)/20) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  have hmx : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] 16 : ℝ) - 2) = (7:ℝ) := by norm_num [Nlist]
  have hTOT : (Work.LinnikAreas.A7.Phi ((5:ℝ)/4) / Work.LinnikAreas.A7.Wf ((5:ℝ)/4)) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((10643898013:ℝ)/312500000000) + 2 * ((10643898013:ℝ)/312500000000)
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] 16 : ℝ) - 2) * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (min ((211:ℝ)/250) ((5:ℝ)/4))
      + ∑ j ∈ Finset.range 16, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] (j+1) : ℝ))
        * Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (((5:ℝ)/4) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ (9968:ℝ)/10000 := by
    rw [hsum, hmx, show min ((211:ℝ)/250) ((5:ℝ)/4) = (211/250) from by norm_num]
    linarith only [htail, hCf_l2, hCf_l3, hCfL1, hCfL2, hCfL3, hCfL4, hCfL5, hCfL6, hCfL7, hCfL8, hCfL9, hCfL10, hCfL11, hCfL12, hCfL13, hCfL14, hCfL15, hCfL16, hETAB]
  have hΛ : (0:ℝ) < ((5:ℝ)/4) := by norm_num
  have hlamN : ((379:ℝ)/500) ≤ lamN := by
    rw [← hlam0]
    exact lamOf_narrow_ge hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hlamN0 : 0 < lamN := lt_of_lt_of_le (by norm_num) hlamN
  have h348 : (348:ℝ)/1000 ≤ lamN := le_trans (by norm_num) hlamN
  have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ lamN :=
    Work.A7.lam0Bound_self hnarrow hlam0
  have hLam2 : Work.LinnikContract.Lam2Bound χ₀ ((379:ℝ)/500) :=
    lam2Bound_narrow_of_wide hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hLam3 : Work.LinnikContract.Lam3Bound χ₀ ((211:ℝ)/250) := by
    have h := lam3Bound_narrow_of_wide hrow0 hrow3 hnarrow hnZ
    rwa [show min (((844:ℝ)/1000)) (((856:ℝ)/1000)) = ((211:ℝ)/250) from by norm_num] at h
  have hCf_lam : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) lamN ≤ ((10643898013:ℝ)/312500000000) := by
    have h0 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) lamN ≤ Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((379/500)) :=
      Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) hΛ (by norm_num)
        (by have h := hlamN; norm_num at h; exact h)
    linarith [h0, hCf_l2]
  have hcard : (((({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩
      Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ 2 := Work.A7.card_S1_le_two
  have hS1pt : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
      Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((10643898013:ℝ)/312500000000)
        + (Work.LinnikAreas.A7.Phi ((5:ℝ)/4) / Work.LinnikAreas.A7.Wf ((5:ℝ)/4)) * Work.LinnikContract.wHB lamN + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_eq_of_isMin1 hq hnarrow rfl]
        rw [h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀ hnarrow.1.1 lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hnarrow.1.1 hz' hb')
    · rw [Finset.mem_singleton.mp h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_inv_eq hq hnarrow rfl]
        rw [Finset.mem_singleton.mp h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      have hne : χ₀⁻¹ ≠ 1 := fun hh => hnarrow.1.1 (inv_eq_one.mp hh)
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀⁻¹ hne lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀⁻¹ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
  have hcred : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) (min ((211:ℝ)/250) ((5:ℝ)/4)) ≤ ((10643898013:ℝ)/312500000000) := by
    rw [show min ((211:ℝ)/250) ((5:ℝ)/4) = ((211/250)) from by norm_num]
    exact le_trans hCf_l3 (by norm_num)
  have hcred2 : Work.LinnikAreas.A7.Cf ((5:ℝ)/4) ((379:ℝ)/500) ≤ ((10643898013:ℝ)/312500000000) := by
    rw [show ((379:ℝ)/500) = ((379/500)) from by norm_num]
    exact le_trans hCf_l2 (by norm_num)
  have hle3 : min ((211:ℝ)/250) ((5:ℝ)/4) ≤ ((5:ℝ)/4) - (25:ℝ)/1000 * (16:ℝ) := by norm_num
  have hcount : ∀ j : ℕ, j ≤ 16 → ((Work.LinnikContract.Ncount q (((5:ℝ)/4) - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] j : ℝ) := by
    intro j hj
    interval_cases j
    · convert hN0 using 2 <;> norm_num [Nlist]
    · convert hN1 using 2 <;> norm_num [Nlist]
    · convert hN2 using 2 <;> norm_num [Nlist]
    · convert hN3 using 2 <;> norm_num [Nlist]
    · convert hN4 using 2 <;> norm_num [Nlist]
    · convert hN5 using 2 <;> norm_num [Nlist]
    · convert hN6 using 2 <;> norm_num [Nlist]
    · convert hN7 using 2 <;> norm_num [Nlist]
    · convert hN8 using 2 <;> norm_num [Nlist]
    · convert hN9 using 2 <;> norm_num [Nlist]
    · convert hN10 using 2 <;> norm_num [Nlist]
    · convert hN11 using 2 <;> norm_num [Nlist]
    · convert hN12 using 2 <;> norm_num [Nlist]
    · convert hN13 using 2 <;> norm_num [Nlist]
    · convert hN14 using 2 <;> norm_num [Nlist]
    · convert hN15 using 2 <;> norm_num [Nlist]
    · convert hN16 using 2 <;> norm_num [Nlist]
  have hNdec : ∀ j < 16, Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] (j+1) ≤ Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] j := by
    intro j hj
    interval_cases j <;> norm_num [Nlist]
  have hlamSpos : (0:ℝ) < min ((211:ℝ)/250) ((5:ℝ)/4) := by norm_num
  exact window_step (q := q) (R := R) (Λ := ((5:ℝ)/4)) (η := η) (εw := εw) (lam₁ := lamN)
    (CST1 := ((10643898013:ℝ)/312500000000)) (CST2 := ((10643898013:ℝ)/312500000000)) (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
    (s := 16) (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9, 9] j) (n₁ := 2) (c₀ := lamN) (l₂ := ((379:ℝ)/500)) (l₃ := ((211:ℝ)/250))
    (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hΛ hη hlamN0 (by norm_num) hnarrow hlam0 h348 hlamNΛ le_rfl
    hLam0 hLam2 hLam3 (by simpa using hcard) hS1pt hS hSiff hD1 hPC hcount hNdec hle3 hlamSpos
    hcred (le_rfl) hcred2 hTOT hETAB

theorem win_g5 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ lamN : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hwide : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
        Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
        Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u)
    (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁) (hcol : ((29:ℝ)/50) ≤ lam₁)
    (hnZ : ¬ Work.LinnikContract.IsZ χ₁ ρ₁)
    (hrow0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((815:ℝ)/1000))
    (hrow2 : Work.LinnikContract.Lam2Bound χ₁ ((187:ℝ)/250))
    (hrow3 : Work.LinnikContract.Lam3Bound χ₁ ((856:ℝ)/1000))
    (hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hlam0 : Work.LinnikContract.lamOf q ρ₀ = lamN) (hlamNΛ : lamN ≤ ((51:ℝ)/40))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have hΛ : (0:ℝ) < ((51:ℝ)/40) := by norm_num
  have hlamLe : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ :=
    hwide χ₀ ρ₀ hnarrow.1.1 hnarrow.1.2.1 (by linarith [hnarrow.1.2.2])
  have hcoln : ((29:ℝ)/50) ≤ lamN := by
    rw [← hlam0]
    exact le_trans (by rw [hlam1]; exact hcol) hlamLe
  have hN0 : Work.LinnikContract.Ncount q ((51:ℝ)/40) ≤ 100 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  have hN1 : Work.LinnikContract.Ncount q ((5:ℝ)/4) ≤ 70 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  have hN2 : Work.LinnikContract.Ncount q ((49:ℝ)/40) ≤ 53 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  have hN3 : Work.LinnikContract.Ncount q ((6:ℝ)/5) ≤ 42 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  have hN4 : Work.LinnikContract.Ncount q ((47:ℝ)/40) ≤ 35 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  have hN5 : Work.LinnikContract.Ncount q ((23:ℝ)/20) ≤ 29 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  have hN6 : Work.LinnikContract.Ncount q ((9:ℝ)/8) ≤ 25 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  have hN7 : Work.LinnikContract.Ncount q ((11:ℝ)/10) ≤ 22 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  have hN8 : Work.LinnikContract.Ncount q ((43:ℝ)/40) ≤ 19 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  have hN9 : Work.LinnikContract.Ncount q ((21:ℝ)/20) ≤ 17 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  have hN10 : Work.LinnikContract.Ncount q ((41:ℝ)/40) ≤ 15 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  have hN11 : Work.LinnikContract.Ncount q ((1:ℝ)/1) ≤ 14 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  have hN12 : Work.LinnikContract.Ncount q ((39:ℝ)/40) ≤ 13 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  have hN13 : Work.LinnikContract.Ncount q ((19:ℝ)/20) ≤ 12 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  have hN14 : Work.LinnikContract.Ncount q ((37:ℝ)/40) ≤ 11 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  have hN15 : Work.LinnikContract.Ncount q ((9:ℝ)/10) ≤ 10 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  have hN16 : Work.LinnikContract.Ncount q ((7:ℝ)/8) ≤ 9 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))
  have hN17 : Work.LinnikContract.Ncount q ((17:ℝ)/20) ≤ 8 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 14 (by decide) rfl (by norm_num) (by norm_num))
  have hN18 : Work.LinnikContract.Ncount q ((33:ℝ)/40) ≤ 8 :=
    Ncount_le_table_w hnarrow hlam0 hcoln hcol hD2
      (t13_mem 9 (by decide) rfl (by norm_num) (by norm_num))
  have hCf_l2 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (187/250) ≤ ((92083822927:ℝ)/2500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (187/250)) (r := ((92083822927:ℝ)/2500000000000))
      (v_187_250).1 (v_51_40).2.1 (by norm_num) (v_187_250).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCf_l3 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (163/200) ≤ ((24688879299:ℝ)/1000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (163/200)) (r := ((24688879299:ℝ)/1000000000000))
      (v_163_200).1 (v_51_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL1 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((5:ℝ)/4)) ≤ ((263016854977:ℝ)/1000000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((5:ℝ)/4))) (r := ((263016854977:ℝ)/1000000000000000))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL2 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((49:ℝ)/40)) ≤ ((115056450931:ℝ)/200000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((49:ℝ)/40))) (r := ((115056450931:ℝ)/200000000000000))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL3 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((6:ℝ)/5)) ≤ ((14753897059:ℝ)/15625000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((6:ℝ)/5))) (r := ((14753897059:ℝ)/15625000000000))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL4 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((47:ℝ)/40)) ≤ ((3445896169:ℝ)/2500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((47:ℝ)/40))) (r := ((3445896169:ℝ)/2500000000000))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL5 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((23:ℝ)/20)) ≤ ((1887254749:ℝ)/1000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((23:ℝ)/20))) (r := ((1887254749:ℝ)/1000000000000))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL6 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((9:ℝ)/8)) ≤ ((248191789711:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((9:ℝ)/8))) (r := ((248191789711:ℝ)/100000000000000))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL7 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((11:ℝ)/10)) ≤ ((317486273867:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((11:ℝ)/10))) (r := ((317486273867:ℝ)/100000000000000))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL8 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((43:ℝ)/40)) ≤ ((79607316007:ℝ)/20000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((43:ℝ)/40))) (r := ((79607316007:ℝ)/20000000000000))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL9 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((21:ℝ)/20)) ≤ ((491472923017:ℝ)/100000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((21:ℝ)/20))) (r := ((491472923017:ℝ)/100000000000000))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL10 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((41:ℝ)/40)) ≤ ((149912161009:ℝ)/25000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((41:ℝ)/40))) (r := ((149912161009:ℝ)/25000000000000))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL11 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((1:ℝ)/(1))) ≤ ((72467812359:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((1:ℝ)/(1)))) (r := ((72467812359:ℝ)/10000000000000))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL12 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((39:ℝ)/40)) ≤ ((173793408577:ℝ)/20000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((39:ℝ)/40))) (r := ((173793408577:ℝ)/20000000000000))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL13 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((19:ℝ)/20)) ≤ ((25881498703:ℝ)/2500000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((19:ℝ)/20))) (r := ((25881498703:ℝ)/2500000000000))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL14 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((37:ℝ)/40)) ≤ ((12266765119:ℝ)/1000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((37:ℝ)/40))) (r := ((12266765119:ℝ)/1000000000000))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL15 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((9:ℝ)/10)) ≤ ((144677601041:ℝ)/10000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((9:ℝ)/10))) (r := ((144677601041:ℝ)/10000000000000))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL16 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((7:ℝ)/8)) ≤ ((1327819309:ℝ)/78125000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((7:ℝ)/8))) (r := ((1327819309:ℝ)/78125000000))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL17_pt : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((163:ℝ)/200)) ≤ ((24688879299:ℝ)/1000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((163:ℝ)/200))) (r := ((24688879299:ℝ)/1000000000000))
      (v_163_200).1 (v_51_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL17 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((17:ℝ)/20)) ≤ ((24688879299:ℝ)/1000000000000) :=
    le_trans (Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) (by norm_num)
      (by norm_num) (by norm_num)) hCfL17_pt
  have hCfL18_pt : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((163:ℝ)/200)) ≤ ((24688879299:ℝ)/1000000000000) :=
    Work.LinnikAreas.A7.Cf_le (L := ((51:ℝ)/40)) (x := (((163:ℝ)/200))) (r := ((24688879299:ℝ)/1000000000000))
      (v_163_200).1 (v_51_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Work.A7.Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  have hCfL18 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((33:ℝ)/40)) ≤ ((24688879299:ℝ)/1000000000000) :=
    le_trans (Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) (by norm_num)
      (by norm_num) (by norm_num)) hCfL18_pt
  have htail : (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40)) * ((67:ℝ)/6 + εw) ≤ ((844912157:ℝ)/1736364250) :=
    Work.A7.tail_le (L := ((51:ℝ)/40)) (PU := ((75657:ℝ)/25000000)) (WL := ((6945457:ℝ)/100000000)) (r := ((844912157:ℝ)/1736364250))
      (by norm_num) hεw hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (by norm_num)
  have hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac * ((51:ℝ)/40))) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40)) * ((67:ℝ)/6 + εw)
      + (100:ℝ) + 4 ≤ 1000 := by
    refine Work.A7.etab_le (L := ((51:ℝ)/40)) (E := ((193529:ℝ)/100000000)) (WL := ((6945457:ℝ)/100000000)) (N0 := (100:ℝ))
      (by norm_num) hεw hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num)
    rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
    exact exF_a_51_40
  have hsum : (∑ j ∈ Finset.range 18, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] (j+1) : ℝ))
      * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((51:ℝ)/40) - (25:ℝ)/1000 * ((j:ℝ)+1)))
      = (30:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((5:ℝ)/4) + (17:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((49:ℝ)/40) + (11:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((6:ℝ)/5) + (7:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((47:ℝ)/40) + (6:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((23:ℝ)/20) + (4:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((9:ℝ)/8) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((11:ℝ)/10) + (3:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((43:ℝ)/40) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((21:ℝ)/20) + (2:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((41:ℝ)/40) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((1:ℝ)/1) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((39:ℝ)/40) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((19:ℝ)/20) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((37:ℝ)/40) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((9:ℝ)/10) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((7:ℝ)/8) + (1:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((17:ℝ)/20) + (0:ℝ) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((33:ℝ)/40) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  have hmx : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] 18 : ℝ) - 2) = (6:ℝ) := by norm_num [Nlist]
  have hTOT : (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40)) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((92083822927:ℝ)/2500000000000) + 2 * ((92083822927:ℝ)/2500000000000)
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] 18 : ℝ) - 2) * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (min ((163:ℝ)/200) ((51:ℝ)/40))
      + ∑ j ∈ Finset.range 18, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] (j+1) : ℝ))
        * Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (((51:ℝ)/40) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ (9968:ℝ)/10000 := by
    rw [hsum, hmx, show min ((163:ℝ)/200) ((51:ℝ)/40) = (163/200) from by norm_num]
    linarith only [htail, hCf_l2, hCf_l3, hCfL1, hCfL2, hCfL3, hCfL4, hCfL5, hCfL6, hCfL7, hCfL8, hCfL9, hCfL10, hCfL11, hCfL12, hCfL13, hCfL14, hCfL15, hCfL16, hCfL17, hCfL18, hETAB]
  have hΛ : (0:ℝ) < ((51:ℝ)/40) := by norm_num
  have hlamN : ((187:ℝ)/250) ≤ lamN := by
    rw [← hlam0]
    exact lamOf_narrow_ge hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hlamN0 : 0 < lamN := lt_of_lt_of_le (by norm_num) hlamN
  have h348 : (348:ℝ)/1000 ≤ lamN := le_trans (by norm_num) hlamN
  have hLam0 : Work.LinnikContract.Lam0Bound χ₀ ρ₀ lamN :=
    Work.A7.lam0Bound_self hnarrow hlam0
  have hLam2 : Work.LinnikContract.Lam2Bound χ₀ ((187:ℝ)/250) :=
    lam2Bound_narrow_of_wide hrow0 hrow2 (by norm_num) hnarrow hnZ
  have hLam3 : Work.LinnikContract.Lam3Bound χ₀ ((163:ℝ)/200) := by
    have h := lam3Bound_narrow_of_wide hrow0 hrow3 hnarrow hnZ
    rwa [show min (((815:ℝ)/1000)) (((856:ℝ)/1000)) = ((163:ℝ)/200) from by norm_num] at h
  have hCf_lam : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) lamN ≤ ((92083822927:ℝ)/2500000000000) := by
    have h0 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) lamN ≤ Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((187/250)) :=
      Work.A7.Cf_antitone (fun hx hxy => Work.A7.PhiWf_antitone hx hxy) hΛ (by norm_num)
        (by have h := hlamN; norm_num at h; exact h)
    linarith [h0, hCf_l2]
  have hcard : (((({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩
      Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ 2 := Work.A7.card_S1_le_two
  have hS1pt : ∀ χ ∈ ({χ₀, χ₀⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
      Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((92083822927:ℝ)/2500000000000)
        + (Work.LinnikAreas.A7.Phi ((51:ℝ)/40) / Work.LinnikAreas.A7.Wf ((51:ℝ)/40)) * Work.LinnikContract.wHB lamN + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_eq_of_isMin1 hq hnarrow rfl]
        rw [h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀ hnarrow.1.1 lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀ ρ' (Work.A7.box_api7_p1 hq hRlog hnarrow.1.1 hz' hb')
    · rw [Finset.mem_singleton.mp h]
      have hlamR : lamN ≤ R := by
        rw [← hlam0, ← Work.A7.lamChar_inv_eq hq hnarrow rfl]
        rw [Finset.mem_singleton.mp h] at hχA
        exact Work.A7.lamChar_le_R_of_mem_Aset hq hRlog hχA
      have hne : χ₀⁻¹ ≠ 1 := fun hh => hnarrow.1.1 (inv_eq_one.mp hh)
      refine Work.A7.S1_plain (c := 0) hΛ hη hlamN0 hlamNΛ ?_
        (hPC χ₀⁻¹ hne lamN hlamN0.le hlamR (fun ρ hZ => by rw [← hlam0]; exact hnarrow.2 χ₀⁻¹ ρ hZ)) hCf_lam (le_rfl)
      intro ρ' hb' hz'
      rw [← hlam0]
      exact hnarrow.2 χ₀⁻¹ ρ' (Work.A7.box_api7_p1 hq hRlog hne hz' hb')
  have hcred : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) (min ((163:ℝ)/200) ((51:ℝ)/40)) ≤ ((92083822927:ℝ)/2500000000000) := by
    rw [show min ((163:ℝ)/200) ((51:ℝ)/40) = ((163/200)) from by norm_num]
    exact le_trans hCf_l3 (by norm_num)
  have hcred2 : Work.LinnikAreas.A7.Cf ((51:ℝ)/40) ((187:ℝ)/250) ≤ ((92083822927:ℝ)/2500000000000) := by
    rw [show ((187:ℝ)/250) = ((187/250)) from by norm_num]
    exact le_trans hCf_l2 (by norm_num)
  have hle3 : min ((163:ℝ)/200) ((51:ℝ)/40) ≤ ((51:ℝ)/40) - (25:ℝ)/1000 * (18:ℝ) := by norm_num
  have hcount : ∀ j : ℕ, j ≤ 18 → ((Work.LinnikContract.Ncount q (((51:ℝ)/40) - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] j : ℝ) := by
    intro j hj
    interval_cases j
    · convert hN0 using 2 <;> norm_num [Nlist]
    · convert hN1 using 2 <;> norm_num [Nlist]
    · convert hN2 using 2 <;> norm_num [Nlist]
    · convert hN3 using 2 <;> norm_num [Nlist]
    · convert hN4 using 2 <;> norm_num [Nlist]
    · convert hN5 using 2 <;> norm_num [Nlist]
    · convert hN6 using 2 <;> norm_num [Nlist]
    · convert hN7 using 2 <;> norm_num [Nlist]
    · convert hN8 using 2 <;> norm_num [Nlist]
    · convert hN9 using 2 <;> norm_num [Nlist]
    · convert hN10 using 2 <;> norm_num [Nlist]
    · convert hN11 using 2 <;> norm_num [Nlist]
    · convert hN12 using 2 <;> norm_num [Nlist]
    · convert hN13 using 2 <;> norm_num [Nlist]
    · convert hN14 using 2 <;> norm_num [Nlist]
    · convert hN15 using 2 <;> norm_num [Nlist]
    · convert hN16 using 2 <;> norm_num [Nlist]
    · convert hN17 using 2 <;> norm_num [Nlist]
    · convert hN18 using 2 <;> norm_num [Nlist]
  have hNdec : ∀ j < 18, Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] (j+1) ≤ Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] j := by
    intro j hj
    interval_cases j <;> norm_num [Nlist]
  have hlamSpos : (0:ℝ) < min ((163:ℝ)/200) ((51:ℝ)/40) := by norm_num
  exact window_step (q := q) (R := R) (Λ := ((51:ℝ)/40)) (η := η) (εw := εw) (lam₁ := lamN)
    (CST1 := ((92083822927:ℝ)/2500000000000)) (CST2 := ((92083822927:ℝ)/2500000000000)) (TOTAL := (9968:ℝ)/10000) (ETAB := 1000)
    (s := 18) (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9, 8, 8] j) (n₁ := 2) (c₀ := lamN) (l₂ := ((187:ℝ)/250)) (l₃ := ((163:ℝ)/200))
    (χ₁ := χ₀) (ρ₁ := ρ₀)
    hq hR hRlog hRmax hΛ hη hlamN0 (by norm_num) hnarrow hlam0 h348 hlamNΛ le_rfl
    hLam0 hLam2 hLam3 (by simpa using hcard) hS1pt hS hSiff hD1 hPC hcount hNdec hle3 hlamSpos
    hcred (le_rfl) hcred2 hTOT hETAB


end Work.LinnikContract2.A7
