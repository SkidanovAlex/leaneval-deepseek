import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas
import Submission.Work.LinnikAreas.A7.NumPoints
import Submission.Work.LinnikAreas.A7.NumExp
import Submission.Work.LinnikAreas.A7.Aref2
import Submission.Work.LinnikAreas.Density4.wHB_antitone
import Submission.Work.A7.sec15_helper

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.A7

private lemma t13_mem {t c t' c' : ℝ} {N : ℕ} (k : ℕ) (hk : k < Work.LinnikContract.table13.length)
    (hget : Work.LinnikContract.table13[k] = (t', c', N)) (ht : t = t') (hc : c = c') :
    (t, c, N) ∈ Work.LinnikContract.table13 := by
  subst ht hc; rw [← hget]; exact List.getElem_mem hk

open Work.LinnikContract
open Work.LinnikAreas.A7

-- I : Lam=49/40 s=0 col=1 n1=2 TA~0.888717
theorem total_r0 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((3646547:ℝ)/(25000000)) + 2 * ((165177:ℝ)/(12500000))
      + max 0 ((Nlist [218] 0 : ℝ) - 2 - 2) * Cf (((49:ℝ)/(40))) (min ((1229:ℝ)/(1000)) (((49:ℝ)/(40))))
      + ∑ j ∈ Finset.range 0, ((Nlist [218] j : ℝ) - (Nlist [218] (j+1) : ℝ))
          * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((49:ℝ)/(40))) := by norm_num
  have htail : (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((49:ℝ)/(40)))) (PU := ((390907:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (r := ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_49_40).1 (v_49_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((49:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((16475281:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((16475281:ℝ)/(765128300000000))))
      (v_49_40).1 (v_49_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hmax : max 0 ((Nlist [218] 0 : ℝ) - 2 - 2) = (214:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((1229:ℝ)/(1000)) (((49:ℝ)/(40))) = ((49:ℝ)/(40)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3]

lemma cred_r0 :
    Cf (((49:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((165177:ℝ)/(12500000)) ∧ Cf (((49:ℝ)/(40))) (((451:ℝ)/(500))) ≤ ((165177:ℝ)/(12500000))
      ∧ Cf (((49:ℝ)/(40))) (((327:ℝ)/(250))) ≤ ((165177:ℝ)/(12500000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((165177:ℝ)/(12500000))))
      (v_49_40).1 (v_49_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((451:ℝ)/(500)))) (r := (((165177:ℝ)/(12500000))))
      (v_451_500).1 (v_49_40).2.1 (by norm_num) (v_451_500).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((327:ℝ)/(250)))) (r := (((165177:ℝ)/(12500000))))
      (v_327_250).1 (v_49_40).2.1 (by norm_num) (v_327_250).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r0 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((49:ℝ)/(40))))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [218] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((49:ℝ)/(40)))) (E := ((247257:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (N0 := (218:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_49_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_49_40

lemma hcount_r0 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((87:ℝ)/(250)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 0 → (Work.LinnikContract.Ncount q ((((49:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [218] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((87:ℝ)/(250))) (t := ((49:ℝ)/(40))) (N := 218)
      (t13_mem 85 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=6/5 s=0 col=1 n1=2 TA~0.950044
theorem total_r1 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((13564633:ℝ)/(100000000)) + 2 * ((282441:ℝ)/(20000000))
      + max 0 ((Nlist [111] 0 : ℝ) - 2 - 2) * Cf (((6:ℝ)/(5))) (min ((59:ℝ)/(50)) (((6:ℝ)/(5))))
      + ∑ j ∈ Finset.range 0, ((Nlist [111] j : ℝ) - (Nlist [111] (j+1) : ℝ))
          * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((6:ℝ)/(5))) := by norm_num
  have htail : (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw) ≤ ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((6:ℝ)/(5)))) (PU := ((444289:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (r := ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((6:ℝ)/(5))) (((59:ℝ)/(50))) ≤ ((244543786501:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((59:ℝ)/(50)))) (r := (((244543786501:ℝ)/(802963200000000))))
      (v_59_50).1 (v_6_5).2.1 (by norm_num) (v_59_50).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hmax : max 0 ((Nlist [111] 0 : ℝ) - 2 - 2) = (107:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((59:ℝ)/(50)) (((6:ℝ)/(5))) = ((59:ℝ)/(50)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3]

lemma cred_r1 :
    Cf (((6:ℝ)/(5))) (((59:ℝ)/(50))) ≤ ((282441:ℝ)/(20000000)) ∧ Cf (((6:ℝ)/(5))) (((443:ℝ)/(500))) ≤ ((282441:ℝ)/(20000000))
      ∧ Cf (((6:ℝ)/(5))) (((1249:ℝ)/(1000))) ≤ ((282441:ℝ)/(20000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((59:ℝ)/(50)))) (r := (((282441:ℝ)/(20000000))))
      (v_59_50).1 (v_6_5).2.1 (by norm_num) (v_59_50).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((443:ℝ)/(500)))) (r := (((282441:ℝ)/(20000000))))
      (v_443_500).1 (v_6_5).2.1 (by norm_num) (v_443_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((1249:ℝ)/(1000)))) (r := (((282441:ℝ)/(20000000))))
      (v_1249_1000).1 (v_6_5).2.1 (by norm_num) (v_1249_1000).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r1 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((6:ℝ)/(5))))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (Nlist [111] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((6:ℝ)/(5)))) (E := ((279479:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (N0 := (111:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_6_5

lemma hcount_r1 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((87:ℝ)/(250)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 0 → (Work.LinnikContract.Ncount q ((((6:ℝ)/(5))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [111] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((87:ℝ)/(250))) (t := ((6:ℝ)/(5))) (N := 111)
      (t13_mem 80 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=6/5 s=2 col=1 n1=2 TA~0.983278
theorem total_r2 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((3046547:ℝ)/(25000000)) + 2 * ((394349:ℝ)/(25000000))
      + max 0 ((Nlist [111, 73, 54] 2 : ℝ) - 2 - 2) * Cf (((6:ℝ)/(5))) (min ((567:ℝ)/(500)) (((6:ℝ)/(5))))
      + ∑ j ∈ Finset.range 2, ((Nlist [111, 73, 54] j : ℝ) - (Nlist [111, 73, 54] (j+1) : ℝ))
          * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((6:ℝ)/(5))) := by norm_num
  have htail : (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw) ≤ ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((6:ℝ)/(5)))) (PU := ((444289:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (r := ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((6:ℝ)/(5))) (((567:ℝ)/(500))) ≤ ((317199275051:ℝ)/(267654400000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((567:ℝ)/(500)))) (r := (((317199275051:ℝ)/(267654400000000))))
      (v_567_500).1 (v_6_5).2.1 (by norm_num) (v_567_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) ≤ ((311167640879:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((47:ℝ)/(40)))) (r := (((311167640879:ℝ)/(802963200000000))))
      (v_47_40).1 (v_6_5).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) ≤ ((56716153959:ℝ)/(66913600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((23:ℝ)/(20)))) (r := (((56716153959:ℝ)/(66913600000000))))
      (v_23_20).1 (v_6_5).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 2, ((Nlist [111, 73, 54] j : ℝ) - (Nlist [111, 73, 54] (j+1) : ℝ)) * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (38:ℝ) * Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) + (19:ℝ) * Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [111, 73, 54] 2 : ℝ) - 2 - 2) = (50:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((567:ℝ)/(500)) (((6:ℝ)/(5))) = ((567:ℝ)/(500)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1]

lemma cred_r2 :
    Cf (((6:ℝ)/(5))) (((567:ℝ)/(500))) ≤ ((394349:ℝ)/(25000000)) ∧ Cf (((6:ℝ)/(5))) (((87:ℝ)/(100))) ≤ ((394349:ℝ)/(25000000))
      ∧ Cf (((6:ℝ)/(5))) (((239:ℝ)/(200))) ≤ ((394349:ℝ)/(25000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((567:ℝ)/(500)))) (r := (((394349:ℝ)/(25000000))))
      (v_567_500).1 (v_6_5).2.1 (by norm_num) (v_567_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((87:ℝ)/(100)))) (r := (((394349:ℝ)/(25000000))))
      (v_87_100).1 (v_6_5).2.1 (by norm_num) (v_87_100).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((239:ℝ)/(200)))) (r := (((394349:ℝ)/(25000000))))
      (v_239_200).1 (v_6_5).2.1 (by norm_num) (v_239_200).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r2 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((6:ℝ)/(5))))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (Nlist [111, 73, 54] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((6:ℝ)/(5)))) (E := ((279479:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (N0 := (111:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_6_5

lemma hcount_r2 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((87:ℝ)/(250)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 2 → (Work.LinnikContract.Ncount q ((((6:ℝ)/(5))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [111, 73, 54] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((87:ℝ)/(250))) (t := ((6:ℝ)/(5))) (N := 111)
      (t13_mem 80 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((87:ℝ)/(250))) (t := ((47:ℝ)/(40))) (N := 73)
      (t13_mem 75 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((87:ℝ)/(250))) (t := ((23:ℝ)/(20))) (N := 54)
      (t13_mem 70 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=6/5 s=4 col=2 n1=2 TA~0.974823
theorem total_r3 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((10969797:ℝ)/(100000000)) + 2 * ((436587:ℝ)/(25000000))
      + max 0 ((Nlist [81, 58, 45, 36, 30] 4 : ℝ) - 2 - 2) * Cf (((6:ℝ)/(5))) (min ((1093:ℝ)/(1000)) (((6:ℝ)/(5))))
      + ∑ j ∈ Finset.range 4, ((Nlist [81, 58, 45, 36, 30] j : ℝ) - (Nlist [81, 58, 45, 36, 30] (j+1) : ℝ))
          * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((6:ℝ)/(5))) := by norm_num
  have htail : (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw) ≤ ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((6:ℝ)/(5)))) (PU := ((444289:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (r := ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((6:ℝ)/(5))) (((1093:ℝ)/(1000))) ≤ ((447376848257:ℝ)/(200740800000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((1093:ℝ)/(1000)))) (r := (((447376848257:ℝ)/(200740800000000))))
      (v_1093_1000).1 (v_6_5).2.1 (by norm_num) (v_1093_1000).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) ≤ ((311167640879:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((47:ℝ)/(40)))) (r := (((311167640879:ℝ)/(802963200000000))))
      (v_47_40).1 (v_6_5).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) ≤ ((56716153959:ℝ)/(66913600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((23:ℝ)/(20)))) (r := (((56716153959:ℝ)/(66913600000000))))
      (v_23_20).1 (v_6_5).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((6:ℝ)/(5))) (((9:ℝ)/(8))) ≤ ((558516000191:ℝ)/(401481600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((9:ℝ)/(8)))) (r := (((558516000191:ℝ)/(401481600000000))))
      (v_9_8).1 (v_6_5).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((6:ℝ)/(5))) (((11:ℝ)/(10))) ≤ ((1630447575073:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((11:ℝ)/(10)))) (r := (((1630447575073:ℝ)/(802963200000000))))
      (v_11_10).1 (v_6_5).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 4, ((Nlist [81, 58, 45, 36, 30] j : ℝ) - (Nlist [81, 58, 45, 36, 30] (j+1) : ℝ)) * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (23:ℝ) * Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) + (13:ℝ) * Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) + (9:ℝ) * Cf (((6:ℝ)/(5))) (((9:ℝ)/(8))) + (6:ℝ) * Cf (((6:ℝ)/(5))) (((11:ℝ)/(10))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [81, 58, 45, 36, 30] 4 : ℝ) - 2 - 2) = (26:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((1093:ℝ)/(1000)) (((6:ℝ)/(5))) = ((1093:ℝ)/(1000)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3]

lemma cred_r3 :
    Cf (((6:ℝ)/(5))) (((1093:ℝ)/(1000))) ≤ ((436587:ℝ)/(25000000)) ∧ Cf (((6:ℝ)/(5))) (((171:ℝ)/(200))) ≤ ((436587:ℝ)/(25000000))
      ∧ Cf (((6:ℝ)/(5))) (((143:ℝ)/(125))) ≤ ((436587:ℝ)/(25000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((1093:ℝ)/(1000)))) (r := (((436587:ℝ)/(25000000))))
      (v_1093_1000).1 (v_6_5).2.1 (by norm_num) (v_1093_1000).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((171:ℝ)/(200)))) (r := (((436587:ℝ)/(25000000))))
      (v_171_200).1 (v_6_5).2.1 (by norm_num) (v_171_200).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((143:ℝ)/(125)))) (r := (((436587:ℝ)/(25000000))))
      (v_143_125).1 (v_6_5).2.1 (by norm_num) (v_143_125).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r3 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((6:ℝ)/(5))))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (Nlist [81, 58, 45, 36, 30] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((6:ℝ)/(5)))) (E := ((279479:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (N0 := (81:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_6_5

lemma hcount_r3 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((2:ℝ)/(5)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 4 → (Work.LinnikContract.Ncount q ((((6:ℝ)/(5))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [81, 58, 45, 36, 30] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((6:ℝ)/(5))) (N := 81)
      (t13_mem 81 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((47:ℝ)/(40))) (N := 58)
      (t13_mem 76 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((23:ℝ)/(20))) (N := 45)
      (t13_mem 71 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((9:ℝ)/(8))) (N := 36)
      (t13_mem 66 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((11:ℝ)/(10))) (N := 30)
      (t13_mem 61 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=6/5 s=5 col=2 n1=2 TA~0.987110
theorem total_r4 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((618589:ℝ)/(6250000)) + 2 * ((1917351:ℝ)/(100000000))
      + max 0 ((Nlist [81, 58, 45, 36, 30, 26] 5 : ℝ) - 2 - 2) * Cf (((6:ℝ)/(5))) (min ((527:ℝ)/(500)) (((6:ℝ)/(5))))
      + ∑ j ∈ Finset.range 5, ((Nlist [81, 58, 45, 36, 30, 26] j : ℝ) - (Nlist [81, 58, 45, 36, 30, 26] (j+1) : ℝ))
          * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((6:ℝ)/(5))) := by norm_num
  have htail : (Phi (((6:ℝ)/(5))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw) ≤ ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((6:ℝ)/(5)))) (PU := ((444289:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (r := ((444289:ℝ)/(100000000))/((8029629:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_6_5).1 (v_6_5).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((6:ℝ)/(5))) (((527:ℝ)/(500))) ≤ ((234620163053:ℝ)/(66913600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((527:ℝ)/(500)))) (r := (((234620163053:ℝ)/(66913600000000))))
      (v_527_500).1 (v_6_5).2.1 (by norm_num) (v_527_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) ≤ ((311167640879:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((47:ℝ)/(40)))) (r := (((311167640879:ℝ)/(802963200000000))))
      (v_47_40).1 (v_6_5).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) ≤ ((56716153959:ℝ)/(66913600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((23:ℝ)/(20)))) (r := (((56716153959:ℝ)/(66913600000000))))
      (v_23_20).1 (v_6_5).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((6:ℝ)/(5))) (((9:ℝ)/(8))) ≤ ((558516000191:ℝ)/(401481600000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((9:ℝ)/(8)))) (r := (((558516000191:ℝ)/(401481600000000))))
      (v_9_8).1 (v_6_5).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((6:ℝ)/(5))) (((11:ℝ)/(10))) ≤ ((1630447575073:ℝ)/(802963200000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((11:ℝ)/(10)))) (r := (((1630447575073:ℝ)/(802963200000000))))
      (v_11_10).1 (v_6_5).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((6:ℝ)/(5))) (((43:ℝ)/(40))) ≤ ((446443332319:ℝ)/(160592640000000)) := by
    exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((43:ℝ)/(40)))) (r := (((446443332319:ℝ)/(160592640000000))))
      (v_43_40).1 (v_6_5).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 5, ((Nlist [81, 58, 45, 36, 30, 26] j : ℝ) - (Nlist [81, 58, 45, 36, 30, 26] (j+1) : ℝ)) * Cf (((6:ℝ)/(5))) ((((6:ℝ)/(5))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (23:ℝ) * Cf (((6:ℝ)/(5))) (((47:ℝ)/(40))) + (13:ℝ) * Cf (((6:ℝ)/(5))) (((23:ℝ)/(20))) + (9:ℝ) * Cf (((6:ℝ)/(5))) (((9:ℝ)/(8))) + (6:ℝ) * Cf (((6:ℝ)/(5))) (((11:ℝ)/(10))) + (4:ℝ) * Cf (((6:ℝ)/(5))) (((43:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [81, 58, 45, 36, 30, 26] 5 : ℝ) - 2 - 2) = (22:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((527:ℝ)/(500)) (((6:ℝ)/(5))) = ((527:ℝ)/(500)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4]

lemma cred_r4 :
    Cf (((6:ℝ)/(5))) (((527:ℝ)/(500))) ≤ ((1917351:ℝ)/(100000000)) ∧ Cf (((6:ℝ)/(5))) (((841:ℝ)/(1000))) ≤ ((1917351:ℝ)/(100000000))
      ∧ Cf (((6:ℝ)/(5))) (((549:ℝ)/(500))) ≤ ((1917351:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((527:ℝ)/(500)))) (r := (((1917351:ℝ)/(100000000))))
      (v_527_500).1 (v_6_5).2.1 (by norm_num) (v_527_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((841:ℝ)/(1000)))) (r := (((1917351:ℝ)/(100000000))))
      (v_841_1000).1 (v_6_5).2.1 (by norm_num) (v_841_1000).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((6:ℝ)/(5)))) (x := (((549:ℝ)/(500)))) (r := (((1917351:ℝ)/(100000000))))
      (v_549_500).1 (v_6_5).2.1 (by norm_num) (v_549_500).2.2.2.1 (by norm_num)
      (v_6_5).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r4 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((6:ℝ)/(5))))) / Wf (((6:ℝ)/(5)))) * ((67:ℝ)/6 + εw)
      + (Nlist [81, 58, 45, 36, 30, 26] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((6:ℝ)/(5)))) (E := ((279479:ℝ)/(100000000))) (WL := ((8029629:ℝ)/(100000000))) (N0 := (81:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_6_5).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_6_5

lemma hcount_r4 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((2:ℝ)/(5)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 5 → (Work.LinnikContract.Ncount q ((((6:ℝ)/(5))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [81, 58, 45, 36, 30, 26] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((6:ℝ)/(5))) (N := 81)
      (t13_mem 81 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((47:ℝ)/(40))) (N := 58)
      (t13_mem 76 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((23:ℝ)/(20))) (N := 45)
      (t13_mem 71 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((9:ℝ)/(8))) (N := 36)
      (t13_mem 66 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((11:ℝ)/(10))) (N := 30)
      (t13_mem 61 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((2:ℝ)/(5))) (t := ((43:ℝ)/(40))) (N := 26)
      (t13_mem 56 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=49/40 s=8 col=3 n1=2 TA~0.973888
theorem total_r5 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((1137307:ℝ)/(12500000)) + 2 * ((539411:ℝ)/(25000000))
      + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] 8 : ℝ) - 2 - 2) * Cf (((49:ℝ)/(40))) (min ((1017:ℝ)/(1000)) (((49:ℝ)/(40))))
      + ∑ j ∈ Finset.range 8, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] (j+1) : ℝ))
          * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((49:ℝ)/(40))) := by norm_num
  have htail : (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((49:ℝ)/(40)))) (PU := ((390907:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (r := ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_49_40).1 (v_49_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((49:ℝ)/(40))) (((1017:ℝ)/(1000))) ≤ ((844683104053:ℝ)/(153025660000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((1017:ℝ)/(1000)))) (r := (((844683104053:ℝ)/(153025660000000))))
      (v_1017_1000).1 (v_49_40).2.1 (by norm_num) (v_1017_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((130279374271:ℝ)/(382564150000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((130279374271:ℝ)/(382564150000000))))
      (v_6_5).1 (v_49_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((142477023773:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((142477023773:ℝ)/(191282075000000))))
      (v_47_40).1 (v_49_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((935397601261:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((935397601261:ℝ)/(765128300000000))))
      (v_23_20).1 (v_49_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((341344801001:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((341344801001:ℝ)/(191282075000000))))
      (v_9_8).1 (v_49_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((1869377498371:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((1869377498371:ℝ)/(765128300000000))))
      (v_11_10).1 (v_49_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((153641411861:ℝ)/(47820518750000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((153641411861:ℝ)/(47820518750000))))
      (v_43_40).1 (v_49_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((6288905091:ℝ)/(1530256600000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((6288905091:ℝ)/(1530256600000))))
      (v_21_20).1 (v_49_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((492758770323:ℝ)/(95641037500000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((492758770323:ℝ)/(95641037500000))))
      (v_41_40).1 (v_49_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 8, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] (j+1) : ℝ)) * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) + (16:ℝ) * Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) + (11:ℝ) * Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) + (7:ℝ) * Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) + (5:ℝ) * Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) + (4:ℝ) * Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] 8 : ℝ) - 2 - 2) = (14:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((1017:ℝ)/(1000)) (((49:ℝ)/(40))) = ((1017:ℝ)/(1000)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7]

lemma cred_r5 :
    Cf (((49:ℝ)/(40))) (((1017:ℝ)/(1000))) ≤ ((539411:ℝ)/(25000000)) ∧ Cf (((49:ℝ)/(40))) (((207:ℝ)/(250))) ≤ ((539411:ℝ)/(25000000))
      ∧ Cf (((49:ℝ)/(40))) (((527:ℝ)/(500))) ≤ ((539411:ℝ)/(25000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((1017:ℝ)/(1000)))) (r := (((539411:ℝ)/(25000000))))
      (v_1017_1000).1 (v_49_40).2.1 (by norm_num) (v_1017_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((207:ℝ)/(250)))) (r := (((539411:ℝ)/(25000000))))
      (v_207_250).1 (v_49_40).2.1 (by norm_num) (v_207_250).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((527:ℝ)/(500)))) (r := (((539411:ℝ)/(25000000))))
      (v_527_500).1 (v_49_40).2.1 (by norm_num) (v_527_500).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r5 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((49:ℝ)/(40))))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((49:ℝ)/(40)))) (E := ((247257:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (N0 := (97:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_49_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_49_40

lemma hcount_r5 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((11:ℝ)/(25)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 8 → (Work.LinnikContract.Ncount q ((((49:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((49:ℝ)/(40))) (N := 97)
      (t13_mem 87 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((6:ℝ)/(5))) (N := 67)
      (t13_mem 82 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((47:ℝ)/(40))) (N := 51)
      (t13_mem 77 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((23:ℝ)/(20))) (N := 40)
      (t13_mem 72 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((9:ℝ)/(8))) (N := 33)
      (t13_mem 67 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((11:ℝ)/(10))) (N := 28)
      (t13_mem 62 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((43:ℝ)/(40))) (N := 24)
      (t13_mem 57 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((21:ℝ)/(20))) (N := 21)
      (t13_mem 52 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((41:ℝ)/(40))) (N := 18)
      (t13_mem 47 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=49/40 s=9 col=3 n1=2 TA~0.984125
theorem total_r6 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((8277873:ℝ)/(100000000)) + 2 * ((1171667:ℝ)/(50000000))
      + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] 9 : ℝ) - 2 - 2) * Cf (((49:ℝ)/(40))) (min ((983:ℝ)/(1000)) (((49:ℝ)/(40))))
      + ∑ j ∈ Finset.range 9, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] (j+1) : ℝ))
          * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((49:ℝ)/(40))) := by norm_num
  have htail : (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((49:ℝ)/(40)))) (PU := ((390907:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (r := ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_49_40).1 (v_49_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((49:ℝ)/(40))) (((983:ℝ)/(1000))) ≤ ((5578460593963:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((983:ℝ)/(1000)))) (r := (((5578460593963:ℝ)/(765128300000000))))
      (v_983_1000).1 (v_49_40).2.1 (by norm_num) (v_983_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((130279374271:ℝ)/(382564150000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((130279374271:ℝ)/(382564150000000))))
      (v_6_5).1 (v_49_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((142477023773:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((142477023773:ℝ)/(191282075000000))))
      (v_47_40).1 (v_49_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((935397601261:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((935397601261:ℝ)/(765128300000000))))
      (v_23_20).1 (v_49_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((341344801001:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((341344801001:ℝ)/(191282075000000))))
      (v_9_8).1 (v_49_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((1869377498371:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((1869377498371:ℝ)/(765128300000000))))
      (v_11_10).1 (v_49_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((153641411861:ℝ)/(47820518750000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((153641411861:ℝ)/(47820518750000))))
      (v_43_40).1 (v_49_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((6288905091:ℝ)/(1530256600000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((6288905091:ℝ)/(1530256600000))))
      (v_21_20).1 (v_49_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((492758770323:ℝ)/(95641037500000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((492758770323:ℝ)/(95641037500000))))
      (v_41_40).1 (v_49_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((49:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((4867232934773:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((4867232934773:ℝ)/(765128300000000))))
      (v_1_1).1 (v_49_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 9, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] (j+1) : ℝ)) * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) + (16:ℝ) * Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) + (11:ℝ) * Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) + (7:ℝ) * Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) + (5:ℝ) * Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) + (4:ℝ) * Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((49:ℝ)/(40))) (((1:ℝ)/(1))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] 9 : ℝ) - 2 - 2) = (12:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((983:ℝ)/(1000)) (((49:ℝ)/(40))) = ((983:ℝ)/(1000)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8]

lemma cred_r6 :
    Cf (((49:ℝ)/(40))) (((983:ℝ)/(1000))) ≤ ((1171667:ℝ)/(50000000)) ∧ Cf (((49:ℝ)/(40))) (((163:ℝ)/(200))) ≤ ((1171667:ℝ)/(50000000))
      ∧ Cf (((49:ℝ)/(40))) (((507:ℝ)/(500))) ≤ ((1171667:ℝ)/(50000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((983:ℝ)/(1000)))) (r := (((1171667:ℝ)/(50000000))))
      (v_983_1000).1 (v_49_40).2.1 (by norm_num) (v_983_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((163:ℝ)/(200)))) (r := (((1171667:ℝ)/(50000000))))
      (v_163_200).1 (v_49_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((507:ℝ)/(500)))) (r := (((1171667:ℝ)/(50000000))))
      (v_507_500).1 (v_49_40).2.1 (by norm_num) (v_507_500).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r6 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((49:ℝ)/(40))))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((49:ℝ)/(40)))) (E := ((247257:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (N0 := (97:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_49_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_49_40

lemma hcount_r6 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((11:ℝ)/(25)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 9 → (Work.LinnikContract.Ncount q ((((49:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((49:ℝ)/(40))) (N := 97)
      (t13_mem 87 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((6:ℝ)/(5))) (N := 67)
      (t13_mem 82 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((47:ℝ)/(40))) (N := 51)
      (t13_mem 77 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((23:ℝ)/(20))) (N := 40)
      (t13_mem 72 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((9:ℝ)/(8))) (N := 33)
      (t13_mem 67 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((11:ℝ)/(10))) (N := 28)
      (t13_mem 62 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((43:ℝ)/(40))) (N := 24)
      (t13_mem 57 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((21:ℝ)/(20))) (N := 21)
      (t13_mem 52 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((41:ℝ)/(40))) (N := 18)
      (t13_mem 47 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := (1:ℝ)) (N := 16)
      (t13_mem 42 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=49/40 s=10 col=3 n1=2 TA~0.996673
theorem total_r7 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((3785989:ℝ)/(50000000)) + 2 * ((2542779:ℝ)/(100000000))
      + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 10 : ℝ) - 2 - 2) * Cf (((49:ℝ)/(40))) (min ((951:ℝ)/(1000)) (((49:ℝ)/(40))))
      + ∑ j ∈ Finset.range 10, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) : ℝ))
          * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((49:ℝ)/(40))) := by norm_num
  have htail : (Phi (((49:ℝ)/(40))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((49:ℝ)/(40)))) (PU := ((390907:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (r := ((390907:ℝ)/(100000000))/((95641:ℝ)/(1250000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_49_40).1 (v_49_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((49:ℝ)/(40))) (((951:ℝ)/(1000))) ≤ ((7123142983187:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((951:ℝ)/(1000)))) (r := (((7123142983187:ℝ)/(765128300000000))))
      (v_951_1000).1 (v_49_40).2.1 (by norm_num) (v_951_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((130279374271:ℝ)/(382564150000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((130279374271:ℝ)/(382564150000000))))
      (v_6_5).1 (v_49_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((142477023773:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((142477023773:ℝ)/(191282075000000))))
      (v_47_40).1 (v_49_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((935397601261:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((935397601261:ℝ)/(765128300000000))))
      (v_23_20).1 (v_49_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((341344801001:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((341344801001:ℝ)/(191282075000000))))
      (v_9_8).1 (v_49_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((1869377498371:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((1869377498371:ℝ)/(765128300000000))))
      (v_11_10).1 (v_49_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((153641411861:ℝ)/(47820518750000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((153641411861:ℝ)/(47820518750000))))
      (v_43_40).1 (v_49_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((6288905091:ℝ)/(1530256600000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((6288905091:ℝ)/(1530256600000))))
      (v_21_20).1 (v_49_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((492758770323:ℝ)/(95641037500000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((492758770323:ℝ)/(95641037500000))))
      (v_41_40).1 (v_49_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((49:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((4867232934773:ℝ)/(765128300000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((4867232934773:ℝ)/(765128300000000))))
      (v_1_1).1 (v_49_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((49:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((1484571234109:ℝ)/(191282075000000)) := by
    exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((1484571234109:ℝ)/(191282075000000))))
      (v_39_40).1 (v_49_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 10, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) : ℝ)) * Cf (((49:ℝ)/(40))) ((((49:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((49:ℝ)/(40))) (((6:ℝ)/(5))) + (16:ℝ) * Cf (((49:ℝ)/(40))) (((47:ℝ)/(40))) + (11:ℝ) * Cf (((49:ℝ)/(40))) (((23:ℝ)/(20))) + (7:ℝ) * Cf (((49:ℝ)/(40))) (((9:ℝ)/(8))) + (5:ℝ) * Cf (((49:ℝ)/(40))) (((11:ℝ)/(10))) + (4:ℝ) * Cf (((49:ℝ)/(40))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((21:ℝ)/(20))) + (3:ℝ) * Cf (((49:ℝ)/(40))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((49:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((49:ℝ)/(40))) (((39:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 10 : ℝ) - 2 - 2) = (11:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((951:ℝ)/(1000)) (((49:ℝ)/(40))) = ((951:ℝ)/(1000)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9]

lemma cred_r7 :
    Cf (((49:ℝ)/(40))) (((951:ℝ)/(1000))) ≤ ((2542779:ℝ)/(100000000)) ∧ Cf (((49:ℝ)/(40))) (((401:ℝ)/(500))) ≤ ((2542779:ℝ)/(100000000))
      ∧ Cf (((49:ℝ)/(40))) (((122:ℝ)/(125))) ≤ ((2542779:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((951:ℝ)/(1000)))) (r := (((2542779:ℝ)/(100000000))))
      (v_951_1000).1 (v_49_40).2.1 (by norm_num) (v_951_1000).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((401:ℝ)/(500)))) (r := (((2542779:ℝ)/(100000000))))
      (v_401_500).1 (v_49_40).2.1 (by norm_num) (v_401_500).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((49:ℝ)/(40)))) (x := (((122:ℝ)/(125)))) (r := (((2542779:ℝ)/(100000000))))
      (v_122_125).1 (v_49_40).2.1 (by norm_num) (v_122_125).2.2.2.1 (by norm_num)
      (v_49_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r7 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((49:ℝ)/(40))))) / Wf (((49:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((49:ℝ)/(40)))) (E := ((247257:ℝ)/(100000000))) (WL := ((95641:ℝ)/(1250000))) (N0 := (97:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_49_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_49_40

lemma hcount_r7 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((11:ℝ)/(25)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 10 → (Work.LinnikContract.Ncount q ((((49:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((49:ℝ)/(40))) (N := 97)
      (t13_mem 87 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((6:ℝ)/(5))) (N := 67)
      (t13_mem 82 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((47:ℝ)/(40))) (N := 51)
      (t13_mem 77 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((23:ℝ)/(20))) (N := 40)
      (t13_mem 72 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((9:ℝ)/(8))) (N := 33)
      (t13_mem 67 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((11:ℝ)/(10))) (N := 28)
      (t13_mem 62 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((43:ℝ)/(40))) (N := 24)
      (t13_mem 57 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((21:ℝ)/(20))) (N := 21)
      (t13_mem 52 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((41:ℝ)/(40))) (N := 18)
      (t13_mem 47 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := (1:ℝ)) (N := 16)
      (t13_mem 42 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((11:ℝ)/(25))) (t := ((39:ℝ)/(40))) (N := 15)
      (t13_mem 37 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=5/4 s=13 col=4 n1=2 TA~0.967571
theorem total_r8 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((7084397:ℝ)/(100000000)) + 2 * ((702093:ℝ)/(25000000))
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] 13 : ℝ) - 2 - 2) * Cf (((5:ℝ)/(4))) (min ((921:ℝ)/(1000)) (((5:ℝ)/(4))))
      + ∑ j ∈ Finset.range 13, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] (j+1) : ℝ))
          * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((5:ℝ)/(4))) := by norm_num
  have htail : (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw) ≤ ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((5:ℝ)/(4)))) (PU := ((68789:ℝ)/(20000000))) (WL := ((364507:ℝ)/(5000000))) (r := ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((5:ℝ)/(4))) (((921:ℝ)/(1000))) ≤ ((2206216785839:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((921:ℝ)/(1000)))) (r := (((2206216785839:ℝ)/(182253550000000))))
      (v_921_1000).1 (v_5_4).2.1 (by norm_num) (v_921_1000).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) ≤ ((109085496517:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((49:ℝ)/(40)))) (r := (((109085496517:ℝ)/(364507100000000))))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) ≤ ((5965040519:ℝ)/(9112677500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((6:ℝ)/(5)))) (r := (((5965040519:ℝ)/(9112677500000))))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) ≤ ((195812943421:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(40)))) (r := (((195812943421:ℝ)/(182253550000000))))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) ≤ ((571663381369:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((23:ℝ)/(20)))) (r := (((571663381369:ℝ)/(364507100000000))))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) ≤ ((24459533893:ℝ)/(11390846875000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(8)))) (r := (((24459533893:ℝ)/(11390846875000))))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) ≤ ((1029301115689:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((11:ℝ)/(10)))) (r := (((1029301115689:ℝ)/(364507100000000))))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) ≤ ((131664319379:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((43:ℝ)/(40)))) (r := (((131664319379:ℝ)/(36450710000000))))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) ≤ ((825330478701:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((21:ℝ)/(20)))) (r := (((825330478701:ℝ)/(182253550000000))))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) ≤ ((203809679127:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((41:ℝ)/(40)))) (r := (((203809679127:ℝ)/(36450710000000))))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) ≤ ((2486643995117:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((1:ℝ)/(1)))) (r := (((2486643995117:ℝ)/(364507100000000))))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) ≤ ((7512642919:ℝ)/(911267750000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((39:ℝ)/(40)))) (r := (((7512642919:ℝ)/(911267750000))))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) ≤ ((450415681251:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((19:ℝ)/(20)))) (r := (((450415681251:ℝ)/(45563387500000))))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) ≤ ((1073201195161:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((37:ℝ)/(40)))) (r := (((1073201195161:ℝ)/(91126775000000))))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 13, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] (j+1) : ℝ)) * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (33:ℝ) * Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) + (17:ℝ) * Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) + (12:ℝ) * Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) + (7:ℝ) * Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) + (6:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) + (4:ℝ) * Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] 13 : ℝ) - 2 - 2) = (7:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((921:ℝ)/(1000)) (((5:ℝ)/(4))) = ((921:ℝ)/(1000)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12]

lemma cred_r8 :
    Cf (((5:ℝ)/(4))) (((921:ℝ)/(1000))) ≤ ((702093:ℝ)/(25000000)) ∧ Cf (((5:ℝ)/(4))) (((79:ℝ)/(100))) ≤ ((702093:ℝ)/(25000000))
      ∧ Cf (((5:ℝ)/(4))) (((47:ℝ)/(50))) ≤ ((702093:ℝ)/(25000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((921:ℝ)/(1000)))) (r := (((702093:ℝ)/(25000000))))
      (v_921_1000).1 (v_5_4).2.1 (by norm_num) (v_921_1000).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((79:ℝ)/(100)))) (r := (((702093:ℝ)/(25000000))))
      (v_79_100).1 (v_5_4).2.1 (by norm_num) (v_79_100).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(50)))) (r := (((702093:ℝ)/(25000000))))
      (v_47_50).1 (v_5_4).2.1 (by norm_num) (v_47_50).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r8 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((5:ℝ)/(4))))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((5:ℝ)/(4)))) (E := ((7:ℝ)/(3200))) (WL := ((364507:ℝ)/(5000000))) (N0 := (104:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_5_4

lemma hcount_r8 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((1:ℝ)/(2)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 13 → (Work.LinnikContract.Ncount q ((((5:ℝ)/(4))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((5:ℝ)/(4))) (N := 104)
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((49:ℝ)/(40))) (N := 71)
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((6:ℝ)/(5))) (N := 54)
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((47:ℝ)/(40))) (N := 42)
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((23:ℝ)/(20))) (N := 35)
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(8))) (N := 29)
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((11:ℝ)/(10))) (N := 25)
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((43:ℝ)/(40))) (N := 22)
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((21:ℝ)/(20))) (N := 19)
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((41:ℝ)/(40))) (N := 17)
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := (1:ℝ)) (N := 15)
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((39:ℝ)/(40))) (N := 14)
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=5/4 s=14 col=4 n1=2 TA~0.978821
theorem total_r9 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((6576779:ℝ)/(100000000)) + 2 * ((750559:ℝ)/(25000000))
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] 14 : ℝ) - 2 - 2) * Cf (((5:ℝ)/(4))) (min ((223:ℝ)/(250)) (((5:ℝ)/(4))))
      + ∑ j ∈ Finset.range 14, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] (j+1) : ℝ))
          * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((5:ℝ)/(4))) := by norm_num
  have htail : (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw) ≤ ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((5:ℝ)/(4)))) (PU := ((68789:ℝ)/(20000000))) (WL := ((364507:ℝ)/(5000000))) (r := ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((5:ℝ)/(4))) (((223:ℝ)/(250))) ≤ ((670597134369:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((223:ℝ)/(250)))) (r := (((670597134369:ℝ)/(45563387500000))))
      (v_223_250).1 (v_5_4).2.1 (by norm_num) (v_223_250).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) ≤ ((109085496517:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((49:ℝ)/(40)))) (r := (((109085496517:ℝ)/(364507100000000))))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) ≤ ((5965040519:ℝ)/(9112677500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((6:ℝ)/(5)))) (r := (((5965040519:ℝ)/(9112677500000))))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) ≤ ((195812943421:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(40)))) (r := (((195812943421:ℝ)/(182253550000000))))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) ≤ ((571663381369:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((23:ℝ)/(20)))) (r := (((571663381369:ℝ)/(364507100000000))))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) ≤ ((24459533893:ℝ)/(11390846875000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(8)))) (r := (((24459533893:ℝ)/(11390846875000))))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) ≤ ((1029301115689:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((11:ℝ)/(10)))) (r := (((1029301115689:ℝ)/(364507100000000))))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) ≤ ((131664319379:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((43:ℝ)/(40)))) (r := (((131664319379:ℝ)/(36450710000000))))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) ≤ ((825330478701:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((21:ℝ)/(20)))) (r := (((825330478701:ℝ)/(182253550000000))))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) ≤ ((203809679127:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((41:ℝ)/(40)))) (r := (((203809679127:ℝ)/(36450710000000))))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) ≤ ((2486643995117:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((1:ℝ)/(1)))) (r := (((2486643995117:ℝ)/(364507100000000))))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) ≤ ((7512642919:ℝ)/(911267750000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((39:ℝ)/(40)))) (r := (((7512642919:ℝ)/(911267750000))))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) ≤ ((450415681251:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((19:ℝ)/(20)))) (r := (((450415681251:ℝ)/(45563387500000))))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) ≤ ((1073201195161:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((37:ℝ)/(40)))) (r := (((1073201195161:ℝ)/(91126775000000))))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) ≤ ((1271613190197:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(10)))) (r := (((1271613190197:ℝ)/(91126775000000))))
      (v_9_10).1 (v_5_4).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 14, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] (j+1) : ℝ)) * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (33:ℝ) * Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) + (17:ℝ) * Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) + (12:ℝ) * Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) + (7:ℝ) * Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) + (6:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) + (4:ℝ) * Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] 14 : ℝ) - 2 - 2) = (6:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((223:ℝ)/(250)) (((5:ℝ)/(4))) = ((223:ℝ)/(250)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13]

lemma cred_r9 :
    Cf (((5:ℝ)/(4))) (((223:ℝ)/(250))) ≤ ((750559:ℝ)/(25000000)) ∧ Cf (((5:ℝ)/(4))) (((779:ℝ)/(1000))) ≤ ((750559:ℝ)/(25000000))
      ∧ Cf (((5:ℝ)/(4))) (((453:ℝ)/(500))) ≤ ((750559:ℝ)/(25000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((223:ℝ)/(250)))) (r := (((750559:ℝ)/(25000000))))
      (v_223_250).1 (v_5_4).2.1 (by norm_num) (v_223_250).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((779:ℝ)/(1000)))) (r := (((750559:ℝ)/(25000000))))
      (v_779_1000).1 (v_5_4).2.1 (by norm_num) (v_779_1000).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((453:ℝ)/(500)))) (r := (((750559:ℝ)/(25000000))))
      (v_453_500).1 (v_5_4).2.1 (by norm_num) (v_453_500).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r9 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((5:ℝ)/(4))))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((5:ℝ)/(4)))) (E := ((7:ℝ)/(3200))) (WL := ((364507:ℝ)/(5000000))) (N0 := (104:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_5_4

lemma hcount_r9 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((1:ℝ)/(2)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 14 → (Work.LinnikContract.Ncount q ((((5:ℝ)/(4))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((5:ℝ)/(4))) (N := 104)
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((49:ℝ)/(40))) (N := 71)
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((6:ℝ)/(5))) (N := 54)
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((47:ℝ)/(40))) (N := 42)
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((23:ℝ)/(20))) (N := 35)
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(8))) (N := 29)
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((11:ℝ)/(10))) (N := 25)
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((43:ℝ)/(40))) (N := 22)
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((21:ℝ)/(20))) (N := 19)
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((41:ℝ)/(40))) (N := 17)
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := (1:ℝ)) (N := 15)
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((39:ℝ)/(40))) (N := 14)
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 23 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=5/4 s=15 col=4 n1=2 TA~0.990510
theorem total_r10 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((615773:ℝ)/(10000000)) + 2 * ((128321:ℝ)/(4000000))
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 2 - 2) * Cf (((5:ℝ)/(4))) (min ((173:ℝ)/(200)) (((5:ℝ)/(4))))
      + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((5:ℝ)/(4))) := by norm_num
  have htail : (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw) ≤ ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((5:ℝ)/(4)))) (PU := ((68789:ℝ)/(20000000))) (WL := ((364507:ℝ)/(5000000))) (r := ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((5:ℝ)/(4))) (((173:ℝ)/(200))) ≤ ((6401013522127:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((173:ℝ)/(200)))) (r := (((6401013522127:ℝ)/(364507100000000))))
      (v_173_200).1 (v_5_4).2.1 (by norm_num) (v_173_200).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) ≤ ((109085496517:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((49:ℝ)/(40)))) (r := (((109085496517:ℝ)/(364507100000000))))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) ≤ ((5965040519:ℝ)/(9112677500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((6:ℝ)/(5)))) (r := (((5965040519:ℝ)/(9112677500000))))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) ≤ ((195812943421:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(40)))) (r := (((195812943421:ℝ)/(182253550000000))))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) ≤ ((571663381369:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((23:ℝ)/(20)))) (r := (((571663381369:ℝ)/(364507100000000))))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) ≤ ((24459533893:ℝ)/(11390846875000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(8)))) (r := (((24459533893:ℝ)/(11390846875000))))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) ≤ ((1029301115689:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((11:ℝ)/(10)))) (r := (((1029301115689:ℝ)/(364507100000000))))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) ≤ ((131664319379:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((43:ℝ)/(40)))) (r := (((131664319379:ℝ)/(36450710000000))))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) ≤ ((825330478701:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((21:ℝ)/(20)))) (r := (((825330478701:ℝ)/(182253550000000))))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) ≤ ((203809679127:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((41:ℝ)/(40)))) (r := (((203809679127:ℝ)/(36450710000000))))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) ≤ ((2486643995117:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((1:ℝ)/(1)))) (r := (((2486643995117:ℝ)/(364507100000000))))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) ≤ ((7512642919:ℝ)/(911267750000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((39:ℝ)/(40)))) (r := (((7512642919:ℝ)/(911267750000))))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) ≤ ((450415681251:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((19:ℝ)/(20)))) (r := (((450415681251:ℝ)/(45563387500000))))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) ≤ ((1073201195161:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((37:ℝ)/(40)))) (r := (((1073201195161:ℝ)/(91126775000000))))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) ≤ ((1271613190197:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(10)))) (r := (((1271613190197:ℝ)/(91126775000000))))
      (v_9_10).1 (v_5_4).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) ≤ ((5999016101057:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((7:ℝ)/(8)))) (r := (((5999016101057:ℝ)/(364507100000000))))
      (v_7_8).1 (v_5_4).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (33:ℝ) * Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) + (17:ℝ) * Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) + (12:ℝ) * Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) + (7:ℝ) * Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) + (6:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) + (4:ℝ) * Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 2 - 2) = (5:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((173:ℝ)/(200)) (((5:ℝ)/(4))) = ((173:ℝ)/(200)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14]

lemma cred_r10 :
    Cf (((5:ℝ)/(4))) (((173:ℝ)/(200))) ≤ ((128321:ℝ)/(4000000)) ∧ Cf (((5:ℝ)/(4))) (((96:ℝ)/(125))) ≤ ((128321:ℝ)/(4000000))
      ∧ Cf (((5:ℝ)/(4))) (((437:ℝ)/(500))) ≤ ((128321:ℝ)/(4000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((173:ℝ)/(200)))) (r := (((128321:ℝ)/(4000000))))
      (v_173_200).1 (v_5_4).2.1 (by norm_num) (v_173_200).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((96:ℝ)/(125)))) (r := (((128321:ℝ)/(4000000))))
      (v_96_125).1 (v_5_4).2.1 (by norm_num) (v_96_125).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((437:ℝ)/(500)))) (r := (((128321:ℝ)/(4000000))))
      (v_437_500).1 (v_5_4).2.1 (by norm_num) (v_437_500).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r10 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((5:ℝ)/(4))))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((5:ℝ)/(4)))) (E := ((7:ℝ)/(3200))) (WL := ((364507:ℝ)/(5000000))) (N0 := (104:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_5_4

lemma hcount_r10 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((1:ℝ)/(2)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 15 → (Work.LinnikContract.Ncount q ((((5:ℝ)/(4))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((5:ℝ)/(4))) (N := 104)
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((49:ℝ)/(40))) (N := 71)
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((6:ℝ)/(5))) (N := 54)
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((47:ℝ)/(40))) (N := 42)
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((23:ℝ)/(20))) (N := 35)
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(8))) (N := 29)
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((11:ℝ)/(10))) (N := 25)
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((43:ℝ)/(40))) (N := 22)
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((21:ℝ)/(20))) (N := 19)
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((41:ℝ)/(40))) (N := 17)
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := (1:ℝ)) (N := 15)
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((39:ℝ)/(40))) (N := 14)
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 23 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 18 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=5/4 s=15 col=4 n1=2 TA~0.992926
theorem total_r11 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((5818981:ℝ)/(100000000)) + 2 * ((106439:ℝ)/(3125000))
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 2 - 2) * Cf (((5:ℝ)/(4))) (min ((107:ℝ)/(125)) (((5:ℝ)/(4))))
      + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((5:ℝ)/(4))) := by norm_num
  have htail : (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw) ≤ ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((5:ℝ)/(4)))) (PU := ((68789:ℝ)/(20000000))) (WL := ((364507:ℝ)/(5000000))) (r := ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((5:ℝ)/(4))) (((107:ℝ)/(125))) ≤ ((3391163346941:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((107:ℝ)/(125)))) (r := (((3391163346941:ℝ)/(182253550000000))))
      (v_107_125).1 (v_5_4).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) ≤ ((109085496517:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((49:ℝ)/(40)))) (r := (((109085496517:ℝ)/(364507100000000))))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) ≤ ((5965040519:ℝ)/(9112677500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((6:ℝ)/(5)))) (r := (((5965040519:ℝ)/(9112677500000))))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) ≤ ((195812943421:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(40)))) (r := (((195812943421:ℝ)/(182253550000000))))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) ≤ ((571663381369:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((23:ℝ)/(20)))) (r := (((571663381369:ℝ)/(364507100000000))))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) ≤ ((24459533893:ℝ)/(11390846875000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(8)))) (r := (((24459533893:ℝ)/(11390846875000))))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) ≤ ((1029301115689:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((11:ℝ)/(10)))) (r := (((1029301115689:ℝ)/(364507100000000))))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) ≤ ((131664319379:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((43:ℝ)/(40)))) (r := (((131664319379:ℝ)/(36450710000000))))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) ≤ ((825330478701:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((21:ℝ)/(20)))) (r := (((825330478701:ℝ)/(182253550000000))))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) ≤ ((203809679127:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((41:ℝ)/(40)))) (r := (((203809679127:ℝ)/(36450710000000))))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) ≤ ((2486643995117:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((1:ℝ)/(1)))) (r := (((2486643995117:ℝ)/(364507100000000))))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) ≤ ((7512642919:ℝ)/(911267750000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((39:ℝ)/(40)))) (r := (((7512642919:ℝ)/(911267750000))))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) ≤ ((450415681251:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((19:ℝ)/(20)))) (r := (((450415681251:ℝ)/(45563387500000))))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) ≤ ((1073201195161:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((37:ℝ)/(40)))) (r := (((1073201195161:ℝ)/(91126775000000))))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) ≤ ((1271613190197:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(10)))) (r := (((1271613190197:ℝ)/(91126775000000))))
      (v_9_10).1 (v_5_4).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) ≤ ((5999016101057:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((7:ℝ)/(8)))) (r := (((5999016101057:ℝ)/(364507100000000))))
      (v_7_8).1 (v_5_4).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (33:ℝ) * Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) + (17:ℝ) * Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) + (12:ℝ) * Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) + (7:ℝ) * Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) + (6:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) + (4:ℝ) * Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 2 - 2) = (5:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((5:ℝ)/(4))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14]

lemma cred_r11 :
    Cf (((5:ℝ)/(4))) (((107:ℝ)/(125))) ≤ ((106439:ℝ)/(3125000)) ∧ Cf (((5:ℝ)/(4))) (((379:ℝ)/(500))) ≤ ((106439:ℝ)/(3125000))
      ∧ Cf (((5:ℝ)/(4))) (((211:ℝ)/(250))) ≤ ((106439:ℝ)/(3125000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((107:ℝ)/(125)))) (r := (((106439:ℝ)/(3125000))))
      (v_107_125).1 (v_5_4).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((379:ℝ)/(500)))) (r := (((106439:ℝ)/(3125000))))
      (v_379_500).1 (v_5_4).2.1 (by norm_num) (v_379_500).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((211:ℝ)/(250)))) (r := (((106439:ℝ)/(3125000))))
      (v_211_250).1 (v_5_4).2.1 (by norm_num) (v_211_250).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r11 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((5:ℝ)/(4))))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((5:ℝ)/(4)))) (E := ((7:ℝ)/(3200))) (WL := ((364507:ℝ)/(5000000))) (N0 := (104:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_5_4

lemma hcount_r11 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((1:ℝ)/(2)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 15 → (Work.LinnikContract.Ncount q ((((5:ℝ)/(4))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((5:ℝ)/(4))) (N := 104)
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((49:ℝ)/(40))) (N := 71)
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((6:ℝ)/(5))) (N := 54)
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((47:ℝ)/(40))) (N := 42)
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((23:ℝ)/(20))) (N := 35)
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(8))) (N := 29)
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((11:ℝ)/(10))) (N := 25)
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((43:ℝ)/(40))) (N := 22)
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((21:ℝ)/(20))) (N := 19)
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((41:ℝ)/(40))) (N := 17)
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := (1:ℝ)) (N := 15)
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((39:ℝ)/(40))) (N := 14)
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 23 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 18 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=51/40 s=16 col=5 n1=2 TA~0.941373
theorem total_r12 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((5651003:ℝ)/(100000000)) + 2 * ((3683353:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((107:ℝ)/(125)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((138653321707:ℝ)/(7234853125000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((138653321707:ℝ)/(7234853125000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG15 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) = (5:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((51:ℝ)/(40))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14, hCG15]

lemma cred_r12 :
    Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((3683353:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((187:ℝ)/(250))) ≤ ((3683353:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((163:ℝ)/(200))) ≤ ((3683353:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((3683353:ℝ)/(100000000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((187:ℝ)/(250)))) (r := (((3683353:ℝ)/(100000000))))
      (v_187_250).1 (v_51_40).2.1 (by norm_num) (v_187_250).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((163:ℝ)/(200)))) (r := (((3683353:ℝ)/(100000000))))
      (v_163_200).1 (v_51_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r12 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_r12 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 16 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))

-- I : Lam=5/4 s=15 col=4 n1=1 TA~0.994286
theorem total_r11rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (1:ℝ) * ((2478327:ℝ)/(25000000)) + 2 * ((106439:ℝ)/(3125000))
      + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 1 - 2) * Cf (((5:ℝ)/(4))) (min ((107:ℝ)/(125)) (((5:ℝ)/(4))))
      + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((5:ℝ)/(4))) := by norm_num
  have htail : (Phi (((5:ℝ)/(4))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw) ≤ ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((5:ℝ)/(4)))) (PU := ((68789:ℝ)/(20000000))) (WL := ((364507:ℝ)/(5000000))) (r := ((68789:ℝ)/(20000000))/((364507:ℝ)/(5000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_5_4).1 (v_5_4).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((5:ℝ)/(4))) (((107:ℝ)/(125))) ≤ ((3391163346941:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((107:ℝ)/(125)))) (r := (((3391163346941:ℝ)/(182253550000000))))
      (v_107_125).1 (v_5_4).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) ≤ ((109085496517:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((49:ℝ)/(40)))) (r := (((109085496517:ℝ)/(364507100000000))))
      (v_49_40).1 (v_5_4).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) ≤ ((5965040519:ℝ)/(9112677500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((6:ℝ)/(5)))) (r := (((5965040519:ℝ)/(9112677500000))))
      (v_6_5).1 (v_5_4).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) ≤ ((195812943421:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((47:ℝ)/(40)))) (r := (((195812943421:ℝ)/(182253550000000))))
      (v_47_40).1 (v_5_4).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) ≤ ((571663381369:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((23:ℝ)/(20)))) (r := (((571663381369:ℝ)/(364507100000000))))
      (v_23_20).1 (v_5_4).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) ≤ ((24459533893:ℝ)/(11390846875000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(8)))) (r := (((24459533893:ℝ)/(11390846875000))))
      (v_9_8).1 (v_5_4).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) ≤ ((1029301115689:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((11:ℝ)/(10)))) (r := (((1029301115689:ℝ)/(364507100000000))))
      (v_11_10).1 (v_5_4).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) ≤ ((131664319379:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((43:ℝ)/(40)))) (r := (((131664319379:ℝ)/(36450710000000))))
      (v_43_40).1 (v_5_4).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) ≤ ((825330478701:ℝ)/(182253550000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((21:ℝ)/(20)))) (r := (((825330478701:ℝ)/(182253550000000))))
      (v_21_20).1 (v_5_4).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) ≤ ((203809679127:ℝ)/(36450710000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((41:ℝ)/(40)))) (r := (((203809679127:ℝ)/(36450710000000))))
      (v_41_40).1 (v_5_4).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) ≤ ((2486643995117:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((1:ℝ)/(1)))) (r := (((2486643995117:ℝ)/(364507100000000))))
      (v_1_1).1 (v_5_4).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) ≤ ((7512642919:ℝ)/(911267750000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((39:ℝ)/(40)))) (r := (((7512642919:ℝ)/(911267750000))))
      (v_39_40).1 (v_5_4).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) ≤ ((450415681251:ℝ)/(45563387500000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((19:ℝ)/(20)))) (r := (((450415681251:ℝ)/(45563387500000))))
      (v_19_20).1 (v_5_4).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) ≤ ((1073201195161:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((37:ℝ)/(40)))) (r := (((1073201195161:ℝ)/(91126775000000))))
      (v_37_40).1 (v_5_4).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) ≤ ((1271613190197:ℝ)/(91126775000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((9:ℝ)/(10)))) (r := (((1271613190197:ℝ)/(91126775000000))))
      (v_9_10).1 (v_5_4).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) ≤ ((5999016101057:ℝ)/(364507100000000)) := by
    exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((7:ℝ)/(8)))) (r := (((5999016101057:ℝ)/(364507100000000))))
      (v_7_8).1 (v_5_4).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((5:ℝ)/(4))) ((((5:ℝ)/(4))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (33:ℝ) * Cf (((5:ℝ)/(4))) (((49:ℝ)/(40))) + (17:ℝ) * Cf (((5:ℝ)/(4))) (((6:ℝ)/(5))) + (12:ℝ) * Cf (((5:ℝ)/(4))) (((47:ℝ)/(40))) + (7:ℝ) * Cf (((5:ℝ)/(4))) (((23:ℝ)/(20))) + (6:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(8))) + (4:ℝ) * Cf (((5:ℝ)/(4))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((43:ℝ)/(40))) + (3:ℝ) * Cf (((5:ℝ)/(4))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((41:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((39:ℝ)/(40))) + (2:ℝ) * Cf (((5:ℝ)/(4))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((5:ℝ)/(4))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - 1 - 2) = (6:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((5:ℝ)/(4))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14]

lemma cred_r11rc :
    Cf (((5:ℝ)/(4))) (((107:ℝ)/(125))) ≤ ((106439:ℝ)/(3125000)) ∧ Cf (((5:ℝ)/(4))) (((379:ℝ)/(500))) ≤ ((106439:ℝ)/(3125000))
      ∧ Cf (((5:ℝ)/(4))) (((211:ℝ)/(250))) ≤ ((106439:ℝ)/(3125000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((107:ℝ)/(125)))) (r := (((106439:ℝ)/(3125000))))
      (v_107_125).1 (v_5_4).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((379:ℝ)/(500)))) (r := (((106439:ℝ)/(3125000))))
      (v_379_500).1 (v_5_4).2.1 (by norm_num) (v_379_500).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((5:ℝ)/(4)))) (x := (((211:ℝ)/(250)))) (r := (((106439:ℝ)/(3125000))))
      (v_211_250).1 (v_5_4).2.1 (by norm_num) (v_211_250).2.2.2.1 (by norm_num)
      (v_5_4).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r11rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((5:ℝ)/(4))))) / Wf (((5:ℝ)/(4)))) * ((67:ℝ)/6 + εw)
      + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((5:ℝ)/(4)))) (E := ((7:ℝ)/(3200))) (WL := ((364507:ℝ)/(5000000))) (N0 := (104:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_5_4).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_5_4

lemma hcount_r11rc {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((1:ℝ)/(2)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 15 → (Work.LinnikContract.Ncount q ((((5:ℝ)/(4))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((5:ℝ)/(4))) (N := 104)
      (t13_mem 93 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((49:ℝ)/(40))) (N := 71)
      (t13_mem 88 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((6:ℝ)/(5))) (N := 54)
      (t13_mem 83 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((47:ℝ)/(40))) (N := 42)
      (t13_mem 78 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((23:ℝ)/(20))) (N := 35)
      (t13_mem 73 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(8))) (N := 29)
      (t13_mem 68 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((11:ℝ)/(10))) (N := 25)
      (t13_mem 63 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((43:ℝ)/(40))) (N := 22)
      (t13_mem 58 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((21:ℝ)/(20))) (N := 19)
      (t13_mem 53 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((41:ℝ)/(40))) (N := 17)
      (t13_mem 48 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := (1:ℝ)) (N := 15)
      (t13_mem 43 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((39:ℝ)/(40))) (N := 14)
      (t13_mem 38 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 33 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 28 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 23 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((1:ℝ)/(2))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 18 (by decide) rfl (by norm_num) (by norm_num))

theorem rowA2_r11rc {p : ℝ} (h1 : ((14:ℝ)/(25)) ≤ p) (h2 : p ≤ ((29:ℝ)/(50)))
    (hBfun_mono : Bfun ((3:ℝ)/10) p ≤ Bfun ((3:ℝ)/10) ((14:ℝ)/(25)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100))
    (hBF2 : 2*((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p) :
    Cf (((5:ℝ)/(4))) p - Aref2 ((211:ℝ)/(250)) p ≤ ((2478327:ℝ)/(25000000)) := by
  have hp : (0:ℝ) < p := by linarith
  have hpc : p ≤ ((211:ℝ)/(250)) := by linarith
  have hEa : Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) ≤ ((6431259:ℝ)/(100000000)) := exF_a_14_25
  have hEaL : Real.exp (-((49:ℝ)/10*p)) ≤ Real.exp (-((49:ℝ)/10*((14:ℝ)/(25)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Bfun ((3:ℝ)/10) ((14:ℝ)/(25)) ≤ ((184051631:ℝ)/(100000000)) := (v_14_25).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((14:ℝ)/(25)))))/((14:ℝ)/(25)))^2/((9:ℝ)/100) ≤ ((84734403:ℝ)/(100000000)) := (v_14_25).2.2.2.2.2.2
  have hWbA : ((12917771:ℝ)/(50000000)) ≤ Wf ((29:ℝ)/(50)) := (v_29_50).2.2.2.1
  have hWp : Wf ((29:ℝ)/(50)) ≤ Wf p := Work.LinnikAreas.Density4.wHB_antitone (by linarith) h2
  have hPL : ((171971:ℝ)/(50000000)) ≤ Phi (((5:ℝ)/(4))) := (v_5_4).2.1
  have hWU : Wf (((5:ℝ)/(4))) ≤ ((3645071:ℝ)/(50000000)) := (v_5_4).2.2.1
  have hWL : ((364507:ℝ)/(5000000)) ≤ Wf (((5:ℝ)/(4))) := (v_5_4).2.2.2.1
  exact Cst1_le2 (a := ((14:ℝ)/(25))) (b := ((29:ℝ)/(50))) hp hpc hBF2 (exF_a_211_250) (exG_a_211_250)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hWbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((364507:ℝ)/(5000000))) hWL) (by norm_num) (by norm_num)

-- I : Lam=51/40 s=16 col=5 n1=1 TA~0.937618
theorem total_r12rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (1:ℝ) * ((4505027:ℝ)/(50000000)) + 2 * ((3683353:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 1 - 2) * Cf (((51:ℝ)/(40))) (min ((107:ℝ)/(125)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((138653321707:ℝ)/(7234853125000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((138653321707:ℝ)/(7234853125000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG15 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 1 - 2) = (6:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((51:ℝ)/(40))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14, hCG15]

lemma cred_r12rc :
    Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((3683353:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((187:ℝ)/(250))) ≤ ((3683353:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((163:ℝ)/(200))) ≤ ((3683353:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((3683353:ℝ)/(100000000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((187:ℝ)/(250)))) (r := (((3683353:ℝ)/(100000000))))
      (v_187_250).1 (v_51_40).2.1 (by norm_num) (v_187_250).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((163:ℝ)/(200)))) (r := (((3683353:ℝ)/(100000000))))
      (v_163_200).1 (v_51_40).2.1 (by norm_num) (v_163_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_r12rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_r12rc {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 16 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))

theorem rowA2_r12rc {p : ℝ} (h1 : ((29:ℝ)/(50)) ≤ p) (h2 : p ≤ ((3:ℝ)/(5)))
    (hBfun_mono : Bfun ((3:ℝ)/10) p ≤ Bfun ((3:ℝ)/10) ((29:ℝ)/(50)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100))
    (hBF2 : 2*((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p) :
    Cf (((51:ℝ)/(40))) p - Aref2 ((163:ℝ)/(200)) p ≤ ((4505027:ℝ)/(50000000)) := by
  have hp : (0:ℝ) < p := by linarith
  have hpc : p ≤ ((163:ℝ)/(200)) := by linarith
  have hEa : Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) ≤ ((2915447:ℝ)/(50000000)) := exF_a_29_50
  have hEaL : Real.exp (-((49:ℝ)/10*p)) ≤ Real.exp (-((49:ℝ)/10*((29:ℝ)/(50)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Bfun ((3:ℝ)/10) ((29:ℝ)/(50)) ≤ ((18318101:ℝ)/(10000000)) := (v_29_50).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((29:ℝ)/(50)))))/((29:ℝ)/(50)))^2/((9:ℝ)/100) ≤ ((84241919:ℝ)/(100000000)) := (v_29_50).2.2.2.2.2.2
  have hWbA : ((24901651:ℝ)/(100000000)) ≤ Wf ((3:ℝ)/(5)) := (v_3_5).2.2.2.1
  have hWp : Wf ((3:ℝ)/(5)) ≤ Wf p := Work.LinnikAreas.Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Phi (((51:ℝ)/(40))) := (v_51_40).2.1
  have hWU : Wf (((51:ℝ)/(40))) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Wf (((51:ℝ)/(40))) := (v_51_40).2.2.2.1
  exact Cst1_le2 (a := ((29:ℝ)/(50))) (b := ((3:ℝ)/(5))) hp hpc hBF2 (exF_a_163_200) (exG_a_163_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hWbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

-- II : Lam=51/40 s=16 col=5 n1=2 TA~0.990610
theorem total_u2 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((6788827:ℝ)/(100000000)) + 2 * ((100147:ℝ)/(2000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((107:ℝ)/(125)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((138653321707:ℝ)/(7234853125000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((138653321707:ℝ)/(7234853125000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG15 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) = (5:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((51:ℝ)/(40))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14, hCG15]

lemma cred_u2 :
    Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((100147:ℝ)/(2000000)) ∧ Cf (((51:ℝ)/(40))) (((701:ℝ)/(1000))) ≤ ((100147:ℝ)/(2000000))
      ∧ Cf (((51:ℝ)/(40))) (((139:ℝ)/(200))) ≤ ((100147:ℝ)/(2000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((100147:ℝ)/(2000000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((701:ℝ)/(1000)))) (r := (((100147:ℝ)/(2000000))))
      (v_701_1000).1 (v_51_40).2.1 (by norm_num) (v_701_1000).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((139:ℝ)/(200)))) (r := (((100147:ℝ)/(2000000))))
      (v_139_200).1 (v_51_40).2.1 (by norm_num) (v_139_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u2 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u2 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 16 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))

-- II : Lam=51/40 s=16 col=5 n1=1 TA~0.958365
theorem total_u2rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (1:ℝ) * ((4218353:ℝ)/(50000000)) + 2 * ((100147:ℝ)/(2000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 1 - 2) * Cf (((51:ℝ)/(40))) (min ((107:ℝ)/(125)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((138653321707:ℝ)/(7234853125000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((138653321707:ℝ)/(7234853125000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG15 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 1 - 2) = (6:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((51:ℝ)/(40))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14, hCG15]

lemma cred_u2rc :
    Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((100147:ℝ)/(2000000)) ∧ Cf (((51:ℝ)/(40))) (((701:ℝ)/(1000))) ≤ ((100147:ℝ)/(2000000))
      ∧ Cf (((51:ℝ)/(40))) (((139:ℝ)/(200))) ≤ ((100147:ℝ)/(2000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((100147:ℝ)/(2000000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((701:ℝ)/(1000)))) (r := (((100147:ℝ)/(2000000))))
      (v_701_1000).1 (v_51_40).2.1 (by norm_num) (v_701_1000).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((139:ℝ)/(200)))) (r := (((100147:ℝ)/(2000000))))
      (v_139_200).1 (v_51_40).2.1 (by norm_num) (v_139_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u2rc {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u2rc {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 16 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))

theorem rowA2_u2rc {p : ℝ} (h1 : ((3:ℝ)/(5)) ≤ p) (h2 : p ≤ ((139:ℝ)/(200)))
    (hBfun_mono : Bfun ((3:ℝ)/10) p ≤ Bfun ((3:ℝ)/10) ((3:ℝ)/(5)))
    (hF2_mono : ((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100))
    (hBF2 : 2*((1-Real.exp (-((3:ℝ)/10*p)))/p)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) p) :
    Cf (((51:ℝ)/(40))) p - Aref2 ((139:ℝ)/(200)) p ≤ ((4218353:ℝ)/(50000000)) := by
  have hp : (0:ℝ) < p := by linarith
  have hpc : p ≤ ((139:ℝ)/(200)) := by linarith
  have hEa : Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) ≤ ((5286573:ℝ)/(100000000)) := exF_a_3_5
  have hEaL : Real.exp (-((49:ℝ)/10*p)) ≤ Real.exp (-((49:ℝ)/10*((3:ℝ)/(5)))) := Real.exp_le_exp.mpr (by nlinarith)
  have hBaL : Bfun ((3:ℝ)/10) ((3:ℝ)/(5)) ≤ ((9115823:ℝ)/(5000000)) := (v_3_5).2.2.2.2.1
  have hF2aL : ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/(5)))))/((3:ℝ)/(5)))^2/((9:ℝ)/100) ≤ ((8375279:ℝ)/(10000000)) := (v_3_5).2.2.2.2.2.2
  have hWbA : ((20889217:ℝ)/(100000000)) ≤ Wf ((139:ℝ)/(200)) := (v_139_200).2.2.2.1
  have hWp : Wf ((139:ℝ)/(200)) ≤ Wf p := Work.LinnikAreas.Density4.wHB_antitone (by linarith) h2
  have hPL : ((2421:ℝ)/(800000)) ≤ Phi (((51:ℝ)/(40))) := (v_51_40).2.1
  have hWU : Wf (((51:ℝ)/(40))) ≤ ((6945459:ℝ)/(100000000)) := (v_51_40).2.2.1
  have hWL : ((6945457:ℝ)/(100000000)) ≤ Wf (((51:ℝ)/(40))) := (v_51_40).2.2.2.1
  exact Cst1_le2 (a := ((3:ℝ)/(5))) (b := ((139:ℝ)/(200))) hp hpc hBF2 (exF_a_139_200) (exG_a_139_200)
    hEa hBaL hF2aL (le_trans hEaL hEa) (le_trans hBfun_mono hBaL) (le_trans hF2_mono hF2aL)
    hPL (by norm_num) (le_trans hWbA hWp) (by norm_num) hWU (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < ((6945457:ℝ)/(100000000))) hWL) (by norm_num) (by norm_num)

-- III : Lam=51/40 s=16 col=5 n1=2 TA~0.954980
theorem total_u3 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((100147:ℝ)/(2000000)) + 2 * ((100147:ℝ)/(2000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((107:ℝ)/(125)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((138653321707:ℝ)/(7234853125000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((138653321707:ℝ)/(7234853125000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG15 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - 2 - 2) = (5:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((107:ℝ)/(125)) (((51:ℝ)/(40))) = ((107:ℝ)/(125)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14, hCG15]

lemma cred_u3 :
    Cf (((51:ℝ)/(40))) (((107:ℝ)/(125))) ≤ ((100147:ℝ)/(2000000)) ∧ Cf (((51:ℝ)/(40))) (((701:ℝ)/(1000))) ≤ ((100147:ℝ)/(2000000))
      ∧ Cf (((51:ℝ)/(40))) (((139:ℝ)/(200))) ≤ ((100147:ℝ)/(2000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((107:ℝ)/(125)))) (r := (((100147:ℝ)/(2000000))))
      (v_107_125).1 (v_51_40).2.1 (by norm_num) (v_107_125).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((701:ℝ)/(1000)))) (r := (((100147:ℝ)/(2000000))))
      (v_701_1000).1 (v_51_40).2.1 (by norm_num) (v_701_1000).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((139:ℝ)/(200)))) (r := (((100147:ℝ)/(2000000))))
      (v_139_200).1 (v_51_40).2.1 (by norm_num) (v_139_200).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u3 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u3 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 16 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((7:ℝ)/(8))) (N := 9)
      (t13_mem 19 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=15 col=5 n1=2 TA~0.811828
theorem total_u4_15 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((1699609:ℝ)/(100000000)) + 2 * ((1699609:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] 15 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((7:ℝ)/(8)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 15, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((3934854216551:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((3934854216551:ℝ)/(231515300000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG14 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 15, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] 15 : ℝ) - 2 - 2) = (6:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((7:ℝ)/(8)) (((51:ℝ)/(40))) = ((7:ℝ)/(8)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13, hCG14]

lemma cred_u4_15 :
    Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((1699609:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((1699609:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((7:ℝ)/(8))) ≤ ((1699609:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((1699609:ℝ)/(100000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((1699609:ℝ)/(100000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((7:ℝ)/(8)))) (r := (((1699609:ℝ)/(100000000))))
      (v_7_8).1 (v_51_40).2.1 (by norm_num) (v_7_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_15 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_15 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 15 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(10))) (N := 10)
      (t13_mem 24 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=14 col=5 n1=2 TA~0.786545
theorem total_u4_14 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((1446777:ℝ)/(100000000)) + 2 * ((1446777:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] 14 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((9:ℝ)/(10)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 14, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1674753910407:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1674753910407:ℝ)/(115757650000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG13 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 14, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] 14 : ℝ) - 2 - 2) = (7:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((9:ℝ)/(10)) (((51:ℝ)/(40))) = ((9:ℝ)/(10)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12, hCG13]

lemma cred_u4_14 :
    Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1446777:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1446777:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((9:ℝ)/(10))) ≤ ((1446777:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1446777:ℝ)/(100000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1446777:ℝ)/(100000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(10)))) (r := (((1446777:ℝ)/(100000000))))
      (v_9_10).1 (v_51_40).2.1 (by norm_num) (v_9_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_14 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_14 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 14 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((37:ℝ)/(40))) (N := 11)
      (t13_mem 29 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=13 col=5 n1=2 TA~0.762334
theorem total_u4_13 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((1226677:ℝ)/(100000000)) + 2 * ((1226677:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] 13 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((37:ℝ)/(40)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 13, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((709985951637:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((709985951637:ℝ)/(57878825000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG12 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 13, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] 13 : ℝ) - 2 - 2) = (8:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((37:ℝ)/(40)) (((51:ℝ)/(40))) = ((37:ℝ)/(40)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11, hCG12]

lemma cred_u4_13 :
    Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((1226677:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((1226677:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((37:ℝ)/(40))) ≤ ((1226677:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((1226677:ℝ)/(100000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((1226677:ℝ)/(100000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((37:ℝ)/(40)))) (r := (((1226677:ℝ)/(100000000))))
      (v_37_40).1 (v_51_40).2.1 (by norm_num) (v_37_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_13 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_13 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 13 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((19:ℝ)/(20))) (N := 12)
      (t13_mem 34 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=12 col=5 n1=2 TA~0.739364
theorem total_u4_12 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((51763:ℝ)/(5000000)) + 2 * ((51763:ℝ)/(5000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] 12 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((19:ℝ)/(20)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 12, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((119839258733:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((119839258733:ℝ)/(11575765000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG11 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 12, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] 12 : ℝ) - 2 - 2) = (9:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((19:ℝ)/(20)) (((51:ℝ)/(40))) = ((19:ℝ)/(20)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10, hCG11]

lemma cred_u4_12 :
    Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((51763:ℝ)/(5000000)) ∧ Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((51763:ℝ)/(5000000))
      ∧ Cf (((51:ℝ)/(40))) (((19:ℝ)/(20))) ≤ ((51763:ℝ)/(5000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((51763:ℝ)/(5000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((51763:ℝ)/(5000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((19:ℝ)/(20)))) (r := (((51763:ℝ)/(5000000))))
      (v_19_20).1 (v_51_40).2.1 (by norm_num) (v_19_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_12 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_12 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 12 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((39:ℝ)/(40))) (N := 13)
      (t13_mem 39 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=11 col=5 n1=2 TA~0.717746
theorem total_u4_11 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((108621:ℝ)/(12500000)) + 2 * ((108621:ℝ)/(12500000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] 11 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((39:ℝ)/(40)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 11, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((502947914059:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((502947914059:ℝ)/(57878825000000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG10 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 11, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) + (1:ℝ) * Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] 11 : ℝ) - 2 - 2) = (10:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((39:ℝ)/(40)) (((51:ℝ)/(40))) = ((39:ℝ)/(40)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9, hCG10]

lemma cred_u4_11 :
    Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((108621:ℝ)/(12500000)) ∧ Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((108621:ℝ)/(12500000))
      ∧ Cf (((51:ℝ)/(40))) (((39:ℝ)/(40))) ≤ ((108621:ℝ)/(12500000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((108621:ℝ)/(12500000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((108621:ℝ)/(12500000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((39:ℝ)/(40)))) (r := (((108621:ℝ)/(12500000))))
      (v_39_40).1 (v_51_40).2.1 (by norm_num) (v_39_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_11 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_11 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 11 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := (1:ℝ)) (N := 14)
      (t13_mem 44 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=10 col=5 n1=2 TA~0.697545
theorem total_u4_10 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((724679:ℝ)/(100000000)) + 2 * ((724679:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] 10 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((1:ℝ)/(1)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 10, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((1677740731863:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((1677740731863:ℝ)/(231515300000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG9 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 10, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] 10 : ℝ) - 2 - 2) = (11:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((1:ℝ)/(1)) (((51:ℝ)/(40))) = ((1:ℝ)/(1)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8, hCG9]

lemma cred_u4_10 :
    Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((724679:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((724679:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((1:ℝ)/(1))) ≤ ((724679:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((724679:ℝ)/(100000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((724679:ℝ)/(100000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((1:ℝ)/(1)))) (r := (((724679:ℝ)/(100000000))))
      (v_1_1).1 (v_51_40).2.1 (by norm_num) (v_1_1).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_10 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_10 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 10 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((41:ℝ)/(40))) (N := 15)
      (t13_mem 49 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=9 col=5 n1=2 TA~0.678791
theorem total_u4_9 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((599649:ℝ)/(100000000)) + 2 * ((599649:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] 9 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((41:ℝ)/(40)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 9, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((21691849331:ℝ)/(3617426562500)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((21691849331:ℝ)/(3617426562500))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG8 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 9, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) + (2:ℝ) * Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] 9 : ℝ) - 2 - 2) = (13:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((41:ℝ)/(40)) (((51:ℝ)/(40))) = ((41:ℝ)/(40)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7, hCG8]

lemma cred_u4_9 :
    Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((599649:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((599649:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((41:ℝ)/(40))) ≤ ((599649:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((599649:ℝ)/(100000000))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((599649:ℝ)/(100000000))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((41:ℝ)/(40)))) (r := (((599649:ℝ)/(100000000))))
      (v_41_40).1 (v_51_40).2.1 (by norm_num) (v_41_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_9 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_9 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 9 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((21:ℝ)/(20))) (N := 17)
      (t13_mem 54 (by decide) rfl (by norm_num) (by norm_num))

-- IV : Lam=51/40 s=8 col=5 n1=2 TA~0.660401
theorem total_u4_8 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (2:ℝ) * ((491473:ℝ)/(100000000)) + 2 * ((491473:ℝ)/(100000000))
      + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] 8 : ℝ) - 2 - 2) * Cf (((51:ℝ)/(40))) (min ((21:ℝ)/(20)) (((51:ℝ)/(40))))
      + ∑ j ∈ Finset.range 8, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] (j+1) : ℝ))
          * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))
    ≤ (9968:ℝ)/10000 := by
  have hΛ : (0:ℝ) < (((51:ℝ)/(40))) := by norm_num
  have htail : (Phi (((51:ℝ)/(40))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw) ≤ ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000) :=
    tail_le (L := (((51:ℝ)/(40)))) (PU := ((75657:ℝ)/(25000000))) (WL := ((6945457:ℝ)/(100000000))) (r := ((75657:ℝ)/(25000000))/((6945457:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000))
      hΛ hεw0 hεw1 (v_51_40).1 (v_51_40).2.2.2.1 (by norm_num) (le_refl _)
  have hCL3 : Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((56891750607:ℝ)/(11575765000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((56891750607:ℝ)/(11575765000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG0 : Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) ≤ ((12178485217:ℝ)/(46303060000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((5:ℝ)/(4)))) (r := (((12178485217:ℝ)/(46303060000000))))
      (v_5_4).1 (v_51_40).2.1 (by norm_num) (v_5_4).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG1 : Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) ≤ ((133186643771:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((49:ℝ)/(40)))) (r := (((133186643771:ℝ)/(231515300000000))))
      (v_49_40).1 (v_51_40).2.1 (by norm_num) (v_49_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG2 : Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) ≤ ((109304092921:ℝ)/(115757650000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((6:ℝ)/(5)))) (r := (((109304092921:ℝ)/(115757650000000))))
      (v_6_5).1 (v_51_40).2.1 (by norm_num) (v_6_5).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG3 : Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) ≤ ((79777768533:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((47:ℝ)/(40)))) (r := (((79777768533:ℝ)/(57878825000000))))
      (v_47_40).1 (v_51_40).2.1 (by norm_num) (v_47_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG4 : Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) ≤ ((436928349391:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((23:ℝ)/(20)))) (r := (((436928349391:ℝ)/(231515300000000))))
      (v_23_20).1 (v_51_40).2.1 (by norm_num) (v_23_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG5 : Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) ≤ ((143650491631:ℝ)/(57878825000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((9:ℝ)/(8)))) (r := (((143650491631:ℝ)/(57878825000000))))
      (v_9_8).1 (v_51_40).2.1 (by norm_num) (v_9_8).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG6 : Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) ≤ ((735029299401:ℝ)/(231515300000000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((11:ℝ)/(10)))) (r := (((735029299401:ℝ)/(231515300000000))))
      (v_11_10).1 (v_51_40).2.1 (by norm_num) (v_11_10).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hCG7 : Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) ≤ ((115189447797:ℝ)/(28939412500000)) := by
    exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((43:ℝ)/(40)))) (r := (((115189447797:ℝ)/(28939412500000))))
      (v_43_40).1 (v_51_40).2.1 (by norm_num) (v_43_40).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

  have hsum : (∑ j ∈ Finset.range 8, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] (j+1) : ℝ)) * Cf (((51:ℝ)/(40))) ((((51:ℝ)/(40))) - (25:ℝ)/1000 * ((j:ℝ)+1))) = (30:ℝ) * Cf (((51:ℝ)/(40))) (((5:ℝ)/(4))) + (17:ℝ) * Cf (((51:ℝ)/(40))) (((49:ℝ)/(40))) + (11:ℝ) * Cf (((51:ℝ)/(40))) (((6:ℝ)/(5))) + (7:ℝ) * Cf (((51:ℝ)/(40))) (((47:ℝ)/(40))) + (6:ℝ) * Cf (((51:ℝ)/(40))) (((23:ℝ)/(20))) + (4:ℝ) * Cf (((51:ℝ)/(40))) (((9:ℝ)/(8))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((11:ℝ)/(10))) + (3:ℝ) * Cf (((51:ℝ)/(40))) (((43:ℝ)/(40))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nlist, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
  rw [hsum]
  have hmax : max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] 8 : ℝ) - 2 - 2) = (15:ℝ) := by
    norm_num [Nlist]
  rw [hmax]
  have hmin : min ((21:ℝ)/(20)) (((51:ℝ)/(40))) = ((21:ℝ)/(20)) := by norm_num
  rw [hmin]
  linarith only [htail, hCL3, hCG0, hCG1, hCG2, hCG3, hCG4, hCG5, hCG6, hCG7]

lemma cred_u4_8 :
    Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((491473:ℝ)/(100000000)) ∧ Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((491473:ℝ)/(100000000))
      ∧ Cf (((51:ℝ)/(40))) (((21:ℝ)/(20))) ≤ ((491473:ℝ)/(100000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((491473:ℝ)/(100000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((491473:ℝ)/(100000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)
  · exact Cf_le (L := (((51:ℝ)/(40)))) (x := (((21:ℝ)/(20)))) (r := (((491473:ℝ)/(100000000))))
      (v_21_20).1 (v_51_40).2.1 (by norm_num) (v_21_20).2.2.2.1 (by norm_num)
      (v_51_40).2.2.1 (Wf_pos (by norm_num)) (by norm_num) (by norm_num)

lemma etab_u4_8 {εw : ℝ} (hεw0 : 0 ≤ εw) (hεw1 : εw ≤ 1/1000) :
    (Real.exp (-(ac * (((51:ℝ)/(40))))) / Wf (((51:ℝ)/(40)))) * ((67:ℝ)/6 + εw)
      + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] 0 : ℝ) + 4 ≤ 1000 := by
  refine etab_le (L := (((51:ℝ)/(40)))) (E := ((193529:ℝ)/(100000000))) (WL := ((6945457:ℝ)/(100000000))) (N0 := (100:ℝ))
    (by norm_num) hεw0 hεw1 ?_ (v_51_40).2.2.2.1 (by norm_num) (by norm_num [Nlist])
  rw [show ac = (49:ℝ)/10 from rfl]
  exact exF_a_51_40

lemma hcount_u4_8 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (hcol : ((29:ℝ)/(50)) ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2) :
    ∀ j : ℕ, j ≤ 8 → (Work.LinnikContract.Ncount q ((((51:ℝ)/(40))) - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] j : ℝ) := by
  intro j hj
  interval_cases j
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((51:ℝ)/(40))) (N := 100)
      (t13_mem 97 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((5:ℝ)/(4))) (N := 70)
      (t13_mem 94 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((49:ℝ)/(40))) (N := 53)
      (t13_mem 89 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((6:ℝ)/(5))) (N := 42)
      (t13_mem 84 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((47:ℝ)/(40))) (N := 35)
      (t13_mem 79 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((23:ℝ)/(20))) (N := 29)
      (t13_mem 74 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((9:ℝ)/(8))) (N := 25)
      (t13_mem 69 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((11:ℝ)/(10))) (N := 22)
      (t13_mem 64 (by decide) rfl (by norm_num) (by norm_num))
  · norm_num [Nlist]
    exact_mod_cast Ncount_le_table hmin hlam1 hcol hD2 (c := ((29:ℝ)/(50))) (t := ((43:ℝ)/(40))) (N := 19)
      (t13_mem 59 (by decide) rfl (by norm_num) (by norm_num))

end Work.A7
