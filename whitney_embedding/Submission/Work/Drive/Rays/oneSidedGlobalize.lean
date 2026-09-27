import Mathlib
import Submission.Work.Crux.exists_contDiff_iteratedDeriv
import Submission.Work.Noncompact.ProperLine.flatGlue2
import Submission.Work.Noncompact.CompressionTube.exists_smooth_squash

namespace Work.Drive.Rays

open Set Filter
open scoped Topology ContDiff

theorem oneSidedGlobalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Set.Ici (0 : ℝ)) 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Set.Ioo (0 : ℝ) δ)) :
    ∃ F : ℝ → E,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo (-δ) δ) ∧
      (∀ t : ℝ, 0 ≤ t → t < δ → F t = h t) := by
  classical
  -- Step 1. A globally smooth function `G` whose jet at `0` reproduces the one-sided jet of `h`.
  obtain ⟨G, hG, hGjet⟩ :=
    Work.Crux.exists_contDiff_iteratedDeriv (E := E)
      (fun k : ℕ => iteratedDerivWithin k h (Set.Ici (0 : ℝ)) 0)
  have hG0 : G 0 = h 0 := by
    have h1 : iteratedDeriv 0 G 0 = iteratedDerivWithin 0 h (Set.Ici (0 : ℝ)) 0 := hGjet 0
    rw [iteratedDeriv_zero, iteratedDerivWithin_zero] at h1
    exact h1
  -- Step 2. A smooth step `χ`: it is `1` for `t ≤ δ/4` and `0` for `t ≥ δ/2`.
  set χ : ℝ → ℝ := fun t => Real.smoothTransition ((δ/2 - t) / (δ/2 - δ/4)) with hχdef
  have hd : 0 < δ/2 - δ/4 := by linarith
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχdef]
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (δ/2 - t) / (δ/2 - δ/4)) := by fun_prop
    have h2 := (Real.smoothTransition.contDiff (n := ⊤)).comp h1
    simpa [Function.comp_def] using h2
  have hχ_one : ∀ t : ℝ, t ≤ δ/4 → χ t = 1 := by
    intro t ht
    rw [hχdef]
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div hd]
    linarith
  have hχ_zero : ∀ t : ℝ, δ/2 ≤ t → χ t = 0 := by
    intro t ht
    rw [hχdef]
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_nonpos_iff]
    exact Or.inr ⟨by linarith, le_of_lt hd⟩
  -- Step 3. The right-hand piece `V = χ • (h - G)`.
  set V : ℝ → E := fun t => χ t • (h t - G t) with hVdef
  have hV0 : V 0 = 0 := by
    rw [hVdef]
    show χ 0 • (h 0 - G 0) = (0:E)
    rw [hχ_one 0 (by linarith : (0:ℝ) ≤ δ/4), one_smul]
    rw [hG0, sub_self]
  have hV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V (Set.Ici (0 : ℝ)) := by
    rw [hVdef]
    intro x hx
    rw [Set.mem_Ici] at hx
    rcases lt_or_eq_of_le hx with hx0 | rfl
    · rw [contDiffWithinAt_iff_contDiffAt (Ici_mem_nhds hx0)]
      rcases le_or_gt x (δ/2) with hxμ | hxμ
      · have hxδ : x < δ := by linarith
        exact hχ.contDiffAt.smul
          ((hsm.contDiffAt (Ioo_mem_nhds hx0 hxδ)).sub hG.contDiffAt)
      · have hev : (fun t => χ t • (h t - G t)) =ᶠ[𝓝 x] (fun _ => (0:E)) := by
          filter_upwards [Ioo_mem_nhds hxμ (by linarith : x < x + 1)] with t ht
          rw [hχ_zero t (le_of_lt ht.1), zero_smul]
        exact (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq hev
    · exact hχ.contDiffWithinAt.smul (h0.sub hG.contDiffWithinAt)
  have hVjet : ∀ k : ℕ, 0 < k →
      iteratedDerivWithin k V (Set.Ici (0 : ℝ)) 0 = 0 := by
    intro k _
    rw [hVdef]
    have hev : (fun t => χ t • (h t - G t)) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] (fun t => h t - G t) := by
      filter_upwards [show Set.Iic (δ/4) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 from
        nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : (0:ℝ) < δ/4))] with t ht
      rw [hχ_one t (Set.mem_Iic.mp ht), one_smul]
    have hpt : (fun t => χ t • (h t - G t)) 0 = (fun t => h t - G t) 0 := by
      show χ 0 • (h 0 - G 0) = h 0 - G 0
      rw [hχ_one 0 (by linarith : (0:ℝ) ≤ δ/4), one_smul]
    rw [hev.iteratedDerivWithin_eq (n := k) hpt]
    have hsub : iteratedDerivWithin k (fun t => h t - G t) (Set.Ici (0 : ℝ)) 0
        = iteratedDerivWithin k h (Set.Ici (0 : ℝ)) 0
          - iteratedDerivWithin k G (Set.Ici (0 : ℝ)) 0 :=
      iteratedDerivWithin_sub (n := k) (x := (0:ℝ)) (s := Set.Ici (0 : ℝ)) (f := h) (g := G)
        (Set.mem_Ici.mpr le_rfl) (uniqueDiffOn_Ici 0)
        (h0.of_le (Work.Noncompact.ProperLine.coe_nat_le_inf_withTop k))
        (hG.contDiffAt.contDiffWithinAt.of_le (Work.Noncompact.ProperLine.coe_nat_le_inf_withTop k))
    rw [hsub]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
        (hG.contDiffAt.of_le (Work.Noncompact.ProperLine.coe_nat_le_inf_withTop k))
        (Set.mem_Ici.mpr le_rfl)]
    rw [hGjet k, sub_self]
  -- Step 4. Glue `0` on the left to `V` on the right.
  have hUjet : ∀ k : ℕ, 0 < k →
      iteratedDerivWithin k (fun _ : ℝ => (0 : E)) (Set.Iic (0 : ℝ)) 0 = 0 := by
    intro k _
    exact iteratedDerivWithin_fun_const_zero
  have hflat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Noncompact.ProperLine.flatGlue (fun _ : ℝ => (0:E)) V 0) 0 := by
    have hall : ∀ n : ℕ, ContDiff ℝ (↑n : WithTop ℕ∞)
        (Work.Noncompact.ProperLine.flatGlue (fun _ : ℝ => (0:E)) V 0) := by
      intro n
      rw [contDiff_iff_contDiffAt]
      intro x
      rcases lt_trichotomy x 0 with hx | rfl | hx
      · refine (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Iio.mem_nhds hx] with t ht
        rw [Work.Noncompact.ProperLine.flatGlue_of_le (le_of_lt ht)]
      · exact Work.Noncompact.ProperLine.contDiffAt_flatGlue_nat (F := E) n
          ((contDiff_const (c := (0:E))).contDiffOn) hV hV0.symm hUjet hVjet
      · have hVA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V x :=
          (contDiffWithinAt_iff_contDiffAt (Ici_mem_nhds hx)).mp (hV x (le_of_lt hx))
        refine (hVA.of_le (Work.Noncompact.ProperLine.coe_nat_le_inf_withTop n)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hx] with t ht
        rw [Work.Noncompact.ProperLine.flatGlue_of_gt ht]
    exact ((contDiff_all_iff_nat.mpr hall) ⊤).contDiffAt
  -- Step 5. The flat piece `K`.
  have hmain : ∀ t : ℝ, t ≤ δ/4 →
      (if t ≤ 0 then (0:E) else h t - G t)
        = Work.Noncompact.ProperLine.flatGlue (fun _ : ℝ => (0:E)) V 0 t := by
    intro t ht
    by_cases ht0 : t ≤ 0
    · rw [if_pos ht0, Work.Noncompact.ProperLine.flatGlue_of_le ht0]
    · rw [if_neg ht0, Work.Noncompact.ProperLine.flatGlue_of_gt (lt_of_not_ge ht0)]
      rw [hVdef]
      show h t - G t = χ t • (h t - G t)
      rw [hχ_one t ht, one_smul]
  have hK : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => if t ≤ 0 then (0:E) else h t - G t) 0 := by
    refine hflat.congr_of_eventuallyEq ?_
    filter_upwards [Iic_mem_nhds (show (0:ℝ) < δ/4 by linarith)] with t ht
    exact hmain t ht
  -- Step 6. Assemble `F = G + K` and check the two required properties.
  set F : ℝ → E := fun t => G t + (if t ≤ 0 then (0:E) else h t - G t) with hFdef
  have hFsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo (-δ) δ) := by
    intro x hx
    rw [contDiffWithinAt_iff_contDiffAt (Ioo_mem_nhds hx.1 hx.2)]
    rcases lt_trichotomy x 0 with hx0 | rfl | hx0
    · refine hG.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx0] with t ht
      rw [hFdef]
      show G t + (if t ≤ 0 then (0:E) else h t - G t) = G t
      rw [if_pos (le_of_lt ht), add_zero]
    · rw [hFdef]
      exact hG.contDiffAt.add hK
    · refine (hsm.contDiffAt (Ioo_mem_nhds hx0 hx.2)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx0 hx.2] with t ht
      rw [hFdef]
      show G t + (if t ≤ 0 then (0:E) else h t - G t) = h t
      rw [if_neg (not_le.mpr ht.1), add_sub_cancel]
  have hFagree : ∀ t : ℝ, 0 ≤ t → t < δ → F t = h t := by
    intro t _ _
    rw [hFdef]
    show G t + (if t ≤ 0 then (0:E) else h t - G t) = h t
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ t from by assumption) with ht0' | rfl
    · rw [if_neg (not_le.mpr ht0'), add_sub_cancel]
    · rw [if_pos le_rfl, add_zero]
      exact hG0
  exact ⟨F, hFsmooth, hFagree⟩

end Work.Drive.Rays
