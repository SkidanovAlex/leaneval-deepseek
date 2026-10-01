/-
# `Work.LinnikContract2.A7.window_step` — the HB §15 step at the *narrow* pivot (round 2)

This is the §15 step used to close the **window** of the round-2 contract, i.e. the case
`¬ IsZ χ₁ ρ₁ ∧ 348/1000 ≤ λ₁` in which the numbered (wide) zero of §6 does not lie in the working
region: the §15 argument is then run at the *narrow* (working-region) minimiser `(χ₁,ρ₁)`
(`hmin : IsMin1` is **round 1's** predicate, i.e. `IsMin1H 1`), whose level `lam₁ = lamOf q ρ₁`
dominates the wide `λ₁`.  The result is `Work.A7.core15` with

* the *honest* zero count `hcount : Ncount q (Λ - 25/1000*j) ≤ N j` (no subtraction of the pivot
  pair `{χ₁,χ₁⁻¹}`, which is charged separately by `hcard`/`hS1point`) — hence, unlike `core15`,
  **no** `hlam1small` hypothesis: the pivot level `lam₁` may exceed the lowest grid level
  `Λ - 25/1000*s`, which is exactly the window case;
* the credit term `max 0 (N s - 2) * Cf Λ (min l₃ Λ)` in `hTOTAL` (`core15` has
  `max 0 (N s - n₁ - 2) * ...`), so that the S1-part is paid for by `n₁*CST1` rather than by a
  subtraction inside the count;
* two hypotheses bounding the counting function `N`: `hNdec` (the table entries decrease) and
  `hlamSpos` (the tail threshold is positive).

**Why `hlamSpos` is needed.**  `wHB 0 = 0/(1-1) = 0` by totalised division, so `Cf Λ 0 = Phi 0 =
19/9`, while `Cf Λ z → 19/9 − Phi Λ·(30/41)/Wf Λ < 19/9` as `z → 0`: `Cf Λ` is *not* decreasing on
all of `ℝ`, and `Work.A7.grid_sum_boundR` — whose hypothesis `hmono` is global — cannot be applied
to it.  The proof uses instead the globally decreasing `C t := Cf Λ (max t (min l₃ Λ))`, which
agrees with `Cf Λ` on the grid levels because `hle3 : min l₃ Λ ≤ Λ - 25/1000*s` and the levels
decrease.  Without `hlamSpos` the statement is FALSE: with a non-positive lowest grid level
`Cf Λ (min l₃ Λ) < Cf Λ (Λ - 25/1000*s)`, so inflating the counting function `N s` (which
`hcount`, a mere lower bound, allows) drives the left-hand side of `hTOTAL`, and hence `TOTAL`, to
`-∞` while the conclusion's left-hand side is fixed; the machine-checked numerical core of that
counterexample is `A7/Cf_zero_gt_neg.lean`.  `hNdec` bounds `N` from above in the same spirit.

**Proof.**  Adaptation of `Work.A7.core15`; the only structural changes are the two points above
plus the definition of `S1 := {χ₁,χ₁⁻¹} ∩ Aset q R` (instead of a hypothesis) and the derivation of
`lamChar χ = lam₁` on `S1` (`Work.A7.lamChar_eq_of_isMin1`, `Work.A7.lamChar_inv_eq`).
-/
import Mathlib
import Submission.Work.LinnikContract2.A7.WindowAPI

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.LinnikContract2.A7

open Work.LinnikContract
open Work.LinnikAreas.A7
open Work.A7

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem window_step {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R Λ η εw lam₁ CST1 CST2 TOTAL ETAB : ℝ}
    {s : ℕ} {N : ℕ → ℕ} {n₁ : ℕ} {c₀ l₂ l₃ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hc0 : 0 < c₀) (hl2 : 0 < l₂)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (h348 : (348:ℝ)/1000 ≤ lam₁) (hlam1Λ : lam₁ ≤ Λ) (hlam1c0 : lam₁ ≤ c₀)
    (hLam0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ c₀)
    (hLam2 : Work.LinnikContract.Lam2Bound χ₁ l₂)
    (hLam3 : Work.LinnikContract.Lam3Bound χ₁ l₃)
    (hcard : (((({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R).card : ℕ) : ℝ) ≤ (n₁ : ℝ))
    (hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Work.LinnikAreas.A7.Aset q R,
        Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikContract.wHB lam₁ + η))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ,
        Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) *
          (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hcount : ∀ j ≤ s, ((Work.LinnikContract.Ncount q (Λ - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (N j : ℝ))
    (hNdec : ∀ j < s, N (j+1) ≤ N j)
    (hle3 : min l₃ Λ ≤ Λ - (25:ℝ)/1000 * (s:ℝ))
    (hlamSpos : 0 < min l₃ Λ)
    (hcred : Work.LinnikAreas.A7.Cf Λ (min l₃ Λ) ≤ CST2) (hcred12 : CST2 ≤ CST1)
    (hcred2 : Work.LinnikAreas.A7.Cf Λ l₂ ≤ CST2)
    (hTOTAL : (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * ((67:ℝ)/6 + εw)
        + (n₁:ℝ) * CST1 + 2 * CST2
        + max 0 ((N s : ℝ) - 2) * Work.LinnikAreas.A7.Cf Λ (min l₃ Λ)
        + ∑ j ∈ Finset.range s,
            ((N j : ℝ) - (N (j+1) : ℝ)) * Work.LinnikAreas.A7.Cf Λ (Λ - (25:ℝ)/1000 * ((j:ℝ)+1))
        ≤ TOTAL)
    (hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac*Λ)) / Work.LinnikAreas.A7.Wf Λ) * ((67:ℝ)/6 + εw)
        + (N 0 : ℝ) + 4 ≤ ETAB) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * TOTAL + ((9:ℝ)/100) * η * ETAB := by
  classical
  have hpos348 : (0:ℝ) < lam₁ := lt_of_lt_of_le (by norm_num) h348
  have hWΛ : 0 < Work.LinnikAreas.A7.Wf Λ := Wf_pos hΛ
  have hWlam1 : 0 < Work.LinnikAreas.A7.Wf lam₁ := Wf_pos hpos348
  set A : Finset (DirichletCharacter ℂ q) := Work.LinnikAreas.A7.Aset q R with hA
  set W : ℝ := (67:ℝ)/6 + εw with hW
  set rPhi : ℝ := Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ with hrPhi
  set ePhi : ℝ := Real.exp (-(Work.LinnikAreas.A7.ac * Λ)) / Work.LinnikAreas.A7.Wf Λ with hePhi
  set q0 : ℝ := Work.LinnikAreas.A7.Cf Λ (min l₃ Λ) with hq0
  set Lam : ℕ → ℝ := fun j => Λ - (25:ℝ)/1000 * (j:ℝ) with hLam
  have hLam_apply : ∀ j : ℕ, Lam j = Λ - (25:ℝ)/1000 * (j:ℝ) := by intro j; rw [hLam]
  set S1 : Finset (DirichletCharacter ℂ q) :=
    ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ A with hS1
  set Ahi : Finset (DirichletCharacter ℂ q) := A.filter (fun χ => Λ < lamChar χ) with hAhi
  set Alo : Finset (DirichletCharacter ℂ q) := A.filter (fun χ => lamChar χ ≤ Λ) with hAlo
  set B2 : Finset (DirichletCharacter ℂ q) := Alo \ S1 with hB2
  set Lf : Finset (DirichletCharacter ℂ q) := B2.filter (fun χ => lamChar χ < min l₃ Λ) with hLf
  set kR : ℝ := (S1.card : ℝ) with hkR
  set mR : ℝ := (Lf.card : ℝ) with hmR
  set Shi : ℝ := ∑ χ ∈ Ahi, Work.LinnikAreas.A7.Wf (lamChar χ) with hShi
  set SB2 : ℝ := ∑ χ ∈ B2, Work.LinnikAreas.A7.Wf (lamChar χ) with hSB2
  set CfB2 : ℝ := ∑ χ ∈ B2, Work.LinnikAreas.A7.Cf Λ (lamChar χ) with hCfB2
  set Dsum : ℝ := ∑ j ∈ Finset.range s, ((N j : ℝ) - (N (j+1) : ℝ)) * Work.LinnikAreas.A7.Cf Λ (Λ - (25:ℝ)/1000 * ((j:ℝ)+1)) with hDsum
  have hrPhi_nn : 0 ≤ rPhi := by
    rw [hrPhi]
    exact div_nonneg (le_of_lt (mul_pos (Real.exp_pos _) (Work.LinnikContract.API.Bfun_pos (by norm_num [Work.LinnikAreas.A7.Kc]) hΛ))) (le_of_lt hWΛ)
  have hePhi_nn : 0 ≤ ePhi := by rw [hePhi]; exact div_nonneg (Real.exp_nonneg _) (le_of_lt hWΛ)
  have hq0_nn : 0 ≤ q0 := by rw [hq0, Work.LinnikAreas.A7.Cf]; exact le_max_left _ _
  have hcq : q0 ≤ CST2 := hcred
  have hCST2nn : 0 ≤ CST2 := le_trans hq0_nn hcq
  have hkRle : kR ≤ (n₁:ℝ) := by rw [hkR, hS1]; exact hcard
  -- ---------- membership facts ----------
  have hexists_isZ : ∀ χ ∈ A, ∃ ρ, IsZ χ ρ := by
    intro χ hχ
    rw [hA] at hχ
    obtain ⟨ρ, hZ, -⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχ
    exact ⟨ρ, hZ⟩
  have hge : ∀ χ ∈ A, lam₁ ≤ lamChar χ := by
    intro χ hχ
    obtain ⟨ρ, hZ⟩ := hexists_isZ χ hχ
    have h := isMin1_lamOf_le_lamChar hmin ⟨ρ, hZ⟩
    rwa [hlam1] at h
  have hWboxA : ∀ χ ∈ A, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (lamChar χ)
          + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))) := by
    intro χ hχ
    rw [hA] at hχ
    exact WBox_le_Phi hq hRlog hPC hχ
  have hhi : ∀ χ ∈ A, Λ < lamChar χ → Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (rPhi + η * ePhi) * Work.LinnikAreas.A7.Wf (lamChar χ) := by
    intro χ hχ hlt
    have h1 := hWboxA χ hχ
    have h2 : Work.LinnikAreas.A7.Phi (lamChar χ) + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))
        ≤ (rPhi + η * ePhi) * Work.LinnikAreas.A7.Wf (lamChar χ) := by
      rw [hrPhi, hePhi]
      exact Phi_exp_le_Wf_hi hΛ hη hlt.le
    calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (lamChar χ)
            + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))) := h1
      _ ≤ ((9:ℝ)/100) * ((rPhi + η * ePhi) * Work.LinnikAreas.A7.Wf (lamChar χ)) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = ((9:ℝ)/100) * (rPhi + η * ePhi) * Work.LinnikAreas.A7.Wf (lamChar χ) := by ring
  have hlo : ∀ χ ∈ A, lamChar χ ≤ Λ → Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Cf Λ (lamChar χ)
          + rPhi * Work.LinnikAreas.A7.Wf (lamChar χ) + η) := by
    intro χ hχ hle
    have h := WBox_le_Cf hq hRlog hΛ hpos348 hη hPC (by rwa [← hA]) (hge χ hχ) hle
    rw [hrPhi]
    exact h
  -- ---------- the sets ----------
  have hS1_sub_A : S1 ⊆ A := by
    intro χ hχ
    rw [hS1] at hχ
    exact (Finset.mem_inter.mp hχ).2
  have hS1lam : ∀ χ ∈ S1, lamChar χ = lam₁ := by
    intro χ hχ
    rw [hS1] at hχ
    obtain ⟨hχp, -⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact lamChar_eq_of_isMin1 hq hmin hlam1
    · rw [Finset.mem_singleton.mp h]; exact lamChar_inv_eq hq hmin hlam1
  have hS1_sub_Alo : S1 ⊆ Alo := by
    intro χ hχ
    rw [hAlo, Finset.mem_filter]
    exact ⟨hS1_sub_A hχ, by rw [hS1lam χ hχ]; exact hlam1Λ⟩
  have hdisj : Disjoint S1 B2 := by rw [hB2]; exact Finset.disjoint_sdiff
  have hunion : S1 ∪ B2 = Alo := by rw [hB2]; exact Finset.union_sdiff_of_subset hS1_sub_Alo
  have hpart : ∀ f : DirichletCharacter ℂ q → ℝ,
      ∑ χ ∈ A, f χ = ∑ χ ∈ Ahi, f χ + ∑ χ ∈ Alo, f χ := by
    intro f
    have h1 := Finset.sum_filter_add_sum_filter_not A (fun χ : DirichletCharacter ℂ q => Λ < lamChar χ) f
    have h2 : A.filter (fun χ : DirichletCharacter ℂ q => ¬ (Λ < lamChar χ)) = Alo := by
      rw [hAlo]
      exact Finset.filter_congr (fun χ _ => not_lt)
    rw [← hAhi, h2] at h1
    exact h1.symm
  have hS1part : ∀ f : DirichletCharacter ℂ q → ℝ,
      ∑ χ ∈ Alo, f χ = ∑ χ ∈ S1, f χ + ∑ χ ∈ B2, f χ := by
    intro f
    rw [← hunion, Finset.sum_union hdisj]
  have hsum_decomp : ∑ χ ∈ A, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      = (∑ χ ∈ Ahi, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
        + (∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
        + (∑ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ) := by
    rw [hpart, hS1part]; ring
  -- ---------- character bounds for B2 ----------
  have hB2_char : ∀ χ ∈ B2, χ ∈ A ∧ lamChar χ ≤ Λ ∧ lam₁ ≤ lamChar χ := by
    intro χ hχ
    have hχ' : χ ∈ Alo \ S1 := by rwa [hB2] at hχ
    have hAlo_mem : χ ∈ Alo := (Finset.mem_sdiff.mp hχ').1
    have hmem : χ ∈ A.filter (fun χ => lamChar χ ≤ Λ) := by rwa [hAlo] at hAlo_mem
    obtain ⟨hAm, hle⟩ := Finset.mem_filter.mp hmem
    exact ⟨hAm, hle, hge χ hAm⟩
  have hB2_not : ∀ χ ∈ B2, χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹ := by
    intro χ hχ
    have hχ' : χ ∈ Alo \ S1 := by rwa [hB2] at hχ
    have hnotS1 : χ ∉ S1 := (Finset.mem_sdiff.mp hχ').2
    have hAlo_mem : χ ∈ Alo := (Finset.mem_sdiff.mp hχ').1
    have hAm : χ ∈ A := (Finset.mem_filter.mp (by rwa [hAlo] at hAlo_mem)).1
    constructor
    · intro h
      apply hnotS1
      rw [hS1, Finset.mem_inter]
      exact ⟨by rw [h]; exact Finset.mem_insert_self _ _, h ▸ hAm⟩
    · intro h
      apply hnotS1
      rw [hS1, Finset.mem_inter]
      refine ⟨?_, h ▸ hAm⟩
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self χ₁⁻¹)
  -- ---------- budget sums ----------
  have hwS1 : ∑ χ ∈ S1, Work.LinnikAreas.A7.Wf (lamChar χ) = (S1.card : ℝ) * Work.LinnikAreas.A7.Wf lam₁ := by
    have hcongr : (∑ χ ∈ S1, Work.LinnikAreas.A7.Wf (lamChar χ))
        = ∑ _χ ∈ S1, Work.LinnikAreas.A7.Wf lam₁ :=
      Finset.sum_congr rfl (fun χ hχ => by rw [hS1lam χ hχ])
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hA_sub_hS : A ⊆ hS := by
    intro χ hχ
    rw [hSiff]
    rw [hA] at hχ
    obtain ⟨ρ, hZ, hle⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχ
    exact ⟨ρ, hZ, le_trans hle hRmax⟩
  have hSbudget : Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2 ≤ W := by
    have h1 : ∑ χ ∈ A, Work.LinnikAreas.A7.Wf (lamChar χ) ≤ W :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hA_sub_hS
        (fun χ _ _ => Wf_nonneg_of_nonneg (lamChar_nonneg_of_hq hq χ))) hD1
    have h2 : (∑ χ ∈ A, Work.LinnikAreas.A7.Wf (lamChar χ)) = Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2 := by
      rw [hShi, hSB2, hkR, ← hwS1]
      rw [hpart (fun χ => Work.LinnikAreas.A7.Wf (lamChar χ))]
      rw [hS1part (fun χ => Work.LinnikAreas.A7.Wf (lamChar χ))]
      ring
    linarith [h1, h2]
  have hShi_le_W : Shi ≤ W := by
    have h1 : 0 ≤ kR * Work.LinnikAreas.A7.Wf lam₁ + SB2 := by
      have h2 : 0 ≤ Work.LinnikAreas.A7.Wf lam₁ := le_of_lt hWlam1
      have h3 : 0 ≤ SB2 := by
        rw [hSB2]; exact Finset.sum_nonneg (fun χ _ => Wf_nonneg_of_nonneg (lamChar_nonneg_of_hq hq χ))
      have h4 : 0 ≤ kR := by rw [hkR]; positivity
      linarith [mul_nonneg h4 h2]
    linarith [hSbudget]
  have hetabudget : kR + (B2.card : ℝ) ≤ (N 0 : ℝ) := by
    have hcard' : Alo.card = S1.card + B2.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hsub : Alo ⊆ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ Λ) := by
      intro χ hχ
      rw [hAlo] at hχ
      obtain ⟨hAm, hle⟩ := Finset.mem_filter.mp hχ
      rw [hA] at hAm
      obtain ⟨ρ, hZ, -⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hAm
      obtain ⟨ρ', hZ', heq⟩ := exists_lamChar_eq_lamOf ⟨ρ, hZ⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ρ', hZ', by rw [← heq]; exact hle⟩
    have h1 : (Alo.card : ℝ) ≤ (Work.LinnikContract.Ncount q Λ : ℝ) := by
      rw [Work.LinnikContract.Ncount]
      exact_mod_cast Finset.card_le_card hsub
    have h2 : (Work.LinnikContract.Ncount q Λ : ℝ) ≤ (N 0 : ℝ) := by
      have h := hcount 0 (Nat.zero_le s); simpa using h
    have hcardR : (Alo.card : ℝ) = kR + (B2.card : ℝ) := by
      rw [hcard', hkR]; push_cast; ring
    linarith [h1, h2, hcardR]
  -- ---------- character bounds for Lf ----------
  have hL_sub_B2 : Lf ⊆ B2 := by rw [hLf]; exact Finset.filter_subset _ _
  have hLg : ∀ a ∈ Lf, lamChar a < min l₃ Λ := by
    intro a ha; rw [hLf] at ha; exact (Finset.mem_filter.mp ha).2
  have hL_ge_l2 : ∀ χ ∈ Lf, l₂ ≤ lamChar χ := by
    intro χ hχ
    obtain ⟨hχA, -, -⟩ := hB2_char χ (hL_sub_B2 hχ)
    obtain ⟨hne1, hne2⟩ := hB2_not χ (hL_sub_B2 hχ)
    obtain ⟨ρ, hZ⟩ := hexists_isZ χ hχA
    obtain ⟨ρ', hZ', heq⟩ := exists_lamChar_eq_lamOf ⟨ρ, hZ⟩
    have h := hLam2 χ ρ' hZ' hne1 hne2
    rw [heq]; exact h
  have hL_bound : ∀ χ ∈ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar χ) ≤ CST2 := by
    intro χ hχ
    exact le_trans (Cf_antitone (fun hx hxy => PhiWf_antitone hx hxy) hΛ hl2 (hL_ge_l2 χ hχ)) hcred2
  have hLcard : Lf.card ≤ 2 := by
    obtain ⟨χ₂, hχ₂⟩ := hLam3
    have hsub : Lf ⊆ ({χ₂, χ₂⁻¹} : Finset (DirichletCharacter ℂ q)) := by
      intro χ hχ
      by_contra hcon
      have hχB2 := hL_sub_B2 hχ
      obtain ⟨hχA, -, -⟩ := hB2_char χ hχB2
      obtain ⟨hne1, hne2⟩ := hB2_not χ hχB2
      have hltl3 : lamChar χ < l₃ := lt_of_lt_of_le (hLg χ hχ) (min_le_left _ _)
      obtain ⟨ρ, hZ⟩ := hexists_isZ χ hχA
      obtain ⟨ρ', hZ', heq⟩ := exists_lamChar_eq_lamOf ⟨ρ, hZ⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcon
      push Not at hcon
      have h := hχ₂ χ ρ' hZ' hne1 hne2 hcon.1 hcon.2
      rw [← heq] at h
      linarith
    calc Lf.card ≤ ({χ₂, χ₂⁻¹} : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le χ₂ ({χ₂⁻¹} : Finset (DirichletCharacter ℂ q))
          rw [Finset.card_singleton] at h
          linarith
  have hmR2 : mR ≤ 2 := by rw [hmR]; exact_mod_cast hLcard
  -- ---------- the honest count bound ----------
  have hcount' : ∀ j ≤ s, ((B2.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ) ≤ (N j : ℝ) := by
    intro j hj
    have hsub : B2.filter (fun χ => lamChar χ ≤ Lam j) ⊆
        Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ Lam j) := by
      intro χ hχ
      obtain ⟨hχB2, hχP⟩ := Finset.mem_filter.mp hχ
      obtain ⟨hχA, -, -⟩ := hB2_char χ hχB2
      rw [hA] at hχA
      obtain ⟨ρ, hZ, -⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχA
      obtain ⟨ρ', hZ', heq⟩ := exists_lamChar_eq_lamOf ⟨ρ, hZ⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ρ', hZ', by rw [← heq]; exact hχP⟩
    have hNc : ((B2.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ)
        ≤ (Work.LinnikContract.Ncount q (Lam j) : ℝ) := by
      rw [Work.LinnikContract.Ncount]
      exact_mod_cast Finset.card_le_card hsub
    have hNj : (Work.LinnikContract.Ncount q (Lam j) : ℝ) ≤ (N j : ℝ) := by
      have h := hcount j hj; rw [hLam_apply j]; exact h
    linarith [hNc, hNj]
  -- ---------- the clipped C-function and the Abel summation ----------
  -- `Cf Λ` is *not* decreasing on `ℝ` (it spikes at `0`, where `Wf 0 = 0` by totalised
  -- division); `C` clips the argument into `[min l₃ Λ, Λ]`, where `Cf Λ` *is* decreasing, and
  -- agrees with `Cf Λ` on that interval.
  set C : ℝ → ℝ := fun t => Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min t Λ)) with hC
  have hmono : ∀ x y : ℝ, x ≤ y → C y ≤ C x := by
    intro x y hxy
    have h1 : min x Λ ≤ min y Λ := min_le_min hxy le_rfl
    have h2 : max (min l₃ Λ) (min x Λ) ≤ max (min l₃ Λ) (min y Λ) := max_le_max le_rfl h1
    have h3 : C y = Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min y Λ)) := by rw [hC]
    have h4 : C x = Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min x Λ)) := by rw [hC]
    rw [h3, h4]
    exact Cf_antitone (fun hx hxy => PhiWf_antitone hx hxy) hΛ
      (lt_of_lt_of_le hlamSpos (le_max_left _ _)) h2
  have hC0 : C (Lam 0) = 0 := by
    have h0 : Lam 0 = Λ := by rw [hLam_apply 0]; simp
    have hCev : C (Lam 0)
        = Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min (Lam 0) Λ)) := by rw [hC]
    have hmid : max (min l₃ Λ) (min (Lam 0) Λ) = Λ := by
      rw [h0, min_eq_left (le_refl (Λ:ℝ)), max_eq_right (min_le_right l₃ Λ)]
    rw [hCev, hmid]
    exact Cf_self hΛ
  have hCLamS : C (min l₃ Λ) = q0 := by
    rw [hC]
    show Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min (min l₃ Λ) Λ)) = q0
    rw [min_eq_left (min_le_right l₃ Λ), max_self]
  have hdec : ∀ j, j < s → Lam (j+1) ≤ Lam j := by
    intro j hj
    rw [hLam_apply (j+1), hLam_apply j]
    push_cast
    linarith
  have hLamS : min l₃ Λ ≤ Lam s := by rw [hLam_apply s]; exact hle3
  have hlamSle : ∀ j, j ≤ s → min l₃ Λ ≤ Lam j := by
    intro j hj
    have hjs : Lam s ≤ Lam j := by
      rw [hLam_apply s, hLam_apply j]
      have hj' : (j : ℝ) ≤ (s : ℝ) := by exact_mod_cast hj
      push_cast
      linarith
    linarith [hLamS, hjs]
  have hCsum : CfB2 ≤ mR * CST2 + ((N s : ℝ) - mR) * q0 + Dsum := by
    have hg := grid_sum_boundR (A := B2) (L := Lf) (g := fun χ => lamChar χ) (Lam := Lam)
      (C := C) (N0 := fun j => (N j : ℝ)) (s := s) (lamS := min l₃ Λ)
      hL_sub_B2 (fun a ha => hLg a ha)
      (fun a ha hle => by
        by_cases hh : min l₃ Λ ≤ lamChar a
        · exact Or.inl hh
        · exact Or.inr (by rw [hLf, Finset.mem_filter]; exact ⟨ha, lt_of_not_ge hh⟩))
      hLamS hdec hmono hC0 hcount'
    have hfilt : B2.filter (fun a => lamChar a ≤ Lam 0) = B2 := by
      apply Finset.filter_true_of_mem
      intro a ha
      have h0 : Lam 0 = Λ := by rw [hLam_apply 0]; simp
      rw [h0]; exact (hB2_char a ha).2.1
    have hLsum : (∑ a ∈ Lf, C (lamChar a)) = mR * q0 := by
      have h1 : ∀ a ∈ Lf, C (lamChar a) = Work.LinnikAreas.A7.Cf Λ (min l₃ Λ) := by
        intro a ha
        have hlt := hLg a ha
        have hleΛ : lamChar a ≤ Λ := le_of_lt (lt_of_lt_of_le hlt (min_le_right l₃ Λ))
        rw [hC]
        show Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min (lamChar a) Λ))
          = Work.LinnikAreas.A7.Cf Λ (min l₃ Λ)
        rw [min_eq_left hleΛ, max_eq_left (le_of_lt hlt)]
      calc (∑ a ∈ Lf, C (lamChar a))
          = ∑ _a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (min l₃ Λ) := Finset.sum_congr rfl h1
        _ = mR * q0 := by rw [Finset.sum_const, nsmul_eq_mul, hmR, hq0]
    have hstair : (∑ j ∈ Finset.range s, ((N j : ℝ) - (N (j+1) : ℝ)) * C (Lam (j+1))) = Dsum := by
      rw [hDsum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j + 1 ≤ s := by simp only [Finset.mem_range] at hj; omega
      have hge : min l₃ Λ ≤ Lam (j+1) := hlamSle (j+1) hjle
      have hle : Lam (j+1) ≤ Λ := by
        rw [hLam_apply (j+1)]
        have hnn : (0:ℝ) ≤ (((j+1 : ℕ)) : ℝ) := Nat.cast_nonneg _
        nlinarith
      have hCe : C (Lam (j+1)) = Work.LinnikAreas.A7.Cf Λ (Lam (j+1)) := by
        rw [hC]
        show Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min (Lam (j+1)) Λ))
          = Work.LinnikAreas.A7.Cf Λ (Lam (j+1))
        rw [min_eq_left hle, max_eq_right hge]
      have harge : Λ - (25:ℝ)/1000 * (((j+1 : ℕ)) : ℝ) = Λ - (25:ℝ)/1000 * ((j:ℝ)+1) := by
        push_cast; ring
      rw [hCe, hLam_apply (j+1), harge]
    have hg2 : (∑ a ∈ B2 \ Lf, C (lamChar a)) ≤ ((N s : ℝ) - mR) * q0 + Dsum := by
      have h := hg
      rw [hfilt, hLsum, hstair, hCLamS] at h
      rw [← Finset.sum_sdiff hL_sub_B2, hLsum] at h
      linarith
    have hCeq : (∑ a ∈ B2 \ Lf, C (lamChar a))
        = (∑ a ∈ B2 \ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haB2 : a ∈ B2 := (Finset.mem_sdiff.mp ha).1
      have hanL : a ∉ Lf := (Finset.mem_sdiff.mp ha).2
      have hge : min l₃ Λ ≤ lamChar a :=
        le_of_not_gt (fun hlt => hanL (by rw [hLf, Finset.mem_filter]; exact ⟨haB2, hlt⟩))
      have hle : lamChar a ≤ Λ := (hB2_char a haB2).2.1
      rw [hC]
      show Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) (min (lamChar a) Λ))
        = Work.LinnikAreas.A7.Cf Λ (lamChar a)
      rw [min_eq_left hle, max_eq_right hge]
    have hLfb : (∑ a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar a)) ≤ mR * CST2 := by
      calc (∑ a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar a))
          ≤ ∑ _a ∈ Lf, CST2 := Finset.sum_le_sum (fun a ha => hL_bound a ha)
        _ = mR * CST2 := by rw [Finset.sum_const, nsmul_eq_mul, hmR]
    have hsplit : CfB2 = (∑ a ∈ B2 \ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar a))
        + (∑ a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (lamChar a)) := by
      rw [hCfB2, ← Finset.sum_sdiff hL_sub_B2]
    rw [hsplit, ← hCeq]
    linarith [hg2, hLfb]
  -- ---------- credit ----------
  have hcredit : kR * CST1 + mR * CST2 + ((N s : ℝ) - mR) * q0
      ≤ (n₁:ℝ) * CST1 + 2 * CST2 + max 0 ((N s : ℝ) - 2) * q0 := by
    have hk : kR ≤ (n₁:ℝ) := hkRle
    have hm : mR ≤ 2 := hmR2
    have h1 : kR * CST1 ≤ (n₁:ℝ) * CST1 := by
      have h2 : (0:ℝ) ≤ (n₁:ℝ) - kR := by linarith
      have h3 : ((n₁:ℝ) - kR) * CST2 ≤ ((n₁:ℝ) - kR) * CST1 :=
        mul_le_mul_of_nonneg_left hcred12 h2
      nlinarith [h3, mul_nonneg h2 hCST2nn]
    have h4 : ((N s : ℝ) - mR) * q0
        ≤ max 0 ((N s : ℝ) - 2) * q0 + (2 - mR) * CST2 := by
      have hm2 : (0:ℝ) ≤ 2 - mR := by linarith
      have h5 : (2 - mR) * q0 ≤ (2 - mR) * CST2 := mul_le_mul_of_nonneg_left hcq hm2
      have h6 : ((N s : ℝ) - 2) * q0 ≤ max 0 ((N s : ℝ) - 2) * q0 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hq0_nn
      nlinarith [h5, h6]
    have h7 : mR * CST2 + (2 - mR) * CST2 = 2 * CST2 := by ring
    nlinarith [h1, h4, h7]
  have hp3 : kR * CST1 + CfB2 ≤ (n₁:ℝ) * CST1 + 2 * CST2
      + max 0 ((N s : ℝ) - 2) * q0 + Dsum := by
    linarith [hCsum, hcredit]
  -- ---------- the three group sums ----------
  have hAhi_sum : ∑ χ ∈ Ahi, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (rPhi + η * ePhi) * Shi := by
    rw [hShi, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    obtain ⟨hχA, hlt⟩ := Finset.mem_filter.mp (by rw [← hAhi]; exact hχ)
    exact hhi χ hχA hlt
  have hS1term : ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η)) := by
    have h1 : ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ∑ _χ ∈ S1, ((9:ℝ)/100) * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η) := by
      refine Finset.sum_le_sum (fun χ hχ => ?_)
      have hχS1 : χ ∈ S1 := hχ
      have hp := hS1point χ (show χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ A from hχS1)
      rw [hrPhi]; exact hp
    calc ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ∑ _χ ∈ S1, ((9:ℝ)/100) * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η) := h1
      _ = (S1.card : ℝ) * (((9:ℝ)/100) * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η)) := by
          rw [hkR]; ring
  have hS1_sum : ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η)) := by
    have hw : Work.LinnikContract.wHB lam₁ = Work.LinnikAreas.A7.Wf lam₁ := rfl
    have heq : ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η))
        = ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η)) := by
      rw [hw]
    exact le_trans hS1term heq.le
  have hB2_sum : ∑ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (CfB2 + rPhi * SB2 + (B2.card : ℝ) * η) := by
    have hpoint : ∀ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Cf Λ (lamChar χ)
            + rPhi * Work.LinnikAreas.A7.Wf (lamChar χ) + η) := by
      intro χ hχ
      obtain ⟨hχA, hle, -⟩ := hB2_char χ hχ
      exact hlo χ hχA hle
    calc ∑ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ∑ χ ∈ B2, ((9:ℝ)/100) * (Work.LinnikAreas.A7.Cf Λ (lamChar χ)
            + rPhi * Work.LinnikAreas.A7.Wf (lamChar χ) + η) := Finset.sum_le_sum hpoint
      _ = ((9:ℝ)/100) * ((∑ χ ∈ B2, Work.LinnikAreas.A7.Cf Λ (lamChar χ))
            + rPhi * (∑ χ ∈ B2, Work.LinnikAreas.A7.Wf (lamChar χ)) + (B2.card : ℝ) * η) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
      _ = ((9:ℝ)/100) * (CfB2 + rPhi * SB2 + (B2.card : ℝ) * η) := by rw [hCfB2, hSB2]
  -- ---------- final assembly ----------
  have hT : rPhi * W + (n₁:ℝ) * CST1 + 2 * CST2 + max 0 ((N s : ℝ) - 2) * q0 + Dsum ≤ TOTAL := hTOTAL
  have hET : ePhi * W + (N 0 : ℝ) ≤ ETAB := by linarith [hETAB]
  have hEp : ePhi * Shi ≤ ePhi * W := mul_le_mul_of_nonneg_left hShi_le_W hePhi_nn
  have hEp2 : ePhi * Shi + kR + (B2.card : ℝ) ≤ ePhi * W + (N 0 : ℝ) := by linarith [hEp, hetabudget]
  have hp1 : rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2) ≤ rPhi * W :=
    mul_le_mul_of_nonneg_left hSbudget hrPhi_nn
  have hp2 : η * (ePhi * Shi + kR + (B2.card : ℝ)) ≤ η * (ePhi * W + (N 0 : ℝ)) :=
    mul_le_mul_of_nonneg_left hEp2 hη
  have hbr : rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2) + η * (ePhi * Shi + kR + (B2.card : ℝ)) + kR * CST1 + CfB2
      ≤ rPhi * W + η * (ePhi * W + (N 0 : ℝ)) + (n₁:ℝ) * CST1 + 2 * CST2
        + max 0 ((N s : ℝ) - 2) * q0 + Dsum := by
    linarith [hp1, hp2, hp3]
  have hFinal : ∑ χ ∈ A, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * TOTAL + ((9:ℝ)/100) * η * ETAB := by
    calc ∑ χ ∈ A, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        = (∑ χ ∈ Ahi, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
          + (∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
          + (∑ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ) := hsum_decomp
      _ ≤ ((9:ℝ)/100) * (rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2)
            + η * (ePhi * Shi + kR + (B2.card : ℝ)) + kR * CST1 + CfB2) := by
          have hle : (∑ χ ∈ Ahi, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              + (∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              + (∑ χ ∈ B2, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              ≤ ((9:ℝ)/100) * ((rPhi + η * ePhi) * Shi)
                + ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η))
                + ((9:ℝ)/100) * (CfB2 + rPhi * SB2 + (B2.card : ℝ) * η) := by
            linarith [hAhi_sum, hS1_sum, hB2_sum]
          have heq : ((9:ℝ)/100) * ((rPhi + η * ePhi) * Shi)
                + ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η))
                + ((9:ℝ)/100) * (CfB2 + rPhi * SB2 + (B2.card : ℝ) * η)
              = ((9:ℝ)/100) * (rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2)
                + η * (ePhi * Shi + kR + (B2.card : ℝ)) + kR * CST1 + CfB2) := by ring
          exact le_trans hle heq.le
      _ ≤ ((9:ℝ)/100) * (rPhi * W + η * (ePhi * W + (N 0 : ℝ)) + (n₁:ℝ) * CST1 + 2 * CST2
            + max 0 ((N s : ℝ) - 2) * q0 + Dsum) :=
          mul_le_mul_of_nonneg_left hbr (by norm_num)
      _ = ((9:ℝ)/100) * (rPhi * W + (n₁:ℝ) * CST1 + 2 * CST2
            + max 0 ((N s : ℝ) - 2) * q0 + Dsum) + ((9:ℝ)/100) * η * (ePhi * W + (N 0 : ℝ)) := by
          ring
      _ ≤ ((9:ℝ)/100) * TOTAL + ((9:ℝ)/100) * η * ETAB := by
          have h1 := mul_le_mul_of_nonneg_left hT (by norm_num : (0:ℝ) ≤ (9:ℝ)/100)
          have h2 := mul_le_mul_of_nonneg_left hET (by positivity : (0:ℝ) ≤ (9:ℝ)/100 * η)
          linarith [h1, h2]
  rw [hA]
  exact hFinal

end Work.LinnikContract2.A7
