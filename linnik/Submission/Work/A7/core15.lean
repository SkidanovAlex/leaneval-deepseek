import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.A7.grid_sum_bound
import Submission.Work.A7.grid_sum_boundR
import Submission.Work.A7.Cf_nonpos
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.A7.ExpWf_antitone
import Submission.Work.A7.lamChar_api
import Submission.Work.A7.box_api7
import Submission.Work.A7.chi1_inv_api

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
noncomputable section

open Work.LinnikContract
open Work.LinnikAreas.A7

/-! ## Membership API for `Aset` -/

lemma mem_Aset {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q} :
    χ ∈ Work.LinnikAreas.A7.Aset q R ↔
      χ ≠ 1 ∧ ∃ ρ : ℂ, InBox q R ρ ∧ zeroMult χ ρ ≠ 0 := by
  simp only [Work.LinnikAreas.A7.Aset, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    and_true]

lemma mem_Aset_ne_one {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q}
    (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) : χ ≠ 1 := (mem_Aset.mp hχ).1

lemma mem_Aset_box {q : ℕ} [NeZero q] {R : ℝ} {χ : DirichletCharacter ℂ q}
    (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) :
    ∃ ρ : ℂ, InBox q R ρ ∧ zeroMult χ ρ ≠ 0 := (mem_Aset.mp hχ).2

lemma exists_isZ_le_R_of_mem_Aset {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R : ℝ}
    (hRlog : R ≤ Real.log q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) :
    ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ R := by
  obtain ⟨ρ, hbox, hzm⟩ := mem_Aset_box hχ
  exact ⟨ρ, box_api7_p1 hq hRlog (mem_Aset_ne_one hχ) hzm hbox, hbox.1⟩

lemma lamChar_le_R_of_mem_Aset {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R : ℝ}
    (hRlog : R ≤ Real.log q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) : lamChar χ ≤ R := by
  obtain ⟨ρ, hZ, hle⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχ
  exact le_trans (lamChar_le_lamOf hq hZ) hle

lemma lamChar_le_lamOf_of_box {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R : ℝ}
    (hRlog : R ≤ Real.log q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) {ρ : ℂ}
    (hbox : InBox q R ρ) (hzm : zeroMult χ ρ ≠ 0) : lamChar χ ≤ lamOf q ρ :=
  lamChar_le_lamOf hq (box_api7_p1 hq hRlog (mem_Aset_ne_one hχ) hzm hbox)

/-! ## The per-character `WBox` bound -/

lemma WBox_le_Phi {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η : ℝ} (hRlog : R ≤ Real.log q)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    {χ : DirichletCharacter ℂ q} (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (lamChar χ)
        + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))) := by
  have hne := mem_Aset_ne_one hχ
  have hnn : 0 ≤ lamChar χ := lamChar_nonneg_of_hq hq χ
  have hleR : lamChar χ ≤ R := lamChar_le_R_of_mem_Aset hq hRlog hχ
  have hW := Work.LinnikAreas.A7.WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ
    (fun ρ hbox hzm => lamChar_le_lamOf_of_box hq hRlog hχ hbox hzm)
  have hb := hPC χ hne (lamChar χ) hnn hleR (fun ρ hZ => lamChar_le_lamOf hq hZ)
  have hexp : (0:ℝ) ≤ Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ)) := Real.exp_nonneg _
  have h1 : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ)) *
        (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) (lamChar χ) + η)) :=
    le_trans hW (mul_le_mul_of_nonneg_left hb hexp)
  have h2 : Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ)) *
        (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) (lamChar χ) + η))
      = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (lamChar χ)
        + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))) := by
    rw [Work.LinnikAreas.A7.Phi, Work.LinnikAreas.A7.Kc]
    ring
  rwa [h2] at h1

/-! ## Small facts about `Wf` and `Cf` -/

/-- `Wf x ≥ 0` for `x ≥ 0` (with `Wf 0 = 0`). -/
lemma Wf_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Work.LinnikAreas.A7.Wf x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    rw [Work.LinnikAreas.A7.Wf, Work.LinnikContract.wHB]
    simp
  · exact le_of_lt (Wf_pos h)

/-- `C(Λ,Λ) = 0`. -/
lemma Cf_self {Λ : ℝ} (hΛ : 0 < Λ) : Work.LinnikAreas.A7.Cf Λ Λ = 0 := by
  have hne : Work.LinnikAreas.A7.Wf Λ ≠ 0 := ne_of_gt (Wf_pos hΛ)
  have h : Work.LinnikAreas.A7.Phi Λ
      - Work.LinnikAreas.A7.Phi Λ * Work.LinnikAreas.A7.Wf Λ / Work.LinnikAreas.A7.Wf Λ = 0 := by
    field_simp
    ring
  rw [Work.LinnikAreas.A7.Cf, h, max_self]

/-! ## Splitting the per-character bound -/

lemma Phi_exp_le_Wf_hi {Λ lam η : ℝ} (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam : Λ ≤ lam) :
    Work.LinnikAreas.A7.Phi lam + η * Real.exp (-(Work.LinnikAreas.A7.ac * lam)) ≤
      (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ
        + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ)) / Work.LinnikAreas.A7.Wf Λ))
        * Work.LinnikAreas.A7.Wf lam := by
  have hlam0 : 0 < lam := lt_of_lt_of_le hΛ hlam
  have hWl : 0 < Work.LinnikAreas.A7.Wf lam := Wf_pos hlam0
  have hR : Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam ≤
      Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ :=
    PhiWf_antitone hΛ hlam
  have hE : Real.exp (-(Work.LinnikAreas.A7.ac * lam)) / Work.LinnikAreas.A7.Wf lam ≤
      Real.exp (-(Work.LinnikAreas.A7.ac * Λ)) / Work.LinnikAreas.A7.Wf Λ := by
    have h := ExpWf_antitone hΛ hlam
    simpa only [Work.LinnikAreas.A7.ac] using h
  have hne : Work.LinnikAreas.A7.Wf lam ≠ 0 := ne_of_gt hWl
  have h1 : Work.LinnikAreas.A7.Phi lam
      = (Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam) * Work.LinnikAreas.A7.Wf lam := by
    field_simp
  have h2 : Real.exp (-(Work.LinnikAreas.A7.ac * lam))
      = (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) / Work.LinnikAreas.A7.Wf lam) * Work.LinnikAreas.A7.Wf lam := by
    field_simp
  rw [h1, h2]
  have hsum : Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam
        + η * (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) / Work.LinnikAreas.A7.Wf lam)
      ≤ Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ
        + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ)) / Work.LinnikAreas.A7.Wf Λ) :=
    add_le_add hR (mul_le_mul_of_nonneg_left hE hη)
  calc (Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam) * Work.LinnikAreas.A7.Wf lam
        + η * ((Real.exp (-(Work.LinnikAreas.A7.ac * lam)) / Work.LinnikAreas.A7.Wf lam)
            * Work.LinnikAreas.A7.Wf lam)
      = (Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam
          + η * (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) / Work.LinnikAreas.A7.Wf lam))
          * Work.LinnikAreas.A7.Wf lam := by ring
    _ ≤ (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ
          + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ)) / Work.LinnikAreas.A7.Wf Λ))
          * Work.LinnikAreas.A7.Wf lam :=
        mul_le_mul_of_nonneg_right hsum (le_of_lt hWl)

lemma Phi_eq_Cf_add {Λ lam lam1 : ℝ} (hΛ : 0 < Λ) (hlam1 : 0 < lam1) (hp : lam1 ≤ lam)
    (hle : lam ≤ Λ) :
    Work.LinnikAreas.A7.Phi lam = Work.LinnikAreas.A7.Cf Λ lam
      + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikAreas.A7.Wf lam := by
  have hlam0 : 0 < lam := lt_of_lt_of_le hlam1 hp
  have hW : 0 < Work.LinnikAreas.A7.Wf lam := Wf_pos hlam0
  have hne : Work.LinnikAreas.A7.Wf lam ≠ 0 := ne_of_gt hW
  have hR : Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ ≤
      Work.LinnikAreas.A7.Phi lam / Work.LinnikAreas.A7.Wf lam :=
    PhiWf_antitone hlam0 hle
  have hpos : 0 ≤ Work.LinnikAreas.A7.Phi lam
      - Work.LinnikAreas.A7.Phi Λ * Work.LinnikAreas.A7.Wf lam / Work.LinnikAreas.A7.Wf Λ := by
    have h := mul_le_mul_of_nonneg_right hR (le_of_lt hW)
    rw [div_mul_cancel₀ _ hne] at h
    rw [sub_nonneg]
    calc Work.LinnikAreas.A7.Phi Λ * Work.LinnikAreas.A7.Wf lam / Work.LinnikAreas.A7.Wf Λ
        = (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikAreas.A7.Wf lam := by ring
      _ ≤ Work.LinnikAreas.A7.Phi lam := h
  rw [Work.LinnikAreas.A7.Cf, max_eq_right hpos]
  field_simp
  ring

lemma WBox_le_Cf {q : ℕ} [NeZero q] {R Λ η lam1 : ℝ} (hq : 2 ≤ q) (hRlog : R ≤ Real.log q)
    (hΛ : 0 < Λ) (hlam1 : 0 < lam1) (hη : 0 ≤ η)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    {χ : DirichletCharacter ℂ q} (hχ : χ ∈ Work.LinnikAreas.A7.Aset q R)
    (hge : lam1 ≤ lamChar χ) (hle : lamChar χ ≤ Λ) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikAreas.A7.Cf Λ (lamChar χ)
        + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikAreas.A7.Wf (lamChar χ)
        + η) := by
  have hbase := WBox_le_Phi hq hRlog hPC hχ
  have hlam0 : 0 < lamChar χ := lt_of_lt_of_le hlam1 hge
  have hE1 : Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Work.LinnikAreas.A7.ac_pos]
  have hPeq := Phi_eq_Cf_add hΛ hlam1 hge hle
  have hmain : Work.LinnikAreas.A7.Phi (lamChar χ)
        + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))
      ≤ Work.LinnikAreas.A7.Cf Λ (lamChar χ)
        + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikAreas.A7.Wf (lamChar χ) + η := by
    rw [hPeq]
    have := mul_le_of_le_one_right hη hE1
    linarith
  calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (lamChar χ)
          + η * Real.exp (-(Work.LinnikAreas.A7.ac * lamChar χ))) := hbase
    _ ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Cf Λ (lamChar χ)
          + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikAreas.A7.Wf (lamChar χ) + η) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)


theorem core15 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R Λ η εw lam₁ CST1 CST2 TOTAL ETAB : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {s : ℕ} {N : ℕ → ℕ} {n₁ : ℕ} {c₀ l₂ l₃ : ℝ}
    (S1 : Finset (DirichletCharacter ℂ q))
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hc0 : 0 < c₀) (hl2 : 0 < l₂)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (h348 : (348:ℝ)/1000 ≤ lam₁) (hlam1Λ : lam₁ ≤ Λ) (hlam1c0 : lam₁ ≤ c₀)
    (hLam0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ c₀) (hLam2 : Work.LinnikContract.Lam2Bound χ₁ l₂)
    (hLam3 : Work.LinnikContract.Lam3Bound χ₁ l₃)
    (hS1sub : S1 ⊆ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)))
    (hS1chi1 : (χ₁ ∈ S1) ↔ (χ₁ ∈ Work.LinnikAreas.A7.Aset q R))
    (hS1inv : (χ₁⁻¹ ∈ S1) ↔ (χ₁⁻¹ ∈ Work.LinnikAreas.A7.Aset q R))
    (hS1lam : ∀ χ ∈ S1, Work.LinnikContract.lamChar χ = lam₁)
    (hS1card : (S1.card : ℝ) ≤ (n₁ : ℝ))
    (hS1term : ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (S1.card : ℝ) *
        (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * Work.LinnikContract.wHB lam₁ + η))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η))
    (hcount : ∀ j ≤ s, (Work.LinnikContract.Ncount q (Λ - (25:ℝ)/1000 * (j:ℝ)) : ℝ) ≤ (N j : ℝ))
    (hle3 : min l₃ Λ ≤ Λ - (25:ℝ)/1000 * (s:ℝ))
    (hlam1small : lam₁ ≤ Λ - (25:ℝ)/1000 * (s:ℝ))
    (hcred : Work.LinnikAreas.A7.Cf Λ (min l₃ Λ) ≤ CST2) (hcred12 : CST2 ≤ CST1)
    (hcred2 : Work.LinnikAreas.A7.Cf Λ (max l₂ lam₁) ≤ CST2)
    (hTOTAL : (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) * ((67:ℝ)/6 + εw) + (n₁:ℝ) * CST1 + 2 * CST2
        + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * Work.LinnikAreas.A7.Cf Λ (min l₃ Λ)
        + ∑ j ∈ Finset.range s, ((N j : ℝ) - (N (j+1) : ℝ)) * Work.LinnikAreas.A7.Cf Λ (Λ - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ TOTAL)
    (hETAB : (Real.exp (-(Work.LinnikAreas.A7.ac*Λ)) / Work.LinnikAreas.A7.Wf Λ) * ((67:ℝ)/6 + εw) + (N 0 : ℝ) + 4 ≤ ETAB) :
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
  have hkRle : kR ≤ (n₁:ℝ) := by rw [hkR]; exact hS1card
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
    have hm := hS1sub hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · rw [h]; exact hS1chi1.mp (by rw [← h]; exact hχ)
    · rw [h]; exact hS1inv.mp (by rw [← h]; exact hχ)
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
      rw [h]
      exact hS1chi1.mpr (h ▸ hAm)
    · intro h
      apply hnotS1
      rw [h]
      exact hS1inv.mpr (h ▸ hAm)
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
      have h4 : 0 ≤ kR := by rw [hkR]; exact Nat.cast_nonneg _
      linarith [mul_nonneg h4 h2]
    linarith [hSbudget]
  have hetabudget : kR + (B2.card : ℝ) ≤ (N 0 : ℝ) := by
    have hcard : Alo.card = S1.card + B2.card := by
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
      rw [hcard, hkR]; push_cast; ring
    linarith [h1, h2, hcardR]
  -- ---------- the C-function at the threshold ----------
  have hCτ : Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) lam₁) ≤ q0 := by
    rw [hq0]
    rcases lt_or_ge (min l₃ Λ) lam₁ with h | h
    · rw [max_eq_right h.le]
      rcases lt_or_ge (0:ℝ) (min l₃ Λ) with h0 | h0
      · exact Cf_antitone (fun hx hxy => PhiWf_antitone hx hxy) hΛ h0 h.le
      · exact Cf_nonpos h348 hlam1Λ h0
    · rw [max_eq_left h]
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
  have hL_bound : ∀ χ ∈ Lf, Work.LinnikAreas.A7.Cf Λ (max (lamChar χ) lam₁) ≤ CST2 := by
    intro χ hχ
    have h1 : lam₁ ≤ lamChar χ := (hB2_char χ (hL_sub_B2 hχ)).2.2
    rw [max_eq_left h1]
    have hmu : (0:ℝ) < max l₂ lam₁ := lt_of_lt_of_le hl2 (le_max_left _ _)
    have hge_mu : max l₂ lam₁ ≤ lamChar χ := max_le (hL_ge_l2 χ hχ) h1
    exact le_trans (Cf_antitone (fun hx hxy => PhiWf_antitone hx hxy) hΛ hmu hge_mu) hcred2
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
      push_neg at hcon
      have h := hχ₂ χ ρ' hZ' hne1 hne2 hcon.1 hcon.2
      rw [← heq] at h
      linarith
    calc Lf.card ≤ ({χ₂, χ₂⁻¹} : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          have h := Finset.card_insert_le χ₂ ({χ₂⁻¹} : Finset (DirichletCharacter ℂ q))
          rw [Finset.card_singleton] at h
          linarith
  have hmR2 : mR ≤ 2 := by rw [hmR]; exact_mod_cast hLcard
  -- ---------- count bound ----------
  have hcount' : ∀ j ≤ s, ((B2.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ) ≤ (N j : ℝ) - kR := by
    intro j hj
    have hjle : (25:ℝ)/1000*(j:ℝ) ≤ (25:ℝ)/1000*(s:ℝ) := by
      have hj' : (j:ℝ) ≤ (s:ℝ) := by exact_mod_cast hj
      linarith
    have hS1filt : S1.filter (fun χ => lamChar χ ≤ Lam j) = S1 := by
      apply Finset.filter_true_of_mem
      intro χ hχ
      rw [hS1lam χ hχ, hLam_apply j]
      linarith [hlam1small, hjle]
    have hAloP : Alo.filter (fun χ => lamChar χ ≤ Lam j)
        = S1 ∪ B2.filter (fun χ => lamChar χ ≤ Lam j) := by
      rw [← hunion, Finset.filter_union, hS1filt]
    have hdisjP : Disjoint S1 (B2.filter (fun χ => lamChar χ ≤ Lam j)) :=
      hdisj.mono_right (Finset.filter_subset _ _)
    have hcardP : (Alo.filter (fun χ => lamChar χ ≤ Lam j)).card
        = S1.card + (B2.filter (fun χ => lamChar χ ≤ Lam j)).card := by
      rw [hAloP, Finset.card_union_of_disjoint hdisjP]
    have hsub : Alo.filter (fun χ => lamChar χ ≤ Lam j) ⊆
        Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ Lam j) := by
      intro χ hχ
      obtain ⟨hχAlo, hχP⟩ := Finset.mem_filter.mp hχ
      rw [hAlo] at hχAlo
      obtain ⟨hAm, -⟩ := Finset.mem_filter.mp hχAlo
      rw [hA] at hAm
      obtain ⟨ρ, hZ, -⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hAm
      obtain ⟨ρ', hZ', heq⟩ := exists_lamChar_eq_lamOf ⟨ρ, hZ⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ρ', hZ', by rw [← heq]; exact hχP⟩
    have hNc : ((Alo.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ)
        ≤ (Work.LinnikContract.Ncount q (Lam j) : ℝ) := by
      rw [Work.LinnikContract.Ncount]
      exact_mod_cast Finset.card_le_card hsub
    have hNj : (Work.LinnikContract.Ncount q (Lam j) : ℝ) ≤ (N j : ℝ) := by
      have h := hcount j hj; rw [hLam_apply j]; exact h
    have hcardR : ((Alo.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ)
        = (S1.card : ℝ) + ((B2.filter (fun χ => lamChar χ ≤ Lam j)).card : ℝ) := by
      rw [hcardP]; push_cast; ring
    rw [hkR]
    linarith [hNc, hNj, hcardR]
  -- ---------- the ordering used for the tails ----------
  have hN0s_ge : mR ≤ (N s : ℝ) - kR := by
    have h1 := hcount' s le_rfl
    have hsub : Lf ⊆ B2.filter (fun χ => lamChar χ ≤ Lam s) := by
      intro χ hχ
      have hχ' := hL_sub_B2 hχ
      rw [Finset.mem_filter]
      refine ⟨hχ', ?_⟩
      have hlt : lamChar χ < min l₃ Λ := hLg χ hχ
      have hMs : Lam s = Λ - (25:ℝ)/1000*(s:ℝ) := hLam_apply s
      have hminle : min l₃ Λ ≤ Λ - (25:ℝ)/1000*(s:ℝ) := by rw [← hMs] at hle3; exact hle3
      linarith
    have h2 : (Lf.card : ℝ) ≤ ((B2.filter (fun χ => lamChar χ ≤ Lam s)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [hmR]
    linarith [h1, h2]
  -- ---------- C-sum via Abel summation ----------
  have hmono : ∀ x y : ℝ, x ≤ y → (fun t => Work.LinnikAreas.A7.Cf Λ (max t lam₁)) y
      ≤ (fun t => Work.LinnikAreas.A7.Cf Λ (max t lam₁)) x := by
    intro x y hxy
    exact Cf_antitone (fun hx hxy => PhiWf_antitone hx hxy) hΛ
      (lt_of_lt_of_le hpos348 (le_max_right _ _)) (max_le_max hxy le_rfl)
  have hC0 : (fun t => Work.LinnikAreas.A7.Cf Λ (max t lam₁)) (Lam 0) = 0 := by
    have h0 : Lam 0 = Λ := by rw [hLam_apply 0]; simp
    show Work.LinnikAreas.A7.Cf Λ (max (Lam 0) lam₁) = 0
    rw [h0, max_eq_left hlam1Λ]
    exact Cf_self hΛ
  have hdec : ∀ j, j < s → Lam (j+1) ≤ Lam j := by
    intro j hj
    rw [hLam_apply (j+1), hLam_apply j]
    push_cast
    linarith
  have hLamS : min l₃ Λ ≤ Lam s := by rw [hLam_apply s]; exact hle3
  have hCsum : CfB2 ≤ mR * CST2 + ((N s : ℝ) - kR - mR) * q0 + Dsum := by
    have hg := grid_sum_boundR (A := B2) (L := Lf) (g := fun χ => lamChar χ) (Lam := Lam)
      (C := fun t => Work.LinnikAreas.A7.Cf Λ (max t lam₁))
      (N0 := fun j => (N j : ℝ) - kR) (s := s) (lamS := min l₃ Λ)
      hL_sub_B2 (fun a ha => hLg a ha)
      (fun a ha hle => by
        by_cases hh : min l₃ Λ ≤ lamChar a
        · exact Or.inl hh
        · exact Or.inr (by rw [hLf, Finset.mem_filter]; exact ⟨ha, lt_of_not_ge hh⟩))
      hLamS hdec hmono hC0 hcount'
    have hfilP : B2.filter (fun a => lamChar a ≤ Lam 0) = B2 := by
      apply Finset.filter_true_of_mem
      intro a ha
      have h0 : Lam 0 = Λ := by rw [hLam_apply 0]; simp
      rw [h0]; exact (hB2_char a ha).2.1
    have hLHS : (∑ a ∈ B2.filter (fun a => lamChar a ≤ Lam 0),
          Work.LinnikAreas.A7.Cf Λ (max (lamChar a) lam₁)) = CfB2 := by
      rw [hfilP, hCfB2]
      apply Finset.sum_congr rfl
      intro a ha
      rw [max_eq_left (hge a (hB2_char a ha).1)]
    have hLsum : (∑ a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (max (lamChar a) lam₁)) ≤ mR * CST2 := by
      rw [hmR]
      calc ∑ a ∈ Lf, Work.LinnikAreas.A7.Cf Λ (max (lamChar a) lam₁)
          ≤ ∑ _a ∈ Lf, CST2 := Finset.sum_le_sum (fun a ha => hL_bound a ha)
        _ = (Lf.card : ℝ) * CST2 := by rw [Finset.sum_const, nsmul_eq_mul]
    have htail : (((N s : ℝ) - kR) - mR) * Work.LinnikAreas.A7.Cf Λ (max (min l₃ Λ) lam₁)
        ≤ (((N s : ℝ) - kR) - mR) * q0 :=
      mul_le_mul_of_nonneg_left hCτ (by linarith [hN0s_ge])
    have hstair : (∑ j ∈ Finset.range s,
          (((N j : ℝ) - kR) - ((N (j+1) : ℝ) - kR)) * Work.LinnikAreas.A7.Cf Λ (max (Lam (j+1)) lam₁))
        = Dsum := by
      rw [hDsum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j+1 ≤ s := by simp only [Finset.mem_range] at hj; omega
      have hge_lam1 : lam₁ ≤ Lam (j+1) := by
        rw [hLam_apply (j+1)]
        have hjle' : ((j+1:ℕ):ℝ) ≤ (s:ℝ) := by exact_mod_cast hjle
        have : (25:ℝ)/1000*((j+1:ℕ):ℝ) ≤ (25:ℝ)/1000*(s:ℝ) := by linarith
        linarith [hlam1small]
      have hLameq : Lam (j+1) = Λ - (25:ℝ)/1000 * ((j:ℝ)+1) := by
        rw [hLam_apply (j+1)]; push_cast; ring
      rw [max_eq_left hge_lam1, hLameq]
      ring
    linarith [hg, hLHS, hLsum, htail, hstair]
  -- ---------- credit ----------
  have hcredit : kR * CST1 + mR * CST2 + ((N s : ℝ) - kR - mR) * q0
      ≤ (n₁:ℝ) * CST1 + 2 * CST2 + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 := by
    have hk : kR ≤ (n₁:ℝ) := hkRle
    have hm : mR ≤ 2 := hmR2
    have hstep : (N s : ℝ) - kR - mR ≤ max 0 ((N s : ℝ) - (n₁:ℝ) - 2) + ((n₁:ℝ) + 2 - kR - mR) := by
      rcases lt_or_ge (N s : ℝ) ((n₁:ℝ) + 2) with h | h
      · rw [max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith)]; linarith
    have hA' : ((N s : ℝ) - kR - mR) * q0
        ≤ max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + ((n₁:ℝ) + 2 - kR - mR) * q0 := by
      have h := mul_le_mul_of_nonneg_right hstep hq0_nn
      rw [add_mul] at h; linarith [h]
    have hB' : ((n₁:ℝ) + 2 - kR - mR) * q0 ≤ ((n₁:ℝ) - kR) * CST1 + (2 - mR) * CST2 := by
      have ha : 0 ≤ (n₁:ℝ) - kR := by linarith
      have hb : 0 ≤ 2 - mR := by linarith
      have h1 := mul_le_mul_of_nonneg_left hcq ha
      have h2 := mul_le_mul_of_nonneg_left hcq hb
      have h3 : ((n₁:ℝ) - kR) * CST2 ≤ ((n₁:ℝ) - kR) * CST1 := mul_le_mul_of_nonneg_left hcred12 ha
      linarith only [h1, h2, h3]
    linarith [hA', hB']
  have hp3 : kR * CST1 + CfB2 ≤ (n₁:ℝ) * CST1 + 2 * CST2 + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + Dsum := by
    linarith [hCsum, hcredit]
  -- ---------- the three group sums ----------
  have hAhi_sum : ∑ χ ∈ Ahi, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (rPhi + η * ePhi) * Shi := by
    rw [hShi, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    obtain ⟨hχA, hlt⟩ := Finset.mem_filter.mp (by rw [← hAhi]; exact hχ)
    exact hhi χ hχA hlt
  have hS1_sum : ∑ χ ∈ S1, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η)) := by
    have hw : Work.LinnikContract.wHB lam₁ = Work.LinnikAreas.A7.Wf lam₁ := rfl
    have heq : ((9:ℝ)/100) * kR * (CST1 + rPhi * Work.LinnikContract.wHB lam₁ + η)
        = ((9:ℝ)/100) * (kR * (CST1 + rPhi * Work.LinnikAreas.A7.Wf lam₁ + η)) := by
      rw [hw]; ring
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
  have hT : rPhi * W + (n₁:ℝ) * CST1 + 2 * CST2 + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + Dsum ≤ TOTAL := hTOTAL
  have hET : ePhi * W + (N 0 : ℝ) ≤ ETAB := by linarith [hETAB]
  have hEp : ePhi * Shi ≤ ePhi * W := mul_le_mul_of_nonneg_left hShi_le_W hePhi_nn
  have hEp2 : ePhi * Shi + kR + (B2.card : ℝ) ≤ ePhi * W + (N 0 : ℝ) := by linarith [hEp, hetabudget]
  have hp1 : rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2) ≤ rPhi * W :=
    mul_le_mul_of_nonneg_left hSbudget hrPhi_nn
  have hp2 : η * (ePhi * Shi + kR + (B2.card : ℝ)) ≤ η * (ePhi * W + (N 0 : ℝ)) :=
    mul_le_mul_of_nonneg_left hEp2 hη
  have hbr : rPhi * (Shi + kR * Work.LinnikAreas.A7.Wf lam₁ + SB2) + η * (ePhi * Shi + kR + (B2.card : ℝ)) + kR * CST1 + CfB2
      ≤ rPhi * W + η * (ePhi * W + (N 0 : ℝ)) + (n₁:ℝ) * CST1 + 2 * CST2
        + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + Dsum := by
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
            + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + Dsum) :=
          mul_le_mul_of_nonneg_left hbr (by norm_num)
      _ = ((9:ℝ)/100) * (rPhi * W + (n₁:ℝ) * CST1 + 2 * CST2
            + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * q0 + Dsum) + ((9:ℝ)/100) * η * (ePhi * W + (N 0 : ℝ)) := by
          ring
      _ ≤ ((9:ℝ)/100) * TOTAL + ((9:ℝ)/100) * η * ETAB := by
          have h1 := mul_le_mul_of_nonneg_left hT (by norm_num : (0:ℝ) ≤ (9:ℝ)/100)
          have h2 := mul_le_mul_of_nonneg_left hET (by positivity : (0:ℝ) ≤ (9:ℝ)/100 * η)
          linarith [h1, h2]
  rw [hA]
  exact hFinal


end
end Work.A7
