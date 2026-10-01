/-
# §15 — the uniform box-sum bound (HB §15 / Lemma 15.1) for `λ₁ ≥ 0.348`

`sec15_uniform` is the §15 branch of the area-7 assembly.  The proof is a case analysis on `λ₁`
instantiating the §15 core `Work.A7.core15` with explicit numerical data (`Λ`, grid length `s`,
Table 13 counts, and the constants `CST1`, `CST2`), all of which is generated and verified in
`Submission/Work/A7/sec15_num.lean`; the shared estimate lemmas live in `sec15_helper` and
`sec15_s1`.
-/
import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.A7.core15
import Submission.Work.A7.chi1_refined_le
import Submission.Work.A7.chi1_refined2_le
import Submission.Work.A7.chi1_second_le
import Submission.Work.A7.chi1_plain_le
import Submission.Work.A7.box_api7
import Submission.Work.A7.lamChar_api
import Submission.Work.A7.sec15_helper
import Submission.Work.A7.sec15_s1
import Submission.Work.A7.sec15_num
import Submission.Work.A7.F2K2_antitone
import Submission.Work.LinnikAreas.A7.NumRows

set_option maxHeartbeats 8000000

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract
open Work.LinnikAreas.A7

/-- `lamChar χ₁ = λ₁` for a minimal pair. -/
lemma lamChar_eq_of_isMin1 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    {lam₁ : ℝ} (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁) : lamChar χ₁ = lam₁ :=
  le_antisymm (by rw [← hlam1]; exact lamChar_le_lamOf hq hmin.1)
    (by rw [← hlam1]; exact isMin1_lamOf_le_lamChar hmin ⟨ρ₁, hmin.1⟩)

/-- `lamChar χ₁⁻¹ = λ₁` for a minimal pair. -/
lemma lamChar_inv_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    {lam₁ : ℝ} (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁) : lamChar χ₁⁻¹ = lam₁ := by
  have h0 : Lam0Bound χ₁ ρ₁ lam₁ :=
    ⟨fun _ => by rw [← hlam1], fun ρ hZ _ _ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ⟩
  exact (chi1_inv_api hq hmin h0).1.trans hlam1

/-- `Lam0Bound χ₁ ρ₁ λ₁` holds for a minimal pair. -/
lemma lam0Bound_self {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {lam₁ : ℝ}
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁) : Lam0Bound χ₁ ρ₁ lam₁ :=
  ⟨fun _ => by rw [← hlam1], fun ρ hZ _ _ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ⟩

/-- The `S₁ = {χ₁,χ₁⁻¹} ∩ Aset` cardinal bound `≤ 2`. -/
lemma card_S1_le_two {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {R : ℝ} :
    (((({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R).card : ℕ) : ℝ) ≤ 2 := by
  have h := Finset.card_le_card (Finset.inter_subset_left :
    ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R ⊆ ({χ₁, χ₁⁻¹} : Finset _))
  have h2 : (({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)).card : ℝ) ≤ 2 := by
    have h3 := Finset.card_insert_le χ₁ ({χ₁⁻¹} : Finset (DirichletCharacter ℂ q))
    rw [Finset.card_singleton] at h3
    exact_mod_cast h3
  calc _ ≤ (({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)).card : ℝ) := by exact_mod_cast h
    _ ≤ 2 := h2

/-- The `S₁` cardinal bound `≤ 1` when `χ₁` is real. -/
lemma card_S1_le_one {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {R : ℝ}
    (hinv : χ₁⁻¹ = χ₁) :
    (((({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R).card : ℕ) : ℝ) ≤ 1 := by
  have hsub : ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R ⊆ {χ₁} := by
    intro χ hχ
    have h1 : χ = χ₁ ∨ χ = χ₁⁻¹ := by
      have := (Finset.mem_inter.mp hχ).1
      simpa using this
    rw [Finset.mem_singleton]
    rcases h1 with h | h
    · exact h
    · exact h.trans hinv
  calc _ ≤ (({χ₁} : Finset (DirichletCharacter ℂ q)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = 1 := by simp

/-- Complex conjugation fixes a complex number with vanishing imaginary part. -/
lemma inv_eq_self_of_sq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (h : χ ^ 2 = 1) : χ⁻¹ = χ := by
  have h2 : χ * χ = 1 := by rw [← sq]; exact h
  exact inv_eq_of_mul_eq_one_right h2

/-- **The generic `core15` step**: assemble `S₁ = {χ₁,χ₁⁻¹} ∩ Aset` and apply the §15 core. -/
lemma sec15_step {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R Λ η εw lam₁ CST1 CST2 TOTAL ETAB : ℝ}
    {s : ℕ} {N : ℕ → ℕ} {n₁ : ℕ} {c₀ l₂ l₃ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hc0 : 0 < c₀) (hl2 : 0 < l₂)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h348 : (348:ℝ)/1000 ≤ lam₁) (hlam1Λ : lam₁ ≤ Λ) (hlam1c0 : lam₁ ≤ c₀)
    (hLam0 : Lam0Bound χ₁ ρ₁ c₀) (hLam2 : Lam2Bound χ₁ l₂) (hLam3 : Lam3Bound χ₁ l₃)
    (hcard : (((({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R).card : ℕ) : ℝ) ≤ (n₁ : ℝ))
    (hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
        WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hcount : ∀ j ≤ s, ((Ncount q (Λ - (25:ℝ)/1000 * (j:ℝ))) : ℝ) ≤ (N j : ℝ))
    (hle3 : min l₃ Λ ≤ Λ - (25:ℝ)/1000 * (s:ℝ))
    (hlam1small : lam₁ ≤ Λ - (25:ℝ)/1000 * (s:ℝ))
    (hcred : Cf Λ (min l₃ Λ) ≤ CST2) (hcred12 : CST2 ≤ CST1) (hcred2 : Cf Λ l₂ ≤ CST2)
    (hTOTAL : (Phi Λ / Wf Λ) * ((67:ℝ)/6 + εw) + (n₁:ℝ) * CST1 + 2 * CST2
        + max 0 ((N s : ℝ) - (n₁:ℝ) - 2) * Cf Λ (min l₃ Λ)
        + ∑ j ∈ Finset.range s, ((N j : ℝ) - (N (j+1) : ℝ)) * Cf Λ (Λ - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ TOTAL)
    (hETAB : (Real.exp (-(ac*Λ)) / Wf Λ) * ((67:ℝ)/6 + εw) + (N 0 : ℝ) + 4 ≤ ETAB) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * TOTAL + ((9:ℝ)/100) * η * ETAB := by
  classical
  set S1 : Finset (DirichletCharacter ℂ q) := ({χ₁, χ₁⁻¹} : Finset _) ∩ Aset q R with hS1
  have hS1sub : S1 ⊆ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) :=
    fun _ hχ => (Finset.mem_inter.mp hχ).1
  have hS1chi1 : (χ₁ ∈ S1) ↔ (χ₁ ∈ Aset q R) := by
    constructor
    · intro h; exact (Finset.mem_inter.mp h).2
    · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, h⟩
  have hS1inv : (χ₁⁻¹ ∈ S1) ↔ (χ₁⁻¹ ∈ Aset q R) := by
    constructor
    · intro h; exact (Finset.mem_inter.mp h).2
    · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩
  have hlc : lamChar χ₁ = lam₁ := lamChar_eq_of_isMin1 hq hmin hlam1
  have hS1lam : ∀ χ ∈ S1, lamChar χ = lam₁ := by
    intro χ hχ
    obtain ⟨hχp, -⟩ := Finset.mem_inter.mp hχ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχp
    rcases hχp with rfl | rfl
    · exact hlc
    · exact lamChar_inv_eq hq hmin hlam1
  have hS1card : (S1.card : ℝ) ≤ (n₁ : ℝ) := hcard
  have hS1term : ∑ χ ∈ S1, WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (S1.card : ℝ) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η) :=
    S1_sum_of S1 hS1point
  have hcred2' : Cf Λ (max l₂ lam₁) ≤ CST2 :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ hl2 (le_max_left _ _)) hcred2
  exact core15 hq S1 hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ hlam1c0 hLam0 hLam2 hLam3
    hS1sub hS1chi1 hS1inv hS1lam hS1card hS1term hS hSiff hD1 hPC hcount hle3 hlam1small
    hcred hcred12 hcred2' hTOTAL hETAB

/-- **Region V** (`λ₁ ≥ 43/40`): the crude global bound
`Σ_{χ∈A} WBox χ ≤ (9/100)(Φ/w)(λ₁)Σ w(λ_χ) + η···`, valid because `Φ/w` and `e^{-aλ}/w` are
antitone and `Σ_{χ∈A} w(λ_χ) ≤ 67/6 + εw`. -/
lemma sec15_crude {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁) (h1075 : (43:ℝ)/40 ≤ lam₁)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η)) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  classical
  have hsub : Aset q R ⊆ hS := fun χ hχ => (hSiff χ).mpr (by
    obtain ⟨ρ, hZ, hle⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχ
    exact ⟨ρ, hZ, le_trans hle hRmax⟩)
  have hW : ∑ χ ∈ Aset q R, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun χ _ _ => Wf_nonneg_of_nonneg (lamChar_nonneg_of_hq hq χ))) hD1
  have hpt : ∀ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
          + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)))) * wHB (lamChar χ) := by
    intro χ hχ
    have hne : χ ≠ 1 := mem_Aset_ne_one hχ
    have hZ : ∃ ρ : ℂ, IsZ χ ρ := by
      obtain ⟨ρ, hZ, -⟩ := exists_isZ_le_R_of_mem_Aset hq hRlog hχ
      exact ⟨ρ, hZ⟩
    obtain ⟨ρ, hZρ⟩ := hZ
    have hge : lam₁ ≤ lamChar χ := by
      rw [← hlam1]; exact isMin1_lamOf_le_lamChar hmin ⟨ρ, hZρ⟩
    have hge' : (43:ℝ)/40 ≤ lamChar χ := le_trans h1075 hge
    have hlam0 : 0 < lamChar χ := lt_of_lt_of_le (by norm_num) hge'
    have hcert : boxAbs q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) (lamChar χ) + η) :=
      hPC χ hne (lamChar χ) hlam0.le (lamChar_le_R_of_mem_Aset hq hRlog hχ)
        (fun ρ hZ => lamChar_le_lamOf hq hZ)
    have hW1 := WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ
      (fun ρ hbox hzm => lamChar_le_lamOf_of_box hq hRlog hχ hbox hzm)
    have hPhi : Phi (lamChar χ) ≤ ((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)) * wHB (lamChar χ) := by
      have h1 : Phi (lamChar χ) / Wf (lamChar χ) ≤ Phi ((43:ℝ)/40) / Wf ((43:ℝ)/40) :=
        PhiWf_antitone (by norm_num) hge'
      have h2 : Phi ((43:ℝ)/40) / Wf ((43:ℝ)/40) ≤ ((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)) := by
        have hPL : Phi ((43:ℝ)/40) ≤ ((842817:ℝ)/(100000000)) := (v_43_40).1
        have hWL : ((10208027:ℝ)/(100000000)) ≤ Wf ((43:ℝ)/40) := (v_43_40).2.2.2.1
        rw [div_le_div_iff₀ (Wf_pos (by norm_num)) (by norm_num)]
        nlinarith [hPL, hWL, (Phi_pos (by norm_num : (0:ℝ) < 43/40)).le]
      have := le_trans h1 h2
      calc Phi (lamChar χ) = Phi (lamChar χ) / Wf (lamChar χ) * Wf (lamChar χ) := by
            rw [div_mul_cancel₀]; exact ne_of_gt (Wf_pos hlam0)
        _ ≤ (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))) * wHB (lamChar χ) := by
            rw [← Wf]; exact mul_le_mul_of_nonneg_right this (Wf_pos hlam0).le
    have hExp : Real.exp (-(ac * lamChar χ))
        ≤ (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))) * wHB (lamChar χ) := by
      have h1 : Real.exp (-(ac * lamChar χ)) / Wf (lamChar χ)
          ≤ Real.exp (-(ac * ((43:ℝ)/40))) / Wf ((43:ℝ)/40) := by
        have h2 := ExpWf_antitone (x := (43:ℝ)/40) (y := lamChar χ) (by norm_num) hge'
        simpa only [ac] using h2
      have h3 : Real.exp (-(ac * ((43:ℝ)/40))) ≤ ((515649:ℝ)/(100000000)) := by
        have h4 := exF_a_43_40
        simpa only [ac] using h4
      have hWL : ((10208027:ℝ)/(100000000)) ≤ Wf ((43:ℝ)/40) := (v_43_40).2.2.2.1
      have h2 : Real.exp (-(ac * ((43:ℝ)/40))) / Wf ((43:ℝ)/40)
          ≤ (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))) := by
        rw [div_le_div_iff₀ (Wf_pos (by norm_num)) (by norm_num)]
        nlinarith [h3, hWL, Real.exp_pos (-(ac * ((43:ℝ)/40)))]
      calc Real.exp (-(ac * lamChar χ))
          = Real.exp (-(ac * lamChar χ)) / Wf (lamChar χ) * Wf (lamChar χ) := by
            rw [div_mul_cancel₀]; exact ne_of_gt (Wf_pos hlam0)
        _ ≤ (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))) * wHB (lamChar χ) := by
            rw [← Wf]; exact mul_le_mul_of_nonneg_right (le_trans h1 h2) (Wf_pos hlam0).le
    calc WBox q ((3:ℝ)/10) R χ
        ≤ Real.exp (-(ac * lamChar χ)) * boxAbs q ((3:ℝ)/10) R χ := hW1
      _ ≤ Real.exp (-(ac * lamChar χ)) * (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) (lamChar χ) + η)) :=
          mul_le_mul_of_nonneg_left hcert (Real.exp_nonneg _)
      _ = ((9:ℝ)/100) * (Phi (lamChar χ) + η * Real.exp (-(ac * lamChar χ))) := by
          rw [Phi, Kc]; ring
      _ ≤ ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)) * wHB (lamChar χ)
            + η * ((((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))) * wHB (lamChar χ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact add_le_add hPhi (by nlinarith [hExp, hη])
      _ = ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
            + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)))) * wHB (lamChar χ) := by
          ring
  have hfin : ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
        + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)))) * ((67:ℝ)/6 + εw)
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
    have hA : ((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000)
        ≤ ((9968:ℝ)/10000) := by norm_num
    have hB : ((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)) * ((67:ℝ)/6 + 1/1000)
        ≤ 1000 := by norm_num
    have hε0 : (0:ℝ) ≤ ((67:ℝ)/6 + εw) := by linarith
    have hε : ((67:ℝ)/6 + εw) ≤ ((67:ℝ)/6 + 1/1000) := by linarith
    have hη0 : 0 ≤ η := hη
    nlinarith [hA, hB, hε, hε0, hη0,
      mul_nonneg (by norm_num : (0:ℝ) ≤ (9:ℝ)/100) hη0,
      mul_le_mul_of_nonneg_left hε hη0]
  calc ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ
      ≤ ∑ χ ∈ Aset q R, ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
          + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)))) * wHB (lamChar χ) :=
        Finset.sum_le_sum hpt
    _ = ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
          + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))))
          * (∑ χ ∈ Aset q R, wHB (lamChar χ)) := by rw [Finset.mul_sum]
    _ ≤ ((9:ℝ)/100) * (((842817:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000))
          + η * (((515649:ℝ)/(100000000)) / ((10208027:ℝ)/(100000000)))) * ((67:ℝ)/6 + εw) := by
        apply mul_le_mul_of_nonneg_left hW
        positivity
    _ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := hfin

/-- Region I, row 0. -/
theorem cfg_r0 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((87:ℝ)/(250)) ≤ lam₁) (h2 : lam₁ ≤ ((9:ℝ)/(25)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((327:ℝ)/(250))) (hL2 : Lam2Bound χ₁ ((451:ℝ)/(500))) (hL3 : Lam3Bound χ₁ ((1229:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((49:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((451:ℝ)/(500)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((49:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((327:ℝ)/(250)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((87:ℝ)/(250))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((87:ℝ)/(250))))))/(((87:ℝ)/(250))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((87:ℝ)/(250))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((1229:ℝ)/(1000)) ((49:ℝ)/(40)) ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((0:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((0:ℕ):ℝ) := by linarith
  have hrowA : Cf ((49:ℝ)/(40)) lam₁ - Aref ((327:ℝ)/(250)) lam₁ ≤ ((3646547:ℝ)/(25000000)) := by
    refine le_trans (rowA_0_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((3646547:ℝ)/(25000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((3646547:ℝ)/(25000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((3646547:ℝ)/(25000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((3646547:ℝ)/(25000000)) + 2 * ((165177:ℝ)/(12500000))
        + max 0 ((Nlist [218] 0 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((49:ℝ)/(40)) (min ((1229:ℝ)/(1000)) ((49:ℝ)/(40)))
        + ∑ j ∈ Finset.range 0, ((Nlist [218] j : ℝ) - (Nlist [218] (j+1) : ℝ))
            * Cf ((49:ℝ)/(40)) (((49:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r0 hεw hεw1
  have hETA : (Real.exp (-(ac * ((49:ℝ)/(40)))) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [218] 0 : ℝ) + 4 ≤ 1000 := etab_r0 hεw hεw1
  have hcred : Cf ((49:ℝ)/(40)) (min ((1229:ℝ)/(1000)) ((49:ℝ)/(40))) ≤ ((165177:ℝ)/(12500000)) := by
    rw [show min ((1229:ℝ)/(1000)) ((49:ℝ)/(40)) = ((49:ℝ)/(40)) from by norm_num]
    exact (cred_r0).1
  have hc0 : (0:ℝ) < ((327:ℝ)/(250)) := by norm_num
  exact sec15_step (N := fun j => Nlist [218] j) (c₀ := ((327:ℝ)/(250))) (l₂ := ((451:ℝ)/(500)))
    (l₃ := ((1229:ℝ)/(1000))) (CST1 := ((3646547:ℝ)/(25000000))) (CST2 := ((165177:ℝ)/(12500000)))
    (n₁ := 2) (s := 0) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r0 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r0).2.1 hTOT hETA

/-- Region I, row 1. -/
theorem cfg_r1 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((9:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((19:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((1249:ℝ)/(1000))) (hL2 : Lam2Bound χ₁ ((443:ℝ)/(500))) (hL3 : Lam3Bound χ₁ ((59:ℝ)/(50)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((6:ℝ)/(5)) := by norm_num
  have hl2 : (0:ℝ) < ((443:ℝ)/(500)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((6:ℝ)/(5)) := by linarith
  have hlam1c0 : lam₁ ≤ ((1249:ℝ)/(1000)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((9:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((9:ℝ)/(25))))))/(((9:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((9:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((59:ℝ)/(50)) ((6:ℝ)/(5)) ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((0:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((0:ℕ):ℝ) := by linarith
  have hrowA : Cf ((6:ℝ)/(5)) lam₁ - Aref ((1249:ℝ)/(1000)) lam₁ ≤ ((13564633:ℝ)/(100000000)) := by
    refine le_trans (rowA_1_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((13564633:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((13564633:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((13564633:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((13564633:ℝ)/(100000000)) + 2 * ((282441:ℝ)/(20000000))
        + max 0 ((Nlist [111] 0 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((6:ℝ)/(5)) (min ((59:ℝ)/(50)) ((6:ℝ)/(5)))
        + ∑ j ∈ Finset.range 0, ((Nlist [111] j : ℝ) - (Nlist [111] (j+1) : ℝ))
            * Cf ((6:ℝ)/(5)) (((6:ℝ)/(5)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r1 hεw hεw1
  have hETA : (Real.exp (-(ac * ((6:ℝ)/(5)))) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + (Nlist [111] 0 : ℝ) + 4 ≤ 1000 := etab_r1 hεw hεw1
  have hcred : Cf ((6:ℝ)/(5)) (min ((59:ℝ)/(50)) ((6:ℝ)/(5))) ≤ ((282441:ℝ)/(20000000)) := by
    rw [show min ((59:ℝ)/(50)) ((6:ℝ)/(5)) = ((59:ℝ)/(50)) from by norm_num]
    exact (cred_r1).1
  have hc0 : (0:ℝ) < ((1249:ℝ)/(1000)) := by norm_num
  exact sec15_step (N := fun j => Nlist [111] j) (c₀ := ((1249:ℝ)/(1000))) (l₂ := ((443:ℝ)/(500)))
    (l₃ := ((59:ℝ)/(50))) (CST1 := ((13564633:ℝ)/(100000000))) (CST2 := ((282441:ℝ)/(20000000)))
    (n₁ := 2) (s := 0) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r1 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r1).2.1 hTOT hETA

/-- Region I, row 2. -/
theorem cfg_r2 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((19:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((2:ℝ)/(5)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((239:ℝ)/(200))) (hL2 : Lam2Bound χ₁ ((87:ℝ)/(100))) (hL3 : Lam3Bound χ₁ ((567:ℝ)/(500)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((6:ℝ)/(5)) := by norm_num
  have hl2 : (0:ℝ) < ((87:ℝ)/(100)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((6:ℝ)/(5)) := by linarith
  have hlam1c0 : lam₁ ≤ ((239:ℝ)/(200)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((19:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((19:ℝ)/(50))))))/(((19:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((19:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((567:ℝ)/(500)) ((6:ℝ)/(5)) ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((2:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((2:ℕ):ℝ) := by linarith
  have hrowA : Cf ((6:ℝ)/(5)) lam₁ - Aref ((239:ℝ)/(200)) lam₁ ≤ ((3046547:ℝ)/(25000000)) := by
    refine le_trans (rowA_2_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((3046547:ℝ)/(25000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((3046547:ℝ)/(25000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((3046547:ℝ)/(25000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((3046547:ℝ)/(25000000)) + 2 * ((394349:ℝ)/(25000000))
        + max 0 ((Nlist [111, 73, 54] 2 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((6:ℝ)/(5)) (min ((567:ℝ)/(500)) ((6:ℝ)/(5)))
        + ∑ j ∈ Finset.range 2, ((Nlist [111, 73, 54] j : ℝ) - (Nlist [111, 73, 54] (j+1) : ℝ))
            * Cf ((6:ℝ)/(5)) (((6:ℝ)/(5)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r2 hεw hεw1
  have hETA : (Real.exp (-(ac * ((6:ℝ)/(5)))) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + (Nlist [111, 73, 54] 0 : ℝ) + 4 ≤ 1000 := etab_r2 hεw hεw1
  have hcred : Cf ((6:ℝ)/(5)) (min ((567:ℝ)/(500)) ((6:ℝ)/(5))) ≤ ((394349:ℝ)/(25000000)) := by
    rw [show min ((567:ℝ)/(500)) ((6:ℝ)/(5)) = ((567:ℝ)/(500)) from by norm_num]
    exact (cred_r2).1
  have hc0 : (0:ℝ) < ((239:ℝ)/(200)) := by norm_num
  exact sec15_step (N := fun j => Nlist [111, 73, 54] j) (c₀ := ((239:ℝ)/(200))) (l₂ := ((87:ℝ)/(100)))
    (l₃ := ((567:ℝ)/(500))) (CST1 := ((3046547:ℝ)/(25000000))) (CST2 := ((394349:ℝ)/(25000000)))
    (n₁ := 2) (s := 2) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r2 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r2).2.1 hTOT hETA

/-- Region I, row 3. -/
theorem cfg_r3 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((2:ℝ)/(5)) ≤ lam₁) (h2 : lam₁ ≤ ((21:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((143:ℝ)/(125))) (hL2 : Lam2Bound χ₁ ((171:ℝ)/(200))) (hL3 : Lam3Bound χ₁ ((1093:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((6:ℝ)/(5)) := by norm_num
  have hl2 : (0:ℝ) < ((171:ℝ)/(200)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((6:ℝ)/(5)) := by linarith
  have hlam1c0 : lam₁ ≤ ((143:ℝ)/(125)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((2:ℝ)/(5))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((2:ℝ)/(5))))))/(((2:ℝ)/(5))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((2:ℝ)/(5))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((1093:ℝ)/(1000)) ((6:ℝ)/(5)) ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((4:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((4:ℕ):ℝ) := by linarith
  have hrowA : Cf ((6:ℝ)/(5)) lam₁ - Aref ((143:ℝ)/(125)) lam₁ ≤ ((10969797:ℝ)/(100000000)) := by
    refine le_trans (rowA_3_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((10969797:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((10969797:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((10969797:ℝ)/(100000000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((10969797:ℝ)/(100000000)) + 2 * ((436587:ℝ)/(25000000))
        + max 0 ((Nlist [81, 58, 45, 36, 30] 4 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((6:ℝ)/(5)) (min ((1093:ℝ)/(1000)) ((6:ℝ)/(5)))
        + ∑ j ∈ Finset.range 4, ((Nlist [81, 58, 45, 36, 30] j : ℝ) - (Nlist [81, 58, 45, 36, 30] (j+1) : ℝ))
            * Cf ((6:ℝ)/(5)) (((6:ℝ)/(5)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r3 hεw hεw1
  have hETA : (Real.exp (-(ac * ((6:ℝ)/(5)))) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + (Nlist [81, 58, 45, 36, 30] 0 : ℝ) + 4 ≤ 1000 := etab_r3 hεw hεw1
  have hcred : Cf ((6:ℝ)/(5)) (min ((1093:ℝ)/(1000)) ((6:ℝ)/(5))) ≤ ((436587:ℝ)/(25000000)) := by
    rw [show min ((1093:ℝ)/(1000)) ((6:ℝ)/(5)) = ((1093:ℝ)/(1000)) from by norm_num]
    exact (cred_r3).1
  have hc0 : (0:ℝ) < ((143:ℝ)/(125)) := by norm_num
  exact sec15_step (N := fun j => Nlist [81, 58, 45, 36, 30] j) (c₀ := ((143:ℝ)/(125))) (l₂ := ((171:ℝ)/(200)))
    (l₃ := ((1093:ℝ)/(1000))) (CST1 := ((10969797:ℝ)/(100000000))) (CST2 := ((436587:ℝ)/(25000000)))
    (n₁ := 2) (s := 4) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r3 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r3).2.1 hTOT hETA

/-- Region I, row 4. -/
theorem cfg_r4 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((21:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((11:ℝ)/(25)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((549:ℝ)/(500))) (hL2 : Lam2Bound χ₁ ((841:ℝ)/(1000))) (hL3 : Lam3Bound χ₁ ((527:ℝ)/(500)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((6:ℝ)/(5)) := by norm_num
  have hl2 : (0:ℝ) < ((841:ℝ)/(1000)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((6:ℝ)/(5)) := by linarith
  have hlam1c0 : lam₁ ≤ ((549:ℝ)/(500)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((21:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((21:ℝ)/(50))))))/(((21:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((21:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((527:ℝ)/(500)) ((6:ℝ)/(5)) ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((5:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((6:ℝ)/(5)) - (25:ℝ)/1000 * ((5:ℕ):ℝ) := by linarith
  have hrowA : Cf ((6:ℝ)/(5)) lam₁ - Aref ((549:ℝ)/(500)) lam₁ ≤ ((618589:ℝ)/(6250000)) := by
    refine le_trans (rowA_4_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((618589:ℝ)/(6250000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((618589:ℝ)/(6250000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((618589:ℝ)/(6250000)) + (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((6:ℝ)/(5)) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((618589:ℝ)/(6250000)) + 2 * ((1917351:ℝ)/(100000000))
        + max 0 ((Nlist [81, 58, 45, 36, 30, 26] 5 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((6:ℝ)/(5)) (min ((527:ℝ)/(500)) ((6:ℝ)/(5)))
        + ∑ j ∈ Finset.range 5, ((Nlist [81, 58, 45, 36, 30, 26] j : ℝ) - (Nlist [81, 58, 45, 36, 30, 26] (j+1) : ℝ))
            * Cf ((6:ℝ)/(5)) (((6:ℝ)/(5)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r4 hεw hεw1
  have hETA : (Real.exp (-(ac * ((6:ℝ)/(5)))) / Wf ((6:ℝ)/(5))) * ((67:ℝ)/6 + εw) + (Nlist [81, 58, 45, 36, 30, 26] 0 : ℝ) + 4 ≤ 1000 := etab_r4 hεw hεw1
  have hcred : Cf ((6:ℝ)/(5)) (min ((527:ℝ)/(500)) ((6:ℝ)/(5))) ≤ ((1917351:ℝ)/(100000000)) := by
    rw [show min ((527:ℝ)/(500)) ((6:ℝ)/(5)) = ((527:ℝ)/(500)) from by norm_num]
    exact (cred_r4).1
  have hc0 : (0:ℝ) < ((549:ℝ)/(500)) := by norm_num
  exact sec15_step (N := fun j => Nlist [81, 58, 45, 36, 30, 26] j) (c₀ := ((549:ℝ)/(500))) (l₂ := ((841:ℝ)/(1000)))
    (l₃ := ((527:ℝ)/(500))) (CST1 := ((618589:ℝ)/(6250000))) (CST2 := ((1917351:ℝ)/(100000000)))
    (n₁ := 2) (s := 5) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r4 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r4).2.1 hTOT hETA

/-- Region I, row 5. -/
theorem cfg_r5 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((11:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((23:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((527:ℝ)/(500))) (hL2 : Lam2Bound χ₁ ((207:ℝ)/(250))) (hL3 : Lam3Bound χ₁ ((1017:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((49:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((207:ℝ)/(250)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((49:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((527:ℝ)/(500)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((11:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((11:ℝ)/(25))))))/(((11:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((11:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((1017:ℝ)/(1000)) ((49:ℝ)/(40)) ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((8:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((8:ℕ):ℝ) := by linarith
  have hrowA : Cf ((49:ℝ)/(40)) lam₁ - Aref ((527:ℝ)/(500)) lam₁ ≤ ((1137307:ℝ)/(12500000)) := by
    refine le_trans (rowA_5_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((1137307:ℝ)/(12500000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((1137307:ℝ)/(12500000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((1137307:ℝ)/(12500000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((1137307:ℝ)/(12500000)) + 2 * ((539411:ℝ)/(25000000))
        + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] 8 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((49:ℝ)/(40)) (min ((1017:ℝ)/(1000)) ((49:ℝ)/(40)))
        + ∑ j ∈ Finset.range 8, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] (j+1) : ℝ))
            * Cf ((49:ℝ)/(40)) (((49:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r5 hεw hεw1
  have hETA : (Real.exp (-(ac * ((49:ℝ)/(40)))) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] 0 : ℝ) + 4 ≤ 1000 := etab_r5 hεw hεw1
  have hcred : Cf ((49:ℝ)/(40)) (min ((1017:ℝ)/(1000)) ((49:ℝ)/(40))) ≤ ((539411:ℝ)/(25000000)) := by
    rw [show min ((1017:ℝ)/(1000)) ((49:ℝ)/(40)) = ((1017:ℝ)/(1000)) from by norm_num]
    exact (cred_r5).1
  have hc0 : (0:ℝ) < ((527:ℝ)/(500)) := by norm_num
  exact sec15_step (N := fun j => Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18] j) (c₀ := ((527:ℝ)/(500))) (l₂ := ((207:ℝ)/(250)))
    (l₃ := ((1017:ℝ)/(1000))) (CST1 := ((1137307:ℝ)/(12500000))) (CST2 := ((539411:ℝ)/(25000000)))
    (n₁ := 2) (s := 8) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r5 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r5).2.1 hTOT hETA

/-- Region I, row 6. -/
theorem cfg_r6 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((23:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((12:ℝ)/(25)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((507:ℝ)/(500))) (hL2 : Lam2Bound χ₁ ((163:ℝ)/(200))) (hL3 : Lam3Bound χ₁ ((983:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((49:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((163:ℝ)/(200)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((49:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((507:ℝ)/(500)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((23:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((23:ℝ)/(50))))))/(((23:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((23:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((983:ℝ)/(1000)) ((49:ℝ)/(40)) ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((9:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((9:ℕ):ℝ) := by linarith
  have hrowA : Cf ((49:ℝ)/(40)) lam₁ - Aref ((507:ℝ)/(500)) lam₁ ≤ ((8277873:ℝ)/(100000000)) := by
    refine le_trans (rowA_6_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((8277873:ℝ)/(100000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((8277873:ℝ)/(100000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((8277873:ℝ)/(100000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((8277873:ℝ)/(100000000)) + 2 * ((1171667:ℝ)/(50000000))
        + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] 9 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((49:ℝ)/(40)) (min ((983:ℝ)/(1000)) ((49:ℝ)/(40)))
        + ∑ j ∈ Finset.range 9, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] (j+1) : ℝ))
            * Cf ((49:ℝ)/(40)) (((49:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r6 hεw hεw1
  have hETA : (Real.exp (-(ac * ((49:ℝ)/(40)))) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] 0 : ℝ) + 4 ≤ 1000 := etab_r6 hεw hεw1
  have hcred : Cf ((49:ℝ)/(40)) (min ((983:ℝ)/(1000)) ((49:ℝ)/(40))) ≤ ((1171667:ℝ)/(50000000)) := by
    rw [show min ((983:ℝ)/(1000)) ((49:ℝ)/(40)) = ((983:ℝ)/(1000)) from by norm_num]
    exact (cred_r6).1
  have hc0 : (0:ℝ) < ((507:ℝ)/(500)) := by norm_num
  exact sec15_step (N := fun j => Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16] j) (c₀ := ((507:ℝ)/(500))) (l₂ := ((163:ℝ)/(200)))
    (l₃ := ((983:ℝ)/(1000))) (CST1 := ((8277873:ℝ)/(100000000))) (CST2 := ((1171667:ℝ)/(50000000)))
    (n₁ := 2) (s := 9) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r6 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r6).2.1 hTOT hETA

/-- Region I, row 7. -/
theorem cfg_r7 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((12:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((1:ℝ)/(2)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((122:ℝ)/(125))) (hL2 : Lam2Bound χ₁ ((401:ℝ)/(500))) (hL3 : Lam3Bound χ₁ ((951:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((49:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((401:ℝ)/(500)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((49:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((122:ℝ)/(125)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((12:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((12:ℝ)/(25))))))/(((12:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((12:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((951:ℝ)/(1000)) ((49:ℝ)/(40)) ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((10:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((49:ℝ)/(40)) - (25:ℝ)/1000 * ((10:ℕ):ℝ) := by linarith
  have hrowA : Cf ((49:ℝ)/(40)) lam₁ - Aref ((122:ℝ)/(125)) lam₁ ≤ ((3785989:ℝ)/(50000000)) := by
    refine le_trans (rowA_7_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((3785989:ℝ)/(50000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((3785989:ℝ)/(50000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((3785989:ℝ)/(50000000)) + (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((49:ℝ)/(40)) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((3785989:ℝ)/(50000000)) + 2 * ((2542779:ℝ)/(100000000))
        + max 0 ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 10 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((49:ℝ)/(40)) (min ((951:ℝ)/(1000)) ((49:ℝ)/(40)))
        + ∑ j ∈ Finset.range 10, ((Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j : ℝ) - (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] (j+1) : ℝ))
            * Cf ((49:ℝ)/(40)) (((49:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r7 hεw hεw1
  have hETA : (Real.exp (-(ac * ((49:ℝ)/(40)))) / Wf ((49:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] 0 : ℝ) + 4 ≤ 1000 := etab_r7 hεw hεw1
  have hcred : Cf ((49:ℝ)/(40)) (min ((951:ℝ)/(1000)) ((49:ℝ)/(40))) ≤ ((2542779:ℝ)/(100000000)) := by
    rw [show min ((951:ℝ)/(1000)) ((49:ℝ)/(40)) = ((951:ℝ)/(1000)) from by norm_num]
    exact (cred_r7).1
  have hc0 : (0:ℝ) < ((122:ℝ)/(125)) := by norm_num
  exact sec15_step (N := fun j => Nlist [97, 67, 51, 40, 33, 28, 24, 21, 18, 16, 15] j) (c₀ := ((122:ℝ)/(125))) (l₂ := ((401:ℝ)/(500)))
    (l₃ := ((951:ℝ)/(1000))) (CST1 := ((3785989:ℝ)/(50000000))) (CST2 := ((2542779:ℝ)/(100000000)))
    (n₁ := 2) (s := 10) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r7 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r7).2.1 hTOT hETA

/-- Region I, row 8. -/
theorem cfg_r8 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((1:ℝ)/(2)) ≤ lam₁) (h2 : lam₁ ≤ ((13:ℝ)/(25)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((47:ℝ)/(50))) (hL2 : Lam2Bound χ₁ ((79:ℝ)/(100))) (hL3 : Lam3Bound χ₁ ((921:ℝ)/(1000)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hl2 : (0:ℝ) < ((79:ℝ)/(100)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((5:ℝ)/(4)) := by linarith
  have hlam1c0 : lam₁ ≤ ((47:ℝ)/(50)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((1:ℝ)/(2))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((1:ℝ)/(2))))))/(((1:ℝ)/(2))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((1:ℝ)/(2))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((921:ℝ)/(1000)) ((5:ℝ)/(4)) ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((13:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((13:ℕ):ℝ) := by linarith
  have hrowA : Cf ((5:ℝ)/(4)) lam₁ - Aref ((47:ℝ)/(50)) lam₁ ≤ ((7084397:ℝ)/(100000000)) := by
    refine le_trans (rowA_8_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((7084397:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((7084397:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((7084397:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((7084397:ℝ)/(100000000)) + 2 * ((702093:ℝ)/(25000000))
        + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] 13 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((5:ℝ)/(4)) (min ((921:ℝ)/(1000)) ((5:ℝ)/(4)))
        + ∑ j ∈ Finset.range 13, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] (j+1) : ℝ))
            * Cf ((5:ℝ)/(4)) (((5:ℝ)/(4)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r8 hεw hεw1
  have hETA : (Real.exp (-(ac * ((5:ℝ)/(4)))) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] 0 : ℝ) + 4 ≤ 1000 := etab_r8 hεw hεw1
  have hcred : Cf ((5:ℝ)/(4)) (min ((921:ℝ)/(1000)) ((5:ℝ)/(4))) ≤ ((702093:ℝ)/(25000000)) := by
    rw [show min ((921:ℝ)/(1000)) ((5:ℝ)/(4)) = ((921:ℝ)/(1000)) from by norm_num]
    exact (cred_r8).1
  have hc0 : (0:ℝ) < ((47:ℝ)/(50)) := by norm_num
  exact sec15_step (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11] j) (c₀ := ((47:ℝ)/(50))) (l₂ := ((79:ℝ)/(100)))
    (l₃ := ((921:ℝ)/(1000))) (CST1 := ((7084397:ℝ)/(100000000))) (CST2 := ((702093:ℝ)/(25000000)))
    (n₁ := 2) (s := 13) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r8 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r8).2.1 hTOT hETA

/-- Region I, row 9. -/
theorem cfg_r9 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((13:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((27:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((453:ℝ)/(500))) (hL2 : Lam2Bound χ₁ ((779:ℝ)/(1000))) (hL3 : Lam3Bound χ₁ ((223:ℝ)/(250)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hl2 : (0:ℝ) < ((779:ℝ)/(1000)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((5:ℝ)/(4)) := by linarith
  have hlam1c0 : lam₁ ≤ ((453:ℝ)/(500)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((13:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((13:ℝ)/(25))))))/(((13:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((13:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((223:ℝ)/(250)) ((5:ℝ)/(4)) ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((14:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((14:ℕ):ℝ) := by linarith
  have hrowA : Cf ((5:ℝ)/(4)) lam₁ - Aref ((453:ℝ)/(500)) lam₁ ≤ ((6576779:ℝ)/(100000000)) := by
    refine le_trans (rowA_9_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((6576779:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((6576779:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((6576779:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((6576779:ℝ)/(100000000)) + 2 * ((750559:ℝ)/(25000000))
        + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] 14 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((5:ℝ)/(4)) (min ((223:ℝ)/(250)) ((5:ℝ)/(4)))
        + ∑ j ∈ Finset.range 14, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] (j+1) : ℝ))
            * Cf ((5:ℝ)/(4)) (((5:ℝ)/(4)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r9 hεw hεw1
  have hETA : (Real.exp (-(ac * ((5:ℝ)/(4)))) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] 0 : ℝ) + 4 ≤ 1000 := etab_r9 hεw hεw1
  have hcred : Cf ((5:ℝ)/(4)) (min ((223:ℝ)/(250)) ((5:ℝ)/(4))) ≤ ((750559:ℝ)/(25000000)) := by
    rw [show min ((223:ℝ)/(250)) ((5:ℝ)/(4)) = ((223:ℝ)/(250)) from by norm_num]
    exact (cred_r9).1
  have hc0 : (0:ℝ) < ((453:ℝ)/(500)) := by norm_num
  exact sec15_step (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10] j) (c₀ := ((453:ℝ)/(500))) (l₂ := ((779:ℝ)/(1000)))
    (l₃ := ((223:ℝ)/(250))) (CST1 := ((6576779:ℝ)/(100000000))) (CST2 := ((750559:ℝ)/(25000000)))
    (n₁ := 2) (s := 14) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r9 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r9).2.1 hTOT hETA

/-- Region I, row 10. -/
theorem cfg_r10 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((27:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((14:ℝ)/(25)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((437:ℝ)/(500))) (hL2 : Lam2Bound χ₁ ((96:ℝ)/(125))) (hL3 : Lam3Bound χ₁ ((173:ℝ)/(200)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hl2 : (0:ℝ) < ((96:ℝ)/(125)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((5:ℝ)/(4)) := by linarith
  have hlam1c0 : lam₁ ≤ ((437:ℝ)/(500)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((27:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((27:ℝ)/(50))))))/(((27:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((27:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((173:ℝ)/(200)) ((5:ℝ)/(4)) ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by linarith
  have hrowA : Cf ((5:ℝ)/(4)) lam₁ - Aref ((437:ℝ)/(500)) lam₁ ≤ ((615773:ℝ)/(10000000)) := by
    refine le_trans (rowA_10_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((615773:ℝ)/(10000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((615773:ℝ)/(10000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((615773:ℝ)/(10000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((615773:ℝ)/(10000000)) + 2 * ((128321:ℝ)/(4000000))
        + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((5:ℝ)/(4)) (min ((173:ℝ)/(200)) ((5:ℝ)/(4)))
        + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((5:ℝ)/(4)) (((5:ℝ)/(4)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r10 hεw hεw1
  have hETA : (Real.exp (-(ac * ((5:ℝ)/(4)))) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_r10 hεw hεw1
  have hcred : Cf ((5:ℝ)/(4)) (min ((173:ℝ)/(200)) ((5:ℝ)/(4))) ≤ ((128321:ℝ)/(4000000)) := by
    rw [show min ((173:ℝ)/(200)) ((5:ℝ)/(4)) = ((173:ℝ)/(200)) from by norm_num]
    exact (cred_r10).1
  have hc0 : (0:ℝ) < ((437:ℝ)/(500)) := by norm_num
  exact sec15_step (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j) (c₀ := ((437:ℝ)/(500))) (l₂ := ((96:ℝ)/(125)))
    (l₃ := ((173:ℝ)/(200))) (CST1 := ((615773:ℝ)/(10000000))) (CST2 := ((128321:ℝ)/(4000000)))
    (n₁ := 2) (s := 15) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r10 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r10).2.1 hTOT hETA

/-- Region I, row 11. -/
theorem cfg_r11 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((14:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((29:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((211:ℝ)/(250))) (hL2 : Lam2Bound χ₁ ((379:ℝ)/(500))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hl2 : (0:ℝ) < ((379:ℝ)/(500)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((5:ℝ)/(4)) := by linarith
  have hlam1c0 : lam₁ ≤ ((211:ℝ)/(250)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((14:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((14:ℝ)/(25))))))/(((14:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((14:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((5:ℝ)/(4)) ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by linarith
  have hrowA : Cf ((5:ℝ)/(4)) lam₁ - Aref ((211:ℝ)/(250)) lam₁ ≤ ((5818981:ℝ)/(100000000)) := by
    refine le_trans (rowA_11_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((5818981:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((5818981:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((5818981:ℝ)/(100000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((5818981:ℝ)/(100000000)) + 2 * ((106439:ℝ)/(3125000))
        + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((5:ℝ)/(4)) (min ((107:ℝ)/(125)) ((5:ℝ)/(4)))
        + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((5:ℝ)/(4)) (((5:ℝ)/(4)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r11 hεw hεw1
  have hETA : (Real.exp (-(ac * ((5:ℝ)/(4)))) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_r11 hεw hεw1
  have hcred : Cf ((5:ℝ)/(4)) (min ((107:ℝ)/(125)) ((5:ℝ)/(4))) ≤ ((106439:ℝ)/(3125000)) := by
    rw [show min ((107:ℝ)/(125)) ((5:ℝ)/(4)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_r11).1
  have hc0 : (0:ℝ) < ((211:ℝ)/(250)) := by norm_num
  exact sec15_step (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j) (c₀ := ((211:ℝ)/(250))) (l₂ := ((379:ℝ)/(500)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((5818981:ℝ)/(100000000))) (CST2 := ((106439:ℝ)/(3125000)))
    (n₁ := 2) (s := 15) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r11 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r11).2.1 hTOT hETA

/-- Region I, row 12. -/
theorem cfg_r12 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((29:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((3:ℝ)/(5)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((163:ℝ)/(200))) (hL2 : Lam2Bound χ₁ ((187:ℝ)/(250))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((187:ℝ)/(250)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((163:ℝ)/(200)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((29:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((29:ℝ)/(50))))))/(((29:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((29:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by linarith
  have hrowA : Cf ((51:ℝ)/(40)) lam₁ - Aref ((163:ℝ)/(200)) lam₁ ≤ ((5651003:ℝ)/(100000000)) := by
    refine le_trans (rowA_12_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((5651003:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((5651003:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((5651003:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((5651003:ℝ)/(100000000)) + 2 * ((3683353:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r12 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_r12 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40))) ≤ ((3683353:ℝ)/(100000000)) := by
    rw [show min ((107:ℝ)/(125)) ((51:ℝ)/(40)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_r12).1
  have hc0 : (0:ℝ) < ((163:ℝ)/(200)) := by norm_num
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j) (c₀ := ((163:ℝ)/(200))) (l₂ := ((187:ℝ)/(250)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((5651003:ℝ)/(100000000))) (CST2 := ((3683353:ℝ)/(100000000)))
    (n₁ := 2) (s := 16) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r12 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r12).2.1 hTOT hETA

/-- Region I, row 11 (rc). -/
theorem cfg_r11rc {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((14:ℝ)/(25)) ≤ lam₁) (h2 : lam₁ ≤ ((29:ℝ)/(50)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((211:ℝ)/(250))) (hL2 : Lam2Bound χ₁ ((379:ℝ)/(500))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hsq : χ₁ ^ 2 = 1)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((5:ℝ)/(4)) := by norm_num
  have hl2 : (0:ℝ) < ((379:ℝ)/(500)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((5:ℝ)/(4)) := by linarith
  have hlam1c0 : lam₁ ≤ ((211:ℝ)/(250)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((14:ℝ)/(25))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((14:ℝ)/(25))))))/(((14:ℝ)/(25))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((14:ℝ)/(25))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((5:ℝ)/(4)) ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((5:ℝ)/(4)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by linarith
  have hrowA : Cf ((5:ℝ)/(4)) lam₁ - Aref ((211:ℝ)/(250)) lam₁ ≤ ((2478327:ℝ)/(25000000)) := by
    refine le_trans (rowA_11_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hrowA2 : Cf ((5:ℝ)/(4)) lam₁ - Aref2 ((211:ℝ)/(250)) lam₁ ≤ ((2478327:ℝ)/(25000000)) := by
    refine le_trans (rowA2_r11rc h1 h2 hbn hf2 hbf2) ?_
    norm_num
  have hcard := card_S1_le_one (q := q) (χ₁ := χ₁) (R := R) (inv_eq_self_of_sq_one hsq)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((2478327:ℝ)/(25000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_rc hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hsq
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA hrowA2
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((2478327:ℝ)/(25000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_rc hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hsq ?_ hrowA hrowA2
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((2478327:ℝ)/(25000000)) + (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((5:ℝ)/(4)) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + ((1:ℕ):ℝ) * ((2478327:ℝ)/(25000000)) + 2 * ((106439:ℝ)/(3125000))
        + max 0 ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 15 : ℝ) - ((1:ℕ):ℝ) - 2) * Cf ((5:ℝ)/(4)) (min ((107:ℝ)/(125)) ((5:ℝ)/(4)))
        + ∑ j ∈ Finset.range 15, ((Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j : ℝ) - (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((5:ℝ)/(4)) (((5:ℝ)/(4)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r11rc hεw hεw1
  have hETA : (Real.exp (-(ac * ((5:ℝ)/(4)))) / Wf ((5:ℝ)/(4))) * ((67:ℝ)/6 + εw) + (Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_r11rc hεw hεw1
  have hcred : Cf ((5:ℝ)/(4)) (min ((107:ℝ)/(125)) ((5:ℝ)/(4))) ≤ ((106439:ℝ)/(3125000)) := by
    rw [show min ((107:ℝ)/(125)) ((5:ℝ)/(4)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_r11rc).1
  have hc0 : (0:ℝ) < ((211:ℝ)/(250)) := by norm_num
  exact sec15_step (N := fun j => Nlist [104, 71, 54, 42, 35, 29, 25, 22, 19, 17, 15, 14, 12, 11, 10, 9] j) (c₀ := ((211:ℝ)/(250))) (l₂ := ((379:ℝ)/(500)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((2478327:ℝ)/(25000000))) (CST2 := ((106439:ℝ)/(3125000)))
    (n₁ := 1) (s := 15) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r11rc hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r11rc).2.1 hTOT hETA

/-- Region I, row 12 (rc). -/
theorem cfg_r12rc {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((29:ℝ)/(50)) ≤ lam₁) (h2 : lam₁ ≤ ((3:ℝ)/(5)))
    (hL0 : Lam0Bound χ₁ ρ₁ ((163:ℝ)/(200))) (hL2 : Lam2Bound χ₁ ((187:ℝ)/(250))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hsq : χ₁ ^ 2 = 1)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((187:ℝ)/(250)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((163:ℝ)/(200)) := by linarith

  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) (((29:ℝ)/(50))) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*(((29:ℝ)/(50))))))/(((29:ℝ)/(50))))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := ((29:ℝ)/(50))) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by linarith
  have hrowA : Cf ((51:ℝ)/(40)) lam₁ - Aref ((163:ℝ)/(200)) lam₁ ≤ ((4505027:ℝ)/(50000000)) := by
    refine le_trans (rowA_12_cx h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hrowA2 : Cf ((51:ℝ)/(40)) lam₁ - Aref2 ((163:ℝ)/(200)) lam₁ ≤ ((4505027:ℝ)/(50000000)) := by
    refine le_trans (rowA2_r12rc h1 h2 hbn hf2 hbf2) ?_
    norm_num
  have hcard := card_S1_le_one (q := q) (χ₁ := χ₁) (R := R) (inv_eq_self_of_sq_one hsq)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((4505027:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_rc hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hsq
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA hrowA2
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((4505027:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_rc hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hsq ?_ hrowA hrowA2
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((4505027:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((1:ℕ):ℝ) * ((4505027:ℝ)/(50000000)) + 2 * ((3683353:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((1:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_r12rc hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_r12rc hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40))) ≤ ((3683353:ℝ)/(100000000)) := by
    rw [show min ((107:ℝ)/(125)) ((51:ℝ)/(40)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_r12rc).1
  have hc0 : (0:ℝ) < ((163:ℝ)/(200)) := by norm_num
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j) (c₀ := ((163:ℝ)/(200))) (l₂ := ((187:ℝ)/(250)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((4505027:ℝ)/(50000000))) (CST2 := ((3683353:ℝ)/(100000000)))
    (n₁ := 1) (s := 16) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_r12rc hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_r12rc).2.1 hTOT hETA

/-- Region II (`λ₁ ∈ [3/5, 139/200]`), universal row. -/
theorem cfg_u2 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : (3:ℝ)/5 ≤ lam₁) (h2 : lam₁ ≤ (139:ℝ)/200)
    (hL0 : Lam0Bound χ₁ ρ₁ ((139:ℝ)/(200))) (hL2 : Lam2Bound χ₁ ((701:ℝ)/(1000))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((701:ℝ)/(1000)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((139:ℝ)/(200)) := by linarith
  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) ((3:ℝ)/5) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/5))))/((3:ℝ)/5))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := (3:ℝ)/5) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by linarith
  have hrowA : Cf ((51:ℝ)/(40)) lam₁ - Aref ((139:ℝ)/(200)) lam₁ ≤ ((6788827:ℝ)/(100000000)) :=
    rowA_13_cx h1 h2 hbn hf2 hbf1
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((6788827:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_alpha1 hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hnotrc
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((6788827:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_alpha1 hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hnotrc ?_ hrowA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((6788827:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((6788827:ℝ)/(100000000)) + 2 * ((100147:ℝ)/(2000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u2 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_u2 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40))) ≤ ((100147:ℝ)/(2000000)) := by
    rw [show min ((107:ℝ)/(125)) ((51:ℝ)/(40)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_u2).1
  have hc0 : (0:ℝ) < ((139:ℝ)/(200)) := by norm_num
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j) (c₀ := ((139:ℝ)/(200))) (l₂ := ((701:ℝ)/(1000)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((6788827:ℝ)/(100000000))) (CST2 := ((100147:ℝ)/(2000000)))
    (n₁ := 2) (s := 16) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u2 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u2).2.1 hTOT hETA

/-- Region II (`λ₁ ∈ [3/5, 139/200]`), universal row (rc). -/
theorem cfg_u2rc {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : (3:ℝ)/5 ≤ lam₁) (h2 : lam₁ ≤ (139:ℝ)/200)
    (hL0 : Lam0Bound χ₁ ρ₁ ((139:ℝ)/(200))) (hL2 : Lam2Bound χ₁ ((701:ℝ)/(1000))) (hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hsq : χ₁ ^ 2 = 1)
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((701:ℝ)/(1000)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ ((139:ℝ)/(200)) := by linarith
  have hbn : Bfun ((3:ℝ)/10) lam₁ ≤ Bfun ((3:ℝ)/10) ((3:ℝ)/5) :=
    Bfun_antitone (K := (3:ℝ)/10) (by norm_num) (by linarith) h1
  have hf2 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ ((1-Real.exp (-((3:ℝ)/10*((3:ℝ)/5))))/((3:ℝ)/5))^2/((9:ℝ)/100) :=
    F2K2_antitone (p := (3:ℝ)/5) (q := lam₁) (by linarith) h1
  have hbf1 : ((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    simpa using cF2K2_le_Bfun (c := 1) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
  have hbf2 : 2*((1-Real.exp (-((3:ℝ)/10*lam₁)))/lam₁)^2/((9:ℝ)/100) ≤ Bfun ((3:ℝ)/10) lam₁ := by
    have h := cF2K2_le_Bfun (c := 2) (p := lam₁) (by linarith) (by norm_num) (by norm_num)
    linarith [h]
  have hle3 : min ((107:ℝ)/(125)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by linarith
  have hrowA : Cf ((51:ℝ)/(40)) lam₁ - Aref ((139:ℝ)/(200)) lam₁ ≤ ((4218353:ℝ)/(50000000)) := by
    refine le_trans (rowA_13_rc h1 h2 hbn hf2 hbf1) ?_
    norm_num
  have hrowA2 : Cf ((51:ℝ)/(40)) lam₁ - Aref2 ((139:ℝ)/(200)) lam₁ ≤ ((4218353:ℝ)/(50000000)) := by
    refine le_trans (rowA2_u2rc h1 h2 hbn hf2 hbf2) ?_
    norm_num
  have hcard := card_S1_le_one (q := q) (χ₁ := χ₁) (R := R) (inv_eq_self_of_sq_one hsq)
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((4218353:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    exact S1_rc hq hRlog hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hmin.1 hlam1 hsq
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowA hrowA2
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((4218353:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_inv_bound_rc hq hRlog hmin hlam1 hΛ hη (by linarith) hlam1Λ hlam1c0 hL0 hsq ?_ hrowA hrowA2
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    exact hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((4218353:ℝ)/(50000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((1:ℕ):ℝ) * ((4218353:ℝ)/(50000000)) + 2 * ((100147:ℝ)/(2000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((1:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u2rc hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_u2rc hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40))) ≤ ((100147:ℝ)/(2000000)) := by
    rw [show min ((107:ℝ)/(125)) ((51:ℝ)/(40)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_u2rc).1
  have hc0 : (0:ℝ) < ((139:ℝ)/(200)) := by norm_num
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j) (c₀ := ((139:ℝ)/(200))) (l₂ := ((701:ℝ)/(1000)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((4218353:ℝ)/(50000000))) (CST2 := ((100147:ℝ)/(2000000)))
    (n₁ := 1) (s := 16) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    hlam1c0 hL0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u2rc hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u2rc).2.1 hTOT hETA

/-- III: plain `χ₁` bound. -/
theorem cfg_u3 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : (139:ℝ)/200 ≤ lam₁) (h2 : lam₁ ≤ (7:ℝ)/8)
        (hZ3L2 : Lam2Bound χ₁ ((701:ℝ)/(1000))) (hZ3L3 : Lam3Bound χ₁ ((107:ℝ)/(125)))
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((701:ℝ)/(1000)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((701:ℝ)/(1000)) := hZ3L2
  have hL3 : Lam3Bound χ₁ ((107:ℝ)/(125)) := hZ3L3
  have hle3 : min ((107:ℝ)/(125)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((16:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((100147:ℝ)/(2000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u3).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((100147:ℝ)/(2000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((100147:ℝ)/(2000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((100147:ℝ)/(2000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((100147:ℝ)/(2000000)) + 2 * ((100147:ℝ)/(2000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 16 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 16, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u3 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] 0 : ℝ) + 4 ≤ 1000 := etab_u3 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((107:ℝ)/(125)) ((51:ℝ)/(40))) ≤ ((100147:ℝ)/(2000000)) := by
    rw [show min ((107:ℝ)/(125)) ((51:ℝ)/(40)) = ((107:ℝ)/(125)) from by norm_num]
    exact (cred_u3).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10, 9] j) (c₀ := lam₁) (l₂ := ((701:ℝ)/(1000)))
    (l₃ := ((107:ℝ)/(125))) (CST1 := ((100147:ℝ)/(2000000))) (CST2 := ((100147:ℝ)/(2000000)))
    (n₁ := 2) (s := 16) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u3 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u3).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_15 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((7:ℝ)/(8)) ≤ lam₁) (h2 : lam₁ ≤ ((9:ℝ)/(10)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((7:ℝ)/(8)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((7:ℝ)/(8)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((7:ℝ)/(8)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((7:ℝ)/(8)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((15:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((1699609:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_15).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((1699609:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((1699609:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((1699609:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((1699609:ℝ)/(100000000)) + 2 * ((1699609:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] 15 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((7:ℝ)/(8)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 15, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_15 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] 0 : ℝ) + 4 ≤ 1000 := etab_u4_15 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((7:ℝ)/(8)) ((51:ℝ)/(40))) ≤ ((1699609:ℝ)/(100000000)) := by
    rw [show min ((7:ℝ)/(8)) ((51:ℝ)/(40)) = ((7:ℝ)/(8)) from by norm_num]
    exact (cred_u4_15).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11, 10] j) (c₀ := lam₁) (l₂ := ((7:ℝ)/(8)))
    (l₃ := ((7:ℝ)/(8))) (CST1 := ((1699609:ℝ)/(100000000))) (CST2 := ((1699609:ℝ)/(100000000)))
    (n₁ := 2) (s := 15) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_15 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_15).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_14 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((9:ℝ)/(10)) ≤ lam₁) (h2 : lam₁ ≤ ((37:ℝ)/(40)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((9:ℝ)/(10)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((9:ℝ)/(10)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((9:ℝ)/(10)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((9:ℝ)/(10)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((14:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((14:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((1446777:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_14).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((1446777:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((1446777:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((1446777:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((1446777:ℝ)/(100000000)) + 2 * ((1446777:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] 14 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((9:ℝ)/(10)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 14, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_14 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] 0 : ℝ) + 4 ≤ 1000 := etab_u4_14 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((9:ℝ)/(10)) ((51:ℝ)/(40))) ≤ ((1446777:ℝ)/(100000000)) := by
    rw [show min ((9:ℝ)/(10)) ((51:ℝ)/(40)) = ((9:ℝ)/(10)) from by norm_num]
    exact (cred_u4_14).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12, 11] j) (c₀ := lam₁) (l₂ := ((9:ℝ)/(10)))
    (l₃ := ((9:ℝ)/(10))) (CST1 := ((1446777:ℝ)/(100000000))) (CST2 := ((1446777:ℝ)/(100000000)))
    (n₁ := 2) (s := 14) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_14 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_14).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_13 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((37:ℝ)/(40)) ≤ lam₁) (h2 : lam₁ ≤ ((19:ℝ)/(20)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((37:ℝ)/(40)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((37:ℝ)/(40)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((37:ℝ)/(40)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((37:ℝ)/(40)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((13:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((13:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((1226677:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_13).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((1226677:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((1226677:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((1226677:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((1226677:ℝ)/(100000000)) + 2 * ((1226677:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] 13 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((37:ℝ)/(40)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 13, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_13 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] 0 : ℝ) + 4 ≤ 1000 := etab_u4_13 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((37:ℝ)/(40)) ((51:ℝ)/(40))) ≤ ((1226677:ℝ)/(100000000)) := by
    rw [show min ((37:ℝ)/(40)) ((51:ℝ)/(40)) = ((37:ℝ)/(40)) from by norm_num]
    exact (cred_u4_13).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13, 12] j) (c₀ := lam₁) (l₂ := ((37:ℝ)/(40)))
    (l₃ := ((37:ℝ)/(40))) (CST1 := ((1226677:ℝ)/(100000000))) (CST2 := ((1226677:ℝ)/(100000000)))
    (n₁ := 2) (s := 13) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_13 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_13).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_12 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((19:ℝ)/(20)) ≤ lam₁) (h2 : lam₁ ≤ ((39:ℝ)/(40)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((19:ℝ)/(20)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((19:ℝ)/(20)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((19:ℝ)/(20)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((19:ℝ)/(20)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((12:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((12:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((51763:ℝ)/(5000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_12).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((51763:ℝ)/(5000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((51763:ℝ)/(5000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((51763:ℝ)/(5000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((51763:ℝ)/(5000000)) + 2 * ((51763:ℝ)/(5000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] 12 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((19:ℝ)/(20)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 12, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_12 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] 0 : ℝ) + 4 ≤ 1000 := etab_u4_12 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((19:ℝ)/(20)) ((51:ℝ)/(40))) ≤ ((51763:ℝ)/(5000000)) := by
    rw [show min ((19:ℝ)/(20)) ((51:ℝ)/(40)) = ((19:ℝ)/(20)) from by norm_num]
    exact (cred_u4_12).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14, 13] j) (c₀ := lam₁) (l₂ := ((19:ℝ)/(20)))
    (l₃ := ((19:ℝ)/(20))) (CST1 := ((51763:ℝ)/(5000000))) (CST2 := ((51763:ℝ)/(5000000)))
    (n₁ := 2) (s := 12) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_12 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_12).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_11 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((39:ℝ)/(40)) ≤ lam₁) (h2 : lam₁ ≤ ((1:ℝ)/(1)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((39:ℝ)/(40)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((39:ℝ)/(40)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((39:ℝ)/(40)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((39:ℝ)/(40)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((11:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((11:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((108621:ℝ)/(12500000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_11).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((108621:ℝ)/(12500000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((108621:ℝ)/(12500000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((108621:ℝ)/(12500000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((108621:ℝ)/(12500000)) + 2 * ((108621:ℝ)/(12500000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] 11 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((39:ℝ)/(40)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 11, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_11 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] 0 : ℝ) + 4 ≤ 1000 := etab_u4_11 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((39:ℝ)/(40)) ((51:ℝ)/(40))) ≤ ((108621:ℝ)/(12500000)) := by
    rw [show min ((39:ℝ)/(40)) ((51:ℝ)/(40)) = ((39:ℝ)/(40)) from by norm_num]
    exact (cred_u4_11).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15, 14] j) (c₀ := lam₁) (l₂ := ((39:ℝ)/(40)))
    (l₃ := ((39:ℝ)/(40))) (CST1 := ((108621:ℝ)/(12500000))) (CST2 := ((108621:ℝ)/(12500000)))
    (n₁ := 2) (s := 11) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_11 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_11).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_10 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((1:ℝ)/(1)) ≤ lam₁) (h2 : lam₁ ≤ ((41:ℝ)/(40)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((1:ℝ)/(1)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((1:ℝ)/(1)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((1:ℝ)/(1)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((1:ℝ)/(1)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((10:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((10:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((724679:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_10).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((724679:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((724679:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((724679:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((724679:ℝ)/(100000000)) + 2 * ((724679:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] 10 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((1:ℝ)/(1)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 10, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_10 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] 0 : ℝ) + 4 ≤ 1000 := etab_u4_10 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((1:ℝ)/(1)) ((51:ℝ)/(40))) ≤ ((724679:ℝ)/(100000000)) := by
    rw [show min ((1:ℝ)/(1)) ((51:ℝ)/(40)) = ((1:ℝ)/(1)) from by norm_num]
    exact (cred_u4_10).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17, 15] j) (c₀ := lam₁) (l₂ := ((1:ℝ)/(1)))
    (l₃ := ((1:ℝ)/(1))) (CST1 := ((724679:ℝ)/(100000000))) (CST2 := ((724679:ℝ)/(100000000)))
    (n₁ := 2) (s := 10) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_10 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_10).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_9 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((41:ℝ)/(40)) ≤ lam₁) (h2 : lam₁ ≤ ((21:ℝ)/(20)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((41:ℝ)/(40)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((41:ℝ)/(40)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((41:ℝ)/(40)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((41:ℝ)/(40)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((9:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((9:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((599649:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_9).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((599649:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((599649:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((599649:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((599649:ℝ)/(100000000)) + 2 * ((599649:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] 9 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((41:ℝ)/(40)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 9, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_9 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] 0 : ℝ) + 4 ≤ 1000 := etab_u4_9 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((41:ℝ)/(40)) ((51:ℝ)/(40))) ≤ ((599649:ℝ)/(100000000)) := by
    rw [show min ((41:ℝ)/(40)) ((51:ℝ)/(40)) = ((41:ℝ)/(40)) from by norm_num]
    exact (cred_u4_9).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19, 17] j) (c₀ := lam₁) (l₂ := ((41:ℝ)/(40)))
    (l₃ := ((41:ℝ)/(40))) (CST1 := ((599649:ℝ)/(100000000))) (CST2 := ((599649:ℝ)/(100000000)))
    (n₁ := 2) (s := 9) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_9 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_9).2.1 hTOT hETA

/-- IV: plain `χ₁` bound. -/
theorem cfg_u4_8 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : IsMin1 χ₁ ρ₁) (hlam1 : lamOf q ρ₁ = lam₁)
    (h1 : ((21:ℝ)/(20)) ≤ lam₁) (h2 : lam₁ ≤ ((43:ℝ)/(40)))
        (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    (hD1 : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η))
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2) :
    ∑ χ ∈ Aset q R, WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  have h348 : (348:ℝ)/1000 ≤ lam₁ := by linarith
  have hΛ : (0:ℝ) < ((51:ℝ)/(40)) := by norm_num
  have hl2 : (0:ℝ) < ((21:ℝ)/(20)) := by norm_num
  have hlam1Λ : lam₁ ≤ ((51:ℝ)/(40)) := by linarith
  have hlam1c0 : lam₁ ≤ lam₁ := le_rfl
  have hLam0 : Lam0Bound χ₁ ρ₁ lam₁ := lam0Bound_self hmin hlam1
  have hL2 : Lam2Bound χ₁ ((21:ℝ)/(20)) := fun _χ _ρ _hZ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)
  have hL3 : Lam3Bound χ₁ ((21:ℝ)/(20)) := ⟨χ₁, fun _χ _ρ _hZ _ _ _ _ =>
    le_trans (hlam1.symm ▸ h1) (hmin.2 _χ _ρ _hZ)⟩
  have hle3 : min ((21:ℝ)/(20)) ((51:ℝ)/(40)) ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((8:ℕ):ℝ) := by norm_num
  have hlam1small : lam₁ ≤ ((51:ℝ)/(40)) - (25:ℝ)/1000 * ((8:ℕ):ℝ) := by linarith
  have hcard := card_S1_le_two (q := q) (χ₁ := χ₁) (R := R)
  have hrowB : Cf ((51:ℝ)/(40)) lam₁ ≤ ((491473:ℝ)/(100000000)) :=
    le_trans (Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ (by linarith) h1) (cred_u4_8).2.2
  have hpt1 (hA : χ₁ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁ ≤ ((9:ℝ)/100) * (((491473:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_eq_of_isMin1 hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁ hmin.1.1 lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁ ρ' (box_api7_p1 hq hRlog hmin.1.1 hz' hb')
  have hpt2 (hA : χ₁⁻¹ ∈ Aset q R) : WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (((491473:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    have hlam1R : lam₁ ≤ R := by
      rw [← lamChar_inv_eq hq hmin hlam1]
      exact lamChar_le_R_of_mem_Aset hq hRlog hA
    have hne : χ₁⁻¹ ≠ 1 := fun h => hmin.1.1 (inv_eq_one.mp h)
    refine S1_plain (c := 0) hΛ hη (lt_of_lt_of_le (by norm_num) h348) hlam1Λ ?_
      (hPC χ₁⁻¹ hne lam₁ (by linarith) hlam1R (fun ρ hZ => by rw [← hlam1]; exact hmin.2 χ₁⁻¹ ρ hZ)) hrowB (by norm_num)
    intro ρ' hb' hz'
    rw [← hlam1]
    exact hmin.2 χ₁⁻¹ ρ' (box_api7_p1 hq hRlog hne hz' hb')
  have hS1point : ∀ χ ∈ ({χ₁, χ₁⁻¹} : Finset (DirichletCharacter ℂ q)) ∩ Aset q R,
      WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (((491473:ℝ)/(100000000)) + (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * wHB lam₁ + η) := by
    intro χ hχ
    obtain ⟨hχp, hχA⟩ := Finset.mem_inter.mp hχ
    rcases Finset.mem_insert.mp hχp with h | h
    · rw [h]; exact hpt1 (h ▸ hχA)
    · rw [Finset.mem_singleton.mp h]; exact hpt2 (Finset.mem_singleton.mp h ▸ hχA)
  have hTOT : (Phi ((51:ℝ)/(40)) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + ((2:ℕ):ℝ) * ((491473:ℝ)/(100000000)) + 2 * ((491473:ℝ)/(100000000))
        + max 0 ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] 8 : ℝ) - ((2:ℕ):ℝ) - 2) * Cf ((51:ℝ)/(40)) (min ((21:ℝ)/(20)) ((51:ℝ)/(40)))
        + ∑ j ∈ Finset.range 8, ((Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] j : ℝ) - (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] (j+1) : ℝ))
            * Cf ((51:ℝ)/(40)) (((51:ℝ)/(40)) - (25:ℝ)/1000 * ((j:ℝ)+1)) ≤ ((9968:ℝ)/10000) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using total_u4_8 hεw hεw1
  have hETA : (Real.exp (-(ac * ((51:ℝ)/(40)))) / Wf ((51:ℝ)/(40))) * ((67:ℝ)/6 + εw) + (Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] 0 : ℝ) + 4 ≤ 1000 := etab_u4_8 hεw hεw1
  have hcred : Cf ((51:ℝ)/(40)) (min ((21:ℝ)/(20)) ((51:ℝ)/(40))) ≤ ((491473:ℝ)/(100000000)) := by
    rw [show min ((21:ℝ)/(20)) ((51:ℝ)/(40)) = ((21:ℝ)/(20)) from by norm_num]
    exact (cred_u4_8).1
  have hc0 : (0:ℝ) < lam₁ := by linarith
  exact sec15_step (N := fun j => Nlist [100, 70, 53, 42, 35, 29, 25, 22, 19] j) (c₀ := lam₁) (l₂ := ((21:ℝ)/(20)))
    (l₃ := ((21:ℝ)/(20))) (CST1 := ((491473:ℝ)/(100000000))) (CST2 := ((491473:ℝ)/(100000000)))
    (n₁ := 2) (s := 8) hq hR hRlog hRmax hΛ hη hc0 hl2 hmin hlam1 h348 hlam1Λ
    le_rfl hLam0 hL2 hL3 (by simpa using hcard) hS1point hS hSiff hD1 hPC
    (hcount_u4_8 hmin hlam1 (by linarith) hD2) hle3 hlam1small
    hcred (by norm_num) (cred_u4_8).2.1 hTOT hETA

theorem sec15_uniform {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R η εw lam₁ : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hεw : 0 ≤ εw) (hεw1 : εw ≤ 1/1000)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (hlam1 : Work.LinnikContract.lamOf q ρ₁ = lam₁)
    (h348 : (348:ℝ)/1000 ≤ lam₁)
    (hZ2 : χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → (56:ℝ)/100 ≤ Work.LinnikContract.lamOf q ρ₁)
    (hZ3 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ ((695:ℝ)/1000) ∧ Work.LinnikContract.Lam2Bound χ₁ ((701:ℝ)/1000) ∧ Work.LinnikContract.Lam3Bound χ₁ ((856:ℝ)/1000))
    (hZ4 : ∀ r ∈ Work.LinnikContract.rows15, r.1 ≤ Work.LinnikContract.lamOf q ρ₁ → Work.LinnikContract.lamOf q ρ₁ ≤ r.2.1 →
        Work.LinnikContract.Lam0Bound χ₁ ρ₁ r.2.2.1 ∧ Work.LinnikContract.Lam2Bound χ₁ r.2.2.2.1 ∧ Work.LinnikContract.Lam3Bound χ₁ r.2.2.2.2)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13,
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → e.2.1 ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.Ncount q e.1 ≤ e.2.2)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η)) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
  by_cases hI : lam₁ ≤ (3:ℝ)/5
  · have hbI : lam₁ ≤ (3:ℝ)/5 := hI
    by_cases hc : χ₁ ^ 2 = 1
    · by_cases him : ρ₁.im = 0
      · -- rr: rows 0..12
        by_cases hb0 : lam₁ ≤ ((9:ℝ)/(25))
        · have hlamL : ((87:ℝ)/(250)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((9:ℝ)/(25)) := by rw [hlam1]; exact hb0
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((87:ℝ)/(250))), (((9:ℝ)/(25))), (((327:ℝ)/(250))), (((451:ℝ)/(500))), (((1229:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r0 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb0 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb1 : lam₁ ≤ ((19:ℝ)/(50))
        · have hlamL : ((9:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((19:ℝ)/(50)) := by rw [hlam1]; exact hb1
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((9:ℝ)/(25))), (((19:ℝ)/(50))), (((1249:ℝ)/(1000))), (((443:ℝ)/(500))), (((59:ℝ)/(50))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r1 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb1 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb2 : lam₁ ≤ ((2:ℝ)/(5))
        · have hlamL : ((19:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((2:ℝ)/(5)) := by rw [hlam1]; exact hb2
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((19:ℝ)/(50))), (((2:ℝ)/(5))), (((239:ℝ)/(200))), (((87:ℝ)/(100))), (((567:ℝ)/(500))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r2 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb2 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb3 : lam₁ ≤ ((21:ℝ)/(50))
        · have hlamL : ((2:ℝ)/(5)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((21:ℝ)/(50)) := by rw [hlam1]; exact hb3
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((2:ℝ)/(5))), (((21:ℝ)/(50))), (((143:ℝ)/(125))), (((171:ℝ)/(200))), (((1093:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r3 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb3 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb4 : lam₁ ≤ ((11:ℝ)/(25))
        · have hlamL : ((21:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((11:ℝ)/(25)) := by rw [hlam1]; exact hb4
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((21:ℝ)/(50))), (((11:ℝ)/(25))), (((549:ℝ)/(500))), (((841:ℝ)/(1000))), (((527:ℝ)/(500))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r4 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb4 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb5 : lam₁ ≤ ((23:ℝ)/(50))
        · have hlamL : ((11:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((23:ℝ)/(50)) := by rw [hlam1]; exact hb5
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((11:ℝ)/(25))), (((23:ℝ)/(50))), (((527:ℝ)/(500))), (((207:ℝ)/(250))), (((1017:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r5 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb5 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb6 : lam₁ ≤ ((12:ℝ)/(25))
        · have hlamL : ((23:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((12:ℝ)/(25)) := by rw [hlam1]; exact hb6
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((23:ℝ)/(50))), (((12:ℝ)/(25))), (((507:ℝ)/(500))), (((163:ℝ)/(200))), (((983:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r6 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb6 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb7 : lam₁ ≤ ((1:ℝ)/(2))
        · have hlamL : ((12:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((1:ℝ)/(2)) := by rw [hlam1]; exact hb7
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((12:ℝ)/(25))), (((1:ℝ)/(2))), (((122:ℝ)/(125))), (((401:ℝ)/(500))), (((951:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r7 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb7 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb8 : lam₁ ≤ ((13:ℝ)/(25))
        · have hlamL : ((1:ℝ)/(2)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((13:ℝ)/(25)) := by rw [hlam1]; exact hb8
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((1:ℝ)/(2))), (((13:ℝ)/(25))), (((47:ℝ)/(50))), (((79:ℝ)/(100))), (((921:ℝ)/(1000))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r8 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb8 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb9 : lam₁ ≤ ((27:ℝ)/(50))
        · have hlamL : ((13:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((27:ℝ)/(50)) := by rw [hlam1]; exact hb9
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((13:ℝ)/(25))), (((27:ℝ)/(50))), (((453:ℝ)/(500))), (((779:ℝ)/(1000))), (((223:ℝ)/(250))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r9 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb9 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb10 : lam₁ ≤ ((14:ℝ)/(25))
        · have hlamL : ((27:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((14:ℝ)/(25)) := by rw [hlam1]; exact hb10
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((27:ℝ)/(50))), (((14:ℝ)/(25))), (((437:ℝ)/(500))), (((96:ℝ)/(125))), (((173:ℝ)/(200))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r10 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb10 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        by_cases hb11 : lam₁ ≤ ((29:ℝ)/(50))
        · have hlamL : ((14:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((29:ℝ)/(50)) := by rw [hlam1]; exact hb11
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((14:ℝ)/(25))), (((29:ℝ)/(50))), (((211:ℝ)/(250))), (((379:ℝ)/(500))), (((107:ℝ)/(125))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r11 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb11 hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        · have hlamL : ((29:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((3:ℝ)/(5)) := by rw [hlam1]; exact hI
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((29:ℝ)/(50))), (((3:ℝ)/(5))), (((163:ℝ)/(200))), (((187:ℝ)/(250))), (((107:ℝ)/(125))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r12 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hI hL0 hL2 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
      · -- rc: rows 11,12
        by_cases hb11 : lam₁ ≤ ((29:ℝ)/(50))
        · have hlamL : ((14:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by have hh := hZ2 hc him; rw [hlam1] at hh; linarith)
          have hlamH : lamOf q ρ₁ ≤ ((29:ℝ)/(50)) := by rw [hlam1]; exact hb11
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((14:ℝ)/(25))), (((29:ℝ)/(50))), (((211:ℝ)/(250))), (((379:ℝ)/(500))), (((107:ℝ)/(125))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r11rc hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by have hh := hZ2 hc him; rw [hlam1] at hh; linarith) hb11 hL0 hL2 hL3 hc hS hSiff hD1 hPC hD2
        · have hlamL : ((29:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
          have hlamH : lamOf q ρ₁ ≤ ((3:ℝ)/(5)) := by rw [hlam1]; exact hI
          obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((29:ℝ)/(50))), (((3:ℝ)/(5))), (((163:ℝ)/(200))), (((187:ℝ)/(250))), (((107:ℝ)/(125))))
            (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
          exact cfg_r12rc hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hI hL0 hL2 hL3 hc hS hSiff hD1 hPC hD2
    · -- cx: rows 0..12
      by_cases hb0 : lam₁ ≤ ((9:ℝ)/(25))
      · have hlamL : ((87:ℝ)/(250)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((9:ℝ)/(25)) := by rw [hlam1]; exact hb0
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((87:ℝ)/(250))), (((9:ℝ)/(25))), (((327:ℝ)/(250))), (((451:ℝ)/(500))), (((1229:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r0 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb0 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb1 : lam₁ ≤ ((19:ℝ)/(50))
      · have hlamL : ((9:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((19:ℝ)/(50)) := by rw [hlam1]; exact hb1
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((9:ℝ)/(25))), (((19:ℝ)/(50))), (((1249:ℝ)/(1000))), (((443:ℝ)/(500))), (((59:ℝ)/(50))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r1 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb1 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb2 : lam₁ ≤ ((2:ℝ)/(5))
      · have hlamL : ((19:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((2:ℝ)/(5)) := by rw [hlam1]; exact hb2
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((19:ℝ)/(50))), (((2:ℝ)/(5))), (((239:ℝ)/(200))), (((87:ℝ)/(100))), (((567:ℝ)/(500))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r2 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb2 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb3 : lam₁ ≤ ((21:ℝ)/(50))
      · have hlamL : ((2:ℝ)/(5)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((21:ℝ)/(50)) := by rw [hlam1]; exact hb3
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((2:ℝ)/(5))), (((21:ℝ)/(50))), (((143:ℝ)/(125))), (((171:ℝ)/(200))), (((1093:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r3 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb3 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb4 : lam₁ ≤ ((11:ℝ)/(25))
      · have hlamL : ((21:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((11:ℝ)/(25)) := by rw [hlam1]; exact hb4
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((21:ℝ)/(50))), (((11:ℝ)/(25))), (((549:ℝ)/(500))), (((841:ℝ)/(1000))), (((527:ℝ)/(500))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r4 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb4 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb5 : lam₁ ≤ ((23:ℝ)/(50))
      · have hlamL : ((11:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((23:ℝ)/(50)) := by rw [hlam1]; exact hb5
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((11:ℝ)/(25))), (((23:ℝ)/(50))), (((527:ℝ)/(500))), (((207:ℝ)/(250))), (((1017:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r5 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb5 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb6 : lam₁ ≤ ((12:ℝ)/(25))
      · have hlamL : ((23:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((12:ℝ)/(25)) := by rw [hlam1]; exact hb6
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((23:ℝ)/(50))), (((12:ℝ)/(25))), (((507:ℝ)/(500))), (((163:ℝ)/(200))), (((983:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r6 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb6 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb7 : lam₁ ≤ ((1:ℝ)/(2))
      · have hlamL : ((12:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((1:ℝ)/(2)) := by rw [hlam1]; exact hb7
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((12:ℝ)/(25))), (((1:ℝ)/(2))), (((122:ℝ)/(125))), (((401:ℝ)/(500))), (((951:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r7 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb7 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb8 : lam₁ ≤ ((13:ℝ)/(25))
      · have hlamL : ((1:ℝ)/(2)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((13:ℝ)/(25)) := by rw [hlam1]; exact hb8
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((1:ℝ)/(2))), (((13:ℝ)/(25))), (((47:ℝ)/(50))), (((79:ℝ)/(100))), (((921:ℝ)/(1000))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r8 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb8 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb9 : lam₁ ≤ ((27:ℝ)/(50))
      · have hlamL : ((13:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((27:ℝ)/(50)) := by rw [hlam1]; exact hb9
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((13:ℝ)/(25))), (((27:ℝ)/(50))), (((453:ℝ)/(500))), (((779:ℝ)/(1000))), (((223:ℝ)/(250))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r9 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb9 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb10 : lam₁ ≤ ((14:ℝ)/(25))
      · have hlamL : ((27:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((14:ℝ)/(25)) := by rw [hlam1]; exact hb10
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((27:ℝ)/(50))), (((14:ℝ)/(25))), (((437:ℝ)/(500))), (((96:ℝ)/(125))), (((173:ℝ)/(200))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r10 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb10 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      by_cases hb11 : lam₁ ≤ ((29:ℝ)/(50))
      · have hlamL : ((14:ℝ)/(25)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((29:ℝ)/(50)) := by rw [hlam1]; exact hb11
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((14:ℝ)/(25))), (((29:ℝ)/(50))), (((211:ℝ)/(250))), (((379:ℝ)/(500))), (((107:ℝ)/(125))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r11 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb11 hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
      · have hlamL : ((29:ℝ)/(50)) ≤ lamOf q ρ₁ := by rw [hlam1]; exact (by linarith)
        have hlamH : lamOf q ρ₁ ≤ ((3:ℝ)/(5)) := by rw [hlam1]; exact hI
        obtain ⟨hL0, hL2, hL3⟩ := hZ4 ((((29:ℝ)/(50))), (((3:ℝ)/(5))), (((163:ℝ)/(200))), (((187:ℝ)/(250))), (((107:ℝ)/(125))))
          (by norm_num [Work.LinnikContract.rows15]) hlamL hlamH
        exact cfg_r12 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hI hL0 hL2 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
  · by_cases hII : lam₁ ≤ (139:ℝ)/200
    · by_cases hc : χ₁ ^ 2 = 1
      · by_cases him : ρ₁.im = 0
        · have hL0 : Lam0Bound χ₁ ρ₁ ((139:ℝ)/200) := by
            rw [show ((139:ℝ)/200) = ((695:ℝ)/1000) from by norm_num]; exact hZ3.1
          have hL3 : Lam3Bound χ₁ ((107:ℝ)/125) := by
            rw [show ((107:ℝ)/125) = ((856:ℝ)/1000) from by norm_num]; exact hZ3.2.2
          exact cfg_u2 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hII hL0 hZ3.2.1 hL3 (fun _ => him) hS hSiff hD1 hPC hD2
        · have hL0 : Lam0Bound χ₁ ρ₁ ((139:ℝ)/200) := by
            rw [show ((139:ℝ)/200) = ((695:ℝ)/1000) from by norm_num]; exact hZ3.1
          have hL3 : Lam3Bound χ₁ ((107:ℝ)/125) := by
            rw [show ((107:ℝ)/125) = ((856:ℝ)/1000) from by norm_num]; exact hZ3.2.2
          exact cfg_u2rc hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hII hL0 hZ3.2.1 hL3 hc hS hSiff hD1 hPC hD2
      · have hL0 : Lam0Bound χ₁ ρ₁ ((139:ℝ)/200) := by
          rw [show ((139:ℝ)/200) = ((695:ℝ)/1000) from by norm_num]; exact hZ3.1
        have hL3 : Lam3Bound χ₁ ((107:ℝ)/125) := by
          rw [show ((107:ℝ)/125) = ((856:ℝ)/1000) from by norm_num]; exact hZ3.2.2
        exact cfg_u2 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hII hL0 hZ3.2.1 hL3 (fun h => absurd h hc) hS hSiff hD1 hPC hD2
    · by_cases hIII : lam₁ ≤ (7:ℝ)/8
      · have hZ3L3 : Lam3Bound χ₁ ((107:ℝ)/125) := by
          rw [show ((107:ℝ)/125) = ((856:ℝ)/1000) from by norm_num]; exact hZ3.2.2
        exact cfg_u3 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hIII hZ3.2.1 hZ3L3 hS hSiff hD1 hPC hD2
      by_cases hb0 : lam₁ ≤ ((9:ℝ)/(10))
      · exact cfg_u4_15 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb0 hS hSiff hD1 hPC hD2
      by_cases hb1 : lam₁ ≤ ((37:ℝ)/(40))
      · exact cfg_u4_14 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb1 hS hSiff hD1 hPC hD2
      by_cases hb2 : lam₁ ≤ ((19:ℝ)/(20))
      · exact cfg_u4_13 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb2 hS hSiff hD1 hPC hD2
      by_cases hb3 : lam₁ ≤ ((39:ℝ)/(40))
      · exact cfg_u4_12 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb3 hS hSiff hD1 hPC hD2
      by_cases hb4 : lam₁ ≤ ((1:ℝ)/(1))
      · exact cfg_u4_11 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb4 hS hSiff hD1 hPC hD2
      by_cases hb5 : lam₁ ≤ ((41:ℝ)/(40))
      · exact cfg_u4_10 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb5 hS hSiff hD1 hPC hD2
      by_cases hb6 : lam₁ ≤ ((21:ℝ)/(20))
      · exact cfg_u4_9 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb6 hS hSiff hD1 hPC hD2
      by_cases hb7 : lam₁ ≤ ((43:ℝ)/(40))
      · exact cfg_u4_8 hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 (by linarith) hb7 hS hSiff hD1 hPC hD2
      · have h1075 : (43:ℝ)/40 ≤ lam₁ := by linarith
        exact sec15_crude hq hR hRlog hRmax hη hεw hεw1 hmin hlam1 h1075 hS hSiff hD1 hPC

end

end Work.A7
