import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.A7.lamChar_api
import Submission.Work.A7.box_api7
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.A7.ExpWf_antitone
import Submission.Work.A7.Bfun_antitone
import Submission.Work.A7.chi1_le
import Submission.Work.A7.tail_le

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators

theorem core14 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R c η εw lam : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hcpos : 0 < c)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁)
    (hlam : Work.LinnikContract.lamOf q ρ₁ = lam) (hlam0 : 0 < lam)
    (hZ1 : (χ₁ ^ 2 = 1) ∧ (ρ₁.im = 0) ∧ (Work.LinnikContract.zeroMult χ₁ ρ₁ = 1) ∧
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) →
        (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ))
    (hLam0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ c)
    (hLam2 : Work.LinnikContract.Lam2Bound χ₁ c)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η)) :
    ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
            (((1 - Real.exp (-((3:ℝ)/10 * lam))) / lam) ^ 2 / ((9:ℝ)/100))
          + Real.exp (-(Work.LinnikAreas.A7.ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
          + (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c * ((67:ℝ)/6 + εw) + 1) := by
  classical
  set T : Finset (DirichletCharacter ℂ q) := Work.LinnikAreas.A7.Aset q R with hT
  -- membership characterisation of `Aset`
  have hmemAset : ∀ χ : DirichletCharacter ℂ q, χ ∈ T ↔
      χ ≠ 1 ∧ ∃ ρ : ℂ, Work.LinnikContract.InBox q R ρ ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
    intro χ
    simp only [hT, Work.LinnikAreas.A7.Aset, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true]
  -- the tail bound
  have htail := tail_le14 (q := q) (ρ₁ := ρ₁) hq hR hRlog hRmax hη hcpos hZ1.1 hLam2 hS hSiff hD1 hPC
  rw [← hT] at htail
  -- the `χ₁` bound
  set chi1b : ℝ :=
    Real.exp (-(Work.LinnikAreas.A7.ac * lam)) * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2)
      + ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
    with hchi1b
  have hchi1b_nonneg : 0 ≤ chi1b := by
    have hac : (0:ℝ) < Work.LinnikAreas.A7.ac := Work.LinnikAreas.A7.ac_pos
    have hB : 0 ≤ Work.LinnikContract.Bfun ((3:ℝ)/10) lam :=
      (Work.LinnikContract.API.Bfun_pos (by norm_num) hlam0).le
    have h1 : 0 ≤ Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
        (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2) :=
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have h2 : 0 ≤ ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) *
        (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (by linarith)
    rw [hchi1b]; linarith
  have hsplit : (∑ χ ∈ T, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
      ≤ (∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ) + chi1b := by
    by_cases hmem : χ₁ ∈ T
    · have hsum := Finset.sum_erase_add T
        (fun χ => Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ) hmem
      have hlamR : lam ≤ R := by
        obtain ⟨hne1, ρ, hboxρ, hmρ⟩ := (hmemAset χ₁).mp hmem
        have hZ : Work.LinnikContract.IsZ χ₁ ρ := box_api7_p1 hq hRlog hne1 hmρ hboxρ
        have h2 := hmin.2 χ₁ ρ hZ
        rw [hlam] at h2
        exact le_trans h2 hboxρ.1
      have hc1 := chi1_le (q := q) hq hRlog hR hmin ⟨hZ1.1, hZ1.2.1, hZ1.2.2.1⟩ hLam0 hlam hlam0 hlamR hPC
      have hble : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ₁ ≤ chi1b := by
        rw [hchi1b]; exact hc1
      linarith [hsum]
    · have hEq : T.erase χ₁ = T := Finset.erase_eq_of_notMem hmem
      rw [hEq]
      linarith [hchi1b_nonneg]
  have hmain : (∑ χ ∈ T, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ) ≤
      ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
      + chi1b := le_trans hsplit (add_le_add htail (le_refl chi1b))
  -- final arithmetic
  have hArith : ((9:ℝ)/100) * (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
            (((1 - Real.exp (-((3:ℝ)/10 * lam))) / lam) ^ 2 / ((9:ℝ)/100))
          + Real.exp (-(Work.LinnikAreas.A7.ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
          + (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c * ((67:ℝ)/6 + εw) + 1)
      = ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + chi1b
        + ((9:ℝ)/100) * η := by
    rw [hchi1b]; ring
  have hfin : ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
      + chi1b
      ≤ ((9:ℝ)/100) * (Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
            (((1 - Real.exp (-((3:ℝ)/10 * lam))) / lam) ^ 2 / ((9:ℝ)/100))
          + Real.exp (-(Work.LinnikAreas.A7.ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
          + (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c * ((67:ℝ)/6 + εw) + 1) := by
    have hnn : 0 ≤ ((9:ℝ)/100) * η := mul_nonneg (by norm_num) hη
    linarith [hArith]
  exact le_trans hmain hfin

end Work.A7
