import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.A7.WBox_refined
import Submission.Work.A7.box_api7

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract
open Work.LinnikAreas.A7

theorem chi1_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R c η lam : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hRlog : R ≤ Real.log q) (hRpos : 0 < R)
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁)
    (hZ1 : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ Work.LinnikContract.zeroMult χ₁ ρ₁ = 1)
    (hLam0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ c)
    (hlam : Work.LinnikContract.lamOf q ρ₁ = lam) (hlam0 : 0 < lam) (hRlam : lam ≤ R)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η)) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ₁
      ≤ Real.exp (-(Work.LinnikAreas.A7.ac * lam)) * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2)
        + ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) := by
  classical
  have hac : (0:ℝ) < ac := Work.LinnikAreas.A7.ac_pos
  have hchi1 : χ₁ ≠ 1 := hmin.1.1
  have hmult : Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 := hZ1.2.2
  have him : ρ₁.im = 0 := hZ1.2.1
  have hconj : (starRingEnd ℂ) ρ₁ = ρ₁ := Complex.conj_eq_iff_im.mpr him
  -- `λ(ρ₁) = lam` is a lower bound for the zero-parameter of every box zero of `χ₁`
  have hlow : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 →
      lam ≤ Work.LinnikContract.lamOf q ρ := by
    intro ρ hbox hzm
    have hZ : Work.LinnikContract.IsZ χ₁ ρ := box_api7_p1 hq hRlog hchi1 hzm hbox
    have h := hmin.2 χ₁ ρ hZ
    rwa [hlam] at h
  have hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ₁
      ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) :=
    hPC χ₁ hchi1 lam hlam0.le hRlam (fun ρ hZ => by
      have h := hmin.2 χ₁ ρ hZ
      rwa [hlam] at h)
  by_cases hlamc : lam ≤ c
  · -- the refined branch: the isolated simple zero `ρ₁` carries the full weight `e^{-a·lam}`
    have hbox : Work.LinnikContract.InBox q R ρ₁ := by
      refine ⟨?_, ?_⟩
      · rw [hlam]; exact hRlam
      · rw [him]; simp only [abs_zero, zero_mul]; exact hRpos.le
    have hsecond : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ →
        Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 → ρ ≠ ρ₁ → c ≤ Work.LinnikContract.lamOf q ρ := by
      intro ρ hbox hzm hne
      have hZ : Work.LinnikContract.IsZ χ₁ ρ := box_api7_p1 hq hRlog hchi1 hzm hbox
      exact hLam0.2 ρ hZ hne (fun _ => by rw [hconj]; exact hne)
    have hW := WBox_refined (q := q) (χ := χ₁) (ρs := ρ₁) hbox hmult hlam hlam0 hlamc hsecond hcert
    have hkey : ((9:ℝ)/100) * (Phi lam - Aref c lam)
          + ((9:ℝ)/100) * Real.exp (-(ac * c)) * η
        = ((9:ℝ)/100) * Real.exp (-(ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
          + (Real.exp (-(ac * lam)) - Real.exp (-(ac * c)))
              * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2) := by
      rw [Phi, Aref]
      simp only [Kc, K2]
      field_simp
      ring
    calc WBox q ((3:ℝ)/10) R χ₁
        ≤ ((9:ℝ)/100) * (Phi lam - Aref c lam) + ((9:ℝ)/100) * Real.exp (-(ac * c)) * η := hW
      _ = ((9:ℝ)/100) * Real.exp (-(ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)
            + (Real.exp (-(ac * lam)) - Real.exp (-(ac * c)))
                * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2) := hkey
      _ ≤ Real.exp (-(ac * lam)) * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2)
            + ((9:ℝ)/100) * Real.exp (-(ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) := by
          have h0 : 0 ≤ Real.exp (-(ac * c)) *
              (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2) :=
            mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
          nlinarith [h0]
  · -- otherwise `c < lam`, so every box zero is weighted by at most `e^{-a·c}`
    push Not at hlamc
    have hW := WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ₁ hlow
    have hboxAbs_nn : 0 ≤ Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ₁ :=
      (Work.LinnikContract.API.box_api).2.2 q ((3:ℝ)/10) R χ₁
    have hElam : Real.exp (-(ac * lam)) ≤ Real.exp (-(ac * c)) := by
      rw [Real.exp_le_exp]; nlinarith [hac, hlamc.le]
    calc WBox q ((3:ℝ)/10) R χ₁
        ≤ Real.exp (-(ac * lam)) * Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ₁ := hW
      _ ≤ Real.exp (-(ac * c)) * Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ₁ :=
          mul_le_mul_of_nonneg_right hElam hboxAbs_nn
      _ ≤ Real.exp (-(ac * c)) * (((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)) :=
          mul_le_mul_of_nonneg_left hcert (Real.exp_nonneg _)
      _ ≤ Real.exp (-(ac * lam)) * (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2)
            + ((9:ℝ)/100) * Real.exp (-(ac * c)) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η) := by
          have h1 : 0 ≤ Real.exp (-(ac * lam)) *
              (((1 - Real.exp (-(((3:ℝ)/10) * lam))) / lam) ^ 2) :=
            mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
          nlinarith [h1]

end

end Work.A7
