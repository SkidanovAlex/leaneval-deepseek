import Mathlib
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.FiberEndsA

theorem A_lo_mem (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ a : ℕ, ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F0 D (p + 1) →
      Work.WilG4c.A_lo p Z ∈ S.Ω a (100 * D + 1000) (p + 1) := by
  let a1 : ℕ := max (F0 + (p + 2)) ((p + 2) + (p + 1)) + 1 + (p + 1)
  let a3 : ℕ := max (F0 + (p + 3)) ((p + 3) + (p + 1)) + 1 + (p + 1)
  let FNE1 : ℕ := a1 + 1
  let FLBb : ℕ := (max a1 (p + 2 + 3) + 1) + 1
  let FLB1 : ℕ := FLBb + 1
  let G0 : ℕ := max a3 (p + 3 + 3) + 1
  let G2 : ℕ := (G0 + 1) + 1
  let G3 : ℕ := max G2 (p + 2 + 3) + 1
  let FGLBb : ℕ := G3 + 1
  let FGLB1 : ℕ := FGLBb + 1
  let F1 : ℕ := max (max FNE1 FLB1 + 1) FGLB1 + 1
  let F2 : ℕ := max (FNE1 + 1) (p + 1) + 1
  refine ⟨max F1 F2, ?_⟩
  intro D Z hZ
  -- the two pullbacks of `Z`
  have hpull2 : Work.WilG4c.pull2 p Z ∈ S.Ω a1 (D + 2) (p + 2) :=
    Work.WilG4c.Subst S (Work.WilG4c.iota1 p) hZ
  have hpull3 : Work.WilG4c.pull3 p Z ∈ S.Ω a3 (D + 2) (p + 3) :=
    Work.WilG4c.Subst S (Work.WilG4c.iota2 p) hZ
  -- `NE1`
  have hNE1 : Work.WilG4c.NE1 p Z ∈ S.Ω FNE1 (D + 2) (p + 1) := S.proj hpull2
  -- the coordinate comparisons
  have hlt2 : Work.WilG4c.lastLtMid p ∈ S.Ω (p + 2 + 3) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) D
      (Fin.last (p + 1)) (Fin.castSucc (Fin.last p))
    have h' : Work.WilG4c.lastLtMid p ∈ S.Ω (p + 2 + 3) ((Polynomial.C 3).eval D) (p + 2) := by
      simpa only [Work.WilG4c.lastLtMid] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  have hmid2 : Work.WilG4c.midLtLast p ∈ S.Ω (p + 2 + 3) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) D
      (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))
    have h' : Work.WilG4c.midLtLast p ∈ S.Ω (p + 2 + 3) ((Polynomial.C 3).eval D) (p + 2) := by
      simpa only [Work.WilG4c.midLtLast] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  have hlt3 : Work.WilG4c.lastLtMid3 p ∈ S.Ω (p + 3 + 3) 3 (p + 3) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 3) D
      (Fin.last (p + 2)) (Fin.castSucc (Fin.last (p + 1)))
    have h' : Work.WilG4c.lastLtMid3 p ∈ S.Ω (p + 3 + 3) ((Polynomial.C 3).eval D) (p + 3) := by
      simpa only [Work.WilG4c.lastLtMid3] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  -- `LB1 = (projLast (pull2 Z ∩ lastLtMid))ᶜ`
  have hLBb : Work.WilG4c.LBb p Z ∈ S.Ω FLBb ((D + 2) + 3) (p + 1) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpull2)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hlt2))
  have hLB1 : Work.WilG4c.LB1 p Z ∈ S.Ω FLB1 ((D + 2) + 3) (p + 1) := S.compl hLBb
  -- `GLB1 = (projLast ((projLast (pull3 Z ∩ lastLtMid3))ᶜ ∩ midLtLast))ᶜ`
  have hprojlt3 : WilkiesDesign.projLast (Work.WilG4c.pull3 p Z ∩ Work.WilG4c.lastLtMid3 p) ∈
      S.Ω (G0 + 1) ((D + 2) + 3) (p + 2) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpull3)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hlt3))
  have hG2 : (WilkiesDesign.projLast (Work.WilG4c.pull3 p Z ∩ Work.WilG4c.lastLtMid3 p))ᶜ ∈
      S.Ω G2 ((D + 2) + 3) (p + 2) := S.compl hprojlt3
  have hGLBb : Work.WilG4c.GLBb p Z ∈ S.Ω FGLBb (((D + 2) + 3) + 3) (p + 1) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hG2)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hmid2))
  have hGLB1 : Work.WilG4c.GLB1 p Z ∈ S.Ω FGLB1 (((D + 2) + 3) + 3) (p + 1) :=
    S.compl hGLBb
  -- the first disjunct `NE1 ∩ LB1 ∩ GLB1`
  have hpart1 : (Work.WilG4c.NE1 p Z ∩ Work.WilG4c.LB1 p Z ∩ Work.WilG4c.GLB1 p Z) ∈
      S.Ω F1 ((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _)
        (Work.WilG0.Omega_inter2 (S := S)
          (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hNE1)
          (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hLB1)))
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hGLB1)
  -- the second disjunct `NE1ᶜ ∩ yZero`
  have hyZero : Work.WilG4c.yZero p ∈ S.Ω (p + 1) 1 (p + 1) := by
    have h := S.hyp (p + 1) (MvPolynomial.X (Fin.last p))
    simpa [Work.WilG4c.yZero, MvPolynomial.totalDegree_X] using h
  have hpart2 : ((Work.WilG4c.NE1 p Z)ᶜ ∩ Work.WilG4c.yZero p) ∈
      S.Ω F2 ((D + 2) + 1) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) (S.compl hNE1))
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hyZero)
  -- union
  have hun : ((Work.WilG4c.NE1 p Z ∩ Work.WilG4c.LB1 p Z ∩ Work.WilG4c.GLB1 p Z) ∪
      ((Work.WilG4c.NE1 p Z)ᶜ ∩ Work.WilG4c.yZero p)) ∈
      S.Ω (max F1 F2)
        (((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) + ((D + 2) + 1)) (p + 1) :=
    Work.WilG0.Omega_union2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpart1)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hpart2)
  have hdeg : ((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) + ((D + 2) + 1) ≤
      100 * D + 1000 := by omega
  exact Work.WilG0.Omega_mono_D (S := S) hdeg hun

end Work.WilG4c.FiberEndsA
