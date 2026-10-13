import Mathlib
import Submission.Work.WilCrux.FailSetChainDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 4. The atoms are `Ω`-sets -/

theorem fmWd_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (i : Fin a) :
    fmWd a b i ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos3_mem (fmetaD a b) (fmwpD a b i) (fmwD a b i)

theorem fmWu_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (i : Fin a) :
    fmWu a b i ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos3_mem (fmetaD a b) (fmwD a b i) (fmwpD a b i)

theorem fmZlow_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    fmZlow a b j ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos2_mem (fmetaD a b) (fmzD a b j)

theorem fmZup_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    fmZup a b j ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos2p_mem (fmetaD a b) (fmzD a b j)

theorem fmZlowp_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    fmZlowp a b j ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos2_mem (fmetaD a b) (fmzpD a b j)

theorem fmZupp_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    fmZupp a b j ∈ S.Ω (fmD a b + 2) 3 (fmD a b) :=
  fm_pos2p_mem (fmetaD a b) (fmzpD a b j)

theorem fm_hyper_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    {v : Fin (fmD a b) → ℝ | v (fmzD a b j) = 0} ∈ S.Ω (fmD a b) 1 (fmD a b) := by
  have h := S.hyp (fmD a b) ((MvPolynomial.X (fmzD a b j)) : MvPolynomial (Fin (fmD a b)) ℝ)
  simpa [MvPolynomial.eval_X, MvPolynomial.totalDegree_X] using h

theorem fm_hyperp_mem {S : WilkiesDesign.SOMin} {a b : ℕ} (j : Fin b) :
    {v : Fin (fmD a b) → ℝ | v (fmzpD a b j) = 0} ∈ S.Ω (fmD a b) 1 (fmD a b) := by
  have h := S.hyp (fmD a b) ((MvPolynomial.X (fmzpD a b j)) : MvPolynomial (Fin (fmD a b)) ℝ)
  simpa [MvPolynomial.eval_X, MvPolynomial.totalDegree_X] using h

theorem fmZne_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmZne a b ∈ S.Ω (fmD a b + 2) b (fmD a b) := by
  have h2 := Work.WilG1.Omega.inter_mem (S := S) (n := fmD a b) (k := b)
    (a := fmD a b) (b := (1 : Polynomial ℕ)) (D := 0)
    (fun j : Fin b => {v : Fin (fmD a b) → ℝ | v (fmzD a b j) = 0})
    (by intro j; simpa using fm_hyper_mem (S := S) (a := a) (b := b) j)
  have h3 := S.compl h2
  rw [fmZne]
  have : ((Polynomial.C b * (1 : Polynomial ℕ))).eval 0 = b := by simp
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) (le_of_eq this) h3

theorem fmZpne_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmZpne a b ∈ S.Ω (fmD a b + 2) b (fmD a b) := by
  have h2 := Work.WilG1.Omega.inter_mem (S := S) (n := fmD a b) (k := b)
    (a := fmD a b) (b := (1 : Polynomial ℕ)) (D := 0)
    (fun j : Fin b => {v : Fin (fmD a b) → ℝ | v (fmzpD a b j) = 0})
    (by intro j; simpa using fm_hyperp_mem (S := S) (a := a) (b := b) j)
  have h3 := S.compl h2
  rw [fmZpne]
  have : ((Polynomial.C b * (1 : Polynomial ℕ))).eval 0 = b := by simp
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) (le_of_eq this) h3

theorem fmWdist_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmWdist a b ∈ S.Ω (fmD a b + 4) (6 * a) (fmD a b) := by
  have h1 : ∀ i : Fin a, fmWd a b i ∩ fmWu a b i ∈
      S.Ω (fmD a b + 3) ((Polynomial.C 6).eval 0) (fmD a b) := by
    intro i
    have h := Work.WilG0.Omega_inter2 (S := S)
      (fmWd_mem (S := S) (a := a) (b := b) i) (fmWu_mem (S := S) (a := a) (b := b) i)
    simpa using h
  have h2 := Work.WilG1.Omega.inter_mem (S := S) (n := fmD a b) (k := a)
    (a := fmD a b + 3) (b := (Polynomial.C 6)) (D := 0)
    (fun i : Fin a => fmWd a b i ∩ fmWu a b i)
    (by intro i; simpa using h1 i)
  rw [fmWdist]
  have heq : ((Polynomial.C a * Polynomial.C 6)).eval 0 = 6 * a := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) (le_of_eq heq) h2

theorem fmNormZ_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmNormZ a b ∈ S.Ω (fmD a b + 4) (6 * b) (fmD a b) := by
  have h1 : ∀ j : Fin b, fmZlow a b j ∩ fmZup a b j ∈
      S.Ω (fmD a b + 3) ((Polynomial.C 6).eval 0) (fmD a b) := by
    intro j
    have h := Work.WilG0.Omega_inter2 (S := S)
      (fmZlow_mem (S := S) (a := a) (b := b) j) (fmZup_mem (S := S) (a := a) (b := b) j)
    simpa using h
  have h2 := Work.WilG1.Omega.inter_mem (S := S) (n := fmD a b) (k := b)
    (a := fmD a b + 3) (b := (Polynomial.C 6)) (D := 0)
    (fun j : Fin b => fmZlow a b j ∩ fmZup a b j)
    (by intro j; simpa using h1 j)
  rw [fmNormZ]
  have heq : ((Polynomial.C b * Polynomial.C 6)).eval 0 = 6 * b := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) (le_of_eq heq) h2

theorem fmNormZp_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmNormZp a b ∈ S.Ω (fmD a b + 4) (6 * b) (fmD a b) := by
  have h1 : ∀ j : Fin b, fmZlowp a b j ∩ fmZupp a b j ∈
      S.Ω (fmD a b + 3) ((Polynomial.C 6).eval 0) (fmD a b) := by
    intro j
    have h := Work.WilG0.Omega_inter2 (S := S)
      (fmZlowp_mem (S := S) (a := a) (b := b) j) (fmZupp_mem (S := S) (a := a) (b := b) j)
    simpa using h
  have h2 := Work.WilG1.Omega.inter_mem (S := S) (n := fmD a b) (k := b)
    (a := fmD a b + 3) (b := (Polynomial.C 6)) (D := 0)
    (fun j : Fin b => fmZlowp a b j ∩ fmZupp a b j)
    (by intro j; simpa using h1 j)
  rw [fmNormZp]
  have heq : ((Polynomial.C b * Polynomial.C 6)).eval 0 = 6 * b := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) (le_of_eq heq) h2

/-- The hypothesis conjunction, at format `fmD+8` and degree `6a + 14b`. -/
theorem fmHyp_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmHyp a b ∈ S.Ω (fmD a b + 8) (6 * a + 14 * b) (fmD a b) := by
  have hW := fmWdist_mem (S := S) (a := a) (b := b)
  have hZ := fmZne_mem (S := S) (a := a) (b := b)
  have hNZ := fmNormZ_mem (S := S) (a := a) (b := b)
  have hZp := fmZpne_mem (S := S) (a := a) (b := b)
  have hNZp := fmNormZp_mem (S := S) (a := a) (b := b)
  have i1 := Work.WilG1.Omega.inter₂ (S := S) (b₁ := Polynomial.C (6 * a))
    (b₂ := Polynomial.C b) (D := 0) (X := fmWdist a b) (Y := fmZne a b)
    (by simpa using hW) (by simpa using hZ)
  have i1' : fmWdist a b ∩ fmZne a b ∈ S.Ω (fmD a b + 5) (6 * a + b) (fmD a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ ?_ i1
    · omega
    · simp only [Polynomial.eval_add, Polynomial.eval_C]
      omega
  have i2 := Work.WilG1.Omega.inter₂ (S := S) (b₁ := Polynomial.C (6 * a + b))
    (b₂ := Polynomial.C (6 * b)) (D := 0)
    (X := fmWdist a b ∩ fmZne a b) (Y := fmNormZ a b)
    (by simpa using i1') (by simpa using hNZ)
  have i2' : fmWdist a b ∩ fmZne a b ∩ fmNormZ a b ∈
      S.Ω (fmD a b + 6) (6 * a + b + 6 * b) (fmD a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ ?_ i2
    · omega
    · simp only [Polynomial.eval_add, Polynomial.eval_C]
      omega
  have i3 := Work.WilG1.Omega.inter₂ (S := S) (b₁ := Polynomial.C (6 * a + b + 6 * b))
    (b₂ := Polynomial.C b) (D := 0)
    (X := fmWdist a b ∩ fmZne a b ∩ fmNormZ a b) (Y := fmZpne a b)
    (by simpa using i2') (by simpa using hZp)
  have i3' : fmWdist a b ∩ fmZne a b ∩ fmNormZ a b ∩ fmZpne a b ∈
      S.Ω (fmD a b + 7) (6 * a + b + 6 * b + b) (fmD a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ ?_ i3
    · omega
    · simp only [Polynomial.eval_add, Polynomial.eval_C]
      omega
  have i4 := Work.WilG1.Omega.inter₂ (S := S)
    (b₁ := Polynomial.C (6 * a + b + 6 * b + b)) (b₂ := Polynomial.C (6 * b)) (D := 0)
    (X := fmWdist a b ∩ fmZne a b ∩ fmNormZ a b ∩ fmZpne a b) (Y := fmNormZp a b)
    (by simpa using i3') (by simpa using hNZp)
  rw [fmHyp]
  refine Work.WilG0.Omega_mono_FD (S := S) ?_ ?_ i4
  · omega
  · simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega

/-! ## 5. The body and its `Ω`-membership -/

/-- The `|y - y'| < ε` atom is `Ω`-definable. -/
theorem fmAbsLt_mem {S : WilkiesDesign.SOMin} {a b : ℕ} :
    fmAbsLt a b ∈ S.Ω (fmN a b + 3) 6 (fmN a b) := by
  have hA := fm_pos3_mem (S := S) (n := fmN a b) (fmepsN a b) (fmyN a b) (fmypN a b)
  have hB := fm_pos3_mem (S := S) (n := fmN a b) (fmepsN a b) (fmypN a b) (fmyN a b)
  have h := Work.WilG0.Omega_inter2 (S := S) hA hB
  rw [fmAbsLt]
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  omega

/-- The body conjunction is `Ω`-definable. -/
theorem fmK_mem {S : WilkiesDesign.SOMin} {a b F0 degT : ℕ}
    (T : Set (Fin ((a + b) + 1) → ℝ)) (hT : T ∈ S.Ω F0 degT ((a + b) + 1)) :
    fmK a b T ∈ S.Ω (F0 + fmFpb a b + 2) ((fmKdeg a b).eval degT) (fmN a b) := by
  have h1 := Work.WilG5.coordPre_mem (S := S) (m := (a + b) + 1) (N := fmN a b)
    (ι := fme1 a b) (A := T) hT
  have h2 := Work.WilG5.coordPre_mem (S := S) (m := (a + b) + 1) (N := fmN a b)
    (ι := fme2 a b) (A := T) hT
  have h1' : Work.WilG5.coordPre (fme1 a b) T ∈
      S.Ω (F0 + fmFpb a b) ((fmDP a b).eval degT) (fmN a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h1
    simp only [fmDP, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  have h2' : Work.WilG5.coordPre (fme2 a b) T ∈
      S.Ω (F0 + fmFpb a b) ((fmDP a b).eval degT) (fmN a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h2
    simp only [fmDP, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  have h3 := fmAbsLt_mem (S := S) (a := a) (b := b)
  have h3''' : fmAbsLt a b ∈ S.Ω (fmN a b + 3) ((Polynomial.C 6).eval degT) (fmN a b) := by
    simpa only [Polynomial.eval_C] using h3
  have h3'' : fmAbsLt a b ∈ S.Ω (F0 + fmFpb a b + 1) ((Polynomial.C 6).eval degT) (fmN a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ (le_refl _) h3'''
    simp only [fmFpb, fmN, fmD, fmE, fmB]
    omega
  have h12 := Work.WilG1.Omega.inter₂ (S := S) (D := degT) (b₁ := fmDP a b) (b₂ := fmDP a b)
    (X := Work.WilG5.coordPre (fme1 a b) T) (Y := Work.WilG5.coordPre (fme2 a b) T) h1' h2'
  have h12' : Work.WilG5.coordPre (fme1 a b) T ∩ Work.WilG5.coordPre (fme2 a b) T ∈
      S.Ω (F0 + fmFpb a b + 1) (((fmDP a b) + fmDP a b).eval degT) (fmN a b) := by
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ (le_refl _) h12
    simp only [max_self]
    omega
  have hres := Work.WilG1.Omega.inter₂ (S := S) (D := degT)
    (b₁ := (fmDP a b) + fmDP a b) (b₂ := Polynomial.C 6)
    (X := Work.WilG5.coordPre (fme1 a b) T ∩ Work.WilG5.coordPre (fme2 a b) T)
    (Y := fmAbsLt a b) h12' h3''
  rw [fmK]
  refine Work.WilG0.Omega_mono_FD (S := S) ?_ (le_refl _) hres
  simp only [max_self]
  omega

/-! ## 6. The chain is `Ω`-definable -/

theorem fmPosEta_mem {S : WilkiesDesign.SOMin} {a : ℕ} :
    fmPosEta a ∈ S.Ω (fmE a + 2) 3 (fmE a) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := fmE a) 0
    ((MvPolynomial.X (Fin.last (a + 1))) : MvPolynomial (Fin (fmE a)) ℝ)
  have hset : {v : Fin (fmE a) → ℝ | 0 < MvPolynomial.eval v
        ((MvPolynomial.X (Fin.last (a + 1))) : MvPolynomial (Fin (fmE a)) ℝ)} = fmPosEta a := by
    ext v; simp [fmPosEta, MvPolynomial.eval_X]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  simp only [Polynomial.eval_C, MvPolynomial.totalDegree_X]
  omega

theorem fmPosEps_mem {S : WilkiesDesign.SOMin} {a : ℕ} :
    fmPosEps a ∈ S.Ω ((a + 1) + 2) 3 (a + 1) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := a + 1) 0
    ((MvPolynomial.X (Fin.last a)) : MvPolynomial (Fin (a + 1)) ℝ)
  have hset : {v : Fin (a + 1) → ℝ | 0 < MvPolynomial.eval v
        ((MvPolynomial.X (Fin.last a)) : MvPolynomial (Fin (a + 1)) ℝ)} = fmPosEps a := by
    ext v; simp [fmPosEps, MvPolynomial.eval_X]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  simp only [Polynomial.eval_C, MvPolynomial.totalDegree_X]
  omega

theorem fmChain_mem (S : WilkiesDesign.SOMin) {a b : ℕ}
    (T : Set (Fin ((a + b) + 1) → ℝ)) {F0 degT : ℕ} (hT : T ∈ S.Ω F0 degT ((a + b) + 1)) :
    fmChain a b T ∈ S.Ω (F0 + (500 * (a + b) + 5000))
      ((Polynomial.C 2 * Polynomial.X + Polynomial.C (10000 * (a + b) + 100000)).eval degT)
      (a + 1) := by
  have hK := fmK_mem (S := S) (a := a) (b := b) (F0 := F0) (degT := degT) T hT
  have hK1 := Work.WilG0.projLastIter_mem S (fmD a b) 2 (F0 + fmFpb a b + 2)
    ((fmKdeg a b).eval degT) (fmK a b T) hK
  have hK1c := S.compl hK1
  have hHyp0 := fmHyp_mem (S := S) (a := a) (b := b)
  have hHyp : fmHyp a b ∈ S.Ω (fmD a b + 8) ((Polynomial.C (6 * a + 14 * b)).eval degT)
      (fmD a b) := by
    simpa only [Polynomial.eval_C] using hHyp0
  have hA1 : fmA1 a b T ∈ S.Ω (F0 + fmFpb a b + fmD a b + 6)
      ((fmKdeg a b + Polynomial.C (6 * a + 14 * b)).eval degT) (fmD a b) := by
    have hraw := Work.WilG1.Omega.inter₂ (S := S) (D := degT)
      (b₁ := fmKdeg a b) (b₂ := Polynomial.C (6 * a + 14 * b))
      (X := (fmK1 a b T)ᶜ) (Y := fmHyp a b) hK1c hHyp
    rw [fmA1]
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ (le_refl _) hraw
    simp only [fmFpb, fmN, fmD, fmE, fmB]
    omega
  have hA2 : fmA2 a b T ∈ S.Ω (F0 + fmFpb a b + fmD a b + 6 + fmB a b + fmE a)
      ((fmKdeg a b + Polynomial.C (6 * a + 14 * b)).eval degT) (fmE a) := by
    rw [fmA2]
    exact Work.WilG0.projLastIter_mem S (fmE a) (fmB a b) (F0 + fmFpb a b + fmD a b + 6)
      ((fmKdeg a b + Polynomial.C (6 * a + 14 * b)).eval degT) (fmA1 a b T) hA1
  have hA2c := S.compl hA2
  have hEta : fmPosEta a ∈ S.Ω (fmE a + 2) ((Polynomial.C 3).eval degT) (fmE a) := by
    simpa only [Polynomial.eval_C] using fmPosEta_mem (S := S) (a := a)
  have hBs : fmBset a b T ∈ S.Ω (F0 + fmFpb a b + fmD a b + 6 + fmB a b + fmE a + 2)
      (((fmKdeg a b + Polynomial.C (6 * a + 14 * b)) + Polynomial.C 3).eval degT)
      (fmE a) := by
    have hraw := Work.WilG1.Omega.inter₂ (S := S) (D := degT)
      (b₁ := fmKdeg a b + Polynomial.C (6 * a + 14 * b)) (b₂ := Polynomial.C 3)
      (X := (fmA2 a b T)ᶜ) (Y := fmPosEta a) hA2c hEta
    rw [fmBset]
    refine Work.WilG0.Omega_mono_FD (S := S) ?_ (le_refl _) hraw
    simp only [fmFpb, fmN, fmD, fmE, fmB]
    omega
  have hPL : WilkiesDesign.projLast (fmBset a b T) ∈
      S.Ω (F0 + fmFpb a b + fmD a b + 6 + fmB a b + fmE a + 3)
        (((fmKdeg a b + Polynomial.C (6 * a + 14 * b)) + Polynomial.C 3).eval degT) (a + 1) :=
    Work.WilG1.Omega.projLast_mem (S := S) hBs
  have hPLc := S.compl hPL
  have hEps : fmPosEps a ∈ S.Ω ((a + 1) + 2) ((Polynomial.C 3).eval degT) (a + 1) := by
    simpa only [Polynomial.eval_C] using fmPosEps_mem (S := S) (a := a)
  have hFin := Work.WilG1.Omega.inter₂ (S := S) (D := degT) (b₁ := Polynomial.C 3)
    (b₂ := (fmKdeg a b + Polynomial.C (6 * a + 14 * b)) + Polynomial.C 3)
    (X := fmPosEps a) (Y := (WilkiesDesign.projLast (fmBset a b T))ᶜ) hEps hPLc
  rw [fmChain]
  refine Work.WilG0.Omega_mono_FD (S := S) ?_ ?_ hFin
  · simp only [fmFpb, fmN, fmD, fmE, fmB]
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      fmKdeg, fmDP, fmN, fmD, fmE, fmB]
    omega


end Work.WilCrux
