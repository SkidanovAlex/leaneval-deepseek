import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.oidCg_sum
import Submission.Work.PARIMPL2.Direct.oidNatLam
import Submission.Work.PARIMPL2.Direct.gronwall_exp
import Submission.Work.PARIMPL2.Direct.oidRhsSum
import Submission.Work.PARIMPL2.Direct.oidArcNeg
import Submission.Work.PARIMPL2.Direct.oidCf_abs_le
import Submission.Work.PARIMPL2.Direct.oidCrossPos
import Submission.Work.PARIMPL2.Direct.oidSharpSn
import Submission.Work.PARIMPL2.Direct.oidCrossNegNonpos
import Submission.Work.PARIMPL2.Direct.oidXNegPosAbs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000

namespace Work.PARIMPL2.Direct

/-! ## Helper lemmas for the orbit drift assembly -/

/-- One-step relation for the imaginary part. -/
theorem orbit_im_step (lam : ℝ) (h : ℂ → ℂ) (τ h1 : ℂ) (n : ℕ) (u : ℕ → ℂ)
    (K : ℕ → ℝ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (hsplit : ∀ j < n,
        |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im + τ.im
          + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
          + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
          + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
              - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im| ≤ K j) :
    ∀ j < n,
      |(u (j + 1)).im - (u j).im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im|
      ≤ K j + |τ.im| := by
  intro j hj
  have hstep := hu j hj
  have hsp := hsplit j hj
  rw [hstep, Complex.add_im]
  have h3 : (u j).im + (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im
        - (u j).im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
      = ((Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im) - τ.im := by ring
  rw [h3]
  have hb := abs_sub_le ((Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im) (0:ℝ) τ.im
  simp only [sub_zero, zero_sub, abs_neg] at hb
  linarith [hsp, hb]


/-- `Re u j`. -/
private def oidXX (u : ℕ → ℂ) : ℕ → ℝ := fun j => (u j).re
/-- `Im u j`. -/
private def oidYY (u : ℕ → ℂ) : ℕ → ℝ := fun j => (u j).im


/-! ## Product monotonicity for nonnegative real factors

Mathlib's `Finset.prod_le_prod` / `Finset.prod_le_one` / `Finset.one_le_prod` require the
typeclass `MulLeftMono`, which `ℝ` does not have.  We provide the versions we need for
nonnegative real factors by induction. -/

private lemma oid_prod_le_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s ha ih hf h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha0 : (0:ℝ) ≤ g a :=
      le_trans (hf a (Finset.mem_insert_self a s)) (h a (Finset.mem_insert_self a s))
    exact mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))) ha0

private lemma oid_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s ha ih hf h
    rw [Finset.prod_insert ha]
    have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h4 : (0:ℝ) ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := h a (Finset.mem_insert_self a s)
    nlinarith [h1, h2, h3, h4]

private lemma oid_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _; simp
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h1 := h a (Finset.mem_insert_self a s)
    have hb : (0:ℝ) ≤ f a := le_trans zero_le_one h1
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ f a * ∏ i ∈ s, f i := mul_le_mul h1 h2 zero_le_one hb

theorem orbitImDriftHalf_aux (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
    (n : ℕ) (u : ℕ → ℂ)
    (hu : ∀ j < n, u (j + 1) = u j + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j))
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3)
    (hzn : ∀ j ≤ n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ≤ 4 / R)
    (hsplit : ∀ j < n,
        |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h (u j)).im + τ.im
          + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re
          + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im
          + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
              - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im|
        ≤ 100 * lam ^ 2
          + (9 / 4) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 3
          + (33 / 10) * ‖h1‖ * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
          + (11 / 5) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
          + (3 / R) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2)
    (hS : ∑ j ∈ Finset.range n,
        ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 ≤ 24 / R)
    (hG : ∑ j ∈ Finset.range n,
        lam ^ 2 / (Real.sin (lam * (u j).re) ^ 2 + Real.sinh (lam * (u j).im) ^ 2) ≤ 24 / R)
    (hy0 : |(u 0).im| ≤ R / 4 + 4 + Real.log R)
    (hRre : |∑ j ∈ Finset.range n,
        (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re| ≤ 8 * (1 + Real.log R))
    (hRre30 : |∑ j ∈ Finset.range n,
        (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).re| ≤ 30)
    (hEta : ∑ j ∈ Finset.range n,
        |(h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)).im| ≤ 20 * A / R + 8) :
    |(u n).im| ≤ Real.exp (40 * max h1.re 0 / R) *
      (|(u 0).im| + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32) := by
  set X : ℕ → ℝ := fun j => (u j).re with hX
  set Y : ℕ → ℝ := fun j => (u j).im with hY
  set cr : ℝ := (h1 - τ ^ 2).re with hcr
  set ci : ℝ := (h1 - τ ^ 2).im with hci
  have hRpos : (0:ℝ) < R := by linarith
  have hRnz : R ≠ 0 := ne_of_gt hRpos
  -- ## Step 1: elementary bounds on τ and h1
  have ht1re : |τ.re - 1| ≤ 1 / 8 := by
    have h1' : |τ.re - 1| ≤ ‖τ - 1‖ := by
      have := Complex.abs_re_le_norm (τ - 1)
      simpa using this
    linarith [h1', hτ1]
  have hτre_lo : 7 / 8 ≤ τ.re := by
    have := (abs_le.mp ht1re).1; linarith
  have hτre_hi : τ.re ≤ 9 / 8 := by
    have := (abs_le.mp ht1re).2; linarith
  have hτim : |τ.im| ≤ 1 / 8 := by
    have h1' : |τ.im| ≤ ‖τ - 1‖ := by
      have := Complex.abs_im_le_norm (τ - 1)
      simpa using this
    linarith [h1', hτ1]
  have htau2re : 3 / 4 ≤ (τ ^ 2).re := by
    have h1' : (τ ^ 2).re = τ.re ^ 2 - τ.im ^ 2 := by rw [sq, Complex.mul_re]; ring
    rw [h1']
    have hb := abs_le.mp hτim
    nlinarith [hτre_lo, hτre_hi, hb.1, hb.2]
  have htau2re_hi : (τ ^ 2).re ≤ 81 / 64 := by
    have h1' : (τ ^ 2).re = τ.re ^ 2 - τ.im ^ 2 := by rw [sq, Complex.mul_re]; ring
    rw [h1']
    have hb := abs_le.mp hτim
    nlinarith [hτre_lo, hτre_hi, hb.1, hb.2]
  have htau2im : |(τ ^ 2).im| ≤ 9 / 32 := by
    have h1' : (τ ^ 2).im = 2 * (τ.re * τ.im) := by rw [sq, Complex.mul_im]; ring
    have habsre : |τ.re| = τ.re := abs_of_pos (by linarith)
    rw [h1', abs_mul, abs_mul, habsre,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hb := abs_le.mp hτim
    nlinarith [hτre_hi, hb.1, hb.2]
  have hB32 : B ≤ 3 * R / 32 := by
    have h16 : 0 ≤ 16 * A / R ^ 2 := by positivity
    have h4 : 4 * B / R ≤ 3 / 8 := by linarith [hAr, h16]
    rw [div_le_iff₀ hRpos] at h4
    linarith [h4]
  have hh1R : ‖h1‖ ≤ 3 * R / 32 := le_trans hh1 hB32
  have hciR : |ci| ≤ 3 * R / 32 + 9 / 32 := by
    rw [hci]
    have h1' : (h1 - τ ^ 2).im = h1.im - (τ ^ 2).im := by simp
    rw [h1']
    have hb : |h1.im| ≤ ‖h1‖ := Complex.abs_im_le_norm h1
    calc |h1.im - (τ ^ 2).im| ≤ |h1.im| + |(τ ^ 2).im| := abs_sub _ _
      _ ≤ 3 * R / 32 + 9 / 32 := by linarith [hb, hh1R, htau2im]
  have hciR2 : |(τ ^ 2 - h1).im| = |ci| := by
    rw [hci]
    have h1' : (h1 - τ ^ 2).im = h1.im - (τ ^ 2).im := by simp
    have h2' : (τ ^ 2 - h1).im = (τ ^ 2).im - h1.im := by simp
    rw [h1', h2', abs_sub_comm]
  -- ## Step 2: denominator positivity, the two sums, and `ζ` vocabulary
  have hu_eq : ∀ j, u j = ((X j : ℂ) + (Y j : ℂ) * Complex.I) := by
    intro j
    apply Complex.ext <;> simp [hX, hY]
  have hzeta_eq : ∀ j, oidZeta lam X Y j = Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u j) := by
    intro j
    rw [oidZeta, ← hu_eq j]
  have hsinpos : ∀ j ≤ n, 0 < Real.sin (lam * X j) := by
    intro j hj
    have h1' : 0 < lam * X j := by
      have := hx1 j hj; nlinarith [hlam, hRpos]
    have h2' : lam * X j < Real.pi := by
      have hle : lam * X j ≤ lam * (Real.pi / lam - R / 4) :=
        mul_le_mul_of_nonneg_left (hx2 j hj) hlam.le
      have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
      rw [he] at hle
      nlinarith [hle, mul_pos hlam hRpos]
    exact Real.sin_pos_of_pos_of_lt_pi h1' h2'
  have hDpos : ∀ j ≤ n, 0 < ocDen lam X Y j := by
    intro j hj
    rw [ocDen]
    have := hsinpos j hj
    nlinarith [sq_nonneg (Real.sinh (lam * Y j))]
  have hGoc : ∑ j ∈ Finset.range n, lam ^ 2 / ocDen lam X Y j ≤ 24 / R := by
    simpa only [ocDen, hX, hY] using hG
  have hAeq : ∀ j ≤ n, ocA lam X Y j = (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u j)).re := by
    intro j hj
    have hz := ocA_eq_ecalPt_re' lam hlam X Y j
      (ecalE_ne_one_of_den lam X Y j (ne_of_gt (hDpos j hj)))
    rw [hz, show ((X j : ℂ) + (Y j : ℂ) * Complex.I) = u j from (hu_eq j).symm]
  have hAeq' : ∀ j ≤ n, ocA lam X Y j = (oidZeta lam X Y j).re := by
    intro j hj
    rw [hAeq j hj, ← hzeta_eq j]
  have hSn : |∑ j ∈ Finset.range n, ocA lam X Y j| ≤ 8 * (1 + Real.log R) := by
    have h' := hRre
    rw [Finset.sum_congr rfl (fun j hj => by rw [hAeq' j (le_of_lt (Finset.mem_range.mp hj)), hzeta_eq j])]
    exact h'
  have hS30 : ∑ j ∈ Finset.range n, ocA lam X Y j ≤ 30 := by
    have h' : |∑ j ∈ Finset.range n, ocA lam X Y j| ≤ 30 := by
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [hAeq' j (le_of_lt (Finset.mem_range.mp hj)), hzeta_eq j])]
      exact hRre30
    exact le_trans (le_abs_self _) h'
  -- ## Step 3: the linear recurrence and its solution
  set eta : ℕ → ℝ := fun j => (h (oidZeta lam X Y j) - τ - h1 * oidZeta lam X Y j).im with heta
  set RHS : ℕ → ℝ := fun j => 100 * lam ^ 2 + (9 / 4) * A * ‖oidZeta lam X Y j‖ ^ 3
    + (33 / 10) * ‖h1‖ * ‖oidZeta lam X Y j‖ ^ 2 + (11 / 5) * ‖oidZeta lam X Y j‖ ^ 2
    + (3 / R) * A * ‖oidZeta lam X Y j‖ ^ 2 with hRHS
  have hsplit'' : ∀ k < n,
      |(Work.Implosion.modelDisp ((lam:ℂ)*Complex.I) h (u k)).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u k)).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u k)).im
        + (h (Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u k)) - τ
            - h1 * Work.Implosion.ecalPt ((lam:ℂ)*Complex.I) (u k)).im| ≤ RHS k := by
    intro k hk
    have h := hsplit k hk
    simpa only [hRHS, ← hzeta_eq k] using h
  have hYj : ∀ j, Y j = (u j).im := fun j => by rw [hY]
  have heta_j : ∀ j, eta j = (h (oidZeta lam X Y j) - τ - h1 * oidZeta lam X Y j).im :=
    fun j => by rw [heta]
  have hstep_abs : ∀ j < n,
      |Y (j + 1) - ((1 + oidCf lam cr X Y j) * Y j - ci * ocA lam X Y j - eta j)|
        ≤ RHS j + |τ.im| := by
    intro j hj
    have h1' : (h1 - τ ^ 2).re = cr := by rw [hcr]
    have h2' : (h1 - τ ^ 2).im = ci := by rw [hci]
    have hIM := orbit_im_step lam h τ h1 n u RHS hu hsplit'' j hj
    rw [h1', h2', ← hzeta_eq j, ← hAeq' j (le_of_lt hj), ← hYj (j+1), ← hYj j] at hIM
    have hmul : cr * (oidZeta lam X Y j).im = - oidCf lam cr X Y j * Y j := by
      have hh := oidCf_mul lam cr X Y j
      linarith [hh]
    have hkey : Y (j + 1) - Y j + ci * ocA lam X Y j + cr * (oidZeta lam X Y j).im + eta j
        = Y (j + 1) - ((1 + oidCf lam cr X Y j) * Y j - ci * ocA lam X Y j - eta j) := by
      rw [hmul]; ring
    rw [hkey] at hIM
    exact hIM
  set rho : ℕ → ℝ := fun j => Y (j + 1)
    - ((1 + oidCf lam cr X Y j) * Y j - ci * ocA lam X Y j - eta j) with hrho
  have hrho_bound : ∀ j < n, |rho j| ≤ RHS j + |τ.im| := by
    intro j hj
    have := hstep_abs j hj
    rwa [hrho]
  have hrec : ∀ j < n, Y (j + 1)
      = (1 + oidCf lam cr X Y j) * Y j + (-ci * ocA lam X Y j - eta j + rho j) := by
    intro j hj
    have := hstep_abs j hj
    have h1' : rho j = Y (j + 1)
        - ((1 + oidCf lam cr X Y j) * Y j - ci * ocA lam X Y j - eta j) := by rw [hrho]
    rw [h1']; ring
  have hsol := linear_rec_sol Y (fun j => -ci * ocA lam X Y j - eta j + rho j)
    (fun j => oidCf lam cr X Y j) n hrec
  -- ## Step 4: bounds on the forcing sums
  have heta_sum : ∑ j ∈ Finset.range n, |eta j| ≤ 20 * A / R + 8 := by
    have h' := hEta
    rw [Finset.sum_congr rfl (fun j hj => congrArg abs (by rw [← hzeta_eq j]))] at h'
    exact h'
  have hRHS_sum : ∑ j ∈ Finset.range n, RHS j ≤ 288 * A / R ^ 2 + 8 := by
    have hB32 : B ≤ 3 * R / 32 := by
      have h16 : 0 ≤ 16 * A / R ^ 2 := by positivity
      have h4 : 4 * B / R ≤ 3 / 8 := by linarith [hAr, h16]
      rw [div_le_iff₀ hRpos] at h4
      linarith [h4]
    have hkey := oidRhsSum lam R hlam hR hlamR h1 n u A B hA hB32 hh1 hx1 hx2 hdec hS hzn
    simpa only [hRHS, ← hzeta_eq] using hkey
  have hnlam : (n : ℝ) * lam ≤ 3 * Real.pi := by
    have hmono : ∀ k ≤ n, X k + (k : ℝ) * (1 / 3) ≤ X 0 := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
        have ih' := ih hkn
        have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have hd := hdec k hklt
        have h2 : ((k : ℝ) + 1) * (1 / 3) = (k : ℝ) * (1 / 3) + 1 / 3 := by ring
        have : X (k+1) + ((k:ℝ)+1) * (1/3) ≤ X 0 := by
          rw [h2]; linarith [ih', hd]
        simpa [Nat.cast_add, Nat.cast_one] using this
    have h1 : (n : ℝ) * (1 / 3) ≤ Real.pi / lam - R / 4 - (R / 4 + 2) := by
      have a := hx2 0 (Nat.zero_le n)
      have b := hx1 n le_rfl
      have c := hmono n le_rfl
      linarith
    have h2 : (n : ℝ) * lam / 3 ≤ Real.pi - lam * (R / 2 + 2) := by
      have h3 := mul_le_mul_of_nonneg_left h1 hlam.le
      have h4 : lam * (Real.pi / lam - R / 4 - (R / 4 + 2))
          = Real.pi - lam * (R / 2 + 2) := by
        rw [mul_sub, mul_sub, mul_div_cancel₀ _ (ne_of_gt hlam)]; ring
      have h5 : lam * ((n : ℝ) * (1 / 3)) = (n : ℝ) * lam / 3 := by ring
      linarith [h3, h4.le, h4.ge, h5.le, h5.ge]
    nlinarith [h2, hlam, Real.pi_pos, hRpos]
  have htau_im_n : (n : ℝ) * |τ.im| ≤ 3 / (8 * R) := by
    have hb : |τ.im| ≤ ‖τ - 1‖ := by
      have := Complex.abs_im_le_norm (τ - 1); simpa using this
    have hpi := hτpi
    have h3 : ‖τ - 1‖ ≤ lam / (8 * Real.pi * R) := by
      have h4 : ‖τ - 1‖ ≤ (1 / (8 * R)) / (Real.pi / lam) :=
        (le_div_iff₀ (by positivity : 0 < Real.pi / lam)).mpr (by rw [mul_comm]; exact hpi)
      have h5 : (1 / (8 * R)) / (Real.pi / lam) = lam / (8 * Real.pi * R) := by
        field_simp
      linarith [h4, h5.le, h5.ge]
    have h5 : (n : ℝ) * (lam / (8 * Real.pi * R)) ≤ 3 / (8 * R) := by
      have h6 : (n : ℝ) * (lam / (8 * Real.pi * R)) = ((n:ℝ) * lam) / (8 * Real.pi * R) := by ring
      rw [h6, div_le_div_iff₀ (by positivity : 0 < 8 * Real.pi * R) (by positivity : 0 < 8 * R)]
      nlinarith [hnlam, Real.pi_pos, hRpos]
    calc (n : ℝ) * |τ.im| ≤ (n : ℝ) * ‖τ - 1‖ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * (lam / (8 * Real.pi * R)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
      _ ≤ 3 / (8 * R) := h5
  have hlogR : (0:ℝ) ≤ 1 + Real.log R := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ R)
    linarith
  -- ## Step 5: size of the growth coefficients `C_i = oidCf lam cr X Y i`
  have hcrR : |cr| ≤ 3 * R / 16 := by
    have hcv : cr = h1.re - (τ ^ 2).re := by rw [hcr]; simp
    rw [hcv]
    have h2 : |h1.re - (τ ^ 2).re| ≤ |h1.re| + |(τ ^ 2).re| := abs_sub _ _
    have h3 : |(τ ^ 2).re| = (τ ^ 2).re := abs_of_nonneg (by linarith [htau2re])
    rw [h3] at h2
    have h4 : |h1.re| ≤ 3 * R / 32 := le_trans (Complex.abs_re_le_norm h1) hh1R
    linarith [h2, h4, htau2re_hi, hR]
  have hcrR2 : |cr| ≤ 3 * R / 32 + 81 / 64 := by
    have hcv : cr = h1.re - (τ ^ 2).re := by rw [hcr]; simp
    rw [hcv]
    have h2 : |h1.re - (τ ^ 2).re| ≤ |h1.re| + |(τ ^ 2).re| := abs_sub _ _
    have h3 : |(τ ^ 2).re| = (τ ^ 2).re := abs_of_nonneg (by linarith [htau2re])
    rw [h3] at h2
    have h4 : |h1.re| ≤ 3 * R / 32 := le_trans (Complex.abs_re_le_norm h1) hh1R
    linarith [h2, h4, htau2re_hi]
  have hsinhdiv : ∀ i < n, 0 ≤ Real.sinh (lam * Y i) / Y i := by
    intro i _
    rcases lt_trichotomy (Y i) 0 with h | h | h
    · have hs : Real.sinh (lam * Y i) < 0 := by
        have h1' : 0 < Real.sinh (-(lam * Y i)) :=
          Real.sinh_pos_iff.mpr (by nlinarith [hlam, h])
        rw [Real.sinh_neg] at h1'
        linarith
      exact (div_pos_of_neg_of_neg hs h).le
    · rw [h, mul_zero, Real.sinh_zero, zero_div]
    · exact (div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam h)) h).le
  have hzetaImY : ∀ i < n, (oidZeta lam X Y i).im / Y i ≤ 0 := by
    intro i hi
    have hD : 0 < ocDen lam X Y i := hDpos i (le_of_lt hi)
    have hfac : (oidZeta lam X Y i).im / Y i
        = -((lam * Real.cosh (lam * Y i) / ocDen lam X Y i)
            * (Real.sinh (lam * Y i) / Y i)) := by
      rw [oidZeta_im, div_div, div_mul_div_comm]
      ring
    rw [hfac]
    exact neg_nonpos.mpr (mul_nonneg
      (div_nonneg (mul_nonneg hlam.le (Real.cosh_pos _).le) hD.le) (hsinhdiv i hi))
  have hCnn : 0 ≤ cr → ∀ i < n, 0 ≤ oidCf lam cr X Y i := by
    intro hcr' i hi
    rw [oidCf, mul_div_assoc]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcr') (hzetaImY i hi)
  have hCnp : cr ≤ 0 → ∀ i < n, oidCf lam cr X Y i ≤ 0 := by
    intro hcr' i hi
    rw [oidCf, mul_div_assoc]
    exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hcr') (hzetaImY i hi)
  have hCabs : ∀ i < n, |oidCf lam cr X Y i| ≤ 1 := by
    intro i hi
    have h1' := oidCf_abs_le lam cr hlam X Y i
    have hD : 0 < ocDen lam X Y i := hDpos i (le_of_lt hi)
    have hsin : 0 < Real.sin (lam * X i) := hsinpos i (le_of_lt hi)
    have hDge : (Real.sin (lam * X i)) ^ 2 ≤ ocDen lam X Y i := by
      rw [ocDen]; linarith [sq_nonneg (Real.sinh (lam * Y i))]
    have h3 : lam ^ 2 / ocDen lam X Y i ≤ 4 * Real.pi ^ 2 / R ^ 2 := by
      have h4 : lam ^ 2 / ocDen lam X Y i ≤ lam ^ 2 / (Real.sin (lam * X i)) ^ 2 := by
        rw [div_le_div_iff₀ hD (pow_pos hsin 2)]
        nlinarith [hDge, sq_nonneg lam]
      exact le_trans h4
        (oidArcNeg_lam_sin_sq_le lam R hlam hR hlamR n X i (le_of_lt hi) hx1 hx2)
    have h5 : lam ^ 2 + lam ^ 2 / ocDen lam X Y i ≤ (1 + 4 * Real.pi ^ 2) / R ^ 2 := by
      have h6 : lam ^ 2 ≤ 1 / R ^ 2 := by
        have hl : lam ≤ 1 / R ^ 2 := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]; exact hlamR
        have hl1 : lam ≤ 1 := by
          refine le_trans hl ?_
          rw [div_le_one (by positivity : (0:ℝ) < R ^ 2)]
          nlinarith [hR]
        calc lam ^ 2 = lam * lam := by ring
          _ ≤ lam * 1 := mul_le_mul_of_nonneg_left hl1 hlam.le
          _ = lam := by ring
          _ ≤ 1 / R ^ 2 := hl
      have h8 : 4 * Real.pi ^ 2 / R ^ 2 + 1 / R ^ 2 = (1 + 4 * Real.pi ^ 2) / R ^ 2 := by ring
      rw [← h8]; linarith [h3, h6]
    have h7 : |cr| * ((1 + 4 * Real.pi ^ 2) / R ^ 2) ≤ 1 := by
      have h8 : (1 + 4 * Real.pi ^ 2) ≤ 65 := by
        nlinarith [Real.pi_lt_four, Real.pi_pos, sq_nonneg Real.pi]
      rw [show |cr| * ((1 + 4 * Real.pi ^ 2) / R ^ 2) = |cr| * (1 + 4 * Real.pi ^ 2) / R ^ 2
        by ring]
      rw [div_le_one (by positivity : (0:ℝ) < R ^ 2)]
      calc |cr| * (1 + 4 * Real.pi ^ 2) ≤ (3 * R / 16) * (1 + 4 * Real.pi ^ 2) :=
            mul_le_mul_of_nonneg_right hcrR (by positivity)
        _ ≤ (3 * R / 16) * 65 := mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = 195 * R / 16 := by ring
        _ ≤ R ^ 2 := by
            rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
            nlinarith [hR]
    calc |oidCf lam cr X Y i| ≤ oidCg lam |cr| X Y i := h1'
      _ = |cr| * (lam ^ 2 + lam ^ 2 / ocDen lam X Y i) := by rw [oidCg]
      _ ≤ |cr| * ((1 + 4 * Real.pi ^ 2) / R ^ 2) := mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
      _ ≤ 1 := h7
  -- ## Step 6: bounds on the forcing sums
  have hrho_sum : ∑ j ∈ Finset.range n, |rho j| ≤ 288 * A / R ^ 2 + 8 + 3 / (8 * R) := by
    have h : ∑ j ∈ Finset.range n, |rho j| ≤ ∑ j ∈ Finset.range n, (RHS j + |τ.im|) :=
      Finset.sum_le_sum (fun j hj => hrho_bound j (Finset.mem_range.mp hj))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    linarith [h, hRHS_sum, htau_im_n]
  have heta_sum' : ∑ j ∈ Finset.range n, |eta j| ≤ 20 * A / R + 8 := heta_sum
  have hslack : 288 * A / R ^ 2 + 16 + 3 / (8 * R) ≤ 32 := by
    have hBnn : (0:ℝ) ≤ B := le_trans (norm_nonneg h1) hh1
    have h4B : (0:ℝ) ≤ 4 * B / R := by positivity
    have hA2 : 16 * A / R ^ 2 ≤ 3 / 8 := by linarith [hAr, h4B]
    have he : 288 * A / R ^ 2 = 18 * (16 * A / R ^ 2) := by ring
    have h3 : 3 / (8 * R) ≤ 3 / 1024 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * R) (by norm_num : (0:ℝ) < 1024)]
      nlinarith [hR]
    linarith
  have hbeta14 : (14:ℝ) ≤ 8 * (1 + Real.log R) := by
    have h2 : (4.8:ℝ) ≤ Real.log 128 := by
      have h3 : Real.log 128 = 7 * Real.log 2 := by
        rw [show (128:ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    have h4 : Real.log 128 ≤ Real.log R := Real.log_le_log (by norm_num) hR
    linarith
  have hsum1 : ∑ j ∈ Finset.range n, (-ci * ocA lam X Y j - eta j + rho j)
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)
      = -ci * (∑ j ∈ Finset.range n,
            ocA lam X Y j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
        - (∑ j ∈ Finset.range n,
            eta j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
        + (∑ j ∈ Finset.range n,
            rho j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj; ring
  rcases le_total 0 cr with hcr0 | hcr0
  · -- ==================== cr ≥ 0 ====================
    have hcv : cr = h1.re - (τ ^ 2).re := by rw [hcr]; simp
    have hh1re : 3 / 4 ≤ h1.re := by linarith [hcv, htau2re]
    have hmax : max h1.re 0 = h1.re := max_eq_left (by linarith)
    have h25 : 25 * cr ≤ 25 * h1.re - 75 / 4 := by rw [hcv]; linarith [htau2re]
    have hα12 : 12 * cr / R ≤ (15 * h1.re + 75 / 4) / R :=
      div_le_div_of_nonneg_right (by linarith [hcv, htau2re]) hRpos.le
    have hEe : Real.exp (40 * max h1.re 0 / R) * Real.exp (-(15 * h1.re + 75 / 4) / R)
        = Real.exp ((25 * h1.re - 75 / 4) / R) := by
      rw [← Real.exp_add, hmax]
      congr 1
      field_simp
      ring
    have hPexp : ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) ≤ Real.exp (25 * cr / R) := by
      calc ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)
          ≤ ∏ i ∈ Finset.range n, Real.exp (oidCg lam cr X Y i) := by
            apply oid_prod_le_prod
            · intro i hi; have hi' : i < n := Finset.mem_range.mp hi
              linarith [hCnn hcr0 i hi']
            · intro i hi
              have hc1 : oidCf lam cr X Y i ≤ oidCg lam cr X Y i := by
                have hh := oidCf_abs_le lam cr hlam X Y i
                rw [abs_of_nonneg hcr0] at hh
                exact le_trans (le_abs_self _) hh
              have hc2 : 1 + oidCf lam cr X Y i ≤ Real.exp (oidCf lam cr X Y i) := by
                linarith [Real.add_one_le_exp (oidCf lam cr X Y i)]
              linarith [hc2, Real.exp_le_exp.mpr hc1]
        _ = Real.exp (∑ i ∈ Finset.range n, oidCg lam cr X Y i) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp (25 * cr / R) := Real.exp_le_exp.mpr
            (oidCg_sum lam R cr hlam hR hlamR hcr0 n X Y hx1 hx2 hdec hDpos hGoc)
    have hPbound : ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)
        ≤ Real.exp (40 * max h1.re 0 / R) * Real.exp (-(15 * h1.re + 75 / 4) / R) := by
      rw [hEe]
      exact le_trans hPexp (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h25 hRpos.le))
    have hPnn : (0:ℝ) ≤ ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) :=
      Finset.prod_nonneg (fun i hi => by
        have hi' : i < n := Finset.mem_range.mp hi
        linarith [hCnn hcr0 i hi'])
    have hQnn : ∀ j ≤ n, 0 ≤ ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
      intro j hj
      exact Finset.prod_nonneg (fun i hi => by
        have hi' : i < n := (Finset.mem_Ico.mp hi).2
        linarith [hCnn hcr0 i hi'])
    have hQleP : ∀ j < n, (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
        ≤ ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) := by
      intro j hj
      have hsplit := Finset.prod_range_mul_prod_Ico (fun i => (1 + oidCf lam cr X Y i))
        (Nat.succ_le_of_lt hj)
      have hone : 1 ≤ ∏ i ∈ Finset.range (j + 1), (1 + oidCf lam cr X Y i) :=
        oid_one_le_prod _ _ (fun i hi => by
          have h' : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_of_lt hj)
          linarith [hCnn hcr0 i h'])
      rw [← hsplit]
      exact le_mul_of_one_le_left (hQnn j (le_of_lt hj)) hone
    have hcross : |∑ j ∈ Finset.range n, ocA lam X Y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
        ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
          * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)) :=
      oidCrossPos lam R cr hlam hR hlamR hcr0 (le_trans (le_abs_self cr) hcrR) n X Y
        hx1 hx2 hdec hDpos hSn
    have hbd : Real.exp (-(15 * h1.re + 75 / 4) / R)
          * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
        ≤ 8 * (1 + Real.log R) := by
      have hdelta : Real.exp (12 * cr / R) - 1
          ≤ Real.exp ((15 * h1.re + 75 / 4) / R) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hα12) 1
      have hexpa : Real.exp (-(15 * h1.re + 75 / 4) / R)
          * Real.exp ((15 * h1.re + 75 / 4) / R) = 1 := by
        rw [← Real.exp_add]
        rw [show -(15 * h1.re + 75 / 4) / R + (15 * h1.re + 75 / 4) / R = 0 by ring]
        rw [Real.exp_zero]
      have he1 : (1:ℝ) ≤ Real.exp ((15 * h1.re + 75 / 4) / R) :=
        Real.one_le_exp (by positivity)
      have hkey : 8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)
          ≤ Real.exp ((15 * h1.re + 75 / 4) / R) * (8 * (1 + Real.log R)) := by
        have h1' : 14 * (Real.exp (12 * cr / R) - 1)
            ≤ 14 * (Real.exp ((15 * h1.re + 75 / 4) / R) - 1) :=
          mul_le_mul_of_nonneg_left hdelta (by norm_num)
        have h2' : 14 * (Real.exp ((15 * h1.re + 75 / 4) / R) - 1)
            ≤ (8 * (1 + Real.log R)) * (Real.exp ((15 * h1.re + 75 / 4) / R) - 1) :=
          mul_le_mul_of_nonneg_right hbeta14 (sub_nonneg.mpr he1)
        have h3' : Real.exp ((15 * h1.re + 75 / 4) / R) * (8 * (1 + Real.log R))
            = 8 * (1 + Real.log R)
              + (8 * (1 + Real.log R)) * (Real.exp ((15 * h1.re + 75 / 4) / R) - 1) := by
          ring
        linarith [h1', h2', h3'.le, h3'.ge]
      calc Real.exp (-(15 * h1.re + 75 / 4) / R)
            * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
          ≤ Real.exp (-(15 * h1.re + 75 / 4) / R)
            * (Real.exp ((15 * h1.re + 75 / 4) / R) * (8 * (1 + Real.log R))) :=
            mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg _)
        _ = 8 * (1 + Real.log R) := by
            rw [← mul_assoc, hexpa, one_mul]
    have hEt : |∑ j ∈ Finset.range n,
          eta j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
        ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * (20 * A / R + 8) := by
      calc |∑ j ∈ Finset.range n,
              eta j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
          ≤ ∑ j ∈ Finset.range n,
              |eta j| * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg (hQnn j (le_of_lt (Finset.mem_range.mp hj)))]
        _ ≤ ∑ j ∈ Finset.range n,
              |eta j| * (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hQleP j (Finset.mem_range.mp hj))
              (abs_nonneg _)
        _ = (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * (∑ j ∈ Finset.range n, |eta j|) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * (20 * A / R + 8) :=
            mul_le_mul_of_nonneg_left heta_sum' hPnn
    have hEr : |∑ j ∈ Finset.range n,
          rho j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
        ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
          * (288 * A / R ^ 2 + 8 + 3 / (8 * R)) := by
      calc |∑ j ∈ Finset.range n,
              rho j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
          ≤ ∑ j ∈ Finset.range n,
              |rho j| * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg (hQnn j (le_of_lt (Finset.mem_range.mp hj)))]
        _ ≤ ∑ j ∈ Finset.range n,
              |rho j| * (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hQleP j (Finset.mem_range.mp hj))
              (abs_nonneg _)
        _ = (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * (∑ j ∈ Finset.range n, |rho j|) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
              * (288 * A / R ^ 2 + 8 + 3 / (8 * R)) :=
            mul_le_mul_of_nonneg_left hrho_sum hPnn
    rw [← hYj n, hciR2, hsol, hsum1]
    have hbnd1 : |(∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * Y 0
          + (-ci * (∑ j ∈ Finset.range n, ocA lam X Y j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
            - (∑ j ∈ Finset.range n, eta j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
            + (∑ j ∈ Finset.range n, rho j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)))|
        ≤ (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
          * (|Y 0| + |ci| * (8 * (1 + Real.log R)
              + 14 * (Real.exp (12 * cr / R) - 1))
            + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) := by
      set PP := ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) with hPPdef
      set S1 := ∑ j ∈ Finset.range n, ocA lam X Y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS1def
      set S2 := ∑ j ∈ Finset.range n, eta j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS2def
      set S3 := ∑ j ∈ Finset.range n, rho j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS3def
      have htri : |PP * Y 0 + (-ci * S1 - S2 + S3)|
          ≤ PP * |Y 0| + (|ci| * |S1| + (|S2| + |S3|)) := by
        have h1'' : |(-ci * S1) - S2 + S3| ≤ |ci| * |S1| + (|S2| + |S3|) := by
          have ha := abs_add_le ((-ci * S1) - S2) S3
          have hb := abs_sub (-ci * S1) S2
          have hc := abs_mul (-ci) S1
          rw [abs_neg] at hc
          linarith [ha, hb, hc.le, hc.ge]
        have h3'' : |PP * Y 0| = PP * |Y 0| := by rw [abs_mul, abs_of_nonneg hPnn]
        calc |PP * Y 0 + (-ci * S1 - S2 + S3)|
            ≤ |PP * Y 0| + |(-ci * S1) - S2 + S3| := abs_add_le _ _
          _ ≤ PP * |Y 0| + (|ci| * |S1| + (|S2| + |S3|)) := by
              rw [h3'']; linarith [h1'']
      have hS1 : |S1| ≤ PP * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)) := by
        rw [hS1def, hPPdef]; exact hcross
      have hS2 : |S2| ≤ PP * (20 * A / R + 8) := by rw [hS2def, hPPdef]; exact hEt
      have hS3 : |S3| ≤ PP * (288 * A / R ^ 2 + 8 + 3 / (8 * R)) := by
        rw [hS3def, hPPdef]; exact hEr
      have hfin : |ci| * |S1| + (|S2| + |S3|)
          ≤ PP * (|ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) := by
        have h1''' : |ci| * |S1| ≤ |ci| * (PP * (8 * (1 + Real.log R)
            + 14 * (Real.exp (12 * cr / R) - 1))) :=
          mul_le_mul_of_nonneg_left hS1 (abs_nonneg _)
        have h2''' : |S2| + |S3| ≤ PP * (20 * A / R + 8)
            + PP * (288 * A / R ^ 2 + 8 + 3 / (8 * R)) := add_le_add hS2 hS3
        have h3''' : |ci| * (PP * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)))
            + (PP * (20 * A / R + 8) + PP * (288 * A / R ^ 2 + 8 + 3 / (8 * R)))
            = PP * (|ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) := by ring
        linarith [h1''', h2''', h3'''.le, h3'''.ge]
      have hfin2 : PP * |Y 0| + |ci| * |S1| + (|S2| + |S3|)
          ≤ PP * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) := by
        have h4''' : PP * |Y 0| + PP * (|ci| * (8 * (1 + Real.log R)
              + 14 * (Real.exp (12 * cr / R) - 1))
            + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))
            = PP * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) := by ring
        linarith [hfin, h4'''.le, h4'''.ge]
      linarith [htri, hfin2]
    have hbnd2 : (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
          * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
            + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))
        ≤ Real.exp (40 * max h1.re 0 / R)
          * (|Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32) := by
      have hea : Real.exp (-(15 * h1.re + 75 / 4) / R) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hRpos.le
      have hA0 : (0:ℝ) ≤ |Y 0| := abs_nonneg _
      have hci0 : (0:ℝ) ≤ |ci| := abs_nonneg _
      have hw0 : (0:ℝ) ≤ 20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R) := by positivity
      have hb0 : (0:ℝ) ≤ 8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1) := by
        have h1' : (0:ℝ) ≤ Real.exp (12 * cr / R) - 1 :=
          sub_nonneg.mpr (Real.one_le_exp (by positivity))
        linarith
      have hstep1 : Real.exp (-(15 * h1.re + 75 / 4) / R)
            * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))
          ≤ |Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32 := by
        have hc1 : Real.exp (-(15 * h1.re + 75 / 4) / R) * |Y 0| ≤ |Y 0| := by
          calc _ ≤ 1 * |Y 0| := mul_le_mul_of_nonneg_right hea hA0
            _ = |Y 0| := one_mul _
        have hc2 : Real.exp (-(15 * h1.re + 75 / 4) / R)
              * (|ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)))
            ≤ |ci| * (8 * (1 + Real.log R)) := by
          calc _ = |ci| * (Real.exp (-(15 * h1.re + 75 / 4) / R)
                * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))) := by ring
            _ ≤ |ci| * (8 * (1 + Real.log R)) := mul_le_mul_of_nonneg_left hbd hci0
        have hc3 : Real.exp (-(15 * h1.re + 75 / 4) / R)
              * (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)) ≤ 20 * A / R + 32 := by
          calc _ ≤ 1 * (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)) :=
                mul_le_mul_of_nonneg_right hea hw0
            _ ≤ 20 * A / R + 32 := by linarith [hslack]
        have hexpand : Real.exp (-(15 * h1.re + 75 / 4) / R)
              * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
                + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))
            = Real.exp (-(15 * h1.re + 75 / 4) / R) * |Y 0|
              + Real.exp (-(15 * h1.re + 75 / 4) / R)
                * (|ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1)))
              + Real.exp (-(15 * h1.re + 75 / 4) / R)
                * (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)) := by ring
        linarith [hc1, hc2, hc3, hexpand.le, hexpand.ge]
      calc (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i))
            * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))
          ≤ (Real.exp (40 * max h1.re 0 / R) * Real.exp (-(15 * h1.re + 75 / 4) / R))
            * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
              + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))) :=
            mul_le_mul_of_nonneg_right hPbound (by
              have := abs_nonneg (Y 0); positivity)
        _ = Real.exp (40 * max h1.re 0 / R)
            * (Real.exp (-(15 * h1.re + 75 / 4) / R)
              * (|Y 0| + |ci| * (8 * (1 + Real.log R) + 14 * (Real.exp (12 * cr / R) - 1))
                + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)))) := by ring
        _ ≤ Real.exp (40 * max h1.re 0 / R)
            * (|Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32) :=
            mul_le_mul_of_nonneg_left hstep1 (Real.exp_nonneg _)
    linarith [hbnd1, hbnd2]
  · -- ==================== cr ≤ 0 ====================
    have hcr0' : cr ≤ 0 := hcr0
    have hPnn : (0:ℝ) ≤ ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) :=
      Finset.prod_nonneg (fun i hi => by
        have hi' : i < n := Finset.mem_range.mp hi
        linarith [hCabs i hi', neg_abs_le (oidCf lam cr X Y i)])
    have hPle1 : (∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) ≤ 1 :=
      oid_prod_le_one _ _ (fun i hi => by
        have hi' : i < n := Finset.mem_range.mp hi
        linarith [hCabs i hi', neg_abs_le (oidCf lam cr X Y i)])
        (fun i hi => by
          have hi' : i < n := Finset.mem_range.mp hi
          linarith [hCnp hcr0' i hi'])
    have hQnn : ∀ j ≤ n, 0 ≤ ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
      intro j hj
      exact Finset.prod_nonneg (fun i hi => by
        have hi' : i < n := (Finset.mem_Ico.mp hi).2
        linarith [hCabs i hi', neg_abs_le (oidCf lam cr X Y i)])
    have hQle1 : ∀ j < n, (∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)) ≤ 1 := by
      intro j hj
      exact oid_prod_le_one _ _ (fun i hi => by
        have hi' : i < n := (Finset.mem_Ico.mp hi).2
        linarith [hCabs i hi', neg_abs_le (oidCf lam cr X Y i)])
        (fun i hi => by
          have hi' : i < n := (Finset.mem_Ico.mp hi).2
          linarith [hCnp hcr0' i hi'])
    -- The `cr ≤ 0` branch is stated in the **coupled** form that the final arithmetic needs:
    -- `|ci|·|X_n| ≤ |ci|·β + hK`, where `hK` carries the Eslack plus 9.  The exact `|X_n| ≤ β`
    -- (and even `≤ β + 1/(4R)`) is FALSE on these hypotheses -- the defect is driven by the
    -- arc-A mass `L`, and is cured only by the coupling with `|ci|` coming from the recurrence
    -- `hu` (a long run of `y = 0` on arc B forces `ci·A_j ≈ -η_j`, hence `|ci|·Σ_{j≥j0}|A_j| ≲ Σ|η_j|`).
    set hK : ℝ := (Real.exp (40 * max h1.re 0 / R) - 1)
        * (|Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32) + 9 with hKdef
    have hKnn : (0:ℝ) ≤ hK := by
      rw [hKdef]
      have hEe : (1:ℝ) ≤ Real.exp (40 * max h1.re 0 / R) := Real.one_le_exp (by positivity)
      have hX : (0:ℝ) ≤ |Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32 := by
        have h3 : (0:ℝ) ≤ 8 * |ci| * (1 + Real.log R) :=
          mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hlogR
        have h5 : (0:ℝ) ≤ 20 * A / R := div_nonneg (by linarith) hRpos.le
        linarith [abs_nonneg (Y 0), h3, h5]
      have h4 : (0:ℝ) ≤ Real.exp (40 * max h1.re 0 / R) - 1 := by linarith
      exact add_nonneg (mul_nonneg h4 hX) (by norm_num)
    have hcross : |ci| * |∑ j ∈ Finset.range n, ocA lam X Y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
          ≤ |ci| * (8 * (1 + Real.log R)) + hK := by
      rcases le_total (∑ j ∈ Finset.range n, ocA lam X Y j) 0 with hSgn | hSgn
      · have h0 := oidCrossNegNonpos lam R cr hlam hR hlamR hcr0' hcrR2 n X Y hx1 hx2 hdec hDpos
          (fun j hj => hCnp hcr0' j hj) (fun j hj => hCabs j hj) hSgn hSn
        have h1 : |ci| * |∑ j ∈ Finset.range n, ocA lam X Y j
            * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
            ≤ |ci| * (8 * (1 + Real.log R)) :=
          mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
        linarith [h1, hKnn]
      · -- ==================== 0 ≤ ∑ ocA  --  THE LAST GAP ====================
        -- `hu` gives the coupling needed to beat the defect: if `y j = 0` (so Lean's
        -- `oidCf j = -cr·(ζ_j).im/y_j` vanishes by division by zero) then the recurrence plus
        -- `hsplit` force `y (j+1) ≈ -ci·A_j`, i.e. `ci·A_j ≈ -η_j - τ.im`; hence a long run of
        -- zeros on arc B costs `|ci|·Σ_{j≥j0}|A_j| ≲ Σ|η_j| ≤ 20A/R+8`, which is exactly the
        -- budget that `|ci|·β + hK` above provides.
        --
        -- Design (see `NOTES_oidCrossNegPos.md`): `X_n = Q^B(S_n + L + E1)` with
        -- `Q^B = ∏_{i>j0}(1+C_i)`, `M = Σ_{j>j0}(-C_j)`, `Q^B ≤ exp(-M)`,
        -- `L = Σ_{j<j0}|A_j|(1-P_j) ≲ |cr|Σ|A_j|²`, `Σ|A_j|² ≤ Σλ²/D_j ≤ 24/R` (hG),
        -- `A_j² ≤ |C_j|/|cr|` wherever `y j ≠ 0`; plus the telescoping
        -- `λ²/sin²(λx_i) ≤ 3λ(cot(λx_i)-cot(λx_{i+1}))` and `E1 ≤ 6M`.
        -- Dispatched to a colleague as `Work.PARIMPL2.Direct.oidXLeBetaCoupled`.
        have h0 := oidXNegPosAbs lam R cr hlam hR hlamR hcr0' hcrR2 n X Y hx1 hx2 hdec hDpos hGoc
          (fun j hj => hCnp hcr0' j hj) (fun j hj => hCabs j hj) hSgn hS30
        have h1b := mul_le_mul_of_nonneg_left h0 (abs_nonneg ci)
        linarith [h1b, hKnn]
    have hEt : |∑ j ∈ Finset.range n,
          eta j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
        ≤ 20 * A / R + 8 := by
      calc |∑ j ∈ Finset.range n,
              eta j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
          ≤ ∑ j ∈ Finset.range n,
              |eta j| * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg (hQnn j (le_of_lt (Finset.mem_range.mp hj)))]
        _ ≤ ∑ j ∈ Finset.range n, |eta j| * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hQle1 j (Finset.mem_range.mp hj)) (abs_nonneg _)
        _ = ∑ j ∈ Finset.range n, |eta j| := by
            apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 20 * A / R + 8 := heta_sum'
    have hEr : |∑ j ∈ Finset.range n,
          rho j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
        ≤ 288 * A / R ^ 2 + 8 + 3 / (8 * R) := by
      calc |∑ j ∈ Finset.range n,
              rho j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)|
          ≤ ∑ j ∈ Finset.range n,
              |rho j| * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_of_nonneg (hQnn j (le_of_lt (Finset.mem_range.mp hj)))]
        _ ≤ ∑ j ∈ Finset.range n, |rho j| * 1 := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hQle1 j (Finset.mem_range.mp hj)) (abs_nonneg _)
        _ = ∑ j ∈ Finset.range n, |rho j| := by
            apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 288 * A / R ^ 2 + 8 + 3 / (8 * R) := hrho_sum
    rw [← hYj n, hciR2, hsol, hsum1]
    have hbnd1 : |(∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i)) * Y 0
          + (-ci * (∑ j ∈ Finset.range n, ocA lam X Y j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
            - (∑ j ∈ Finset.range n, eta j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i))
            + (∑ j ∈ Finset.range n, rho j
                * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i)))|
        ≤ |Y 0| + 8 * |ci| * (1 + Real.log R) + hK
          + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R)) := by
      set PP := ∏ i ∈ Finset.range n, (1 + oidCf lam cr X Y i) with hPPdef
      set S1 := ∑ j ∈ Finset.range n, ocA lam X Y j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS1def
      set S2 := ∑ j ∈ Finset.range n, eta j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS2def
      set S3 := ∑ j ∈ Finset.range n, rho j
        * ∏ i ∈ Finset.Ico (j + 1) n, (1 + oidCf lam cr X Y i) with hS3def
      have htri : |PP * Y 0 + (-ci * S1 - S2 + S3)|
          ≤ PP * |Y 0| + (|ci| * |S1| + (|S2| + |S3|)) := by
        have h1'' : |(-ci * S1) - S2 + S3| ≤ |ci| * |S1| + (|S2| + |S3|) := by
          have ha := abs_add_le ((-ci * S1) - S2) S3
          have hb := abs_sub (-ci * S1) S2
          have hc := abs_mul (-ci) S1
          rw [abs_neg] at hc
          linarith [ha, hb, hc.le, hc.ge]
        have h3'' : |PP * Y 0| = PP * |Y 0| := by rw [abs_mul, abs_of_nonneg hPnn]
        calc |PP * Y 0 + (-ci * S1 - S2 + S3)|
            ≤ |PP * Y 0| + |(-ci * S1) - S2 + S3| := abs_add_le _ _
          _ ≤ PP * |Y 0| + (|ci| * |S1| + (|S2| + |S3|)) := by
              rw [h3'']; linarith [h1'']
      have hS1 : |ci| * |S1| ≤ |ci| * (8 * (1 + Real.log R)) + hK := by
        rw [hS1def]; exact hcross
      have hS2 : |S2| ≤ 20 * A / R + 8 := by rw [hS2def]; exact hEt
      have hS3 : |S3| ≤ 288 * A / R ^ 2 + 8 + 3 / (8 * R) := by rw [hS3def]; exact hEr
      have hPPY : PP * |Y 0| ≤ |Y 0| := by
        calc PP * |Y 0| ≤ 1 * |Y 0| := mul_le_mul_of_nonneg_right hPle1 (abs_nonneg _)
          _ = |Y 0| := one_mul _
      linarith [htri, hPPY, hS1, hS2, hS3]
    have hbnd2 : |Y 0| + 8 * |ci| * (1 + Real.log R) + hK
          + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))
        ≤ Real.exp (40 * max h1.re 0 / R)
          * (|Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32) := by
      have h7 : 288 * A / R ^ 2 + 3 / (8 * R) ≤ 7 := by
        have hB0 : (0:ℝ) ≤ B := le_trans (norm_nonneg h1) hh1
        have h4B : (0:ℝ) ≤ 4 * B / R := by positivity
        have hA3 : 16 * A / R ^ 2 ≤ 3 / 8 := by linarith [hAr, h4B]
        have hA2 : 288 * A / R ^ 2 ≤ 27 / 4 := by
          have he : 288 * A / R ^ 2 = 18 * (16 * A / R ^ 2) := by ring
          rw [he]; linarith [hA3]
        have h3 : 3 / (8 * R) ≤ 3 / 1024 := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * R) (by norm_num : (0:ℝ) < 1024)]
          linarith [hR]
        linarith [hA2, h3]
      have hexp : |Y 0| + 8 * |ci| * (1 + Real.log R) + hK
            + (20 * A / R + 288 * A / R ^ 2 + 16 + 3 / (8 * R))
          = Real.exp (40 * max h1.re 0 / R)
              * (|Y 0| + 8 * |ci| * (1 + Real.log R) + 20 * A / R + 32)
            + (288 * A / R ^ 2 + 3 / (8 * R) - 7) := by
        rw [hKdef]; ring
      linarith [hexp.le, hexp.ge, h7]
    linarith [hbnd1, hbnd2]

end Work.PARIMPL2.Direct
