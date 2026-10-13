import Mathlib
import Submission.Work.WilCrux.SliceCauchyBig
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG5.Basic

set_option autoImplicit false

namespace Work.WilCrux.SCBig

open WilkiesDesign

/-- The set where a single coordinate is nonzero is `Ω`-definable: it is the complement of the
hyperplane `x i = 0` (`Work.WilG1.Omega.hyp_mem` with the linear polynomial `X i`). -/
theorem coordNe_mem (S : SOMin) {n : ℕ} (D : ℕ) (i : Fin n) :
    {x : Fin n → ℝ | x i ≠ 0} ∈ S.Ω (n + 1) ((Polynomial.C 1).eval D) n := by
  have h := Work.WilG1.Omega.hyp_mem (S := S) D (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
  have hset : {x : Fin n → ℝ |
      MvPolynomial.eval x (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) = 0}
      = {x : Fin n → ℝ | x i = 0} := by
    ext x; simp
  rw [hset] at h
  have h' : {x : Fin n → ℝ | x i = 0} ∈ S.Ω n ((Polynomial.C 1).eval D) n :=
    Work.WilG1.Omega.mono h le_rfl (by simp [MvPolynomial.totalDegree_X])
  have hc := Work.WilG1.Omega.compl_mem h'
  have hset2 : ({x : Fin n → ℝ | x i = 0}ᶜ) = {x : Fin n → ℝ | x i ≠ 0} := by
    ext x; simp
  rwa [hset2] at hc

/-- The set `{x | |x i| < x e}` is `Ω`-definable: `|x i| < x e ↔ 0 < x e - x i ∧ 0 < x e + x i`,
an intersection of two positivity sets of linear polynomials (`Work.WilG1.Calc.pos_mem`). -/
theorem absLtCoord_mem (S : SOMin) {n : ℕ} (D : ℕ) (i e : Fin n) :
    {x : Fin n → ℝ | |x i| < x e} ∈ S.Ω (n + 3) ((Polynomial.C 6).eval D) n := by
  have htd1 : ((MvPolynomial.X e - MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have htd2 : ((MvPolynomial.X e + MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have h1 := Work.WilG1.Calc.pos_mem (S := S) D
    (MvPolynomial.X e - MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
  have h2 := Work.WilG1.Calc.pos_mem (S := S) D
    (MvPolynomial.X e + MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
  have h1' : {x : Fin n → ℝ | 0 < x e - x i} ∈ S.Ω (n + 2) ((Polynomial.C 3).eval D) n := by
    have heq : {x : Fin n → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.X e - MvPolynomial.X i : MvPolynomial (Fin n) ℝ)}
        = {x : Fin n → ℝ | 0 < x e - x i} := by
      ext x; simp
    rw [heq] at h1
    refine Work.WilG1.Omega.mono h1 le_rfl ?_
    simp only [Polynomial.eval_C]
    omega
  have h2' : {x : Fin n → ℝ | 0 < x e + x i} ∈ S.Ω (n + 2) ((Polynomial.C 3).eval D) n := by
    have heq : {x : Fin n → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.X e + MvPolynomial.X i : MvPolynomial (Fin n) ℝ)}
        = {x : Fin n → ℝ | 0 < x e + x i} := by
      ext x; simp
    rw [heq] at h2
    refine Work.WilG1.Omega.mono h2 le_rfl ?_
    simp only [Polynomial.eval_C]
    omega
  have h := Work.WilG1.Omega.inter₂ h1' h2'
  have hset : {x : Fin n → ℝ | |x i| < x e}
      = {x : Fin n → ℝ | 0 < x e - x i} ∩ {x : Fin n → ℝ | 0 < x e + x i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · rintro ⟨h1,h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1,h2⟩; exact ⟨by linarith, by linarith⟩
  rw [hset]
  refine Work.WilG1.Omega.mono h ?_ ?_
  · simp only [max_self]
    omega
  · simp only [Polynomial.eval_add, Polynomial.eval_C]
    norm_num

/-- The general hypothesis-shaped set attached to two lists of coordinates `zl`, `zr` and a
"scale" coordinate `η`: the two vectors are nonzero and all their coordinates are `< η` in
absolute value.  It is `Ω`-definable with format `n + 6` and degree `4 * (7 * b)`, uniformly in
`D`. -/
theorem hypShape_mem (S : SOMin) {n b : ℕ} (η : Fin n) (zl zr : Fin b → Fin n) (D : ℕ) :
    {x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0 ∧
      (∀ j : Fin b, |x (zl j)| < x η) ∧
      (fun j : Fin b => x (zr j)) ≠ 0 ∧
      (∀ j : Fin b, |x (zr j)| < x η)} ∈
      S.Ω (n + 6) ((Polynomial.C 4 * Polynomial.C (7 * b)).eval D) n := by
  have hA1 : {x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0} ∈
      S.Ω (n + 5) ((Polynomial.C (7 * b)).eval D) n := by
    have hmem : (⋃ j : Fin b, {x : Fin n → ℝ | x (zl j) ≠ 0}) ∈
        S.Ω (n + 1) ((Polynomial.C b * Polynomial.C 1).eval D) n :=
      Work.WilG1.Omega.union_mem (S := S) (n := n) (k := b) (a := n + 1)
        (b := Polynomial.C 1) (D := D) (fun j : Fin b => {x : Fin n → ℝ | x (zl j) ≠ 0})
        (fun j => coordNe_mem S D (zl j))
    have hset : {x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0}
        = ⋃ j : Fin b, {x : Fin n → ℝ | x (zl j) ≠ 0} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, ne_eq, funext_iff, Pi.zero_apply,
        not_forall]
    rw [hset]
    refine Work.WilG1.Omega.mono hmem (show n + 1 ≤ n + 5 by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hA2 : {x : Fin n → ℝ | ∀ j : Fin b, |x (zl j)| < x η} ∈
      S.Ω (n + 5) ((Polynomial.C (7 * b)).eval D) n := by
    have hmem : (⋂ j : Fin b, {x : Fin n → ℝ | |x (zl j)| < x η}) ∈
        S.Ω (n + 4) ((Polynomial.C b * Polynomial.C 6).eval D) n :=
      Work.WilG1.Omega.inter_mem (S := S) (n := n) (k := b) (a := n + 3)
        (b := Polynomial.C 6) (D := D) (fun j : Fin b => {x : Fin n → ℝ | |x (zl j)| < x η})
        (fun j => absLtCoord_mem S D (zl j) η)
    rw [Set.iInter_ofPred
      (fun j : Fin b => fun x : Fin n → ℝ => |x (zl j)| < x η)] at hmem
    refine Work.WilG1.Omega.mono hmem (show n + 4 ≤ n + 5 by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hA3 : {x : Fin n → ℝ | (fun j : Fin b => x (zr j)) ≠ 0} ∈
      S.Ω (n + 5) ((Polynomial.C (7 * b)).eval D) n := by
    have hmem : (⋃ j : Fin b, {x : Fin n → ℝ | x (zr j) ≠ 0}) ∈
        S.Ω (n + 1) ((Polynomial.C b * Polynomial.C 1).eval D) n :=
      Work.WilG1.Omega.union_mem (S := S) (n := n) (k := b) (a := n + 1)
        (b := Polynomial.C 1) (D := D) (fun j : Fin b => {x : Fin n → ℝ | x (zr j) ≠ 0})
        (fun j => coordNe_mem S D (zr j))
    have hset : {x : Fin n → ℝ | (fun j : Fin b => x (zr j)) ≠ 0}
        = ⋃ j : Fin b, {x : Fin n → ℝ | x (zr j) ≠ 0} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, ne_eq, funext_iff, Pi.zero_apply,
        not_forall]
    rw [hset]
    refine Work.WilG1.Omega.mono hmem (show n + 1 ≤ n + 5 by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hA4 : {x : Fin n → ℝ | ∀ j : Fin b, |x (zr j)| < x η} ∈
      S.Ω (n + 5) ((Polynomial.C (7 * b)).eval D) n := by
    have hmem : (⋂ j : Fin b, {x : Fin n → ℝ | |x (zr j)| < x η}) ∈
        S.Ω (n + 4) ((Polynomial.C b * Polynomial.C 6).eval D) n :=
      Work.WilG1.Omega.inter_mem (S := S) (n := n) (k := b) (a := n + 3)
        (b := Polynomial.C 6) (D := D) (fun j : Fin b => {x : Fin n → ℝ | |x (zr j)| < x η})
        (fun j => absLtCoord_mem S D (zr j) η)
    rw [Set.iInter_ofPred
      (fun j : Fin b => fun x : Fin n → ℝ => |x (zr j)| < x η)] at hmem
    refine Work.WilG1.Omega.mono hmem (show n + 4 ≤ n + 5 by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hfam : ∀ i : Fin 4,
      (![{x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zl j)| < x η},
         {x : Fin n → ℝ | (fun j : Fin b => x (zr j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zr j)| < x η}] :
          Fin 4 → Set (Fin n → ℝ)) i ∈ S.Ω (n + 5) ((Polynomial.C (7 * b)).eval D) n := by
    intro i
    fin_cases i
    · exact hA1
    · exact hA2
    · exact hA3
    · exact hA4
  have hInter := Work.WilG1.Omega.inter_mem (S := S) (n := n) (k := 4) (a := n + 5)
    (b := Polynomial.C (7 * b)) (D := D)
    (fun i : Fin 4 =>
      (![{x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zl j)| < x η},
         {x : Fin n → ℝ | (fun j : Fin b => x (zr j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zr j)| < x η}] :
          Fin 4 → Set (Fin n → ℝ)) i) hfam
  have hEq : (⋂ i : Fin 4,
      (![{x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zl j)| < x η},
         {x : Fin n → ℝ | (fun j : Fin b => x (zr j)) ≠ 0},
         {x : Fin n → ℝ | ∀ j : Fin b, |x (zr j)| < x η}] :
          Fin 4 → Set (Fin n → ℝ)) i)
      = {x : Fin n → ℝ | (fun j : Fin b => x (zl j)) ≠ 0 ∧
          (∀ j : Fin b, |x (zl j)| < x η) ∧
          (fun j : Fin b => x (zr j)) ≠ 0 ∧
          (∀ j : Fin b, |x (zr j)| < x η)} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
    · rintro ⟨h1, h2, h3, h4⟩ i
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  rw [hEq] at hInter
  refine Work.WilG1.Omega.mono hInter (show n + 5 + 1 ≤ n + 6 by omega) le_rfl

theorem hyp_mem (S : WilkiesDesign.SOMin) (a b : ℕ) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ D : ℕ,
      hypSet (a := a) (b := b) ∈ S.Ω A (q.eval D) ((a + 1) + (b + b)) := by
  refine ⟨((a + 1) + (b + b)) + 6, Polynomial.C 4 * Polynomial.C (7 * b), fun D => ?_⟩
  exact hypShape_mem (S := S) (η := etaM (a := a) (b := b)) (zl := zM (a := a) (b := b))
    (zr := zM' (a := a) (b := b)) D

end Work.WilCrux.SCBig
