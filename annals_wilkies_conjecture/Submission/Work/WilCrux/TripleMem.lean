import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG1.Calc.lt_mem

set_option autoImplicit false
noncomputable section

namespace Work.WilCrux

open WilkiesDesign

/-!
## `Work.WilCrux.TripleMem`

The set

`{u : ℝ^N | ∀ i, |u (α i) - u (β i)| < u γ, (j ↦ u (δ j)) ≠ 0, ∀ j, |u (δ j)| < u γ}`

is a Boolean combination of *linear* strict inequalities and one non-vanishing condition, hence
semi-algebraic, hence `Ω`-definable, with a format and a degree bound that depend only on the
fixed data `N, a, b, α, β, δ, γ`.  We build it from the `Ω`-calculus:

* a strict inequality `0 < eval u P` for a linear `P` is the projection (dropping one variable `t`)
  of the hypersurface `t ^ 2 * P = 1` (`Work.WilG1.Calc.pos_mem`, wrapped as `posLin_mem`);
* a coordinate non-vanishing `u k ≠ 0` is the complement of the hypersurface `X k = 0`
  (`coord_ne_mem`);
* the conditions are then combined with the finite intersection/union axioms.
-/

/-! ## 1. Linear forms -/

/-- The linear form `X i - X j + X k`. -/
def lf {N : ℕ} (i j k : Fin N) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X i - MvPolynomial.X j + MvPolynomial.X k

/-- The linear form `X i - X j`. -/
def lfd {N : ℕ} (i j : Fin N) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X i - MvPolynomial.X j

/-- The linear form `X i + X j`. -/
def lfs {N : ℕ} (i j : Fin N) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X i + MvPolynomial.X j

lemma lf_td {N : ℕ} (i j k : Fin N) : (lf i j k).totalDegree ≤ 1 := by
  unfold lf
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [max_le_iff]
  exact ⟨by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩,
    by simp [MvPolynomial.totalDegree_X]⟩

lemma lfd_td {N : ℕ} (i j : Fin N) : (lfd i j).totalDegree ≤ 1 := by
  unfold lfd
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩

lemma lfs_td {N : ℕ} (i j : Fin N) : (lfs i j).totalDegree ≤ 1 := by
  unfold lfs
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [max_le_iff]
  exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩

/-! ## 2. Two `Ω`-atoms -/

/-- The positivity set of a linear polynomial is `Ω`-definable. -/
lemma posLin_mem {S : SOMin} {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (hP : P.totalDegree ≤ 1) (D : ℕ) :
    {x : Fin N → ℝ | 0 < MvPolynomial.eval x P} ∈ S.Ω (N + 2) ((Polynomial.C 3).eval D) N := by
  refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D P) le_rfl ?_
  simp only [Polynomial.eval_C]
  omega

/-- The set where one coordinate does not vanish is `Ω`-definable. -/
lemma coord_ne_mem {S : SOMin} {N : ℕ} (D : ℕ) (k : Fin N) :
    {u : Fin N → ℝ | u k ≠ 0} ∈ S.Ω (N + 1) ((Polynomial.C 1).eval D) N := by
  have h : {u : Fin N → ℝ | u k = 0} ∈ S.Ω N ((Polynomial.C 1).eval D) N := by
    have h0 := Work.WilG1.Omega.hyp_mem (S := S) D (MvPolynomial.X k : MvPolynomial (Fin N) ℝ)
    have hset : {x : Fin N → ℝ | MvPolynomial.eval x (MvPolynomial.X k : MvPolynomial (Fin N) ℝ) = 0}
        = {u : Fin N → ℝ | u k = 0} := by ext u; simp
    rw [hset] at h0
    refine Work.WilG1.Omega.mono h0 le_rfl ?_
    simp only [Polynomial.eval_C]
    exact le_of_eq (MvPolynomial.totalDegree_X k)
  have hc := Work.WilG1.Omega.compl_mem h
  convert hc using 2
  ext u; simp

/-! ## 3. The main statement -/

theorem TripleMem (S : WilkiesDesign.SOMin) {N a b : ℕ}
    (α β : Fin a → Fin N) (δ : Fin b → Fin N) (γ : Fin N) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (D : ℕ),
      {u : Fin N → ℝ | (∀ i : Fin a, |u (α i) - u (β i)| < u γ)
        ∧ (fun j : Fin b => u (δ j)) ≠ 0
        ∧ (∀ j : Fin b, |u (δ j)| < u γ)} ∈ S.Ω A (q.eval D) N := by
  classical
  refine ⟨N + 6, Polynomial.C (24 * (a + b + 1)), ?_⟩
  intro D
  set G1 : Set (Fin N → ℝ) := ⋂ i : Fin a, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (α i) (β i))} with hG1def
  set G2 : Set (Fin N → ℝ) := ⋂ i : Fin a, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (β i) (α i))} with hG2def
  set K1 : Set (Fin N → ℝ) := ⋂ j : Fin b, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfd γ (δ j))} with hK1def
  set K2 : Set (Fin N → ℝ) := ⋂ j : Fin b, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfs γ (δ j))} with hK2def
  set H : Set (Fin N → ℝ) := ⋃ j : Fin b, {u : Fin N → ℝ | u (δ j) ≠ 0} with hHdef
  have hG1mem : G1 ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
    rw [hG1def]
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := a) (a := N + 2) (b := Polynomial.C 3) (D := D)
      (fun i : Fin a => {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (α i) (β i))})
      (fun i => posLin_mem (S := S) (lf γ (α i) (β i)) (lf_td γ (α i) (β i)) D)
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hG2mem : G2 ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
    rw [hG2def]
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := a) (a := N + 2) (b := Polynomial.C 3) (D := D)
      (fun i : Fin a => {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (β i) (α i))})
      (fun i => posLin_mem (S := S) (lf γ (β i) (α i)) (lf_td γ (β i) (α i)) D)
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hK1mem : K1 ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
    rw [hK1def]
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := b) (a := N + 2) (b := Polynomial.C 3) (D := D)
      (fun j : Fin b => {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfd γ (δ j))})
      (fun j => posLin_mem (S := S) (lfd γ (δ j)) (lfd_td γ (δ j)) D)
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hK2mem : K2 ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
    rw [hK2def]
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := b) (a := N + 2) (b := Polynomial.C 3) (D := D)
      (fun j : Fin b => {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfs γ (δ j))})
      (fun j => posLin_mem (S := S) (lfs γ (δ j)) (lfs_td γ (δ j)) D)
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hHmem : H ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
    rw [hHdef]
    have h := Work.WilG1.Omega.union_mem (S := S) (n := N) (k := b) (a := N + 1) (b := Polynomial.C 1) (D := D)
      (fun j : Fin b => {u : Fin N → ℝ | u (δ j) ≠ 0})
      (fun j => coord_ne_mem (S := S) D (δ j))
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hG12 : G1 ∩ G2 ∈ S.Ω (N + 3 + 1) ((Polynomial.C 2 * Polynomial.C (3 * (a + b + 1))).eval D) N := by
    have hA : ∀ i : Fin 2, (if i = 0 then G1 else G2) ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
      intro i
      fin_cases i
      · simpa using hG1mem
      · simpa using hG2mem
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := 2) (a := N + 3) (b := Polynomial.C (3 * (a + b + 1))) (D := D)
      (fun i : Fin 2 => if i = 0 then G1 else G2) hA
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    exact h
  have hK12 : K1 ∩ K2 ∈ S.Ω (N + 3 + 1) ((Polynomial.C 2 * Polynomial.C (3 * (a + b + 1))).eval D) N := by
    have hA : ∀ i : Fin 2, (if i = 0 then K1 else K2) ∈ S.Ω (N + 3) ((Polynomial.C (3 * (a + b + 1))).eval D) N := by
      intro i
      fin_cases i
      · simpa using hK1mem
      · simpa using hK2mem
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := 2) (a := N + 3) (b := Polynomial.C (3 * (a + b + 1))) (D := D)
      (fun i : Fin 2 => if i = 0 then K1 else K2) hA
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    exact h
  have hGK : G1 ∩ G2 ∩ (K1 ∩ K2) ∈ S.Ω (N + 3 + 1 + 1)
      ((Polynomial.C 2 * (Polynomial.C 2 * Polynomial.C (3 * (a + b + 1)))).eval D) N := by
    have hA : ∀ i : Fin 2, (if i = 0 then G1 ∩ G2 else K1 ∩ K2) ∈ S.Ω (N + 3 + 1)
        ((Polynomial.C 2 * Polynomial.C (3 * (a + b + 1))).eval D) N := by
      intro i
      fin_cases i
      · simpa using hG12
      · simpa using hK12
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := 2) (a := N + 3 + 1)
      (b := Polynomial.C 2 * Polynomial.C (3 * (a + b + 1))) (D := D)
      (fun i : Fin 2 => if i = 0 then G1 ∩ G2 else K1 ∩ K2) hA
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    exact h
  have hH2 : H ∈ S.Ω (N + 3 + 1 + 1) ((Polynomial.C 2 * (Polynomial.C 2 * Polynomial.C (3 * (a + b + 1)))).eval D) N := by
    refine Work.WilG1.Omega.mono hHmem (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hmain : G1 ∩ G2 ∩ (K1 ∩ K2) ∩ H ∈ S.Ω (N + 6) ((Polynomial.C (24 * (a + b + 1))).eval D) N := by
    have hA : ∀ i : Fin 2, (if i = 0 then G1 ∩ G2 ∩ (K1 ∩ K2) else H) ∈ S.Ω (N + 3 + 1 + 1)
        ((Polynomial.C 2 * (Polynomial.C 2 * Polynomial.C (3 * (a + b + 1)))).eval D) N := by
      intro i
      fin_cases i
      · simpa using hGK
      · simpa using hH2
    have h := Work.WilG1.Omega.inter_mem (S := S) (n := N) (k := 2) (a := N + 3 + 1 + 1)
      (b := Polynomial.C 2 * (Polynomial.C 2 * Polynomial.C (3 * (a + b + 1)))) (D := D)
      (fun i : Fin 2 => if i = 0 then G1 ∩ G2 ∩ (K1 ∩ K2) else H) hA
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    refine Work.WilG1.Omega.mono h (by omega) ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    omega
  have hEq : G1 ∩ G2 ∩ (K1 ∩ K2) ∩ H =
      {u : Fin N → ℝ | (∀ i : Fin a, |u (α i) - u (β i)| < u γ)
        ∧ (fun j : Fin b => u (δ j)) ≠ 0
        ∧ (∀ j : Fin b, |u (δ j)| < u γ)} := by
    rw [hG1def, hG2def, hK1def, hK2def, hHdef]
    have e1 : (⋂ i : Fin a, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (α i) (β i))})
        ∩ (⋂ i : Fin a, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lf γ (β i) (α i))})
        = {u : Fin N → ℝ | ∀ i : Fin a, |u (α i) - u (β i)| < u γ} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, lf,
        MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_X]
      constructor
      · rintro ⟨h1, h2⟩ i
        rw [abs_lt]
        constructor <;> linarith [h1 i, h2 i]
      · intro h
        exact ⟨fun i => by have := (abs_lt.mp (h i)).2; linarith,
               fun i => by have := (abs_lt.mp (h i)).1; linarith⟩
    have e2 : (⋂ j : Fin b, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfd γ (δ j))})
        ∩ (⋂ j : Fin b, {u : Fin N → ℝ | 0 < MvPolynomial.eval u (lfs γ (δ j))})
        = {u : Fin N → ℝ | ∀ j : Fin b, |u (δ j)| < u γ} := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, lfd, lfs,
        MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_X]
      constructor
      · rintro ⟨h1, h2⟩ j
        rw [abs_lt]
        constructor <;> linarith [h1 j, h2 j]
      · intro h
        exact ⟨fun j => by have := (abs_lt.mp (h j)).2; linarith,
               fun j => by have := (abs_lt.mp (h j)).1; linarith⟩
    have e3 : (⋃ j : Fin b, {u : Fin N → ℝ | u (δ j) ≠ 0})
        = {u : Fin N → ℝ | (fun j : Fin b => u (δ j)) ≠ 0} := by
      ext u
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj⟩ h
        exact hj (by simpa using congr_fun h j)
      · intro h
        by_contra hc
        exact h (funext fun j => by
          by_contra hj
          exact hc ⟨j, by simpa using hj⟩)
    rw [e1, e2, e3]
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
  rw [hEq] at hmain
  exact hmain

end Work.WilCrux
