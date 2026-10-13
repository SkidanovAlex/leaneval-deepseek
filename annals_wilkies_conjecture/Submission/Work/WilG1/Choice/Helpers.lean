/-
  WilG1/Choice/Helpers — generic Ω-calculus tools for the selection-membership proof
  `Work.WilG1.Choice.selSet_mem`.

  The tools are:
  * `inter2_mem`, `union2_mem` — binary intersections / unions with explicit format and
    degree bookkeeping (format is `max`ed, degrees add);
  * `forall_mem` — universal quantification of the last coordinate, via
    `∀ t φ(t) = (∃ t ¬φ(t))ᶜ` (three Ω-steps);
  * `coordEq_mem`, `linEq_mem` — coordinate equations `y i = c`, `y i = y j` as hypersurfaces;
  * `gtConst_mem`, `ltConst_mem`, `leConst_mem`, `geConst_mem` — the half-spaces
    `c < y i`, `y i < c`, `y i ≤ c`, `c ≤ y i`, via the square-root trick of
    `Work.WilG1.Calc.lt_mem`;
  * `sum_coeff_mul` — the identity `∑ i, L (Pi.single i 1) * y i = L y` for a linear
    functional `L` on `Fin N → ℝ`, which turns the coefficient vector of
    `Work.WilG1.Choice.affLast_mem` into an evaluation of `L`;
  * `affLast_one`, `affLast_add`, `affLast_sub`, `affLast_last` — the specialisations of
    `affLast_mem` in which the replaced last coordinate is `y u + c`, `y u + y v + c`,
    `y u - y v + c`, and `y (Fin.last p) + c` with the first `p` coordinates of the ambient
    point.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG1.Calc.le_mem
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Choice.AffLast

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 1. Boolean combinators -/

theorem inter2_mem {S : SOMin} {n F₁ F₂ D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∩ B ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : A ∈ S.Ω (max F₁ F₂) D₁ n := Omega.mono hA (le_max_left F₁ F₂) le_rfl
  have h2 : B ∈ S.Ω (max F₁ F₂) D₂ n := Omega.mono hB (le_max_right F₁ F₂) le_rfl
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by intro i
        fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [Omega.iInter_fin_two] at h
  have hs : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hs] at h
  exact h

theorem union2_mem {S : SOMin} {n F₁ F₂ D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∪ B ∈ S.Ω (max F₁ F₂) (D₁ + D₂) n := by
  have h1 : A ∈ S.Ω (max F₁ F₂) D₁ n := Omega.mono hA (le_max_left F₁ F₂) le_rfl
  have h2 : B ∈ S.Ω (max F₁ F₂) D₂ n := Omega.mono hB (le_max_right F₁ F₂) le_rfl
  have h := S.union (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by intro i
        fin_cases i
        · simpa using h1
        · simpa using h2)
  rw [Omega.iUnion_fin_two] at h
  have hs : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hs] at h
  exact h

/-! ## 2. Universal quantification of the last coordinate -/

theorem forall_mem {S : SOMin} {n F D : ℕ} {A : Set (Fin (n + 1) → ℝ)}
    (hA : A ∈ S.Ω F D (n + 1)) :
    {y : Fin n → ℝ | ∀ t : ℝ, Fin.snoc y t ∈ A} ∈ S.Ω (F + 3) D n := by
  have h3 : (projLast Aᶜ)ᶜ ∈ S.Ω (F + 3) D n := S.compl (S.proj (S.compl hA))
  have he : (projLast Aᶜ)ᶜ = {y : Fin n → ℝ | ∀ t : ℝ, Fin.snoc y t ∈ A} := by
    ext y
    simp only [Set.mem_compl_iff, projLast, Set.mem_ofPred_eq, not_exists, not_not]
  rw [he] at h3
  exact h3

/-! ## 3. Equations -/

theorem coordEq_mem {S : SOMin} {N : ℕ} (i : Fin N) (c : ℝ) :
    {y : Fin N → ℝ | y i = c} ∈ S.Ω N 1 N := by
  have htd : (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨le_of_eq (MvPolynomial.totalDegree_X i),
      le_trans (le_of_eq (MvPolynomial.totalDegree_C c)) (Nat.zero_le 1)⟩
  have h := Omega.mono (S.hyp N (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin N) ℝ))
    le_rfl htd
  have he : {y : Fin N → ℝ |
        MvPolynomial.eval y (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin N) ℝ) = 0}
      = {y : Fin N → ℝ | y i = c} := by
    ext y
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [he] at h
  exact h

theorem linEq_mem {S : SOMin} {N : ℕ} (i j : Fin N) :
    {y : Fin N → ℝ | y i = y j} ∈ S.Ω N 1 N := by
  have htd : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨le_of_eq (MvPolynomial.totalDegree_X i), le_of_eq (MvPolynomial.totalDegree_X j)⟩
  have h := Omega.mono (S.hyp N (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ))
    le_rfl htd
  have he : {y : Fin N → ℝ |
        MvPolynomial.eval y (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ) = 0}
      = {y : Fin N → ℝ | y i = y j} := by
    ext y
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [he] at h
  exact h

/-! ## 4. Half-spaces -/

theorem gtConst_mem {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c < x i} ∈ S.Ω (n + 2) 3 n := by
  set P : MvPolynomial (Fin (n + 1)) ℝ :=
    (MvPolynomial.X (Fin.castSucc i) - MvPolynomial.C c) * MvPolynomial.X (Fin.last n) ^ 2 - 1
    with hP
  have htd : P.totalDegree ≤ 3 := by
    rw [hP]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.X (Fin.castSucc i) - MvPolynomial.C c :
          MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        rw [max_le_iff]
        exact ⟨le_of_eq (MvPolynomial.totalDegree_X _),
          le_trans (le_of_eq (MvPolynomial.totalDegree_C c)) (Nat.zero_le 1)⟩
      have h2 : (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 2 := by
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      linarith
    · rw [MvPolynomial.totalDegree_one]; norm_num
  have h0 : {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω (n + 1) 3 (n + 1) :=
    Omega.mono (S.hyp (n + 1) P) le_rfl htd
  have h1 : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω (n + 2) 3 n :=
    S.proj h0
  have hev : ∀ (x : Fin n → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc x t) P = (x i - c) * t ^ 2 - 1 := by
    intro x t
    rw [hP]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.snoc_castSucc, Fin.snoc_last, map_one]
  have he : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} =
      {x : Fin n → ℝ | c < x i} := by
    ext x
    simp only [projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hev x t] at ht
      have key : (x i - c) * t ^ 2 = 1 := by linarith
      have ht2 : 0 < t ^ 2 := by
        rcases lt_or_eq_of_le (sq_nonneg t) with hh | hh
        · exact hh
        · rw [← hh] at key; norm_num at key
      have hc : 0 < x i - c := by
        by_contra hcon
        have hcon' : x i - c ≤ 0 := le_of_not_gt hcon
        have : (x i - c) * t ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon' (sq_nonneg t)
        linarith
      linarith
    · intro hlt
      have hd : 0 < x i - c := by linarith
      refine ⟨(Real.sqrt (x i - c))⁻¹, ?_⟩
      rw [hev x (Real.sqrt (x i - c))⁻¹]
      have hs : (Real.sqrt (x i - c)) ^ 2 = x i - c := Real.sq_sqrt (le_of_lt hd)
      have hne : x i - c ≠ 0 := ne_of_gt hd
      rw [inv_pow, hs, mul_inv_cancel₀ hne]
      norm_num
  rw [he] at h1
  exact h1

theorem ltConst_mem {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i < c} ∈ S.Ω (n + 2) 3 n := by
  set P : MvPolynomial (Fin (n + 1)) ℝ :=
    (MvPolynomial.C c - MvPolynomial.X (Fin.castSucc i)) * MvPolynomial.X (Fin.last n) ^ 2 - 1
    with hP
  have htd : P.totalDegree ≤ 3 := by
    rw [hP]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C c - MvPolynomial.X (Fin.castSucc i) :
          MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        rw [max_le_iff]
        exact ⟨le_trans (le_of_eq (MvPolynomial.totalDegree_C c)) (Nat.zero_le 1),
          le_of_eq (MvPolynomial.totalDegree_X _)⟩
      have h2 : (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 2 := by
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      linarith
    · rw [MvPolynomial.totalDegree_one]; norm_num
  have h0 : {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω (n + 1) 3 (n + 1) :=
    Omega.mono (S.hyp (n + 1) P) le_rfl htd
  have h1 : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} ∈ S.Ω (n + 2) 3 n :=
    S.proj h0
  have hev : ∀ (x : Fin n → ℝ) (t : ℝ),
      MvPolynomial.eval (Fin.snoc x t) P = (c - x i) * t ^ 2 - 1 := by
    intro x t
    rw [hP]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.snoc_castSucc, Fin.snoc_last, map_one]
  have he : projLast {z : Fin (n + 1) → ℝ | MvPolynomial.eval z P = 0} =
      {x : Fin n → ℝ | x i < c} := by
    ext x
    simp only [projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [hev x t] at ht
      have key : (c - x i) * t ^ 2 = 1 := by linarith
      have ht2 : 0 < t ^ 2 := by
        rcases lt_or_eq_of_le (sq_nonneg t) with hh | hh
        · exact hh
        · rw [← hh] at key; norm_num at key
      have hc : 0 < c - x i := by
        by_contra hcon
        have hcon' : c - x i ≤ 0 := le_of_not_gt hcon
        have : (c - x i) * t ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon' (sq_nonneg t)
        linarith
      linarith
    · intro hlt
      have hd : 0 < c - x i := by linarith
      refine ⟨(Real.sqrt (c - x i))⁻¹, ?_⟩
      rw [hev x (Real.sqrt (c - x i))⁻¹]
      have hs : (Real.sqrt (c - x i)) ^ 2 = c - x i := Real.sq_sqrt (le_of_lt hd)
      have hne : c - x i ≠ 0 := ne_of_gt hd
      rw [inv_pow, hs, mul_inv_cancel₀ hne]
      norm_num
  rw [he] at h1
  exact h1

theorem leConst_mem {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i ≤ c} ∈ S.Ω (n + 3) 3 n := by
  have h := S.compl (gtConst_mem (S := S) i c)
  have he : {x : Fin n → ℝ | c < x i}ᶜ = {x : Fin n → ℝ | x i ≤ c} := by
    ext x; simp [not_lt]
  rw [he] at h
  exact h

theorem geConst_mem {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c ≤ x i} ∈ S.Ω (n + 3) 3 n := by
  have h := S.compl (ltConst_mem (S := S) i c)
  have he : {x : Fin n → ℝ | x i < c}ᶜ = {x : Fin n → ℝ | c ≤ x i} := by
    ext x; simp [not_lt]
  rw [he] at h
  exact h

/-! ## 5. Linear functionals as coefficient vectors -/

/-- The `u`-th coordinate functional on `Fin N → ℝ`. -/
def linProj {N : ℕ} (u : Fin N) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun y := y u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linProj_apply {N : ℕ} (u : Fin N) (y : Fin N → ℝ) : linProj u y = y u := rfl

theorem sum_coeff_mul {N : ℕ} (L : (Fin N → ℝ) →ₗ[ℝ] ℝ) (y : Fin N → ℝ) :
    ∑ i : Fin N, L (Pi.single i (1 : ℝ)) * y i = L y := by
  rw [LinearMap.pi_apply_eq_sum_univ L y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  rw [show L (Pi.single i (1 : ℝ)) = L (fun j => if i = j then 1 else 0) from ?_]
  · ring
  · congr 1
    funext j
    rw [Pi.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]

/-! ## 6. Specialisations of `affLast_mem` -/

theorem affLast_one {S : SOMin} {p N : ℕ} (hp : p ≤ N) {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (u : Fin N) (c : ℝ) :
    {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u + c) ∈ K} ∈
      S.Ω (max (a + N) (N + (p + 1)) + 1 + (p + 1)) ((b + Polynomial.C 2).eval D) N := by
  have h := affAtom_mem (S := S) hp hK (L := fun i => linProj u (Pi.single i (1 : ℝ))) c
  have he : {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
        ((∑ i : Fin N, linProj u (Pi.single i (1 : ℝ)) * y i) + c) ∈ K}
      = {y : Fin N → ℝ |
          Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u + c) ∈ K} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [sum_coeff_mul (linProj u) y]
    simp [linProj]
  rw [he] at h
  exact h

theorem affLast_add {S : SOMin} {p N : ℕ} (hp : p ≤ N) {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (u v : Fin N) (c : ℝ) :
    {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u + y v + c) ∈ K} ∈
      S.Ω (max (a + N) (N + (p + 1)) + 1 + (p + 1)) ((b + Polynomial.C 2).eval D) N := by
  have h := affAtom_mem (S := S) hp hK
    (L := fun i => (linProj u + linProj v) (Pi.single i (1 : ℝ))) c
  have he : {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
        ((∑ i : Fin N, (linProj u + linProj v) (Pi.single i (1 : ℝ)) * y i) + c) ∈ K}
      = {y : Fin N → ℝ |
          Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u + y v + c) ∈ K} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [sum_coeff_mul (linProj u + linProj v) y]
    simp [linProj]
  rw [he] at h
  exact h

theorem affLast_sub {S : SOMin} {p N : ℕ} (hp : p ≤ N) {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (u v : Fin N) (c : ℝ) :
    {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u - y v + c) ∈ K} ∈
      S.Ω (max (a + N) (N + (p + 1)) + 1 + (p + 1)) ((b + Polynomial.C 2).eval D) N := by
  have h := affAtom_mem (S := S) hp hK
    (L := fun i => (linProj u - linProj v) (Pi.single i (1 : ℝ))) c
  have he : {y : Fin N → ℝ | Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
        ((∑ i : Fin N, (linProj u - linProj v) (Pi.single i (1 : ℝ)) * y i) + c) ∈ K}
      = {y : Fin N → ℝ |
          Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (y u - y v + c) ∈ K} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [sum_coeff_mul (linProj u - linProj v) y]
    simp [linProj]
  rw [he] at h
  exact h

theorem affLast_last {S : SOMin} {p a D : ℕ} {b : Polynomial ℕ} {K : Set (Fin (p + 1) → ℝ)}
    (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (c : ℝ) :
    {y : Fin (p + 1) → ℝ | Fin.snoc (Fin.init y) (y (Fin.last p) + c) ∈ K} ∈
      S.Ω (max (a + (p + 1)) ((p + 1) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1) := by
  have h := affLast_one (S := S) (p := p) (N := p + 1) (Nat.le_succ p) hK (Fin.last p) c
  have he : {y : Fin (p + 1) → ℝ |
        Fin.snoc (fun i : Fin p => y (Fin.castLE (Nat.le_succ p) i)) (y (Fin.last p) + c) ∈ K}
      = {y : Fin (p + 1) → ℝ | Fin.snoc (Fin.init y) (y (Fin.last p) + c) ∈ K} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    have hfun : (fun i : Fin p => y (Fin.castLE (Nat.le_succ p) i)) = Fin.init y := by
      funext i
      show y (Fin.castLE (Nat.le_succ p) i) = y (Fin.castSucc i)
      congr 1
    rw [hfun]
  rw [he] at h
  exact h

theorem affLast_last_sub {S : SOMin} {p a D : ℕ} {b : Polynomial ℕ} {K : Set (Fin (p + 1) → ℝ)}
    (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (d : ℝ) :
    {y : Fin (p + 1) → ℝ | Fin.snoc (Fin.init y) (y (Fin.last p) - d) ∈ K} ∈
      S.Ω (max (a + (p + 1)) ((p + 1) + (p + 1)) + 1 + (p + 1))
        ((b + Polynomial.C 2).eval D) (p + 1) := by
  have h := affLast_last (S := S) hK (-d)
  have he : {y : Fin (p + 1) → ℝ | Fin.snoc (Fin.init y) (y (Fin.last p) + (-d)) ∈ K}
      = {y : Fin (p + 1) → ℝ | Fin.snoc (Fin.init y) (y (Fin.last p) - d) ∈ K} := by
    ext y
    simp only [Set.mem_ofPred_eq, sub_eq_add_neg]
  rwa [he] at h

end Work.WilG1.Choice
