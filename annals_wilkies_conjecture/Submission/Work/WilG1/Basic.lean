/-
  WilG1 : the Ω-calculus for abstract sharply o-minimal structures.

  Elementary closure properties of the format-degree filtration `SOMin.Ω` that area G
  (and H) needs: intersections, unions over `Fin k`, complements, projections, products,
  hypersurfaces.  Every lemma carries explicit format and degree bounds: the format is a
  numeral independent of `D`, the degree a polynomial in the degree parameter `D`.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1

open WilkiesDesign WilkiesConjecture

/-! ## 1. Polynomial bookkeeping for degree bounds -/

/-- Substitute `X₁ := k` into a two-variable polynomial with natural coefficients, producing
a one-variable polynomial, so that `eval ![D,k] b = (psubst b k).eval D`. -/
def psubst (b : MvPolynomial (Fin 2) ℕ) (k : ℕ) : Polynomial ℕ :=
  b.eval₂ Polynomial.C (fun i => if i = (0 : Fin 2) then Polynomial.X else Polynomial.C k)

theorem eval_psubst (b : MvPolynomial (Fin 2) ℕ) (k D : ℕ) :
    (psubst b k).eval D = MvPolynomial.eval ![D, k] b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp [psubst]
  | add p q hp hq =>
      simp only [psubst, MvPolynomial.eval₂_add, Polynomial.eval_add] at hp hq ⊢
      rw [hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
      simp only [psubst, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at hp ⊢
      rw [Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      congr 1
      by_cases h : i = (0 : Fin 2)
      · subst h; simp
      · have hik : ![D, k] i = k := by fin_cases i <;> simp_all
        rw [hik]; simp [h]

/-- `Polynomial ℕ` is monotone in its evaluation point. -/
theorem Polynomial.eval_mono {b : Polynomial ℕ} {D D' : ℕ} (h : D ≤ D') :
    b.eval D ≤ b.eval D' := by
  induction b using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial n a =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left h n)

/-- A linear polynomial cutting out the hyperplane `x i = x j`. -/
def linPoly {n : ℕ} (i j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i - MvPolynomial.X j

/-! ## 2. Elementary closure lemmas for `S.Ω` with explicit bounds -/

namespace Omega

variable {S : SOMin}

/-- Raising the format and degree of an `Ω` membership. -/
theorem mono {n : ℕ} {X : Set (Fin n → ℝ)} {F D F' D' : ℕ}
    (h : X ∈ S.Ω F D n) (hF : F ≤ F') (hD : D ≤ D') : X ∈ S.Ω F' D' n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hD
  have hFk : ∀ k, X ∈ S.Ω (F + k) D n := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih => simpa [Nat.add_assoc] using S.mono_F ih
  have hDl : ∀ l, X ∈ S.Ω (F + k) (D + l) n := by
    intro l
    induction l with
    | zero => simpa using hFk k
    | succ l ih => simpa [Nat.add_assoc] using S.mono_D ih
  exact hDl l

/-- Finite intersections: uniform bounds in the family. -/
theorem inter_mem {n k : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ}
    (A : Fin k → Set (Fin n → ℝ)) (hA : ∀ i, A i ∈ S.Ω a (b.eval D) n) :
    (⋂ i, A i) ∈ S.Ω (a + 1) ((Polynomial.C k * b).eval D) n := by
  have h := S.inter (F := a) (D := fun _ : Fin k => b.eval D) A hA
  have hsum : (∑ _ : Fin k, b.eval D) = (Polynomial.C k * b).eval D := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp [Polynomial.eval_mul]
  rwa [hsum] at h

/-- Finite unions: uniform bounds in the family. -/
theorem union_mem {n k : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ}
    (A : Fin k → Set (Fin n → ℝ)) (hA : ∀ i, A i ∈ S.Ω a (b.eval D) n) :
    (⋃ i, A i) ∈ S.Ω a ((Polynomial.C k * b).eval D) n := by
  have h := S.union (F := a) (D := fun _ : Fin k => b.eval D) A hA
  have hsum : (∑ _ : Fin k, b.eval D) = (Polynomial.C k * b).eval D := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp [Polynomial.eval_mul]
  rwa [hsum] at h

/-- The intersection of the `Fin 2`-indexed family selecting `X,Y`. -/
theorem iInter_fin_two {α : Type*} (X Y : Set α) :
    Set.iInter (fun i : Fin 2 => if i = 0 then X else Y) = X ∩ Y := by
  ext z
  rw [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro hh
    exact ⟨by simpa using hh 0, by simpa using hh 1⟩
  · rintro ⟨hx, hy⟩ i
    fin_cases i
    · simpa using hx
    · simpa using hy

/-- The union of the `Fin 2`-indexed family selecting `X,Y`. -/
theorem iUnion_fin_two {α : Type*} (X Y : Set α) :
    Set.iUnion (fun i : Fin 2 => if i = 0 then X else Y) = X ∪ Y := by
  ext z
  rw [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa using hi)
    · exact Or.inr (by simpa using hi)
  · rintro (hx | hy)
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hy⟩

/-- Binary intersection. -/
theorem inter₂ {n : ℕ} {a₁ a₂ : ℕ} {b₁ b₂ : Polynomial ℕ} {D : ℕ}
    {X Y : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a₁ (b₁.eval D) n)
    (hY : Y ∈ S.Ω a₂ (b₂.eval D) n) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) ((b₁ + b₂).eval D) n := by
  have h1 : X ∈ S.Ω (max a₁ a₂) (b₁.eval D) n := mono hX (le_max_left _ _) le_rfl
  have h2 : Y ∈ S.Ω (max a₁ a₂) (b₂.eval D) n := mono hY (le_max_right _ _) le_rfl
  have h := S.inter (F := max a₁ a₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then b₁.eval D else b₂.eval D)
    (fun i : Fin 2 => if i = 0 then X else Y) (by intro i; fin_cases i <;> simpa using ‹_›)
  have hsum : (∑ i : Fin 2, (if i = 0 then b₁.eval D else b₂.eval D)) = (b₁ + b₂).eval D := by
    rw [Fin.sum_univ_two]; simp [Polynomial.eval_add]
  rw [hsum] at h
  rw [iInter_fin_two] at h
  exact h

/-- Binary union. -/
theorem union₂ {n : ℕ} {a₁ a₂ : ℕ} {b₁ b₂ : Polynomial ℕ} {D : ℕ}
    {X Y : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a₁ (b₁.eval D) n)
    (hY : Y ∈ S.Ω a₂ (b₂.eval D) n) :
    X ∪ Y ∈ S.Ω (max a₁ a₂) ((b₁ + b₂).eval D) n := by
  have h1 : X ∈ S.Ω (max a₁ a₂) (b₁.eval D) n := mono hX (le_max_left _ _) le_rfl
  have h2 : Y ∈ S.Ω (max a₁ a₂) (b₂.eval D) n := mono hY (le_max_right _ _) le_rfl
  have h := S.union (F := max a₁ a₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then b₁.eval D else b₂.eval D)
    (fun i : Fin 2 => if i = 0 then X else Y) (by intro i; fin_cases i <;> simpa using ‹_›)
  have hsum : (∑ i : Fin 2, (if i = 0 then b₁.eval D else b₂.eval D)) = (b₁ + b₂).eval D := by
    rw [Fin.sum_univ_two]; simp [Polynomial.eval_add]
  rw [hsum] at h
  rw [iUnion_fin_two] at h
  exact h

/-- Complements. -/
theorem compl_mem {n : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) : Xᶜ ∈ S.Ω (a + 1) (b.eval D) n :=
  S.compl hX

/-- Projecting out the last coordinate. -/
theorem projLast_mem {n : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ}
    {X : Set (Fin (n + 1) → ℝ)} (hX : X ∈ S.Ω a (b.eval D) (n + 1)) :
    projLast X ∈ S.Ω (a + 1) (b.eval D) n :=
  S.proj hX

/-- Adding a dummy last coordinate. -/
theorem prodRight_mem {n : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ}
    {X : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a (b.eval D) n) :
    {z : Fin (n + 1) → ℝ | Fin.init z ∈ X} ∈ S.Ω (a + 1) (b.eval D) (n + 1) :=
  S.prod_right hX

/-- Adding a dummy first coordinate. -/
theorem prodLeft_mem {n : ℕ} {a : ℕ} {b : Polynomial ℕ} {D : ℕ}
    {X : Set (Fin n → ℝ)} (hX : X ∈ S.Ω a (b.eval D) n) :
    {z : Fin (n + 1) → ℝ | Fin.tail z ∈ X} ∈ S.Ω (a + 1) (b.eval D) (n + 1) :=
  S.prod_left hX

/-- Hypersurfaces. -/
theorem hyp_mem {n : ℕ} (D : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    {x : Fin n → ℝ | MvPolynomial.eval x P = 0} ∈
      S.Ω n ((Polynomial.C P.totalDegree).eval D) n := by
  simpa using S.hyp n P

/-- Affine hyperplanes: `{x | x i = x j}`. -/
theorem coordEq_mem {n : ℕ} (D : ℕ) (i j : Fin n) :
    {x : Fin n → ℝ | x i = x j} ∈ S.Ω n ((Polynomial.C 1).eval D) n := by
  have h := hyp_mem (S := S) D (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
  have htd : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  have hset : {x : Fin n → ℝ | MvPolynomial.eval x
        (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ) = 0}
      = {x : Fin n → ℝ | x i = x j} := by
    ext x; simp only [Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      sub_eq_zero]
  rw [hset] at h
  refine Omega.mono h le_rfl ?_
  show (Polynomial.C (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ).totalDegree).eval D
    ≤ (Polynomial.C 1).eval D
  simpa using htd

end Omega

end Work.WilG1
