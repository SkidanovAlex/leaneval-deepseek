/-
  WilG1 / Calc / ClosureStep.

  The two halves of `Work.WilG1.Calc.closure_mem`:

  * `projLast_finalC_eq_of` : `projLast (finalC X) = (closure X)ᶜ`, the set-theoretic
    identification of the closure complement with a projection of `finalC X`.  It is stated
    conditional on the two "reading" facts it consumes: the closure criterion `ClosureReading`
    (delegated as `Work.WilG1.Calc.closure_char`) and the coordinate reading of the big set
    `AppendReading` (delegated as `Work.WilG1.Calc.closure_append_mem`).

  * `finalC_mem` : the `Ω`-membership of `finalC X`, with crude format and degree bounds.

  The format bookkeeping deliberately avoids `max`: both intersections are performed at a
  *common* format (obtained by monotonicity), so that `SOMin.inter` may be used directly and
  every displayed bound is a linear expression in `a` and `n` (plus the degree `b.eval D`).
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.ClosureDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Calc

open WilkiesDesign WilkiesConjecture

/-! ## 1. Replacing the threshold comparison by a squared unknown -/

/-- `S ≤ t²` is the same as the solvability of `S + s² = t²`. -/
theorem exists_sq_eq_iff (S t : ℝ) : (∃ s : ℝ, S + s ^ 2 = t ^ 2) ↔ S ≤ t ^ 2 := by
  constructor
  · rintro ⟨s, hs⟩
    nlinarith [sq_nonneg s]
  · intro h
    exact ⟨Real.sqrt (t ^ 2 - S), by rw [Real.sq_sqrt (by linarith)]; ring⟩

/-- `Fin.snoc y s`, with the codomain made explicit so that the (dependent) codomain of
`Fin.snoc` is fixed to the constant family `ℝ`. -/
def snocFun {n : ℕ} (y : Fin n → ℝ) (s : ℝ) : Fin (n + 1) → ℝ := Fin.snoc y s

/-- The first `n` coordinates of `snocFun y s` are those of `y`. -/
theorem snocFun_castSucc {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    (fun j : Fin n => snocFun y s (Fin.castSucc j)) = y := by
  simpa [snocFun, Function.comp_def] using Fin.snoc_comp_castSucc (f := y) (a := s)

/-- The last coordinate of `snocFun y s` is `s`. -/
theorem snocFun_last {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    snocFun y s (Fin.last n) = s := by
  simpa [snocFun] using Fin.snoc_last (p := y) (x := s)

/-- An element `u : Fin (n+1) → ℝ` together with the two equations of `bigJ` is the same data
as a pair `(y, s)` with `y ∈ X` and `Σ_j (y_j - x_j)^2 + s^2 = t^2`; equivalently
`∃ y ∈ X, Σ_j (y_j - x_j)^2 ≤ t^2`. -/
theorem exists_u_iff {n : ℕ} {X : Set (Fin n → ℝ)} (x : Fin n → ℝ) (t : ℝ) :
    (∃ u : Fin (n + 1) → ℝ, (fun j : Fin n => u (Fin.castSucc j)) ∈ X ∧
        (∑ j : Fin n, (u (Fin.castSucc j) - x j) ^ 2) + u (Fin.last n) ^ 2 = t ^ 2) ↔
      ∃ y ∈ X, ∑ j : Fin n, (y j - x j) ^ 2 ≤ t ^ 2 := by
  constructor
  · rintro ⟨u, huX, hu⟩
    exact ⟨fun j => u (Fin.castSucc j), huX, (exists_sq_eq_iff _ t).mp ⟨u (Fin.last n), hu⟩⟩
  · rintro ⟨y, hyX, hy⟩
    obtain ⟨s, hs⟩ := (exists_sq_eq_iff _ t).mpr hy
    refine ⟨snocFun y s, ?_, ?_⟩
    · rw [snocFun_castSucc]
      exact hyX
    · rw [snocFun_last]
      have hsum : (∑ j : Fin n, (snocFun y s (Fin.castSucc j) - x j) ^ 2) =
          ∑ j : Fin n, (y j - x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show snocFun y s (Fin.castSucc j) = y j from congrFun (snocFun_castSucc y s) j]
      rw [hsum]
      exact hs

/-! ## 2. The reading hypotheses -/

/-- Reading the big set in the coordinates `(x, r, y, s)`: a point of `ℝ^{(n+1)+(n+1)}` written
`Fin.append (Fin.snoc x r) u` lies in `bigJ X` exactly when the `X`-block of `u` lies in `X` and
`Σ_j (u_j - x_j)^2 + u_n^2 = r^2`. -/
def AppendReading {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∀ (x : Fin n → ℝ) (r : ℝ) (u : Fin (n + 1) → ℝ),
    Fin.append (Fin.snoc x r) u ∈ (bigSpace_eq n ▸ bigJ X) ↔
      (fun j : Fin n => u (Fin.castSucc j)) ∈ X ∧
        (∑ j : Fin n, (u (Fin.castSucc j) - x j) ^ 2) + (u (Fin.last n)) ^ 2 - r ^ 2 = 0

/-- The closure criterion used by the construction. -/
def ClosureReading {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  ∀ x : Fin n → ℝ, (x ∈ closure X ↔
    ∀ r : ℝ, r ≠ 0 → ∃ y ∈ X, ∑ i : Fin n, (y i - x i) ^ 2 ≤ r ^ 2)

/-! ## 3. The complement of the closure is the projection of `finalC` -/

theorem projLast_finalC_eq_of {n : ℕ} {X : Set (Fin n → ℝ)}
    (happ : AppendReading X) (hchar : ClosureReading X) :
    projLast (finalC X) = (closure X)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, hchar x]
  have hm : (x ∈ projLast (finalC X)) ↔
      ∃ t : ℝ, t ≠ 0 ∧ ¬ ∃ y ∈ X, ∑ j : Fin n, (y j - x j) ^ 2 ≤ t ^ 2 := by
    rw [projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      have ht1 : t ≠ 0 := by
        have h := ht.1
        rwa [Set.mem_ofPred_eq, Fin.snoc_last] at h
      refine ⟨t, ht1, ?_⟩
      rintro ⟨y, hyX, hy⟩
      obtain ⟨u, huX, hu⟩ := (exists_u_iff x t).mpr ⟨y, hyX, hy⟩
      refine ht.2 ?_
      rw [WilG5.projN, Set.mem_ofPred_eq]
      exact ⟨u, (happ x t u).mpr (by rw [sub_eq_zero]; exact ⟨huX, hu⟩)⟩
    · rintro ⟨t, ht1, ht2⟩
      refine ⟨t, ?_, ?_⟩
      · rwa [Set.mem_ofPred_eq, Fin.snoc_last]
      · rw [Set.mem_compl_iff, WilG5.projN, Set.mem_ofPred_eq]
        rintro ⟨u, hu⟩
        have hu' := (happ x t u).mp hu
        rw [sub_eq_zero] at hu'
        exact ht2 ((exists_u_iff x t).mp ⟨u, hu'.1, hu'.2⟩)
  rw [hm]
  constructor
  · rintro ⟨t, ht1, ht2⟩ hforall
    obtain ⟨y, hyX, hy⟩ := hforall t ht1
    exact ht2 ⟨y, hyX, hy⟩
  · intro h
    by_contra hcon
    apply h
    intro r hr
    by_contra hno
    exact hcon ⟨r, hr, hno⟩

/-! ## 4. Intersections at a common format -/

/-- Binary intersection with a `Fin 2`-indexed degree family: the format stays `F + 1` and the
degree is the *sum* of the two degrees (no `max`, so the bookkeeping is linear). -/
theorem interTwo {S : SOMin} {n F D₁ D₂ : ℕ} {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F D₁ n) (hY : Y ∈ S.Ω F D₂ n) :
    X ∩ Y ∈ S.Ω (F + 1) (D₁ + D₂) n := by
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y) (by
      intro i
      fin_cases i
      · simpa using hX
      · simpa using hY)
  rw [show (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; simp] at h
  rw [show (⋂ i : Fin 2, (if i = 0 then X else Y)) = X ∩ Y from by
    ext z; simp [Fin.forall_fin_two]] at h
  exact h

/-! ## 5. The `Ω`-membership of `finalC X` -/

theorem finalC_mem {S : SOMin} {n a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) :
    finalC X ∈ S.Ω (a + 3 * n + 9) (b.eval D + 3) (n + 1) := by
  -- the two members at a common format
  have hCYL : cylSet X ∈ S.Ω (a + 2 * n + 5) (b.eval D) (n + (n + 1) + 1) :=
    WilG5.mem_mono (cylSet_mem (S := S) hX) _ _ (by omega) le_rfl
  have hHYP : hypSet n ∈ S.Ω (a + 2 * n + 5) ((Polynomial.C 2).eval D) (n + (n + 1) + 1) := by
    rw [show (Polynomial.C 2 : Polynomial ℕ).eval D = 2 from by rw [Polynomial.eval_C]]
    exact WilG5.mem_mono (hypSet_mem (S := S) n) _ _ (by omega) le_rfl
  have hJ : bigJ X ∈ S.Ω (a + 2 * n + 6) (b.eval D + 2) (n + (n + 1) + 1) := by
    have h := interTwo (S := S) hCYL hHYP
    rw [show (b.eval D) + (Polynomial.C 2 : Polynomial ℕ).eval D = b.eval D + 2 from by
      rw [Polynomial.eval_C]] at h
    exact h
  -- transport to the `(n+1) + (n+1)` layout and project out `(y, s)`
  have hT : (bigSpace_eq n ▸ bigJ X) ∈ S.Ω (a + 2 * n + 6) (b.eval D + 2) ((n + 1) + (n + 1)) :=
    WilG5.omega_ndrec (bigSpace_eq n) hJ
  have hP : WilG5.projN (n + 1) (bigSpace_eq n ▸ bigJ X) ∈
      S.Ω (a + 2 * n + 6 + (n + 1)) (b.eval D + 2) (n + 1) :=
    WilG5.projN_mem (S := S) (n + 1) _ _ hT
  have hB : (WilG5.projN (n + 1) (bigSpace_eq n ▸ bigJ X))ᶜ ∈
      S.Ω (a + 3 * n + 8) (b.eval D + 2) (n + 1) := by
    have h := S.compl hP
    exact WilG5.mem_mono h _ _ (by omega) le_rfl
  -- the condition `r ≠ 0`
  have hNE : {v : Fin (n + 1) → ℝ | v (Fin.last n) ≠ 0} ∈
      S.Ω (a + 3 * n + 8) ((Polynomial.C 1).eval D) (n + 1) := by
    have h0 : {v : Fin (n + 1) → ℝ |
        MvPolynomial.eval v (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ) = 0} ∈
        S.Ω (n + 1) ((Polynomial.C 1).eval D) (n + 1) := by
      rw [show (Polynomial.C 1 : Polynomial ℕ).eval D = 1 from by rw [Polynomial.eval_C]]
      simpa using S.hyp (n + 1) (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ)
    have h1 := S.compl h0
    have he : {v : Fin (n + 1) → ℝ | MvPolynomial.eval v
        (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ) = 0}ᶜ =
        {v : Fin (n + 1) → ℝ | v (Fin.last n) ≠ 0} := by
      ext v; simp
    rw [he] at h1
    exact WilG5.mem_mono h1 _ _ (by omega) le_rfl
  -- the intersection is `finalC X`
  have hC := interTwo (S := S) hNE hB
  have hdeg : (Polynomial.C 1 : Polynomial ℕ).eval D + (b.eval D + 2) = b.eval D + 3 := by
    rw [Polynomial.eval_C]
    omega
  rw [hdeg] at hC
  exact WilG5.mem_mono hC _ _ (by omega) le_rfl

/-! ## 6. The assembly, conditional on the two reading facts -/

theorem closure_mem_of {S : SOMin} {n : ℕ} {a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hchar : ClosureReading X) (happ : AppendReading X) (hX : X ∈ S.Ω a (b.eval D) n) :
    closure X ∈ S.Ω (a + 3 * n + 40) ((Polynomial.C 12 * b + Polynomial.C 60).eval D) n := by
  have h1 := finalC_mem (S := S) hX
  have h2 : (projLast (finalC X))ᶜ ∈ S.Ω (a + 3 * n + 9 + 1 + 1) (b.eval D + 3) n :=
    S.compl (S.proj h1)
  rw [projLast_finalC_eq_of happ hchar, compl_compl] at h2
  refine WilG5.mem_mono h2 _ _ (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Work.WilG1.Calc
