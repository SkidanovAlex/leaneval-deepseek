/-
  WilG1/Choice/AffLast — the affine substitution atom.

  For a set `K ⊆ ℝ^{p+1}` in `S.Ω`, an affine functional `L` and a constant `c`, the set of
  parameters `y ∈ ℝ^N` whose associated point
  `Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) (∑ i, L i * y i + c)` lies in `K` is again
  an `Ω`-set: lift `K` onto the last `p+1` coordinates of `ℝ^{N+(p+1)}` (format `a+N`), cut out
  the graph of the affine map by the single polynomial
  `∑_{i<p} (w_i - y_i)² + (w_last - ∑ L_i y_i - c)²` of total degree `2`, and project the
  `p+1` fresh coordinates away.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice

open WilkiesDesign WilkiesConjecture

/-! ## 1. Degree bookkeeping -/

theorem td_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N) ℝ) {C : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ C) : (∑ i ∈ s, f i).totalDegree ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (hf a (Finset.mem_insert_self a s)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

theorem td_sq_le {N : ℕ} {P : MvPolynomial (Fin N) ℝ} (h : P.totalDegree ≤ 1) :
    (P ^ 2).totalDegree ≤ 2 := by
  rw [pow_two]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  omega

theorem td_X_sub_X_le {N : ℕ} (i j : Fin N) :
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_of_eq (MvPolynomial.totalDegree_X i), le_of_eq (MvPolynomial.totalDegree_X j)⟩

theorem td_lin_le {N M : ℕ} (L : Fin N → ℝ) (e : Fin N → Fin M) :
    (∑ i : Fin N, MvPolynomial.C (L i) * MvPolynomial.X (e i) :
      MvPolynomial (Fin M) ℝ).totalDegree ≤ 1 := by
  refine le_trans (td_sum_le Finset.univ _ (C := 1) ?_) le_rfl
  intro i _
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact le_of_eq (MvPolynomial.totalDegree_X (e i))

/-! ## 2. Lifting onto the last coordinates of the more convenient index type -/

theorem liftLastN_mem {S : SOMin} {n N F Dn : ℕ} {A : Set (Fin n → ℝ)} (hA : A ∈ S.Ω F Dn n) :
    {z : Fin (N + n) → ℝ | (fun j : Fin n => z (Fin.natAdd N j)) ∈ A} ∈
      S.Ω (F + N) Dn (N + n) := by
  have h := WilG5.liftLast_mem (S := S) N F Dn hA
  have h2 := WilG5.omega_ndrec (S := S) (Nat.add_comm n N) h
  have he : (Nat.add_comm n N) ▸ WilG5.liftLast N A =
      {z : Fin (N + n) → ℝ | (fun j : Fin n => z (Fin.natAdd N j)) ∈ A} := by
    ext z
    have h1 : z ∈ ((Nat.add_comm n N) ▸ WilG5.liftLast N A) ↔
        (fun i : Fin (n + N) => z (Fin.cast (Nat.add_comm n N) i)) ∈ WilG5.liftLast N A :=
      WilG5.mem_ndrec (Nat.add_comm n N) (WilG5.liftLast N A) z
    rw [h1]
    have hfun : (fun i : Fin n => z (Fin.cast (Nat.add_comm n N) (WilG5.lidx N i))) =
        (fun j : Fin n => z (Fin.natAdd N j)) := by
      funext j
      congr 1
    simp only [WilG5.liftLast, Set.mem_ofPred_eq]
    rw [hfun]
  rw [he] at h2
  exact h2

/-! ## 3. The affine atom -/

theorem affAtom_mem {S : SOMin} {p N : ℕ} (hp : p ≤ N) {a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) (L : Fin N → ℝ) (c : ℝ) :
    {y : Fin N → ℝ |
      Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) ((∑ i : Fin N, L i * y i) + c) ∈ K} ∈
      S.Ω (max (a + N) (N + (p + 1)) + 1 + (p + 1)) ((b + Polynomial.C 2).eval D) N := by
  set P : MvPolynomial (Fin (N + (p + 1))) ℝ :=
    (∑ i : Fin p, (MvPolynomial.X (Fin.natAdd N (Fin.castSucc i)) -
        MvPolynomial.X (Fin.castAdd (p + 1) (Fin.castLE hp i))) ^ 2) +
      (MvPolynomial.X (Fin.natAdd N (Fin.last p)) -
        ((∑ i : Fin N, MvPolynomial.C (L i) * MvPolynomial.X (Fin.castAdd (p + 1) i)) +
          MvPolynomial.C c)) ^ 2 with hPdef
  have htd : P.totalDegree ≤ 2 := by
    rw [hPdef]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine td_sum_le Finset.univ _ (C := 2) ?_
      intro i _
      exact td_sq_le (td_X_sub_X_le _ _)
    · refine td_sq_le ?_
      refine le_trans (MvPolynomial.totalDegree_sub _ _)
        (max_le (le_of_eq (MvPolynomial.totalDegree_X _)) ?_)
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le (td_lin_le L _) ?_)
      rw [MvPolynomial.totalDegree_C]
      exact Nat.zero_le 1
  have hLiftL : {z : Fin (N + (p + 1)) → ℝ | (fun j : Fin (p + 1) => z (Fin.natAdd N j)) ∈ K} ∈
      S.Ω (a + N) (b.eval D) (N + (p + 1)) := liftLastN_mem (S := S) hK
  have hHyp : {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0} ∈
      S.Ω (N + (p + 1)) 2 (N + (p + 1)) := Omega.mono (S.hyp _ P) le_rfl htd
  have hI : ({z : Fin (N + (p + 1)) → ℝ | (fun j : Fin (p + 1) => z (Fin.natAdd N j)) ∈ K} ∩
      {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0}) ∈
      S.Ω (max (a + N) (N + (p + 1)) + 1) (b.eval D + 2) (N + (p + 1)) := by
    have h1 : {z : Fin (N + (p + 1)) → ℝ | (fun j : Fin (p + 1) => z (Fin.natAdd N j)) ∈ K} ∈
        S.Ω (max (a + N) (N + (p + 1))) (b.eval D) (N + (p + 1)) :=
      Omega.mono hLiftL (le_max_left _ _) le_rfl
    have h2 : {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0} ∈
        S.Ω (max (a + N) (N + (p + 1))) 2 (N + (p + 1)) :=
      Omega.mono hHyp (le_max_right _ _) le_rfl
    have h := S.inter (fun i : Fin 2 => if i = 0 then b.eval D else 2)
      (fun i : Fin 2 => if i = 0 then
          {z : Fin (N + (p + 1)) → ℝ | (fun j : Fin (p + 1) => z (Fin.natAdd N j)) ∈ K}
        else {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0})
      (by intro i
          fin_cases i
          · simpa using h1
          · simpa using h2)
    rw [Omega.iInter_fin_two] at h
    have hs : (∑ i : Fin 2, (if i = 0 then b.eval D else 2)) = b.eval D + 2 := by
      rw [Fin.sum_univ_two]; simp
    rw [hs] at h
    exact h
  have hProj := WilG5.projN_mem (S := S) (p + 1)
    (max (a + N) (N + (p + 1)) + 1) (b.eval D + 2) hI
  have he : WilG5.projN (p + 1)
        ({z : Fin (N + (p + 1)) → ℝ | (fun j : Fin (p + 1) => z (Fin.natAdd N j)) ∈ K} ∩
          {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0}) =
      {y : Fin N → ℝ |
        Fin.snoc (fun i : Fin p => y (Fin.castLE hp i)) ((∑ i : Fin N, L i * y i) + c) ∈ K} := by
    ext y
    have heval : ∀ w : Fin (p + 1) → ℝ,
        MvPolynomial.eval (Fin.append y w : Fin (N + (p + 1)) → ℝ) P =
          (∑ i : Fin p, (w (Fin.castSucc i) - y (Fin.castLE hp i)) ^ 2) +
            (w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c)) ^ 2 := by
      intro w
      rw [hPdef]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_pow,
        MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
        Fin.append_left, Fin.append_right]
    constructor
    · rintro ⟨w, hw1, hw2⟩
      have hKmem : (fun j : Fin (p + 1) => w j) ∈ K := by
        have h1 : (fun j : Fin (p + 1) =>
            (Fin.append y w : Fin (N + (p + 1)) → ℝ) (Fin.natAdd N j)) ∈ K := hw1
        simpa only [Fin.append_right] using h1
      have hzero : MvPolynomial.eval (Fin.append y w : Fin (N + (p + 1)) → ℝ) P = 0 := hw2
      rw [heval w] at hzero
      have hsq1 : (∑ i : Fin p, (w (Fin.castSucc i) - y (Fin.castLE hp i)) ^ 2) = 0 := by
        nlinarith [Finset.sum_nonneg
          (fun i (_ : i ∈ Finset.univ) => sq_nonneg (w (Fin.castSucc i) - y (Fin.castLE hp i))),
          sq_nonneg (w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c))]
      have hsq2 : (w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c)) ^ 2 = 0 := by
        nlinarith [Finset.sum_nonneg
          (fun i (_ : i ∈ Finset.univ) => sq_nonneg (w (Fin.castSucc i) - y (Fin.castLE hp i))),
          sq_nonneg (w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c))]
      have hcoord : ∀ i : Fin p, w (Fin.castSucc i) = y (Fin.castLE hp i) := by
        intro i
        have h0 : (w (Fin.castSucc i) - y (Fin.castLE hp i)) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j (_ : j ∈ Finset.univ) => sq_nonneg (w (Fin.castSucc j) - y (Fin.castLE hp j))
              )).mp hsq1 i (Finset.mem_univ i)
        have h0' : w (Fin.castSucc i) - y (Fin.castLE hp i) = 0 := by
          nlinarith [sq_nonneg (w (Fin.castSucc i) - y (Fin.castLE hp i))]
        exact sub_eq_zero.mp h0'
      have hlast : w (Fin.last p) = (∑ i : Fin N, L i * y i) + c := by
        have h0' : w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c) = 0 := by
          nlinarith [sq_nonneg (w (Fin.last p) - ((∑ i : Fin N, L i * y i) + c))]
        exact sub_eq_zero.mp h0'
      have hw_eq : w = Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
          ((∑ i : Fin N, L i * y i) + c) := by
        funext j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · simpa only [Fin.snoc_castSucc] using hcoord i
        · simpa only [Fin.snoc_last] using hlast
      rw [show (fun j : Fin (p + 1) => w j) =
          Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
            ((∑ i : Fin N, L i * y i) + c) from funext fun j => congrFun hw_eq j] at hKmem
      exact hKmem
    · intro hy
      set W : Fin (p + 1) → ℝ := Fin.snoc (fun i : Fin p => y (Fin.castLE hp i))
        ((∑ i : Fin N, L i * y i) + c) with hWdef
      refine ⟨W, ?_, ?_⟩
      · show (fun j : Fin (p + 1) => (Fin.append y W : Fin (N + (p + 1)) → ℝ) (Fin.natAdd N j)) ∈ K
        have hfun : (fun j : Fin (p + 1) =>
            (Fin.append y W : Fin (N + (p + 1)) → ℝ) (Fin.natAdd N j)) = W := by
          funext j
          rw [Fin.append_right]
        rw [hfun, hWdef]
        exact hy
      · show (Fin.append y W : Fin (N + (p + 1)) → ℝ)
          ∈ {z : Fin (N + (p + 1)) → ℝ | MvPolynomial.eval z P = 0}
        show MvPolynomial.eval (Fin.append y W : Fin (N + (p + 1)) → ℝ) P = 0
        rw [heval W]
        have h1 : ∀ i : Fin p, W (Fin.castSucc i) = y (Fin.castLE hp i) := by
          intro i
          rw [hWdef, Fin.snoc_castSucc]
        have h2 : W (Fin.last p) = (∑ i : Fin N, L i * y i) + c := by
          rw [hWdef, Fin.snoc_last]
        rw [Finset.sum_congr rfl (fun i _ => by rw [h1 i]), h2]
        simp
  rw [he] at hProj
  refine Omega.mono hProj le_rfl ?_
  rw [Polynomial.eval_add, Polynomial.eval_C]

end Work.WilG1.Choice
