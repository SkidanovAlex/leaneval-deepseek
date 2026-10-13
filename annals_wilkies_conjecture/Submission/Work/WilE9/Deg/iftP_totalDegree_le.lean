import Mathlib
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.EaD.eaD_totalDegree_le
import Submission.Work.WilE2.Lift

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open WilkiesDesign WilkiesDesign.E

namespace Work.WilE9.Deg

/-! ## Degree bookkeeping for the implicit-derivative polynomials `iftP`

Everything here is a bound on `MvPolynomial.totalDegree`.  The key point of the recursion
defining `iftP` is that every ingredient is either

* `jQ c F = det (∂F/∂y)`, of degree `≤ ∑ j, (F j).totalDegree =: D`,
* `jc c F l i` — a sum of products `adjugate · (∂F)` — of degree `≤ 2 * D`,
* or a symbolic derivative `eaD`, which never raises the degree (`eaD_totalDegree_le`),

so that one recursion step raises the degree by at most `3 * D`.  The advertised increment
`4 * (q^3 + q^2 + q + 1) * (D + 1)` is far larger than `3 * D`, so the estimate is additive. -/

/-- The determinant of a matrix of polynomials is bounded in degree by the sum of a *row-wise*
bound on the entries (transpose of `Work.WilE2.Matrix.det_totalDegree_le`). -/
theorem det_totalDegree_le_row {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Type*}
    (M : Matrix ι ι (MvPolynomial σ ℝ)) (b : ι → ℕ)
    (hb : ∀ i j, (M i j).totalDegree ≤ b i) :
    (M.det).totalDegree ≤ ∑ i, b i := by
  have h := Work.WilE2.Matrix.det_totalDegree_le M.transpose b (fun i j => hb j i)
  rwa [Matrix.det_transpose] at h

/-- Each entry of the fibre Jacobian has degree at most that of the corresponding equation. -/
theorem jm_totalDegree_le {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r)
    (j l : Fin q) : ((Work.WilE9.jm c F) j l).totalDegree ≤ (F j).totalDegree :=
  Work.WilE9.EaD.eaD_totalDegree_le c (Fin.natAdd n l) (F j)

/-- `Q = det (∂F/∂y)` has degree at most the sum of the degrees of the equations. -/
theorem jQ_totalDegree_le {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r) :
    (Work.WilE9.jQ c F).totalDegree ≤ ∑ j : Fin q, (F j).totalDegree := by
  rw [Work.WilE9.jQ]
  exact det_totalDegree_le_row (Work.WilE9.jm c F) (fun j => (F j).totalDegree)
    (fun i j => jm_totalDegree_le c F i j)

/-- The adjugate entries obey the same bound as `Q` itself: they are determinants of matrices
whose entries are either entries of `∂F/∂y` or `0`/`1`. -/
theorem adjugate_totalDegree_le {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (l j : Fin q) :
    ((Work.WilE9.jm c F).adjugate l j).totalDegree ≤ ∑ i : Fin q, (F i).totalDegree := by
  rw [Matrix.adjugate_apply]
  refine det_totalDegree_le_row _ (fun i => (F i).totalDegree) (fun i k => ?_)
  by_cases h : i = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases hk : k = l
    · subst hk; rw [Pi.single_eq_same, MvPolynomial.totalDegree_one]; exact Nat.zero_le _
    · rw [Pi.single_apply, if_neg hk, MvPolynomial.totalDegree_zero]; exact Nat.zero_le _
  · rw [Matrix.updateRow_ne h]
    exact Work.WilE9.EaD.eaD_totalDegree_le c (Fin.natAdd n k) (F i)

/-- The cleared first derivative `jc` has degree at most `2 D`. -/
theorem jc_totalDegree_le {n q r : ℕ} (c : EAChain (n + q) r) (F : Fin q → EAPoly (n + q) r)
    (l : Fin q) (i : Fin n) :
    (Work.WilE9.jc c F l i).totalDegree ≤ 2 * ∑ j : Fin q, (F j).totalDegree := by
  rw [Work.WilE9.jc, MvPolynomial.totalDegree_neg]
  refine MvPolynomial.totalDegree_finsetSum_le (fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 : ((Work.WilE9.jm c F).adjugate l j).totalDegree ≤ ∑ i : Fin q, (F i).totalDegree :=
    adjugate_totalDegree_le c F l j
  have h2 : (Work.WilE9.jb c F j i).totalDegree ≤ ∑ i : Fin q, (F i).totalDegree :=
    (Work.WilE9.EaD.eaD_totalDegree_le c (Fin.castAdd q i) (F j)).trans
      (Finset.single_le_sum (f := fun k => (F k).totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  omega

/-- The degree of the implicit-derivative polynomial grows *additively* in the order: the
content of "sharp derivatives".  `∑ j, (F j).totalDegree` is the sum of the degrees of the
equations.  (Generous bound; `Mathlib`'s `MvPolynomial.totalDegree_add`/`_mul`/`_finsetSum`
plus `Work.WilE9.EaD.eaD_totalDegree_le` are the tools.) -/
theorem iftP_totalDegree_le {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (n + q) r) (l₀ : Fin q) (L : List (Fin n)) :
    (Work.WilE9.iftP c F l₀ L).totalDegree ≤
      ((∑ j : Fin q, (F j).totalDegree) + 1)
        + L.length * (4 * (q * q * q + q * q + q + 1) * ((∑ j : Fin q, (F j).totalDegree) + 1)) := by
  induction L with
  | nil =>
    rw [show Work.WilE9.iftP c F l₀ ([] : List (Fin n)) =
        MvPolynomial.X (Sum.inl (Fin.natAdd n l₀)) from rfl]
    rw [MvPolynomial.totalDegree_X, List.length_nil, Nat.zero_mul, Nat.add_zero]
    omega
  | cons i L ih =>
    set D : ℕ := ∑ j : Fin q, (F j).totalDegree with hD
    set K : ℕ := 4 * (q * q * q + q * q + q + 1) * (D + 1) with hK
    have hS : 1 ≤ q * q * q + q * q + q + 1 := by omega
    have hKD : 3 * D ≤ K := by
      rw [hK]
      nlinarith [hS]
    have hQ : (Work.WilE9.jQ c F).totalDegree ≤ D := by
      rw [hD]
      exact jQ_totalDegree_le c F
    have hjc : ∀ (l : Fin q) (i : Fin n), (Work.WilE9.jc c F l i).totalDegree ≤ 2 * D := by
      intro l i
      rw [hD]
      exact jc_totalDegree_le c F l i
    rw [Work.WilE9.iftP, List.length_cons, Nat.add_mul, one_mul, sub_eq_add_neg]
    set M : ℕ := L.length * K with hM
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        have hQ2 : (Work.WilE9.jQ c F ^ 2).totalDegree ≤ 2 * D := by
          rw [pow_two]
          exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
        have he : (eaD c (Fin.castAdd q i) (Work.WilE9.iftP c F l₀ L)).totalDegree ≤
            (D + 1) + M :=
          (Work.WilE9.EaD.eaD_totalDegree_le c _ _).trans ih
        omega
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        have hsum : (∑ l : Fin q,
              eaD c (Fin.natAdd n l) (Work.WilE9.iftP c F l₀ L) * Work.WilE9.jc c F l i).totalDegree
            ≤ (D + 1) + M + 2 * D := by
          refine MvPolynomial.totalDegree_finsetSum_le (fun l _ => ?_)
          refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          have h1 : (eaD c (Fin.natAdd n l) (Work.WilE9.iftP c F l₀ L)).totalDegree ≤
              (D + 1) + M :=
            (Work.WilE9.EaD.eaD_totalDegree_le c _ _).trans ih
          have h2 : (Work.WilE9.jc c F l i).totalDegree ≤ 2 * D := hjc l i
          omega
        omega
    · rw [MvPolynomial.totalDegree_neg]
      refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have he : (Work.WilE9.iftP c F l₀ L).totalDegree ≤ (D + 1) + M := ih
      have hinner : (Work.WilE9.jQ c F * eaD c (Fin.castAdd q i) (Work.WilE9.jQ c F)
            + ∑ l : Fin q,
                eaD c (Fin.natAdd n l) (Work.WilE9.jQ c F) * Work.WilE9.jc c F l i).totalDegree
            ≤ 3 * D := by
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          have h1 : (eaD c (Fin.castAdd q i) (Work.WilE9.jQ c F)).totalDegree ≤ D :=
            (Work.WilE9.EaD.eaD_totalDegree_le c _ _).trans hQ
          omega
        · refine MvPolynomial.totalDegree_finsetSum_le (fun l _ => ?_)
          refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          have h1 : (eaD c (Fin.natAdd n l) (Work.WilE9.jQ c F)).totalDegree ≤ D :=
            (Work.WilE9.EaD.eaD_totalDegree_le c _ _).trans hQ
          have h2 : (Work.WilE9.jc c F l i).totalDegree ≤ 2 * D := hjc l i
          omega
      omega

end Work.WilE9.Deg
