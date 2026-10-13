import Mathlib
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4a.liftNM_mem
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG4c.CritAux.hypoRaw_eq_hypoRawE
import Submission.Work.WilG4c.CritAux.hypoBuild_eq_hypoRawE

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.CritAux

open WilkiesDesign

/-! ## The `Ω`-membership of the condensation construction

The set `HypoBuild p n X` is built from `X` by six `Ω`-operations; the only non-trivial
bookkeeping is the format/degree accounting.  This part of the file does not use
`HypoRaw`/`HypoRawE` at all. -/

/-- The total degree of the ball polynomial is at most two, uniformly in `p, n`. -/
theorem ballP_totalDegree_le (p n : ℕ) : (Work.WilkG4c.ballP p n).totalDegree ≤ 2 := by
  have hX2 : (MvPolynomial.X (Fin.castAdd (n + 1) (Fin.last (Work.WilkG4c.hypoN p n))) ^ 2 :
      MvPolynomial (Fin (Work.WilkG4c.hypoM p n)) ℝ).totalDegree ≤ 2 := by
    rw [MvPolynomial.totalDegree_X_pow]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      ((MvPolynomial.X (Fin.natAdd (Work.WilkG4c.hypoN p n + 1) j) -
        MvPolynomial.X (Fin.castAdd (n + 1)
          (Fin.castSucc (Fin.natAdd p j)))) ^ 2 :
          MvPolynomial (Fin (Work.WilkG4c.hypoM p n)) ℝ).totalDegree ≤ 2 := by
    intro j _
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    have hsub : ((MvPolynomial.X (Fin.natAdd (Work.WilkG4c.hypoN p n + 1) j) -
        MvPolynomial.X (Fin.castAdd (n + 1)
          (Fin.castSucc (Fin.natAdd p j)))) :
          MvPolynomial (Fin (Work.WilkG4c.hypoM p n)) ℝ).totalDegree ≤ 1 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans ?_
      rw [max_le_iff]
      exact ⟨by simp, by simp⟩
    calc 2 * ((MvPolynomial.X (Fin.natAdd (Work.WilkG4c.hypoN p n + 1) j) -
        MvPolynomial.X (Fin.castAdd (n + 1)
          (Fin.castSucc (Fin.natAdd p j)))) :
          MvPolynomial (Fin (Work.WilkG4c.hypoM p n)) ℝ).totalDegree ≤ 2 * 1 :=
          Nat.mul_le_mul_left 2 hsub
      _ = 2 := by norm_num
  unfold Work.WilkG4c.ballP
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [max_le_iff]
  exact ⟨hX2, MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ) hterm⟩

/-- Binary intersection with independent formats and degrees. -/
theorem omega_inter2' {S : WilkiesDesign.SOMin} {n : ℕ} {A B : Set (Fin n → ℝ)}
    {F₁ F₂ D₁ D₂ : ℕ} (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∩ B ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : A ∈ S.Ω (max F₁ F₂) D₁ n := Work.WilG4a.mem_mono hA (le_max_left _ _) le_rfl
  have h2 : B ∈ S.Ω (max F₁ F₂) D₂ n := Work.WilG4a.mem_mono hB (le_max_right _ _) le_rfl
  have h := S.inter (F := max F₁ F₂) (n := n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by intro i; fin_cases i
        · simpa using h1
        · simpa using h2)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; norm_num
  rw [hsum] at h
  rw [Work.WilG1.Omega.iInter_fin_two A B] at h
  exact h

/-- The core `Ω`-statement: `HypoBuild p n X` is an `Ω`-set with format `F + a₀` and degree
`D + 9` whenever `X ∈ S.Ω F D`, where `a₀ = 3·hypoM + 3·hypoN + (n+1) + 12`. -/
theorem HypoBuild_mem (S : WilkiesDesign.SOMin) (p n F D : ℕ)
    (X : Set (Fin (p + (n + 1)) → ℝ)) (hX : X ∈ S.Ω F D (p + (n + 1))) :
    Work.WilkG4c.HypoBuild p n X ∈
      S.Ω (F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12))
        (D + 9) (p + (n + 1)) := by
  have hXc : Xᶜ ∈ S.Ω (F + 1) D (Work.WilkG4c.hypoN p n) := S.compl hX
  -- The pullback of `Xᶜ` along the substitution `w ↦ w ∘ iotaA`.
  have hA : Work.WilkG4c.HypoA p n X ∈
      S.Ω ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
        (D + 2) (Work.WilkG4c.hypoM p n) :=
    Work.WilG4a.subst_mem S (Work.WilkG4c.iotaA p n) hXc
  -- The ball positivity locus.
  have hBall : Work.WilkG4c.HypoBall p n ∈
      S.Ω (Work.WilkG4c.hypoM p n + 2) 4 (Work.WilkG4c.hypoM p n) := by
    have h0 : Work.WilkG4c.HypoBall p n ∈
        S.Ω (Work.WilkG4c.hypoM p n + 2)
          ((Work.WilkG4c.ballP p n).totalDegree + 2) (Work.WilkG4c.hypoM p n) := by
      simpa [Work.WilkG4c.HypoBall, Polynomial.eval_C] using
        Work.WilG1.Calc.pos_mem (S := S) D (Work.WilkG4c.ballP p n)
    refine Work.WilG4a.mem_mono h0 le_rfl ?_
    have := ballP_totalDegree_le p n
    omega
  -- `Z = A ∩ Ball`.
  have hZ : Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n ∈
      S.Ω (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1) (D + 6) (Work.WilkG4c.hypoM p n) := by
    have h := omega_inter2' hA hBall
    exact h
  -- Project the `y`-block away.
  have hPY : Work.WilG0.projLastIter (Work.WilkG4c.hypoN p n + 1) (n + 1)
        (Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n) ∈
      S.Ω (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1)) (D + 6)
          (Work.WilkG4c.hypoN p n + 1) :=
    Work.WilG4a.projLastIter_mem (S := S) hZ
  -- Complement.
  have hC : (Work.WilG0.projLastIter (Work.WilkG4c.hypoN p n + 1) (n + 1)
        (Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n))ᶜ ∈
      S.Ω (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1) (D + 6)
          (Work.WilkG4c.hypoN p n + 1) :=
    S.compl hPY
  -- The condition `r > 0`.
  have hPos : {u : Fin (Work.WilkG4c.hypoN p n + 1) → ℝ |
        0 < u (Fin.last (Work.WilkG4c.hypoN p n))} ∈
      S.Ω (Work.WilkG4c.hypoN p n + 3) 3 (Work.WilkG4c.hypoN p n + 1) := by
    have h0 := Work.WilG1.Calc.pos_mem (S := S) D
      (MvPolynomial.X (Fin.last (Work.WilkG4c.hypoN p n)) :
        MvPolynomial (Fin (Work.WilkG4c.hypoN p n + 1)) ℝ)
    have hset : {x : Fin (Work.WilkG4c.hypoN p n + 1) → ℝ |
          0 < (MvPolynomial.eval x)
            (MvPolynomial.X (Fin.last (Work.WilkG4c.hypoN p n)) :
              MvPolynomial (Fin (Work.WilkG4c.hypoN p n + 1)) ℝ)}
        = {u : Fin (Work.WilkG4c.hypoN p n + 1) → ℝ |
            0 < u (Fin.last (Work.WilkG4c.hypoN p n))} := by
      ext x; simp [MvPolynomial.eval_X]
    rw [hset] at h0
    refine Work.WilG4a.mem_mono h0 (by omega) ?_
    simp only [Polynomial.eval_C, MvPolynomial.totalDegree_X]
    omega
  -- `S7 = Cᶜ ∩ {r > 0}`.
  have hS7 : ((Work.WilG0.projLastIter (Work.WilkG4c.hypoN p n + 1) (n + 1)
        (Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n))ᶜ
      ∩ {u : Fin (Work.WilkG4c.hypoN p n + 1) → ℝ |
          0 < u (Fin.last (Work.WilkG4c.hypoN p n))}) ∈
      S.Ω (max (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1)
            (Work.WilkG4c.hypoN p n + 3) + 1) (D + 9) (Work.WilkG4c.hypoN p n + 1) := by
    have h := omega_inter2' hC hPos
    exact h
  -- Project `r` away.
  have hFin : WilkiesDesign.projLast (((Work.WilG0.projLastIter (Work.WilkG4c.hypoN p n + 1)
        (n + 1) (Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n))ᶜ)
      ∩ {u : Fin (Work.WilkG4c.hypoN p n + 1) → ℝ |
          0 < u (Fin.last (Work.WilkG4c.hypoN p n))}) ∈
      S.Ω (max (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1)
            (Work.WilkG4c.hypoN p n + 3) + 1 + 1) (D + 9) (Work.WilkG4c.hypoN p n) :=
    S.proj hS7
  -- Bound the accumulated format expression.
  have key : max (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1)
            (Work.WilkG4c.hypoN p n + 3) + 1 + 1
      ≤ F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12) := by
    have h1 : max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
          (Work.WilkG4c.hypoM p n + 2)
        ≤ F + (2 * Work.WilkG4c.hypoM p n + 2 * Work.WilkG4c.hypoN p n + 2)
            + (Work.WilkG4c.hypoM p n + 2) := by
      rw [max_le_iff]; constructor <;> omega
    have h2 : max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
          (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1
        ≤ F + (2 * Work.WilkG4c.hypoM p n + 2 * Work.WilkG4c.hypoN p n + 2)
            + (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1 := by
      omega
    have h3 : max (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1) (Work.WilkG4c.hypoN p n + 3)
        ≤ F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 10) := by
      rw [max_le_iff]; constructor
      · omega
      · omega
    omega
  have hFinal : Work.WilkG4c.HypoBuild p n X ∈
      S.Ω (F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12))
        (D + 9) (p + (n + 1)) := by
    have hb : Work.WilkG4c.HypoBuild p n X ∈
        S.Ω (max (max ((F + 1) + 2 * (Work.WilkG4c.hypoM p n + Work.WilkG4c.hypoN p n) + 1)
            (Work.WilkG4c.hypoM p n + 2) + 1 + (n + 1) + 1)
            (Work.WilkG4c.hypoN p n + 3) + 1 + 1) (D + 9) (Work.WilkG4c.hypoN p n) := hFin
    exact Work.WilG4a.mem_mono hb key le_rfl
  exact hFinal

theorem hypoRaw_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)),
      X ∈ S.Ω F D (p + (n + 1)) →
      Work.WilkG4c.HypoRaw p n X ∈ S.Ω (F + a) (b.eval D) (p + (n + 1)) := by
  refine ⟨3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12,
    Polynomial.X + Polynomial.C 9, ?_⟩
  intro F D X hX
  have hbuild := HypoBuild_mem S p n F D X hX
  have hraw : Work.WilkG4c.HypoRaw p n X ∈
      S.Ω (F + (3 * Work.WilkG4c.hypoM p n + 3 * Work.WilkG4c.hypoN p n + (n + 1) + 12))
        (D + 9) (p + (n + 1)) := by
    rw [Work.WilG4c.CritAux.hypoRaw_eq_hypoRawE p n X,
        ← Work.WilG4c.CritAux.hypoBuild_eq_hypoRawE p n X]
    exact hbuild
  refine Work.WilG4a.mem_mono hraw le_rfl ?_
  simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

end Work.WilG4c.CritAux
