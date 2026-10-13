import Mathlib
import Submission.Work.WilCrux.OmegaDefs
import Submission.Work.WilG0.API
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG1.Calc.liftNM_mem
import Submission.Work.WilG1.Calc.projLastIter_mem
import Submission.Work.WilG4a.setOf_lt_graph_mem
import Submission.Work.WilCrux.TsetProjEq
import Submission.Work.WilCrux.AbsLtGraphMem
import Submission.Work.WilCrux.TripleMem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- **H1 (shared Omega-bookkeeping).** For a definable family `f` the set of pairs `(w, eta)`
with `eta > 0` such that `f` is uniformly `< eps` in the punctured ball of radius `eta`
around `w` is `Omega`-definable in `R^{a+1}`, with format and degree bounds independent of
`eps`.

This set is the intersection of `{eta > 0}` with the complement of the projection (to
`(w,eta)`) of the `Omega`-set
`{(w,eta,w',z) : dist w w' < eta  /\  z != 0  /\  ||z|| < eta  /\  eps <= |f w' z|}`.
The last condition is expressed from `famGraph f` (the pattern of
`Work.WilG4a.setOf_lt_graph_mem`: compare the graph of `f` with the constant-`eps` graph);
the projections are `SOMin.proj`, the complement is `SOMin.compl`, and `SOMin.mono_F`/`mono_D`
merge the bounds. -/
theorem OmegaModulus (S : WilkiesDesign.SOMin) {a b F D : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F D (a + b + 1)) :
    ∃ (F' : ℕ) (b' : Polynomial ℕ), ∀ (ε : ℝ),
      {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a) ∧
        (∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
          dist (Fin.init p) w' < p (Fin.last a) → z ≠ 0 → ‖z‖ < p (Fin.last a) →
            |f w' z| < ε)} ∈ S.Ω F' (b'.eval D) (a + 1) := by
  -- Format used for both graphs in the comparison lemma, and the two delegated bounds.
  have hAbsEx : ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (D : ℕ) (h : (Fin (a + b) → ℝ) → ℝ),
      graphOf h ∈ S.Ω (max F (a + b + 1)) D (a + b + 1) → ∀ (ε : ℝ),
      {l : Fin (a + b) → ℝ | |h l| < ε} ∈ S.Ω A (q.eval D) (a + b) :=
    AbsLtGraphMem S (n := a + b) (F := max F (a + b + 1))
  obtain ⟨A, q, hAbs⟩ := hAbsEx
  have hTriEx : ∃ (A3 : ℕ) (q3 : Polynomial ℕ), ∀ (D : ℕ),
      {u : Fin ((a + 1) + (a + b)) → ℝ |
          (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
          ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
          ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))} ∈
        S.Ω A3 (q3.eval D) ((a + 1) + (a + b)) :=
    TripleMem S (centreIdx a b) (upperIdx a b) (fibreIdx a b) (etaIdx a b)
  obtain ⟨A3, q3, hTriple⟩ := hTriEx
  have hProjEq : ∀ (ε : ℝ),
      Work.WilG0.projLastIter (a + 1) (a + b) (Tset f ε) =
        {p : Fin (a + 1) → ℝ | ∃ (w' : Fin a → ℝ) (z : Fin b → ℝ),
          (∀ i : Fin a, |Fin.init p i - w' i| < p (Fin.last a)) ∧ z ≠ 0 ∧
          (∀ j : Fin b, |z j| < p (Fin.last a)) ∧ ¬ (|f w' z| < ε)} :=
    fun ε => TsetProjEq f ε
  -- Bookkeeping.
  set Fbig : ℕ := (a + 1) + (a + b) + A + A3 + 40 with hFbig
  set Db : Polynomial ℕ := Polynomial.C 3 + q + q3 with hDb
  refine ⟨Fbig + (a + b) + 3, Polynomial.C 4 * Db, ?_⟩
  intro ε
  have hDbval : Db.eval D = 3 + q.eval D + q3.eval D := by
    rw [hDb]; simp [Polynomial.eval_add]
  -- The three coordinate atoms.
  have hTri : {u : Fin ((a + 1) + (a + b)) → ℝ |
        (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
        ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
        ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))} ∈
      S.Ω A3 (q3.eval D) ((a + 1) + (a + b)) := hTriple D
  -- The complement of the lifted graph-comparison set `|famLift f ·| < ε`.
  have hC : {l : Fin (a + b) → ℝ | |famLift f l| < ε} ∈ S.Ω A (q.eval D) (a + b) :=
    hAbs D (famLift f)
      (by rw [graphOf_famLift]; exact WilG1.Omega.mono hf (le_max_left _ _) le_rfl) ε
  have hLift : {u : Fin ((a + 1) + (a + b)) → ℝ |
        (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k)) ∈
          {l : Fin (a + b) → ℝ | |famLift f l| < ε}} ∈
      S.Ω (A + (a + 1)) (q.eval D) ((a + 1) + (a + b)) :=
    WilG1.Calc.liftNM_mem hC (a + 1)
  have hS4 : {u : Fin ((a + 1) + (a + b)) → ℝ |
        ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)} ∈
      S.Ω (A + (a + 1) + 1) (q.eval D) ((a + 1) + (a + b)) := by
    have h := S.compl hLift
    have hset : ({u : Fin ((a + 1) + (a + b)) → ℝ |
        (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k)) ∈
          {l : Fin (a + b) → ℝ | |famLift f l| < ε}})ᶜ =
        {u : Fin ((a + 1) + (a + b)) → ℝ |
          ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)} := by
      ext u; simp
    rw [hset] at h
    exact h
  -- Raise both to the common bounds.
  have hTri' : {u : Fin ((a + 1) + (a + b)) → ℝ |
        (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
        ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
        ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))} ∈
      S.Ω Fbig (Db.eval D) ((a + 1) + (a + b)) :=
    WilG1.Omega.mono hTri (by rw [hFbig]; omega) (by rw [hDbval]; omega)
  have hS4' : {u : Fin ((a + 1) + (a + b)) → ℝ |
        ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)} ∈
      S.Ω Fbig (Db.eval D) ((a + 1) + (a + b)) :=
    WilG1.Omega.mono hS4 (by rw [hFbig]; omega) (by rw [hDbval]; omega)
  -- Intersect, and identify with `Tset f ε`.
  have hraw : ({u : Fin ((a + 1) + (a + b)) → ℝ |
        (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
        ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
        ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))}) ∩
      {u : Fin ((a + 1) + (a + b)) → ℝ |
        ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)} ∈
      S.Ω (Fbig + 1) ((Db + Db).eval D) ((a + 1) + (a + b)) := by
    have h := WilG1.Omega.inter₂ hTri' hS4'
    rw [max_self] at h
    exact h
  have hTeq : ({u : Fin ((a + 1) + (a + b)) → ℝ |
        (∀ i : Fin a, |u (centreIdx a b i) - u (upperIdx a b i)| < u (etaIdx a b))
        ∧ (fun j : Fin b => u (fibreIdx a b j)) ≠ 0
        ∧ (∀ j : Fin b, |u (fibreIdx a b j)| < u (etaIdx a b))}) ∩
      {u : Fin ((a + 1) + (a + b)) → ℝ |
        ¬ (|famLift f (fun k : Fin (a + b) => u (Fin.natAdd (a + 1) k))| < ε)} = Tset f ε := by
    ext u
    simp only [Tset, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hdeg : (Db + Db).eval D = (Polynomial.C 2 * Db).eval D := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have hI : Tset f ε ∈ S.Ω (Fbig + 1) ((Polynomial.C 2 * Db).eval D) ((a + 1) + (a + b)) := by
    rw [← hTeq, ← hdeg]
    exact hraw
  -- Project the last `a+b` coordinates away and complement.
  have hCompl : (Work.WilG0.projLastIter (a + 1) (a + b) (Tset f ε))ᶜ ∈
      S.Ω (Fbig + 1 + (a + b) + 1) ((Polynomial.C 2 * Db).eval D) (a + 1) :=
    S.compl (WilG1.Calc.projLastIter_mem (a + 1) (a + b) hI)
  -- The positivity piece `{eta > 0}`.
  have hH1 : {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∈
      S.Ω (Fbig + 1 + (a + b) + 1) ((Polynomial.C 2 * Db).eval D) (a + 1) := by
    have h0 := WilG1.Calc.pos_mem (S := S) (m := a + 1) D
      (MvPolynomial.X (Fin.last a) : MvPolynomial (Fin (a + 1)) ℝ)
    have hset : {x : Fin (a + 1) → ℝ |
         0 < MvPolynomial.eval x (MvPolynomial.X (Fin.last a) : MvPolynomial (Fin (a + 1)) ℝ)}
        = {x : Fin (a + 1) → ℝ | 0 < x (Fin.last a)} := by
      ext x; simp
    rw [hset] at h0
    have hD0 : (Polynomial.C (((MvPolynomial.X (Fin.last a) :
          MvPolynomial (Fin (a + 1)) ℝ).totalDegree) + 2)).eval D
        ≤ (Polynomial.C 2 * Db).eval D := by
      rw [Polynomial.eval_C, MvPolynomial.totalDegree_X]
      rw [Polynomial.eval_mul, Polynomial.eval_C, hDbval]
      omega
    exact WilG1.Omega.mono h0 (by rw [hFbig]; omega) hD0
  -- Combine.
  have hFinal : {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
      (Work.WilG0.projLastIter (a + 1) (a + b) (Tset f ε))ᶜ ∈
      S.Ω (Fbig + (a + b) + 3) ((Polynomial.C 4 * Db).eval D) (a + 1) := by
    have h := WilG1.Omega.inter₂ hH1 hCompl
    rw [max_self] at h
    have hd : ((Polynomial.C 2 * Db) + (Polynomial.C 2 * Db)).eval D
        = (Polynomial.C 4 * Db).eval D := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      ring
    rw [hd] at h
    refine WilG1.Omega.mono h ?_ le_rfl
    omega
  -- The set identity, using the projection normal form.
  have hset : {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a) ∧
      (∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        dist (Fin.init p) w' < p (Fin.last a) → z ≠ 0 → ‖z‖ < p (Fin.last a) →
          |f w' z| < ε)}
      = {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
        (Work.WilG0.projLastIter (a + 1) (a + b) (Tset f ε))ᶜ := by
    rw [hProjEq ε]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, ?_⟩
      rintro ⟨w', z, h1, h2, h3, h4⟩
      have hp1 : dist (Fin.init p) w' < p (Fin.last a) := by
        rw [dist_pi_lt_iff h0]
        intro i
        simpa [Real.dist_eq] using h1 i
      have hp3 : ‖z‖ < p (Fin.last a) := by
        rw [pi_norm_lt_iff h0]
        intro j
        simpa [Real.norm_eq_abs] using h3 j
      exact h4 (h w' z hp1 h2 hp3)
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun w' z h1 h2 h3 => ?_⟩
      by_contra hcon
      have hc1 : ∀ i : Fin a, |Fin.init p i - w' i| < p (Fin.last a) := by
        intro i
        have := (dist_pi_lt_iff h0).mp h1 i
        simpa [Real.dist_eq] using this
      have hc3 : ∀ j : Fin b, |z j| < p (Fin.last a) := by
        intro j
        rw [pi_norm_lt_iff h0] at h3
        simpa [Real.norm_eq_abs] using h3 j
      exact h ⟨w', z, hc1, h2, hc3, hcon⟩
  rw [hset]
  exact hFinal

end Work.WilCrux
