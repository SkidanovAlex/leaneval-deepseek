import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## Degree bookkeeping -/

/-- Evaluating a `ℕ`-coefficient polynomial at `![D, ·]` is monotone in the second
coordinate. -/
theorem eval_le_eval (b : MvPolynomial (Fin 2) ℕ) {D m r : ℕ} (hm : m ≤ r) :
    MvPolynomial.eval ![D, m] b ≤ MvPolynomial.eval ![D, r] b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      rw [MvPolynomial.eval_add, MvPolynomial.eval_add]
      exact add_le_add hp hq
  | mul_X p i hp =>
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have hle : ![D, m] i ≤ ![D, r] i := by fin_cases i <;> simp_all
      exact Nat.mul_le_mul hp hle

/-! ## The derivative-graph set of `SharpDeriv` -/

/-- The set that `SOMin.SharpDeriv` exhibits as `Ω`-definable: the graph of the `k`-th
directional derivative of `g` along the multi-index `v`, over the interior of the `C^k`
locus. -/
def dgSet {n : ℕ} (g : (Fin n → ℝ) → ℝ) (k : ℕ) (v : Fin k → Fin n) :
    Set (Fin (n + 1) → ℝ) :=
  {z | Fin.init z ∈ interior {x | ContDiffAt ℝ k g x} ∧
    z (Fin.last n) = iteratedFDeriv ℝ k g (Fin.init z) (fun j => Pi.single (v j) 1)}

/-- Projecting a derivative-graph set onto the base returns the interior of the `C^k` locus. -/
theorem projLast_dgSet {n : ℕ} (g : (Fin n → ℝ) → ℝ) (k : ℕ) (v : Fin k → Fin n) :
    projLast (dgSet g k v) = interior {x : Fin n → ℝ | ContDiffAt ℝ k g x} := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    simp only [dgSet, Set.mem_setOf_eq, Fin.init_snoc] at ht
    exact ht.1
  · intro hx
    refine ⟨iteratedFDeriv ℝ k g x (fun j => Pi.single (v j) 1), ?_⟩
    simp only [dgSet, Set.mem_setOf_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨hx, trivial⟩

/-- **BNZ §2.4 (sharp derivatives), locus form.**  For a family member `f : ℝ^p × ℝ^N → ℝ`
whose graph is `Ω`-bounded with format `F0`, the complement of the interior of its
`C^m`-locus is `Ω`-bounded with a format independent of `D, r` and a degree polynomial in
`D` and `r`. -/
theorem StepBadLoc (S : SOMin) (hder : S.SharpDeriv) (p N F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ),
        famGraph f ∈ S.Ω F0 D (p + N + 1) →
        ∀ m : ℕ, m ≤ r → badLoc f m ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + N) := by
  obtain ⟨a, b, hb⟩ := hder F0 (p + N)
  refine ⟨a + 1 + 1, b, ?_⟩
  intro D r f hf m hm
  by_cases hPN : p + N = 0
  · -- Degenerate ambient space `ℝ^0`: every function is smooth, so the bad locus is empty.
    have hsm : {z : Fin (p + N) → ℝ | ContDiffAt ℝ m (famFun f) z} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      have hg : famFun f = fun _ : Fin (p + N) → ℝ => famFun f z := by
        funext x
        have hxz : x = z := by
          funext i
          exact Fin.elim0 (hPN ▸ i)
        exact congrArg (famFun f) hxz
      rw [hg]
      show ContDiffAt ℝ m (fun _ : Fin (p + N) → ℝ => famFun f z) z
      exact contDiffAt_const
    have hb0 : badLoc f m = ∅ := by
      unfold badLoc cLoc
      rw [hsm, interior_univ]
      exact Set.compl_univ
    rw [hb0]
    have hempty : (∅ : Set (Fin (p + N) → ℝ)) ∈ S.Ω (p + N) 0 (p + N) := by
      have h := S.hyp (p + N) (1 : MvPolynomial (Fin (p + N)) ℝ)
      rw [MvPolynomial.totalDegree_one] at h
      convert h using 1
      ext x
      simp
    exact Work.WilG1.Omega.mono (S := S) hempty (by omega) (Nat.zero_le _)
  · have hmem : graphOf (famFun f) ∈ S.Ω F0 D (p + N + 1) := by
      rw [graphOf_famFun]; exact hf
    have hpN : 0 < p + N := Nat.pos_of_ne_zero hPN
    have hd := hb D (famFun f) hmem m (fun _ : Fin m => (⟨0, hpN⟩ : Fin (p + N)))
    have hproj : cLoc f m ∈ S.Ω (a + 1) (MvPolynomial.eval ![D, m] b) (p + N) := by
      have h' : projLast (dgSet (famFun f) m (fun _ : Fin m => (⟨0, hpN⟩ : Fin (p + N))))
          ∈ S.Ω (a + 1) (MvPolynomial.eval ![D, m] b) (p + N) := S.proj hd
      rw [projLast_dgSet] at h'
      exact h'
    have hcompl : badLoc f m ∈ S.Ω (a + 1 + 1) (MvPolynomial.eval ![D, m] b) (p + N) :=
      S.compl hproj
    exact Work.WilG1.Omega.mono (S := S) hcompl le_rfl (eval_le_eval b hm)

end Work.WilG4c
