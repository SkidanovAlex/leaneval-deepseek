/-
  WilE8 / Hyp — the semi-Pfaffian model of a hyperplane `{Q = 0} ⊆ ℝⁿ`.

  The `*`-set machinery works with `psiV ⁻¹' Z`, where `psiV x i = xᵢ/√(1+xᵢ²)` maps `ℝⁿ`
  onto the open cube.  A polynomial equation `Q = 0` on `ℝⁿ` becomes the equation
  `(clearDenom Q)(u, w) = 0` on the pair `(u, w) = (psiV x, √(1 - (psiV x)²))`, which is
  *semialgebraic* in the `2n` variables `(u, w)`.  Together with the equations
  `uᵢ² + wᵢ² = 1` and the sign conditions `wᵢ > 0` this describes exactly the graph of
  `x ↦ (psiV x, √(1 - (psiV x)²))`, so the projection to the first `n` coordinates is
  `psiV '' {Q = 0}`.

  This file contains the definitions; the elementary evaluation lemmas are in
  `Submission.Work.WilE8.Hyp.Eval`, and the two set inclusions and the degree bound are
  stated and proved in the sibling modules.
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Clear.clearDenom_eval
import Submission.Work.WilE8.Clear.clearDenom_totalDegree_le
import Submission.Work.WilE1.Basic
import Submission.Work.WilE10.Psi

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE8.Hyp

open WilkiesDesign WilkiesDesign.E

/-! ## The variables of `clearDenom` inside `Fin (n+n) ⊕ Fin 0` -/

/-- The variable map `(yᵢ, wᵢ) ↦ (yᵢ, wᵢ)` from the variables of `clearDenom`
(`Fin n ⊕ Fin n`, first the `y`'s then the `w`'s) into the `2n` coordinates of `hyperPF`. -/
def clrVar (n : ℕ) : Fin n ⊕ Fin n → Fin (n + n) ⊕ Fin 0 :=
  Sum.inl ∘ finSumFinEquiv

/-- `clearDenom Q`, viewed as an `EA`-polynomial in the `2n` coordinates `(u, w)`. -/
def clrPoly {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) : EAPoly (n + n) 0 :=
  MvPolynomial.rename (clrVar n) (Work.WilE8.clearDenom Q)

/-- The equation `uᵢ² + wᵢ² = 1` in the `2n` coordinates. -/
def sqPoly (n : ℕ) (i : Fin n) : EAPoly (n + n) 0 :=
  MvPolynomial.X (Sum.inl (Fin.castAdd n i)) ^ 2 +
    MvPolynomial.X (Sum.inl (Fin.natAdd n i)) ^ 2 - 1

/-- The strict inequality `wᵢ > 0` in the `2n` coordinates. -/
def wPoly (n : ℕ) (i : Fin n) : EAPoly (n + n) 0 :=
  MvPolynomial.X (Sum.inl (Fin.natAdd n i))

/-- The semi-Pfaffian set in `ℝ^{n+n}` whose projection to the first `n` coordinates is
`psiV '' {x | Q x = 0}`.  Its format is `2n` (semialgebraic, so `r = 0`). -/
def hyperPF {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) : SemiPf (n + n) :=
  ⟨0, EAChain.nil (n + n),
    [⟨List.ofFn (sqPoly n) ++ [clrPoly Q], List.ofFn (wPoly n)⟩]⟩

/-! ## Elementary evaluation lemmas -/

/-- Evaluation of the equation `uᵢ² + wᵢ² = 1`. -/
theorem eaEval_sqPoly (n : ℕ) (i : Fin n) (z : Fin (n + n) → ℝ) :
    eaEval (EAChain.nil (n + n)) (sqPoly n i) z
      = z (Fin.castAdd n i) ^ 2 + z (Fin.natAdd n i) ^ 2 - 1 := by
  rw [Work.WilE1.eaEval_nil]
  simp only [sqPoly, map_add, map_sub, map_pow, Work.WilE1.eaPolyEquiv_X_inl, map_one]
  simp

/-- Evaluation of the sign condition `wᵢ > 0`. -/
theorem eaEval_wPoly (n : ℕ) (i : Fin n) (z : Fin (n + n) → ℝ) :
    eaEval (EAChain.nil (n + n)) (wPoly n i) z = z (Fin.natAdd n i) := by
  rw [Work.WilE1.eaEval_nil]
  simp only [wPoly, Work.WilE1.eaPolyEquiv_X_inl]
  simp

/-- The transported polynomial of `clrPoly Q` is `clearDenom Q` renamed along the
coordinate identification `Fin n ⊕ Fin n ≃ Fin (n+n)`. -/
theorem eaPolyEquiv_clrPoly (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    Work.WilE1.eaPolyEquiv (n + n) (clrPoly Q)
      = MvPolynomial.rename (finSumFinEquiv : Fin n ⊕ Fin n → Fin (n + n))
          (Work.WilE8.clearDenom Q) := by
  rw [clrPoly, clrVar, Work.WilE1.eaPolyEquiv_apply, MvPolynomial.rename_rename]
  rfl

/-- Evaluation of the cleared-denominator equation at `z`. -/
theorem eaEval_clrPoly (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (z : Fin (n + n) → ℝ) :
    eaEval (EAChain.nil (n + n)) (clrPoly Q) z
      = MvPolynomial.eval (fun v : Fin n ⊕ Fin n => z (finSumFinEquiv v))
          (Work.WilE8.clearDenom Q) := by
  rw [Work.WilE1.eaEval_nil, clrPoly, clrVar, Work.WilE1.eaPolyEquiv_apply,
    MvPolynomial.rename_rename, MvPolynomial.eval_rename]
  rfl

/-- **Membership in `hyperPF Q`.**  A point `z ∈ ℝ^{n+n}` lies in the set of `hyperPF Q`
iff it is in the closed cube, the equations `uᵢ² + wᵢ² = 1` hold, the cleared denominator
equation holds, and the sign conditions `wᵢ > 0` hold. -/
theorem mem_hyperPF_set {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) (z : Fin (n + n) → ℝ) :
    z ∈ (hyperPF Q).set ↔
      z ∈ cubeC (n + n) ∧
      (∀ i : Fin n, z (Fin.castAdd n i) ^ 2 + z (Fin.natAdd n i) ^ 2 = 1) ∧
      MvPolynomial.eval (fun v : Fin n ⊕ Fin n => z (finSumFinEquiv v))
        (Work.WilE8.clearDenom Q) = 0 ∧
      (∀ i : Fin n, 0 < z (Fin.natAdd n i)) := by
  simp only [hyperPF, SemiPf.set, Basic.holds, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, B, hB, h1, h2⟩
    have hBeq : B = ⟨List.ofFn (sqPoly n) ++ [clrPoly Q], List.ofFn (wPoly n)⟩ :=
      List.mem_singleton.mp hB
    subst hBeq
    refine ⟨hz, fun i => ?_, ?_, fun i => ?_⟩
    · have hsqi := h1 (sqPoly n i) (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)))
      rw [eaEval_sqPoly] at hsqi
      linarith
    · have hclr := h1 (clrPoly Q) (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      rwa [eaEval_clrPoly] at hclr
    · have hw := h2 (wPoly n i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
      rwa [eaEval_wPoly] at hw
  · rintro ⟨hz, h1, h2, h3⟩
    refine ⟨hz, ⟨List.ofFn (sqPoly n) ++ [clrPoly Q], List.ofFn (wPoly n)⟩,
      List.mem_singleton.mpr rfl, ?_, ?_⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
        rw [eaEval_sqPoly]
        linarith [h1 i]
      · rw [List.mem_singleton.mp hf, eaEval_clrPoly]
        exact h2
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      rw [eaEval_wPoly]
      exact h3 i

end Work.WilE8.Hyp
