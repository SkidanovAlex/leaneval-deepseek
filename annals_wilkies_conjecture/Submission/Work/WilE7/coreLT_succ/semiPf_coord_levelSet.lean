import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FaceAux.InsertCoord

namespace Work.WilE7.coreLT_succ

open WilkiesDesign.E

/-!
  Cutting a restricted semi-Pfaffian set `X ⊆ ℝ^{n+m}` by one coordinate hyperplane
  `π_{n+l} = t` (i.e. `z (natAdd n l) = t`).

  The construction is `Work.WilE7.FaceAux.addEq`: keep the chain of `X` and adjoin the
  equation `x_{n+l} - t = 0` to every basic set.  Nothing about the chain changes, so the
  format is unchanged; the degree grows by `atomDeg (x - t) ≤ 2` per basic set.
-/

/-- Evaluation of the pinning equation `x_i - t` at `z`: it is `z i - t`. -/
theorem eaEval_var_sub {k r : ℕ} (c : EAChain k r) (i : Fin k) (t : ℝ) (z : Fin k → ℝ) :
    eaEval c ((MvPolynomial.X (Sum.inl i) - MvPolynomial.C t : EAPoly k r)) z = z i - t := by
  have hsub : eaEval c (MvPolynomial.X (Sum.inl i) - MvPolynomial.C t : EAPoly k r) z
      = eaEval c (MvPolynomial.X (Sum.inl i) : EAPoly k r) z
        - eaEval c (MvPolynomial.C t : EAPoly k r) z := by
    simp only [eaEval, map_sub]
  rw [hsub]
  simp only [eaEval, MvPolynomial.eval_X, Sum.elim_inl, MvPolynomial.eval_C]

/-- The total degree of the pinning equation `x_i - t` is at most `1`. -/
lemma totalDegree_var_sub_le {k r : ℕ} (i : Fin k) (t : ℝ) :
    (MvPolynomial.X (Sum.inl i) - MvPolynomial.C t : EAPoly k r).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg]
  calc (MvPolynomial.X (Sum.inl i) + -MvPolynomial.C t : EAPoly k r).totalDegree
      ≤ max (MvPolynomial.X (Sum.inl i) : EAPoly k r).totalDegree
          (-MvPolynomial.C t : EAPoly k r).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
        have hneg : (-MvPolynomial.C t : EAPoly k r) = MvPolynomial.C (-t) := by simp
        rw [MvPolynomial.totalDegree_X, hneg, MvPolynomial.totalDegree_C]
        simp

/-- The atom degree of the pinning equation `x_i - t` is at most `2`. -/
lemma atomDeg_var_sub_le {k r : ℕ} (i : Fin k) (t : ℝ) :
    atomDeg (MvPolynomial.X (Sum.inl i) - MvPolynomial.C t : EAPoly k r) ≤ 2 := by
  simp only [atomDeg]
  have := totalDegree_var_sub_le (k := k) (r := r) i t
  omega

/-- Adjoining one equation to a basic set raises its degree by exactly the atom degree of that
equation. -/
lemma basic_deg_append_eq {k r : ℕ} (B : Basic k r) (Q : EAPoly k r) :
    Basic.deg (⟨B.eqs ++ [Q], B.pos⟩ : Basic k r) = Basic.deg B + atomDeg Q := by
  simp only [Basic.deg, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- Adjoining an equation of atom degree `≤ 2` to every basic set of a list raises the total
degree by at most `2` per basic set. -/
lemma sum_map_deg_addEq_le {k r : ℕ} (l : List (Basic k r)) (Q : EAPoly k r)
    (hQ : atomDeg Q ≤ 2) :
    ((l.map (fun B => (⟨B.eqs ++ [Q], B.pos⟩ : Basic k r))).map Basic.deg).sum
      ≤ (l.map Basic.deg).sum + 2 * l.length := by
  induction l with
  | nil => simp
  | cons B l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hB : Basic.deg (⟨B.eqs ++ [Q], B.pos⟩ : Basic k r) ≤ Basic.deg B + 2 := by
      rw [basic_deg_append_eq]; omega
    omega

theorem semiPf_coord_levelSet {n m : ℕ} (X : WilkiesDesign.E.SemiPf (n + m)) (l : Fin m) (t : ℝ) :
    ∃ Y : WilkiesDesign.E.SemiPf (n + m),
      Y.set = X.set ∩ {z : Fin (n + m) → ℝ | WilkiesDesign.E.projSnd n m z l = t} ∧
      Y.fmt ≤ X.fmt ∧ Y.deg ≤ X.deg + 2 * X.basics.length := by
  refine ⟨Work.WilE7.FaceAux.addEq X
    ((MvPolynomial.X (Sum.inl (Fin.natAdd n l)) - MvPolynomial.C t : EAPoly (n + m) X.r)),
    ?_, ?_, ?_⟩
  · rw [Work.WilE7.FaceAux.addEq_set]
    have hset : {z : Fin (n + m) → ℝ | WilkiesDesign.E.eaEval X.c
          (MvPolynomial.X (Sum.inl (Fin.natAdd n l)) - MvPolynomial.C t :
            EAPoly (n + m) X.r) z = 0}
        = {z : Fin (n + m) → ℝ | WilkiesDesign.E.projSnd n m z l = t} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      rw [eaEval_var_sub]
      simp only [WilkiesDesign.E.projSnd, sub_eq_zero]
    rw [hset]
  · rw [Work.WilE7.FaceAux.addEq_fmt]
  · simp only [WilkiesDesign.E.SemiPf.deg, Work.WilE7.FaceAux.addEq_basics]
    exact sum_map_deg_addEq_le X.basics _
      (atomDeg_var_sub_le (k := n + m) (r := X.r) (Fin.natAdd n l) t)

end Work.WilE7.coreLT_succ
