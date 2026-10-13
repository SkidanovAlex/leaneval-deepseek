import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.MPsi.Defs

namespace Work.WilE3.MPsi

open WilkiesDesign.E

/-- The total degree of a list sum is bounded by the sum of the total degrees. -/
lemma totalDegree_list_sum {σ : Type*} (l : List (MvPolynomial σ ℝ)) :
    l.sum.totalDegree ≤ (l.map MvPolynomial.totalDegree).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    calc (a + l.sum).totalDegree
        ≤ max a.totalDegree l.sum.totalDegree := MvPolynomial.totalDegree_add _ _
      _ ≤ a.totalDegree + l.sum.totalDegree := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      _ ≤ a.totalDegree + (l.map MvPolynomial.totalDegree).sum := Nat.add_le_add_left ih _

/-- `(l.map (c * ·)).sum = c * l.sum` on `ℕ`. -/
lemma sum_map_mul_left (l : List ℕ) (c : ℕ) :
    (l.map (fun x => c * x)).sum = c * l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

/-- The arithmetic core: `A + max (2ν A) (2E) ≤ (2ν+2)(A+E)`. -/
lemma nat_bound (ν A E : ℕ) :
    A + max (2 * ν * A) (2 * E) ≤ (2 * ν + 2) * (A + E) := by
  rcases le_total (2 * ν * A) (2 * E) with h | h
  · rw [max_eq_right h]; nlinarith [Nat.zero_le ν, Nat.zero_le A, Nat.zero_le E]
  · rw [max_eq_left h]; nlinarith [Nat.zero_le ν, Nat.zero_le A, Nat.zero_le E]

/-- **Degree bookkeeping for the penalised product** (namespace `Work.WilE3.MPsi`; the definition
`Work.WilE3.MPsi.phiPen` is in `Submission.Work.WilE3.MPsi.Defs`):
`atomDeg (phiPen B ν) ≤ (2ν+2) * B.deg + 1`, uniformly in `ν` (including `ν = 0`) and for empty
lists of equations or inequalities.  Here `B.deg = ∑_{f ∈ B.eqs ++ B.pos} atomDeg f` and
`atomDeg Q = Q.totalDegree + 1`.  Writing `A = ∑_{g ∈ B.pos} totalDegree g`,
`E = ∑_{f ∈ B.eqs} totalDegree f`, one has `totalDegree (phiPen B ν) ≤ A + max (2ν A) (2E)`. -/
theorem atomDeg_phiPen_le {k r : ℕ} (B : Basic k r) (ν : ℕ) :
    atomDeg (Work.WilE3.MPsi.phiPen B ν) ≤ (2 * ν + 2) * B.deg + 1 := by
  set A := (B.pos.map MvPolynomial.totalDegree).sum with hA
  set E := (B.eqs.map MvPolynomial.totalDegree).sum with hE
  have hP : (psiProd B).totalDegree ≤ A := by
    rw [hA, psiProd]
    exact MvPolynomial.totalDegree_list_prod _
  have hR : (resid B).totalDegree ≤ 2 * E := by
    rw [hE, resid]
    calc ((B.eqs.map (· ^ 2)).sum).totalDegree
        ≤ ((B.eqs.map (· ^ 2)).map MvPolynomial.totalDegree).sum := totalDegree_list_sum _
      _ = (B.eqs.map (fun f => (f ^ 2).totalDegree)).sum := by rw [List.map_map]; rfl
      _ ≤ (B.eqs.map (fun f => 2 * f.totalDegree)).sum :=
            List.sum_le_sum (fun f _ => MvPolynomial.totalDegree_pow f 2)
      _ = 2 * (B.eqs.map MvPolynomial.totalDegree).sum := by
            have hmap : (B.eqs.map (fun f => 2 * MvPolynomial.totalDegree f))
                = (B.eqs.map MvPolynomial.totalDegree).map (fun x => 2 * x) := by
              rw [List.map_map]; rfl
            rw [hmap, sum_map_mul_left]
  have hPow : (psiProd B ^ (2 * ν)).totalDegree ≤ 2 * ν * A := by
    calc (psiProd B ^ (2 * ν)).totalDegree
        ≤ (2 * ν) * ((psiProd B).totalDegree) := MvPolynomial.totalDegree_pow _ _
      _ ≤ (2 * ν) * A := Nat.mul_le_mul_left _ hP
  have hInner : (psiProd B ^ (2 * ν) - resid B).totalDegree ≤ max (2 * ν * A) (2 * E) := by
    calc (psiProd B ^ (2 * ν) - resid B).totalDegree
        ≤ max (psiProd B ^ (2 * ν)).totalDegree (resid B).totalDegree :=
            MvPolynomial.totalDegree_sub _ _
      _ ≤ max (2 * ν * A) (2 * E) := max_le_max hPow hR
  have hPhi : (phiPen B ν).totalDegree ≤ A + max (2 * ν * A) (2 * E) := by
    rw [phiPen]
    calc (psiProd B * (psiProd B ^ (2 * ν) - resid B)).totalDegree
        ≤ (psiProd B).totalDegree + (psiProd B ^ (2 * ν) - resid B).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ A + max (2 * ν * A) (2 * E) := Nat.add_le_add hP hInner
  have hdeg : A + E ≤ B.deg := by
    rw [hA, hE, Basic.deg]
    have h1 : (B.eqs.map MvPolynomial.totalDegree).sum ≤ (B.eqs.map atomDeg).sum :=
      List.sum_le_sum (fun f _ => Nat.le_succ f.totalDegree)
    have h2 : (B.pos.map MvPolynomial.totalDegree).sum ≤ (B.pos.map atomDeg).sum :=
      List.sum_le_sum (fun f _ => Nat.le_succ f.totalDegree)
    rw [List.map_append, List.sum_append]
    omega
  rw [atomDeg]
  exact le_trans (Nat.add_le_add_right hPhi 1)
    (Nat.add_le_add_right (le_trans (nat_bound ν A E) (Nat.mul_le_mul_left (2 * ν + 2) hdeg)) 1)

end Work.WilE3.MPsi
