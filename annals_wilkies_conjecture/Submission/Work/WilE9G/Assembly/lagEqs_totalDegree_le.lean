import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE9.EaD.eaD_totalDegree_le

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-!
## The total degree of the equations of the Lagrange stratum

`lagEqs S Phi c` has one block of `1 + m` Lagrange equations `lagL`,
`S.j` lifted equations `lagH` and the normalisation `lagN`.  We bound the total
degree of every block, the point being that

* `pad` (a variable renaming) and `eaD` (the symbolic derivative) never raise the
  total degree,
* the multiplier variables `μ_a`, `μ₀` have degree `1`,
* `atomDeg (S.h a) = (S.h a).totalDegree + 1 ≤ S.deg`, so the lifted equations
  fit in the budget `S.deg`.

Every bound is then comfortably below `S.deg + atomDeg Phi + 2`.
-/

/-! ## Generic plumbing -/

/-- Subtracting `1` never raises the total degree. -/
private lemma td_one_sub_le {N r : ℕ} (Q : EAPoly N r) :
    (1 - Q : EAPoly N r).totalDegree ≤ Q.totalDegree := by
  rw [sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_neg]
  simp

/-- The padding `EAPoly.pad` of the Lagrange construction does not raise the total degree. -/
private lemma td_padLag_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) {r : ℕ}
    (Q : EAPoly (n + (1 + m)) r) :
    (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Q).totalDegree
      ≤ Q.totalDegree := by
  have h := Work.WilE7.atomDeg_pad_le (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Q
  simp only [atomDeg] at h
  omega

/-- A single equation degree is bounded by the ambient degree. -/
private lemma atomDeg_h_le_deg {N : ℕ} (S : AmbStratum N) (a : Fin S.j) :
    atomDeg (S.h a) ≤ S.deg := by
  have h := Finset.single_le_sum (f := fun a : Fin S.j => atomDeg (S.h a))
    (s := Finset.univ) (fun a _ => Nat.zero_le _) (Finset.mem_univ a)
  simp only [AmbStratum.deg] at h ⊢
  omega

/-- The degree of a multiplier variable. -/
private lemma td_muVar_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) (a : Fin S.j) :
    (muVar S a).totalDegree ≤ 1 := by
  rw [muVar, MvPolynomial.totalDegree_X]

/-- The degree of the homogeneous multiplier variable. -/
private lemma td_mu0Var_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    (mu0Var S).totalDegree ≤ 1 := by
  rw [mu0Var, MvPolynomial.totalDegree_X]

/-! ## Per-block bounds -/

private lemma lagH_totalDegree_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) (b : Fin S.j) :
    (lagH S b).totalDegree ≤ S.deg := by
  have hp : (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (S.h b)).totalDegree ≤ (S.h b).totalDegree := td_padLag_le S (S.h b)
  have hd : (S.h b).totalDegree + 1 ≤ S.deg := by
    have h := atomDeg_h_le_deg S b
    simp only [atomDeg] at h
    exact h
  show (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (S.h b)).totalDegree ≤ S.deg
  omega

private lemma lagN_totalDegree_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    (lagN S).totalDegree ≤ 2 := by
  have hsum : (∑ a : Fin S.j, (muVar S a) ^ 2).totalDegree ≤ 2 := by
    refine MvPolynomial.totalDegree_finsetSum_le (fun a _ => ?_)
    refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
    have h := td_muVar_le S a
    omega
  have hsq : ((mu0Var S) ^ 2).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
    have h := td_mu0Var_le S
    omega
  have htot : ((∑ a : Fin S.j, (muVar S a) ^ 2) + (mu0Var S) ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le hsum hsq)
  show ((∑ a : Fin S.j, (muVar S a) ^ 2) + (mu0Var S) ^ 2 - 1).totalDegree ≤ 2
  exact (MvPolynomial.totalDegree_sub_C_le _ (1 : ℝ)).trans htot

private lemma lagL_totalDegree_le {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    (lagL S Phi c l).totalDegree ≤ S.deg + atomDeg Phi := by
  have hpadPhi : (Work.WilE7.EAPoly.pad
      (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (eaD S.X.c (Fin.natAdd n l) Phi)).totalDegree ≤ Phi.totalDegree :=
    (td_padLag_le S (eaD S.X.c (Fin.natAdd n l) Phi)).trans
      (Work.WilE9.EaD.eaD_totalDegree_le S.X.c (Fin.natAdd n l) Phi)
  have hCpadPhi : (MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
      (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi).totalDegree
      ≤ Phi.totalDegree := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (MvPolynomial.C (c l) : EAPoly (n + (1 + (m + S.j + 1))) S.X.r).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    have h2 : (Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi).totalDegree
        ≤ Phi.totalDegree := td_padLag_le S Phi
    omega
  have hprod1 : (mu0Var S * (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) Phi)
      + MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi)).totalDegree
      ≤ S.deg + atomDeg Phi := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hinner : (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
          (eaD S.X.c (Fin.natAdd n l) Phi)
        + MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
          (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi).totalDegree
        ≤ Phi.totalDegree :=
      (MvPolynomial.totalDegree_add _ _).trans (max_le hpadPhi hCpadPhi)
    have hm0 := td_mu0Var_le S
    simp only [atomDeg]
    omega
  have hprod2 : (∑ a : Fin S.j, muVar S a * Work.WilE7.EAPoly.pad
      (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (eaD S.X.c (Fin.natAdd n l) (S.h a))).totalDegree ≤ S.deg + atomDeg Phi := by
    refine MvPolynomial.totalDegree_finsetSum_le (fun a _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := td_muVar_le S a
    have h2 : (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) (S.h a))).totalDegree ≤ (S.h a).totalDegree :=
      (td_padLag_le S (eaD S.X.c (Fin.natAdd n l) (S.h a))).trans
        (Work.WilE9.EaD.eaD_totalDegree_le S.X.c (Fin.natAdd n l) (S.h a))
    have h3 : (S.h a).totalDegree + 1 ≤ S.deg := by
      have h := atomDeg_h_le_deg S a
      simp only [atomDeg] at h
      exact h
    simp only [atomDeg]
    omega
  show (mu0Var S * (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) Phi)
      + MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi)
      - ∑ a : Fin S.j, muVar S a * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) (S.h a))).totalDegree ≤ S.deg + atomDeg Phi
  have hneg : (-(∑ a : Fin S.j, muVar S a * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) (S.h a)))).totalDegree ≤ S.deg + atomDeg Phi := by
    rw [MvPolynomial.totalDegree_neg]
    exact hprod2
  have hadd : (mu0Var S * (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) Phi)
      + MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi)
      + -(∑ a : Fin S.j, muVar S a * Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
        (eaD S.X.c (Fin.natAdd n l) (S.h a)))).totalDegree ≤ S.deg + atomDeg Phi :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le hprod1 hneg)
  simpa [sub_eq_add_neg] using hadd

/-! ## Assembly of `lagEqs` -/

theorem lagEqs_totalDegree_le {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) :
    (Work.WilE9G.Lagrange.lagEqs S Phi c a).totalDegree
      ≤ S.deg + WilkiesDesign.E.atomDeg Phi + 2 := by
  have hL := lagL_totalDegree_le S Phi c
  have hH := lagH_totalDegree_le S
  have hN := lagN_totalDegree_le S
  set i : Fin ((1 + m) + (S.j + 1)) := (lagEquiv m S.j) a with hi
  have hmain : (Fin.addCases (fun l : Fin (1 + m) => lagL S Phi c l)
        (fun s : Fin (S.j + 1) =>
          Fin.addCases (fun b : Fin S.j => lagH S b) (fun _ : Fin 1 => lagN S) s) i
      : EAPoly (n + (1 + (m + S.j + 1))) S.X.r).totalDegree ≤ S.deg + atomDeg Phi + 2 := by
    by_cases hlt : i.val < 1 + m
    · have hii : i = Fin.castAdd (S.j + 1) ⟨i.val, hlt⟩ := Fin.ext rfl
      rw [hii, Fin.addCases_left]
      have := hL ⟨i.val, hlt⟩
      omega
    · have hge : 1 + m ≤ i.val := Nat.le_of_not_lt hlt
      have hv : i.val - (1 + m) < S.j + 1 := by omega
      have hii : i = Fin.natAdd (1 + m) ⟨i.val - (1 + m), hv⟩ := by
        apply Fin.ext
        show i.val = (1 + m) + (i.val - (1 + m))
        omega
      rw [hii, Fin.addCases_right]
      by_cases hv2 : i.val - (1 + m) < S.j
      · have hs : (⟨i.val - (1 + m), hv⟩ : Fin (S.j + 1))
            = Fin.castAdd 1 ⟨i.val - (1 + m), hv2⟩ := Fin.ext rfl
        rw [hs, Fin.addCases_left]
        have := hH ⟨i.val - (1 + m), hv2⟩
        omega
      · have hv3 : i.val - (1 + m) = S.j := by omega
        have hs : (⟨i.val - (1 + m), hv⟩ : Fin (S.j + 1)) = Fin.natAdd S.j 0 := by
          apply Fin.ext
          show i.val - (1 + m) = S.j + 0
          omega
        rw [hs, Fin.addCases_right]
        omega
  exact hmain

end Work.WilE9G.Assembly
