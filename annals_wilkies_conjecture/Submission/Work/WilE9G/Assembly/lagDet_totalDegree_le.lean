/-
  Subproject WilE9G / Assembly — degree bound for the symbolic Lagrange determinant.

  `lagDet S Phi c` is the determinant of the square `(1 + (m + S.j + 1)) × (1 + (m + S.j + 1))`
  matrix whose `(a, l)` entry is the partial `eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a)`
  of the `a`-th equation of the Lagrange system in the `l`-th fibre direction.  Since

  * `eaD` never raises the total degree (`Work.WilE9.EaD.eaD_totalDegree_le`), and
  * every equation `lagEqs S Phi c a` has total degree `≤ S.deg + atomDeg Phi + 2`
    (the Lagrange equations `lagL`, the lifted equations `lagH` and the normalisation `lagN`),

  the determinant of the `(1 + (m + S.j + 1))`-term sum of products is bounded by the number of
  factors times that bound (`Work.WilE2.Matrix.det_totalDegree_le`).

  The per-equation estimates are proved here (privately) for the ambient strata of the assembly.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE9.EaD.eaD_totalDegree_le
import Submission.Work.WilE2.Lift

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## Generic degree plumbing for the Lagrange system -/

/-- Padding an `EA`-polynomial from the coordinates of `S` to the Lagrange stratum's ambient
space does not raise its total degree. -/
private lemma td_pad_lag {n m : ℕ} (S : AmbStratum (n + (1 + m))) {r : ℕ}
    (Q : EAPoly (n + (1 + m)) r) :
    (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Q).totalDegree
      ≤ Q.totalDegree := by
  have h := Work.WilE7.atomDeg_pad_le (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Q
  simp only [atomDeg] at h
  omega

/-- Each equation of `S` contributes at most `S.deg` to the degree budget. -/
private lemma atomDeg_h_le_deg {N : ℕ} (S : AmbStratum N) (a : Fin S.j) :
    atomDeg (S.h a) ≤ S.deg := by
  have h := Finset.single_le_sum (f := fun a : Fin S.j => atomDeg (S.h a))
    (s := Finset.univ) (fun a _ => Nat.zero_le _) (Finset.mem_univ a)
  simp only [AmbStratum.deg] at h ⊢
  omega

/-- The multiplier variable `μ_a` has total degree `1`. -/
private lemma td_muVar_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) (a : Fin S.j) :
    (muVar S a).totalDegree ≤ 1 := by
  rw [muVar, MvPolynomial.totalDegree_X]

/-- The multiplier variable `μ₀` has total degree `1`. -/
private lemma td_mu0Var_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
    (mu0Var S).totalDegree ≤ 1 := by
  rw [mu0Var, MvPolynomial.totalDegree_X]

/-! ## Per-block bounds -/

/-- A lifted equation `lagH S b` has total degree at most `S.deg`. -/
private lemma lagH_td_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) (b : Fin S.j) :
    (lagH S b).totalDegree ≤ S.deg := by
  have hp : (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (S.h b)).totalDegree ≤ (S.h b).totalDegree := td_pad_lag S (S.h b)
  have hd : (S.h b).totalDegree + 1 ≤ S.deg := by
    have h := atomDeg_h_le_deg S b
    simp only [atomDeg] at h
    exact h
  show (Work.WilE7.EAPoly.pad (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (S.h b)).totalDegree ≤ S.deg
  omega

/-- The normalisation `lagN S` has total degree at most `2`. -/
private lemma lagN_td_le {n m : ℕ} (S : AmbStratum (n + (1 + m))) :
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

/-- A Lagrange equation `lagL S Phi c l` has total degree at most `S.deg + atomDeg Phi`. -/
private lemma lagL_td_le {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) (l : Fin (1 + m)) :
    (lagL S Phi c l).totalDegree ≤ S.deg + atomDeg Phi := by
  have hpadPhi : (Work.WilE7.EAPoly.pad
      (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega)
      (eaD S.X.c (Fin.natAdd n l) Phi)).totalDegree ≤ Phi.totalDegree :=
    (td_pad_lag S (eaD S.X.c (Fin.natAdd n l) Phi)).trans
      (Work.WilE9.EaD.eaD_totalDegree_le S.X.c (Fin.natAdd n l) Phi)
  have hCpadPhi : (MvPolynomial.C (c l) * Work.WilE7.EAPoly.pad
      (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi).totalDegree
      ≤ Phi.totalDegree := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (MvPolynomial.C (c l) : EAPoly (n + (1 + (m + S.j + 1))) S.X.r).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    have h2 : (Work.WilE7.EAPoly.pad
        (show n + (1 + m) ≤ n + (1 + (m + S.j + 1)) by omega) Phi).totalDegree
        ≤ Phi.totalDegree := td_pad_lag S Phi
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
      (td_pad_lag S (eaD S.X.c (Fin.natAdd n l) (S.h a))).trans
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

/-- **Every equation of the Lagrange system has total degree at most `S.deg + atomDeg Phi + 2`.** -/
private lemma lagEqs_td_le {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) :
    (lagEqs S Phi c a).totalDegree ≤ S.deg + atomDeg Phi + 2 := by
  have hL := lagL_td_le S Phi c
  have hH := lagH_td_le S
  have hN := lagN_td_le S
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

/-! ## The determinant -/

theorem lagDet_totalDegree_le {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    (Work.WilE9G.Lagrange.lagDet S Phi c).totalDegree
      ≤ (1 + (m + S.j + 1)) * (S.deg + WilkiesDesign.E.atomDeg Phi + 2) := by
  rw [Work.WilE9G.Lagrange.lagDet]
  refine (Work.WilE2.Matrix.det_totalDegree_le _ (fun _ => S.deg + atomDeg Phi + 2)
      (fun a l => ?_)).trans ?_
  · exact (Work.WilE9.EaD.eaD_totalDegree_le (lagChain S) (Fin.natAdd n l)
      (lagEqs S Phi c a)).trans (lagEqs_td_le S Phi c a)
  · have hsum : (∑ _ : Fin (1 + (m + S.j + 1)), (S.deg + atomDeg Phi + 2))
        = (1 + (m + S.j + 1)) * (S.deg + atomDeg Phi + 2) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hsum]

end Work.WilE9G.Assembly
