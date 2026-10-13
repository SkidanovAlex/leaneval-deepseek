import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE5.Bounds.totalDegree_detOp_le

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Bookkeeping lemmas for `critSet_deg_bound_Sdeg` -/

/-- Sum of a list of numbers to which a constant has been added. -/
lemma list_sum_map_add_const {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- The degree of a basic set whose equations have been extended by a list `L`. -/
lemma basic_deg_append_eqs {k r : ℕ} (B : Basic k r) (L : List (EAPoly k r)) :
    (⟨B.eqs ++ L, B.pos⟩ : Basic k r).deg = B.deg + (L.map atomDeg).sum := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  omega

/-- **Degree of `critSet`.**  Appending the list `critMinors S l` of critical minors to *every*
branch of `S.X` adds the same amount `M` to each branch, so the degree of `critSet S l` is the
degree of `S.X` plus the number of branches times `M`. -/
lemma critSet_deg_eq {p q : ℕ} (S : Stratum p q) (l : Fin q) :
    (critSet S l).deg =
      S.X.deg + S.X.basics.length * ((critMinors S l).map atomDeg).sum := by
  set M : ℕ := ((critMinors S l).map atomDeg).sum with hM
  dsimp only [critSet, SemiPf.deg]
  rw [List.map_map]
  have hmap : (List.map (Basic.deg ∘ fun B =>
      (⟨B.eqs ++ critMinors S l, B.pos⟩ : Basic (p + q) S.X.r)) S.X.basics)
      = S.X.basics.map (fun B => B.deg + M) := by
    apply List.map_congr_left
    intro B hB
    show Basic.deg (⟨B.eqs ++ critMinors S l, B.pos⟩ : Basic (p + q) S.X.r) = B.deg + M
    rw [basic_deg_append_eqs, hM]
  rw [hmap, list_sum_map_add_const S.X.basics Basic.deg M]

/-- **Degree bound for `critSet`, in terms of `Stratum.deg`.**  For a stratum of format `≤ F` with
`S.j ≤ q` (which holds automatically for `Good` strata, whose fibrewise Jacobian has rank `S.j`
and `q` columns) and whose `basics` list has been normalised (`basics.length ≤ X.deg + 1`, as
delivered by `Work.WilE7.semiPf_normalize_exists`), the degree of the fibre-critical set
`critSet S l` is bounded by a polynomial in `S.deg = S.X.deg + ∑_a atomDeg (S.h a)` (and *not* by a
polynomial in `S.X.deg` alone: the `q^(S.j+1)` minors appended by `critSet` have degree controlled
by the degrees of the equations `S.h`).  The polynomial depends on the format bound `F` only, which
is what makes the fibre-cut recursion's degree bookkeeping close. -/
theorem critSet_deg_bound_Sdeg (F : ℕ) :
    ∃ c : Polynomial ℕ, ∀ (p q : ℕ) (S : WilkiesDesign.E.Stratum p q), S.X.fmt ≤ F →
      S.j ≤ q → S.X.basics.length ≤ S.X.deg + 1 → ∀ l : Fin q,
      (Work.WilE7.critSet S l).deg ≤ c.eval S.deg := by
  -- The bounding polynomial: `D ↦ K·(F+1)·(D+1)·(D+2) + K·(D+1) + (D+1)`, where `K = (F+1)^(F+1)`
  -- bounds the number `q^(S.j+1)` of critical minors.
  refine ⟨Polynomial.C (((F + 1) ^ (F + 1)) * (F + 1)) * (Polynomial.X + Polynomial.C 1)
      * (Polynomial.X + Polynomial.C 2)
    + Polynomial.C ((F + 1) ^ (F + 1)) * (Polynomial.X + Polynomial.C 1)
    + Polynomial.X + Polynomial.C 1, ?_⟩
  intro p q S hfmt hj hlen l
  set K : ℕ := (F + 1) ^ (F + 1) with hK
  set M : ℕ := ((critMinors S l).map atomDeg).sum with hM
  -- `q ≤ F` and `S.j + 1 ≤ F + 1` follow from the format bound.
  have hqF : q ≤ F := by
    have h := hfmt
    simp only [SemiPf.fmt] at h
    omega
  have hjF : S.j + 1 ≤ F + 1 := by omega
  -- (1) the degree of `critSet S l` splits into the degree of `S.X` plus `|S.X.basics| · M`.
  have hdecomp : (critSet S l).deg = S.X.deg + S.X.basics.length * M := critSet_deg_eq S l
  -- (2) each critical minor has atom degree at most `(S.j+1)·(S.deg+2) + 1`.
  have hmin : ∀ σ : Fin (S.j + 1) → Fin q,
      atomDeg (critMinor S.X.c S.h l σ) ≤ (S.j + 1) * (S.deg + 2) + 1 := by
    intro σ
    have hrow : ∀ a : Fin S.j, (S.h a).totalDegree ≤ S.deg + 1 := by
      intro a
      have h1 : atomDeg (S.h a) ≤ S.deg := by
        have : atomDeg (S.h a) ≤ ∑ b : Fin S.j, atomDeg (S.h b) :=
          Finset.single_le_sum (f := fun b => atomDeg (S.h b)) (s := Finset.univ)
            (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
        simp only [Stratum.deg]
        omega
      simp only [atomDeg] at h1; omega
    have hf : (MvPolynomial.X (Sum.inl (fibDir p q l)) : EAPoly (p + q) S.X.r).totalDegree
        ≤ S.deg + 1 := by
      rw [MvPolynomial.totalDegree_X]; omega
    have hdet := Work.WilE5.Bounds.totalDegree_detOp_le S.X.c S.h
      (fun b : Fin S.j => fibDir p q (σ (Fin.castSucc b)))
      (fibDir p q (σ (Fin.last S.j)))
      (MvPolynomial.X (Sum.inl (fibDir p q l)) : EAPoly (p + q) S.X.r) (S.deg + 1) hrow hf
    have htd : (critMinor S.X.c S.h l σ).totalDegree ≤ (S.j + 1) * (S.deg + 2) := by
      simpa only [critMinor, Nat.add_assoc] using hdet
    simp only [atomDeg]; omega
  -- (3) hence `M ≤ q^(S.j+1) · ((S.j+1)·(S.deg+2) + 1)`.
  have hMle : M ≤ q ^ (S.j + 1) * ((S.j + 1) * (S.deg + 2) + 1) := by
    have hlenM : (critMinors S l).length = q ^ (S.j + 1) := by
      simp only [critMinors, List.length_map, Finset.length_toList, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]
    have h1 : ((critMinors S l).map atomDeg).sum
        ≤ ((critMinors S l).map atomDeg).length • ((S.j + 1) * (S.deg + 2) + 1) :=
      List.sum_le_length_nsmul _ _ (fun x hx => by
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        simp only [critMinors] at hy
        rcases List.mem_map.mp hy with ⟨σ, -, rfl⟩
        exact hmin σ)
    rw [List.length_map, hlenM, nsmul_eq_mul] at h1
    rw [hM]
    exact h1
  -- (4) `q^(S.j+1) ≤ K`.
  have hKbound : q ^ (S.j + 1) ≤ K := by
    calc q ^ (S.j + 1) ≤ (F + 1) ^ (S.j + 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (F + 1) ^ (F + 1) := Nat.pow_le_pow_right (by omega) hjF
  -- (5) assemble the bound on the degree.
  have hstep : S.X.deg + S.X.basics.length * M
      ≤ S.deg + (S.deg + 1) * (K * ((F + 1) * (S.deg + 2) + 1)) := by
    have hclen : S.X.basics.length ≤ S.deg + 1 := by
      have : S.X.deg ≤ S.deg := by simp only [Stratum.deg]; omega
      omega
    have h1 : S.X.basics.length * M
        ≤ (S.deg + 1) * (K * ((F + 1) * (S.deg + 2) + 1)) := by
      refine Nat.mul_le_mul hclen ?_
      refine hMle.trans ?_
      refine Nat.mul_le_mul hKbound ?_
      exact Nat.add_le_add_right (Nat.mul_le_mul_right (S.deg + 2) hjF) 1
    have h2 : S.X.deg ≤ S.deg := by simp only [Stratum.deg]; omega
    omega
  -- (6) the polynomial dominates the bound at `D = S.deg`.
  have hpoly : S.deg + (S.deg + 1) * (K * ((F + 1) * (S.deg + 2) + 1))
      ≤ (Polynomial.C (K * (F + 1)) * (Polynomial.X + Polynomial.C 1)
          * (Polynomial.X + Polynomial.C 2)
        + Polynomial.C K * (Polynomial.X + Polynomial.C 1)
        + Polynomial.X + Polynomial.C 1).eval S.deg := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring_nf
    omega
  rw [hdecomp]
  exact hstep.trans hpoly

end Work.WilE7
