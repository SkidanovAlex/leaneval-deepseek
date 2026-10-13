/-
  Area E7: padding a `Stratum` by `d` coordinates pinned to zero.

  Given a fibrewise effectively smooth (`Good`) stratum `S : Stratum p q` with `S.j = q` and a
  finite covering of `S.X.set` over a set `C ⊆ ℝ^p` by `k` continuous sections, this file
  produces the stratum `padStratS p q d S hj : Stratum p (d+q)` obtained by inserting `d`
  coordinates pinned to `0` between the base and the fibre coordinates, together with the
  sections `x ↦ padSection q d (s j x)` (the section of `S` with `d` zeros inserted).  The padded
  stratum is `Good` again, its format is bounded by `F + d` and its degree by a polynomial in
  `S.X.deg` whose coefficients depend only on `d` and `F`; the covering data transfer verbatim.

  The construction and its API live in `Submission.Work.WilE7.PadDefs`; the independent pieces are
  proved in `Submission/Work/WilE7/PadAux/`.
-/
import Mathlib
import Submission.Work.WilE7.FaceAux.InsertCoord
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.PadDefs
import Submission.Work.WilE7.PadAux.rank_block
import Submission.Work.WilE7.PadAux.eaD_extend
import Submission.Work.WilE7.PadAux.eaD_extend_zero
import Submission.Work.WilE7.PadAux.tidy_bounds
import Submission.Work.WilE7.PadAux.padStrat_deg
import Submission.Work.WilE7.PadAux.fiber_padStrat_ncard
import Submission.Work.WilE7.PadAux.padStratS_good_fst
import Submission.Work.WilE7.PadAux.padStratS_good_local

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The polynomial bound on the degree of the padded stratum, for a fixed padding `d`:
`D ↦ 2d + (1 + 2d)·D`. -/
def padDegPoly (d : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * d) + Polynomial.C (1 + 2 * d) * Polynomial.X

theorem padDegPoly_eval (d D : ℕ) : (padDegPoly d).eval D = 2 * d + (1 + 2 * d) * D := by
  simp [padDegPoly]

/-! ## The rank of the padded Jacobian

The `(d+q) × (d+q)` Jacobian of the defining functions of `padStratS p q d S hj` is block
diagonal with blocks `1_d` and the `q × q` fibre Jacobian of `S`, which is nonsingular by
`S.Good` (using `S.j = q`). -/

theorem midIdx_injective (p d q : ℕ) : Function.Injective (midIdx p d q) := by
  intro a b h
  have hv : p + a.val = p + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The derivative of a coordinate function along a coordinate. -/
theorem eaD_X_inl {k r : ℕ} (c : EAChain k r) (i i0 : Fin k) :
    eaD c i (MvPolynomial.X (Sum.inl i0) : EAPoly k r) =
      (if i0 = i then (1 : EAPoly k r) else 0) := by
  have hsum : (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
      MvPolynomial.pderiv (Sum.inr j) (MvPolynomial.X (Sum.inl i0))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [MvPolynomial.pderiv_X_of_ne (show (Sum.inl i0) ≠ (Sum.inr j) from by simp), mul_zero]
  rw [eaD, hsum, add_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : i0 = i
  · rw [if_pos (show (Sum.inl i0 : Fin k ⊕ Fin r) = Sum.inl i by rw [h]), if_pos h]
  · rw [if_neg (show ¬ (Sum.inl i0 : Fin k ⊕ Fin r) = Sum.inl i by simpa using h), if_neg h]

theorem eaEval_eaD_X_inl {k r : ℕ} (c : EAChain k r) (z : Fin k → ℝ) (i i0 : Fin k) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inl i0) : EAPoly k r)) z =
      (if i0 = i then 1 else 0) := by
  rw [eaD_X_inl]
  by_cases h : i0 = i
  · rw [if_pos h, if_pos h]; simp [eaEval]
  · rw [if_neg h, if_neg h]; simp [eaEval]

theorem eaEval_eaD_X_inl_ne {k r : ℕ} (c : EAChain k r) (z : Fin k → ℝ) (i i0 : Fin k)
    (h : i0 ≠ i) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inl i0) : EAPoly k r)) z = 0 := by
  rw [eaEval_eaD_X_inl, if_neg h]

/-- The rank conjunct of `Good` for the padded stratum. -/
theorem padStratS_good_rank_aux (p q d : ℕ) (S : Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (z : Fin (p + (d + q)) → ℝ) (hz : z ∈ (padStratS p q d S hj).X.set) :
    (Matrix.of fun (a : Fin (d + q)) (l : Fin (d + q)) =>
      eaEval (padStratS p q d S hj).X.c
        (eaD (padStratS p q d S hj).X.c (Fin.natAdd p l) ((padStratS p q d S hj).h a)) z).rank
      = d + q := by
  rw [padStratS_X, padStrat_set] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [tidy_set] at hz1
  set J : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun (b : Fin q) (l : Fin q) =>
    eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h (finCongr hj.symm b)))
      (fun i => z (midInj p d q i)) with hJdef
  have hJrank : J.rank = q := by
    have hg : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a))
          (fun i => z (midInj p d q i))).rank = S.j := (hGood _ hz1).2.1
    have hsub : J = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a))
          (fun i => z (midInj p d q i))).submatrix (finCongr hj.symm) id := by
      ext b l; rfl
    have hs : J.rank = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a))
          (fun i => z (midInj p d q i))).rank := by
      rw [hsub]
      exact Matrix.rank_submatrix _ (finCongr hj.symm) (Equiv.refl (Fin q))
    rw [hs]
    exact hg.trans hj
  refine PadAux.rank_block d q J hJrank _ ?_
  ext x y
  rcases x with a | b <;> rcases y with a' | l'
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁,
      Matrix.one_apply, Matrix.of_apply]
    rw [padHead_castAdd, ← midIdx_eq_natAdd, pinAt, eaEval_eaD_X_inl]
    by_cases hab : a = a'
    · rw [if_pos hab, if_pos (show midIdx p d q a = midIdx p d q a' from by rw [hab])]
    · rw [if_neg hab, if_neg (show ¬ midIdx p d q a = midIdx p d q a' from
        fun h => hab (midIdx_injective p d q h))]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply]
    rw [padHead_castAdd, pinAt, eaEval_eaD_X_inl,
      if_neg (show ¬ midIdx p d q a = Fin.natAdd p (Fin.natAdd d l') from fun h => by
        have hv : (midIdx p d q a).val = (Fin.natAdd p (Fin.natAdd d l')).val :=
          congrArg Fin.val h
        rw [Fin.val_natAdd, Fin.val_natAdd] at hv
        simp only [midIdx] at hv
        omega)]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.of_apply]
    rw [padHead_natAdd, ← midIdx_eq_natAdd,
      PadAux.eaD_extend_zero (midInj p d q) S.X.c (midIdx p d q a')
        (fun i' => midInj_ne_midIdx p d q i' a') (S.h (Fin.cast hj.symm b))]
    simp [eaEval]
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply]
    rw [padHead_natAdd, ← midInj_natAdd, PadAux.eaD_extend (midInj_injective p d q)]
    exact eaEval_extend_midInj S.X.c (eaD S.X.c (Fin.natAdd p l') (S.h (Fin.cast hj.symm b))) z

theorem pad_stratum (F : ℕ) :
    ∃ (A : ℕ → ℕ) (A2 : ℕ → Polynomial ℕ), ∀ (p q d : ℕ) (S : WilkiesDesign.E.Stratum p q)
      (hGood : S.Good) (hj : S.j = q)
      (C : Set (Fin p → ℝ)) (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ))
      (hcont : ∀ j, ContinuousOn (s j) C)
      (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
      (hsub : ∀ j, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
      (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p q z ∈ C →
        ∃ j, s j (WilkiesDesign.E.projFirst p q z) = WilkiesDesign.E.projSnd p q z)
      (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k),
      S.X.fmt ≤ F →
      ∃ (S' : WilkiesDesign.E.Stratum p (d + q))
        (s' : Fin k → (Fin p → ℝ) → (Fin (d + q) → ℝ)),
        S'.Good ∧ S'.j = d + q ∧ S'.X.fmt ≤ A d ∧
        S'.X.deg ≤ (A2 d).eval S.X.deg ∧
        S'.X.set = {z : Fin (p + (d + q)) → ℝ |
          Fin.append (WilkiesDesign.E.projFirst p (d + q) z)
            (WilkiesDesign.E.projSnd d q (WilkiesDesign.E.projSnd p (d + q) z)) ∈ S.X.set ∧
          WilkiesDesign.E.projFirst d q (WilkiesDesign.E.projSnd p (d + q) z) = 0} ∧
        (∀ (j : Fin k) (x : Fin p → ℝ), x ∈ C →
          WilkiesDesign.E.projFirst d q (s' j x) = 0 ∧
          WilkiesDesign.E.projSnd d q (s' j x) = s j x) ∧
        (∀ j, ContinuousOn (s' j) C) ∧
        (∀ x ∈ C, Function.Injective fun j : Fin k => s' j x) ∧
        (∀ j, ∀ x ∈ C, Fin.append x (s' j x) ∈ S'.X.set) ∧
        (∀ z ∈ S'.X.set, WilkiesDesign.E.projFirst p (d + q) z ∈ C →
          ∃ j, s' j (WilkiesDesign.E.projFirst p (d + q) z) =
            WilkiesDesign.E.projSnd p (d + q) z) ∧
        (∀ x ∈ C, (WilkiesDesign.E.fiber S'.X.set x).ncard = k) := by
  refine ⟨fun d => F + d, padDegPoly, ?_⟩
  intro p q d S hGood hj C k s hcont hinj hsub hcov hcard hF
  refine ⟨padStratS p q d S hj, fun j x => padSection q d (s j x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Good`
    intro z hz
    exact ⟨fun a => PadAux.padStratS_good_fst p q d S hGood hj z hz a,
      padStratS_good_rank_aux p q d S hGood hj z hz,
      PadAux.padStratS_good_local p q d S hGood hj z hz⟩
  · -- the fibrewise dimension
    rfl
  · -- the format bound
    rw [padStratS_X, padStrat_fmt, tidy_r]
    simp only [SemiPf.fmt] at hF ⊢
    omega
  · -- the degree bound
    rw [padStratS_X, padDegPoly_eval]
    have h1 := PadAux.padStrat_deg p q d (tidy S.X)
    have h2 : (tidy S.X).deg ≤ S.X.deg := (PadAux.tidy_bounds (p + q) S.X).1
    have h3 : (tidy S.X).basics.length ≤ 1 + S.X.deg := (PadAux.tidy_bounds (p + q) S.X).2
    have h4 : 2 * d * (tidy S.X).basics.length ≤ 2 * d * (1 + S.X.deg) :=
      Nat.mul_le_mul_left (2 * d) h3
    have h5 : (padStrat p q d (tidy S.X)).deg ≤ S.X.deg + 2 * d * (1 + S.X.deg) :=
      le_trans h1 (Nat.add_le_add h2 h4)
    have h6 : S.X.deg + 2 * d * (1 + S.X.deg) = 2 * d + (1 + 2 * d) * S.X.deg := by ring
    omega
  · -- the point set
    rw [padStratS_X, padStrat_set]
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [tidy_set] at h1
      rw [midInj_append_fun] at h1
      refine ⟨h1, ?_⟩
      funext a
      exact h2 a
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun a => ?_⟩
      · rw [tidy_set, midInj_append_fun]
        exact h1
      · exact congrFun h2 a
  · -- the projections of the sections
    intro j x _
    exact ⟨projFirst_padSection q d (s j x), projSnd_padSection q d (s j x)⟩
  · -- continuity of the sections
    intro j
    exact continuousOn_padSection p q d k C s hcont j
  · -- injectivity of the sections
    intro x hx j j' hjj'
    have h := congrArg (fun v : Fin (d + q) → ℝ => projSnd d q v) hjj'
    rw [projSnd_padSection, projSnd_padSection] at h
    exact hinj x hx h
  · -- the graph of each section lies in the padded set
    intro j x hx
    rw [padStratS_X, mem_padStrat_append, tidy_set]
    exact ⟨by rw [projSnd_padSection]; exact hsub j x hx, projFirst_padSection q d (s j x)⟩
  · -- the sections cover the fibres of the padded set
    intro z hz hx
    rw [padStratS_X, padStrat_set] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [tidy_set] at hz1
    have hx' : projFirst p q (fun i => z (midInj p d q i)) ∈ C := by
      rw [projFirst_midInj]; exact hx
    obtain ⟨j, hj⟩ := hcov _ hz1 hx'
    rw [projFirst_midInj] at hj
    have hj2 : s j (projFirst p (d + q) z) = projSnd d q (projSnd p (d + q) z) :=
      hj.trans (projSnd_midInj_projSnd p d q z)
    have hz0 : projFirst d q (projSnd p (d + q) z) = 0 := by
      funext a
      exact hz2 a
    refine ⟨j, ?_⟩
    rw [projSnd_append_projFirst_projSnd p d q z, ← hj2, hz0]
    exact padSection_eq_append q d _
  · -- the fibre cardinalities
    intro x hx
    have h := PadAux.fiber_padStrat_ncard p q d (tidy S.X) x
    rw [padStratS_X, h, tidy_set]
    exact hcard x hx

end Work.WilE7
