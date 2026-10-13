import Mathlib
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.mulVec_transpose_eq_zero_of_rank
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff
import Submission.Work.Strat.detOpSt_eq_zero_of_row_combination
import Submission.Work.WilE7.FibreCalc.fibSlice_eaEval_hasStrictFDerivAt
import Submission.Work.WilE7.FibreCalc.critSet_mem_of_rowRelation

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Filter
open scoped Topology Matrix

namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## An evaluation helper

The calculus input (the strict derivative `Work.WilE7.FibreCalc.fibSlice_eaEval_hasStrictFDerivAt`
of the fibre-restricted functions `y ↦ eaEval c Q (Fin.append x y)`) and the algebraic output
(`Work.WilE7.FibreCalc.critSet_mem_of_rowRelation`) are imported from
`Submission/Work/WilE7/FibreCalc`.  All that is left here is the evaluation of a sum of
coordinate functionals on a basis vector.
-/

/-- Evaluation of a "sum of scalars times coordinate functionals" on a basis vector. -/
private theorem sum_smul_proj_apply_single {q : ℕ} (f : Fin q → ℝ) (d : Fin q) :
    (∑ d' : Fin q, f d' • (ContinuousLinearMap.proj d' : (Fin q → ℝ) →L[ℝ] ℝ))
      (Pi.single d 1) = f d := by
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · simp
  · intro d' _ hne
    simp [Pi.single_eq_of_ne hne]
  · intro hd
    exact absurd (Finset.mem_univ d) hd

/-! ## The local maximum criterion -/

/-- **A local maximum of a fibre coordinate on a good stratum is a fibre-critical point.**

If `z = (x, y)` lies in (the set of) a `Good` stratum `S` and the `l`-th fibre coordinate `y_l`
attains a local maximum at `y` on the fibre `S_x` (as witnessed by an open `U ∋ y`), then `y_l`
is critical on the fibre germ at `y`: every `(S.j + 1) × (S.j + 1)` minor of the matrix
`[∂_y h ; e_l]` vanishes at `z`, i.e. `z ∈ (critSet S l).set`.

The proof is the Lagrange multiplier argument: `Good` says that near `z` the fibre germ of
`S.X.set` coincides with the zero locus `{y' | h(x, y') = 0}`, whose Jacobian `∂_y h` has full
rank `S.j`; a local extremum of `y_l` on that zero locus has derivative `e_l` in the span of the
rows `∂_y h_a` (this is `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, combined with
the injectivity of `∂_y hᵀ`, which upgrades the multiplier of `y_l` to a non-zero one).
That row relation makes all the `(S.j + 1)`-minors of `[∂_y h ; e_l]` vanish. -/
theorem critSet_of_localMax {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) (l : Fin q)
    (U : Set (Fin q → ℝ)) (hUopen : IsOpen U) (hUz : WilkiesDesign.E.projSnd p q z ∈ U)
    (hmax : ∀ y' ∈ U, y' ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) →
      y' l ≤ (WilkiesDesign.E.projSnd p q z) l) :
    z ∈ (Work.WilE7.critSet S l).set := by
  set x : Fin p → ℝ := projFirst p q z with hx
  set y : Fin q → ℝ := projSnd p q z with hy
  have hyU : y ∈ U := by rw [hy]; exact hUz
  have hzy : Fin.append x y = z := by
    rw [hx, hy]
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [projFirst, projSnd]
  have hzX : Fin.append x y ∈ S.X.set := by rw [hzy]; exact hz
  have hvan : ∀ a, eaEval S.X.c (S.h a) z = 0 := (hGood z hz).1
  have hrank : (Matrix.of fun (a : Fin S.j) (d : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z).rank = S.j := (hGood z hz).2.1
  -- `Good` transported to the fibre: near `y`, solutions of `h(x, ·) = 0` lie in the fibre.
  have hgerm := eventually_mem_fiber_of_good S hGood x y hzX
  -- the derivatives of the `h_a` and of `y_l` on the fibre
  set fa : Fin S.j → (Fin q → ℝ) →L[ℝ] ℝ :=
    fun a => ∑ d : Fin q,
      (eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z) •
        (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) with hfa
  set phi : (Fin q → ℝ) →L[ℝ] ℝ :=
    ∑ d : Fin q,
      (eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
        (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) •
        (ContinuousLinearMap.proj d : (Fin q → ℝ) →L[ℝ] ℝ) with hphi
  have hfa_strict : ∀ a : Fin S.j, HasStrictFDerivAt
      (fun y' : Fin q → ℝ => eaEval S.X.c (S.h a) (Fin.append x y')) (fa a) y := by
    intro a
    have h := Work.WilE7.FibreCalc.fibSlice_eaEval_hasStrictFDerivAt (p := p) (q := q)
      (r := S.X.r) S.X.c (S.h a) x y
    simpa [hfa, hzy] using h
  have hphi_strict : HasStrictFDerivAt
      (fun y' : Fin q → ℝ =>
        eaEval S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) (Fin.append x y')) phi y := by
    have h := Work.WilE7.FibreCalc.fibSlice_eaEval_hasStrictFDerivAt (p := p) (q := q)
      (r := S.X.r) S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) x y
    simpa [hphi, hzy] using h
  -- `y` is a local maximum of `y_l` on the zero locus of `h` in the fibre
  have hextr : IsLocalExtrOn
      (fun y' : Fin q → ℝ =>
        eaEval S.X.c (MvPolynomial.X (Sum.inl (fibDir p q l))) (Fin.append x y'))
      {y' : Fin q → ℝ | ∀ a, eaEval S.X.c (S.h a) (Fin.append x y')
        = eaEval S.X.c (S.h a) (Fin.append x y)} y := by
    refine Or.inr ?_
    rw [IsMaxFilter, eventually_nhdsWithin_iff]
    filter_upwards [hgerm, hUopen.mem_nhds hyU] with y' hy' hyU' hyS
    have hy0 : ∀ a, eaEval S.X.c (S.h a) (Fin.append x y') = 0 := by
      intro a
      rw [hyS a, hzy, hvan a]
    have hmem : y' ∈ fiber S.X.set x := hy' hy0
    have hmem' : y' ∈ fiber S.X.set (projFirst p q z) := by
      rw [← hx]
      exact hmem
    have hle : y' l ≤ y l := hmax y' hyU' hmem'
    simpa [eaEval, MvPolynomial.eval_X, fibDir, Fin.append_right] using hle
  -- Lagrange multipliers
  obtain ⟨Λ, Λ₀, hΛ, heq⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt hfa_strict hphi_strict
  have hfa_val : ∀ (a : Fin S.j) (d : Fin q),
      fa a (Pi.single d 1) = eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z := by
    intro a d
    simp only [hfa]
    exact sum_smul_proj_apply_single
      (fun d' => eaEval S.X.c (eaD S.X.c (Fin.natAdd p d') (S.h a)) z) d
  have hphi_val : ∀ d : Fin q,
      phi (Pi.single d 1)
        = eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
            (MvPolynomial.X (Sum.inl (fibDir p q l)))) z := by
    intro d
    simp only [hphi]
    exact sum_smul_proj_apply_single
      (fun d' => eaEval S.X.c (eaD S.X.c (Fin.natAdd p d')
        (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) d
  have heq_val : ∀ d : Fin q,
      (∑ a : Fin S.j, Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z)
        + Λ₀ * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
            (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
      = 0 := by
    intro d
    have h := congrArg (fun (L : (Fin q → ℝ) →L[ℝ] ℝ) => L (Pi.single d 1)) heq
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] at h
    simpa [hfa_val, hphi_val] using h
  -- the multiplier of `y_l` is non-zero, by full rank of `∂_y h`
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    have hsum : (∑ a : Fin S.j, Λ a • fa a) = 0 := by
      have h := heq
      rw [h0, zero_smul, add_zero] at h
      exact h
    have hpt : ∀ d : Fin q,
        ∑ a : Fin S.j, Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z = 0 := by
      intro d
      have h := congrArg (fun (L : (Fin q → ℝ) →L[ℝ] ℝ) => L (Pi.single d 1)) hsum
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.zero_apply, smul_eq_mul] at h
      simpa [hfa_val] using h
    set M : Matrix (Fin S.j) (Fin q) ℝ :=
      Matrix.of fun (a : Fin S.j) (d : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z with hM
    have hMrank : M.rank = S.j := by rw [hM]; exact hrank
    have hmv : Matrix.mulVec (Matrix.transpose M) Λ = 0 := by
      funext d
      rw [Matrix.mulVec_apply_eq_sum]
      simp only [Matrix.transpose_apply, hM, Matrix.of_apply]
      simpa [mul_comm] using hpt d
    have hzero : Λ = 0 := mulVec_transpose_eq_zero_of_rank M hMrank Λ hmv
    exact hΛ (by simp [hzero, h0])
  -- the resulting row relation on the derivatives
  have hrow : ∀ d : Fin q,
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
          (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
        = ∑ a : Fin S.j,
            (-(Λ₀)⁻¹ * Λ a) * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z := by
    intro d
    have h := heq_val d
    have h' : eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
          (MvPolynomial.X (Sum.inl (fibDir p q l)))) z
        = -(Λ₀)⁻¹ * (∑ a : Fin S.j,
            Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z) := by
      have h2 : Λ₀⁻¹ * ((∑ a : Fin S.j,
            Λ a * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d) (S.h a)) z)
          + Λ₀ * eaEval S.X.c (eaD S.X.c (Fin.natAdd p d)
              (MvPolynomial.X (Sum.inl (fibDir p q l)))) z) = 0 := by
        rw [h, mul_zero]
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hΛ₀, one_mul] at h2
      linarith
    rw [h', neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  -- assemble: every `(S.j+1)`-minor of `[∂_y h ; e_l]` vanishes at `z`
  exact Work.WilE7.FibreCalc.critSet_mem_of_rowRelation S l z hz
    (fun a : Fin S.j => -(Λ₀)⁻¹ * Λ a) hrow

end Work.WilE7
