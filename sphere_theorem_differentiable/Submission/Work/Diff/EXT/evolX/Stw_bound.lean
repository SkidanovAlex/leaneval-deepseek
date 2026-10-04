import Mathlib
import Submission.Work.Diff.EXT.evolX.substB.Defs
import Submission.Work.Diff.EXT.evolX.wMonBound

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Two product-splitting helpers for the per-state bound -/

/-- **Splitting the product over `Fin m` with `m = n + 1`** at its last entry. -/
private theorem stw_prod_univ_castSucc {m n : ℕ} (h : m = n + 1) (f : Fin m → ℝ) :
    (∏ i : Fin m, f i)
      = (∏ i : Fin n, f (Fin.cast h.symm i.castSucc)) * f (Fin.cast h.symm (Fin.last n)) := by
  subst h
  exact Fin.prod_univ_castSucc f

/-- **The product of the metric norms along `dvcTup` splits at its last entry.**  This is the
product companion of the definition `dvcTup K j F W` (the `(K+j)`-tuple `F` followed by the extra
field `W`), used to split the product of norms which appears in the `StrongAt` bound. -/
private theorem stw_prod_dvcTup (g : Submission.Diff.SMet I M) (x : M) {K j : ℕ}
    (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    (∏ r : Fin ((K + 1) + j),
        Real.sqrt (g.inner x (dvcTup (I := I) (M := M) K j F W r x)
          (dvcTup (I := I) (M := M) K j F W r x)))
      = (∏ r : Fin (K + j), Real.sqrt (g.inner x (F r x) (F r x)))
        * Real.sqrt (g.inner x (W x) (W x)) := by
  have h := stw_prod_univ_castSucc (m := (K + 1) + j) (n := K + j) (by omega)
    (fun r => Real.sqrt (g.inner x (dvcTup (I := I) (M := M) K j F W r x)
      (dvcTup (I := I) (M := M) K j F W r x)))
  rw [h]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    have hlt : (((Fin.cast (by omega : (K + 1) + j = (K + j) + 1).symm i.castSucc) :
        Fin ((K + 1) + j)) : ℕ) < K + j := by simp
    rw [dvcTup_eq_of_lt (K := K) (j := j) F W _ hlt]
    exact congrArg (fun X : Work.Diff.EXT.TField (I := I) (M := M) =>
      Real.sqrt (g.inner x (X x) (X x))) (congrArg F (Fin.ext rfl))
  · have hge : ¬ (((Fin.cast (by omega : (K + 1) + j = (K + j) + 1).symm
        (Fin.last (K + j))) : Fin ((K + 1) + j)) : ℕ) < K + j := by simp
    rw [dvcTup_eq_of_ge (K := K) (j := j) F W _ hge]

theorem Stw_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g V) x)
    (hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    {CV CT : ℕ → ℝ} (hCV : ∀ a, 0 ≤ CV a) (hCT : ∀ a, 0 ≤ CT a) (p q : ℕ)
    (hV : Work.Diff.EXT.evolX.StrongAt g x p CV
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g V))
    (hU : Work.Diff.EXT.evolX.StrongAt g x q CT
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U))
    (a : ℕ) (w : Work.Diff.EXT.evolX.Word a)
    (F : Fin (K + 2 + a) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    |Work.Diff.EXT.evolX.Stw (I := I) (M := M) g V U a w F x|
      ≤ CT (Work.Diff.EXT.evolX.wCntT w) * CV (Work.Diff.EXT.evolX.wCntF w)
        * Real.sqrt (Work.Diff.EXT.curvNormK g x (q + Work.Diff.EXT.evolX.wCntT w))
        * Real.sqrt (Work.Diff.EXT.curvNormK g x (p + Work.Diff.EXT.evolX.wCntF w))
        * Finset.univ.prod (fun r : Fin (K + 2 + a) =>
            Real.sqrt (g.inner x (F r x) (F r x))) := by
  classical
  -- The two factors of `Stw`: the `wCntT w`-fold covariant derivative of `U` and the
  -- `wCntF w`-fold covariant derivative of `V`.
  set W : Work.Diff.EXT.TField (I := I) (M := M) :=
    fun y => dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 a w F) y with hW
  -- A smooth field agreeing with `W` at `x` (the pairing only sees the value at `x`).
  set Wh : Work.Diff.EXT.TField (I := I) (M := M) :=
    Submission.Diff.smoothExt x (W x) with hWh
  have hWhx : Wh x = W x := Work.Diff.GE.smoothExt_apply (I := I) (M := M) x (W x)
  have hWhsm : Work.Diff.EXT.SmoothF (I := I) (M := M) Wh :=
    Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x (W x)
  have hAsm : ∀ i : Fin (K + wCntT w), Work.Diff.EXT.SmoothF (I := I) (M := M)
      (wTupA (I := I) (M := M) K 2 a w F i) := wTupA_smooth (I := I) (M := M) w F hF
  have hBsm : ∀ i : Fin (2 + wCntF w), Work.Diff.EXT.SmoothF (I := I) (M := M)
      (wTupB (I := I) (M := M) K 2 a w F i) := wTupB_smooth (I := I) (M := M) w F hF
  -- the scalars of the estimate
  set σ : ℝ := Real.sqrt (g.inner x (W x) (W x)) with hσ
  set sU : ℝ := CT (wCntT w) * Real.sqrt (curvNormK g x (q + wCntT w)) with hsU
  set sV : ℝ := CV (wCntF w) * Real.sqrt (curvNormK g x (p + wCntF w)) with hsV
  set pA : ℝ := ∏ r : Fin (K + wCntT w),
    Real.sqrt (g.inner x (wTupA (I := I) (M := M) K 2 a w F r x)
      (wTupA (I := I) (M := M) K 2 a w F r x)) with hpA
  set pB : ℝ := ∏ r : Fin (2 + wCntF w),
    Real.sqrt (g.inner x (wTupB (I := I) (M := M) K 2 a w F r x)
      (wTupB (I := I) (M := M) K 2 a w F r x)) with hpB
  set P : ℝ := ∏ r : Fin (K + 2 + a),
    Real.sqrt (g.inner x (F r x) (F r x)) with hP
  -- nonnegativity of the pieces
  have hWnn : 0 ≤ g.inner x (W x) (W x) :=
    Work.Diff.EXT.smet_inner_self_nonneg (I := I) (M := M) g x (W x)
  have hsUnn : 0 ≤ sU := by rw [hsU]; exact mul_nonneg (hCT _) (Real.sqrt_nonneg _)
  have hsVnn : 0 ≤ sV := by rw [hsV]; exact mul_nonneg (hCV _) (Real.sqrt_nonneg _)
  have hpAnn : 0 ≤ pA := by
    rw [hpA]; exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hpBnn : 0 ≤ pB := by
    rw [hpB]; exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  -- smoothness of the tuples of `dvcTup` (needed to invoke `StrongAt`)
  have hUsm : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      (dvcTup (I := I) (M := M) K (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) Wh i) :=
    stb_dvcTup_smooth (I := I) (M := M)
      (wTupA (I := I) (M := M) K 2 a w F) Wh hAsm hWhsm
  have hVsm : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      (dvcTup (I := I) (M := M) 2 (wCntF w) (wTupB (I := I) (M := M) K 2 a w F) Wh i) :=
    stb_dvcTup_smooth (I := I) (M := M)
      (wTupB (I := I) (M := M) K 2 a w F) Wh hBsm hWhsm
  -- the pairing identities of `pairVecJetAll`
  have hpairU := stb_pairVec_jet (I := I) (M := M) hLC g x U hUs (wCntT w)
    (wTupA (I := I) (M := M) K 2 a w F) hAsm Wh hWhsm
  have hpairV := stb_pairVec_jet (I := I) (M := M) hLC g x V hVs (wCntF w)
    (wTupB (I := I) (M := M) K 2 a w F) hBsm Wh hWhsm
  have hStw : Stw (I := I) (M := M) g V U a w F x
      = g.inner x (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) x) (Wh x) := by
    show g.inner x (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) x)
        (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 a w F) x)
      = g.inner x (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) x) (Wh x)
    rw [hWhx]
  have hStw2 : Stw (I := I) (M := M) g V U a w F x
      = jetAll g (wCntT w) (K + 1) (pairVec (I := I) (M := M) g U)
          (dvcTup (I := I) (M := M) K (wCntT w)
            (wTupA (I := I) (M := M) K 2 a w F) Wh) x := hStw.trans hpairU
  -- the product of norms on the `U`-side
  have hprodU : (∏ r : Fin ((K + 1) + wCntT w),
        Real.sqrt (g.inner x (dvcTup (I := I) (M := M) K (wCntT w)
            (wTupA (I := I) (M := M) K 2 a w F) Wh r x)
          (dvcTup (I := I) (M := M) K (wCntT w)
            (wTupA (I := I) (M := M) K 2 a w F) Wh r x))) = pA * σ := by
    rw [stw_prod_dvcTup (I := I) (M := M) g x (K := K) (j := wCntT w)
      (wTupA (I := I) (M := M) K 2 a w F) Wh]
    rw [← hpA, hWhx, ← hσ]
  have h1 : |jetAll g (wCntT w) (K + 1) (pairVec (I := I) (M := M) g U)
        (dvcTup (I := I) (M := M) K (wCntT w)
          (wTupA (I := I) (M := M) K 2 a w F) Wh) x| ≤ sU * (pA * σ) := by
    have h := hU (wCntT w) (dvcTup (I := I) (M := M) K (wCntT w)
      (wTupA (I := I) (M := M) K 2 a w F) Wh) hUsm
    rw [hprodU, ← hsU] at h
    exact h
  -- the pairing identity on the `V`-side, and its bound
  have hpairVs : g.inner x (W x) (W x)
      = jetAll g (wCntF w) (2 + 1) (pairVec (I := I) (M := M) g V)
          (dvcTup (I := I) (M := M) 2 (wCntF w)
            (wTupB (I := I) (M := M) K 2 a w F) Wh) x := by
    have h := hpairV
    rw [hWhx] at h
    exact h
  have hprodV : (∏ r : Fin ((2 + 1) + wCntF w),
        Real.sqrt (g.inner x (dvcTup (I := I) (M := M) 2 (wCntF w)
            (wTupB (I := I) (M := M) K 2 a w F) Wh r x)
          (dvcTup (I := I) (M := M) 2 (wCntF w)
            (wTupB (I := I) (M := M) K 2 a w F) Wh r x))) = pB * σ := by
    rw [stw_prod_dvcTup (I := I) (M := M) g x (K := 2) (j := wCntF w)
      (wTupB (I := I) (M := M) K 2 a w F) Wh]
    rw [← hpB, hWhx, ← hσ]
  have hVb : |g.inner x (W x) (W x)| ≤ sV * (pB * σ) := by
    have h := hV (wCntF w) (dvcTup (I := I) (M := M) 2 (wCntF w)
      (wTupB (I := I) (M := M) K 2 a w F) Wh) hVsm
    rw [← hpairVs, hprodV, ← hsV] at h
    exact h
  -- from the `V`-bound to the bound on the norm `σ` of `W x`
  have hσle : σ ≤ sV * pB := by
    have hsq : σ * σ = g.inner x (W x) (W x) := by
      rw [hσ]; simpa [sq] using Real.sq_sqrt hWnn
    have hineq : σ * σ ≤ sV * pB * σ := by
      rw [hsq]
      have h := hVb
      rw [abs_of_nonneg hWnn] at h
      calc g.inner x (W x) (W x) ≤ sV * (pB * σ) := h
        _ = sV * pB * σ := by ring
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (g.inner x (W x) (W x))) with h0 | hpos
    · rw [← hσ] at h0
      rw [← h0]
      exact mul_nonneg hsVnn hpBnn
    · rw [← hσ] at hpos
      exact le_of_mul_le_mul_right hineq hpos
  -- the splitting of the product of norms of the whole tuple
  have hsplit : pA * pB = P := by
    rw [hpA, hpB, hP]
    exact wMonBound_prodSplitTup (I := I) (M := M) g K 2 a w F x
  calc |Stw (I := I) (M := M) g V U a w F x|
      = |jetAll g (wCntT w) (K + 1) (pairVec (I := I) (M := M) g U)
          (dvcTup (I := I) (M := M) K (wCntT w)
            (wTupA (I := I) (M := M) K 2 a w F) Wh) x| := by rw [hStw2]
    _ ≤ sU * (pA * σ) := h1
    _ ≤ sU * (pA * (sV * pB)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσle hpAnn) hsUnn
    _ = sU * (sV * (pA * pB)) := by ring
    _ = sU * (sV * P) := by rw [hsplit]
    _ = CT (wCntT w) * CV (wCntF w) * Real.sqrt (curvNormK g x (q + wCntT w))
        * Real.sqrt (curvNormK g x (p + wCntF w)) * P := by rw [hsU, hsV]; ring

end Work.Diff.EXT.evolX
