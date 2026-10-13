/-
  WilE9 / Sharp / ExFst — the four structural *branches* of the pulled-back system.

  A solution `Φ` of the pulled-back system `pbChain c`, `pbF n m r h` near `x₀` is, on the
  good locus `w i = Φ (fW i) > 0`, `u = Φ (fU) > 0`, forced onto the `ψ`-graph: the equations

  * `fS`  : `τ - s * u = 0`,
  * `fY i`: `y i - x i * w i = 0`,
  * `fW i`: `y i ^ 2 + w i ^ 2 - 1 = 0`,
  * `fT`  : `τ ^ 2 + u ^ 2 - 1 = 0`

  are the only ones needed, and combined with the strict positivity of `w i` and `u` (which
  `ContDiffAt` propagates from `x₀` to a neighbourhood) they pin the square-root branches:

  `y i = ψ (x i)`, `w i = psig (x i)`, `τ = ψ s`, `u = psig s`, with `s = Φ x (fS n m)`.

  The content is therefore purely algebraic (`circleBranch`) once the equations have been read
  off `pbF` (`eaEval_pbF_fS/fY/fW/fT`) at the ambient point `appendPt x (Φ x) = Fin.append x (Φ x)`
  (`ExFst/AppPt.lean`).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.PbSystem
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.ExFst.AppPt

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp.ExFst
open WilkiesDesign WilkiesDesign.E
open Work.WilE9.Sharp

/-! ## 1. Reading the four algebraic equations of `pbF` off -/

private theorem eaEval_pbF_fS {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fS n m)) (appendPt x y)
      = y (fT n m) - y (fS n m) * y (fU n m) := by
  have h0 : ((fS n m : Fin (qpb n m)) : ℕ) = 0 := rfl
  rw [pbF]
  rw [dif_pos h0]
  simp only [eaEval, Sum.elim_inl, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, appendPt_pbT, appendPt_pbS, appendPt_pbU]

private theorem eaEval_pbF_fY {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ)
    (i : Fin n) :
    eaEval (pbChain c) (pbF n m r h (fY n m i)) (appendPt x y)
      = y (fY n m i) - x i * y (fW n m i) := by
  have h0 : ¬ (((fY n m i : Fin (qpb n m)) : ℕ) = 0) := by simp only [fY]; omega
  have h1 : (((fY n m i : Fin (qpb n m)) : ℕ)) ≤ n := by simp only [fY]; omega
  have hidx : (⟨((fY n m i : Fin (qpb n m)) : ℕ) - 1, by omega⟩ : Fin n) = i :=
    Fin.ext (by simp only [fY]; omega)
  rw [pbF]
  rw [dif_neg h0]
  rw [dif_pos h1]
  dsimp only
  rw [hidx]
  simp only [eaEval, Sum.elim_inl, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, appendPt_pbY, appendPt_pbX, appendPt_pbW]

private theorem eaEval_pbF_fW {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ)
    (i : Fin n) :
    eaEval (pbChain c) (pbF n m r h (fW n m i)) (appendPt x y)
      = y (fY n m i) ^ 2 + y (fW n m i) ^ 2 - 1 := by
  have h0 : ¬ (((fW n m i : Fin (qpb n m)) : ℕ) = 0) := by simp only [fW]; omega
  have h1 : ¬ (((fW n m i : Fin (qpb n m)) : ℕ) ≤ n) := by simp only [fW]; omega
  have h2 : (((fW n m i : Fin (qpb n m)) : ℕ)) ≤ 2 * n := by simp only [fW]; omega
  have hidx : (⟨((fW n m i : Fin (qpb n m)) : ℕ) - n - 1,
      by simp only [fW]; omega⟩ : Fin n) = i :=
    Fin.ext (by simp only [fW]; omega)
  rw [pbF]
  rw [dif_neg h0]
  rw [dif_neg h1]
  rw [dif_pos h2]
  dsimp only
  rw [hidx]
  simp only [eaEval, Sum.elim_inl, MvPolynomial.eval_sub, MvPolynomial.eval_add,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, map_one, appendPt_pbY, appendPt_pbW]

private theorem eaEval_pbF_fT {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fT n m)) (appendPt x y)
      = y (fT n m) ^ 2 + y (fU n m) ^ 2 - 1 := by
  have h0 : ¬ (((fT n m : Fin (qpb n m)) : ℕ) = 0) := by simp only [fT]; omega
  have h1 : ¬ (((fT n m : Fin (qpb n m)) : ℕ) ≤ n) := by simp only [fT]; omega
  have h2 : ¬ (((fT n m : Fin (qpb n m)) : ℕ) ≤ 2 * n) := by simp only [fT]; omega
  have h3 : (((fT n m : Fin (qpb n m)) : ℕ)) = 2 * n + 1 := rfl
  rw [pbF]
  rw [dif_neg h0]
  rw [dif_neg h1]
  rw [dif_neg h2]
  rw [dif_pos h3]
  simp only [eaEval, Sum.elim_inl, MvPolynomial.eval_sub, MvPolynomial.eval_add,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, map_one, appendPt_pbT, appendPt_pbU]

/-! ## 2. The circle: `y = x w`, `y² + w² = 1`, `w > 0` force `(y, w) = (ψ x, psig x)` -/

/-- **The branch of the unit circle cut by `w > 0`.**  `y = x w` and `y² + w² = 1` give
`w² (1 + x²) = 1`; `w > 0` selects the positive square root, so `w = (1+x²)^{-1/2} = psig x` and
then `y = x · psig x = ψ x`.  This is the converse of `Psi.psi_psig_algebra`, and it is exactly
what pins the `ψ`-coordinates of a solution of the pulled-back system. -/
private theorem circleBranch {x y w : ℝ} (hy : y = x * w) (hsq : y ^ 2 + w ^ 2 = 1) (hwp : 0 < w) :
    w = Work.WilE9.psig x ∧ y = WilkiesDesign.E.psi x := by
  have h1x : 0 < 1 + x ^ 2 := by positivity
  have hpsig_pos : 0 < Work.WilE9.psig x := by rw [Work.WilE9.psig]; positivity
  -- `psig x` is the positive solution of the same quadratic equation
  have hsq_psig : Work.WilE9.psig x ^ 2 * (1 + x ^ 2) = 1 := by
    rw [Work.WilE9.psig]
    have h : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  -- hence `w² = psig x²`
  have hsquare : w ^ 2 = Work.WilE9.psig x ^ 2 := by
    have h2 : (x * w) ^ 2 + w ^ 2 = 1 := by rw [← hy]; exact hsq
    have h : w ^ 2 * (1 + x ^ 2) = 1 := by
      calc w ^ 2 * (1 + x ^ 2) = (x * w) ^ 2 + w ^ 2 := by ring
        _ = 1 := h2
    exact mul_right_cancel₀ (ne_of_gt h1x) (by rw [h, hsq_psig])
  -- and the positivity of both sides selects the sign
  have hw_eq : w = Work.WilE9.psig x := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
    · exact h
    · exfalso; nlinarith [hpsig_pos, hwp]
  refine ⟨hw_eq, ?_⟩
  rw [hy, hw_eq, WilkiesDesign.E.psi, Work.WilE9.psig]
  ring

/-! ## 3. The branch theorem -/

theorem exFst_pbF_branch {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r)
    (Φ : (Fin n → ℝ) → (Fin (Work.WilE9.Sharp.qpb n m) → ℝ)) (x₀ : Fin n → ℝ)
    (hcd : ContDiffAt ℝ ⊤ Φ x₀)
    (hs : Work.WilE9.IsSoln (Work.WilE9.Sharp.pbChain c) (Work.WilE9.Sharp.pbF n m r h) Φ x₀)
    (hw : ∀ i : Fin n, 0 < Φ x₀ (Work.WilE9.Sharp.fW n m i))
    (hu : 0 < Φ x₀ (Work.WilE9.Sharp.fU n m)) :
    ∀ᶠ x in nhds x₀,
      (∀ i : Fin n, Φ x (Work.WilE9.Sharp.fY n m i) = WilkiesDesign.E.psi (x i)) ∧
      (∀ i : Fin n, Φ x (Work.WilE9.Sharp.fW n m i) = Work.WilE9.psig (x i)) ∧
      Φ x (Work.WilE9.Sharp.fT n m) = WilkiesDesign.E.psi (Φ x (Work.WilE9.Sharp.fS n m)) ∧
      Φ x (Work.WilE9.Sharp.fU n m) = Work.WilE9.psig (Φ x (Work.WilE9.Sharp.fS n m)) := by
  -- each coordinate of `Φ` is continuous at `x₀`, so the strict positivity at `x₀` persists
  have hcont : ∀ j : Fin (qpb n m), ContinuousAt (fun x : Fin n → ℝ => Φ x j) x₀ := fun j =>
    (continuous_apply j).continuousAt.comp hcd.continuousAt
  have hwpos : ∀ i : Fin n, ∀ᶠ x in nhds x₀, 0 < Φ x (fW n m i) := fun i =>
    (hcont (fW n m i)).eventually (eventually_gt_nhds (hw i))
  have hupos : ∀ᶠ x in nhds x₀, 0 < Φ x (fU n m) :=
    (hcont (fU n m)).eventually (eventually_gt_nhds hu)
  -- the four equations of `pbF`, read off at the ambient point `(x, Φ x)`
  have hS : ∀ᶠ x in nhds x₀, Φ x (fT n m) - Φ x (fS n m) * Φ x (fU n m) = 0 := by
    filter_upwards [hs.1] with x hx
    have h1 : eaEval (pbChain c) (pbF n m r h (fS n m)) (appendPt x (Φ x)) = 0 := hx (fS n m)
    rw [eaEval_pbF_fS] at h1
    exact h1
  have hY : ∀ i : Fin n, ∀ᶠ x in nhds x₀, Φ x (fY n m i) - x i * Φ x (fW n m i) = 0 := by
    intro i
    filter_upwards [hs.1] with x hx
    have h1 : eaEval (pbChain c) (pbF n m r h (fY n m i)) (appendPt x (Φ x)) = 0 :=
      hx (fY n m i)
    rw [eaEval_pbF_fY] at h1
    exact h1
  have hW : ∀ i : Fin n, ∀ᶠ x in nhds x₀,
      Φ x (fY n m i) ^ 2 + Φ x (fW n m i) ^ 2 - 1 = 0 := by
    intro i
    filter_upwards [hs.1] with x hx
    have h1 : eaEval (pbChain c) (pbF n m r h (fW n m i)) (appendPt x (Φ x)) = 0 :=
      hx (fW n m i)
    rw [eaEval_pbF_fW] at h1
    exact h1
  have hT : ∀ᶠ x in nhds x₀, Φ x (fT n m) ^ 2 + Φ x (fU n m) ^ 2 - 1 = 0 := by
    filter_upwards [hs.1] with x hx
    have h1 : eaEval (pbChain c) (pbF n m r h (fT n m)) (appendPt x (Φ x)) = 0 := hx (fT n m)
    rw [eaEval_pbF_fT] at h1
    exact h1
  filter_upwards [hS, Filter.eventually_all.mpr hY, Filter.eventually_all.mpr hW, hT,
    Filter.eventually_all.mpr hwpos, hupos] with x hSx hYx hWx hTx hwx hux
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact (circleBranch (x := x i) (y := Φ x (fY n m i)) (w := Φ x (fW n m i))
      (by linarith [hYx i]) (by linarith [hWx i]) (hwx i)).2
  · exact (circleBranch (x := x i) (y := Φ x (fY n m i)) (w := Φ x (fW n m i))
      (by linarith [hYx i]) (by linarith [hWx i]) (hwx i)).1
  · exact (circleBranch (x := Φ x (fS n m)) (y := Φ x (fT n m)) (w := Φ x (fU n m))
      (by linarith [hSx]) (by linarith [hTx]) hux).2
  · exact (circleBranch (x := Φ x (fS n m)) (y := Φ x (fT n m)) (w := Φ x (fU n m))
      (by linarith [hSx]) (by linarith [hTx]) hux).1

end Work.WilE9.Sharp.ExFst
