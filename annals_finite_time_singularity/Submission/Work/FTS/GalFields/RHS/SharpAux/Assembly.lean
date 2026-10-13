/-
# `SharpAux/Assembly` — the assembly of `sharp_N_diff` from the twenty term bounds

This file reduces `sharp_N_diff` to

* the two term-bound bundles `WlInfTermsBound` and `HonestTermsBound` (`SharpAux/`), and
* the master identity `Sharp.N_diff_eq_sum` (`SharpAux/Identity.lean`),

assembling them into the four clauses of the statement:

1. `SmoothOpen` of the difference (from `smoothOpen_atoms_of_gal` + `smoothOpen_sub`),
2. `HkMem α 4` of the difference (from the term `HkMem`s, the sum lemma below and
   `HkMem_congr_Q0`),
3. the `ℋ⁴`-bound `Xn α (N g - N g') ≤ K(1+|g|_{ℋ⁵}+|g'|_{ℋ⁵})|h|_{ℋ⁵}` (from the identity and
   the term bounds through `HkNorm_foldr_le`),
4. the `L₁₂`-clause at `z = 0` (from `l12zero` applied to the difference, the additivity of
   `L₁₂` and clause 3).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.RHS.SharpAux.Identity
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.NonlinRows.NRow5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The twenty terms as a list -/

/-- The twenty monomials of the difference, in the order of the identity. -/
def termList (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) : List Fn :=
  [TRA α Φs h, TRB α EllSol g' h, TRC α EllSol h, TRD α EllSol g h,
   TUA α Φs h, TUB α EllSol g' h, TUC α EllSol h, TUD α EllSol g h,
   TVA α Φs h, TVB α EllSol g' h, TVC α EllSol h, TVD α EllSol g h,
   TDA α h, TDB α g' h, TDC α h, TDD α g h,
   TEA α h, TEB α g' h, TEC α h, TED α g h]

/-- The folded sum of the list is the left-associated chain of the identity. -/
theorem termList_foldr (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) :
    (termList α Φs EllSol g g' h).foldr (fun f acc => f + acc) (0 : Fn)
      = (TRA α Φs h + TRB α EllSol g' h + TRC α EllSol h + TRD α EllSol g h
        + TUA α Φs h + TUB α EllSol g' h + TUC α EllSol h + TUD α EllSol g h
        + TVA α Φs h + TVB α EllSol g' h + TVC α EllSol h + TVD α EllSol g h
        + TDA α h + TDB α g' h + TDC α h + TDD α g h
        + TEA α h + TEB α g' h + TEC α h + TED α g h) := by
  simp only [termList, List.foldr_cons, List.foldr_nil]
  abel

/-- The length of the term list is `20`. -/
theorem termList_length (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g g' h : Fn) :
    (termList α Φs EllSol g g' h).length = 20 := rfl

/-! ## Sums over lists -/

/-- The sum of a list of `SmoothOpen` functions is `SmoothOpen`. -/
theorem smoothOpen_listFoldr (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (L.foldr (fun f acc => f + acc) (0 : Fn)) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0, Work.FTS.EllipticEst.SmoothOpen]
      exact (contDiffOn_const (c := (0 : ℝ)) (s := Work.FTS.EllipticEst.Q0)).congr
        (fun p _ => rfl)
  | cons f L ih =>
      rw [List.foldr_cons]
      exact Work.FTS.EllipticEst.smoothOpen_add (hS f (by simp))
        (ih (fun a ha => hS a (by simp [ha])))

/-- The sum of a list of `HkMem α 4` functions is `HkMem α 4`. -/
theorem HkMem_listFoldr {α : ℝ} (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f)
    (hM : ∀ f ∈ L, Work.Spaces.HkMem α 4 f) :
    Work.Spaces.HkMem α 4 (L.foldr (fun f acc => f + acc) (0 : Fn)) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0]
      exact Work.FTS.LocData.HkMem_zero_fun α 4
  | cons f L ih =>
      rw [List.foldr_cons]
      exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 (hS f (by simp))
        (smoothOpen_listFoldr L (fun a ha => hS a (by simp [ha])))
        (hM f (by simp)) (ih (fun a ha => hS a (by simp [ha])) (fun a ha => hM a (by simp [ha])))

/-- **The `ℋ⁴`-norm of a list-sum**: with the factor `2^{length}`. -/
theorem HkNorm_listFoldr_le {α : ℝ} (hα : 0 < α) (L : List Fn)
    (hS : ∀ f ∈ L, Work.FTS.EllipticEst.SmoothOpen f)
    (hM : ∀ f ∈ L, Work.Spaces.HkMem α 4 f) :
    Work.FTS.Nonlin.Xn α (L.foldr (fun f acc => f + acc) (0 : Fn))
      ≤ 2 ^ L.length * (L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
  induction L with
  | nil =>
      have h0 : ([] : List Fn).foldr (fun f acc => f + acc) (0 : Fn) = fun _ _ => (0 : ℝ) := rfl
      rw [h0, List.length_nil, List.foldr_nil, pow_zero, one_mul]
      have hz : Work.FTS.Nonlin.Xn α (fun _ _ => (0 : ℝ)) = 0 := by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.Spaces.HkSq]
        rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun _ _ => (0 : ℝ)) z θ) = fun _ => (0 : ℝ) from by
          funext z
          simp only [Work.FTS.GalFields.RHS.HkIntegrand_zero_fun, MeasureTheory.integral_zero]]
        simp
      rw [hz]
  | cons f L ih =>
      rw [List.foldr_cons, List.length_cons, List.foldr_cons]
      have hfl : ∀ a ∈ L, Work.FTS.EllipticEst.SmoothOpen a := fun a ha => hS a (by simp [ha])
      have hml : ∀ a ∈ L, Work.Spaces.HkMem α 4 a := fun a ha => hM a (by simp [ha])
      have hsmS := smoothOpen_listFoldr L hfl
      have hmS := HkMem_listFoldr L hfl hml
      have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα (hS f (by simp)) hsmS
        (hM f (by simp)) hmS
      have hih := ih hfl hml
      have hpow : (1 : ℝ) ≤ 2 ^ L.length := one_le_pow₀ (by norm_num)
      have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
      have hsum0 : 0 ≤ L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0 := by
        have : ∀ (M : List Fn), 0 ≤ M.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0 := by
          intro M
          induction M with
          | nil => simp
          | cons a M ih2 =>
              rw [List.foldr_cons]
              exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 a) ih2
        exact this L
      calc Work.FTS.Nonlin.Xn α
            ((f :: L).foldr (fun f acc => f + acc) (0 : Fn))
          = Work.FTS.Nonlin.Xn α (f + L.foldr (fun f acc => f + acc) (0 : Fn)) := by
            rw [List.foldr_cons]
        _ ≤ 2 * (Work.FTS.Nonlin.Xn α f
              + Work.FTS.Nonlin.Xn α (L.foldr (fun f acc => f + acc) (0 : Fn))) := hstep
        _ ≤ 2 * (Work.FTS.Nonlin.Xn α f
              + 2 ^ L.length * (L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact add_le_add (le_refl _) hih
        _ ≤ 2 ^ (L.length + 1)
              * (Work.FTS.Nonlin.Xn α f + L.foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
            rw [pow_succ]
            nlinarith [hpow, hXf, hsum0]
        _ = 2 ^ (f :: L).length
              * ((f :: L).foldr (fun f acc => Work.FTS.Nonlin.Xn α f + acc) 0) := by
            rw [List.length_cons, List.foldr_cons]

end Work.FTS.GalFields.RHS.Sharp
