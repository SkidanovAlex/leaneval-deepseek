/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.continuousAt_coeff_Gpoly`

The coefficients of `Gshift c m = (F c (m + ·) - (m + ·))` in the *inner* variable depend
continuously on the parameter `c`, uniformly in the shift `m` (and in particular for a continuous
shift `c ↦ m c`).  This is the "everything is a finite sum of continuous functions" ingredient
used whenever the splitting polynomials of `Work.PARIMPL.ParSplit` are differentiated in the
parameter.

Two steps:

* `continuousAt_coeff_of_eval` — a polynomial of degree `≤ N` is determined by its values at the
  `N + 1` distinct points `0, 1, …, N` (Lagrange interpolation), so if `c ↦ (P c).eval t` is
  continuous at `c` for every `t` then so is `c ↦ (P c).coeff k`.  This is the only place where
  the degree bound is needed.
* The degree bound `(Gshift c m).natDegree ≤ 1024` is uniform in `c` and `m`
  (`polyF c` has degree `≤ 4 ^ 5 = 1024`, and shifting the variable does not raise the degree),
  and the values `(Gshift c m).eval t = Work.EL.F c (m + t) - (m + t)` are continuous in `c`
  because `(c, z) ↦ Work.EL.F c z = (Tsq c)^[5] z` is jointly continuous.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.phase_of_split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## Coefficients from evaluations -/

/-- A polynomial of degree `≤ N` is determined by its values at the `N + 1` distinct points
`0, 1, …, N`; hence a family of polynomials of uniformly bounded degree whose evaluations converge
pointwise has convergent coefficients. -/
private theorem continuousAt_coeff_of_eval {P : ℂ → Polynomial ℂ} {c : ℂ} {N : ℕ}
    (hdeg : ∀ c', (P c').natDegree ≤ N)
    (heval : ∀ t : ℂ, ContinuousAt (fun c' => (P c').eval t) c) (k : ℕ) :
    ContinuousAt (fun c' => (P c').coeff k) c := by
  have hdeg_lt : ∀ c', (P c').degree < ((N + 1 : ℕ) : WithBot ℕ) := by
    intro c'
    calc (P c').degree ≤ ((P c').natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (N : WithBot ℕ) := by exact_mod_cast hdeg c'
      _ < ((N + 1 : ℕ) : WithBot ℕ) := by
          rw [Nat.cast_lt]; exact Nat.lt_succ_self N
  have key : (fun c' => (P c').coeff k)
      = fun c' => ∑ i ∈ Finset.range (N + 1),
          (P c').eval ((i : ℂ)) *
            (Lagrange.basis (Finset.range (N + 1)) (fun n : ℕ => (n : ℂ)) i).coeff k := by
    funext c'
    have h1 : P c' = Lagrange.interpolate (Finset.range (N + 1)) (fun n : ℕ => (n : ℂ))
        (fun i => (P c').eval ((i : ℂ))) :=
      Lagrange.eq_interpolate (fun a _ b _ h => Nat.cast_injective h)
        (by rw [Finset.card_range]; exact hdeg_lt c')
    conv_lhs => rw [h1]
    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul]
  rw [key]
  apply tendsto_finsetSum
  intro i hi
  exact (heval ((i : ℂ))).mul_const _

/-! ## Joint continuity of `(c, z) ↦ F c z` -/

/-- The second return map `c ↦ F c = (Tsq c)^[5]` depends jointly continuously on the parameter
and the point. -/
private theorem continuous_EL_F_pair : Continuous (fun p : ℂ × ℂ => Work.EL.F p.1 p.2) := by
  have htsq : Continuous (fun p : ℂ × ℂ => Work.Landing.Tsq p.1 p.2) := by
    simp only [Work.Landing.Tsq]; fun_prop
  set Φ : ℂ × ℂ → ℂ × ℂ := fun q => (q.1, Work.Landing.Tsq q.1 q.2) with hΦdef
  have hΦ : Continuous Φ := continuous_fst.prodMk htsq
  have hiter : ∀ n : ℕ, ∀ p : ℂ × ℂ, Φ^[n] p = (p.1, (Work.Landing.Tsq p.1)^[n] p.2) := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
        intro p
        rw [Function.iterate_succ_apply']
        rw [ih p]
        simp only [hΦdef, Function.iterate_succ_apply']
  have hcont : Continuous (fun p : ℂ × ℂ => (Φ^[5] p).2) := continuous_snd.comp (hΦ.iterate 5)
  have hfun : (fun p : ℂ × ℂ => (Φ^[5] p).2) = fun p => Work.EL.F p.1 p.2 := by
    funext p
    rw [hiter 5 p]
    rfl
  rwa [hfun] at hcont

/-! ## The uniform degree bound -/

private theorem natDegree_compIter_le (q : Polynomial ℂ) (n : ℕ) :
    (compIter q n).natDegree ≤ q.natDegree ^ n := by
  induction n with
  | zero => simp [compIter]
  | succ n ih =>
      rw [compIter]
      calc ((compIter q n).comp q).natDegree ≤ (compIter q n).natDegree * q.natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ q.natDegree ^ n * q.natDegree := Nat.mul_le_mul_right _ ih
        _ = q.natDegree ^ (n + 1) := (pow_succ _ _).symm

private theorem natDegree_polyF_le (c : ℂ) : (polyF c).natDegree ≤ 1024 := by
  have hQ : ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c).natDegree ≤ 4 := by
    have hA : ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2).natDegree ≤ 4 := by
      calc ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2).natDegree
            ≤ 2 * (Polynomial.X ^ 2 + Polynomial.C (star c)).natDegree := Polynomial.natDegree_pow_le
        _ ≤ 2 * 2 := by
              gcongr
              calc (Polynomial.X ^ 2 + Polynomial.C (star c)).natDegree
                  ≤ max (Polynomial.X ^ 2).natDegree (Polynomial.C (star c)).natDegree :=
                    Polynomial.natDegree_add_le _ _
                _ = 2 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]; norm_num
        _ = 4 := by norm_num
    calc ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c).natDegree
          ≤ max ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2).natDegree (Polynomial.C c).natDegree :=
            Polynomial.natDegree_add_le _ _
      _ ≤ 4 := by rw [Polynomial.natDegree_C]; omega
  rw [polyF]
  exact (natDegree_compIter_le _ 5).trans
    (le_trans (Nat.pow_le_pow_left hQ 5) (le_of_eq (by norm_num)))

/-- Uniform degree bound for the shifted difference polynomial, independent of `c` and `m`. -/
private theorem natDegree_Gpoly_le (c m : ℂ) : (Gshift c m).natDegree ≤ 1024 := by
  have hXm : (Polynomial.X + Polynomial.C m).natDegree ≤ 1 := by
    calc (Polynomial.X + Polynomial.C m).natDegree
        ≤ max (Polynomial.X).natDegree (Polynomial.C m).natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by rw [Polynomial.natDegree_X, Polynomial.natDegree_C]; norm_num
  rw [Gshift]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · calc ((polyF c).comp (Polynomial.X + Polynomial.C m)).natDegree
        ≤ (polyF c).natDegree * (Polynomial.X + Polynomial.C m).natDegree := Polynomial.natDegree_comp_le
      _ ≤ 1024 * 1 := Nat.mul_le_mul (natDegree_polyF_le c) hXm
      _ = 1024 := by norm_num
  · exact hXm.trans (by norm_num)

/-! ## The target -/

theorem continuousAt_coeff_Gpoly {c : ℂ} {m : ℂ → ℂ} (hm : ContinuousAt m c) (k : ℕ) :
    ContinuousAt (fun c' : ℂ => (Work.PARIMPL.ParSplit.Gshift c' (m c')).coeff k) c := by
  have heval : ∀ t : ℂ, ContinuousAt (fun c' : ℂ => (Gshift c' (m c')).eval t) c := by
    intro t
    have hf : ContinuousAt (fun c' : ℂ => ((c' : ℂ), m c' + t)) c :=
      continuousAt_id.prodMk (hm.add_const t)
    have hg : ContinuousAt (fun p : ℂ × ℂ => Work.EL.F p.1 p.2) (c, m c + t) :=
      continuous_EL_F_pair.continuousAt
    have h1 : ContinuousAt (fun c' : ℂ => Work.EL.F c' (m c' + t)) c :=
      ContinuousAt.comp (g := fun p : ℂ × ℂ => Work.EL.F p.1 p.2)
        (f := fun c' : ℂ => ((c' : ℂ), m c' + t)) (x := c) hg hf
    have h2 : ContinuousAt (fun c' : ℂ => m c' + t) c := hm.add_const t
    have hfun : (fun c' : ℂ => (Gshift c' (m c')).eval t)
        = fun c' : ℂ => Work.EL.F c' (m c' + t) - (m c' + t) :=
      funext (fun c' => Gshift_eval c' (m c') t)
    rw [hfun]
    exact h1.sub h2
  exact continuousAt_coeff_of_eval (fun c' => natDegree_Gpoly_le c' (m c')) heval k

end Work.PARIMPL.ParSplit
