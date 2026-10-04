import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Iterated commutators `[L, D^[j]]` in the order calculus of `VarCoef`

`IsOrd d C T` (see `Submission/Work/Diff/STE/B3/VarCoef/OpOrder.lean`) records that an operator `T`
preserves smooth `1`-periodic functions, is `ℂ`-linear on them, and is of order at most `d` on the
weighted integer Sobolev scale `CSqZ`:

`CSqZ (t - d) (fourierCoeff (T f)) ≤ C t * CSqZ t (fourierCoeff f)`.

The main result of this file is the *iterated* commutator estimate:

> if `D` has order `2` and the commutator `[L,D]` has order `δ`, then for every `j : ℕ` the
> operator `[L, D^[j]]` has order `δ + 2j - 2`.

This is the quantitative form of "a commutator gains one order".  Indeed `D^[j]` has order `2j`
(composition multiplies orders), so the trivial bound for `[L,D^[j]]` would be `δ + 2j`; the true
order is *two less*, because `[L, D^[j]]` is an iterated commutator and only the one `D` that is
left behind costs its full two orders.

The proof is the standard Leibniz/telescoping induction
`[L, D^{j+1}] = [L,D]·D^j + D·[L,D^j]`, whose two summands have orders `δ + 2j` and
`2 + (δ + 2j - 2) = δ + 2j` respectively, and whose sum is `[L, D^{j+1}]` by the pointwise identity
`(L D^{j+1} - D^{j+1} L) = (L D - D L) D^j + D (L D^j - D^j L)`.  The crucial point is that the
second summand has to be pulled through `D`; this uses the `ℂ`-linearity of `D` on smooth periodic
functions (`IsOrd.lin`).  The hypotheses `LinSP L` and `Preserves L` are what make `[L, ·]` an
operation on smooth periodic functions; `LinSP L` is only needed for the surrounding development
(the induction itself uses `IsOrd.lin` of `D` and `Preserves L`).

Two small ancillary facts are recorded as well:

* `IsOrd.zero_any` — the zero operator has **every** order (needed for the base case `j = 0`, where
  `[L, id] = 0` while the target order `δ - 2` may be negative and no monotonicity in the order is
  available);
* `isOrd_iterate_pow` — a power `D^[k]` of an operator of order `d` has order `d * k`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero operator has **every** order `d : ℤ`.  (For `d ≤ 0` this does not follow from the
order-`0` statement `IsOrd.zero`, since `IsOrd.mono_d` only weakens the order.) -/
theorem IsOrd.zero_any (d : ℤ) : IsOrd d (fun _ => 0) (0 : Op ι) where
  pres := fun f _ => by
    have h : (0 : Op ι) f = 0 := rfl
    rw [h]; exact SmoothPer.zero
  lin := ⟨fun f g _ _ => by simp, fun c f _ => by simp⟩
  nonneg := fun _ => le_refl 0
  bound t f _ := by
    have h : Work.Diff.STE.fourierCoeff ((0 : Op ι) f) = 0 := by
      have h1 : (0 : Op ι) f = 0 := rfl
      rw [h1]
      funext k
      simp only [Work.Diff.STE.fourierCoeff]
      simp
    rw [h]
    simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ]
    simp

/-- A power `D^[k]` of an operator of order `d` has order `d * k`. -/
theorem isOrd_iterate_pow {d : ℤ} {C : ℤ → ℝ} {D : Op ι} (hD : IsOrd d C D) :
    ∀ k : ℕ, ∃ Ck : ℤ → ℝ, IsOrd (d * (k : ℤ)) Ck (D^[k]) := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun _ => 1, ?_⟩
      have h0 : D^[0] = (id : Op ι) := by funext f; rfl
      rw [h0]
      have hd0 : d * ((0 : ℕ) : ℤ) = 0 := by simp
      rw [hd0]
      exact IsOrd.id
  | succ k ih =>
      obtain ⟨Ck, hCk⟩ := ih
      have hcomp : IsOrd (d * ↑k + d) (fun t => C (t - d * ↑k) * Ck t)
          (fun f => D (D^[k] f)) := by
        have := IsOrd.comp hD hCk
        rwa [show d + d * (k : ℤ) = d * (k : ℤ) + d from by ring] at this
      have h1 : D^[k.succ] = (fun f => D (D^[k] f)) := by
        funext f
        exact Function.iterate_succ_apply' D k f
      rw [h1]
      refine ⟨fun t => C (t - d * ↑k) * Ck t, IsOrd.mono_d hcomp ?_⟩
      push_cast
      ring_nf
      omega

set_option linter.unusedVariables false in
theorem isOrd_commOp_iterate {ι : Type*} [Fintype ι] [DecidableEq ι] {D L : Work.Diff.STE.B3.VarCoef.Op ι}
    {CD : ℤ → ℝ} {δ : ℤ} {Cδ : ℤ → ℝ}
    (hD : Work.Diff.STE.B3.VarCoef.IsOrd 2 CD D)
    (hδ : Work.Diff.STE.B3.VarCoef.IsOrd δ Cδ (Work.Diff.STE.B3.VarCoef.commOp L D))
    (hL : Work.Diff.STE.B3.VarCoef.LinSP L) (hLp : Work.Diff.STE.B3.VarCoef.Preserves L) (j : ℕ) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (δ + 2 * (j : ℤ) - 2) C
      (Work.Diff.STE.B3.VarCoef.commOp L (D^[j])) := by
  induction j with
  | zero =>
      -- `[L, id] = 0`, which is of every order, in particular of order `δ - 2`.
      refine ⟨fun _ => 0, ?_⟩
      have h0 : D^[0] = (id : Op ι) := by funext f; rfl
      rw [h0]
      have hd : δ + 2 * ((0 : ℕ) : ℤ) - 2 = δ - 2 := by norm_num
      rw [hd]
      exact IsOrd.congr (IsOrd.zero_any (δ - 2)) (fun f _ => by
        simp only [commOp_apply]
        simp)
  | succ j ih =>
      obtain ⟨Cj, hCj⟩ := ih
      obtain ⟨Cd, hDd⟩ := isOrd_iterate_pow hD j
      -- `[L,D]·D^j` has order `δ + 2j`
      have hT1 : ∃ C : ℤ → ℝ, IsOrd (δ + 2 * (j : ℤ)) C
          (fun f => commOp L D ((D^[j]) f)) := ⟨_, IsOrd.comp hδ hDd⟩
      -- `D·[L,D^j]` has order `2 + (δ + 2j - 2) = δ + 2j`
      have hT2 : ∃ C : ℤ → ℝ, IsOrd (δ + 2 * (j : ℤ)) C
          (fun f => D (commOp L (D^[j]) f)) := by
        refine ⟨_, IsOrd.mono_d (IsOrd.comp hD hCj) ?_⟩
        omega
      obtain ⟨C1, hC1⟩ := hT1
      obtain ⟨C2, hC2⟩ := hT2
      have hsum := IsOrd.add hC1 hC2
      refine ⟨fun t => 2 * (C1 t + C2 t), ?_⟩
      -- the two summands have order `δ + 2j = δ + 2(j+1) - 2`
      refine IsOrd.congr (IsOrd.mono_d hsum ?_) ?_
      · push_cast
        ring_nf
        omega
      · -- the Leibniz identity `[L,D^{j+1}] = [L,D]·D^j + D·[L,D^j]`, pointwise
        intro f hf
        have hDfj : SmoothPer ((D^[j]) f) := hDd.pres f hf
        have hLf : SmoothPer (L f) := hLp f hf
        have hLDfj : SmoothPer (L ((D^[j]) f)) := hLp _ hDfj
        have hDfjL : SmoothPer ((D^[j]) (L f)) := hDd.pres (L f) hLf
        have hT2f : D (commOp L (D^[j]) f) = D (L ((D^[j]) f)) - D ((D^[j]) (L f)) := by
          rw [commOp_apply, linSP_map_sub hD.lin hLDfj hDfjL]
        rw [Pi.add_apply, hT2f]
        simp only [commOp_apply]
        simp only [Function.iterate_succ_apply']
        ring

end Work.Diff.STE.B3.VarCoef
