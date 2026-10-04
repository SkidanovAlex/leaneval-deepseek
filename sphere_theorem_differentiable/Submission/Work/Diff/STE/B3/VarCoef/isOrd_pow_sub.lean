import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.VarCoef.isOrd_commOp_iterate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The difference of two powers of order-`2` operators

`IsOrd d C T` (see `Submission/Work/Diff/STE/B3/VarCoef/OpOrder.lean`) records that the operator `T`
preserves smooth `1`-periodic functions, is `ℂ`-linear on them, and is of order at most `d` on the
weighted integer Sobolev scale `CSqZ`.

Here we prove that if two order-`2` operators `D`, `E` are *close*, in the sense that the
difference `D - E` is itself an operator of order `1`, then the difference of the `k`-th powers,

`D^[k] - E^[k]`,

is an operator of order `2k - 1`.  This is the quantitative form of the fact that `D - E` "gains one
derivative": naively `D^[k] - E^[k]` would only be of order `2k`, but the telescoping expansion

`D^[k] - E^[k] = ∑_{i} D^{k-1-i} (D - E) E^{i}`

exhibits `2k - 1` derivatives.  The proof is the two-term telescoping identity

`D^[k+1] - E^[k+1] = D^[k]·(D - E) + (D^[k] - E^[k])·E`,

whose summands have orders `2k + 1` and `(2k - 1) + 2 = 2k + 1` respectively; the second one has to
be pulled through `E`, which uses the `ℂ`-linearity of `D^[k]` provided by `IsOrd.lin`.  For
`k = 0` the operator is `id - id = 0`, which has *every* order (`IsOrd.zero_any`), in particular the
negative order `-1`; this is why the statement is not vacuous at `k = 0`.
-/

namespace Work.Diff.STE.B3.VarCoef

theorem isOrd_pow_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D E : Work.Diff.STE.B3.VarCoef.Op ι} {CD CE CDE : ℤ → ℝ}
    (hD : Work.Diff.STE.B3.VarCoef.IsOrd 2 CD D)
    (hE : Work.Diff.STE.B3.VarCoef.IsOrd 2 CE E)
    (hDE : Work.Diff.STE.B3.VarCoef.IsOrd 1 CDE (D - E)) (k : ℕ) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C (D^[k] - E^[k]) := by
  induction k with
  | zero =>
      -- `D^[0] - E^[0] = id - id = 0`, the zero operator, which has every order.
      refine ⟨fun _ => 0, ?_⟩
      have hkey : 2 * (((0 : ℕ)) : ℤ) - 1 = (-1 : ℤ) := by norm_num
      rw [hkey]
      refine IsOrd.congr (IsOrd.zero_any (-1)) ?_
      intro f hf
      show (0 : Op ι) f = (D^[0] - E^[0]) f
      simp only [Pi.sub_apply]
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, sub_self]
      rfl
  | succ k ih =>
      obtain ⟨Ck, hCk⟩ := ih
      obtain ⟨CDk, hDk⟩ := isOrd_iterate_pow hD k
      -- `D^[k]·(D - E)` has order `2k + 1`.
      have h1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) + 1) C (fun f => D^[k] ((D - E) f)) :=
        ⟨_, IsOrd.comp hDk hDE⟩
      -- `(D^[k] - E^[k])·E` has order `(2k - 1) + 2 = 2k + 1`.
      have h2 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) + 1) C
          (fun f => (D^[k] - E^[k]) (E f)) :=
        ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) + 1) (IsOrd.comp hCk hE) (by omega)⟩
      obtain ⟨C1, hC1⟩ := h1
      obtain ⟨C2, hC2⟩ := h2
      have hsum := IsOrd.add hC1 hC2
      refine ⟨fun t => 2 * (C1 t + C2 t), ?_⟩
      refine IsOrd.mono_d (d := 2 * (↑(k+1) : ℤ) - 1) (d' := 2 * (k : ℤ) + 1) ?_ ?_
      · refine IsOrd.congr hsum ?_
        intro f hf
        have hDf : SmoothPer (D f) := hD.pres f hf
        have hEf : SmoothPer (E f) := hE.pres f hf
        -- split `D^[k] (D f - E f)` using the `ℂ`-linearity of `D^[k]`.
        have hsplit : D^[k] (D f - E f) = D^[k] (D f) - D^[k] (E f) :=
          linSP_map_sub hDk.lin hDf hEf
        have hsuccD : D^[k] (D f) = D^[k+1] f := (Function.iterate_succ_apply D k f).symm
        have hsuccE : E^[k] (E f) = E^[k+1] f := (Function.iterate_succ_apply E k f).symm
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [hsplit, hsuccD, hsuccE]
        ring
      · push_cast
        omega

end Work.Diff.STE.B3.VarCoef
