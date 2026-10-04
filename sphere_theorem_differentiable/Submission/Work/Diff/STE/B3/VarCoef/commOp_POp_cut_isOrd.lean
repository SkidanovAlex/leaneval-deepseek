import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `commOp_POp_cut_isOrd`: the commutator `[S, P]` with `P = M_{c'} ∘ D^k ∘ M_c` is of order `2k - 1`

This is the second half of step 3 of the route of `varLapPow_cut_comm_pairing`: the composite
operator `P = POp c c' D k = M_{c'} ∘ D^k ∘ M_c` (with `D^[k]` of order `2k`) commutes with the
cutoff `S` up to order `2k - 1`, *once the three basic commutators*
`[S, D^k]`, `[S, M_c]`, `[S, M_{c'}]` (of orders `2k - 1`, `-1`, `-1`) *are supplied*.

The two Leibniz identities of the order calculus
(`Work.Diff.STE.B3.VarCoef.commOp_compOp_apply`, i.e. `[T, AB] = [T,A]B + A[T,B]`) give

  `[S, P] = [S, M_{c'} ∘ D^k] M_c + (M_{c'} ∘ D^k) [S, M_c]`,
  `[S, M_{c'} ∘ D^k] = [S, M_{c'}] D^k + M_{c'} [S, D^k]`,

and each of the five resulting summands has order `2k - 1`:

* `[S,M_{c'}] D^k M_c` : order `-1 + 2k + 0 = 2k - 1`,
* `M_{c'} [S,D^k] M_c` : order `0 + (2k-1) + 0 = 2k - 1`,
* `M_{c'} D^k [S,M_c]` : order `0 + 2k + (-1) = 2k - 1`,

so the sum is of order `2k - 1` as well.  No smoothness or ellipticity hypothesis is needed: the
statement is purely about the abstract `IsOrd` calculus of `Submission/Work/Diff/STE/B3/VarCoef/OpOrder.lean`.
-/

set_option linter.unusedVariables false

namespace Work.Diff.STE.B3.VarCoef

theorem commOp_POp_cut_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c c' : (ι → ℝ) → ℝ} {D S : Work.Diff.STE.B3.VarCoef.Op ι} {k : ℕ} (hk : 1 ≤ k)
    {Cc : ℤ → ℝ} (hc : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cc (Work.Diff.STE.B3.VarCoef.mulOp c))
    {Cc' : ℤ → ℝ} (hc' : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cc' (Work.Diff.STE.B3.VarCoef.mulOp c'))
    {CS : ℤ → ℝ} (hS : Work.Diff.STE.B3.VarCoef.IsOrd 0 (fun _ => 1) S)
    {CDk : ℤ → ℝ} (hDk : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ)) CDk (D^[k]))
    {CSDk : ℤ → ℝ} (hSDk : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) CSDk
        (Work.Diff.STE.B3.VarCoef.commOp S (D^[k])))
    {Csc : ℤ → ℝ} (hSc : Work.Diff.STE.B3.VarCoef.IsOrd (-1) Csc
        (Work.Diff.STE.B3.VarCoef.commOp S (Work.Diff.STE.B3.VarCoef.mulOp c)))
    {Csc' : ℤ → ℝ} (hSc' : Work.Diff.STE.B3.VarCoef.IsOrd (-1) Csc'
        (Work.Diff.STE.B3.VarCoef.commOp S (Work.Diff.STE.B3.VarCoef.mulOp c'))) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.commOp S (Work.Diff.STE.B3.VarCoef.POp c c' D k)) := by
  classical
  -- The operator `A := M_{c'} ∘ D^k` has order `2k`.
  have hA : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ)) C (compOp (mulOp c') (D^[k])) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ))
      (IsOrd.comp (T := mulOp c') (U := (D^[k])) hc' hDk) (by omega)⟩
  obtain ⟨CA, hA⟩ := hA
  -- Leibniz: `[S, A] = [S, M_{c'}] ∘ D^k + M_{c'} ∘ [S, D^k]` has order `2k - 1`.
  have hSA : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp S (compOp (mulOp c') (D^[k]))) := by
    have h1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (compOp (commOp S (mulOp c')) (D^[k])) :=
      ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
        (IsOrd.comp (T := commOp S (mulOp c')) (U := (D^[k])) hSc' hDk) (by omega)⟩
    have h2 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (compOp (mulOp c') (commOp S (D^[k]))) :=
      ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
        (IsOrd.comp (T := mulOp c') (U := commOp S (D^[k])) hc' hSDk) (by omega)⟩
    obtain ⟨C1, hC1⟩ := h1
    obtain ⟨C2, hC2⟩ := h2
    exact ⟨_, IsOrd.congr (IsOrd.add hC1 hC2)
      (fun f hf => (commOp_compOp_apply hc'.lin hS.pres hDk.pres hf).symm)⟩
  obtain ⟨CSA, hSA⟩ := hSA
  -- Leibniz again: `[S, POp] = [S, A] ∘ M_c + A ∘ [S, M_c]`; each summand has order `2k - 1`.
  have hT1 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp S (compOp (mulOp c') (D^[k]))) (mulOp c)) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp S (compOp (mulOp c') (D^[k]))) (U := mulOp c) hSA hc)
      (by omega)⟩
  have hT2 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp c') (D^[k])) (commOp S (mulOp c))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := compOp (mulOp c') (D^[k])) (U := commOp S (mulOp c)) hA hSc)
      (by omega)⟩
  obtain ⟨C1, hT1⟩ := hT1
  obtain ⟨C2, hT2⟩ := hT2
  exact ⟨_, IsOrd.congr (IsOrd.add hT1 hT2)
    (fun f hf => (commOp_compOp_apply hA.lin hS.pres hc.pres hf).symm)⟩

end Work.Diff.STE.B3.VarCoef
