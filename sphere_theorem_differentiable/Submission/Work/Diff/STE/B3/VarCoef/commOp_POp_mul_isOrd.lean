import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `[M_ψ, M_{c'} ∘ D^k ∘ M_c]` is of order `2k - 1`

This is the `M_ψ`-commutator entry of the order calculus of
`Submission/Work/Diff/STE/B3/VarCoef/OpOrder.lean`, companion of
`Work.Diff.STE.B3.VarCoef.commOp_POp_cut_isOrd` (which does the same for the Friedrichs cutoff
`S_ε`).  Both feed `Work.Diff.STE.B3.VarCoef.commOp_XOp_POp_isOrd`, hence the flat commutation
estimate `varLapPow_cut_comm_pairing` for the operator `X = M_ψ S_ε M_ψ` against
`P = M_{c'} D^k M_c`.

The gain of two orders in `[M_ψ, P]` is *entirely* due to the two `-1`-order commutators
`[M_ψ, M_m]` with the multipliers; the power `D^k` contributes its full `2k`:

* `[M_ψ, M_{c'} D^k] = [M_ψ, M_{c'}] D^k + M_{c'} [M_ψ, D^k]`, of order
  `(-1) + 2k = 2k - 1` (first summand, after the `D^k` is moved inside) resp. `0 + (2k-1) = 2k-1`
  (second summand, the hypothesis on `[M_ψ, D^k]`);
* `[M_ψ, P] = [M_ψ, M_{c'} D^k] M_c + M_{c'} D^k [M_ψ, M_c]`, of order `(2k-1) + 0 = 2k-1`
  resp. `2k + (-1) = 2k-1`.

Everything is a direct combination of `IsOrd.comp`, `IsOrd.add`, `IsOrd.mono_d` and
`IsOrd.congr` with the Leibniz identity `commOp_compOp_apply` for commutators of compositions.
No smoothness, positivity or symmetry hypothesis is used: the statement only consumes the `IsOrd`
certificates.
-/

namespace Work.Diff.STE.B3.VarCoef

theorem commOp_POp_mul_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c c' ψ : (ι → ℝ) → ℝ} {D : Work.Diff.STE.B3.VarCoef.Op ι} {k : ℕ} (hk : 1 ≤ k)
    {Cc : ℤ → ℝ} (hc : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cc (Work.Diff.STE.B3.VarCoef.mulOp c))
    {Cc' : ℤ → ℝ} (hc' : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cc' (Work.Diff.STE.B3.VarCoef.mulOp c'))
    {Cψ : ℤ → ℝ} (hψ : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cψ (Work.Diff.STE.B3.VarCoef.mulOp ψ))
    {CDk : ℤ → ℝ} (hDk : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ)) CDk (D^[k]))
    {CMDk : ℤ → ℝ} (hMDk : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) CMDk
        (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp ψ) (D^[k])))
    {Cψc : ℤ → ℝ} (hψc : Work.Diff.STE.B3.VarCoef.IsOrd (-1) Cψc
        (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp ψ) (Work.Diff.STE.B3.VarCoef.mulOp c)))
    {Cψc' : ℤ → ℝ} (hψc' : Work.Diff.STE.B3.VarCoef.IsOrd (-1) Cψc'
        (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp ψ) (Work.Diff.STE.B3.VarCoef.mulOp c'))) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp ψ)
        (Work.Diff.STE.B3.VarCoef.POp c c' D k)) := by
  classical
  -- Abbreviations: `L = M_ψ`, `Mc = M_c`, `Mc' = M_{c'}` and `A = M_{c'} ∘ D^k`, so that the
  -- operator under consideration is `[L, compOp A Mc]`.
  let L : Op ι := mulOp ψ
  let Mc : Op ι := mulOp c
  let Mc' : Op ι := mulOp c'
  let A : Op ι := compOp Mc' (D^[k])
  have hLpres : Preserves L := hψ.pres
  -- `A` is an operator of order `2k`, so it is `ℂ`-linear on smooth periodic functions.
  have hAcert : ∃ CA : ℤ → ℝ, IsOrd (2 * (k : ℤ)) CA A :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := Mc') (U := D^[k]) hc' hDk) (by omega)⟩
  have hAlin : LinSP A := hAcert.choose_spec.lin
  -- Leibniz: `[L, A Mc] = [L,A] Mc + A [L,Mc]`
  have hLeib1 : ∀ f : (ι → ℝ) → ℂ, SmoothPer f →
      commOp L (compOp A Mc) f
        = compOp (commOp L A) Mc f + compOp A (commOp L Mc) f :=
    fun f hf => commOp_compOp_apply hAlin hLpres hc.pres hf
  -- Leibniz: `[L, Mc' D^k] = [L,Mc'] D^k + Mc' [L,D^k]`
  have hLeib2 : ∀ f : (ι → ℝ) → ℂ, SmoothPer f →
      commOp L A f
        = compOp (commOp L Mc') (D^[k]) f + compOp Mc' (commOp L (D^[k])) f :=
    fun f hf => commOp_compOp_apply hc'.lin hLpres hDk.pres hf
  -- ### Step 1: `[L, A]` has order `2k - 1`
  have hcommA : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C (commOp L A) := by
    obtain ⟨C1, h1⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (compOp (commOp L Mc') (D^[k])) :=
      ⟨_, IsOrd.mono_d (IsOrd.comp (T := commOp L Mc') (U := D^[k]) hψc' hDk) (by omega)⟩
    obtain ⟨C2, h2⟩ : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
        (compOp Mc' (commOp L (D^[k]))) :=
      ⟨_, IsOrd.mono_d (IsOrd.comp (T := Mc') (U := commOp L (D^[k])) hc' hMDk) (by omega)⟩
    exact ⟨fun t => 2 * (C1 t + C2 t),
      IsOrd.congr (IsOrd.add h1 h2) (fun f hf => (hLeib2 f hf).symm)⟩
  obtain ⟨CAcomm, hAcomm⟩ := hcommA
  -- ### Step 2: the two summands of `[L, A Mc]` have order `2k - 1`
  have hT3 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C (compOp (commOp L A) Mc) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := commOp L A) (U := Mc) hAcomm hc) (by omega)⟩
  have hT4 : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C (compOp A (commOp L Mc)) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := A) (U := commOp L Mc) hAcert.choose_spec hψc)
      (by omega)⟩
  obtain ⟨C3, h3⟩ := hT3
  obtain ⟨C4, h4⟩ := hT4
  -- ### Step 3: assemble
  exact ⟨fun t => 2 * (C3 t + C4 t),
    IsOrd.congr (IsOrd.add h3 h4) (fun f hf => (hLeib1 f hf).symm)⟩

end Work.Diff.STE.B3.VarCoef
