import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The commutator of `XOp ψ S = M_ψ ∘ S ∘ M_ψ` with a composite operator

`IsOrd d C T` (see `OpOrder.lean`) is the order calculus of the `VarCoef` layer: `T` preserves
smooth `1`-periodic functions, is `ℂ`-linear on them, and gains `d` derivatives on the weighted
integer Sobolev scale `CSqZ`.

This file proves the closure step needed for the "sandwich" operators: if `A` and `B` are of
**order `0`** (multiplications, cutoffs) and the commutators `[A,P]`, `[B,P]` are both of order
`q`, then the commutator of the sandwiched operator `A ∘ B ∘ A` with `P` is again of order `q`.

The mechanism is the Leibniz rule for commutators of compositions, `commOp_compOp_apply`
(`OpOrder.lean`):

  `[A ∘ B, P] = (A ∘ [B,P]) + ([A,P] ∘ B)`,
  `[(A∘B) ∘ A, P] = ((A∘B) ∘ [A,P]) + ([(A∘B),P] ∘ A)`.

Both expansions are identities of *operators applied to smooth periodic functions*; the resulting
three pieces

  `(A∘B) ∘ [A,P]`,  `A ∘ ([B,P] ∘ A)`,  `([A,P] ∘ B) ∘ A`

have order `0 + q`, `0 + q + 0` and `q + 0 + 0` respectively, all equal to `q`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Commutator of a sandwich with a composite operator.**  Let `A`, `B` be operators of order `0`
and let `P` preserve smooth periodic functions.  If `[B,P]` and `[A,P]` both have order `q`, then
`[A ∘ B ∘ A, P]` has order `q`. -/
theorem isOrd_commOp_compOp_compOp_self {A B P : Op ι} {q : ℤ} {CA CB : ℤ → ℝ}
    (hA : IsOrd 0 CA A) (hB : IsOrd 0 CB B) (hP : Preserves P)
    (hBP : ∃ C : ℤ → ℝ, IsOrd q C (commOp B P))
    (hAP : ∃ C : ℤ → ℝ, IsOrd q C (commOp A P)) :
    ∃ C : ℤ → ℝ, IsOrd q C (commOp (compOp (compOp A B) A) P) := by
  classical
  obtain ⟨CBP, hCBP⟩ := hBP
  obtain ⟨CAP, hCAP⟩ := hAP
  -- `A ∘ B` has order `0`.
  have hABlin : LinSP (compOp A B) := linSP_comp (T := A) (U := B) hA.lin hB.lin hB.pres
  have hAB : IsOrd 0 (fun t => CA (t - 0) * CB t) (compOp A B) :=
    IsOrd.mono_d (IsOrd.comp (T := A) (U := B) hA hB) (by omega)
  -- Leibniz: `[A ∘ B, P] = (A ∘ [B,P]) + ([A,P] ∘ B)`, both pieces of order `q`.
  have hW : IsOrd q (fun t => 2 * ((CA (t - q) * CBP t) + (CAP (t - 0) * CB t)))
      (compOp A (commOp B P) + compOp (commOp A P) B) :=
    IsOrd.add (IsOrd.mono_d (IsOrd.comp (T := A) (U := commOp B P) hA hCBP) (by omega))
      (IsOrd.mono_d (IsOrd.comp (T := commOp A P) (U := B) hCAP hB) (by omega))
  have hWP : ∃ C : ℤ → ℝ, IsOrd q C (commOp (compOp A B) P) :=
    ⟨_, IsOrd.congr hW (fun f hf => by
      have h := compOp_commOp_apply (T := P) (A := A) (B := B) hA.lin hP hB.pres hf
      simp only [Pi.add_apply]
      exact h.symm)⟩
  obtain ⟨CWP, hCWP⟩ := hWP
  -- Leibniz again: `[(A∘B) ∘ A, P] = ((A∘B) ∘ [A,P]) + ([(A∘B),P] ∘ A)`.
  have h1 : ∃ C : ℤ → ℝ, IsOrd q C (compOp (compOp A B) (commOp A P)) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := compOp A B) (U := commOp A P) hAB hCAP) (by omega)⟩
  have h2 : ∃ C : ℤ → ℝ, IsOrd q C (compOp (commOp (compOp A B) P) A) :=
    ⟨_, IsOrd.mono_d (IsOrd.comp (T := commOp (compOp A B) P) (U := A) hCWP hA) (by omega)⟩
  obtain ⟨C1, hC1⟩ := h1
  obtain ⟨C2, hC2⟩ := h2
  exact ⟨_, IsOrd.congr (IsOrd.add hC1 hC2) (fun f hf => by
    have h := compOp_commOp_apply (T := P) (A := compOp A B) (B := A) hABlin hP hA.pres hf
    simp only [Pi.add_apply]
    exact h.symm)⟩

theorem commOp_XOp_POp_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c c' ψ : (ι → ℝ) → ℝ} {D S : Work.Diff.STE.B3.VarCoef.Op ι} {k : ℕ} (hk : 1 ≤ k)
    {Cψ : ℤ → ℝ} (hψ : Work.Diff.STE.B3.VarCoef.IsOrd 0 Cψ (Work.Diff.STE.B3.VarCoef.mulOp ψ))
    {CS : ℤ → ℝ} (hS : Work.Diff.STE.B3.VarCoef.IsOrd 0 (fun _ => 1) S)
    {dP : ℤ} {CP : ℤ → ℝ} (hP : Work.Diff.STE.B3.VarCoef.IsOrd dP CP (Work.Diff.STE.B3.VarCoef.POp c c' D k))
    {CSP : ℤ → ℝ} (hSP : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) CSP
        (Work.Diff.STE.B3.VarCoef.commOp S (Work.Diff.STE.B3.VarCoef.POp c c' D k)))
    {CMP : ℤ → ℝ} (hMP : Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) CMP
        (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp ψ) (Work.Diff.STE.B3.VarCoef.POp c c' D k))) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd (2 * (k : ℤ) - 1) C
      (Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.XOp ψ S)
        (Work.Diff.STE.B3.VarCoef.POp c c' D k)) := by
  have h := isOrd_commOp_compOp_compOp_self (A := mulOp ψ) (B := S)
    (P := POp c c' D k) (q := 2 * (k : ℤ) - 1) hψ hS hP.pres ⟨CSP, hSP⟩ ⟨CMP, hMP⟩
  simpa only [XOp] using h

end Work.Diff.STE.B3.VarCoef
