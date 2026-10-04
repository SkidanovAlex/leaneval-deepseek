import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.rhoLipschitz
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.cutOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commCutMul_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.isOrd_commOp_iterate
import Submission.Work.Diff.STE.B3.VarCoef.commOp_POp_cut_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commOp_POp_mul_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commOp_XOp_POp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commMulPd
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat commutation estimate `varLapPow_cut_comm_pairing`

This file assembles the pieces:

* `iterConst` / `commPowConst` — the *explicit* constant functions of the powers `D^[j]` and of the
  iterated commutators `[L, D^[j]]` (orders `2j` and `2j - 1`), so that the estimates are manifestly
  uniform in the cutoff scale `ε`;
* `commPow_unif_fam` — the iterated-commutator estimate for a *family* `S : ℝ → Op ι` of cutoffs;
* `commOp_POp_cut_unif`, `commOp_POp_mul_unif`, `commOp_XOp_POp_unif` — the Leibniz expansions of
  `[S, M_{c'}D^kM_c]`, `[M_ψ, M_{c'}D^kM_c]` and `[X, M_{c'}D^kM_c]` (`X = M_ψ S M_ψ`), each of
  order `2k - 1`, uniformly in `ε`;
* the target `varLapPow_cut_comm_pairing`, obtained by the weighted Cauchy–Schwarz estimate
  `L2re_le_sqrt_CSqZ` applied to the commutator of order `2k - 1`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Explicit constants for the powers of `D` and of the iterated commutators -/

/-- The explicit constant function of `D^[j]` (order `2j`). -/
def iterConst (CD : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 1
  | (j + 1) => fun t => CD (t - 2 * (j : ℤ)) * iterConst CD j t

/-- The explicit constant function of `[L, D^[j]]` (order `2j - 1`). -/
def commPowConst (CSD CD : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 0
  | (j + 1) => fun t => 2 * (CSD (t - 2 * (j : ℤ)) * iterConst CD j t
      + CD (t - (2 * (j : ℤ) - 1)) * commPowConst CSD CD j t)

/-- Powers of an operator of order `2`. -/
theorem iterConst_isOrd {D : Op ι} {CD : ℤ → ℝ} (hD : IsOrd 2 CD D) :
    ∀ j : ℕ, IsOrd (2 * (j : ℤ)) (iterConst CD j) (D^[j]) := by
  intro j
  induction j with
  | zero =>
      have h0 : D^[0] = (id : Op ι) := by funext f; rfl
      rw [h0]
      have h2 : (2 : ℤ) * ((0 : ℕ) : ℤ) = 0 := by simp
      rw [h2]
      exact IsOrd.id
  | succ j ih =>
      have h := IsOrd.comp (T := D) (U := (D^[j])) hD ih
      have h1 : D^[j.succ] = (fun f => D (D^[j] f)) := by
        funext f
        exact Function.iterate_succ_apply' D j f
      rw [h1]
      refine IsOrd.mono_d (d := 2 * (((j : ℕ) + 1 : ℕ) : ℤ)) (d' := 2 + 2 * (j : ℤ)) h ?_
      push_cast
      ring_nf
      omega

/-- **The iterated commutator estimate, uniformly in the cutoff.** -/
theorem commPow_unif_fam {D : Op ι} {CD : ℤ → ℝ} (hD : IsOrd 2 CD D)
    {S : ℝ → Op ι} (hSl : ∀ ε : ℝ, LinSP (S ε)) (hSp : ∀ ε : ℝ, Preserves (S ε))
    {CSD : ℤ → ℝ} (hSD : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd 1 CSD (commOp (S ε) D)) :
    ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsOrd (2 * (j : ℤ) - 1) (commPowConst CSD CD j) (commOp (S ε) (D^[j])) := by
  intro j
  induction j with
  | zero =>
      intro ε hε hε1
      have h0 : D^[0] = (id : Op ι) := by funext f; rfl
      rw [h0]
      have h1 : commOp (S ε) (id : Op ι) = (0 : Op ι) := by
        funext f
        simp only [commOp_apply, id_eq, sub_self]
        rfl
      rw [h1]
      have h2 : (2 : ℤ) * ((0 : ℕ) : ℤ) - 1 = -1 := by simp
      rw [h2]
      exact IsOrd.zero' (-1)
  | succ j ih =>
      intro ε hε hε1
      have hd : IsOrd (2 * (j : ℤ)) (iterConst CD j) (D^[j]) := iterConst_isOrd hD j
      have h1 : IsOrd (1 + 2 * (j : ℤ)) (fun t => CSD (t - 2 * (j : ℤ)) * iterConst CD j t)
          (compOp (commOp (S ε) D) (D^[j])) :=
        IsOrd.comp (T := commOp (S ε) D) (U := (D^[j])) (hSD ε hε hε1) hd
      have h2 : IsOrd (1 + 2 * (j : ℤ)) (fun t => CD (t - (2 * (j : ℤ) - 1)) * commPowConst CSD CD j t)
          (compOp D (commOp (S ε) (D^[j]))) := by
        have hc := IsOrd.comp (T := D) (U := commOp (S ε) (D^[j])) hD (ih ε hε hε1)
        refine IsOrd.mono_d (d := 1 + 2 * (j : ℤ)) (d' := 2 + (2 * (j : ℤ) - 1)) hc ?_
        omega
      have hsum := IsOrd.add h1 h2
      refine IsOrd.congr (IsOrd.mono_d (d := 2 * (((j : ℕ) + 1 : ℕ) : ℤ) - 1) (d' := 1 + 2 * (j : ℤ)) hsum ?_) ?_
      · have : (2 : ℤ) * ((j : ℕ) : ℤ) = 2 * (j : ℤ) := rfl
        push_cast
        ring_nf
        omega
      · -- the Leibniz identity `[S, D^{j+1}] = [S,D] D^j + D [S, D^j]`
        intro f hf
        have hDfj : SmoothPer ((D^[j]) f) := hd.pres f hf
        have hSf : SmoothPer (S ε f) := hSp ε f hf
        have hSDfj : SmoothPer (S ε ((D^[j]) f)) := hSp ε _ hDfj
        have hDfjS : SmoothPer ((D^[j]) (S ε f)) := hd.pres (S ε f) hSf
        have hT2f : D (commOp (S ε) (D^[j]) f)
            = D (S ε ((D^[j]) f)) - D ((D^[j]) (S ε f)) := by
          rw [commOp_apply, linSP_map_sub hD.lin hSDfj hDfjS]
        simp only [compOp_apply, Pi.add_apply]
        rw [hT2f]
        simp only [commOp_apply]
        simp only [Function.iterate_succ_apply']
        ring

/-! ## 2. The Leibniz expansions, uniformly in the cutoff scale -/

/-- `[S, M_{c'} D^k M_c]` has order `2k - 1`, uniformly in the cutoff family `S`. -/
theorem commOp_POp_cut_unif {c c' : (ι → ℝ) → ℝ} {D : Op ι} {k : ℕ} (hk : 1 ≤ k)
    {S : ℝ → Op ι} {Cc Cc' : ℤ → ℝ}
    (hc : IsOrd 0 Cc (mulOp c)) (hc' : IsOrd 0 Cc' (mulOp c'))
    (hS : ∀ ε : ℝ, IsOrd 0 (fun _ => 1) (S ε))
    {CDk : ℤ → ℝ} (hDk : IsOrd (2 * (k : ℤ)) CDk (D^[k]))
    {CSDk : ℤ → ℝ} (hSDk : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsOrd (2 * (k : ℤ) - 1) CSDk (commOp (S ε) (D^[k])))
    {Csc Csc' : ℤ → ℝ}
    (hSc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (-1) Csc (commOp (S ε) (mulOp c)))
    (hSc' : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (-1) Csc' (commOp (S ε) (mulOp c'))) :
    ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (commOp (S ε) (POp c c' D k)) := by
  classical
  have hAex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ)) C (compOp (mulOp c') (D^[k])) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ)) (IsOrd.comp (T := mulOp c') (U := (D^[k])) hc' hDk)
      (by omega)⟩
  obtain ⟨CA, hA⟩ := hAex
  have h1ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp (S ε) (mulOp c')) (D^[k])) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp (S ε) (mulOp c')) (U := (D^[k])) (hSc' ε hε hε1) hDk) (by omega)⟩
  obtain ⟨C1, h1⟩ := h1ex
  have h2ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c') (commOp (S ε) (D^[k]))) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := mulOp c') (U := commOp (S ε) (D^[k])) hc' (hSDk ε hε hε1)) (by omega)⟩
  obtain ⟨C2, h2⟩ := h2ex
  have hSAex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (commOp (S ε) (compOp (mulOp c') (D^[k]))) :=
    ⟨_, fun ε hε hε1 => IsOrd.congr
      (T := compOp (commOp (S ε) (mulOp c')) (D^[k])
        + compOp (mulOp c') (commOp (S ε) (D^[k])))
      (IsOrd.add (h1 ε hε hε1) (h2 ε hε hε1))
      (fun f hf => (commOp_compOp_apply hc'.lin (hS ε).pres hDk.pres hf).symm)⟩
  obtain ⟨CSA, hSA⟩ := hSAex
  have hT1ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp (S ε) (compOp (mulOp c') (D^[k]))) (mulOp c)) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp (S ε) (compOp (mulOp c') (D^[k]))) (U := mulOp c)
        (hSA ε hε hε1) hc) (by omega)⟩
  obtain ⟨CT1, hT1⟩ := hT1ex
  have hT2ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp c') (D^[k])) (commOp (S ε) (mulOp c))) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := compOp (mulOp c') (D^[k])) (U := commOp (S ε) (mulOp c))
        hA (hSc ε hε hε1)) (by omega)⟩
  obtain ⟨CT2, hT2⟩ := hT2ex
  exact ⟨_, fun ε hε hε1 => IsOrd.congr
    (T := compOp (commOp (S ε) (compOp (mulOp c') (D^[k]))) (mulOp c)
      + compOp (compOp (mulOp c') (D^[k])) (commOp (S ε) (mulOp c)))
    (IsOrd.add (hT1 ε hε hε1) (hT2 ε hε hε1))
    (fun f hf => (commOp_compOp_apply hA.lin (hS ε).pres hc.pres hf).symm)⟩

/-- `[M_ψ, M_{c'} D^k M_c]` has order `2k - 1` (no cutoff involved). -/
theorem commOp_POp_mul_const {c c' ψ : (ι → ℝ) → ℝ} {D : Op ι} {k : ℕ} (hk : 1 ≤ k)
    {Cc Cc' Cψ : ℤ → ℝ}
    (hc : IsOrd 0 Cc (mulOp c)) (hc' : IsOrd 0 Cc' (mulOp c'))
    (hψ : IsOrd 0 Cψ (mulOp ψ))
    {CDk : ℤ → ℝ} (hDk : IsOrd (2 * (k : ℤ)) CDk (D^[k]))
    {CMDk : ℤ → ℝ} (hMDk : IsOrd (2 * (k : ℤ) - 1) CMDk
      (commOp (mulOp ψ) (D^[k])))
    {Cψc Cψc' : ℤ → ℝ}
    (hψc : IsOrd (-1) Cψc (commOp (mulOp ψ) (mulOp c)))
    (hψc' : IsOrd (-1) Cψc' (commOp (mulOp ψ) (mulOp c'))) :
    ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp (mulOp ψ) (POp c c' D k)) := by
  classical
  have hAex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ)) C (compOp (mulOp c') (D^[k])) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ)) (IsOrd.comp (T := mulOp c') (U := (D^[k])) hc' hDk)
      (by omega)⟩
  obtain ⟨CA, hA⟩ := hAex
  have h1ex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp (mulOp ψ) (mulOp c')) (D^[k])) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp (mulOp ψ) (mulOp c')) (U := (D^[k])) hψc' hDk) (by omega)⟩
  obtain ⟨C1, h1⟩ := h1ex
  have h2ex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (mulOp c') (commOp (mulOp ψ) (D^[k]))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := mulOp c') (U := commOp (mulOp ψ) (D^[k])) hc' hMDk) (by omega)⟩
  obtain ⟨C2, h2⟩ := h2ex
  have hcommAex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (commOp (mulOp ψ) (compOp (mulOp c') (D^[k]))) :=
    ⟨_, IsOrd.congr
      (T := compOp (commOp (mulOp ψ) (mulOp c')) (D^[k])
        + compOp (mulOp c') (commOp (mulOp ψ) (D^[k])))
      (IsOrd.add h1 h2)
      (fun f hf => (commOp_compOp_apply hc'.lin hψ.pres hDk.pres hf).symm)⟩
  obtain ⟨CSA, hSA⟩ := hcommAex
  have hT1ex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp (mulOp ψ) (compOp (mulOp c') (D^[k]))) (mulOp c)) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp (mulOp ψ) (compOp (mulOp c') (D^[k]))) (U := mulOp c)
        hSA hc) (by omega)⟩
  obtain ⟨CT1, hT1⟩ := hT1ex
  have hT2ex : ∃ C : ℤ → ℝ, IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp c') (D^[k])) (commOp (mulOp ψ) (mulOp c))) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := compOp (mulOp c') (D^[k])) (U := commOp (mulOp ψ) (mulOp c))
        hA hψc) (by omega)⟩
  obtain ⟨CT2, hT2⟩ := hT2ex
  exact ⟨_, IsOrd.congr
    (T := compOp (commOp (mulOp ψ) (compOp (mulOp c') (D^[k]))) (mulOp c)
      + compOp (compOp (mulOp c') (D^[k])) (commOp (mulOp ψ) (mulOp c)))
    (IsOrd.add hT1 hT2)
    (fun f hf => (commOp_compOp_apply hA.lin hψ.pres hc.pres hf).symm)⟩

/-- `[X, M_{c'} D^k M_c]` with `X = M_ψ S M_ψ` has order `2k - 1`, uniformly in `S`. -/
theorem commOp_XOp_POp_unif {c c' ψ : (ι → ℝ) → ℝ} {D : Op ι} {k : ℕ} (hk : 1 ≤ k)
    {S : ℝ → Op ι} {Cψ : ℤ → ℝ} (hψ : IsOrd 0 Cψ (mulOp ψ))
    (hS : ∀ ε : ℝ, IsOrd 0 (fun _ => 1) (S ε))
    (dP : ℤ) {CP : ℤ → ℝ} (hP : IsOrd dP CP (POp c c' D k))
    {CSP : ℤ → ℝ} (hSP : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) CSP
      (commOp (S ε) (POp c c' D k)))
    {CMP : ℤ → ℝ} (hMP : IsOrd (2 * (k : ℤ) - 1) CMP
      (commOp (mulOp ψ) (POp c c' D k))) :
    ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (commOp (XOp ψ (S ε)) (POp c c' D k)) := by
  classical
  have hT1ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp ψ) (S ε)) (commOp (mulOp ψ) (POp c c' D k))) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := compOp (mulOp ψ) (S ε)) (U := commOp (mulOp ψ) (POp c c' D k))
        (IsOrd.comp (T := mulOp ψ) (U := S ε) hψ (hS ε)) hMP) (by omega)⟩
  obtain ⟨CT1, hT1⟩ := hT1ex
  have hT2ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (compOp (mulOp ψ) (commOp (S ε) (POp c c' D k))) (mulOp ψ)) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := compOp (mulOp ψ) (commOp (S ε) (POp c c' D k))) (U := mulOp ψ)
        (IsOrd.comp (T := mulOp ψ) (U := commOp (S ε) (POp c c' D k)) hψ (hSP ε hε hε1)) hψ)
      (by omega)⟩
  obtain ⟨CT2, hT2⟩ := hT2ex
  have hT3ex : ∃ C : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) C
      (compOp (commOp (mulOp ψ) (POp c c' D k)) (compOp (S ε) (mulOp ψ))) :=
    ⟨_, fun ε hε hε1 => IsOrd.mono_d (d := 2 * (k : ℤ) - 1)
      (IsOrd.comp (T := commOp (mulOp ψ) (POp c c' D k)) (U := compOp (S ε) (mulOp ψ))
        hMP (IsOrd.comp (T := S ε) (U := mulOp ψ) (hS ε) hψ)) (by omega)⟩
  obtain ⟨CT3, hT3⟩ := hT3ex
  have hid : ∀ (ε : ℝ) (f : (ι → ℝ) → ℂ), SmoothPer f →
      ((compOp (compOp (mulOp ψ) (S ε)) (commOp (mulOp ψ) (POp c c' D k))
          + compOp (compOp (mulOp ψ) (commOp (S ε) (POp c c' D k))) (mulOp ψ))
          + compOp (commOp (mulOp ψ) (POp c c' D k)) (compOp (S ε) (mulOp ψ))) f
        = commOp (XOp ψ (S ε)) (POp c c' D k) f := by
    intro ε f hf
    have hPf : SmoothPer ((POp c c' D k) f) := hP.pres f hf
    have hmyf : SmoothPer ((mulOp ψ) f) := hψ.pres f hf
    have hA : SmoothPer ((S ε) ((mulOp ψ) f)) := (hS ε).pres _ hmyf
    have hB : SmoothPer ((POp c c' D k) ((mulOp ψ) f)) := hP.pres _ hmyf
    have hC : SmoothPer ((S ε) ((POp c c' D k) f)) := (hS ε).pres _ hPf
    have hD : SmoothPer ((POp c c' D k) ((S ε) ((mulOp ψ) f))) := hP.pres _ hA
    have hE : SmoothPer ((mulOp ψ) ((POp c c' D k) f)) := hψ.pres _ hPf
    have hu1 : SmoothPer ((S ε) ((mulOp ψ) ((POp c c' D k) f))) := (hS ε).pres _ hE
    have hv1 : SmoothPer ((S ε) ((POp c c' D k) ((mulOp ψ) f))) := (hS ε).pres _ hB
    simp only [Pi.add_apply, XOp, compOp_apply, commOp_apply]
    rw [linSP_map_sub (hS ε).lin hE hB, linSP_map_sub hψ.lin hu1 hv1, linSP_map_sub hψ.lin hv1 hD]
    ring
  exact ⟨_, fun ε hε hε1 => IsOrd.congr
    (T := (compOp (compOp (mulOp ψ) (S ε)) (commOp (mulOp ψ) (POp c c' D k))
        + compOp (compOp (mulOp ψ) (commOp (S ε) (POp c c' D k))) (mulOp ψ))
        + compOp (commOp (mulOp ψ) (POp c c' D k)) (compOp (S ε) (mulOp ψ)))
    (IsOrd.add (IsOrd.add (hT1 ε hε hε1) (hT2 ε hε hε1)) (hT3 ε hε hε1))
    (fun f hf => hid ε f hf)⟩

end Work.Diff.STE.B3.VarCoef
