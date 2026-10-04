import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.flatCut_CSqZ_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.pdTransferKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly layer for `Work.Diff.STE.B3.VarCoef.varLapPow_cut_comm_pairing`

This file contains the generic pieces of the "order calculus" assembly:

* `linSP_map_finset_sum` — linearity of an operator on finite sums;
* `IsOrd.zero'` and `isOrd_iterate` — the zero operator has *every* order, and a power `D^[j]` of
  an operator of order `d` has order `d * j`;
* `IsCommOrd L d C Cl T` — a bundled certificate: `T` has order `d` **and** its commutator `[L,T]`
  with a fixed `L` gains one order (`d - 1`).  This is the invariant that makes the commutator
  calculus with the cutoff `S_ε` and with `M_ψ` automatic: it is stable under composition, finite
  sums and negation;
* the variable-coefficient Laplacian `varLap A B` is built from `mulOp` and `pdOp`, so it inherits
  an `IsCommOrd` certificate for *every* `L` that commutes with multiplication (`[L,M_m]` of order
  `-1` at worst) and with the partial derivatives (`[L,∂_a]` of order `0`).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Finite sums -/

theorem SmoothPer.finset_sum' {κ : Type*} (s : Finset κ) (F : κ → (ι → ℝ) → ℂ)
    (h : ∀ i ∈ s, SmoothPer (F i)) : SmoothPer (∑ i ∈ s, F i) := by
  rw [finset_sum_apply_eq]
  exact SmoothPer.finset_sum s F h

/-- An operator that is additive on smooth periodic functions is additive on finite sums. -/
theorem linSP_map_finset_sum {κ : Type*} {T : Op ι} (h : LinSP T) (s : Finset κ)
    (F : κ → (ι → ℝ) → ℂ) (hF : ∀ i ∈ s, SmoothPer (F i)) :
    T (∑ i ∈ s, F i) = ∑ i ∈ s, T (F i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, linSP_map_zero h]
  | insert a s ha ih =>
      have hsum : SmoothPer (∑ i ∈ s, F i) :=
        SmoothPer.finset_sum' s F fun i hi => hF i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        h.add (F a) (∑ i ∈ s, F i) (hF a (Finset.mem_insert_self a s)) hsum,
        ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-! ## 2. The zero operator and powers -/

/-- The zero operator has **every** order. -/
theorem IsOrd.zero' (d : ℤ) : IsOrd d (fun _ => 0) (0 : Op ι) where
  pres := fun f hf => by
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

/-- Powers of an operator of order `d` (the order of `D^[j]` is `d * j`). -/
theorem isOrd_iterate {d : ℤ} {C : ℤ → ℝ} {D : Op ι} (hD : IsOrd d C D) :
    ∀ j : ℕ, ∃ Cj : ℤ → ℝ, IsOrd (d * (j : ℤ)) Cj (D^[j]) := by
  intro j
  induction j with
  | zero =>
      refine ⟨fun _ => 1, ?_⟩
      have h0 : D^[0] = (id : Op ι) := by
        funext f
        rfl
      rw [h0]
      have hd0 : d * ((0 : ℕ) : ℤ) = 0 := by simp
      rw [hd0]
      exact IsOrd.id
  | succ j ih =>
      obtain ⟨Cj, hCj⟩ := ih
      have hcomp : IsOrd (d * ↑j + d) (fun t => C (t - d * ↑j) * Cj t)
          (fun f => D (D^[j] f)) := by
        have := IsOrd.comp hD hCj
        rwa [show d + d * (j : ℤ) = d * (j : ℤ) + d from by ring] at this
      have h1 : D^[j.succ] = (fun f => D (D^[j] f)) := by
        funext f
        exact Function.iterate_succ_apply' D j f
      rw [h1]
      refine ⟨fun t => C (t - d * ↑j) * Cj t, IsOrd.mono_d hcomp ?_⟩
      push_cast
      ring_nf
      omega

/-! ## 3. The bundled "commutator gains one order" certificate -/

/-- `IsCommOrd L d C Cl T`: the operator `T` has order `d`, and its commutator with `L` has order
`d - 1` (one order better), with constant functions `C` and `Cl` respectively. -/
structure IsCommOrd (L : Op ι) (d : ℤ) (C Cl : ℤ → ℝ) (T : Op ι) : Prop where
  ord : IsOrd d C T
  comm : IsOrd (d - 1) Cl (commOp L T)

theorem IsCommOrd.mono_d {L : Op ι} {d d' : ℤ} {C Cl : ℤ → ℝ} {T : Op ι}
    (h : IsCommOrd L d' C Cl T) (hd : d' ≤ d) : IsCommOrd L d C Cl T :=
  ⟨IsOrd.mono_d h.ord hd, IsOrd.mono_d h.comm (by omega)⟩

theorem IsCommOrd.congr {L : Op ι} {d : ℤ} {C Cl : ℤ → ℝ} {T U : Op ι} (hLp : Preserves L)
    (h : IsCommOrd L d C Cl T) (hEq : ∀ f : (ι → ℝ) → ℂ, SmoothPer f → T f = U f) :
    IsCommOrd L d C Cl U :=
  ⟨IsOrd.congr h.ord hEq,
    IsOrd.congr h.comm (fun f hf => by
      simp only [commOp_apply]
      rw [hEq f hf, hEq (L f) (hLp f hf)])⟩

theorem IsCommOrd.compose {L : Op ι} {d₁ d₂ : ℤ} {C₁ Cl₁ C₂ Cl₂ : ℤ → ℝ} {T U : Op ι}
    (hLp : Preserves L) (hT : IsCommOrd L d₁ C₁ Cl₁ T) (hU : IsCommOrd L d₂ C₂ Cl₂ U) :
    IsCommOrd L (d₁ + d₂) (fun t => C₁ (t - d₂) * C₂ t)
      (fun t => 2 * (Cl₁ (t - d₂) * C₂ t + C₁ (t - (d₂ - 1)) * Cl₂ t)) (compOp T U) := by
  refine ⟨IsOrd.comp (T := T) (U := U) hT.ord hU.ord, ?_⟩
  have h1 : IsOrd (d₁ + d₂ - 1) (fun t => Cl₁ (t - d₂) * C₂ t) (compOp (commOp L T) U) :=
    IsOrd.mono_d (IsOrd.comp (T := commOp L T) (U := U) hT.comm hU.ord) (by omega)
  have h2 : IsOrd (d₁ + d₂ - 1) (fun t => C₁ (t - (d₂ - 1)) * Cl₂ t)
      (compOp T (commOp L U)) :=
    IsOrd.mono_d (IsOrd.comp (T := T) (U := commOp L U) hT.ord hU.comm) (by omega)
  refine IsOrd.congr (IsOrd.add h1 h2) ?_
  intro f hf
  rw [commOp_compOp_apply hT.ord.lin hLp hU.ord.pres hf]
  rfl

/-- The commutator with a finite sum of operators. -/
theorem commOp_finset_sum_apply {L : Op ι} {κ : Type*} (s : Finset κ) (T : κ → Op ι)
    (hL : LinSP L) (f : (ι → ℝ) → ℂ)
    (hsm : ∀ i ∈ s, SmoothPer (T i f)) (hsmL : ∀ i ∈ s, SmoothPer (T i (L f))) :
    commOp L (∑ i ∈ s, T i) f = ∑ i ∈ s, commOp L (T i) f := by
  rw [commOp_apply, finset_sumOp_apply, finset_sumOp_apply]
  rw [← finset_sum_apply_eq s (fun i => T i f),
    ← finset_sum_apply_eq s (fun i => T i (L f))]
  rw [linSP_map_finset_sum hL s (fun i => T i f) hsm]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [commOp_apply]

theorem IsCommOrd.sum {L : Op ι} {κ : Type*} {d : ℤ} (s : Finset κ) (T : κ → Op ι)
    (C Cl : κ → ℤ → ℝ) (hL : LinSP L) (hLp : Preserves L)
    (h : ∀ i ∈ s, IsCommOrd L d (C i) (Cl i) (T i)) :
    IsCommOrd L d (fun t => (s.card : ℝ) * ∑ i ∈ s, C i t)
      (fun t => (s.card : ℝ) * ∑ i ∈ s, Cl i t) (∑ i ∈ s, T i) := by
  refine ⟨IsOrd.sum s T C fun i hi => (h i hi).ord, ?_⟩
  refine IsOrd.congr (IsOrd.sum s (fun i => commOp L (T i)) Cl fun i hi => (h i hi).comm) ?_
  intro f hf
  have hsm : ∀ i ∈ s, SmoothPer (T i f) := fun i hi => (h i hi).ord.pres f hf
  have hsmL : ∀ i ∈ s, SmoothPer (T i (L f)) := fun i hi => (h i hi).ord.pres (L f) (hLp f hf)
  rw [finset_sumOp_apply, ← finset_sum_apply_eq s (fun i => commOp L (T i) f)]
  exact (commOp_finset_sum_apply s T hL f hsm hsmL).symm

theorem IsCommOrd.neg {L : Op ι} {d : ℤ} {C Cl : ℤ → ℝ} {T : Op ι} (hL : LinSP L)
    (h : IsCommOrd L d C Cl T) : IsCommOrd L d C Cl (-T) :=
  ⟨h.ord.neg, IsOrd.congr h.comm.neg (fun f hf => by
    simp only [commOp_apply, Pi.neg_apply]
    rw [linSP_map_neg hL (h.ord.pres f hf)]
    ring)⟩

theorem IsCommOrd.add {L : Op ι} {d : ℤ} {C₁ Cl₁ C₂ Cl₂ : ℤ → ℝ} {T U : Op ι} (hL : LinSP L)
    (hT : IsCommOrd L d C₁ Cl₁ T) (hU : IsCommOrd L d C₂ Cl₂ U) :
    IsCommOrd L d (fun t => 2 * (C₁ t + C₂ t)) (fun t => 2 * (Cl₁ t + Cl₂ t)) (T + U) := by
  refine ⟨IsOrd.add hT.ord hU.ord, ?_⟩
  have h1 : IsOrd (d - 1) Cl₁ (commOp L T) := hT.comm
  have h2 : IsOrd (d - 1) Cl₂ (commOp L U) := hU.comm
  refine IsOrd.congr (IsOrd.add h1 h2) ?_
  intro f hf
  rw [commOp_add_right_apply hL hT.ord.pres hU.ord.pres hf]
  rfl

/-! ## 4. The variable-coefficient Laplacian -/

/-- The pointwise identity expressing `varLap A B` as a sum of compositions of multipliers and
partial derivatives. -/
theorem varLap_eq_ops (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) :
    varLap A B f = -(((∑ a, ∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) f)
      + ((∑ a, compOp (mulOp (B a)) (pdOp a)) f)) := by
  funext x
  have h1 : ((∑ a, ∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) f) x
      = ∑ a, ∑ b, ((A a b x : ℝ) : ℂ) * Work.Diff.STE.pd a (Work.Diff.STE.pd b f) x := by
    simp only [finset_sumOp_apply, Finset.sum_apply, compOp_apply, mulOp, pdOp]
  have h2 : ((∑ a, compOp (mulOp (B a)) (pdOp a)) f) x
      = ∑ a, ((B a x : ℝ) : ℂ) * Work.Diff.STE.pd a f x := by
    simp only [finset_sumOp_apply, Finset.sum_apply, compOp_apply, mulOp, pdOp]
  simp only [Pi.neg_apply, Pi.add_apply]
  rw [h1, h2]
  simp only [varLap]

/-- `mulOp` as an `IsCommOrd` certificate, from an order bound and a commutator gain. -/
theorem isCommOrd_mulOp {L : Op ι} {m : (ι → ℝ) → ℝ}
    (hmul : ∃ C : ℤ → ℝ, IsOrd 0 C (mulOp m))
    (hLmul : ∃ C : ℤ → ℝ, IsOrd (-1) C (commOp L (mulOp m))) :
    ∃ C Cl : ℤ → ℝ, IsCommOrd L 0 C Cl (mulOp m) := by
  obtain ⟨C, hC⟩ := hmul
  obtain ⟨Cl, hCl⟩ := hLmul
  exact ⟨C, Cl, hC, by simpa using hCl⟩

/-- `pdOp` as an `IsCommOrd` certificate, from an order bound and a commutator bound. -/
theorem isCommOrd_pdOp {L : Op ι} {i : ι}
    (hpd : ∃ C : ℤ → ℝ, IsOrd 1 C (pdOp i))
    (hLpd : ∃ C : ℤ → ℝ, IsOrd 0 C (commOp L (pdOp i))) :
    ∃ C Cl : ℤ → ℝ, IsCommOrd L 1 C Cl (pdOp i) := by
  obtain ⟨C, hC⟩ := hpd
  obtain ⟨Cl, hCl⟩ := hLpd
  exact ⟨C, Cl, hC, by simpa using hCl⟩

/-- **`varLap A B` gains one order when commutated with any `L` that commutes with the
multiplications (up to order `-1`) and with the partial derivatives (up to order `0`).** -/
theorem varLap_isCommOrd (L : Op ι) (hL : LinSP L) (hLp : Preserves L)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b))
    (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a))
    (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hmul : ∀ m : (ι → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd 0 C (mulOp m))
    (hpd : ∀ i : ι, ∃ C : ℤ → ℝ, IsOrd 1 C (pdOp i))
    (hLmul : ∀ m : (ι → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd (-1) C (commOp L (mulOp m)))
    (hLpd : ∀ i : ι, ∃ C : ℤ → ℝ, IsOrd 0 C (commOp L (pdOp i))) :
    ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl (varLapOp A B) := by
  classical
  have hmulC : ∀ (m : (ι → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C Cl : ℤ → ℝ, IsCommOrd L 0 C Cl (mulOp m) :=
    fun m hm hmp => isCommOrd_mulOp (hmul m hm hmp) (hLmul m hm hmp)
  have hpdC : ∀ i : ι, ∃ C Cl : ℤ → ℝ, IsCommOrd L 1 C Cl (pdOp i) :=
    fun i => isCommOrd_pdOp (hpd i) (hLpd i)
  have hterm : ∀ a b : ι, ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl
      (compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) := by
    intro a b
    obtain ⟨C₁, Cl₁, h₁⟩ := hmulC (A a b) (hA a b) (hAp a b)
    obtain ⟨C₂, Cl₂, h₂⟩ := hpdC a
    obtain ⟨C₃, Cl₃, h₃⟩ := hpdC b
    have h := IsCommOrd.compose hLp (IsCommOrd.compose hLp h₁ h₂) h₃
    exact ⟨_, _, IsCommOrd.mono_d h (by omega)⟩
  have hT1 : ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl
      (∑ a, ∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) := by
    have hinner : ∀ a : ι, ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl
        (∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) := by
      intro a
      choose C Cl hC using fun b : ι => hterm a b
      exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ b, C b t,
        fun t => (Fintype.card ι : ℝ) * ∑ b, Cl b t,
        IsCommOrd.sum Finset.univ
          (fun b => compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) C Cl hL hLp
          (fun b _ => hC b)⟩
    choose C Cl hC using hinner
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      fun t => (Fintype.card ι : ℝ) * ∑ a, Cl a t,
      IsCommOrd.sum Finset.univ
        (fun a => ∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) C Cl hL hLp
        (fun a _ => hC a)⟩
  have hT2 : ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl
      (∑ a, compOp (mulOp (B a)) (pdOp a)) := by
    have hone : ∀ a : ι, ∃ C Cl : ℤ → ℝ, IsCommOrd L 2 C Cl
        (compOp (mulOp (B a)) (pdOp a)) := by
      intro a
      obtain ⟨C₁, Cl₁, h₁⟩ := hmulC (B a) (hB a) (hBp a)
      obtain ⟨C₂, Cl₂, h₂⟩ := hpdC a
      have h := IsCommOrd.compose hLp h₁ h₂
      exact ⟨_, _, IsCommOrd.mono_d h (by omega)⟩
    choose C Cl hC using hone
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      fun t => (Fintype.card ι : ℝ) * ∑ a, Cl a t,
      IsCommOrd.sum Finset.univ (fun a => compOp (mulOp (B a)) (pdOp a)) C Cl hL hLp
        (fun a _ => hC a)⟩
  obtain ⟨C₁, Cl₁, h₁⟩ := hT1
  obtain ⟨C₂, Cl₂, h₂⟩ := hT2
  have hsum := IsCommOrd.add hL h₁ h₂
  have hneg := IsCommOrd.neg hL hsum
  refine ⟨fun t => 2 * (C₁ t + C₂ t), fun t => 2 * (Cl₁ t + Cl₂ t), ?_⟩
  refine IsCommOrd.congr hLp hneg ?_
  intro f _
  exact (varLap_eq_ops A B f).symm

/-! ## 5. The composite operators and the derivative of a real-valued multiplier -/

/-- The composite operator `M_{c'} ∘ D^k ∘ M_c`. -/
def POp (c c' : (ι → ℝ) → ℝ) (D : Op ι) (k : ℕ) : Op ι :=
  compOp (compOp (mulOp c') (D^[k])) (mulOp c)

/-- The composite operator `M_ψ ∘ S ∘ M_ψ`. -/
def XOp (ψ : (ι → ℝ) → ℝ) (S : Op ι) : Op ι :=
  compOp (compOp (mulOp ψ) S) (mulOp ψ)

/-- The partial derivative of a smooth real-valued multiplier is smooth. -/
theorem pdR_contDiff {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (a : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdR a m) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ m) := hm.fderiv_right (m := (⊤ : ℕ∞)) (by norm_num)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ι → ℝ => (fderiv ℝ m x) (Pi.single a 1)) :=
    h1.clm_apply contDiff_const
  rw [show Work.Diff.STE.pdR a m
      = (fun x : ι → ℝ => (fderiv ℝ m x) (Pi.single a 1)) from rfl]
  exact h2

/-- The partial derivative of a `1`-periodic real-valued multiplier is `1`-periodic. -/
theorem pdR_periodic {m : (ι → ℝ) → ℝ} (hmp : Work.Diff.STE.Periodic1 m) (a : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pdR a m) := by
  intro j x
  have h1 : (fun y : ι → ℝ => m (y + Pi.single j 1)) = m := by
    funext y
    exact hmp j y
  have h2 : fderiv ℝ m (x + Pi.single j 1) = fderiv ℝ m x := by
    rw [← fderiv_comp_add_right (f := m) (x := x) (Pi.single j 1), h1]
  simp only [Work.Diff.STE.pdR, h2]

/-! ## 8. Explicit (ε-uniform) constants for the `varLap` commutator certificate -/

/-- The `C` component of the certificate of a single `(a,b)` term of `varLap A B`. -/
def vTmC (CA : ι → ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) (a b : ι) : ℤ → ℝ :=
  fun t => (CA a b ((t - 1) - 1) * Cp a (t - 1)) * Cp b t

/-- The `Cl` component of the certificate of a single `(a,b)` term of `varLap A B`. -/
def vTmCl (CA : ι → ι → ℤ → ℝ) (CAg : ι → ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) (Cpg : ι → ℤ → ℝ)
    (a b : ι) : ℤ → ℝ :=
  fun t => 2 * ((2 * (CAg a b ((t - 1) - 1) * Cp a (t - 1)
      + CA a b ((t - 1) - (1 - 1)) * Cpg a (t - 1))) * Cp b t
    + (CA a b ((t - (1 - 1)) - 1) * Cp a (t - (1 - 1))) * Cpg b t)

/-- The `C` component of the certificate of the second-order part of `varLap A B`. -/
def vT1C (CA : ι → ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) : ℤ → ℝ :=
  fun t => (Fintype.card ι : ℝ) * ∑ a, (Fintype.card ι : ℝ) * ∑ b, vTmC CA Cp a b t

/-- The `Cl` component of the certificate of the second-order part of `varLap A B`. -/
def vT1Cl (CA : ι → ι → ℤ → ℝ) (CAg : ι → ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) (Cpg : ι → ℤ → ℝ) :
    ℤ → ℝ :=
  fun t => (Fintype.card ι : ℝ) * ∑ a, (Fintype.card ι : ℝ) * ∑ b, vTmCl CA CAg Cp Cpg a b t

/-- The `C` component of the certificate of the first-order part of `varLap A B`. -/
def vT2C (CB : ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) : ℤ → ℝ :=
  fun t => (Fintype.card ι : ℝ) * ∑ a, CB a (t - 1) * Cp a t

/-- The `Cl` component of the certificate of the first-order part of `varLap A B`. -/
def vT2Cl (CB : ι → ℤ → ℝ) (CBg : ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) (Cpg : ι → ℤ → ℝ) : ℤ → ℝ :=
  fun t => (Fintype.card ι : ℝ) * ∑ a, 2 * (CBg a (t - 1) * Cp a t
    + CB a (t - (1 - 1)) * Cpg a t)

/-- The `C` component of the `varLap` commutator certificate. -/
def vLapC (CA : ι → ι → ℤ → ℝ) (CB : ι → ℤ → ℝ) (Cp : ι → ℤ → ℝ) : ℤ → ℝ :=
  fun t => 2 * (vT1C CA Cp t + vT2C CB Cp t)

/-- The `Cl` component of the `varLap` commutator certificate. -/
def vLapCl (CA : ι → ι → ℤ → ℝ) (CAg : ι → ι → ℤ → ℝ) (CB : ι → ℤ → ℝ) (CBg : ι → ℤ → ℝ)
    (Cp : ι → ℤ → ℝ) (Cpg : ι → ℤ → ℝ) : ℤ → ℝ :=
  fun t => 2 * (vT1Cl CA CAg Cp Cpg t + vT2Cl CB CBg Cp Cpg t)

/-- **Explicit-constant form of the `varLap` commutator certificate.**  Unlike
`varLap_isCommOrd`, the constants are named, so the statement can be instantiated uniformly in any
parameter (in particular uniformly in the cutoff scale `ε`). -/
theorem varLap_isCommOrd_exp (L : Op ι) (hL : LinSP L) (hLp : Preserves L)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (CA : ι → ι → ℤ → ℝ) (CAg : ι → ι → ℤ → ℝ)
    (CB : ι → ℤ → ℝ) (CBg : ι → ℤ → ℝ)
    (Cp : ι → ℤ → ℝ) (Cpg : ι → ℤ → ℝ)
    (hCA : ∀ a b, IsOrd 0 (CA a b) (mulOp (A a b)))
    (hCAg : ∀ a b, IsOrd (-1) (CAg a b) (commOp L (mulOp (A a b))))
    (hCB : ∀ a, IsOrd 0 (CB a) (mulOp (B a)))
    (hCBg : ∀ a, IsOrd (-1) (CBg a) (commOp L (mulOp (B a))))
    (hCp : ∀ i, IsOrd 1 (Cp i) (pdOp i))
    (hCpg : ∀ i, IsOrd 0 (Cpg i) (commOp L (pdOp i))) :
    IsCommOrd L 2 (vLapC CA CB Cp) (vLapCl CA CAg CB CBg Cp Cpg) (varLapOp A B) := by
  classical
  have hbase : ∀ a b : ι, IsCommOrd L 0 (CA a b) (CAg a b) (mulOp (A a b)) :=
    fun a b => ⟨hCA a b, by simpa using hCAg a b⟩
  have hbasep : ∀ i : ι, IsCommOrd L 1 (Cp i) (Cpg i) (pdOp i) :=
    fun i => ⟨hCp i, by simpa using hCpg i⟩
  have hCBcomm : ∀ a : ι, IsCommOrd L 0 (CB a) (CBg a) (mulOp (B a)) :=
    fun a => ⟨hCB a, by simpa using hCBg a⟩
  have hterm : ∀ a b : ι, IsCommOrd L 2 (vTmC CA Cp a b) (vTmCl CA CAg Cp Cpg a b)
      (compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) := by
    intro a b
    have h12 : IsCommOrd L (0 + 1) (fun t => CA a b (t - 1) * Cp a t)
        (fun t => 2 * (CAg a b (t - 1) * Cp a t + CA a b (t - (1 - 1)) * Cpg a t))
        (compOp (mulOp (A a b)) (pdOp a)) :=
      IsCommOrd.compose hLp (hbase a b) (hbasep a)
    have h123 := IsCommOrd.compose hLp h12 (hbasep b)
    exact IsCommOrd.mono_d h123 (by omega)
  have hT1 : IsCommOrd L 2 (vT1C CA Cp) (vT1Cl CA CAg Cp Cpg)
      (∑ a, ∑ b, compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b)) := by
    refine IsCommOrd.sum Finset.univ _
      (fun a => fun t => (Fintype.card ι : ℝ) * ∑ b, vTmC CA Cp a b t)
      (fun a => fun t => (Fintype.card ι : ℝ) * ∑ b, vTmCl CA CAg Cp Cpg a b t) hL hLp ?_
    intro a _
    exact IsCommOrd.sum Finset.univ (fun b => compOp (compOp (mulOp (A a b)) (pdOp a)) (pdOp b))
      (fun b => vTmC CA Cp a b) (fun b => vTmCl CA CAg Cp Cpg a b) hL hLp
      (fun b _ => hterm a b)
  have hT2 : IsCommOrd L 2 (vT2C CB Cp) (vT2Cl CB CBg Cp Cpg)
      (∑ a, compOp (mulOp (B a)) (pdOp a)) := by
    refine IsCommOrd.sum Finset.univ (fun a => compOp (mulOp (B a)) (pdOp a))
      (fun a => fun t => CB a (t - 1) * Cp a t)
      (fun a => fun t => 2 * (CBg a (t - 1) * Cp a t + CB a (t - (1 - 1)) * Cpg a t))
      hL hLp ?_
    intro a _
    exact IsCommOrd.mono_d (IsCommOrd.compose hLp (hCBcomm a) (hbasep a)) (by omega)
  have hsum := IsCommOrd.add hL hT1 hT2
  have hneg := IsCommOrd.neg hL hsum
  refine IsCommOrd.congr hLp hneg ?_
  intro f _
  exact (varLap_eq_ops A B f).symm

end Work.Diff.STE.B3.VarCoef
