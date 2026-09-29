import Mathlib
import Submission.Work.Fx.FxExpCore
import Submission.Work.Fx.CisKit
import Submission.Work.Fx.CisRbound
import Submission.Work.Fx.CisPhase
import Submission.Work.Fx.CisExpBoundB
import Submission.Work.Fx.CisTrunc
import Submission.Work.Fx.CisStep1
import Submission.Work.Fx.CisStep4
import Submission.Work.Fx.CisStep6

/-!
# The `cis` word (paper Lemma 2.12)

Assembly of the `cis` word from the library words of `KernelLib`/`IntLib` and the two
existential words `pi` and `expc` of `Work.Fx.NumWords`, following the route of the
statement's docstring.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Fx

open HvdH

/-! ## Size helpers -/

/-- A fixed-point pair of modulus `≤ 2^(P+1)` has coordinates of bit-size `≤ P+4`. -/
theorem isz_of_norm_le {P : ℕ} {U V : ℤ} (h : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ 2 ^ (P + 1)) :
    isz U ≤ P + 4 ∧ isz V ≤ P + 4 := by
  have hre : |(U : ℝ)| ≤ 2 ^ (P + 1) := by
    have h2 := Complex.abs_re_le_norm ((U : ℂ) + (V : ℂ) * Complex.I)
    have h3 : (((U : ℂ) + (V : ℂ) * Complex.I).re) = (U : ℝ) := by simp
    rw [h3] at h2
    exact le_trans h2 h
  have him : |(V : ℝ)| ≤ 2 ^ (P + 1) := by
    have h2 := Complex.abs_im_le_norm ((U : ℂ) + (V : ℂ) * Complex.I)
    have h3 : (((U : ℂ) + (V : ℂ) * Complex.I).im) = (V : ℝ) := by simp
    rw [h3] at h2
    exact le_trans h2 h
  have key : ∀ (W : ℤ), |(W : ℝ)| ≤ 2 ^ (P + 1) → W.natAbs < 2 ^ (P + 2) := by
    intro W hW
    have h1 : W.natAbs ≤ 2 ^ (P + 1) := by
      have h2 : ((W.natAbs : ℕ) : ℝ) ≤ ((2 ^ (P + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        push_cast
        exact hW
      exact_mod_cast h2
    exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  constructor
  · have h3 := Nat.size_le.mpr (key U hre); simp only [isz]; omega
  · have h3 := Nat.size_le.mpr (key V him); simp only [isz]; omega

theorem isz_le_Xb_of_norm {p : ℕ} {j : ℤ} {k : ℕ} {U V : ℤ}
    (h : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ 2 ^ (p + 60 + 1)) :
    isz U ≤ Cis.Xb p j k ∧ isz V ≤ Cis.Xb p j k := by
  obtain ⟨hU, hV⟩ := isz_of_norm_le (P := p + 60) h
  have h1 := Cis.two_le_isz j
  have h3 := Cis.two_le_isz (k : ℤ)
  have hle : (p + 60 + 4) + 2 ≤ Cis.Xb p j k := by
    simp only [Cis.Xb]; omega
  exact ⟨by omega, by omega⟩

/-- The `expc` word outputs a pair of modulus `≤ 2^(p+60+1)` (disc bound). -/
theorem norm_UV_le {p : ℕ} {U V : ℤ} {A : ℂ}
    (hA : ‖A‖ ≤ 1 - 32 / (2 : ℝ) ^ (p + 60))
    (hz : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) - A‖
      ≤ 4 / (2 : ℝ) ^ (p + 60)) :
    ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ 2 ^ (p + 60 + 1) := by
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ (p + 60) := by positivity
  have hz1 : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)‖ ≤ 1 := by
    have h1 := norm_add_le (((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) - A) A
    have h2 : (((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) - A) + A
        = ((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) := sub_add_cancel _ _
    rw [h2] at h1
    have h3 : (4 : ℝ) / (2 : ℝ) ^ (p + 60) + (1 - 32 / (2 : ℝ) ^ (p + 60)) ≤ 1 := by
      have h4 : (4 : ℝ) / (2 : ℝ) ^ (p + 60) + (1 - 32 / (2 : ℝ) ^ (p + 60))
          = 1 - 28 / (2 : ℝ) ^ (p + 60) := by ring
      rw [h4]
      have h5 : (0 : ℝ) ≤ 28 / (2 : ℝ) ^ (p + 60) := by positivity
      linarith
    linarith
  have heq : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖
      = ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)‖ * (2 : ℝ) ^ (p + 60) := by
    rw [norm_div]
    have hden : ‖((2 : ℂ)) ^ (p + 60)‖ = (2 : ℝ) ^ (p + 60) := by simp [Complex.norm_pow]
    rw [hden]
    field_simp
  rw [heq]
  calc ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)‖ * (2 : ℝ) ^ (p + 60)
      ≤ 1 * (2 : ℝ) ^ (p + 60) := by
        exact mul_le_mul_of_nonneg_right hz1 (by positivity)
    _ = (2 : ℝ) ^ (p + 60) := one_mul _
    _ ≤ (2 : ℝ) ^ (p + 60 + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)


/-! ## Cost helpers for the assembly (top-level: small tactic contexts) -/

theorem costPow32 {KS AC E0 TT X Kc M : ℕ} (hAC : AC = 2 ^ (KS + 256) * KS + 100)
    (hTT : TT = AC * X ^ E0) (hE0 : 32 ≤ E0) (hX : 0 < X) (hK : Kc ≤ KS) (hM : M ≤ 2 * X) :
    Kc * M ^ 32 ≤ TT := by
  have hM32 : M ^ 32 ≤ 2 ^ 32 * X ^ 32 := by
    calc M ^ 32 ≤ (2 * X) ^ 32 := Nat.pow_le_pow_left hM 32
      _ = 2 ^ 32 * X ^ 32 := by rw [Nat.mul_pow]
  have h32E : X ^ 32 ≤ X ^ E0 := Nat.pow_le_pow_right hX hE0
  have hconst : Kc * 2 ^ 32 ≤ AC := by
    rw [hAC]
    have h1 : Kc * 2 ^ 32 ≤ 2 ^ (KS + 256) * KS := by
      calc Kc * 2 ^ 32 ≤ KS * 2 ^ (KS + 256) :=
            Nat.mul_le_mul hK (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (KS + 256) * KS := by ring
    omega
  have hmain : Kc * M ^ 32 ≤ AC * X ^ E0 :=
    calc Kc * M ^ 32 ≤ Kc * (2 ^ 32 * X ^ 32) := Nat.mul_le_mul_left _ hM32
      _ = (Kc * 2 ^ 32) * X ^ 32 := by ring
      _ ≤ AC * X ^ 32 := Nat.mul_le_mul_right _ hconst
      _ ≤ AC * X ^ E0 := Nat.mul_le_mul_left _ h32E
  exact hmain.trans (le_of_eq hTT.symm)

theorem costLin {KS AC E0 TT X Kc N : ℕ} (hAC : AC = 2 ^ (KS + 256) * KS + 100)
    (hTT : TT = AC * X ^ E0) (hE0 : 1 ≤ E0) (hX : 0 < X) (hK : Kc ≤ KS) (hN : N ≤ 8 * X) :
    Kc * N ≤ TT := by
  have hKS8 : KS * 8 ≤ AC := by
    rw [hAC]
    have h1 : KS * 8 ≤ 2 ^ (KS + 256) * KS := by
      calc KS * 8 ≤ KS * 2 ^ (KS + 256) := Nat.mul_le_mul_left _ (by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (KS + 256) := Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (KS + 256) * KS := by ring
    omega
  have h1E : X ^ 1 ≤ X ^ E0 := Nat.pow_le_pow_right hX hE0
  have hmain : Kc * N ≤ AC * X ^ E0 :=
    calc Kc * N ≤ KS * (8 * X) := Nat.mul_le_mul hK hN
      _ = (KS * 8) * X := by ring
      _ ≤ AC * X := Nat.mul_le_mul_right _ hKS8
      _ ≤ AC * X ^ E0 := Nat.mul_le_mul_left _ (by
            calc X = X ^ 1 := (pow_one X).symm
              _ ≤ X ^ E0 := h1E)
  exact hmain.trans (le_of_eq hTT.symm)

theorem costSum {KS AC E0 TT X Kc N M : ℕ} (hAC : AC = 2 ^ (KS + 256) * KS + 100)
    (hTT : TT = AC * X ^ E0) (hE0 : 1 ≤ E0) (hX : 0 < X) (hK : Kc ≤ KS)
    (hN : N ≤ 8 * X) (hM : M ≤ 8 * X) : Kc * (N + M + 1) ≤ TT := by
  have hKS64 : KS * 64 ≤ AC := by
    rw [hAC]
    have h1 : KS * 64 ≤ 2 ^ (KS + 256) * KS := by
      calc KS * 64 ≤ KS * 2 ^ (KS + 256) := Nat.mul_le_mul_left _ (by
            calc (64 : ℕ) = 2 ^ 6 := by norm_num
              _ ≤ 2 ^ (KS + 256) := Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (KS + 256) * KS := by ring
    omega
  have h1E : X ^ 1 ≤ X ^ E0 := Nat.pow_le_pow_right hX hE0
  have hmain : Kc * (N + M + 1) ≤ AC * X ^ E0 :=
    calc Kc * (N + M + 1) ≤ KS * (8 * X + 8 * X + 1) := Nat.mul_le_mul hK (by omega)
      _ ≤ KS * (64 * X) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (KS * 64) * X := by ring
      _ ≤ AC * X := Nat.mul_le_mul_right _ hKS64
      _ ≤ AC * X ^ E0 := Nat.mul_le_mul_left _ (by
            calc X = X ^ 1 := (pow_one X).symm
              _ ≤ X ^ E0 := h1E)
  exact hmain.trans (le_of_eq hTT.symm)

theorem costExp {KS AC E0 TT X Kc e : ℕ} {p : ℕ} (hAC : AC = 2 ^ (KS + 256) * KS + 100)
    (hTT : TT = AC * X ^ E0) (hE0 : e ≤ E0) (hX : 0 < X) (hK : Kc ≤ KS)
    (hE0' : E0 ≤ KS + 256) (h61 : p + 60 + 1 ≤ 2 * X) :
    Kc * (p + 60 + 1) ^ e ≤ TT := by
  have h2 : (p + 60 + 1) ^ e ≤ (2 * X) ^ e := Nat.pow_le_pow_left h61 e
  have h3 : (2 * X) ^ e = 2 ^ e * X ^ e := by rw [Nat.mul_pow]
  have hconst : Kc * 2 ^ e ≤ AC := by
    rw [hAC]
    have h1 : Kc * 2 ^ e ≤ 2 ^ (KS + 256) * KS := by
      calc Kc * 2 ^ e ≤ KS * 2 ^ (KS + 256) :=
            Nat.mul_le_mul hK (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (KS + 256) * KS := by ring
    omega
  have h5 : X ^ e ≤ X ^ E0 := Nat.pow_le_pow_right hX hE0
  have hmain : Kc * (p + 60 + 1) ^ e ≤ AC * X ^ E0 :=
    calc Kc * (p + 60 + 1) ^ e ≤ Kc * (2 ^ e * X ^ e) := Nat.mul_le_mul_left _ (h2.trans_eq h3)
      _ = (Kc * 2 ^ e) * X ^ e := by ring
      _ ≤ AC * X ^ e := Nat.mul_le_mul_right _ hconst
      _ ≤ AC * X ^ E0 := Nat.mul_le_mul_left _ h5
  exact hmain.trans (le_of_eq hTT.symm)


theorem cisField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (h : Work.Fx.NumWords hk hi) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (j : ℤ) (k : ℕ), 100 ≤ p → 1 ≤ k →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val),
          vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int j :: HvdH.Val.int (k : ℤ) :: rest)
      (fun vs out => ∃ (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int j :: HvdH.Val.int (k : ℤ) :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
        (2 : ℝ) ^ p * ‖HvdH.fxC p w - Complex.exp (2 * Real.pi * Complex.I * j / k)‖ < 2)
      (fun _ => K * (p + HvdH.isz j + HvdH.isz k) ^ K) := by
  obtain ⟨piProg, Kpi, hpi⟩ := h.pi
  obtain ⟨expProg, Kexp, hexp⟩ := h.expc
  obtain ⟨s1Prog, K1, hS1⟩ := Work.Fx.CisStep1 hk hi
  obtain ⟨s4Prog, K4, hS4⟩ := Work.Fx.CisStep4 hk hi
  obtain ⟨s6Prog, K6, hS6⟩ := Work.Fx.CisStep6 hk hi
  obtain ⟨pickProg, Kpick, hPick⟩ := hk.pick
  obtain ⟨swapProg, Kswap, hSwap⟩ := hk.swap
  obtain ⟨pushProg, Kpush, hPush⟩ := hk.pushVal
  set KS : ℕ := K1 + K4 + K6 + Kpick + Kswap + Kpush + Kpi + Kexp + 1 with hKS
  set AC : ℕ := 2 ^ (KS + 256) * KS + 100 with hAC
  set E0 : ℕ := max 32 (max Kpi Kexp) with hE0
  set Kfin : ℕ := 200 * (AC + E0 + 1) with hKfin
  let c1 : HvdH.Cmd := HvdH.Cmd.seq s1Prog (pickProg 0)
  let c2 : HvdH.Cmd := HvdH.Cmd.seq c1 piProg
  let c3 : HvdH.Cmd := HvdH.Cmd.seq c2 s4Prog
  let c4 : HvdH.Cmd := HvdH.Cmd.seq c3 swapProg
  let c5 : HvdH.Cmd := HvdH.Cmd.seq c4 (pushProg (HvdH.Val.int (-64)))
  let c6 : HvdH.Cmd := HvdH.Cmd.seq c5 swapProg
  let c7 : HvdH.Cmd := HvdH.Cmd.seq c6 expProg
  let prog : HvdH.Cmd := HvdH.Cmd.seq c7 s6Prog
  refine ⟨prog, Kfin, ?_⟩
  intro main p j k hp hk1
  let E : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (k : ℂ))
  let RT : ℤ → ℤ := fun w => Int.tdiv (2 * w * Int.fmod j k) k
  let Bnd : ℤ → Prop := fun w => |(w : ℝ) - 2 ^ (p + 60) * Real.pi| ≤ 1
  let Qfin : List HvdH.Val → Prop := fun o => ∃ w : ℤ × ℤ, o = [HvdH.cfxVal w] ∧
      HvdH.inDisc p w ∧ (2 : ℝ) ^ p * ‖HvdH.fxC p w - E‖ < 2
  have hPpZ : (((p + 60 : ℕ)) : ℤ) = (p : ℤ) + 60 := by push_cast; ring
  have hj2 : 2 ≤ HvdH.isz j := Work.Fx.Cis.two_le_isz j
  have hk2 : 2 ≤ HvdH.isz (k : ℤ) := Work.Fx.Cis.two_le_isz (k : ℤ)
  have hX104 : 104 ≤ p + HvdH.isz j + HvdH.isz k := by omega
  have hXpos : 0 < p + HvdH.isz j + HvdH.isz k := by omega
  have hXb_ge : 168 ≤ Work.Fx.Cis.Xb p j k := Work.Fx.Cis.Xb_ge p j k hp
  have hXb_le : Work.Fx.Cis.Xb p j k ≤ 2 * (p + HvdH.isz j + HvdH.isz k) := by
    simp only [Work.Fx.Cis.Xb]; omega
  have h32E : (p + HvdH.isz j + HvdH.isz k) ^ 32 ≤ (p + HvdH.isz j + HvdH.isz k) ^ E0 :=
    Nat.pow_le_pow_right hXpos (by rw [hE0]; exact le_max_left _ _)
  have h1E : (p + HvdH.isz j + HvdH.isz k) ^ 1 ≤ (p + HvdH.isz j + HvdH.isz k) ^ E0 :=
    Nat.pow_le_pow_right hXpos (by rw [hE0]; exact le_trans (by norm_num) (le_max_left _ _))
  have hKpiE : Kpi ≤ E0 := by rw [hE0]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKexpE : Kexp ≤ E0 := by rw [hE0]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hK1 : K1 ≤ KS := by omega
  have hK4 : K4 ≤ KS := by omega
  have hK6 : K6 ≤ KS := by omega
  have hKpick : Kpick ≤ KS := by omega
  have hKswap : Kswap ≤ KS := by omega
  have hKpush : Kpush ≤ KS := by omega
  have hKpi : Kpi ≤ KS := by omega
  have hKexp : Kexp ≤ KS := by omega
  have hE0le : E0 ≤ KS + 256 := by rw [hE0]; omega
  set TT : ℕ := AC * (p + HvdH.isz j + HvdH.isz k) ^ E0 with hTT
  have hE032 : 32 ≤ E0 := by rw [hE0]; exact le_max_left _ _
  have hE01 : 1 ≤ E0 := le_trans (by norm_num) hE032
  have hX61 : p + 60 + 1 ≤ 2 * (p + HvdH.isz j + HvdH.isz k) := by omega
  have cost_pow32 : ∀ (Kc M : ℕ), Kc ≤ KS → M ≤ 2 * (p + HvdH.isz j + HvdH.isz k) →
      Kc * M ^ 32 ≤ TT := fun Kc M hK hM => costPow32 hAC hTT hE032 hXpos hK hM
  have cost_lin : ∀ (Kc N : ℕ), Kc ≤ KS → N ≤ 8 * (p + HvdH.isz j + HvdH.isz k) →
      Kc * N ≤ TT := fun Kc N hK hN => costLin hAC hTT hE01 hXpos hK hN
  have cost_sum : ∀ (Kc N M : ℕ), Kc ≤ KS → N ≤ 8 * (p + HvdH.isz j + HvdH.isz k) →
      M ≤ 8 * (p + HvdH.isz j + HvdH.isz k) → Kc * (N + M + 1) ≤ TT :=
    fun Kc N M hK hN hM => costSum hAC hTT hE01 hXpos hK hN hM
  have cost_exp : ∀ (Kc e : ℕ), Kc ≤ KS → e ≤ E0 → Kc * (p + 60 + 1) ^ e ≤ TT :=
    fun Kc e hK he => costExp (X := p + HvdH.isz j + HvdH.isz k) hAC hTT he hXpos hK hE0le hX61
  -- sizes of the intermediate values
  have hszP : HvdH.isz ((p : ℤ) + 60) ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    have h1 := Work.Fx.Cis.isz_p_add_sixty_le_Xb p j k hp
    omega
  have hszP1 : HvdH.isz ((p : ℤ) + 60) + 1 ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    have h1 := Work.Fx.Cis.isz_p_add_sixty_le_Xb p j k hp
    omega
  have hszF : HvdH.isz (Int.fmod j k) ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    have h1 := Work.Fx.Cis.isz_fmod_le_Xb p j k hk1
    omega
  have hszK : HvdH.isz (k : ℤ) ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    have h1 := Work.Fx.Cis.isz_le_Xb_k p j k
    omega
  have hsz64 : HvdH.isz (-64 : ℤ) ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    rw [Work.Fx.Cis.isz_neg64]; omega
  have hszR : ∀ (R w : ℤ), R = RT w → Bnd w → HvdH.isz R ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
    intro R w hR hw
    subst hR
    have hw' : HvdH.isz w ≤ Work.Fx.Cis.Xb p j k := Work.Fx.Cis.isz_u_le_Xb hp hw
    have h1 : HvdH.isz (RT w) ≤ HvdH.isz (2 * w * Int.fmod j k) := Work.Fx.isz_tdiv_le _ _
    have h2 : HvdH.isz (2 * w * Int.fmod j k) ≤ HvdH.isz (2 * w) + HvdH.isz (Int.fmod j k) :=
      isz_mul_le (2 * w) (Int.fmod j k)
    have h3 : HvdH.isz (2 * w) ≤ HvdH.isz (2 : ℤ) + HvdH.isz w := isz_mul_le 2 w
    have h4 : HvdH.isz (2 : ℤ) = 4 := Work.Fx.Cis.isz_two
    have h5 : HvdH.isz (Int.fmod j k) ≤ Work.Fx.Cis.Xb p j k := Work.Fx.Cis.isz_fmod_le_Xb p j k hk1
    omega
  -- ## the chain
  have hchain1 : Cis.PipeQ main s1Prog
      [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
        HvdH.Val.int (k : ℤ)]) TT :=
    Cis.PipeQ.le (hS1 main p j k hp hk1) (cost_pow32 K1 (Work.Fx.Cis.Xb p j k) hK1 hXb_le)
  have hchain2 : Cis.Pipe main (pickProg 0)
      [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)]
      [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
        HvdH.Val.int (k : ℤ)] TT :=
    Cis.Pipe.le
      (Cis.Pipe.rw
        (Cis.Pipe.pick main hPick
          (A := [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)])
          (k := 0) (by simp))
        (by simp))
      (by
        have hszp : szl ([HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
            HvdH.Val.int (k : ℤ)].take 1) = HvdH.isz ((p : ℤ) + 60) := by
          simp [szl]
        rw [hszp]
        have h := cost_lin Kpick ((0 + 1) * (HvdH.isz ((p : ℤ) + 60) + 1)) hKpick (by
          rw [Nat.one_mul]; exact hszP1)
        simpa using h)
  have hchain3 : Cis.PipeQ main c1 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int ((p : ℤ) + 60),
        HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)]) (2 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain1 (fun o ho => by rw [ho]; exact Cis.Pipe.toPipeQ hchain2))
      (le_of_eq (by ring))
  have hchainPi : Cis.PipeQ main piProg
      [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int ((p : ℤ) + 60),
        HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w : ℤ, o = [HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60),
          HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)] ∧ Bnd w) TT := by
    intro rest vs hvs s R hR
    have hp60 : 100 ≤ p + 60 := by omega
    have hpre : ∃ rest' : List HvdH.Val, vs = HvdH.Val.int (((p + 60 : ℕ) : ℤ)) :: rest' :=
      ⟨_, by rw [hvs, ← hPpZ]; rfl⟩
    obtain ⟨out, s', n, ⟨rest', w, hvs', hout, hw⟩, hev, hn, hstk, hoth⟩ :=
      hpi main (p + 60) hp60 vs hpre s R hR
    have hrest : rest' = [HvdH.Val.int (((p + 60 : ℕ) : ℤ)), HvdH.Val.int (Int.fmod j k),
        HvdH.Val.int (k : ℤ)] ++ rest := by
      have h1 : (HvdH.Val.int (((p + 60 : ℕ) : ℤ)) :: rest') =
          (HvdH.Val.int (((p + 60 : ℕ) : ℤ)) ::
            ([HvdH.Val.int (((p + 60 : ℕ) : ℤ)), HvdH.Val.int (Int.fmod j k),
              HvdH.Val.int (k : ℤ)] ++ rest)) := by
        rw [← hvs', hvs]
        rfl
      exact (List.cons.inj h1).2
    have hgoal : (HvdH.Val.int w :: ([HvdH.Val.int (((p + 60 : ℕ) : ℤ)),
        HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)] ++ rest)) =
        ([HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
          HvdH.Val.int (k : ℤ)] ++ rest) := by
      simp only [← hPpZ, List.cons_append, List.nil_append]
    refine ⟨out, s', n, ⟨[HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60),
        HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)], ?_, ⟨w, rfl, hw⟩⟩, hev,
      le_trans hn (cost_exp Kpi Kpi hKpi hKpiE), hstk, hoth⟩
    rw [hout, hrest]
    exact hgoal
  have hchain4 : Cis.PipeQ main c2 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w : ℤ, o = [HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60),
          HvdH.Val.int (Int.fmod j k), HvdH.Val.int (k : ℤ)] ∧ Bnd w) (3 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain3 (fun o ho => by rw [ho]; exact hchainPi))
      (le_of_eq (by ring))
  have hchainS4 : ∀ (w : ℤ), Bnd w → Cis.PipeQ main s4Prog
      [HvdH.Val.int w, HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (Int.fmod j k),
        HvdH.Val.int (k : ℤ)]
      (fun o => ∃ R : ℤ, o = [HvdH.Val.int R, HvdH.Val.int ((p : ℤ) + 60)] ∧ R = RT w) TT := by
    intro w hw
    have hw' : HvdH.isz w ≤ Work.Fx.Cis.Xb p j k := Work.Fx.Cis.isz_u_le_Xb hp hw
    refine Cis.PipeQ.le (Cis.PipeQ.mono (hS4 main p j k hp hk1 w hw') ?_)
      (cost_pow32 K4 (Work.Fx.Cis.Xb p j k) hK4 hXb_le)
    intro o ho
    exact ⟨RT w, ho, rfl⟩
  have hchain5 : Cis.PipeQ main c3 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w R : ℤ, o = [HvdH.Val.int R, HvdH.Val.int ((p : ℤ) + 60)] ∧ Bnd w ∧
        R = RT w) (4 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain4 (fun o ho => by
      rcases ho with ⟨w, hwin, hw⟩
      rw [hwin]
      exact Cis.PipeQ.mono (hchainS4 w hw)
        (fun o ho2 => by rcases ho2 with ⟨R, hR, hRdef⟩; exact ⟨w, R, hR, hw, hRdef⟩)))
      (le_of_eq (by ring))
  have hchainSw1 : ∀ (R w : ℤ), Bnd w → R = RT w → Cis.PipeQ main swapProg
      [HvdH.Val.int R, HvdH.Val.int ((p : ℤ) + 60)]
      (fun o => o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R]) TT := by
    intro R w hw hRdef
    refine Cis.PipeQ.le (Cis.Pipe.toPipeQ
      (Cis.Pipe.swap main hSwap (HvdH.Val.int R) (HvdH.Val.int ((p : ℤ) + 60)))) ?_
    rw [vsz_int, vsz_int]
    exact cost_sum Kswap (HvdH.isz R) (HvdH.isz ((p : ℤ) + 60)) hKswap
      (hszR R w hRdef hw) hszP
  have hchain6 : Cis.PipeQ main c4 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w R : ℤ, o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R] ∧ Bnd w ∧
        R = RT w) (5 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain5 (fun o ho => by
      rcases ho with ⟨w, R, hwin, hw, hRdef⟩
      rw [hwin]
      exact Cis.PipeQ.mono (hchainSw1 R w hw hRdef)
        (fun o ho2 => by rw [ho2]; exact ⟨w, R, rfl, hw, hRdef⟩)))
      (le_of_eq (by ring))
  have hchainPush : ∀ (R w : ℤ), Bnd w → R = RT w →
      Cis.PipeQ main (pushProg (HvdH.Val.int (-64)))
      [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R]
      (fun o => o = [HvdH.Val.int (-64), HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R]) TT := by
    intro R w hw hRdef
    refine Cis.PipeQ.le (Cis.Pipe.toPipeQ (Cis.Pipe.pushOnAny
      (T := [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R])
      (hPush main (HvdH.Val.int (-64))))) ?_
    rw [vsz_int]
    have h10 : HvdH.isz (-64 : ℤ) + 1 ≤ 8 * (p + HvdH.isz j + HvdH.isz k) := by
      rw [Work.Fx.Cis.isz_neg64]; omega
    exact cost_lin Kpush _ hKpush h10
  have hchain7 : Cis.PipeQ main c5 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w R : ℤ, o = [HvdH.Val.int (-64), HvdH.Val.int ((p : ℤ) + 60),
        HvdH.Val.int R] ∧ Bnd w ∧ R = RT w) (6 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain6 (fun o ho => by
      rcases ho with ⟨w, R, hwin, hw, hRdef⟩
      rw [hwin]
      exact Cis.PipeQ.mono (hchainPush R w hw hRdef)
        (fun o ho2 => by rw [ho2]; exact ⟨w, R, rfl, hw, hRdef⟩)))
      (le_of_eq (by ring))
  have hchainSw2 : ∀ (R w : ℤ), Bnd w → R = RT w → Cis.PipeQ main swapProg
      [HvdH.Val.int (-64), HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int R]
      (fun o => o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (-64), HvdH.Val.int R]) TT := by
    intro R w hw hRdef
    refine Cis.PipeQ.le (Cis.Pipe.toPipeQ (Cis.Pipe.appendTail [HvdH.Val.int R]
      (Cis.Pipe.swap main hSwap (HvdH.Val.int (-64)) (HvdH.Val.int ((p : ℤ) + 60))))) ?_
    rw [vsz_int, vsz_int]
    exact cost_sum Kswap (HvdH.isz (-64)) (HvdH.isz ((p : ℤ) + 60)) hKswap hsz64 hszP
  have hchain8 : Cis.PipeQ main c6 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w R : ℤ, o = [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (-64),
        HvdH.Val.int R] ∧ Bnd w ∧ R = RT w) (7 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain7 (fun o ho => by
      rcases ho with ⟨w, R, hwin, hw, hRdef⟩
      rw [hwin]
      exact Cis.PipeQ.mono (hchainSw2 R w hw hRdef)
        (fun o ho2 => by rw [ho2]; exact ⟨w, R, rfl, hw, hRdef⟩)))
      (le_of_eq (by ring))
  have hchainExp : ∀ (R w : ℤ), Bnd w → R = RT w → Cis.PipeQ main expProg
      [HvdH.Val.int ((p : ℤ) + 60), HvdH.Val.int (-64), HvdH.Val.int R]
      (fun o => ∃ U V : ℤ, o = [HvdH.Val.int U, HvdH.Val.int V] ∧
        ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
          - Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
          ≤ 4 / (2 : ℝ) ^ (p + 60)) TT := by
    intro R w hw hRdef
    have hRb : |(((RT w : ℤ)) : ℝ)
        - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ))| ≤ 3 :=
      Work.Fx.CisRbound p j k hk1 w hw
    have hExp := Work.Fx.CisExpBoundB p hp j k hk1 (RT w) hRb
    intro rest vs hvs s R0 hR0
    have hp60 : 100 ≤ p + 60 := by omega
    have hpre : ∃ rest' : List HvdH.Val, vs = HvdH.Val.int (((p + 60 : ℕ) : ℤ)) ::
        HvdH.Val.int (-64) :: HvdH.Val.int (RT w) :: rest' :=
      ⟨_, by rw [hvs, ← hPpZ, hRdef]; rfl⟩
    obtain ⟨out, s', n, ⟨rest', U, V, hvs', hout, hnorm⟩, hev, hn, hstk, hoth⟩ :=
      hexp main (p + 60) (-64) (RT w) hp60 (by simpa using hExp.2.2) vs hpre s R0 hR0
    have hrest : rest' = rest := by
      have h1 : (HvdH.Val.int (((p + 60 : ℕ) : ℤ)) :: HvdH.Val.int (-64) ::
          HvdH.Val.int (RT w) :: rest') =
          (HvdH.Val.int (((p + 60 : ℕ) : ℤ)) :: HvdH.Val.int (-64) ::
            HvdH.Val.int (RT w) :: rest) := by
        rw [← hvs', hvs, ← hPpZ, hRdef]
        rfl
      exact (List.cons.inj (List.cons.inj (List.cons.inj h1).2).2).2
    have hnorm' : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
          - Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
          ≤ 4 / (2 : ℝ) ^ (p + 60) := by
      rw [hRdef]
      exact hnorm
    refine ⟨out, s', n, ⟨[HvdH.Val.int U, HvdH.Val.int V], ?_, U, V, rfl, hnorm'⟩, hev,
      le_trans hn (cost_exp Kexp Kexp hKexp hKexpE), hstk, hoth⟩
    rw [hout, hrest]
    rfl
  have hchain9 : Cis.PipeQ main c7 [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      (fun o => ∃ w R U V : ℤ, o = [HvdH.Val.int U, HvdH.Val.int V] ∧ Bnd w ∧ R = RT w ∧
        ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
          - Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
          ≤ 4 / (2 : ℝ) ^ (p + 60)) (8 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain8 (fun o ho => by
      rcases ho with ⟨w, R, hwin, hw, hRdef⟩
      rw [hwin]
      exact Cis.PipeQ.mono (hchainExp R w hw hRdef)
        (fun o ho2 => by
          rcases ho2 with ⟨U, V, hUo, hNB⟩
          exact ⟨w, R, U, V, hUo, hw, hRdef, hNB⟩)))
      (le_of_eq (by ring))
  have hchainS6 : ∀ (U V R w : ℤ), Bnd w → R = RT w →
      ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
        - Complex.exp ((((-64 : ℤ) : ℂ) + (R : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
        ≤ 4 / (2 : ℝ) ^ (p + 60) →
      Cis.PipeQ main s6Prog [HvdH.Val.int U, HvdH.Val.int V] Qfin TT := by
    intro U V R w hw hRdef hnorm
    have hRb : |(((RT w : ℤ)) : ℝ)
        - 2 ^ (p + 60) * (2 * Real.pi * (Int.fmod j k : ℝ) / (k : ℝ))| ≤ 3 :=
      Work.Fx.CisRbound p j k hk1 w hw
    have hExp := Work.Fx.CisExpBoundB p hp j k hk1 (RT w) hRb
    have hA : ‖Complex.exp ((((-64 : ℤ) : ℂ) + ((RT w) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (p + 60))‖ ≤ 1 - 32 / (2 : ℝ) ^ (p + 60) := hExp.1
    have hAE : ‖Complex.exp ((((-64 : ℤ) : ℂ) + ((RT w) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (p + 60)) - E‖ ≤ 67 / (2 : ℝ) ^ (p + 60) := by
      have h2 := hExp.2.1
      rw [show E = Complex.exp (2 * Real.pi * Complex.I * ((Int.fmod j k : ℤ) : ℂ) / (k : ℂ))
        from Work.Fx.CisPhase j k hk1]
      exact h2
    have hnorm' : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)
        - Complex.exp ((((-64 : ℤ) : ℂ) + ((RT w) : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
        ≤ 4 / (2 : ℝ) ^ (p + 60) := by
      rw [hRdef] at hnorm
      exact hnorm
    have hUV : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ 2 ^ (p + 60 + 1) :=
      norm_UV_le (A := Complex.exp ((((-64 : ℤ) : ℂ) + ((RT w) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (p + 60))) hA hnorm'
    obtain ⟨hU, hV⟩ := isz_le_Xb_of_norm hUV
    have htr := Work.Fx.CisTrunc p hp U V E
      (Complex.exp ((((-64 : ℤ) : ℂ) + ((RT w) : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60)))
      hA hnorm' hAE
    refine Cis.PipeQ.le (Cis.PipeQ.mono (hS6 main (Work.Fx.Cis.Xb p j k) U V hU hV) ?_)
      (cost_pow32 K6 (Work.Fx.Cis.Xb p j k) hK6 hXb_le)
    intro o ho
    exact ⟨(Int.tdiv U (2 ^ 60), Int.tdiv V (2 ^ 60)), ho, htr.1, htr.2⟩
  have hAll : Cis.PipeQ main prog [HvdH.Val.int (p : ℤ), HvdH.Val.int j, HvdH.Val.int (k : ℤ)]
      Qfin (9 * TT) :=
    Cis.PipeQ.le (Cis.PipeQ.comp hchain9 (fun o ho => by
      rcases ho with ⟨w, R, U, V, hwin, hw, hRdef, hnorm⟩
      rw [hwin]
      exact hchainS6 U V R w hw hRdef hnorm))
      (le_of_eq (by ring))
  -- final cost arithmetic
  have hcost : 9 * TT ≤ Kfin * (p + HvdH.isz j + HvdH.isz k) ^ Kfin := by
    have h1 : 9 * AC ≤ Kfin := by rw [hKfin]; omega
    have h2 : E0 ≤ Kfin := by rw [hKfin]; omega
    have h3 : (0 : ℕ) < p + HvdH.isz j + HvdH.isz k := by omega
    have h4 : 9 * TT = (9 * AC) * (p + HvdH.isz j + HvdH.isz k) ^ E0 := by rw [hTT]; ring
    rw [h4]
    calc (9 * AC) * (p + HvdH.isz j + HvdH.isz k) ^ E0
        ≤ Kfin * (p + HvdH.isz j + HvdH.isz k) ^ E0 := Nat.mul_le_mul_right _ h1
      _ ≤ Kfin * (p + HvdH.isz j + HvdH.isz k) ^ Kfin :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h3 h2)
  intro vs hpre s R hR
  obtain ⟨rest, hvs⟩ := hpre
  obtain ⟨out, s', n, ⟨o, hout, w, ho, hdisc, herr⟩, hev, hn, hstk, hoth⟩ :=
    hAll rest vs hvs s R hR
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hoth⟩
  · refine ⟨rest, w, ?_, ?_, hdisc, herr⟩
    · simpa using hvs
    · rw [hout, ho, List.singleton_append]
  · exact le_trans hn hcost

end Work.Fx
