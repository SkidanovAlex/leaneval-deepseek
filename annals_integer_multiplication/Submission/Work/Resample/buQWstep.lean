import Mathlib
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buQWprodElem
import Submission.Work.Resample.buQWcolWord
import Submission.Work.Resample.buQWpostWord

/-!
# `Work.Resample.buQWstep`: one Neumann round of the `B̃` word

Assembly of the single-round word of the one-dimensional `B̃` resampling (paper Lemma 4.11):

`q` prepends the zero vector, folds the column table `buColsT p α s t` over the accumulator with the
per-column word `buQWcolWord` (rotating the input vector, multiplying by the tabulated weights and
adding), then divides by `2^p` and accumulates the signed result into the Neumann sum
(`buQWpostWord`).  The invariant of the fold is the partial fold `buPFold` together with the size
bounds of its entries; the disc bounds of the output come from the row-sum bound `hrow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

theorem buQWstep (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2
          + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val),
        (σ = 1 ∨ σ = -1) ∧
        vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ acc.length = s ∧ Work.Resample.buInV B v ∧ Work.Resample.buInV B2 acc)
      (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val) (v' acc' : List (ℤ × ℤ)),
        (σ = 1 ∨ σ = -1) ∧
        vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal v' :: HvdH.cvecVal acc' :: rest ∧
        v' = Work.Resample.buRoundL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α) v ∧
        acc' = Work.Resample.buAddV acc (Work.Resample.buSMulV σ v') ∧
        v'.length = s ∧ acc'.length = s ∧
        Work.Resample.buInV (B / 2 + 34 * Work.Resample.egM p α + 4) v' ∧
        Work.Resample.buInV (B2 + B / 2 + 34 * Work.Resample.egM p α + 5) acc')
      (fun _ => Kc * (Work.Resample.egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨dupP, kdup, hdup⟩ := KL.dup
  obtain ⟨dropP, kdrop, hdrop⟩ := KL.drop
  obtain ⟨pickP, kpick, hpick⟩ := KL.pick
  obtain ⟨rollP, kroll, hroll⟩ := KL.roll
  obtain ⟨pushP, kpush, hpush⟩ := KL.pushVal
  obtain ⟨foldP, kfold, hfold⟩ := KL.foldList
  obtain ⟨repP, krep, hrep⟩ := LL.replicate
  obtain ⟨colP, kcol, hcol⟩ := buQWcolWord KL IL LL
  obtain ⟨postP, kpost, hpost⟩ := buQWpostWord KL IL
  let KS : ℕ := kdup + kdrop + kpick + kroll + kpush + kfold + krep + kcol + kpost + 100
  let KC : ℕ := 1000000 * KS
  refine ⟨.seq (.seq (.seq (pushP (cfxVal (0, 0))) (.seq (pickP 5) (.seq repP (rollP 4))))
    (foldP colP)) postP, KC, ?_⟩
  intro p α s t hs hst hα hp B B2 hB hB2 hrow main N Cm hmono hmb hKN
  have hKdup : kdup ≤ KS := by simp only [KS]; omega
  have hKdrop : kdrop ≤ KS := by simp only [KS]; omega
  have hKpick : kpick ≤ KS := by simp only [KS]; omega
  have hKroll : kroll ≤ KS := by simp only [KS]; omega
  have hKpush : kpush ≤ KS := by simp only [KS]; omega
  have hKfold : kfold ≤ KS := by simp only [KS]; omega
  have hKrep : krep ≤ KS := by simp only [KS]; omega
  have hKcol : kcol ≤ KS := by simp only [KS]; omega
  have hKpost : kpost ≤ KS := by simp only [KS]; omega
  have hKNcol : kcol * p < N := by
    have h : kcol * p ≤ KC * p := Nat.mul_le_mul_right p (by simp only [KC]; nlinarith)
    omega
  have hm1 : 1 ≤ egM p α := by
    show 1 ≤ Nat.sqrt p / (2 * α) + 1
    exact le_add_of_nonneg_left (Nat.zero_le _)
  have hcolsT : vsz (buColsT p α s t) ≤ 1000 * (egM p α + 1) * (s + 1) * (p + 1) :=
    buQW_colsT_vsz_le p α s t hs hα hp hrow
  intro vs hpre
  obtain ⟨σ, v, acc, rest, hσ, hvs, hvlen, hacclen, hvin, haccin⟩ := hpre
  -- the prepared stack and the invariant
  set XS : List Val := (egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)) with hXS
  set zF : List (ℤ × ℤ) := buPFold (buWt p α s t) s (egM p α) v (2 * egM p α) with hzF
  set v' : List (ℤ × ℤ) := buTdivV p zF with hv'
  set acc' : List (ℤ × ℤ) := buAddV acc (buSMulV σ v') with hacc'
  have hXSlen : XS.length = 2 * egM p α := by
    simp only [hXS, List.length_map, buQWhs_length]
  have hbufold : buRoundL (buWt p α s t) p s (egM p α) v = v' := by
    rw [hv', hzF, buRoundL_eq_pfold]
  -- the invariant
  set I : ℕ → List Val → Prop := fun i st =>
    ∃ z : List (ℤ × ℤ), st = cvecVal z :: .int σ :: cvecVal v :: cvecVal acc ::
        .int (s : ℤ) :: .int (p : ℤ) :: rest ∧
      z = buPFold (buWt p α s t) s (egM p α) v i ∧ z.length = s ∧
      (∀ y ∈ z, isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8) with hI


  -- ===== 1. the size facts of the input values =====
  have hvin' : ∀ z ∈ v, ‖gz z‖ ≤ (B : ℝ) := fun z hz => (buInV_iff B v).mp hvin z hz
  have haccin' : ∀ z ∈ acc, ‖gz z‖ ≤ (B2 : ℝ) := fun z hz => (buInV_iff B2 acc).mp haccin z hz
  have hvsz : ∀ z ∈ v, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 :=
    fun z hz => buQW_isz_of_buInV hB hvin z hz
  have haccsz : ∀ z ∈ acc, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 :=
    fun z hz => buQW_isz_of_buInV hB2 haccin z hz
  have hszsigma : isz σ ≤ 3 := by
    rcases hσ with h | h <;> rw [h] <;> decide
  have hszs : isz (s : ℤ) ≤ 40 * (s + 1) * (p + 1) := by
    simp only [isz, Int.natAbs_natCast]
    have h : s.size ≤ s + 1 :=
      Nat.size_le.mpr (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ s)))
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  have hszp : isz (p : ℤ) ≤ 40 * (s + 1) * (p + 1) := by
    simp only [isz, Int.natAbs_natCast]
    have h : p.size ≤ p + 1 :=
      Nat.size_le.mpr (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p)))
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  have hszZ : isz ((0 : ℤ)) ≤ 3 := by decide
  have hszvr : vsz (cvecVal (List.replicate s ((0 : ℤ), (0 : ℤ)))) ≤ 40 * (s + 1) * (p + 1) := by
    have h : ∀ z ∈ List.replicate s ((0 : ℤ), (0 : ℤ)), isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 := by
      intro z hz
      have hz' : z = ((0 : ℤ), (0 : ℤ)) := List.eq_of_mem_replicate hz
      rw [hz']
      have h0 : isz ((0 : ℤ)) ≤ p + 5 := by simp only [isz, Int.natAbs_zero, Nat.size_zero]; omega
      exact ⟨h0, h0⟩
    have h2 := buQT_vsz_cvecVal (u := List.replicate s ((0 : ℤ), (0 : ℤ))) (M := p + 5) h
    have h3 : 3 * (List.replicate s ((0 : ℤ), (0 : ℤ))).length * (p + 5 + 1) + 1
        ≤ 40 * (s + 1) * (p + 1) := by
      rw [List.length_replicate]
      nlinarith [Nat.zero_le s, Nat.zero_le p]
    linarith
  -- ===== 2. the numerical constants =====
  let SB : ℕ := 1000 * ((egM p α + 1) * (s + 1) * (p + 1))
  let QA : ℕ := (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1)
  let KCST : ℕ := KC * (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1)
  let MPC : ℕ := KS * 100 * SB
  have hSB1 : 1 ≤ SB := by
    have ha : 1 ≤ egM p α + 1 := by omega
    have hb : 1 ≤ s + 1 := by omega
    have hc : 1 ≤ p + 1 := by omega
    have h2 : 1 ≤ (egM p α + 1) * (s + 1) := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ (egM p α + 1) * (s + 1) := Nat.mul_le_mul ha hb
    have h1 : 1 ≤ (egM p α + 1) * (s + 1) * (p + 1) := by
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ ((egM p α + 1) * (s + 1)) * (p + 1) := Nat.mul_le_mul h2 hc
    simp only [SB]
    nlinarith [h1]
  have h40 : 40 ≤ 1000 * (egM p α + 1) := by
    have hm : 1 ≤ egM p α + 1 := Nat.succ_le_succ (Nat.zero_le _)
    nlinarith
  have hszall : ∀ a : ℕ, a ≤ 40 * (s + 1) * (p + 1) → a ≤ SB := by
    intro a ha
    have h1 : 40 * (s + 1) * (p + 1) ≤ 1000 * (egM p α + 1) * (s + 1) * (p + 1) := by
      nlinarith [h40, Nat.zero_le s, Nat.zero_le p]
    have h2 : 1000 * (egM p α + 1) * (s + 1) * (p + 1) = SB := by simp only [SB]; ring
    linarith
  have hcolsTSB : vsz (buColsT p α s t) ≤ SB := by
    have h := buQW_colsT_vsz_le p α s t hs hα hp hrow
    have h2 : 1000 * (egM p α + 1) * (s + 1) * (p + 1) = SB := by simp only [SB]; ring
    rw [h2] at h
    exact h
  have hQB1 : 1 ≤ QA := by
    simp only [QA]
    have h : 0 < (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1) := by positivity
    omega
  have hsp1 : 1 ≤ (s + 1) * (p + 1) := by
    have h1 : 1 ≤ s + 1 := by omega
    have h2 : 1 ≤ p + 1 := by omega
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (s + 1) * (p + 1) := Nat.mul_le_mul h1 h2
  have h40mul : ∀ a : ℕ, a ≤ 40 → a ≤ 40 * (s + 1) * (p + 1) := by
    intro a ha
    have h2 : 40 * 1 ≤ 40 * ((s + 1) * (p + 1)) := Nat.mul_le_mul_left 40 hsp1
    have h3 : 40 * ((s + 1) * (p + 1)) = 40 * (s + 1) * (p + 1) := by ring
    rw [h3] at h2
    linarith
  have hszsigma40 : isz σ ≤ 40 * (s + 1) * (p + 1) :=
    h40mul _ (le_trans hszsigma (by norm_num))
  have hvsz40 : vsz (cvecVal v) ≤ 40 * (s + 1) * (p + 1) := by
    have ht := buQT_vsz_cvecVal (u := v) (M := p + 5) hvsz
    rw [hvlen] at ht
    nlinarith [ht, Nat.zero_le s, Nat.zero_le p]
  have haccsz40 : vsz (cvecVal acc) ≤ 40 * (s + 1) * (p + 1) := by
    have ht := buQT_vsz_cvecVal (u := acc) (M := p + 5) haccsz
    rw [hacclen] at ht
    nlinarith [ht, Nat.zero_le s, Nat.zero_le p]
  have hszZeq : vsz (cfxVal ((0 : ℤ), (0 : ℤ))) = 5 := by
    rw [Work.Fx.vsz_cfxVal]
    have h2 : isz ((0 : ℤ)) = 2 := by decide
    rw [h2]
  have hZ40 : vsz (cfxVal ((0 : ℤ), (0 : ℤ))) ≤ 40 * (s + 1) * (p + 1) := by
    have h := h40mul 5 (by norm_num)
    rw [hszZeq]
    exact h
  have hrep40 : vsz (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ))))) ≤ SB := by
    have heq : ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) =
        cvecVal (List.replicate s ((0 : ℤ), (0 : ℤ))) := by
      rw [cvecVal, List.map_replicate]
    rw [heq]
    exact hszall _ hszvr
  -- the seven-element window `[cfxVal 0, σ, v, acc, COLS, s, p]`
  have hW1 : ∀ x ∈ ([cfxVal ((0 : ℤ), (0 : ℤ)), .int σ, cvecVal v, cvecVal acc, buColsT p α s t,
      .int (s : ℤ), .int (p : ℤ)] : List Val), vsz x ≤ SB := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hszall _ hZ40
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszsigma40)
    · exact hszall _ hvsz40
    · exact hszall _ haccsz40
    · exact hcolsTSB
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszs)
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszp)
  -- the seven-element window `[ofList (replicate s (cfxVal 0)), σ, v, acc, COLS, s, p]`
  have hW2 : ∀ x ∈ ([ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), .int σ, cvecVal v,
      cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val), vsz x ≤ SB := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrep40
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszsigma40)
    · exact hszall _ hvsz40
    · exact hszall _ haccsz40
    · exact hcolsTSB
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszs)
    · exact hszall _ (by rw [Work.Fx.vsz_int]; exact hszp)
  -- step 1: push the zero value
  have hs1 : Pipe main (pushP (cfxVal (0, 0))) []
      [cfxVal ((0 : ℤ), (0 : ℤ))] (kpush * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1)) :=
    Pipe.pushVal hpush (cfxVal ((0 : ℤ), (0 : ℤ)))
  have hs1' : Pipe main (pushP (cfxVal (0, 0)))
      [.int σ, cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)]
      (cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc, buColsT p α s t,
        .int (s : ℤ), .int (p : ℤ)]) MPC := by
    refine Pipe.le (Pipe.appendTail _ hs1) ?_
    have h1 : vsz (cfxVal ((0 : ℤ), (0 : ℤ))) = 5 := hszZeq
    have h2 : kpush * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) ≤ KS * 6 := by
      rw [h1]; exact Nat.mul_le_mul hKpush (by omega)
    have h3 : KS * 6 ≤ KS * 100 * SB := by
      have : 6 ≤ 100 * SB := by omega
      calc KS * 6 ≤ KS * (100 * SB) := Nat.mul_le_mul_left _ this
        _ = KS * 100 * SB := by ring
    calc kpush * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) ≤ KS * 6 := h2
      _ ≤ KS * 100 * SB := h3
      _ = MPC := by simp only [MPC]
  -- step 2: pick the length s
  have hs2 : Pipe main (pickP 5)
      (cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc, buColsT p α s t,
        .int (s : ℤ), .int (p : ℤ)])
      (.int (s : ℤ) :: cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc,
        buColsT p α s t, .int (s : ℤ), .int (p : ℤ)]) MPC := by
    have hk : 5 < (cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc,
        buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).length := by simp
    have hv : (cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc, buColsT p α s t,
        .int (s : ℤ), .int (p : ℤ)] : List Val).getD 5 .nil = .int (s : ℤ) := by simp
    have hsz : Work.Fx.szl ((cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc,
        buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).take (5 + 1)) + 1 ≤ 8 * SB + 1 :=
      buQW_szl_succ_le hW1 (k := 5) (by omega)
    refine Pipe.le (Pipe.pickAt main hpick (k := 5) hk hv) ?_
    exact buQW_opc_le hKpick hSB1 (k := 5) (by omega) hsz
  -- step 3: replicate
  have hrepPipe : Pipe main repP [.int (s : ℤ), cfxVal ((0 : ℤ), (0 : ℤ))]
      [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ))))]
      (krep * ((s + 1) * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) + isz (s : ℤ) + 1)) := by
    intro rest2 vs2 hvs2 s0 R hR
    have hv2 : vs2 = .int (s : ℤ) :: cfxVal ((0 : ℤ), (0 : ℤ)) :: rest2 := by rw [hvs2]; rfl
    obtain ⟨out, s1, n1, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
      hrep main s (cfxVal ((0 : ℤ), (0 : ℤ))) vs2 ⟨rest2, hv2⟩ s0 R hR
    obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv2)
    refine ⟨out, s1, n1, ?_, hev, hn, hstk, hoth⟩
    show out = [ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ))))] ++ rest2
    rw [hout, h3]
    rfl
  have hs3 : Pipe main repP
      (.int (s : ℤ) :: cfxVal ((0 : ℤ), (0 : ℤ)) :: [.int σ, cvecVal v, cvecVal acc,
        buColsT p α s t, .int (s : ℤ), .int (p : ℤ)])
      (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ, cvecVal v,
        cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)]) MPC := by
    have hsSB : s + 1 ≤ SB := by
      simp only [SB]
      nlinarith [Nat.zero_le s, Nat.zero_le p, Nat.zero_le (egM p α)]
    have h2 : isz (s : ℤ) ≤ SB := hszall _ hszs
    have hcost : krep * ((s + 1) * (vsz (cfxVal ((0 : ℤ), (0 : ℤ))) + 1) + isz (s : ℤ) + 1)
        ≤ KS * 100 * SB := by
      rw [hszZeq]
      have h4 : krep * ((s + 1) * (5 + 1) + isz (s : ℤ) + 1) ≤ KS * ((s + 1) * 6 + SB + 1) := by
        refine Nat.mul_le_mul hKrep ?_
        omega
      have h5 : (s + 1) * 6 + SB + 1 ≤ 100 * SB := by omega
      calc krep * ((s + 1) * (5 + 1) + isz (s : ℤ) + 1) ≤ KS * ((s + 1) * 6 + SB + 1) := h4
        _ ≤ KS * (100 * SB) := Nat.mul_le_mul_left _ h5
        _ = KS * 100 * SB := by ring
    refine Pipe.le (Pipe.appendTail _ hrepPipe) ?_
    exact hcost
  -- step 4: roll the table to the top
  have hs4 : Pipe main (rollP 4)
      (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ, cvecVal v,
        cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)])
      (buColsT p α s t :: ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) ::
        [.int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)]) MPC := by
    have hk : 4 < (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ, cvecVal v,
        cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).length := by simp
    have hpost : (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ, cvecVal v,
        cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).getD 4 .nil ::
        (ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ, cvecVal v,
        cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).eraseIdx 4 =
        (buColsT p α s t :: ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) ::
        [.int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)]) := by simp
    have hsz : Work.Fx.szl ((ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: [.int σ,
        cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)] : List Val).take (4 + 1)) + 1
        ≤ 8 * SB + 1 := buQW_szl_succ_le hW2 (k := 4) (by omega)
    refine Pipe.le (Pipe.rollA main hroll (A := ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ))))
        :: [.int σ, cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)]) hk hpost) ?_
    exact buQW_opc_le hKroll hSB1 (k := 4) (by omega) hsz
  -- compose the four steps
  have hprepW : Pipe main (.seq (pushP (cfxVal (0, 0))) (.seq (pickP 5) (.seq repP (rollP 4))))
      [.int σ, cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ), .int (p : ℤ)]
      [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))), .int σ, cvecVal v,
        cvecVal acc, .int (s : ℤ), .int (p : ℤ)] (4 * MPC) := by
    have hchain := Pipe.comp hs1' (Pipe.comp hs2 (Pipe.comp hs3 hs4))
    refine Pipe.le hchain ?_
    have : MPC + (MPC + (MPC + MPC)) = 4 * MPC := by ring
    rw [this]
  -- ===== 4. the fold over the columns =====
  let LEL : ℕ := 100 * (s + 1) * (p + 1)
  let cCol : ℕ := kcol * (s + 1) * (Cm (kcol * p) + p + 1)
  let KF : ℕ := XS.length * (cCol + kfold * (LEL + 1)) + kfold
  let KPo : ℕ := KS * (s + 1) * (p + 1)
  have hLbnd : ∀ x ∈ XS, vsz x ≤ LEL := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨h, hh, rfl⟩
    exact buQW_col_vsz_le p α s t hα hp hrow hh
  have hElem : ∀ i st, i < XS.length → I i st → WordR main colP
      (fun vs => vs = XS.getD i .nil :: st) (fun _ out => I (i + 1) out) (fun _ => cCol) := by
    intro i st hi hIst
    obtain ⟨z, hst, hz, hzlen, hzsz⟩ := hIst
    have him : i < (egHs (egM p α)).length := by
      rw [hXSlen] at hi; rw [buQWhs_length]; exact hi
    have hidx : i < (buColsN (buWt p α s t) s (egM p α)).length := by
      rw [buColsN_length]
      have h := him
      rw [buQWhs_length] at h
      exact h
    have hh : (egHs (egM p α)).getD i 0 ∈ egHs (egM p α) := by
      rw [List.getD_eq_getElem _ _ him]; exact List.getElem_mem him
    have hhmem : (egHs (egM p α)).getD i 0 ∈ egHset (egM p α) := by
      rw [← (buQWhs (egM p α)).1, List.mem_toFinset]; exact hh
    have hwisz : ∀ y ∈ buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0), isz y ≤ p + 3 := by
      intro y hy
      obtain ⟨ℓ, rfl⟩ := List.mem_ofFn.mp hy
      exact buQT_buWt_isz_le p α s t hα hp hrow _ _ hhmem
    have hcolPipe : Pipe main colP
        [.cons (.int ((egHs (egM p α)).getD i 0))
            (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)),
          cvecVal z, .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)]
        [cvecVal (buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
            (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))),
          .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] cCol :=
      hcol p α s t hs hp main N Cm hmono hmb hKNcol ((egHs (egM p α)).getD i 0)
        (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)) hh rfl hwisz
        (buColL_length _ _ _) σ hσ v z acc hvlen hzlen hacclen hvsz hzsz haccsz
    have hXSget : XS.getD i .nil = Val.cons (.int ((egHs (egM p α)).getD i 0))
        (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)) := by
      rw [List.getD_eq_getElem _ _ hi]
      simp only [hXS, List.getElem_map]
      rw [List.getD_eq_getElem _ _ him]
      rfl
    have hz' : buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
        (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))
        = buPFold (buWt p α s t) s (egM p α) v (i + 1) := by
      rw [hz]
      exact (buPFold_succ (buWt p α s t) s (egM p α) v i hidx).symm
    have hz'len : (buPFold (buWt p α s t) s (egM p α) v (i + 1)).length = s :=
      buPFold_length (buWt p α s t) s (egM p α) v hvlen (i + 1) (by rw [buColsN_length]; omega)
    have hz'sz : ∀ y ∈ buPFold (buWt p α s t) s (egM p α) v (i + 1),
        isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8 := by
      intro y hy
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_iff_getElem.mp hy
      have h2 := him
      rw [buQWhs_length] at h2
      have h := buQW_fold_isz p α s t hp hrow B hB v hvlen hvin (i + 1)
        (by omega) ℓ (by rw [← hz'len]; exact hℓ)
      rwa [List.getD_eq_getElem _ _ hℓ] at h
    intro vs hvs
    have hvseq : vs = [Val.cons (.int ((egHs (egM p α)).getD i 0))
        (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)),
        cvecVal z, .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] ++ rest := by
      rw [hvs, hst, hXSget]
      rfl
    intro s0 R hR
    obtain ⟨out, s1, n1, hout1, hev, hn, hstk, hoth⟩ := hcolPipe rest vs hvseq s0 R hR
    have hout2 : out = cvecVal (buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
        (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))) :: .int σ :: cvecVal v ::
        cvecVal acc :: .int (s : ℤ) :: .int (p : ℤ) :: rest := by
      rw [hout1]
      rfl
    refine ⟨out, s1, n1, ?_, hev, hn, hstk, hoth⟩
    refine ⟨buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
      (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v)), hout2, ?_, ?_, ?_⟩
    · exact hz'
    · rw [hz']; exact hz'len
    · intro y hy
      rw [hz'] at hy
      exact hz'sz y hy
  have hFoldApp : WordR main (foldP colP)
      (fun vs => ∃ acc0, vs = ofList XS :: acc0 ∧ I 0 acc0)
      (fun _ out => I XS.length out)
      (fun _ => XS.length * (cCol + kfold * (LEL + 1)) + kfold) :=
    hfold main colP XS I cCol LEL hLbnd hElem
  -- ===== 5. the post word =====
  have hzFlen : zF.length = s := by
    rw [hzF]
    exact buPFold_length (buWt p α s t) s (egM p α) v hvlen (2 * egM p α) (by rw [buColsN_length])
  have hzFsz : ∀ y ∈ zF, isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8 := by
    intro y hy
    rw [hzF] at hy
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_iff_getElem.mp hy
    have h := buQW_fold_isz p α s t hp hrow B hB v hvlen hvin (2 * egM p α) (by omega) ℓ
      (by rw [← hzFlen]; exact hℓ)
    rwa [List.getD_eq_getElem _ _ hℓ] at h
  have hpostW : Pipe main postP
      [cvecVal zF, .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)]
      [cvecVal v', cvecVal acc'] KPo := by
    have h := hpost p s main hp σ hσ zF v acc hzFlen hzFsz hvlen hvsz haccsz hacclen
    refine Pipe.le h ?_
    exact Nat.mul_le_mul_right (p + 1) (Nat.mul_le_mul_right (s + 1) hKpost)
  -- ===== 6. composing the three phases =====
  have h12 : WordR main (.seq (.seq (pushP (cfxVal (0, 0))) (.seq (pickP 5) (.seq repP (rollP 4))))
        (foldP colP)) (fun vs => vs = [.int σ, cvecVal v, cvecVal acc, buColsT p α s t,
          .int (s : ℤ), .int (p : ℤ)] ++ rest)
      (fun _ out => ∃ mid, (mid = [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))),
          .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] ++ rest) ∧ I XS.length out)
      (fun _ => 4 * MPC + KF) :=
    KL.seq main _ (foldP colP) _ _ (fun _ => 4 * MPC) _ _ (fun _ => KF) (fun _ => KF)
      (hprepW rest) hFoldApp (by
        intro vs mid hvs hmid
        rw [hmid]
        refine ⟨⟨_, rfl, ?_⟩, le_rfl⟩
        refine ⟨List.replicate s ((0 : ℤ), (0 : ℤ)), ?_, ?_, ?_, ?_⟩
        · have hz : ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) =
              cvecVal (List.replicate s ((0 : ℤ), (0 : ℤ))) := by
            rw [cvecVal, List.map_replicate]
          first
          | rw [hz] <;> rfl
          | simp only [hz, List.cons_append, List.nil_append]
        · rw [buPFold_zero]
        · rw [List.length_replicate]
        · intro y hy
          have hy' : y = ((0 : ℤ), (0 : ℤ)) := List.eq_of_mem_replicate hy
          rw [hy']
          have h0 : isz ((0 : ℤ)) ≤ 2 * p + 8 := by simp only [isz, Int.natAbs_zero, Nat.size_zero]; omega
          exact ⟨h0, h0⟩)
  have hall : WordR main (.seq (.seq (.seq (pushP (cfxVal (0, 0))) (.seq (pickP 5)
        (.seq repP (rollP 4)))) (foldP colP)) postP)
      (fun vs => vs = [.int σ, cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ),
        .int (p : ℤ)] ++ rest)
      (fun _ out => ∃ mid, (∃ mid2, (mid2 = [buColsT p α s t, ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))),
          .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] ++ rest) ∧ I XS.length mid) ∧
        out = [cvecVal v', cvecVal acc'] ++ rest)
      (fun _ => 4 * MPC + KF + KPo) :=
    KL.seq main _ postP _ _ (fun _ => 4 * MPC + KF) _ _ (fun _ => KPo) (fun _ => KPo)
      h12 (hpostW rest) (by
        intro vs mid hvs hmid
        obtain ⟨mid2, hmid2, hI⟩ := hmid
        obtain ⟨z, hst, hz, hzlen, hzsz⟩ := hI
        have hzFeq : z = zF := by
          rw [hz, hzF, hXSlen]
        refine ⟨?_, le_rfl⟩
        rw [hst, hzFeq]
        rfl)
  -- ===== 7. the result =====
  have hvsA : vs = [.int σ, cvecVal v, cvecVal acc, buColsT p α s t, .int (s : ℤ),
      .int (p : ℤ)] ++ rest := by rw [hvs]; rfl
  intro st R hR
  obtain ⟨out, s', n, hP, hev, hn, hstk, hoth⟩ := hall vs hvsA st R hR
  obtain ⟨mid, ⟨mid2, hmid2, hI⟩, hout⟩ := hP
  obtain ⟨z, hst, hz, hzlen, hzsz⟩ := hI
  -- the disc bounds
  have hvin'' : ∀ y ∈ v, ‖gz y‖ ≤ (B : ℝ) := hvin'
  have hv'len : v'.length = s := by
    rw [hv', hzF, buTdivV_length]
    exact buPFold_length (buWt p α s t) s (egM p α) v hvlen (2 * egM p α) (by rw [buColsN_length])
  have hv'disc : buInV (B / 2 + 34 * egM p α + 4) v' := by
    rw [buInV_iff]
    intro y hy
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_iff_getElem.mp hy
    have hℓs : ℓ < s := by rw [← hv'len]; exact hℓ
    have h1 : ‖gz (v'.getD ℓ (0, 0))‖ ≤ ((buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α))
        * (B : ℝ)) / (2 : ℝ) ^ p + Real.sqrt 2 := by
      rw [← hbufold]
      exact buRoundL_gz_le (buWt p α s t) p s (egM p α) B v hvlen hvin'' ℓ hℓs
    have h2 : buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α)
        ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) := by
      rw [buRowS_full]; exact hrow (ℓ : ℤ)
    have hBc : (B : ℝ) ≤ (2 : ℝ) ^ (p + 2) := by
      have h := hB
      have h2' : ((2 : ℕ) ^ (p + 2) : ℝ) = (2 : ℝ) ^ (p + 2) := by push_cast; ring
      calc (B : ℝ) ≤ ((2 : ℕ) ^ (p + 2) : ℝ) := by exact_mod_cast h
        _ = (2 : ℝ) ^ (p + 2) := h2'
    have h8m : 8 * (egM p α : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
      have h := buQT_eight_egM_le p α hp
      exact_mod_cast h
    have hp1 : 1 ≤ p := by omega
    have h2p : (2 : ℝ) ^ p = 2 * (2 : ℝ) ^ (p - 1) := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hmain : (buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α) * (B : ℝ)) / (2 : ℝ) ^ p
        + Real.sqrt 2 ≤ ((B / 2 + 34 * egM p α + 4 : ℕ) : ℝ) := by
      have h4 : (buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α) * (B : ℝ)) / (2 : ℝ) ^ p
          ≤ (B : ℝ) / 2 + 32 * (egM p α : ℝ) := by
        have h5 : ((2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)) * (B : ℝ) / (2 : ℝ) ^ p
            = (B : ℝ) / 2 + 8 * (egM p α : ℝ) * (B : ℝ) / (2 : ℝ) ^ p := by
          field_simp
        have h6 : 8 * (egM p α : ℝ) * (B : ℝ) / (2 : ℝ) ^ p ≤ 32 * (egM p α : ℝ) := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
          have hB2' : (B : ℝ) ≤ 4 * (2 : ℝ) ^ p := by
            have hp2 : (2 : ℝ) ^ (p + 2) = 4 * (2 : ℝ) ^ p := by rw [pow_add]; ring
            calc (B : ℝ) ≤ (2 : ℝ) ^ (p + 2) := hBc
              _ = 4 * (2 : ℝ) ^ p := hp2
          calc 8 * (egM p α : ℝ) * (B : ℝ) ≤ 8 * (egM p α : ℝ) * (4 * (2 : ℝ) ^ p) :=
                mul_le_mul_of_nonneg_left hB2' (by positivity)
            _ = 32 * (egM p α : ℝ) * (2 : ℝ) ^ p := by ring
        have h7 : buRowS (buWt p α s t) (egM p α) (ℓ : ℤ) (2 * egM p α) * (B : ℝ) / (2 : ℝ) ^ p
            ≤ ((2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ)) * (B : ℝ) / (2 : ℝ) ^ p := by
          have hBnn : (0 : ℝ) ≤ (B : ℝ) := by positivity
          have h2pnn : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hBnn) (le_of_lt h2pnn)
        rw [h5] at h7
        linarith
      have h8 : ((B / 2 + 34 * egM p α + 4 : ℕ) : ℝ)
          = ((B / 2 : ℕ) : ℝ) + 34 * (egM p α : ℝ) + 4 := by push_cast; ring
      have h9 : (B : ℝ) / 2 ≤ ((B / 2 : ℕ) : ℝ) + 1 := by
        have hB' : B < 2 * (B / 2) + 2 := by
          have h := Nat.div_add_mod B 2
          omega
        have hB'' : (B : ℝ) < 2 * ((B / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hB'
        linarith
      rw [h8]
      have hA : (0 : ℝ) ≤ (egM p α : ℝ) := Nat.cast_nonneg _
      linarith [h4, h9, hsqrt, hA]
    rw [List.getD_eq_getElem _ _ hℓ] at h1
    exact le_trans h1 hmain
  have hacc'disc : buInV (B2 + B / 2 + 34 * egM p α + 5) acc' := by
    rw [hacc']
    have hle : B2 + (B / 2 + 34 * egM p α + 4) ≤ B2 + B / 2 + 34 * egM p α + 5 := by
      have h1 : (B / 2 + 34 * egM p α) + 4 ≤ (B / 2 + 34 * egM p α) + 5 :=
        Nat.add_le_add_left (by norm_num : 4 ≤ 5) _
      calc B2 + (B / 2 + 34 * egM p α + 4) = B2 + ((B / 2 + 34 * egM p α) + 4) := by ring
        _ ≤ B2 + ((B / 2 + 34 * egM p α) + 5) := Nat.add_le_add_left h1 B2
        _ = B2 + B / 2 + 34 * egM p α + 5 := by ring
    refine buQT_buInV_mono (B := B2 + (B / 2 + 34 * egM p α + 4))
      (B' := B2 + B / 2 + 34 * egM p α + 5) hle ?_
    exact buInV_buAddV haccin (buInV_buSMulV hσ hv'disc)
  have hacc'len : acc'.length = s := by
    rw [hacc']
    have h1 : (buAddV acc (buSMulV σ v')).length = min acc.length (buSMulV σ v').length := buAddV_length _ _
    rw [h1, buSMulV, List.length_map, hv'len, hacclen]
    omega
  -- ===== 8. the cost bound =====
  have hcost : 4 * MPC + KF + KPo ≤ KCST := by
    -- (1) the middle phase
    have hMPC : 4 * MPC ≤ 400000 * (KS * QA) := by
      have hSBQA : SB ≤ 1000 * QA := by
        simp only [SB, QA]
        exact Nat.mul_le_mul_left 1000 (Nat.mul_le_mul_left ((egM p α + 1) * (s + 1)) (by omega))
      have h1 : MPC ≤ KS * 100 * (1000 * QA) := by
        simp only [MPC]
        exact Nat.mul_le_mul le_rfl hSBQA
      have h2 : KS * 100 * (1000 * QA) ≤ 100000 * (KS * QA) := by
        have he : KS * 100 * (1000 * QA) = 100000 * (KS * QA) := by ring
        rw [he]
      have h3 : MPC ≤ 100000 * (KS * QA) := by exact le_trans h1 h2
      have h4 : 4 * MPC ≤ 4 * (100000 * (KS * QA)) := by exact Nat.mul_le_mul_left 4 h3
      have h5 : 4 * (100000 * (KS * QA)) = 400000 * (KS * QA) := by ring
      rw [h5] at h4
      exact h4
    -- (2) the fold
    have hKF : KF ≤ 300 * (KS * QA) + KS := by
      have hX : XS.length ≤ 2 * (egM p α + 1) := by rw [hXSlen]; omega
      have hcmcol : Cm (kcol * p) ≤ Cm (KC * p) := by
        exact hmono (Nat.mul_le_mul_right p (by simp only [KC]; nlinarith))
      have hcCol : cCol ≤ KS * (s + 1) * (Cm (KC * p) + p + 1) := by
        simp only [cCol]
        exact Nat.mul_le_mul (Nat.mul_le_mul hKcol le_rfl) (by omega)
      have hLEL : kfold * (LEL + 1) ≤ KS * (101 * ((s + 1) * (p + 1))) := by
        have h7 : 100 * (s + 1) * (p + 1) + 1 ≤ 101 * ((s + 1) * (p + 1)) := by
          have hX' : 100 * (s + 1) * (p + 1) = 100 * ((s + 1) * (p + 1)) := by ring
          have hX'' : 101 * ((s + 1) * (p + 1))
              = 100 * ((s + 1) * (p + 1)) + (s + 1) * (p + 1) := by ring
          rw [hX', hX'']
          exact Nat.add_le_add_left hsp1 (100 * ((s + 1) * (p + 1)))
        have he : LEL + 1 = 100 * (s + 1) * (p + 1) + 1 := by simp only [LEL]
        rw [he]
        calc kfold * (100 * (s + 1) * (p + 1) + 1) ≤ KS * (100 * (s + 1) * (p + 1) + 1) :=
              Nat.mul_le_mul hKfold le_rfl
          _ ≤ KS * (101 * ((s + 1) * (p + 1))) := Nat.mul_le_mul_left KS h7
      have hprod : XS.length * (cCol + kfold * (LEL + 1))
          ≤ (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (p + 1)))) := by
        exact Nat.mul_le_mul hX (Nat.add_le_add hcCol hLEL)
      have hKF1 : KF ≤ (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (p + 1)))) + KS := by
        have he : KF = XS.length * (cCol + kfold * (LEL + 1)) + kfold := by simp only [KF]
        rw [he]
        exact Nat.add_le_add hprod hKfold
      have hKF2 : (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (p + 1)))) + KS ≤ 300 * (KS * QA) + KS := by
        have hPleC : (s + 1) * (p + 1) ≤ (s + 1) * (Cm (KC * p) + p + 1) := by
          exact Nat.mul_le_mul_left (s + 1) (by omega)
        have hIn : KS * (s + 1) * (Cm (KC * p) + p + 1) + KS * (101 * ((s + 1) * (p + 1)))
            ≤ KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (Cm (KC * p) + p + 1))) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left KS (Nat.mul_le_mul_left 101 hPleC)) _
        have hMul : (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (p + 1))))
            ≤ (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (Cm (KC * p) + p + 1)))) := by
          exact Nat.mul_le_mul_left (2 * (egM p α + 1)) hIn
        have hEq : (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (Cm (KC * p) + p + 1)))) = 204 * (KS * QA) := by
          simp only [QA]; ring
        have h204 : 204 * (KS * QA) ≤ 300 * (KS * QA) := by
          exact Nat.mul_le_mul_right (KS * QA) (by norm_num)
        have hstep1 : (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (p + 1)))) + KS
            ≤ (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (Cm (KC * p) + p + 1)))) + KS := by
          exact Nat.add_le_add_right hMul KS
        have hstep2 : (2 * (egM p α + 1)) * (KS * (s + 1) * (Cm (KC * p) + p + 1)
              + KS * (101 * ((s + 1) * (Cm (KC * p) + p + 1)))) + KS
            = 204 * (KS * QA) + KS := by rw [hEq]
        have hstep3 : 204 * (KS * QA) + KS ≤ 300 * (KS * QA) + KS := by
          exact Nat.add_le_add_right h204 KS
        exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
      exact le_trans hKF1 hKF2
    -- (3) the post phase
    have hKPo : KPo ≤ KS * QA := by
      have hKPo1 : KPo ≤ KS * QA := by
        simp only [KPo, QA]
        have h11 : (s + 1) * (p + 1) ≤ (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1) := by
          have h1 : (s + 1) * (p + 1) ≤ (s + 1) * (Cm (KC * p) + p + 1) := by
            exact Nat.mul_le_mul_left (s + 1) (by omega)
          have h2 : (s + 1) * (Cm (KC * p) + p + 1)
              ≤ (egM p α + 1) * ((s + 1) * (Cm (KC * p) + p + 1)) := by
            exact Nat.le_mul_of_pos_left _ (by omega)
          have h3 : (egM p α + 1) * ((s + 1) * (Cm (KC * p) + p + 1))
              = (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1) := by ring
          calc (s + 1) * (p + 1) ≤ (s + 1) * (Cm (KC * p) + p + 1) := h1
            _ ≤ (egM p α + 1) * ((s + 1) * (Cm (KC * p) + p + 1)) := h2
            _ = (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1) := h3
        have heq : KS * (s + 1) * (p + 1) = KS * ((s + 1) * (p + 1)) := by ring
        rw [heq]
        exact Nat.mul_le_mul_left KS h11
      exact hKPo1
    -- (4) assemble
    have hsum : 4 * MPC + KF + KPo
        ≤ 400000 * (KS * QA) + (300 * (KS * QA) + KS) + KS * QA := by
      exact Nat.add_le_add (Nat.add_le_add hMPC hKF) hKPo
    have hsimp : 400000 * (KS * QA) + (300 * (KS * QA) + KS) + KS * QA
        ≤ 1000000 * (KS * QA) := by
      have hT : 400000 * (KS * QA) + (300 * (KS * QA) + KS) + KS * QA
          = 400301 * (KS * QA) + KS := by ring
      rw [hT]
      have hKSQA : KS ≤ KS * QA := by exact Nat.le_mul_of_pos_right KS (by omega)
      calc 400301 * (KS * QA) + KS ≤ 400301 * (KS * QA) + KS * QA :=
            Nat.add_le_add_left hKSQA _
        _ = 400302 * (KS * QA) := by ring
        _ ≤ 1000000 * (KS * QA) := Nat.mul_le_mul_right (KS * QA) (by norm_num)
    have hstep : 1000000 * (KS * QA) ≤ KC * QA := by
      have he : KC * QA = 1000000 * (KS * QA) := by
        show (1000000 * KS) * ((egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1))
          = 1000000 * (KS * ((egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1)))
        ring
      rw [he]
    have hKCbig : 4 * MPC + KF + KPo ≤ KC * QA := by
      exact le_trans hsum (le_trans hsimp hstep)
    have h13 : KC * QA = KCST := by
      show (1000000 * KS) * ((egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1))
        = (1000000 * KS) * (egM p α + 1) * (s + 1) * (Cm (KC * p) + p + 1)
      ring
    exact le_trans hKCbig (le_of_eq h13)
  refine ⟨out, s', n, ?_, hev, ?_, hstk, hoth⟩
  · refine ⟨σ, v, acc, rest, v', acc', hσ, hvs, ?_, hbufold.symm, rfl, hv'len, hacc'len,
      hv'disc, hacc'disc⟩
    rw [hout]; rfl
  · exact hn.trans hcost

end Work.Resample
