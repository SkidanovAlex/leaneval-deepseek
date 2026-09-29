import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.yMulListOK
import Submission.Work.SynFFT.pairTwiddle
import Submission.Work.SynFFT.pairErr
import Submission.Work.SynFFT.zipCvec
import Submission.Work.SynFFT.paramCalc

/-!
# `Work.SynFFT.HasPair` — the butterfly word

The butterfly of the slice-local synthetic FFT (`kit2.HasPair`): given two coefficient
vectors `cvecVal w₁`, `cvecVal w₂` (approximating `u₁`, `u₂` with error `≤ e` in the
`2^p`-scaled sense) and the twiddle data `j`, `sh`, `sgn`, `r`, `p`, produce vectors
`v₁ ≈ (u₁+u₂)/2` and `v₂ ≈ y^{sgn·j·2^sh}·(u₁-u₂)/2`, both with error `≤ e+1`, at cost
`O(r·p)`.

## The program

1. `paramCalc` computes the two parameters of the signed cyclic shift
   `yMulS` (the shift `s` and the sign `sg`) from `j`, `sh`, `sgn`, `r` and pushes them,
   together with copies of `r` and `p`, on top of the input state:
   `W₁ :: W₂ :: j :: sh :: sgn :: r :: p :: rest  ↦  s :: sg :: r :: p :: W₁ :: W₂ :: …`.
2. `pick 5 ;;; pick 5` copies `W₂` and `W₁` to the top, so that `zipCvec` (delegated)
   can apply the pointwise half-difference word `subHalf` to the two vectors, producing
   the difference vector `WD` above the four parameters.
3. `HasYMulShift` applied to `WD` with the parameters `s`, `sg`, `r`, `p` gives
   `V₂ = yMulS r s sg WD = yMulList r (sgn·j·2^sh) WD`, whose fixed-point value is
   `yMul r (sgn·j·2^sh)` applied to the (approximate) half-difference — the twiddle of
   the butterfly; `pairTwiddle` (delegated) supplies the identification of `s`, `sg`.
4. The four parameters are thrown away again (`roll 1 ;;; drop` four times).
5. `zipCvec` with the pointwise half-sum word `addHalf` applies to the *original*
   `W₁`, `W₂` (still on the stack), producing `V₁` above `V₂`.

The numerical part is `pairErr` (delegated): the two pointwise passes contribute `< 1`
each, the input errors contribute `e`, and `yMul` is a signed coordinate permutation
(`yMulFacts`), so it does not amplify the error.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000000
set_option maxRecDepth 1000000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## Sizes of `.int` values -/

theorem vsz_int_le_of_le' {n m : ℕ} (h : n ≤ m) : vsz (.int (n : ℤ)) ≤ 3 * (m + 1) := by
  rw [MrgKit.vsz_int']
  simp only [isz]
  rw [show (n : ℤ).natAbs = n by simp]
  have h1 : n.size ≤ m.size := Nat.size_le_size h
  have h2 : m.size ≤ m := (Nat.size_le).mpr Nat.lt_two_pow_self
  omega

theorem vsz_int_sign_le (z : ℤ) (h : z = 1 ∨ z = -1) : vsz (.int z) ≤ 3 := by
  rcases h with h | h <;> rw [h] <;> decide

/-! ## The two pointwise half-words in constant-cost form -/

/-- `(u+v)/2` with error `< 1`: `FxLib.addHalf` with the input values fixed (so that the
cost is the constant `K·(2p+14)`, all a `zipWith` can rely on). -/
theorem addHalfWord (hf : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (u v : ℤ × ℤ) (rest : List HvdH.Val),
      HvdH.inDisc p u → HvdH.inDisc p v →
      HvdH.WordR main q (fun vs => vs = HvdH.cfxVal u :: HvdH.cfxVal v :: rest)
        (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
          (2 : ℝ) ^ p * ‖HvdH.fxC p w - (HvdH.fxC p u + HvdH.fxC p v) / 2‖ < 1)
        (fun _ => K * (2 * (2 * p + 7))) := by
  obtain ⟨q, K, hq⟩ := hf.addHalf
  refine ⟨q, K, ?_⟩
  intro main p u v rest hu hv
  refine MrgKit.WordR_weaken (hq main p) ?_ ?_ ?_
  · rintro vs hvs
    exact ⟨u, v, rest, hvs, hu, hv⟩
  · rintro vs out hvs hpost
    obtain ⟨u', v', r', w, hvs', hout, hw, herr⟩ := hpost
    have hEq : HvdH.cfxVal u :: HvdH.cfxVal v :: rest = HvdH.cfxVal u' :: HvdH.cfxVal v' :: r' :=
      hvs.symm.trans hvs'
    simp only [HvdH.cfxVal, List.cons.injEq, HvdH.Val.cons.injEq, HvdH.Val.int.injEq,
      Prod.mk.injEq] at hEq
    obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩, hr⟩ := hEq
    have hu' : u' = u := Prod.ext hu1.symm hu2.symm
    have hv' : v' = v := Prod.ext hv1.symm hv2.symm
    rw [← hr] at hout
    rw [hu', hv'] at herr
    exact ⟨w, hout, hw, herr⟩
  · intro vs hvs
    rw [hvs]
    have h1 : vsz (HvdH.cfxVal u) ≤ 2 * p + 7 := MrgKit.vsz_cfxVal_le p u hu
    have h2 : vsz (HvdH.cfxVal v) ≤ 2 * p + 7 := MrgKit.vsz_cfxVal_le p v hv
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    refine Nat.mul_le_mul_left K ?_
    omega

/-- `(u-v)/2` with error `< 1`: `FxLib.subHalf` in constant-cost form. -/
theorem subHalfWord (hf : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (u v : ℤ × ℤ) (rest : List HvdH.Val),
      HvdH.inDisc p u → HvdH.inDisc p v →
      HvdH.WordR main q (fun vs => vs = HvdH.cfxVal u :: HvdH.cfxVal v :: rest)
        (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
          (2 : ℝ) ^ p * ‖HvdH.fxC p w - (HvdH.fxC p u - HvdH.fxC p v) / 2‖ < 1)
        (fun _ => K * (2 * (2 * p + 7))) := by
  obtain ⟨q, K, hq⟩ := hf.subHalf
  refine ⟨q, K, ?_⟩
  intro main p u v rest hu hv
  refine MrgKit.WordR_weaken (hq main p) ?_ ?_ ?_
  · rintro vs hvs
    exact ⟨u, v, rest, hvs, hu, hv⟩
  · rintro vs out hvs hpost
    obtain ⟨u', v', r', w, hvs', hout, hw, herr⟩ := hpost
    have hEq : HvdH.cfxVal u :: HvdH.cfxVal v :: rest = HvdH.cfxVal u' :: HvdH.cfxVal v' :: r' :=
      hvs.symm.trans hvs'
    simp only [HvdH.cfxVal, List.cons.injEq, HvdH.Val.cons.injEq, HvdH.Val.int.injEq,
      Prod.mk.injEq] at hEq
    obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩, hr⟩ := hEq
    have hu' : u' = u := Prod.ext hu1.symm hu2.symm
    have hv' : v' = v := Prod.ext hv1.symm hv2.symm
    rw [← hr] at hout
    rw [hu', hv'] at herr
    exact ⟨w, hout, hw, herr⟩
  · intro vs hvs
    rw [hvs]
    have h1 : vsz (HvdH.cfxVal u) ≤ 2 * p + 7 := MrgKit.vsz_cfxVal_le p u hu
    have h2 : vsz (HvdH.cfxVal v) ≤ 2 * p + 7 := MrgKit.vsz_cfxVal_le p v hv
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    refine Nat.mul_le_mul_left K ?_
    omega

/-! ## Cost helpers -/

theorem pickRollCost_le {Kx Kp MB Cs : ℕ} {A : List Val} {k : ℕ} (hk : k ≤ 5) (hMB1 : 1 ≤ MB)
    (hsmall : ∀ i, i < k + 1 → vsz (A.getD i Val.nil) ≤ MB)
    (hK : Kp ≤ Kx) (hCs : 100 * Kx * (MB + 1) ≤ Cs) :
    Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ Cs := by
  have h1 : ((A.take (k + 1)).map vsz).sum ≤ (k + 1) * MB :=
    MrgKit.vsz_take_sum_le_getD A (k + 1) MB hsmall
  have hk6 : k + 1 ≤ 6 := by omega
  have h2 : (k + 1) * MB + 1 ≤ 6 * MB + 1 := by nlinarith
  calc Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1)
      ≤ Kx * (k + 1) * ((k + 1) * MB + 1) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul hK le_rfl) ?_
        omega
    _ ≤ Kx * 6 * (6 * MB + 1) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk6) ?_
        omega
    _ ≤ 100 * Kx * (MB + 1) := by
        rw [show Kx * 6 * (6 * MB + 1) = Kx * (6 * (6 * MB + 1)) by ring,
          show 100 * Kx * (MB + 1) = Kx * (100 * (MB + 1)) by ring]
        exact Nat.mul_le_mul_left _ (by omega)
    _ ≤ Cs := hCs

theorem dropCost_le {Kx Kdr MB Cs : ℕ} {v : Val} (hv : vsz v ≤ MB)
    (hK : Kdr ≤ Kx) (hCs : 100 * Kx * (MB + 1) ≤ Cs) : Kdr * (vsz v + 1) ≤ Cs := by
  calc Kdr * (vsz v + 1) ≤ Kx * (MB + 1) := by
        refine Nat.mul_le_mul hK ?_
        omega
    _ ≤ 100 * Kx * (MB + 1) := by
        refine Nat.mul_le_mul_right (MB + 1) ?_
        omega
    _ ≤ Cs := hCs

/-! ## Composition with an existential intermediate state -/

theorem WordR_seqD {main p q : Cmd} {A B : List Val} {Bpost : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => Bpost out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => Bpost out) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨mid, s2, n1, hQ, hev1, hn1, hstk1, hoth1⟩ := h1 A rfl s R hR
  rw [hQ] at hstk1
  obtain ⟨out, s3, n2, hpost, hev2, hn2, hstk2, hoth2⟩ := h2 B rfl s2 R hstk1
  exact ⟨out, s3, n1 + n2, hpost, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem WordR_seqE_xhasPair {main p q : Cmd} {A : List Val} {Q : List Val → List Val → Prop}
    {Bpost : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) Q (fun _ => c1))
    (h2 : ∀ mid, Q A mid → WordR main q (fun vs => vs = mid) (fun _ out => Bpost out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => Bpost out) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨mid, s2, n1, hQ, hev1, hn1, hstk1, hoth1⟩ := h1 A rfl s R hR
  obtain ⟨out, s3, n2, hpost, hev2, hn2, hstk2, hoth2⟩ := h2 mid hQ mid rfl s2 R hstk1
  exact ⟨out, s3, n1 + n2, hpost, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

/-! ## The butterfly word -/

theorem hasPair (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) (hf : HvdH.FxLib) (hy : Work.SynFFT.HasYMulShift) (htw : Work.SynFFT.YMulTwiddleProp) : Work.SynFFT.HasPair := by
  unfold HasPair
  obtain ⟨pw, Kc, hpw⟩ := paramCalc hk hi
  obtain ⟨zipP, Kz, hzip⟩ := zipCvec hk
  obtain ⟨ymProg, Kym, hym⟩ := hy
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨qa, Ka, hqa⟩ := addHalfWord hf
  obtain ⟨qs, Ks, hqs⟩ := subHalfWord hf
  set Kx : ℕ := 1000000 * (Kc + Kz + Kym + Kp + Kr + Kdr + Ka + Ks + 1) with hKx
  have hKc : Kc ≤ Kx := by rw [hKx]; omega
  have hKz : Kz ≤ Kx := by rw [hKx]; omega
  have hKym : Kym ≤ Kx := by rw [hKx]; omega
  have hKp : Kp ≤ Kx := by rw [hKx]; omega
  have hKr : Kr ≤ Kx := by rw [hKx]; omega
  have hKdr : Kdr ≤ Kx := by rw [hKx]; omega
  have hKa : Ka ≤ Kx := by rw [hKx]; omega
  have hKs : Ks ≤ Kx := by rw [hKx]; omega
  refine ⟨((pw ;;; pickP 5 ;;; pickP 5) ;;; zipP qs) ;;; (ymProg ;;; (rollP 1 ;;; kdrP ;;;
      rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; rollP 2 ;;;
      zipP qa)), 1000000 * Kx, ?_⟩
  intro main p r j sh sgn w₁ w₂ rest u₁ u₂ e hr hsgn ht hsh hp hw1 hw2 hd1 hd2 he1 he2
  -- ## abbreviations
  set tZ : ℤ := ((j * 2 ^ sh : ℕ) : ℤ) with htZ
  set btZ : ℤ := (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0) with hbtZ
  set bZ : ℤ := max sgn 0 with hbZ
  set sC : ℤ := btZ * (tZ + bZ * ((r : ℤ) - 2 * tZ)) with hsC
  set sgC : ℤ := 1 - 2 * (bZ * btZ) with hsgC
  set sNat : ℕ := if sgn = 1 then (if j * 2 ^ sh = 0 then 0 else r - j * 2 ^ sh) else j * 2 ^ sh
    with hsNat
  set sgReq : ℤ := if sgn = 1 ∧ j * 2 ^ sh ≠ 0 then (-1 : ℤ) else 1 with hsgReq
  set W1 : Val := cvecVal w₁ with hW1
  set W2 : Val := cvecVal w₂ with hW2
  set Jv : Val := .int (j : ℤ) with hJv
  set SHv : Val := .int (sh : ℤ) with hSHv
  set SGv : Val := .int sgn with hSGv
  set Rv : Val := .int (r : ℤ) with hRv
  set Pv : Val := .int (p : ℤ) with hPv
  set MB : ℕ := 20 * ((r + 1) * (p + 1)) with hMB
  set Cs : ℕ := 100 * Kx * (MB + 1) with hCs
  -- ## the twiddle parameters
  have hPT := pairTwiddle htw r j sh sgn w₁ hr hsgn ht hw1
  have hsNatle : sNat ≤ r := by rw [hsNat]; exact hPT.1
  have hsCeq : sC = ((sNat : ℕ) : ℤ) := by
    rw [hsC, htZ, hbtZ, hbZ, hsNat]; exact hPT.2.1
  have hsgCeq : sgC = sgReq := by
    rw [hsgC, hbtZ, hbZ, hsgReq]; exact hPT.2.2.1
  have hsgC1 : sgC = 1 ∨ sgC = -1 := by
    rw [hsgCeq, hsgReq]
    by_cases h : sgn = 1 ∧ j * 2 ^ sh ≠ 0
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl
  have htZnn : 0 ≤ tZ := by rw [htZ]; positivity
  have htZlt : tZ < (r : ℤ) := by rw [htZ]; exact_mod_cast ht
  have hEabs : |sgn * tZ| ≤ (r : ℤ) := by
    rcases hsgn with h | h <;> rw [h] <;> simp only [one_mul, neg_one_mul, abs_neg,
      abs_of_nonneg htZnn] <;> linarith
  -- ## sizes (all in raw form, so that they can be matched by `fin_cases`)
  have hMB1 : 1 ≤ MB := by rw [hMB]; nlinarith
  have hW1sz : vsz (cvecVal w₁) ≤ MB := by
    rw [hMB]
    have h := MrgKit.vsz_cvecVal_le p r w₁ hw1 hd1
    nlinarith
  have hW2sz : vsz (cvecVal w₂) ≤ MB := by
    rw [hMB]
    have h := MrgKit.vsz_cvecVal_le p r w₂ hw2 hd2
    nlinarith
  have hjle : j ≤ r := le_of_lt (by
    have h1 : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
    calc j = j * 1 := (Nat.mul_one j).symm
      _ ≤ j * 2 ^ sh := Nat.mul_le_mul_left j h1
      _ < r := ht)
  have hJsz : vsz (.int (j : ℤ)) ≤ MB := by
    rw [hMB]
    have h := vsz_int_le_of_le' hjle
    nlinarith
  have hSHsz : vsz (.int (sh : ℤ)) ≤ MB := by
    rw [hMB]
    have h1 : sh ≤ 2 * r := le_trans (le_of_lt Nat.lt_two_pow_self) hsh
    have h := vsz_int_le_of_le' h1
    nlinarith
  have hSGsz : vsz (.int sgn) ≤ MB := by
    rw [hMB]
    have h := vsz_int_sign_le sgn hsgn
    nlinarith
  have hRvsz : vsz (.int (r : ℤ)) ≤ MB := by
    rw [hMB]
    have h := vsz_int_le_of_le' (le_refl r)
    nlinarith
  have hPvsz : vsz (.int (p : ℤ)) ≤ MB := by
    rw [hMB]
    have h := vsz_int_le_of_le' (le_refl p)
    nlinarith
  have hS1sz : vsz (.int sC) ≤ MB := by
    rw [hsCeq, hMB]
    have h := vsz_int_le_of_le' hsNatle
    nlinarith
  have hS2sz : vsz (.int sgC) ≤ MB := by
    rw [hMB]
    have h := vsz_int_sign_le sgC hsgC1
    nlinarith
  -- ## the twiddle identification for the y-multiplication step
  have htw4 : ∀ wd : List (ℤ × ℤ), wd.length = r →
      yMulS r sNat sgC wd = yMulList r (sgn * tZ) wd := by
    intro wd hwdlen
    have h := (pairTwiddle htw r j sh sgn wd hr hsgn ht hwdlen).2.2.2
    rw [hsNat, hsgC, hbZ, hbtZ, htZ]
    exact h
  -- ## the error predicates
  set ErrSub : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → Prop :=
    fun u v w => (2 : ℝ) ^ p * ‖fxC p w - (fxC p u - fxC p v) / 2‖ < 1 with hErrSub
  set ErrAdd : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → Prop :=
    fun u v w => (2 : ℝ) ^ p * ‖fxC p w - (fxC p u + fxC p v) / 2‖ < 1 with hErrAdd
  -- ## the final post
  set FPost : List (ℤ × ℤ) → List (ℤ × ℤ) → Prop := fun v₁ v₂ =>
      v₁.length = r ∧ v₂.length = r ∧ (∀ z ∈ v₁, inDisc p z) ∧ (∀ z ∈ v₂, inDisc p z) ∧
      (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₁.getD (c : ℕ) (0, 0)) - (u₁ c + u₂ c) / 2‖ ≤ e + 1) ∧
      (∀ c : Fin r, (2 : ℝ) ^ p * ‖fxC p (v₂.getD (c : ℕ) (0, 0)) -
        yMul r (sgn * tZ) (fun c' => (u₁ c' - u₂ c') / 2) c‖ ≤ e + 1) with hFPost
  set TailPost : List Val → Prop := fun out => ∃ v₁ v₂ : List (ℤ × ℤ),
      out = cvecVal v₁ :: cvecVal v₂ :: Jv :: SHv :: SGv :: Rv :: Pv :: rest ∧
      FPost v₁ v₂ with hTailPost
  -- ## the states
  -- ## the states
  set A0 : List Val := W1 :: W2 :: Jv :: SHv :: SGv :: Rv :: Pv :: rest with hA0
  set C0 : List Val := .int sC :: .int sgC :: Rv :: Pv :: A0 with hC0
  set C1 : List Val := W2 :: C0 with hC1
  set C2 : List Val := W1 :: C1 with hC2

  -- ## step 1: the parameter word
  have hpre : ∀ v ∈ [W1, W2, .int (j : ℤ), .int (sh : ℤ), .int sgn, .int (r : ℤ), .int (p : ℤ)],
      vsz v ≤ MB := by
    intro v hv
    fin_cases hv <;> assumption
  have sP : WordR main pw (fun vs => vs = A0) (fun _ out => out = C0) (fun _ => Cs) := by
    refine MrgKit.WordR_conseqC (hpw main j sh r p sgn W1 W2 rest MB hpre hr hsh ht hsgn) ?_ ?_ ?_
    · rw [hA0, hJv, hSHv, hSGv, hRv, hPv]
    · intro out hout
      rw [hout, hC0, hA0]
    · rw [hCs]
      calc Kc * (MB + 1) * 64 ≤ Kx * (MB + 1) * 64 :=
            Nat.mul_le_mul_right 64 (Nat.mul_le_mul_right (MB + 1) hKc)
        _ ≤ Kx * (MB + 1) * 100 := Nat.mul_le_mul_left _ (by norm_num)
        _ = 100 * Kx * (MB + 1) := by ring
  -- ## step 2: copy the two vectors
  have s1 : WordR main (pickP 5) (fun vs => vs = C0) (fun _ out => out = C1) (fun _ => Cs) := by
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 5 C0 ?_ Cs ?_) rfl ?_ le_rfl
    · rw [hC0, hA0]; simp only [List.length_cons]; omega
    · refine pickRollCost_le (k := 5) le_rfl hMB1 ?_ hKp hCs.ge
      intro i hi
      interval_cases i <;>
        simp only [hC0, hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
          List.getD_cons_zero, List.getD_cons_succ] <;>
        assumption
    · intro out hout
      rw [hout, hC1, hC0, hA0, hJv, hSHv, hSGv, hRv, hPv]
      simp
  have s2 : WordR main (pickP 5) (fun vs => vs = C1) (fun _ out => out = C2) (fun _ => Cs) := by
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 5 C1 ?_ Cs ?_) rfl ?_ le_rfl
    · rw [hC1, hC0, hA0]; simp only [List.length_cons]; omega
    · refine pickRollCost_le (k := 5) le_rfl hMB1 ?_ hKp hCs.ge
      intro i hi
      interval_cases i <;>
        simp only [hC1, hC0, hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
          List.getD_cons_zero, List.getD_cons_succ] <;>
        assumption
    · intro out hout
      rw [hout, hC2, hC1, hC0, hA0, hJv, hSHv, hSGv, hRv, hPv]
      simp
  -- ## step 3: the half-difference of the two vectors
  have hperS : ∀ u v : ℤ × ℤ, inDisc p u → inDisc p v →
      WordR main qs (fun vs => vs = cfxVal u :: cfxVal v :: C0)
        (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: C0 ∧ inDisc p w ∧ ErrSub u v w)
        (fun _ => Ks * (2 * (2 * p + 7))) := by
    intro u v hu hv
    rw [hErrSub]
    exact hqs main p u v C0 hu hv
  have s3 : WordR main (zipP qs) (fun vs => vs = C2)
      (fun _ out => ∃ wd : List (ℤ × ℤ), out = cvecVal wd :: C0 ∧ wd.length = r ∧
        (∀ z ∈ wd, inDisc p z) ∧
        ∀ i : Fin r, ErrSub (w₁.getD (i : ℕ) (0, 0)) (w₂.getD (i : ℕ) (0, 0))
          (wd.getD (i : ℕ) (0, 0)))
      (fun _ => Cs) := by
    refine MrgKit.WordR_weaken
      (hzip main qs C0 p r ErrSub (Ks * (2 * (2 * p + 7))) w₁ w₂ hw1 hw2 hd1 hd2 hperS) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hC2, hC1, hW1, hW2]
    · intro vs out hvs hq
      exact hq
    · intro vs hvs
      rw [hCs, hMB]
      have h1 : Ks * (2 * (2 * p + 7)) ≤ Kx * (18 * (p + 1)) := by
        calc Ks * (2 * (2 * p + 7)) ≤ Kx * (2 * (2 * p + 7)) := Nat.mul_le_mul_right _ hKs
          _ ≤ Kx * (18 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
      have h2 : Kz * (2 * p + 8) ≤ Kx * (10 * (p + 1)) := by
        calc Kz * (2 * p + 8) ≤ Kx * (2 * p + 8) := Nat.mul_le_mul_right _ hKz
          _ ≤ Kx * (10 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
      have h3 : Ks * (2 * (2 * p + 7)) + Kz * (2 * p + 8) ≤ Kx * (28 * (p + 1)) := by
        nlinarith
      have h4 : r * (Ks * (2 * (2 * p + 7)) + Kz * (2 * p + 8)) + Kz ≤
          (r + 1) * (Kx * (28 * (p + 1))) + Kx := by
        nlinarith
      have h5 : (r + 1) * (Kx * (28 * (p + 1))) + Kx ≤
          100 * Kx * (20 * ((r + 1) * (p + 1)) + 1) := by
        nlinarith
      linarith
  -- ## step 4: the twiddle (y-multiplication) and the packaging
  have tail : ∀ (wd : List (ℤ × ℤ)), wd.length = r → (∀ z ∈ wd, inDisc p z) →
      (∀ i : Fin r, ErrSub (w₁.getD (i : ℕ) (0, 0)) (w₂.getD (i : ℕ) (0, 0))
        (wd.getD (i : ℕ) (0, 0))) →
      WordR main (ymProg ;;; (rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;;
        rollP 1 ;;; kdrP ;;; rollP 1 ;;; rollP 2 ;;; zipP qa))
        (fun vs => vs = cvecVal wd :: C0)
        (fun _ => TailPost)
        (fun _ => Cs + 11 * Cs) := by
    intro wd hwdlen hwddisc hwderr
    have htw4w : yMulS r sNat sgC wd = yMulList r (sgn * tZ) wd := htw4 wd hwdlen
    have s4 : WordR main ymProg
        (fun vs => vs = cvecVal wd :: C0)
        (fun _ out => ∃ w' : List (ℤ × ℤ), out = cvecVal w' :: C0 ∧
          w' = yMulS r sNat sgC wd ∧ w'.length = r ∧ (∀ z ∈ w', inDisc p z))
        (fun _ => Cs) := by
      refine MrgKit.WordR_weaken (hym main p r sNat sgC wd
        (W1 :: W2 :: Jv :: SHv :: SGv :: Rv :: Pv :: rest) hwdlen hsNatle hsgC1 hwddisc) ?_ ?_ ?_
      · intro vs hvs
        rw [hvs, hC0, hA0, hRv, hPv, hsCeq]
      · intro vs out hvs hq
        obtain ⟨w', h1, h2, h3, h4⟩ := hq
        refine ⟨w', ?_, h2, h3, h4⟩
        rw [h1, hC0, hA0, hRv, hPv, hsCeq]
      · intro vs hvs
        rw [hCs, hMB]
        calc Kym * (r + 1) * (p + 1) = Kym * ((r + 1) * (p + 1)) := by ring
          _ ≤ Kx * ((r + 1) * (p + 1)) := Nat.mul_le_mul_right _ hKym
          _ ≤ Kx * (20 * ((r + 1) * (p + 1)) + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ 100 * Kx * (20 * ((r + 1) * (p + 1)) + 1) := Nat.mul_le_mul_right _ (by omega)
    have tail2 : ∀ (w' : List (ℤ × ℤ)), w'.length = r → (∀ z ∈ w', inDisc p z) →
        w' = yMulS r sNat sgC wd →
        WordR main (rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;;
          rollP 1 ;;; kdrP ;;; rollP 1 ;;; rollP 2 ;;; zipP qa)
          (fun vs => vs = cvecVal w' :: C0)
          (fun _ => TailPost)
          (fun _ => 11 * Cs) := by
      intro w' hw'len hw'disc hw'eq
      have hVDsz : vsz (cvecVal w') ≤ MB := by
        rw [hMB]
        have h := MrgKit.vsz_cvecVal_le p r w' hw'len hw'disc
        nlinarith
      have hpack : ∀ (v₁ : List (ℤ × ℤ)),
          (∀ i : Fin r, ErrAdd (w₂.getD (i : ℕ) (0, 0)) (w₁.getD (i : ℕ) (0, 0))
            (v₁.getD (i : ℕ) (0, 0))) →
          v₁.length = r → (∀ z ∈ v₁, inDisc p z) → FPost v₁ w' := by
        intro v₁ hv₁err hv₁len hv₁disc
        have hadd : ∀ i : Fin r,
            (2 : ℝ) ^ p * ‖fxC p (v₁.getD (i : ℕ) (0, 0)) -
              (fxC p (w₁.getD (i : ℕ) (0, 0)) + fxC p (w₂.getD (i : ℕ) (0, 0))) / 2‖ < 1 := by
          intro i
          have h := hv₁err i
          rw [hErrAdd] at h
          simpa only [add_comm (fxC p (w₂.getD (i : ℕ) (0, 0)))] using h
        have hsub : ∀ i : Fin r,
            (2 : ℝ) ^ p * ‖fxC p (wd.getD (i : ℕ) (0, 0)) -
              (fxC p (w₁.getD (i : ℕ) (0, 0)) - fxC p (w₂.getD (i : ℕ) (0, 0))) / 2‖ < 1 := by
          intro i
          have h := hwderr i
          rw [hErrSub] at h
          exact h
        have hpe := pairErr p r w₁ w₂ v₁ wd u₁ u₂ e (sgn * tZ) he1 he2 hadd hsub
        rw [hFPost]
        refine ⟨hv₁len, hw'len, hv₁disc, hw'disc, fun c => hpe.1 c, ?_⟩
        intro c
        have hfx : fxC p (w'.getD (c : ℕ) (0, 0)) =
            yMul r (sgn * tZ) (fun c' => fxC p (wd.getD (c' : ℕ) (0, 0))) c := by
          rw [hw'eq, htw4w]
          exact yMulListOK p r (sgn * tZ) wd hwdlen hEabs c
        rw [hfx]
        exact hpe.2.2 c
      -- the four parameter removals
      have t5 : WordR main (rollP 1) (fun vs => vs = cvecVal w' :: C0)
          (fun _ out => out = .int sC :: cvecVal w' :: .int sgC :: Rv :: Pv :: A0)
          (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 1 (cvecVal w' :: C0) ?_ Cs ?_) rfl ?_ le_rfl
        · rw [hC0, hA0]; simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 1) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hC0, hA0, hW1, List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout, hC0, hA0]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      have t6 : WordR main kdrP
          (fun vs => vs = .int sC :: cvecVal w' :: .int sgC :: Rv :: Pv :: A0)
          (fun _ out => out = cvecVal w' :: .int sgC :: Rv :: Pv :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC (MrgKit.kdropStep (hkdr main)
          (.int sC :: cvecVal w' :: .int sgC :: Rv :: Pv :: A0) (by simp) Cs
          (dropCost_le hS1sz hKdr hCs.ge)) rfl ?_ le_rfl
        · intro out hout
          rw [hout]
          simp only [List.drop_succ_cons, List.drop_zero]
      have t7 : WordR main (rollP 1) (fun vs => vs = cvecVal w' :: .int sgC :: Rv :: Pv :: A0)
          (fun _ out => out = .int sgC :: cvecVal w' :: Rv :: Pv :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 1 (cvecVal w' :: .int sgC :: Rv :: Pv :: A0) ?_ Cs ?_)
          rfl ?_ le_rfl
        · simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 1) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hA0, hW1, hRv, hPv, List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      have t8 : WordR main kdrP
          (fun vs => vs = .int sgC :: cvecVal w' :: Rv :: Pv :: A0)
          (fun _ out => out = cvecVal w' :: Rv :: Pv :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC (MrgKit.kdropStep (hkdr main)
          (.int sgC :: cvecVal w' :: Rv :: Pv :: A0) (by simp) Cs
          (dropCost_le hS2sz hKdr hCs.ge)) rfl ?_ le_rfl
        · intro out hout
          rw [hout]
          simp only [List.drop_succ_cons, List.drop_zero]
      have t9 : WordR main (rollP 1) (fun vs => vs = cvecVal w' :: Rv :: Pv :: A0)
          (fun _ out => out = Rv :: cvecVal w' :: Pv :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 1 (cvecVal w' :: Rv :: Pv :: A0) ?_ Cs ?_) rfl ?_ le_rfl
        · rw [hA0]; simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 1) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
              List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout, hA0]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      have t10 : WordR main kdrP (fun vs => vs = Rv :: cvecVal w' :: Pv :: A0)
          (fun _ out => out = cvecVal w' :: Pv :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC (MrgKit.kdropStep (hkdr main)
          (Rv :: cvecVal w' :: Pv :: A0) (by simp) Cs (dropCost_le hRvsz hKdr hCs.ge))
          rfl ?_ le_rfl
        · intro out hout
          rw [hout]
          simp only [List.drop_succ_cons, List.drop_zero]
      have t11 : WordR main (rollP 1) (fun vs => vs = cvecVal w' :: Pv :: A0)
          (fun _ out => out = Pv :: cvecVal w' :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 1 (cvecVal w' :: Pv :: A0) ?_ Cs ?_) rfl ?_ le_rfl
        · rw [hA0]; simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 1) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
              List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout, hA0]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      have t12 : WordR main kdrP (fun vs => vs = Pv :: cvecVal w' :: A0)
          (fun _ out => out = cvecVal w' :: A0) (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC (MrgKit.kdropStep (hkdr main)
          (Pv :: cvecVal w' :: A0) (by simp) Cs (dropCost_le hPvsz hKdr hCs.ge))
          rfl ?_ le_rfl
        · intro out hout
          rw [hout]
          simp only [List.drop_succ_cons, List.drop_zero]
      -- bring the original two vectors to the top
      have t13 : WordR main (rollP 1) (fun vs => vs = cvecVal w' :: A0)
          (fun _ out => out = W1 :: cvecVal w' :: W2 :: Jv :: SHv :: SGv :: Rv :: Pv :: rest)
          (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 1 (cvecVal w' :: A0) ?_ Cs ?_) rfl ?_ le_rfl
        · rw [hA0]; simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 1) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
              List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout, hA0]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      have t14 : WordR main (rollP 2)
          (fun vs => vs = W1 :: cvecVal w' :: W2 :: Jv :: SHv :: SGv :: Rv :: Pv :: rest)
          (fun _ out => out = W2 :: W1 :: cvecVal w' :: Jv :: SHv :: SGv :: Rv :: Pv :: rest)
          (fun _ => Cs) := by
        refine MrgKit.WordR_conseqC
          (MrgKit.rollStep (hroll main) 2
            (W1 :: cvecVal w' :: W2 :: Jv :: SHv :: SGv :: Rv :: Pv :: rest) ?_ Cs ?_)
          rfl ?_ le_rfl
        · simp only [List.length_cons]; omega
        · refine pickRollCost_le (k := 2) (by norm_num) hMB1 ?_ hKr hCs.ge
          intro i hi
          interval_cases i <;>
            simp only [hA0, hW1, hW2, hJv, hSHv, hSGv, hRv, hPv,
              List.getD_cons_zero, List.getD_cons_succ] <;>
            assumption
        · intro out hout
          rw [hout]
          simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
            List.eraseIdx_cons_succ]
      -- the half-sum, from the (originally given) two vectors
      have t15 : WordR main (zipP qa)
          (fun vs => vs = W2 :: W1 :: cvecVal w' :: Jv :: SHv :: SGv :: Rv :: Pv :: rest)
          (fun _ => TailPost)
          (fun _ => Cs) := by
        set rest2 : List Val := cvecVal w' :: Jv :: SHv :: SGv :: Rv :: Pv :: rest with hrest2
        have hperA : ∀ u v : ℤ × ℤ, inDisc p u → inDisc p v →
            WordR main qa (fun vs => vs = cfxVal u :: cfxVal v :: rest2)
              (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: rest2 ∧ inDisc p w ∧ ErrAdd u v w)
              (fun _ => Ka * (2 * (2 * p + 7))) := by
          intro u v hu hv
          rw [hErrAdd]
          exact hqa main p u v rest2 hu hv
        have hraw : WordR main (zipP qa)
            (fun vs => vs = cvecVal w₂ :: cvecVal w₁ :: rest2)
            (fun _ out => ∃ va : List (ℤ × ℤ), out = cvecVal va :: rest2 ∧ va.length = r ∧
              (∀ z ∈ va, inDisc p z) ∧
              ∀ i : Fin r, ErrAdd (w₂.getD (i : ℕ) (0, 0)) (w₁.getD (i : ℕ) (0, 0))
                (va.getD (i : ℕ) (0, 0)))
            (fun _ => r * (Ka * (2 * (2 * p + 7)) + Kz * (2 * p + 8)) + Kz) :=
          hzip main qa rest2 p r ErrAdd (Ka * (2 * (2 * p + 7))) w₂ w₁ hw2 hw1 hd2 hd1 hperA
        refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
        · intro vs hvs
          rw [hvs, hW2, hW1, hrest2]
        · rintro vs out hvs ⟨va, hout, hlen, hdisc, herr⟩
          rw [hTailPost]
          refine ⟨va, w', ?_, hpack va herr hlen hdisc⟩
          rw [hout, hrest2]
        · intro vs hvs
          rw [hCs, hMB]
          have h1 : Ka * (2 * (2 * p + 7)) ≤ Kx * (18 * (p + 1)) := by
            calc Ka * (2 * (2 * p + 7)) ≤ Kx * (2 * (2 * p + 7)) := Nat.mul_le_mul_right _ hKa
              _ ≤ Kx * (18 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
          have h2 : Kz * (2 * p + 8) ≤ Kx * (10 * (p + 1)) := by
            calc Kz * (2 * p + 8) ≤ Kx * (2 * p + 8) := Nat.mul_le_mul_right _ hKz
              _ ≤ Kx * (10 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
          nlinarith
      have v1 := WordR_seqD t5 t6
      have v2 := WordR_seqD v1 t7
      have v3 := WordR_seqD v2 t8
      have v4 := WordR_seqD v3 t9
      have v5 := WordR_seqD v4 t10
      have v6 := WordR_seqD v5 t11
      have v7 := WordR_seqD v6 t12
      have v8 := WordR_seqD v7 t13
      have v9 := WordR_seqD v8 t14
      have v10 := WordR_seqD v9 t15
      refine MrgKit.WordR_weaken v10 (fun vs hvs => hvs) (fun vs out _ hq => hq) ?_
      intro vs hvs
      omega
    refine WordR_seqE_xhasPair s4 (fun mid hq => ?_)
    obtain ⟨w', heq, hyeq, hw'len, hw'disc⟩ := hq
    rw [heq]
    exact tail2 w' hw'len hw'disc hyeq
  -- ## the whole program
  have h123 := WordR_seqD (WordR_seqD sP s1) s2
  have h1234 := WordR_seqD h123 s3
  have hfull : WordR main (((pw ;;; pickP 5 ;;; pickP 5) ;;; zipP qs) ;;; (ymProg ;;; (rollP 1 ;;;
      kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; kdrP ;;; rollP 1 ;;; rollP 2 ;;;
      zipP qa)))
      (fun vs => vs = A0)
      (fun _ => TailPost)
      (fun _ => (((Cs + Cs) + Cs) + Cs) + (Cs + 11 * Cs)) :=
    WordR_seqE_xhasPair h1234 (fun mid hq => by
      obtain ⟨wd, heq, hlen, hdisc, herr⟩ := hq
      rw [heq]
      exact tail wd hlen hdisc herr)
  -- ## the cost bound and the final shape
  refine MrgKit.WordR_weaken hfull ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, hA0, hJv, hSHv, hSGv, hRv, hPv, hW1, hW2]
  · rintro vs out hvs hF
    rw [hTailPost] at hF
    obtain ⟨v₁, v₂, hout, hF⟩ := hF
    refine ⟨v₁, v₂, ?_, ?_⟩
    · rw [hout, hJv, hSHv, hSGv, hRv, hPv]
    · rw [hFPost] at hF
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
      refine ⟨h1, h2, h3, h4, h5, ?_⟩
      intro c
      have h := h6 c
      rw [htZ] at h
      exact h
  · intro vs hvs
    have h1 : Cs = 100 * Kx * (MB + 1) := hCs
    have h2 : (r * (Ks * (2 * (2 * p + 7)) + Kz * (2 * p + 8)) + Kz) ≤ Cs := by
      rw [hCs, hMB]
      have hb1 : Ks * (2 * (2 * p + 7)) ≤ Kx * (18 * (p + 1)) := by
        calc Ks * (2 * (2 * p + 7)) ≤ Kx * (2 * (2 * p + 7)) := Nat.mul_le_mul_right _ hKs
          _ ≤ Kx * (18 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
      have hb2 : Kz * (2 * p + 8) ≤ Kx * (10 * (p + 1)) := by
        calc Kz * (2 * p + 8) ≤ Kx * (2 * p + 8) := Nat.mul_le_mul_right _ hKz
          _ ≤ Kx * (10 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have hL : (((Cs + Cs) + Cs) + Cs) + (Cs + 11 * Cs) ≤ 16 * Cs := by
      omega
    have hR : 16 * Cs ≤ 1000000 * Kx * (r + 1) * (p + 1) + 1000000 * Kx := by
      rw [hCs, hMB]
      have hU : 1 ≤ (r + 1) * (p + 1) := by nlinarith
      nlinarith
    linarith

end Work.SynFFT
