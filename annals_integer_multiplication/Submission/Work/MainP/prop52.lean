
import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop
import Submission.Work.ConvR.dropUnder
import Submission.Work.ConvR.scaleRowWord
import Submission.Work.ConvR.pwdefs
import Submission.Work.MainP.conjVecWord
import Submission.Work.MainP.dftConj
import Submission.Work.MainP.epsComp
import Submission.Work.MainP.scaleErr
import Submission.Work.MainP.p52aux
import Submission.Work.MainP.p52helpers
import Submission.Work.MainP.sizeFactsLem
import Submission.Work.MainP.p52costLem

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 20000000

/-! # Paper Proposition 5.2 (Harvey--van der Hoeven, `M(n) = O(n log n)`)

`Submission/Work/MainP/prop52.lean`: the transform `F̃_s` (sgn = -1) and `F̃*_s` (sgn = 1, by
conjugation) for the coprime size `s = s₁···s_d` of §5.2, assembled from the resampling
Theorem 4.1 (`ResampleProp`), the power-of-two transform Theorem 3.1 (`TransformProp`) and
FxLib's scaling Lemma 2.2.

The word `q1` (sgn = -1) is the straight-line composition

  `D0 ; progA ; perm ; trP ; perm ; progB ; svP ; duP`

where `D0` computes `2^(2Dα²)` and duplicates the four parameters as many times as the three
library words need, and `svP` scales the resampled transform by `2^{2Dα²}`.  The word `q2`
(sgn = 1) is `perm ; conj ; perm ; q1 ; conj`, using `dftMulti ts 1 u = conj (dftMulti ts (-1)
(conj u))`.  The whole program branches on `sgn + 1`.
-/


namespace Work.MainP

open HvdH
open Work.ConvR

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Cost helpers -/

/-- `K * f ≤ ALLOW KB SB Pm` whenever `K ≤ KB` and `f` is at most `c` times the allowance
factor, for a constant `c ≤ 10^6`. -/
theorem allow_ge_mul {K KB SB Pm c f : ℕ} (hK : K ≤ KB) (hf : f ≤ c * (SB + 1 + Pm))
    (hc : c ≤ 1000000) : K * f ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  calc K * f ≤ KB * (c * (SB + 1 + Pm)) := Nat.mul_le_mul hK hf
    _ = (c * KB) * (SB + 1 + Pm) := by ring
    _ ≤ (1000000 * (KB + 1)) * (SB + 1 + Pm) :=
        Nat.mul_le_mul_right _ (le_trans (Nat.mul_le_mul_left c (Nat.le_succ KB))
          (Nat.mul_le_mul_right (KB + 1) hc))
    _ = 1000000 * (KB + 1) * (SB + 1 + Pm) := by ring

/-- A `roll` step on an explicit window whose entries all have encoding size `≤ SB`. -/
theorem rollStepSB (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {KB SB Pm : ℕ} (hKr : Kr ≤ KB) (k : ℕ) (hk : k ≤ 5) (L L' rest : List Val)
    (hL : ∀ v ∈ L, vsz v ≤ SB) (hkL : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L') :
    WordC main (rollP k) (fun vs => vs = L ++ rest) (fun _ out => out = L' ++ rest)
      (ALLOW KB SB Pm) := by
  refine rollStepT hK hroll k L L' rest (ALLOW KB SB Pm) hkL hL' ?_
  rw [show Kr * (k + 1) * ((((L.take (k + 1)).map vsz).sum) + 1)
      = Kr * ((k + 1) * ((((L.take (k + 1)).map vsz).sum) + 1)) from by ring]
  refine allow_ge_mul hKr ?_ (by norm_num : 36 ≤ 1000000)
  have h1 : ((L.take (k + 1)).map vsz).sum ≤ (L.take (k + 1)).length * SB :=
    sum_vsz_le (fun v hv => hL v (List.mem_of_mem_take hv))
  have h2 : (L.take (k + 1)).length ≤ k + 1 := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  have hk6 : k + 1 ≤ 6 := by omega
  have h3 : (L.take (k + 1)).length * SB ≤ (k + 1) * SB := Nat.mul_le_mul_right SB h2
  have h4 : ((L.take (k + 1)).map vsz).sum + 1 ≤ (k + 1) * SB + 1 := by omega
  have h5 : (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ (k + 1) * ((k + 1) * SB + 1) :=
    Nat.mul_le_mul_left _ h4
  have h6 : (k + 1) * ((k + 1) * SB + 1) ≤ 6 * (6 * SB + 1) :=
    Nat.mul_le_mul hk6 (Nat.add_le_add_right (Nat.mul_le_mul_right SB hk6) 1)
  have h7 : 6 * (6 * SB + 1) ≤ 36 * (SB + 1 + Pm) := by omega
  exact le_trans h5 (le_trans h6 h7)

/-- A `pick` step on an explicit window whose entries all have encoding size `≤ SB`. -/
theorem pickStepSB {main : Cmd} {pickP : ℕ → Cmd} {Kp : ℕ}
    (hpick : ∀ (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {KB SB Pm : ℕ} (hKp : Kp ≤ KB) (k : ℕ) (hk : k ≤ 10) (L rest : List Val)
    (hL : ∀ v ∈ L, vsz v ≤ SB) (hkL : k < L.length) :
    WordC main (pickP k) (fun vs => vs = L ++ rest) (fun _ out => out = L.getD k .nil :: L ++ rest)
      (ALLOW KB SB Pm) := by
  refine pickStep hpick k L rest (ALLOW KB SB Pm) hkL ?_
  rw [show Kp * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1)
      = Kp * ((k + 1) * (((L.take (k + 1)).map vsz).sum + 1)) from by ring]
  refine allow_ge_mul hKp ?_ (by norm_num : 121 ≤ 1000000)
  have h1 : ((L.take (k + 1)).map vsz).sum ≤ (L.take (k + 1)).length * SB :=
    sum_vsz_le (fun v hv => hL v (List.mem_of_mem_take hv))
  have h2 : (L.take (k + 1)).length ≤ k + 1 := by
    rw [List.length_take]; exact Nat.min_le_left _ _
  have hk11 : k + 1 ≤ 11 := by omega
  have h3 : (L.take (k + 1)).length * SB ≤ (k + 1) * SB := Nat.mul_le_mul_right SB h2
  have h4 : ((L.take (k + 1)).map vsz).sum + 1 ≤ (k + 1) * SB + 1 := by omega
  have h5 : (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ (k + 1) * ((k + 1) * SB + 1) :=
    Nat.mul_le_mul_left _ h4
  have h6 : (k + 1) * ((k + 1) * SB + 1) ≤ 11 * (11 * SB + 1) :=
    Nat.mul_le_mul hk11 (Nat.add_le_add_right (Nat.mul_le_mul_right SB hk11) 1)
  have h7 : 11 * (11 * SB + 1) ≤ 121 * (SB + 1 + Pm) := by omega
  exact le_trans h5 (le_trans h6 h7)

/-- A `permTop` step on an explicit window whose entries all have encoding size `≤ SB`. -/
theorem permStepSB (hK : KernelLib) {main : Cmd} {permP : List ℕ → Cmd} {KP : ℕ}
    (hperm : ∀ (main : Cmd) (n : ℕ) (σ : List ℕ) (head tail : List Val),
      head.length = n → σ.length = n → σ.Perm (List.range n) →
      WordR main (permP σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
        (fun _ => KP * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1)))
    {KB SB Pm : ℕ} (hKP : KP ≤ KB) (n : ℕ) (hn : n ≤ 13) (σ : List ℕ) (head head' tail : List Val)
    (h1 : head.length = n) (h2 : σ.length = n) (h3 : σ.Perm (List.range n))
    (h4 : σ.map (fun i => head.getD i .nil) = head') (hhead : ∀ v ∈ head, vsz v ≤ SB) :
    WordC main (permP σ) (fun vs => vs = head ++ tail) (fun _ out => out = head' ++ tail)
      (ALLOW KB SB Pm) := by
  have hC : KP * (n + 1) * (n + 1) * ((head.map vsz).sum + 1) ≤ ALLOW KB SB Pm := by
    refine perm_cost_le hKP hn ?_
    have h1' : (head.map vsz).sum ≤ head.length * SB := sum_vsz_le hhead
    rw [h1] at h1'
    exact le_trans h1' (Nat.mul_le_mul_right SB hn)
  refine WordC.conseq hK
    (permStep hperm n σ head tail (ALLOW KB SB Pm) h1 h2 h3 hC) (fun vs h => h) ?_ (le_rfl)
  intro vs out _ hq
  simpa only [hq, h4]

/-- A `pushVal` step for a value of encoding size `≤ SB`. -/
theorem pushStepSB {main : Cmd} {pushP : Val → Cmd} {Kp : ℕ}
    (hpv : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kp * (vsz v + 1)))
    {KB SB Pm : ℕ} (hKp : Kp ≤ KB) (v : Val) (rest : List Val) (hv : vsz v ≤ SB) :
    WordC main (pushP v) (fun vs => vs = rest) (fun _ out => out = v :: rest)
      (ALLOW KB SB Pm) := by
  refine pushStepT hpv v rest (ALLOW KB SB Pm) ?_
  refine allow_ge_mul hKp ?_ (by norm_num : 1 ≤ 1000000)
  omega

/-- A `mulS` step on two integers of numerical size at most `Pm`. -/
theorem mulStepSB {main : Cmd} {mulP : Cmd} {Km : ℕ}
    (hmul : ∀ main : Cmd, BinOp main mulP (fun _ _ => True) (· * ·)
      (fun a b => Km * isz a * isz b))
    {KB SB Pm : ℕ} (hKm : Km ≤ KB) (a b : ℤ) (rest : List Val)
    (hab : isz a * isz b ≤ Pm) :
    WordC main mulP (fun vs => vs = .int a :: .int b :: rest)
      (fun _ out => out = .int (a * b) :: rest) (ALLOW KB SB Pm) := by
  refine mulStepT hmul a b rest (ALLOW KB SB Pm) ?_
  rw [show Km * isz a * isz b = Km * (isz a * isz b) from by ring]
  refine allow_ge_mul hKm ?_ (by norm_num : 1 ≤ 1000000)
  omega

/-- A `pow2` step on an integer of numerical size at most `Pm`. -/
theorem powStepSB {main : Cmd} {powP : Cmd} {Kw : ℕ}
    (hpow : ∀ main : Cmd, UnOp main powP (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat)
      (fun k => Kw * (k.toNat + isz k)))
    {KB SB Pm : ℕ} (hKw : Kw ≤ KB) (k : ℤ) (rest : List Val) (hk : 0 ≤ k)
    (hkb : k.toNat + isz k ≤ Pm) :
    WordC main powP (fun vs => vs = .int k :: rest) (fun _ out => out = .int (2 ^ k.toNat) :: rest)
      (ALLOW KB SB Pm) := by
  refine powStepT hpow k rest (ALLOW KB SB Pm) hk ?_
  rw [show Kw * (k.toNat + isz k) = Kw * (k.toNat + isz k) from rfl]
  refine allow_ge_mul hKw ?_ (by norm_num : 1 ≤ 1000000)
  omega

/-- A `dropUnder`-shaped step is covered by the uniform allowance. -/
theorem allow_ge_quad {K KB SB Pm a b c : ℕ} (hK : K ≤ KB) (ha : a ≤ SB) (hb : b ≤ SB)
    (hc : c ≤ SB) : K * (a + b + c + 1) ≤ ALLOW KB SB Pm := by
  refine allow_ge_mul hK ?_ (by norm_num : 4 ≤ 1000000)
  omega

/-- Peeling a common 4-element prefix ending in a coefficient vector. -/
theorem cvecVal_peel4 {a b c d : Val} {zsA zs : List (ℤ × ℤ)} {rs rs' : List Val}
    (h : a :: b :: c :: d :: cvecVal zsA :: rs = a :: b :: c :: d :: cvecVal zs :: rs') :
    zsA = zs ∧ rs = rs' := by
  have h2 := (List.cons.injEq _ _ _ _).mp h
  have h3 := (List.cons.injEq _ _ _ _).mp h2.2
  have h4 := (List.cons.injEq _ _ _ _).mp h3.2
  have h5 := (List.cons.injEq _ _ _ _).mp h4.2
  have h6 := (List.cons.injEq _ _ _ _).mp h5.2
  exact ⟨Work.ConvR.cvecVal_injective_scaleInject h6.1, h6.2⟩

/-- Peeling a common 2-element prefix ending in a coefficient vector. -/
theorem cvecVal_peel2 {a b : Val} {zsA zs : List (ℤ × ℤ)} {rs rs' : List Val}
    (h : a :: b :: cvecVal zsA :: rs = a :: b :: cvecVal zs :: rs') : zsA = zs ∧ rs = rs' := by
  have h2 := (List.cons.injEq _ _ _ _).mp h
  have h3 := (List.cons.injEq _ _ _ _).mp h2.2
  have h4 := (List.cons.injEq _ _ _ _).mp h3.2
  exact ⟨Work.ConvR.cvecVal_injective_scaleInject h4.1, h4.2⟩

/-- Peeling a common 1-element prefix ending in a coefficient vector. -/
theorem cvecVal_peel1 {a : Val} {zsA zs : List (ℤ × ℤ)} {rs rs' : List Val}
    (h : a :: cvecVal zsA :: rs = a :: cvecVal zs :: rs') : zsA = zs ∧ rs = rs' := by
  have h2 := (List.cons.injEq _ _ _ _).mp h
  have h3 := (List.cons.injEq _ _ _ _).mp h2.2
  exact ⟨Work.ConvR.cvecVal_injective_scaleInject h3.1, h3.2⟩

/-- Paper Proposition 5.2: the transform of coprime size via resampling and a power-of-two
transform. -/
theorem prop52 : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.DFTMathProp →
    HvdH.TransformProp → HvdH.ResampleProp → HvdH.Prop52Prop := by
  intro hK hInt hLay hFx hDFT hTr hRes
  obtain ⟨pickP, Kpick, hpick⟩ := hK.pick
  obtain ⟨dupP, Kdup, hdup⟩ := hK.dup
  obtain ⟨dropP, Kdrop, hdrop⟩ := hK.drop
  obtain ⟨rollP, Kroll, hroll⟩ := hK.roll
  obtain ⟨pushVP, Kpv, hpv⟩ := hK.pushVal
  obtain ⟨ifzB, Kifz, hifz⟩ := hK.ifZero
  obtain ⟨permP, KP, hperm⟩ := Work.ConvR.permTop hK
  obtain ⟨duP, Kdu, hduW⟩ := Work.ConvR.dropUnder hK
  obtain ⟨addP, Kadd, hadd⟩ := hInt.add
  obtain ⟨mulP, Kmul, hmul⟩ := hInt.mulS
  obtain ⟨powP, Kpow, hpow⟩ := hInt.pow2
  obtain ⟨svP, Ksv, hsvW⟩ := Work.ConvR.scaleRowWord hK hFx
  obtain ⟨cjP, Kcj, hcjW⟩ := Work.MainP.conjVecWord hK hInt
  obtain ⟨trP, Ktr, hTrW⟩ := hTr
  obtain ⟨progA, progB, Kres, hResW⟩ := hRes
  set KB : ℕ := KP + Kpick + Kdrop + Kroll + Kdup + Kpv + Kifz + Kadd + Kmul + Kpow + Kcj + Ksv +
    Ktr + Kdu + Kres + 1 with hKB
  set Kf : ℕ := 1000000000000000000 * (KB + 1) * (KB + 1) + 1000000000000000000 with hKf
  let D0 : Cmd := rollP 1 ;;; dupP ;;; pushVP (.int (2 * D : ℤ)) ;;; mulP ;;; pickP 1 ;;; mulP ;;;
    powP ;;; permP [1, 2, 3, 4, 5, 0] ;;; pickP 1 ;;; pickP 1 ;;; pickP 3 ;;; pickP 2 ;;; pickP 6 ;;;
    pickP 8 ;;; pickP 9 ;;; permP [3, 5, 2, 0, 11, 4, 1, 6, 7, 9, 10, 8, 12]
  let q1 : Cmd := D0 ;;; progA ;;; permP [1, 2, 0] ;;; trP ;;; permP [1, 2, 3, 4, 0] ;;; progB ;;;
    svP ;;; duP
  let q2 : Cmd := permP [4, 0, 1, 2, 3] ;;; cjP ;;; permP [1, 2, 3, 4, 0] ;;; q1 ;;; cjP
  let prog : Cmd := rollP 4 ;;; pushVP (.int 1) ;;; addP ;;; ifzB q1 q2
  refine ⟨prog, Kf, ?_⟩

  intro main N Cm hmono hMulB p α ss ts sgn hsgn hFs hN1 hN2
  obtain ⟨hPow, hResP, h2Da, h3Dp, hSsT⟩ := hFs
  have hResP2 : ResParams p α ss ts := hResP
  obtain ⟨hsslen, htslen, hp100, hα2, hα2p, hResF⟩ := hResP2
  obtain ⟨A, B, hAn, hBn, hAid, hResW2⟩ := hResW p α ss ts hResP
  have hKresKB : Kres ≤ KB := by rw [hKB]; omega
  have hKtrKB : Ktr ≤ KB := by rw [hKB]; omega
  have hKsvKB : Ksv ≤ KB := by rw [hKB]; omega
  have hKcjKB : Kcj ≤ KB := by rw [hKB]; omega
  have hKfbig : Kres ≤ Kf := by rw [hKf]; nlinarith
  have hKresN : Kres * p < N := by
    have h : Kres * p ≤ Kf * p := Nat.mul_le_mul_right p hKfbig
    omega
  obtain ⟨hAword, hBword⟩ := hResW2 main N Cm hmono hMulB hKresN
  have hTword := hTrW main N Cm hmono hMulB p ts hPow hN1
  obtain ⟨hi2D, hiα, hi2Da, higam, hgamtoNat, hgameq, hgampos⟩ := sizeFactsLem hα2p h2Da hp100
  -- positivity of the products
  have hprod2 : ∀ {l : List ℕ}, (∀ x ∈ l, 2 ≤ x) → 2 ^ l.length ≤ l.prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha : 2 ≤ a := h a (by simp)
      have ht : 2 ^ t.length ≤ t.prod := ih (fun x hx => h x (by simp [hx]))
      calc 2 ^ (a :: t).length = 2 ^ (t.length + 1) := by rw [List.length_cons]
        _ = 2 ^ t.length * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ t.length := by ring
        _ ≤ a * t.prod := Nat.mul_le_mul ha ht
        _ = (a :: t).prod := rfl
  have hd2 : (2 : ℕ) ≤ 2 ^ D := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by norm_num) (by decide : 1 ≤ D)
  have hpow2t : ∀ t ∈ ts, 2 ≤ t := by
    intro t ht
    obtain ⟨k, hk1, hk2⟩ := hPow.2.1 t ht
    rw [hk2]
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hpow2s : ∀ s ∈ ss, 2 ≤ s := by
    intro s hs
    obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hs
    have h := (hResF i (by rw [← hsslen]; exact hi)).1
    rwa [List.getD_eq_getElem _ _ hi, hsi] at h
  have hts2 : 2 ≤ ts.prod := by
    have h := hprod2 hpow2t
    rw [htslen] at h
    exact le_trans hd2 h
  have hts1 : 1 ≤ ts.prod := by omega
  have htspos : 0 < ts.prod := by omega
  have hss2 : 2 ≤ ss.prod := by
    have h := hprod2 hpow2s
    rw [hsslen] at h
    exact le_trans hd2 h
  have hss1 : 1 ≤ ss.prod := by omega
  have hsspos : 0 < ss.prod := by omega
  have hposT : ∀ t ∈ ts, 0 < t := fun t ht => lt_of_lt_of_le (by norm_num) (hpow2t t ht)
  have hposS : ∀ s ∈ ss, 0 < s := fun s hs => lt_of_lt_of_le (by norm_num) (hpow2s s hs)
  -- the uniform size bound: it dominates the encoding size of every value occurring in the
  -- pipeline (and, for good measure, the numerical size of the small parameters)
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1) :=
    ⟨_, rfl⟩
  have hSinner : 8 * (cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) + isz (p : ℤ) +
      isz (α : ℤ) + isz (2 ^ (2 * D * α ^ 2) : ℤ) + 1) + cvecSz p ts.prod +
      (p + 16) * (p + 16) ≤ S := by
    have hSunf : S = 1000000 * (8 * (cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) +
        isz (p : ℤ) + isz (α : ℤ) + isz (2 ^ (2 * D * α ^ 2) : ℤ) + 1) + cvecSz p ts.prod +
        (p + 16) * (p + 16) + 1) := by rw [hS]; rfl
    rw [hSunf]; nlinarith
  have hcv_ss : cvecSz p ss.prod ≤ S := by nlinarith [hSinner]
  have hcv_ts : cvecSz p ts.prod ≤ S := by nlinarith [hSinner]
  have hsqS : (p + 16) * (p + 16) ≤ S := by nlinarith [hSinner]
  have hSp16 : p + 16 ≤ S := by nlinarith [hSinner, hp100]
  have hSof : ∀ x : ℕ, x ≤ p + 16 → x ≤ S := by intro x hx; omega
  set vP : Val := .int (p : ℤ) with hvP
  set vA : Val := .int (α : ℤ) with hvA
  set vSS : Val := intList ss with hvSS
  set vTS : Val := intList ts with hvTS
  set vC : Val := .int (2 ^ (2 * D * α ^ 2) : ℤ) with hvC
  set n2D : Val := .int (2 * D : ℤ) with hn2D
  set n2Da : Val := .int ((2 * D) * (α : ℤ)) with hn2Da
  set ngam : Val := .int ((α : ℤ) * ((2 * D) * (α : ℤ))) with hngam
  have hi2D14 : isz (2 * D : ℤ) ≤ 14 := by
    have h1 : ((2 : ℤ) * (D : ℤ)) = ((2 * D : ℕ) : ℤ) := by push_cast; ring
    have h : (2 * D : ℕ) < 2 ^ 12 := by rw [HvdH.D]; norm_num
    have h2 : (2 * D : ℕ).size ≤ 12 := Nat.size_le.mpr h
    rw [h1]
    simp only [HvdH.isz, Int.natAbs_natCast]
    omega
  have hiszC : isz (2 ^ (2 * D * α ^ 2) : ℤ) ≤ p + 16 := by
    have h1 : ((2 : ℤ) ^ (2 * D * α ^ 2)) = ((2 ^ (2 * D * α ^ 2) : ℕ) : ℤ) := by
      push_cast; ring
    have h : (2 ^ (2 * D * α ^ 2)).size ≤ 2 * D * α ^ 2 + 1 :=
      Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    rw [h1]
    simp only [HvdH.isz, Int.natAbs_natCast]
    omega
  have hszSS : vsz vSS ≤ S := by
    rw [hvSS]
    have h : vsz (intList ss) ≤ 8 * (cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) +
        isz (p : ℤ) + isz (α : ℤ) + isz (2 ^ (2 * D * α ^ 2) : ℤ) + 1) := by omega
    nlinarith [h, hSinner]
  have hszTS : vsz vTS ≤ S := by
    rw [hvTS]
    have h : vsz (intList ts) ≤ 8 * (cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) +
        isz (p : ℤ) + isz (α : ℤ) + isz (2 ^ (2 * D * α ^ 2) : ℤ) + 1) := by omega
    nlinarith [h, hSinner]
  have hszP : vsz vP ≤ S := by
    rw [hvP, Work.ConvR.vsz_int]
    exact hSof _ (by have h := isz_natCast_le p; omega)
  have hszA : vsz vA ≤ S := by
    rw [hvA, Work.ConvR.vsz_int]
    exact hSof _ hiα
  have hszC : vsz vC ≤ S := by rw [hvC, Work.ConvR.vsz_int]; exact hSof _ hiszC
  have hsz2D : vsz n2D ≤ S := by
    rw [hn2D, Work.ConvR.vsz_int]
    exact hSof _ (by omega)
  have hsz2Da : vsz n2Da ≤ S := by
    rw [hn2Da, Work.ConvR.vsz_int]
    exact hSof _ (by omega)
  have hszg : vsz ngam ≤ S := by
    rw [hngam, Work.ConvR.vsz_int]
    exact hSof _ (by omega)
  have hszSg : vsz (.int sgn) ≤ S := by
    rw [Work.ConvR.vsz_int]
    refine hSof _ ?_
    have h3 : isz sgn ≤ 3 := by
      rcases hsgn with h | h <;> rw [h] <;> decide
    omega
  have hszOne : vsz (.int (1 : ℤ)) ≤ S := by
    rw [Work.ConvR.vsz_int]
    refine hSof _ ?_
    have h : isz (1 : ℤ) = 3 := by decide
    omega
  have hszSg1 : vsz (.int (sgn + 1)) ≤ S := by
    rw [Work.ConvR.vsz_int]
    refine hSof _ ?_
    have h3 : isz (sgn + 1) ≤ 5 := by
      rcases hsgn with h | h <;> rw [h] <;> decide
    omega
  have hpair : ∀ a b : ℕ, a ≤ 14 → b ≤ p + 16 → a * b ≤ S := by
    intro a b ha hb
    have h1 : a * b ≤ 14 * (p + 16) := Nat.mul_le_mul ha hb
    have h2 : 14 * (p + 16) ≤ (p + 16) * (p + 16) := by nlinarith [hp100]
    omega
  have hpair2 : ∀ a b : ℕ, a ≤ p + 16 → b ≤ p + 16 → a * b ≤ S := by
    intro a b ha hb
    have h1 : a * b ≤ (p + 16) * (p + 16) := Nat.mul_le_mul ha hb
    omega
  have hab₂ : isz (2 * D : ℤ) * isz (α : ℤ) ≤ S := hpair _ _ hi2D14 hiα
  have hab₃ : isz (α : ℤ) * isz ((2 * D) * (α : ℤ)) ≤ S := hpair2 _ _ hiα hi2Da
  have hgam2 : ((α : ℤ) * ((2 * D) * (α : ℤ))).toNat +
      isz ((α : ℤ) * ((2 * D) * (α : ℤ))) ≤ S := by
    have h1 : ((α : ℤ) * ((2 * D) * (α : ℤ))).toNat ≤ p + 16 := hgamtoNat
    have h2 : isz ((α : ℤ) * ((2 * D) * (α : ℤ))) ≤ p + 16 := higam
    have h3 : 2 * (p + 16) ≤ (p + 16) * (p + 16) := by nlinarith [hp100]
    omega
  set eA : ℝ := ((D * p ^ 2 : ℕ) : ℝ) with heA
  set eT : ℝ := ((8 * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) with heT
  set eB : ℝ := ((D * p ^ 2 : ℕ) : ℝ) with heB
  set c : ℕ := 2 ^ (2 * D * α ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc1 : 1 ≤ c := by rw [hc]; exact Nat.one_le_two_pow
  have hcle : c ≤ 2 ^ p := by rw [hc]; exact Nat.pow_le_pow_right (by norm_num) h2Da
  obtain ⟨trCost, htrCost⟩ : ∃ x : ℕ, x = 4 * (ts.prod / lmax ts) * Cm (3 * lmax ts * p) +
      Ktr * ts.prod * p ^ 2 + Ktr * ts.sum * (p + 1) ^ Ktr := ⟨_, rfl⟩
  obtain ⟨svCost, hsvCost⟩ : ∃ x : ℕ, x = Ksv * (ss.prod + 1) * (p + 1) ^ 2 + Ksv := ⟨_, rfl⟩
  obtain ⟨cjCost, hcjCost⟩ : ∃ x : ℕ, x = Kcj * (ss.prod + 1) * (p + 1) + Kcj := ⟨_, rfl⟩
  obtain ⟨Cq1, hCq1⟩ : ∃ x : ℕ, x = 20 * ALLOW KB S S + 2 * resCost Kres Cm p α ts + trCost +
      svCost := ⟨_, rfl⟩
  obtain ⟨Cq2, hCq2⟩ : ∃ x : ℕ, x = Cq1 + 3 * ALLOW KB S S + 2 * cjCost := ⟨_, rfl⟩
  -- the `sgn = -1` pipeline
  have hq1 : ∀ (zs : List (ℤ × ℤ)) (rest : List Val), InDiscVec p ss.prod zs →
      WordC main q1 (fun vs => vs = [vP, vA, vSS, vTS, cvecVal zs] ++ rest)
        (fun _ out => ∃ ws, out = cvecVal ws :: rest ∧
          Approx p ws (dftMulti ss (-1) (fxVec p ss.prod zs))
            ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) Cq1 := by
    intro zs rest hdisc
    set vZ : Val := cvecVal zs with hvZ
    have hszZ : vsz vZ ≤ S := by
      have h := Work.ConvR.vsz_cvecVal_le (u := zs) hdisc
      rw [hS]
      show vsz (cvecVal zs) ≤ 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
      omega
    set AppA : List (ℤ × ℤ) → Prop :=
      fun wsA => Approx p wsA (A (fxVec p ss.prod zs)) eA with hAppA
    set AppT : List (ℤ × ℤ) → List (ℤ × ℤ) → Prop :=
      fun wsA wsT => Approx p wsT (dftMulti ts (-1) (fxVec p ts.prod wsA)) eT with hAppT
    set AppB : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → Prop :=
      fun _ wsT wsB => Approx p wsB (B (fxVec p ts.prod wsT)) eB with hAppB
    -- the 16 elementary steps of `D0`
    have S1 : WordC main (rollP 1) (fun vs => vs = [vP, vA, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      exact rollStepSB hK hroll (KB := KB) (SB := S) (Pm := S) (by rw [hKB]; omega) 1 (by norm_num) [vP, vA, vSS, vTS, vZ] [vA, vP, vSS, vTS, vZ] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl
          · exact hszP
          · exact hszA
          · exact hszSS
          · exact hszTS
          · exact hszZ) (by simp) (by simp)
    have S2 : WordC main dupP (fun vs => vs = [vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vA, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      refine WordC.conseq hK (dupStepT hdup vA ([vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) ?_)
        (fun vs h => h) (fun vs out hvs hq => hq) (le_rfl)
      refine allow_ge_mul (by rw [hKB]; omega) ?_ (by norm_num : 1 ≤ 1000000)
      omega
    have S3 : WordC main (pushVP n2D) (fun vs => vs = [vA, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [n2D, vA, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      exact pushStepSB (KB := KB) (SB := S) (Pm := S) hpv (by rw [hKB]; omega) n2D ([vA, vA, vP, vSS, vTS, vZ] ++ rest) hsz2D
    have S4 : WordC main mulP (fun vs => vs = [n2D, vA, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [n2Da, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      exact mulStepSB (KB := KB) (SB := S) (Pm := S) hmul (by rw [hKB]; omega) (2 * D) (α : ℤ) ([vA, vP, vSS, vTS, vZ] ++ rest) hab₂
    have S5 : WordC main (pickP 1) (fun vs => vs = [n2Da, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vA, n2Da, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 1 (by norm_num) [n2Da, vA, vP, vSS, vTS, vZ] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hsz2Da
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ) (by simp)
    have S6 : WordC main mulP (fun vs => vs = [vA, n2Da, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [ngam, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      exact mulStepSB (KB := KB) (SB := S) (Pm := S) hmul (by rw [hKB]; omega) (α : ℤ) ((2 * D) * (α : ℤ)) ([vA, vP, vSS, vTS, vZ] ++ rest) hab₃
    have S7 : WordC main powP (fun vs => vs = [ngam, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vC, vA, vP, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
      refine WordC.conseq hK
        (powStepSB (KB := KB) (SB := S) (Pm := S) hpow (by rw [hKB]; omega) ((α : ℤ) * ((2 * D) * (α : ℤ)))
          ([vA, vP, vSS, vTS, vZ] ++ rest) hgampos hgam2) (fun vs h => h) ?_ (le_rfl)
      intro vs out _ hq
      have hk : (2 : ℤ) ^ (((α : ℤ) * ((2 * D) * (α : ℤ))).toNat) =
          (2 : ℤ) ^ (2 * D * α ^ 2) := by
        rw [hgameq]
      simpa only [hq, hk, hvC, List.cons_append, List.nil_append]
    have S8 : WordC main (permP [1, 2, 3, 4, 5, 0]) (fun vs => vs = [vC, vA, vP, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact permStepSB (KB := KB) (SB := S) (Pm := S) hK hperm (by rw [hKB]; omega) 6 (by norm_num) [1, 2, 3, 4, 5, 0] [vC, vA, vP, vSS, vTS, vZ] [vA, vP, vSS, vTS, vZ, vC] rest
        (by simp) (by simp) (by decide) (by simp) (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszC
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ)
    have S9 : WordC main (pickP 1) (fun vs => vs = [vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 1 (by norm_num) [vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S10 : WordC main (pickP 1) (fun vs => vs = [vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 1 (by norm_num) [vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S11 : WordC main (pickP 3) (fun vs => vs = [vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 3 (by norm_num) [vA, vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S12 : WordC main (pickP 2) (fun vs => vs = [vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 2 (by norm_num) [vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S13 : WordC main (pickP 6) (fun vs => vs = [vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 6 (by norm_num) [vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszP
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S14 : WordC main (pickP 8) (fun vs => vs = [vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 8 (by norm_num) [vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszSS
          · exact hszP
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S15 : WordC main (pickP 9) (fun vs => vs = [vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vTS, vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest) (ALLOW KB S S) := by
      exact pickStepSB (KB := KB) (SB := S) (Pm := S) (hpick main) (by rw [hKB]; omega) 9 (by norm_num) [vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] rest
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszTS
          · exact hszSS
          · exact hszP
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC) (by simp)
    have S16 : WordC main (permP [3, 5, 2, 0, 11, 4, 1, 6, 7, 9, 10, 8, 12]) (fun vs => vs = [vTS, vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] ++ rest)
        (fun _ out => out = [vP, vA, vSS, vTS, vZ, vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest) (ALLOW KB S S) := by
      exact permStepSB (KB := KB) (SB := S) (Pm := S) hK hperm (by rw [hKB]; omega) 13 (by norm_num) [3, 5, 2, 0, 11, 4, 1, 6, 7, 9, 10, 8, 12] [vTS, vTS, vSS, vP, vP, vA, vP, vA, vP, vSS, vTS, vZ, vC] [vP, vA, vSS, vTS, vZ, vP, vTS, vP, vA, vSS, vTS, vP, vC] rest
        (by simp) (by simp) (by decide) (by simp) (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hszTS
          · exact hszTS
          · exact hszSS
          · exact hszP
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszA
          · exact hszP
          · exact hszSS
          · exact hszTS
          · exact hszZ
          · exact hszC)
    -- `progA` (the resampling interpolation `Ã`)
    have S17 : WordC main progA
        (fun vs => vs = [vP, vA, vSS, vTS, vZ, vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest)
        (fun _ out => ∃ wsA, out = cvecVal wsA ::
          ([vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA)
        (resCost Kres Cm p α ts) := by
      refine WordC.conseq hK hAword ?_ ?_ (le_rfl)
      · intro vs hvs
        refine ⟨zs, [vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest, ?_, hdisc⟩
        exact hvs
      · intro vs out hvs hq
        obtain ⟨zsA, rsA, wsA, he, hout, happ⟩ := hq
        have hh : (.int (p : ℤ) :: .int (α : ℤ) :: intList ss :: intList ts :: cvecVal zsA :: rsA)
            = (.int (p : ℤ) :: .int (α : ℤ) :: intList ss :: intList ts :: cvecVal zs ::
                ([vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest)) := he.symm.trans hvs
        obtain ⟨hzs, hr⟩ := cvecVal_peel4 hh
        refine ⟨wsA, ?_, ?_⟩
        · simpa only [hout, hr, List.cons_append, List.nil_append]
        · rw [hzs] at happ; exact happ
    -- `perm [1,2,0]`
    have S18 : WordC main (permP [1, 2, 0])
        (fun vs => ∃ wsA, vs = cvecVal wsA ::
          ([vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA)
        (fun _ out => ∃ wsA, out = [vP, vTS, cvecVal wsA] ++
          ([vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA) (ALLOW KB S S) := by
      intro vs hvs s R hR
      obtain ⟨wsA, hvw, hAppA'⟩ := hvs
      have hszWA : vsz (cvecVal wsA) ≤ S := by
        have h := Work.ConvR.vsz_cvecVal_le (u := wsA) hAppA'.1
        rw [hS]
        show vsz (cvecVal wsA) ≤ 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
        omega
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        permStepSB (KB := KB) (SB := S) (Pm := S) hK hperm (by rw [hKB]; omega) 3 (by norm_num) [1, 2, 0]
          [cvecVal wsA, vP, vTS] [vP, vTS, cvecVal wsA]
          ([vP, vA, vSS, vTS, vP, vC] ++ rest)
          (by simp) (by simp) (by decide) (by simp)
          (fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl <;> assumption)
          vs hvw s R hR
      exact ⟨out, s', n, ⟨wsA, hq, hAppA'⟩, he, hn, hstk, hoth⟩
    -- `trP` (the power-of-two transform `F̃_t`)
    have S19 : WordC main trP
        (fun vs => ∃ wsA, vs = [vP, vTS, cvecVal wsA] ++
          ([vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA)
        (fun _ out => ∃ wsA wsT, out = cvecVal wsT ::
          ([vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA ∧ AppT wsA wsT) trCost := by
      refine WordC.conseq hK hTword ?_ ?_ (le_of_eq (by simp only [htrCost]))
      · intro vs hvs
        obtain ⟨wsA, hvw, hAppA'⟩ := hvs
        refine ⟨wsA, [vP, vA, vSS, vTS, vP, vC] ++ rest, ?_, hAppA'.1⟩
        exact hvw
      · intro vs out hvs hq
        obtain ⟨wsA, hvw, hAppA'⟩ := hvs
        obtain ⟨zt, rt, wsT, he, hout, happ⟩ := hq
        have hh : (.int (p : ℤ) :: intList ts :: cvecVal zt :: rt)
            = (.int (p : ℤ) :: intList ts :: cvecVal wsA ::
                ([vP, vA, vSS, vTS, vP, vC] ++ rest)) := he.symm.trans hvw
        obtain ⟨hzt, hr⟩ := cvecVal_peel2 hh
        refine ⟨wsA, wsT, ?_, hAppA', ?_⟩
        · simpa only [hout, hr, List.cons_append, List.nil_append]
        · rw [hzt] at happ; exact happ
    -- `perm [1,2,3,4,0]`
    have S20 : WordC main (permP [1, 2, 3, 4, 0])
        (fun vs => ∃ wsA wsT, vs = cvecVal wsT ::
          ([vP, vA, vSS, vTS, vP, vC] ++ rest) ∧ AppA wsA ∧ AppT wsA wsT)
        (fun _ out => ∃ wsA wsT, out = [vP, vA, vSS, vTS, cvecVal wsT] ++
          ([vP, vC] ++ rest) ∧ AppA wsA ∧ AppT wsA wsT) (ALLOW KB S S) := by
      intro vs hvs s R hR
      obtain ⟨wsA, wsT, hvw, hAppA', hAppT'⟩ := hvs
      have hszWT : vsz (cvecVal wsT) ≤ S := by
        have h := Work.ConvR.vsz_cvecVal_le (u := wsT) hAppT'.1
        rw [hS]
        show vsz (cvecVal wsT) ≤ 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
        omega
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        permStepSB (KB := KB) (SB := S) (Pm := S) hK hperm (by rw [hKB]; omega) 5 (by norm_num) [1, 2, 3, 4, 0]
          [cvecVal wsT, vP, vA, vSS, vTS] [vP, vA, vSS, vTS, cvecVal wsT]
          ([vP, vC] ++ rest)
          (by simp) (by simp) (by decide) (by simp)
          (fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
          vs hvw s R hR
      exact ⟨out, s', n, ⟨wsA, wsT, hq, hAppA', hAppT'⟩, he, hn, hstk, hoth⟩
    -- `progB` (the resampling projection `B̃`)
    have S21 : WordC main progB
        (fun vs => ∃ wsA wsT, vs = [vP, vA, vSS, vTS, cvecVal wsT] ++
          ([vP, vC] ++ rest) ∧ AppA wsA ∧ AppT wsA wsT)
        (fun _ out => ∃ wsA wsT wsB, out = cvecVal wsB :: ([vP, vC] ++ rest) ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB) (resCost Kres Cm p α ts) := by
      refine WordC.conseq hK hBword ?_ ?_ (le_rfl)
      · intro vs hvs
        obtain ⟨wsA, wsT, hvw, hAppA', hAppT'⟩ := hvs
        refine ⟨wsT, [vP, vC] ++ rest, ?_, hAppT'.1⟩
        exact hvw
      · intro vs out hvs hq
        obtain ⟨wsA, wsT, hvw, hAppA', hAppT'⟩ := hvs
        obtain ⟨zt, rt, wsB, he, hout, happ⟩ := hq
        have hh : (.int (p : ℤ) :: .int (α : ℤ) :: intList ss :: intList ts :: cvecVal zt :: rt)
            = (.int (p : ℤ) :: .int (α : ℤ) :: intList ss :: intList ts :: cvecVal wsT ::
                ([vP, vC] ++ rest)) := he.symm.trans hvw
        obtain ⟨hzt, hr⟩ := cvecVal_peel4 hh
        refine ⟨wsA, wsT, wsB, ?_, hAppA', hAppT', ?_⟩
        · simpa only [hout, hr, List.cons_append, List.nil_append]
        · rw [hzt] at happ; exact happ
    -- `svP` (the scaling by `2^γ`)
    have S22 : WordC main svP
        (fun vs => ∃ wsA wsT wsB, vs = cvecVal wsB :: ([vP, vC] ++ rest) ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB)
        (fun _ out => ∃ wsA wsT wsB vs', out = cvecVal vs' :: ([vP, vC] ++ rest) ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB ∧ InDiscVec p ss.prod vs' ∧
          (∀ j : Fin ss.prod, ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) - (c : ℂ) * x‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p (wsB.getD j (0, 0)) - x‖) + 3)) svCost := by
      intro vs hvs s R hR
      obtain ⟨wsA, wsT, wsB, hvw, hA', hT', hB'⟩ := hvs
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        hsvW main p c ss.prod hc1 hcle wsB rest hB'.1
          vs hvw s R hR
      refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
      · obtain ⟨v, hout, hdisc, hscale⟩ := hq
        refine ⟨wsA, wsT, wsB, v, ?_, hA', hT', hB', ?_, ?_⟩
        · exact hout
        · exact hdisc
        · intro j x hx
          exact hscale j x hx
      · exact le_trans hn (le_of_eq (by simp only [hsvCost]))
    -- `duP` (dropping the two parameters)
    have S23 : WordC main duP
        (fun vs => ∃ wsA wsT wsB vs', vs = cvecVal vs' :: ([vP, vC] ++ rest) ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB ∧ InDiscVec p ss.prod vs' ∧
          (∀ j : Fin ss.prod, ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) - (c : ℂ) * x‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p (wsB.getD j (0, 0)) - x‖) + 3))
        (fun _ out => ∃ wsA wsT wsB vs', out = cvecVal vs' :: rest ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB ∧ InDiscVec p ss.prod vs' ∧
          (∀ j : Fin ss.prod, ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) - (c : ℂ) * x‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p (wsB.getD j (0, 0)) - x‖) + 3))
        (ALLOW KB S S) := by
      intro vs hvs s R hR
      obtain ⟨wsA, wsT, wsB, vs', hv, hA', hT', hB', hD', hS'⟩ := hvs
      have hszV : vsz (cvecVal vs') ≤ S := by
        have h := Work.ConvR.vsz_cvecVal_le (u := vs') hD'
        rw [hS]
        show vsz (cvecVal vs') ≤ 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
        omega
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        hduW main (cvecVal vs') vP vC rest
          vs (by simpa only [hv, List.cons_append, List.nil_append]) s R hR
      refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
      · exact ⟨wsA, wsT, wsB, vs', hq, hA', hT', hB', hD', hS'⟩
      · have hn' : n ≤ Kdu * (vsz (cvecVal vs') + vsz vP + vsz vC + 1) := hn
        have hKdu : Kdu ≤ KB := by rw [hKB]; omega
        exact le_trans hn' (allow_ge_quad (KB := KB) (SB := S) (Pm := S) hKdu hszV hszP hszC)
    -- compose the 16 steps of `D0`
    have hD0 : WordC main D0 (fun vs => vs = [vP, vA, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vP, vA, vSS, vTS, vZ, vP, vTS, vP, vA, vSS, vTS, vP, vC] ++ rest)
        (16 * ALLOW KB S S) := by
      refine WordC.conseq hK
        (seqC hK S1 (seqC hK S2 (seqC hK S3 (seqC hK S4 (seqC hK S5 (seqC hK S6 (seqC hK S7
          (seqC hK S8 (seqC hK S9 (seqC hK S10 (seqC hK S11 (seqC hK S12 (seqC hK S13 (seqC hK S14
          (seqC hK S15 S16))))))))))))))) (fun vs h => h) (fun vs out hvs hq => hq) ?_
      omega
    -- compose the whole `q1` chain
    have hchain : WordC main q1
        (fun vs => vs = [vP, vA, vSS, vTS, vZ] ++ rest)
        (fun _ out => ∃ wsA wsT wsB vs', out = cvecVal vs' :: rest ∧
          AppA wsA ∧ AppT wsA wsT ∧ AppB wsA wsT wsB ∧ InDiscVec p ss.prod vs' ∧
          (∀ j : Fin ss.prod, ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) - (c : ℂ) * x‖ <
              2 * c * ((2 : ℝ) ^ p * ‖fxC p (wsB.getD j (0, 0)) - x‖) + 3)) Cq1 := by
      refine WordC.conseq hK
        (seqC hK hD0 (seqC hK S17 (seqC hK S18 (seqC hK S19 (seqC hK S20 (seqC hK S21
          (seqC hK S22 S23))))))) (fun vs h => h) (fun vs out hvs hq => hq) ?_
      rw [hCq1]
      omega
    -- the numerical part: the scaled transform is close to `F̃_s`
    refine WordC.conseq hK hchain (fun vs h => h) ?_ (le_rfl)
    intro vs out hvs hq
    obtain ⟨wsA, wsT, wsB, vs', hout, hAppA', hAppT', hAppB', hDisc, hScale⟩ := hq
    refine ⟨vs', hout, hDisc, ?_⟩
    intro j
    have hcomp := epsComp hsspos htspos p A (fun u => dftMulti ts (-1) u) B
      (fun u v => dftMulti_sub hDFT hposT (-1) u v)
      (fun u => dftMulti_norm_le hDFT hposT (-1) u)
      (fun u v => map_sub B u v) (fun u => hBn u)
      (fxVec p ss.prod zs) eA eT eB (by rw [heA]; positivity) (by rw [heT]; positivity)
      (by rw [heB]; positivity) wsA wsT wsB hAppA' hAppT' hAppB' j
    have hcx : (c : ℂ) * (B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j) =
        dftMulti ss (-1) (fxVec p ss.prod zs) j := by
      have hid := hAid (fxVec p ss.prod zs)
      rw [hid, Pi.smul_apply, hc]
      push_cast
      ring
    have hxle : (c : ℝ) * ‖B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j‖ ≤ 1 := by
      have h1 : (c : ℝ) * ‖B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j‖ =
          ‖dftMulti ss (-1) (fxVec p ss.prod zs) j‖ := by
        rw [← hcx, norm_mul, Complex.norm_natCast]
      rw [h1]
      calc ‖dftMulti ss (-1) (fxVec p ss.prod zs) j‖ ≤ ‖dftMulti ss (-1) (fxVec p ss.prod zs)‖ :=
            norm_le_pi_norm _ j
        _ ≤ ‖fxVec p ss.prod zs‖ := dftMulti_norm_le hDFT hposS (-1) _
        _ ≤ 1 := pi_norm_le_of_forall (by norm_num)
            (fun i => Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hdisc i))
    have hs1 := hScale j (B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j) hxle
    have hbound : 2 * c * (eA + eT + eB) + 3 <
        ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) := by
      have h3 := scaleErr (D := D) (p := p) (α := α) (T := ts.prod) (L := Nat.log 2 ts.prod)
        (by decide) hp100 h2Da h3Dp rfl
      have heq : 2 * c * (eA + eT + eB) + 3 =
          2 * (2 : ℝ) ^ (2 * D * α ^ 2) * ((D * p ^ 2 : ℝ) +
            (8 * ts.prod * Nat.log 2 ts.prod : ℝ) + (D * p ^ 2 : ℝ)) + 3 := by
        rw [heA, heT, heB, hc]
        push_cast
        ring
      rw [heq]; exact h3
    have hc1' : (1 : ℝ) ≤ c := by rw [hc]; exact_mod_cast Nat.one_le_two_pow
    calc (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) -
          dftMulti ss (-1) (fxVec p ss.prod zs) j‖
        = (2 : ℝ) ^ p * ‖fxC p (vs'.getD j (0, 0)) -
            (c : ℂ) * (B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j)‖ := by rw [hcx]
      _ < 2 * c * ((2 : ℝ) ^ p * ‖fxC p (wsB.getD j (0, 0)) -
            B (dftMulti ts (-1) (A (fxVec p ss.prod zs))) j‖) + 3 := hs1
      _ < 2 * c * (eA + eT + eB) + 3 := by
          have hp2 : (0 : ℝ) < 2 * (c : ℝ) := by rw [hc]; positivity
          have := mul_lt_mul_of_pos_left hcomp hp2
          linarith
      _ < ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) := hbound
  -- the `sgn = 1` pipeline: conjugate, run `q1`, conjugate back
  intro vs hpre s R hR
  obtain ⟨zs, rest, hvs, hdisc⟩ := hpre
  set vZ : Val := cvecVal zs with hvZ
  have hszZ' : vsz vZ ≤ S := by
    have h := Work.ConvR.vsz_cvecVal_le (u := zs) hdisc
    rw [hS]
    show vsz (cvecVal zs) ≤ 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
    omega
  have hdisc' : InDiscVec p ss.prod (zs.map conjP) := by
    refine ⟨?_, ?_⟩
    · rw [List.length_map]; exact hdisc.1
    · intro z hz'
      obtain ⟨z0, hz0, hz'⟩ := List.mem_map.mp hz'
      rw [← hz']
      exact inDisc_conj' (hdisc.2 z0 hz0)
  have hszZc : vsz (cvecVal (zs.map conjP)) ≤ S := by
    have h := Work.ConvR.vsz_cvecVal_le (u := zs.map conjP) hdisc'
    omega
  have hq2 : WordC main q2
      (fun vs => vs = [vP, vA, vSS, vTS, vZ] ++ rest)
      (fun _ out => ∃ ws, out = cvecVal ws :: rest ∧
        Approx p ws (dftMulti ss 1 (fxVec p ss.prod zs))
          ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) Cq2 := by
    have D1 : WordC main (permP [4, 0, 1, 2, 3])
        (fun vs => vs = [vP, vA, vSS, vTS, vZ] ++ rest)
        (fun _ out => out = [vZ, vP, vA, vSS, vTS] ++ rest) (ALLOW KB S S) := by
      exact permStepSB hK hperm (by rw [hKB]; omega) 5 (by norm_num) [4, 0, 1, 2, 3]
        [vP, vA, vSS, vTS, vZ] [vZ, vP, vA, vSS, vTS] rest
        (by simp) (by simp) (by decide) (by simp)
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
    have D2 : WordC main cjP
        (fun vs => vs = vZ :: ([vP, vA, vSS, vTS] ++ rest))
        (fun _ out => out = cvecVal (zs.map conjP) :: ([vP, vA, vSS, vTS] ++ rest)) cjCost := by
      intro vs hvs s R hR
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        hcjW main p zs ([vP, vA, vSS, vTS] ++ rest) ⟨rfl, hdisc.2⟩
          vs (by simpa only [hvs, hvZ, List.cons_append, List.nil_append]) s R hR
      refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
      · obtain ⟨-, hout⟩ := hq
        exact hout
      · refine le_trans hn (le_of_eq (by simp only [hcjCost, hdisc.1]))
    have D3 : WordC main (permP [1, 2, 3, 4, 0])
        (fun vs => vs = cvecVal (zs.map conjP) :: ([vP, vA, vSS, vTS] ++ rest))
        (fun _ out => out = [vP, vA, vSS, vTS, cvecVal (zs.map conjP)] ++ rest)
        (ALLOW KB S S) := by
      exact permStepSB (KB := KB) (SB := S) (Pm := S) hK hperm (by rw [hKB]; omega)
        5 (by norm_num) [1, 2, 3, 4, 0]
        [cvecVal (zs.map conjP), vP, vA, vSS, vTS]
        [vP, vA, vSS, vTS, cvecVal (zs.map conjP)] rest
        (by simp) (by simp) (by decide) (by simp)
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl
          · exact hszZc
          · exact hszP
          · exact hszA
          · exact hszSS
          · exact hszTS)
    have D4 : WordC main q1
        (fun vs => vs = [vP, vA, vSS, vTS, cvecVal (zs.map conjP)] ++ rest)
        (fun _ out => ∃ ws', out = cvecVal ws' :: rest ∧
          Approx p ws' (dftMulti ss (-1) (fxVec p ss.prod (zs.map conjP)))
            ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) Cq1 :=
      hq1 (zs.map conjP) rest hdisc'
    have D5 : WordC main cjP
        (fun vs => ∃ ws', vs = cvecVal ws' :: rest ∧
          Approx p ws' (dftMulti ss (-1) (fxVec p ss.prod (zs.map conjP)))
            ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ))
        (fun _ out => ∃ ws', out = cvecVal (ws'.map conjP) :: rest ∧
          Approx p ws' (dftMulti ss (-1) (fxVec p ss.prod (zs.map conjP)))
            ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) cjCost := by
      intro vs hvs s R hR
      obtain ⟨ws', hvw, hApp'⟩ := hvs
      obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
        hcjW main p ws' rest ⟨rfl, hApp'.1.2⟩ vs hvw s R hR
      refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
      · obtain ⟨-, hout⟩ := hq
        exact ⟨ws', hout, hApp'⟩
      · refine le_trans hn (le_of_eq (by simp only [hcjCost, hApp'.1.1]))
    refine WordC.conseq hK
      (seqC hK D1 (seqC hK D2 (seqC hK D3 (seqC hK D4 D5)))) (fun vs h => h) ?_ ?_
    · intro vs out hvs hq
      obtain ⟨ws', hout, hApp'⟩ := hq
      have h1 : Approx p (ws'.map conjP)
          (fun i => starRingEnd ℂ (dftMulti ss (-1) (fxVec p ss.prod (zs.map conjP)) i))
          ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) :=
        approx_conj hApp'
      have h2 : (fun i => starRingEnd ℂ
            (dftMulti ss (-1) (fxVec p ss.prod (zs.map conjP)) i)) =
          dftMulti ss 1 (fxVec p ss.prod zs) := by
        funext j
        rw [dftConj ss (fxVec p ss.prod zs) j, ← fxVec_conjP]
      rw [h2] at h1
      exact ⟨ws'.map conjP, hout, h1⟩
    · rw [hCq2]
      omega
  -- the top-level steps: rotate `sgn` to the top, push `1`, add, branch
  have hszSgn : vsz (.int sgn) ≤ S := hszSg
  have T1 : WordC main (rollP 4)
      (fun vs => vs = [vP, vA, vSS, vTS, .int sgn, vZ] ++ rest)
      (fun _ out => out = [.int sgn, vP, vA, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
    exact rollStepSB hK hroll (by rw [hKB]; omega) 4 (by norm_num)
      [vP, vA, vSS, vTS, .int sgn, vZ] [.int sgn, vP, vA, vSS, vTS, vZ] rest
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      (by simp) (by simp)
  have T2 : WordC main (pushVP (.int 1))
      (fun vs => vs = [.int sgn, vP, vA, vSS, vTS, vZ] ++ rest)
      (fun _ out => out = [.int 1, .int sgn, vP, vA, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) :=
    pushStepSB hpv (by rw [hKB]; omega) (.int 1)
      ([.int sgn, vP, vA, vSS, vTS, vZ] ++ rest) hszOne
  have T3 : WordC main addP
      (fun vs => vs = [.int 1, .int sgn, vP, vA, vSS, vTS, vZ] ++ rest)
      (fun _ out => out = [.int (sgn + 1), vP, vA, vSS, vTS, vZ] ++ rest) (ALLOW KB S S) := by
    intro vs hvs s R hR
    obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
      hadd main vs (by
        refine ⟨1, sgn, [vP, vA, vSS, vTS, vZ] ++ rest, ?_, trivial⟩
        exact hvs) s R hR
    refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
    · obtain ⟨a', b', r', he', hout⟩ := hq
      have hone : (1 : ℤ) + sgn = sgn + 1 := by ring
      have h4 : a' = 1 ∧ b' = sgn ∧ r' = ([vP, vA, vSS, vTS, vZ] ++ rest) := by
        have h := he'.symm.trans hvs
        have h2 := (List.cons.injEq _ _ _ _).mp h
        have h3 := (List.cons.injEq _ _ _ _).mp h2.2
        exact ⟨(Val.int.injEq _ _).mp h2.1, (Val.int.injEq _ _).mp h3.1, h3.2⟩
      obtain ⟨rfl, rfl, rfl⟩ := h4
      simpa only [hout, hone, List.cons_append, List.nil_append]
    · have hβ : n ≤ Kadd * (isz (1 : ℤ) + isz sgn) := by
        have h := hn
        rw [hvs] at h
        exact h
      have hcost : Kadd * (isz (1 : ℤ) + isz sgn) ≤ ALLOW KB S S := by
        refine allow_ge_mul (KB := KB) (SB := S) (Pm := S) (c := 6) (by rw [hKB]; omega) ?_
          (by norm_num)
        have h1 : isz (1 : ℤ) = 3 := by decide
        have h2 : isz sgn ≤ 3 := by rcases hsgn with h | h <;> rw [h] <;> decide
        omega
      exact le_trans hβ hcost
  have T4 : WordC main (ifzB q1 q2)
      (fun vs => vs = [.int (sgn + 1), vP, vA, vSS, vTS, vZ] ++ rest)
      (fun _ out => (sgn + 1 = 0 → ∃ ws, out = cvecVal ws :: rest ∧
            Approx p ws (dftMulti ss (-1) (fxVec p ss.prod zs))
              ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) ∧
          (sgn + 1 ≠ 0 → ∃ ws, out = cvecVal ws :: rest ∧
            Approx p ws (dftMulti ss 1 (fxVec p ss.prod zs))
              ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)))
      (Kifz * (isz (sgn + 1) + 1) + max Cq1 Cq2) := by
    refine hifz main q1 q2 (sgn + 1) ([vP, vA, vSS, vTS, vZ] ++ rest) _ _ Cq1 Cq2 ?_ ?_
    · intro _hz0
      exact hq1 zs rest hdisc
    · intro _hz0
      exact hq2
  have hT : WordC main (.seq (rollP 4) (.seq (pushVP (.int 1)) (.seq addP (ifzB q1 q2))))
      (fun vs => vs = [vP, vA, vSS, vTS, .int sgn, vZ] ++ rest)
      (fun _ out => (sgn + 1 = 0 → ∃ ws, out = cvecVal ws :: rest ∧
            Approx p ws (dftMulti ss (-1) (fxVec p ss.prod zs))
              ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)) ∧
          (sgn + 1 ≠ 0 → ∃ ws, out = cvecVal ws :: rest ∧
            Approx p ws (dftMulti ss 1 (fxVec p ss.prod zs))
              ((2 ^ (2 * D * α ^ 2 + 5) * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ)))
      (3 * ALLOW KB S S + (Kifz * (isz (sgn + 1) + 1) + max Cq1 Cq2)) := by
    refine WordC.conseq hK (seqC hK T1 (seqC hK T2 (seqC hK T3 T4)))
      (fun vs h => h) (fun vs out hvs hq => hq) ?_
    omega
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
    hT vs (by simpa only [hvs, hvZ, List.cons_append, List.nil_append]) s R hR
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rcases hsgn with h1 | h1
    · rw [h1] at hvs hq ⊢
      obtain ⟨ws, hout, happ⟩ := hq.2 (by omega)
      exact ⟨zs, rest, ws, hvs, hout, happ⟩
    · rw [h1] at hvs hq ⊢
      obtain ⟨ws, hout, happ⟩ := hq.1 (by omega)
      exact ⟨zs, rest, ws, hvs, hout, happ⟩
  · -- the final cost accounting
    have hn' : n ≤ 3 * ALLOW KB S S + (Kifz * (isz (sgn + 1) + 1) + max Cq1 Cq2) := hn
    have hIfz : Kifz * (isz (sgn + 1) + 1) ≤ 5 * KB := by
      have h5 : isz (sgn + 1) + 1 ≤ 5 := by rcases hsgn with h | h <;> rw [h] <;> decide
      calc Kifz * (isz (sgn + 1) + 1) ≤ KB * 5 := Nat.mul_le_mul (by rw [hKB]; omega) h5
        _ = 5 * KB := by ring
    have hmax : max Cq1 Cq2 ≤ Cq2 := max_le (by rw [hCq2]; omega) le_rfl
    have hKB1 : 1 ≤ KB + 1 := Nat.succ_le_succ (Nat.zero_le KB)
    have hp1 : 1 ≤ p := by omega
    have hp0 : 0 < p := by omega
    have hTp1 : 1 ≤ ts.prod * p := Nat.mul_pos htspos hp0
    have hTp2 : 1 ≤ ts.prod * p ^ 2 := by
      have h : 1 ≤ ts.prod * (p * p) := Nat.mul_pos htspos (Nat.mul_pos hp0 hp0)
      simpa [pow_two] using h
    -- basic bounds on `Kf`
    have hKfge : KB ≤ Kf := by
      rw [hKf]
      have h1 : KB ≤ 1000000000000000000 * (KB + 1) := by
        calc KB ≤ KB + 1 := Nat.le_succ KB
          _ = 1 * (KB + 1) := (Nat.one_mul _).symm
          _ ≤ 1000000000000000000 * (KB + 1) := Nat.mul_le_mul_right _ (by norm_num)
      have h2 : 1000000000000000000 * (KB + 1) ≤ 1000000000000000000 * (KB + 1) * (KB + 1) := by
        calc 1000000000000000000 * (KB + 1) = (1000000000000000000 * (KB + 1)) * 1 :=
              (Nat.mul_one _).symm
          _ ≤ (1000000000000000000 * (KB + 1)) * (KB + 1) := Nat.mul_le_mul_left _ hKB1
      exact le_trans (le_trans h1 h2) (Nat.le_add_right _ _)
    have hKB70 : 70 * KB ≤ Kf := by
      rw [hKf]
      have h1 : 70 * KB ≤ 70 * (KB + 1) := Nat.mul_le_mul_left 70 (Nat.le_succ KB)
      have h2 : 70 * (KB + 1) ≤ 1000000000000000000 * (KB + 1) :=
        Nat.mul_le_mul_right _ (by norm_num)
      have h3 : 1000000000000000000 * (KB + 1) ≤ 1000000000000000000 * (KB + 1) * (KB + 1) := by
        calc 1000000000000000000 * (KB + 1) = (1000000000000000000 * (KB + 1)) * 1 :=
              (Nat.mul_one _).symm
          _ ≤ (1000000000000000000 * (KB + 1)) * (KB + 1) := Nat.mul_le_mul_left _ hKB1
      exact le_trans (le_trans h1 (le_trans h2 h3)) (Nat.le_add_right _ _)
    -- bounds on the size parameter `S`
    have hSB0le : SB0 p α ss ts ≤ 200 * ts.prod * p := sb0_le hPow hResP hSsT h3Dp
    have hcvecT : cvecSz p ts.prod ≤ 3 * (ts.prod * p) := by
      have h : 2 * p + 10 ≤ 3 * p := by omega
      have h1 : ts.prod * (2 * p + 8) + ts.prod + 1 ≤ ts.prod * (2 * p + 10) := by
        have h2 := Nat.mul_le_mul_left ts.prod (by omega : 2 * p + 8 ≤ 2 * p + 10)
        nlinarith only [h2, hts1]
      have h3 : ts.prod * (2 * p + 10) ≤ ts.prod * (3 * p) := Nat.mul_le_mul_left _ h
      have h4 : ts.prod * (3 * p) = 3 * (ts.prod * p) := by ring
      simp only [Work.ConvR.cvecSz, Work.ConvR.cfxSz]
      omega
    have hTge : p ≤ ts.prod := by
      have hD1 : 1 ≤ D := by decide
      have h1 : p ≤ 3 * D * p ^ 2 := by
        have h2 : p * (3 * D * p) = 3 * D * p ^ 2 := by ring
        have h3 : 1 ≤ 3 * D * p := by nlinarith only [hp1, hD1]
        calc p = p * 1 := (Nat.mul_one _).symm
          _ ≤ p * (3 * D * p) := Nat.mul_le_mul_left _ h3
          _ = 3 * D * p ^ 2 := h2
      omega
    have hPmS : Pm0 p ≤ 2 * (ts.prod * p) := by
      rw [Pm0]
      have h1 : (p + 16) * (p + 16) ≤ 2 * (p * p) := by nlinarith only [hp100]
      have h2 : p * p ≤ ts.prod * p := Nat.mul_le_mul_right p hTge
      have h3 : 2 * (p * p) ≤ 2 * (ts.prod * p) := Nat.mul_le_mul_left 2 h2
      nlinarith only [h1, h3]
    have hSp : S ≤ 300000000 * (ts.prod * p) := by
      have h1 : SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1 ≤ 206 * (ts.prod * p) := by
        have h2 : 200 * ts.prod * p = 200 * (ts.prod * p) := by ring
        omega
      have h2 : S = 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1) := hS
      rw [h2]
      calc 1000000 * (SB0 p α ss ts + cvecSz p ts.prod + Pm0 p + 1)
          ≤ 1000000 * (206 * (ts.prod * p)) := Nat.mul_le_mul_left _ h1
        _ = 206000000 * (ts.prod * p) := by ring
        _ ≤ 300000000 * (ts.prod * p) := Nat.mul_le_mul_right _ (by norm_num)
    have hALLOWle : ALLOW KB S S ≤ 1000000000000000 * (KB + 1) * (ts.prod * p) := by
      rw [ALLOW]
      have h2 : S + 1 + S ≤ 1000000000 * (ts.prod * p) := by
        have h3 : 2 * S ≤ 600000000 * (ts.prod * p) := by omega
        omega
      calc 1000000 * (KB + 1) * (S + 1 + S)
          ≤ 1000000 * (KB + 1) * (1000000000 * (ts.prod * p)) := Nat.mul_le_mul_left _ h2
        _ = 1000000000000000 * (KB + 1) * (ts.prod * p) := by ring
    have hconst : 52000000000000000 * (KB + 1) ≤ Kf := by
      rw [hKf]
      have h1 : (52000000000000000 : ℕ) ≤ 1000000000000000000 * (KB + 1) := by
        calc (52000000000000000 : ℕ) ≤ 1000000000000000000 := by norm_num
          _ = 1000000000000000000 * 1 := (Nat.mul_one _).symm
          _ ≤ 1000000000000000000 * (KB + 1) := Nat.mul_le_mul_left _ hKB1
      have h2 : 52000000000000000 * (KB + 1) ≤
          (1000000000000000000 * (KB + 1)) * (KB + 1) := Nat.mul_le_mul_right _ h1
      have h3 : (1000000000000000000 * (KB + 1)) * (KB + 1) =
          1000000000000000000 * (KB + 1) * (KB + 1) := by ring
      exact le_trans (by rw [← h3]; exact h2) (Nat.le_add_right _ _)
    -- (2) the machine-step allowance against `Kf * T * p²`
    have hL1 : 52 * ALLOW KB S S ≤ Kf * (ts.prod * p) := by
      calc 52 * ALLOW KB S S ≤ 52 * (1000000000000000 * (KB + 1) * (ts.prod * p)) :=
            Nat.mul_le_mul_left 52 hALLOWle
        _ = (52000000000000000 * (KB + 1)) * (ts.prod * p) := by ring
        _ ≤ Kf * (ts.prod * p) := Nat.mul_le_mul_right _ hconst
    have hL1b : Kf * (ts.prod * p) ≤ Kf * ts.prod * p ^ 2 := by
      have h1 : Kf * (ts.prod * p) = (Kf * ts.prod) * p := by ring
      have h2 : Kf * ts.prod * p ^ 2 = (Kf * ts.prod) * p ^ 2 := by ring
      have h3 : p ≤ p ^ 2 := by nlinarith only [hp1]
      have h4 : (Kf * ts.prod) * p ≤ (Kf * ts.prod) * p ^ 2 := Nat.mul_le_mul_left _ h3
      omega
    have hP1 : 2 * (26 * ALLOW KB S S) ≤ Kf * ts.prod * p ^ 2 := by
      linarith only [hL1, hL1b]
    -- (3) the scaling and conjugation words
    have hpp : (p + 1) * (p + 1) ≤ 4 * (p * p) := by nlinarith only [hp100]
    have hsv2 : svCost ≤ 9 * (KB * (ts.prod * p ^ 2)) := by
      rw [hsvCost]
      have hs : ss.prod + 1 ≤ 2 * ts.prod := by omega
      have h1 : (ss.prod + 1) * ((p + 1) * (p + 1)) ≤ 8 * (ts.prod * (p * p)) := by
        have hX := Nat.mul_le_mul hs hpp
        have hY : (2 * ts.prod) * (4 * (p * p)) = 8 * (ts.prod * (p * p)) := by ring
        rw [← hY]; exact hX
      have h2 : Ksv * (ss.prod + 1) * (p + 1) ^ 2 + Ksv ≤ 8 * (KB * (ts.prod * (p * p))) + KB := by
        have h3 : Ksv * ((ss.prod + 1) * ((p + 1) * (p + 1))) ≤ KB * (8 * (ts.prod * (p * p))) :=
          le_trans (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_right _ hKsvKB)
        have h4 : Ksv * (ss.prod + 1) * (p + 1) ^ 2 =
            Ksv * ((ss.prod + 1) * ((p + 1) * (p + 1))) := by ring
        have h5 : KB * (8 * (ts.prod * (p * p))) = 8 * (KB * (ts.prod * (p * p))) := by ring
        exact add_le_add (le_trans (le_of_eq h4) (le_trans h3 (le_of_eq h5))) hKsvKB
      have h6 : 8 * (KB * (ts.prod * (p * p))) + KB ≤ 9 * (KB * (ts.prod * (p * p))) := by
        have hTp2' : 1 ≤ ts.prod * (p * p) := by simpa [pow_two] using hTp2
        have h7 : KB ≤ KB * (ts.prod * (p * p)) := by
          calc KB = KB * 1 := (Nat.mul_one _).symm
            _ ≤ KB * (ts.prod * (p * p)) := Nat.mul_le_mul_left _ hTp2'
        omega
      have h8 : 9 * (KB * (ts.prod * (p * p))) = 9 * (KB * (ts.prod * p ^ 2)) := by ring
      exact le_trans h2 (le_trans h6 (le_of_eq h8))
    have hcj2 : cjCost ≤ 5 * (KB * (ts.prod * p ^ 2)) := by
      rw [hcjCost]
      have hs : ss.prod + 1 ≤ 2 * ts.prod := by omega
      have hq : p + 1 ≤ 2 * p := by omega
      have h1 : (ss.prod + 1) * (p + 1) ≤ 4 * (ts.prod * p) := by
        have hX := Nat.mul_le_mul hs hq
        have hY : (2 * ts.prod) * (2 * p) = 4 * (ts.prod * p) := by ring
        rw [← hY]; exact hX
      have h2 : Kcj * (ss.prod + 1) * (p + 1) + Kcj ≤ 4 * (KB * (ts.prod * p)) + KB := by
        have h3 : Kcj * ((ss.prod + 1) * (p + 1)) ≤ KB * (4 * (ts.prod * p)) :=
          le_trans (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_right _ hKcjKB)
        have h4 : Kcj * (ss.prod + 1) * (p + 1) = Kcj * ((ss.prod + 1) * (p + 1)) := by ring
        have h5 : KB * (4 * (ts.prod * p)) = 4 * (KB * (ts.prod * p)) := by ring
        omega
      have h6 : 4 * (KB * (ts.prod * p)) + KB ≤ 5 * (KB * (ts.prod * p ^ 2)) := by
        have h7 : KB * (ts.prod * p) ≤ KB * (ts.prod * (p * p)) :=
          Nat.mul_le_mul_left KB (Nat.mul_le_mul_left ts.prod (by nlinarith only [hp1]))
        have h7b : KB * (ts.prod * (p * p)) = KB * (ts.prod * p ^ 2) := by ring
        have h8 : KB ≤ KB * (ts.prod * p ^ 2) := by
          calc KB = KB * 1 := (Nat.mul_one _).symm
            _ ≤ KB * (ts.prod * p ^ 2) := Nat.mul_le_mul_left _ hTp2
        omega
      omega
    have hKtr2 : Ktr * ts.prod * p ^ 2 ≤ KB * (ts.prod * p ^ 2) := by
      have h1 : Ktr * ts.prod * p ^ 2 = Ktr * (ts.prod * p ^ 2) := by ring
      have h2 : Ktr * (ts.prod * p ^ 2) ≤ KB * (ts.prod * p ^ 2) :=
        Nat.mul_le_mul_right _ hKtrKB
      omega
    have hKB5b : 5 * KB ≤ 5 * (KB * (ts.prod * p ^ 2)) := by
      have h1 : KB ≤ KB * (ts.prod * p ^ 2) := by
        calc KB = KB * 1 := (Nat.mul_one _).symm
          _ ≤ KB * (ts.prod * p ^ 2) := Nat.mul_le_mul_left _ hTp2
      exact Nat.mul_le_mul_left 5 h1
    have hP2 : 2 * (5 * KB + Ktr * ts.prod * p ^ 2 + svCost + 2 * cjCost) ≤
        Kf * ts.prod * p ^ 2 := by
      have hsum : 2 * (5 * KB + Ktr * ts.prod * p ^ 2 + svCost + 2 * cjCost) ≤
          70 * (KB * (ts.prod * p ^ 2)) := by
        linarith only [hsv2, hcj2, hKtr2, hKB5b]
      have h70 : 70 * (KB * (ts.prod * p ^ 2)) ≤ Kf * ts.prod * p ^ 2 := by
        calc 70 * (KB * (ts.prod * p ^ 2)) = (70 * KB * ts.prod) * p ^ 2 := by ring
          _ ≤ (Kf * ts.prod) * p ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hKB70)
          _ = Kf * ts.prod * p ^ 2 := by ring
      exact le_trans hsum h70
    have hbudget : 26 * ALLOW KB S S + 5 * KB + Ktr * ts.prod * p ^ 2 + svCost + 2 * cjCost
        ≤ Kf * ts.prod * p ^ 2 := by linarith only [hP1, hP2]
    -- (4) the resampling, transform and conjugation parts
    have hRES : 2 * resCost Kres Cm p α ts ≤ 2 * resCost Kf Cm p α ts :=
      Nat.mul_le_mul_left 2 (resCostMono hmono hKfbig p α ts)
    have hPOW : Ktr * ts.sum * (p + 1) ^ Ktr ≤ Kf * ts.sum * (p + 1) ^ Kf := by
      have hKtrKf : Ktr ≤ Kf := le_trans hKtrKB hKfge
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul hKtrKf le_rfl
      · exact Nat.pow_le_pow_right (by omega) hKtrKf
    -- (5) assembly
    have hn2 : n ≤ 3 * ALLOW KB S S + (5 * KB + Cq2) := by omega
    have hbook : n ≤ 26 * ALLOW KB S S + 5 * KB + 2 * resCost Kres Cm p α ts + trCost + svCost +
        2 * cjCost := by
      have h1 := hn2
      rw [hCq2, hCq1] at h1
      omega
    have hTR1 : trCost = 4 * (ts.prod / lmax ts) * Cm (3 * lmax ts * p) + Ktr * ts.prod * p ^ 2 +
        Ktr * ts.sum * (p + 1) ^ Ktr := htrCost
    have hfinal : n ≤ 4 * (ts.prod / lmax ts) * Cm (3 * lmax ts * p) + 2 * resCost Kf Cm p α ts +
        Kf * ts.prod * p ^ 2 + Kf * ts.sum * (p + 1) ^ Kf := by
      omega
    simpa only [HvdH.fsCost] using hfinal
end Work.MainP
