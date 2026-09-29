import Mathlib
import Mathlib
import Submission.Work.Resample.buWtKit
import Submission.Work.Resample.buZAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- The word computing the working-scale exponent `buZ p α s t ℓ h = ⌊2^P·π α² N/s²⌋` of the one-dimensional
`B̃` weight table (paper §4).  It consumes `ℓ` and `h` and keeps the parameter block `buCB p α s t` in
place: `[ℓ, h, p, α, s, t, m, n, π] ↦ [buZ …, p, α, s, t, m, n, π]`.

Intended implementation (all steps are `IntLib`/`KernelLib` primitives; `Pipe` steps):
copy `ℓ` and `h`; `β₁ = buBeta s t ℓ = t·ℓ − fdiv (2·(t·ℓ)+s) (2·s)·s` (`buBeta_eq`, `IntLib.mulS/add/fdiv`);
`n = ℓ+h`; `β₂ = buBeta s t (ℓ+h)`; `N = (t·h+β₁)² − β₂²`; `Z = tdiv (π·(α²·N)) (s²)`. -/
theorem buZWalt (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s)
      (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ h : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hh : h.natAbs ≤ Work.Resample.egM p α),
      Work.Resample.Pipe main prog
        ([HvdH.Val.int ℓ, HvdH.Val.int h] ++ Work.Resample.buCB p α s t)
        ([HvdH.Val.int (Work.Resample.buZ p α s t ℓ h)] ++ Work.Resample.buCB p α s t)
        (K * (p + 1) ^ K) := by
  obtain ⟨pickP, Kpick, hpick⟩ := KL.pick
  obtain ⟨rollP, Kroll, hroll⟩ := KL.roll
  obtain ⟨dupP, Kd, hdup⟩ := KL.dup
  obtain ⟨mulP, Km, hmul⟩ := IL.mulS
  obtain ⟨addP, Ka, hadd⟩ := IL.add
  obtain ⟨subP, Ksub, hsub⟩ := IL.sub
  obtain ⟨fdivP, Kf, hfdiv⟩ := IL.fdiv
  obtain ⟨tdivP, Kt, htdiv⟩ := IL.tdiv
  set KS : ℕ := Kpick + Kroll + Kd + Km + Ka + Ksub + Kf + Kt + 1 with hKS
  have hKpick : Kpick ≤ KS := by omega
  have hKroll : Kroll ≤ KS := by omega
  have hKd : Kd ≤ KS := by omega
  have hKm : Km ≤ KS := by omega
  have hKa : Ka ≤ KS := by omega
  have hKsub : Ksub ≤ KS := by omega
  have hKf : Kf ≤ KS := by omega
  have hKt : Kt ≤ KS := by omega
  have hKS1 : 1 ≤ KS := by omega
  refine ⟨(.seq (pickP 5) (.seq mulP (.seq (rollP 1) (.seq (pickP 5) (.seq mulP (.seq (pickP 0) (.seq (pickP 2) (.seq addP (.seq (pickP 2) (.seq dupP (.seq addP (.seq (pickP 6) (.seq dupP (.seq addP (.seq (pickP 7) (.seq (rollP 2) (.seq addP (.seq fdivP (.seq (pickP 6) (.seq mulP (.seq (rollP 3) (.seq subP (.seq (pickP 1) (.seq dupP (.seq addP (.seq (pickP 6) (.seq dupP (.seq addP (.seq (pickP 7) (.seq (rollP 2) (.seq addP (.seq fdivP (.seq (pickP 6) (.seq mulP (.seq (rollP 2) (.seq subP (.seq (rollP 2) (.seq (rollP 2) (.seq addP (.seq dupP (.seq mulP (.seq (rollP 1) (.seq dupP (.seq mulP (.seq (rollP 1) (.seq subP (.seq (pickP 2) (.seq dupP (.seq mulP (.seq (rollP 1) (.seq mulP (.seq (pickP 7) (.seq mulP (.seq (pickP 3) (.seq dupP (.seq mulP (.seq (rollP 1) tdivP))))))))))))))))))))))))))))))))))))))))))))))))))))))))), 8 * (58 * KS * 1000000 ^ 2 + 4) + 8, ?_⟩
  intro main p α s t hs hst hα hp htp hαp ℓ h hℓ hℓs hh
  have hs0e : 0 < s := by omega
  have hp2e : 2 ≤ p + 1 := by omega
  have hc1e : 1 ≤ 58 * KS * 1000000 ^ 2 := by nlinarith [hKS1]
  have hsp : s < 2 ^ p := lt_trans hst htp
  have hα2p : α < 2 ^ p := by
    have h1 : α < p := by nlinarith
    exact lt_of_lt_of_le h1 (le_of_lt (Nat.lt_two_pow_self))
  obtain ⟨hszU1, hszV, hszU2, hszD1, hszE, hszA1, hszQ1, hszR1, hszB1, hszD2, hszA2,
    hszQ2, hszR2, hszB2, hszA, hszSq, hszB2sq, hszN, hszA2c, hszA2N, hszP, hszS2⟩ :=
    buZSizes p α s t ℓ h hs hst hα hp htp hαp hℓ hℓs hh
  have hCB : ∀ v ∈ buCB p α s t, vsz v ≤ buSZ p := buCB_small p α s t hs hst hα hp htp hαp
  have hℓz : isz ℓ ≤ buSZ p := buZ_isz_le (A := p) (by simp only [buZBnd]; omega) (by
    refine le_trans (natAbs_le_of ℓ (s : ℤ) (by positivity) (by omega) (by omega)) ?_
    rw [Int.natAbs_natCast]
    exact le_of_lt hsp)
  have hhz : isz h ≤ buSZ p := isz_le_buSZ_pow_p (z := h) (by
    refine le_trans hh (le_trans (egM_le p α) ?_)
    have := Nat.lt_two_pow_self (n := p); omega)
  have hszT0 : isz (t : ℤ) ≤ buSZ p := isz_natCast_lt_buSZ htp
  have hszS0 : isz (s : ℤ) ≤ buSZ p := isz_natCast_lt_buSZ hsp
  have hszAl2 : isz (α : ℤ) ≤ buSZ p := isz_natCast_lt_buSZ hα2p
  have hszPi : isz (auPi p) ≤ buSZ p := isz_auPi_le_buSZ p
  have mP : vsz (Val.int (p : ℤ)) ≤ buSZ p := hCB _ (by simp [buCB])
  have mAl : vsz (Val.int (α : ℤ)) ≤ buSZ p := hCB _ (by simp [buCB])
  have mS : vsz (Val.int (s : ℤ)) ≤ buSZ p := hCB _ (by simp [buCB])
  have mT : vsz (Val.int (t : ℤ)) ≤ buSZ p := hCB _ (by simp [buCB])
  have mM : vsz (Val.int (((egM p α : ℕ) : ℤ))) ≤ buSZ p := hCB _ (by simp [buCB])
  have mN : vsz (Val.int (((egN p α s t : ℕ) : ℤ))) ≤ buSZ p := hCB _ (by simp [buCB])
  have mPi : vsz (Val.int (auPi p)) ≤ buSZ p := hCB _ (by simp [buCB])
  have s1 : Pipe main (pickP 5) ([Val.int ℓ, Val.int h] ++ buCB p α s t) ([Val.int (t : ℤ), Val.int ℓ, Val.int h] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int ℓ, Val.int h] ++ buCB p α s t) (k := 5) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (t : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hℓz) (vsz_mem_le_cons (vsz_int_le_buSZ hhz) (vsz_mem_le_nil))) hCB))

  have t2 : Pipe main mulP ([Val.int (t : ℤ), Val.int ℓ] ++ ([Val.int h] ++ buCB p α s t))
      ([Val.int (((t : ℤ)) * (ℓ))] ++ ([Val.int h] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int h] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (t : ℤ)) (b := ℓ) trivial)
  have s2 : Pipe main mulP ([Val.int (t : ℤ), Val.int ℓ, Val.int h] ++ buCB p α s t) ([Val.int (buZU1 t ℓ), Val.int h] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t2 (le_buSBW_mul hKm (hszT0) (hℓz))

  have s3 : Pipe main (rollP 1) ([Val.int (buZU1 t ℓ), Val.int h] ++ buCB p α s t) ([Val.int h, Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZU1 t ℓ), Val.int h] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_cons (vsz_int_le_buSZ hhz) (vsz_mem_le_nil))) hCB))
    have hV : ([Val.int (buZU1 t ℓ), Val.int h] : List Val).getD 1 .nil = Val.int h := rfl
    have hL : ([Val.int (buZU1 t ℓ), Val.int h] : List Val).eraseIdx 1 = [Val.int (buZU1 t ℓ)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZU1 t ℓ), Val.int h]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZU1 t ℓ), Val.int h]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have s4 : Pipe main (pickP 5) ([Val.int h, Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (t : ℤ), Val.int h, Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int h, Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 5) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (t : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hhz) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))) hCB))

  have t5 : Pipe main mulP ([Val.int (t : ℤ), Val.int h] ++ ([Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((t : ℤ)) * (h))] ++ ([Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (t : ℤ)) (b := h) trivial)
  have s5 : Pipe main mulP ([Val.int (t : ℤ), Val.int h, Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t5 (le_buSBW_mul hKm (hszT0) (hhz))

  have s6 : Pipe main (pickP 0) ([Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZV t h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 0) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (buZV t h))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))) hCB))

  have s7 : Pipe main (pickP 2) ([Val.int (buZV t h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZU1 t ℓ), Val.int (buZV t h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZV t h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (buZU1 t ℓ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil)))) hCB))

  have t8 : Pipe main addP ([Val.int (buZU1 t ℓ), Val.int (buZV t h)] ++ ([Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((buZU1 t ℓ)) + ((buZV t h)))] ++ ([Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZU1 t ℓ)) (b := (buZV t h)) trivial)
  have s8 : Pipe main addP ([Val.int (buZU1 t ℓ), Val.int (buZV t h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t8 (le_buSBW_two hKa (hszU1) (hszV))

  have s9 : Pipe main (pickP 2) ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZU1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (buZU1 t ℓ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil)))) hCB))

  have t10 : Pipe main dupP ([Val.int (buZU1 t ℓ)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (buZU1 t ℓ), Val.int (buZU1 t ℓ)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (buZU1 t ℓ)))
  have s10 : Pipe main dupP ([Val.int (buZU1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZU1 t ℓ), Val.int (buZU1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t10 (le_buSBW_one hKd (vsz_int_le_buSZ hszU1))

  have t11 : Pipe main addP ([Val.int (buZU1 t ℓ), Val.int (buZU1 t ℓ)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((buZU1 t ℓ)) + ((buZU1 t ℓ)))] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZU1 t ℓ)) (b := (buZU1 t ℓ)) trivial)
  have s11 : Pipe main addP ([Val.int (buZU1 t ℓ), Val.int (buZU1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t11 (le_buSBW_two hKa (hszU1) (hszU1))

  have s12 : Pipe main (pickP 6) ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 6) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszD1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))))) hCB))

  have t13 : Pipe main dupP ([Val.int (s : ℤ)] ++ ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (s : ℤ)))
  have s13 : Pipe main dupP ([Val.int (s : ℤ), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t13 (le_buSBW_one hKd (mS))

  have t14 : Pipe main addP ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((s : ℤ)) + ((s : ℤ)))] ++ ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (s : ℤ)) (b := (s : ℤ)) trivial)
  have s14 : Pipe main addP ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t14 (le_buSBW_two hKa (hszS0) (hszS0))

  have s15 : Pipe main (pickP 7) ([Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 7) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszE) (vsz_mem_le_cons (vsz_int_le_buSZ hszD1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil)))))) hCB))

  have s16 : Pipe main (rollP 2) ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZD1 t ℓ), Val.int (s : ℤ), Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (mS) (vsz_mem_le_cons (vsz_int_le_buSZ hszE) (vsz_mem_le_cons (vsz_int_le_buSZ hszD1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))))))) hCB))
    have hV : ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] : List Val).getD 2 .nil = Val.int (buZD1 t ℓ) := rfl
    have hL : ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] : List Val).eraseIdx 2 = [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD1 t ℓ), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t17 : Pipe main addP ([Val.int (buZD1 t ℓ), Val.int (s : ℤ)] ++ ([Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((buZD1 t ℓ)) + ((s : ℤ)))] ++ ([Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZD1 t ℓ)) (b := (s : ℤ)) trivial)
  have s17 : Pipe main addP ([Val.int (buZD1 t ℓ), Val.int (s : ℤ), Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZA1 t ℓ s), Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t17 (le_buSBW_two hKa (hszD1) (hszS0))

  have t18 : Pipe main fdivP ([Val.int (buZA1 t ℓ s), Val.int (buZE s)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (Int.fdiv ((buZA1 t ℓ s)) ((buZE s)))] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hfdiv main) (a := (buZA1 t ℓ s)) (b := (buZE s)) (buZE_pos (by omega)))
  have s18 : Pipe main fdivP ([Val.int (buZA1 t ℓ s), Val.int (buZE s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZQ1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t18 (le_buSBW_mul hKf (hszA1) (hszE))

  have s19 : Pipe main (pickP 6) ([Val.int (buZQ1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZQ1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZQ1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 6) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszQ1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))))) hCB))

  have t20 : Pipe main mulP ([Val.int (s : ℤ), Val.int (buZQ1 t ℓ s)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t))
      ([Val.int (((s : ℤ)) * ((buZQ1 t ℓ s)))] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (s : ℤ)) (b := (buZQ1 t ℓ s)) trivial)
  have s20 : Pipe main mulP ([Val.int (s : ℤ), Val.int (buZQ1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t20 (le_buSBW_mul hKm (hszS0) (hszQ1))

  have s21 : Pipe main (rollP 3) ([Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) ([Val.int (buZU1 t ℓ), Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] ++ buCB p α s t) (k := 3) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszR1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszU1) (vsz_mem_le_nil))))) hCB))
    have hV : ([Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] : List Val).getD 3 .nil = Val.int (buZU1 t ℓ) := rfl
    have hL : ([Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)] : List Val).eraseIdx 3 = [Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)]) (k := 3) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h), Val.int (buZU1 t ℓ)]) (k := 3) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t22 : Pipe main subP ([Val.int (buZU1 t ℓ), Val.int (buZR1 t ℓ s)] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((buZU1 t ℓ)) - ((buZR1 t ℓ s)))] ++ ([Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hsub main) (a := (buZU1 t ℓ)) (b := (buZR1 t ℓ s)) trivial)
  have s22 : Pipe main subP ([Val.int (buZU1 t ℓ), Val.int (buZR1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t22 (le_buSBW_two hKsub (hszU1) (hszR1))

  have s23 : Pipe main (pickP 1) ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZU2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (buZU2 t ℓ h))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil)))) hCB))

  have t24 : Pipe main dupP ([Val.int (buZU2 t ℓ h)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (buZU2 t ℓ h), Val.int (buZU2 t ℓ h)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (buZU2 t ℓ h)))
  have s24 : Pipe main dupP ([Val.int (buZU2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZU2 t ℓ h), Val.int (buZU2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t24 (le_buSBW_one hKd (vsz_int_le_buSZ hszU2))

  have t25 : Pipe main addP ([Val.int (buZU2 t ℓ h), Val.int (buZU2 t ℓ h)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((buZU2 t ℓ h)) + ((buZU2 t ℓ h)))] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZU2 t ℓ h)) (b := (buZU2 t ℓ h)) trivial)
  have s25 : Pipe main addP ([Val.int (buZU2 t ℓ h), Val.int (buZU2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t25 (le_buSBW_two hKa (hszU2) (hszU2))

  have s26 : Pipe main (pickP 6) ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 6) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszD2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil))))) hCB))

  have t27 : Pipe main dupP ([Val.int (s : ℤ)] ++ ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (s : ℤ)))
  have s27 : Pipe main dupP ([Val.int (s : ℤ), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t27 (le_buSBW_one hKd (mS))

  have t28 : Pipe main addP ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((s : ℤ)) + ((s : ℤ)))] ++ ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (s : ℤ)) (b := (s : ℤ)) trivial)
  have s28 : Pipe main addP ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t28 (le_buSBW_two hKa (hszS0) (hszS0))

  have s29 : Pipe main (pickP 7) ([Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 7) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszE) (vsz_mem_le_cons (vsz_int_le_buSZ hszD2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil)))))) hCB))

  have s30 : Pipe main (rollP 2) ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZD2 t ℓ h), Val.int (s : ℤ), Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (mS) (vsz_mem_le_cons (vsz_int_le_buSZ hszE) (vsz_mem_le_cons (vsz_int_le_buSZ hszD2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil))))))) hCB))
    have hV : ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] : List Val).getD 2 .nil = Val.int (buZD2 t ℓ h) := rfl
    have hL : ([Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] : List Val).eraseIdx 2 = [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (s : ℤ), Val.int (buZE s), Val.int (buZD2 t ℓ h), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t31 : Pipe main addP ([Val.int (buZD2 t ℓ h), Val.int (s : ℤ)] ++ ([Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((buZD2 t ℓ h)) + ((s : ℤ)))] ++ ([Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZD2 t ℓ h)) (b := (s : ℤ)) trivial)
  have s31 : Pipe main addP ([Val.int (buZD2 t ℓ h), Val.int (s : ℤ), Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZA2 t ℓ h s), Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t31 (le_buSBW_two hKa (hszD2) (hszS0))

  have t32 : Pipe main fdivP ([Val.int (buZA2 t ℓ h s), Val.int (buZE s)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (Int.fdiv ((buZA2 t ℓ h s)) ((buZE s)))] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hfdiv main) (a := (buZA2 t ℓ h s)) (b := (buZE s)) (buZE_pos (by omega)))
  have s32 : Pipe main fdivP ([Val.int (buZA2 t ℓ h s), Val.int (buZE s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZQ2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t32 (le_buSBW_mul hKf (hszA2) (hszE))

  have s33 : Pipe main (pickP 6) ([Val.int (buZQ2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZQ2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZQ2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 6) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszQ2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil))))) hCB))

  have t34 : Pipe main mulP ([Val.int (s : ℤ), Val.int (buZQ2 t ℓ h s)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((s : ℤ)) * ((buZQ2 t ℓ h s)))] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (s : ℤ)) (b := (buZQ2 t ℓ h s)) trivial)
  have s34 : Pipe main mulP ([Val.int (s : ℤ), Val.int (buZQ2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t34 (le_buSBW_mul hKm (hszS0) (hszQ2))

  have s35 : Pipe main (rollP 2) ([Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZU2 t ℓ h), Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszR2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszU2) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil))))) hCB))
    have hV : ([Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] : List Val).getD 2 .nil = Val.int (buZU2 t ℓ h) := rfl
    have hL : ([Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)] : List Val).eraseIdx 2 = [Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZU2 t ℓ h), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t36 : Pipe main subP ([Val.int (buZU2 t ℓ h), Val.int (buZR2 t ℓ h s)] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t))
      ([Val.int (((buZU2 t ℓ h)) - ((buZR2 t ℓ h s)))] ++ ([Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) (Pipe.binOp (hsub main) (a := (buZU2 t ℓ h)) (b := (buZR2 t ℓ h s)) trivial)
  have s36 : Pipe main subP ([Val.int (buZU2 t ℓ h), Val.int (buZR2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t36 (le_buSBW_two hKsub (hszU2) (hszR2))

  have s37 : Pipe main (rollP 2) ([Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) ([Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszB2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_nil)))) hCB))
    have hV : ([Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] : List Val).getD 2 .nil = Val.int (buZV t h) := rfl
    have hL : ([Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)] : List Val).eraseIdx 2 = [Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s), Val.int (buZV t h)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have s38 : Pipe main (rollP 2) ([Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] ++ buCB p α s t) ([Val.int (buZB1 t ℓ s), Val.int (buZV t h), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszV) (vsz_mem_le_cons (vsz_int_le_buSZ hszB2) (vsz_mem_le_cons (vsz_int_le_buSZ hszB1) (vsz_mem_le_nil)))) hCB))
    have hV : ([Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] : List Val).getD 2 .nil = Val.int (buZB1 t ℓ s) := rfl
    have hL : ([Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)] : List Val).eraseIdx 2 = [Val.int (buZV t h), Val.int (buZB2 t ℓ h s)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZV t h), Val.int (buZB2 t ℓ h s), Val.int (buZB1 t ℓ s)]) (k := 2) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t39 : Pipe main addP ([Val.int (buZB1 t ℓ s), Val.int (buZV t h)] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t))
      ([Val.int (((buZB1 t ℓ s)) + ((buZV t h)))] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (Pipe.binOp (hadd main) (a := (buZB1 t ℓ s)) (b := (buZV t h)) trivial)
  have s39 : Pipe main addP ([Val.int (buZB1 t ℓ s), Val.int (buZV t h), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) ([Val.int (buZA t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t39 (le_buSBW_two hKa (hszB1) (hszV))

  have t40 : Pipe main dupP ([Val.int (buZA t ℓ h s)] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t))
      ([Val.int (buZA t ℓ h s), Val.int (buZA t ℓ h s)] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (buZA t ℓ h s)))
  have s40 : Pipe main dupP ([Val.int (buZA t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) ([Val.int (buZA t ℓ h s), Val.int (buZA t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t40 (le_buSBW_one hKd (vsz_int_le_buSZ hszA))

  have t41 : Pipe main mulP ([Val.int (buZA t ℓ h s), Val.int (buZA t ℓ h s)] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t))
      ([Val.int (((buZA t ℓ h s)) * ((buZA t ℓ h s)))] ++ ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (buZA t ℓ h s)) (b := (buZA t ℓ h s)) trivial)
  have s41 : Pipe main mulP ([Val.int (buZA t ℓ h s), Val.int (buZA t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) ([Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t41 (le_buSBW_mul hKm (hszA) (hszA))

  have s42 : Pipe main (rollP 1) ([Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) ([Val.int (buZB2 t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszSq) (vsz_mem_le_cons (vsz_int_le_buSZ hszB2) (vsz_mem_le_nil))) hCB))
    have hV : ([Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)] : List Val).getD 1 .nil = Val.int (buZB2 t ℓ h s) := rfl
    have hL : ([Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)] : List Val).eraseIdx 1 = [Val.int (buZSq t ℓ h s)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZSq t ℓ h s), Val.int (buZB2 t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t43 : Pipe main dupP ([Val.int (buZB2 t ℓ h s)] ++ ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t))
      ([Val.int (buZB2 t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (buZB2 t ℓ h s)))
  have s43 : Pipe main dupP ([Val.int (buZB2 t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) ([Val.int (buZB2 t ℓ h s), Val.int (buZB2 t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t43 (le_buSBW_one hKd (vsz_int_le_buSZ hszB2))

  have t44 : Pipe main mulP ([Val.int (buZB2 t ℓ h s), Val.int (buZB2 t ℓ h s)] ++ ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t))
      ([Val.int (((buZB2 t ℓ h s)) * ((buZB2 t ℓ h s)))] ++ ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (buZB2 t ℓ h s)) (b := (buZB2 t ℓ h s)) trivial)
  have s44 : Pipe main mulP ([Val.int (buZB2 t ℓ h s), Val.int (buZB2 t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) ([Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t44 (le_buSBW_mul hKm (hszB2) (hszB2))

  have s45 : Pipe main (rollP 1) ([Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) ([Val.int (buZSq t ℓ h s), Val.int (buZB2sq t ℓ h s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszB2sq) (vsz_mem_le_cons (vsz_int_le_buSZ hszSq) (vsz_mem_le_nil))) hCB))
    have hV : ([Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)] : List Val).getD 1 .nil = Val.int (buZSq t ℓ h s) := rfl
    have hL : ([Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)] : List Val).eraseIdx 1 = [Val.int (buZB2sq t ℓ h s)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZB2sq t ℓ h s), Val.int (buZSq t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t46 : Pipe main subP ([Val.int (buZSq t ℓ h s), Val.int (buZB2sq t ℓ h s)] ++ (buCB p α s t))
      ([Val.int (((buZSq t ℓ h s)) - ((buZB2sq t ℓ h s)))] ++ (buCB p α s t)) _ :=
    Pipe.appendTail (buCB p α s t) (Pipe.binOp (hsub main) (a := (buZSq t ℓ h s)) (b := (buZB2sq t ℓ h s)) trivial)
  have s46 : Pipe main subP ([Val.int (buZSq t ℓ h s), Val.int (buZB2sq t ℓ h s)] ++ buCB p α s t) ([Val.int (buZN t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t46 (le_buSBW_two hKsub (hszSq) (hszB2sq))

  have s47 : Pipe main (pickP 2) ([Val.int (buZN t ℓ h s)] ++ buCB p α s t) ([Val.int (α : ℤ), Val.int (buZN t ℓ h s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZN t ℓ h s)] ++ buCB p α s t) (k := 2) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (α : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszN) (vsz_mem_le_nil)) hCB))

  have t48 : Pipe main dupP ([Val.int (α : ℤ)] ++ ([Val.int (buZN t ℓ h s)] ++ buCB p α s t))
      ([Val.int (α : ℤ), Val.int (α : ℤ)] ++ ([Val.int (buZN t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZN t ℓ h s)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (α : ℤ)))
  have s48 : Pipe main dupP ([Val.int (α : ℤ), Val.int (buZN t ℓ h s)] ++ buCB p α s t) ([Val.int (α : ℤ), Val.int (α : ℤ), Val.int (buZN t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t48 (le_buSBW_one hKd (mAl))

  have t49 : Pipe main mulP ([Val.int (α : ℤ), Val.int (α : ℤ)] ++ ([Val.int (buZN t ℓ h s)] ++ buCB p α s t))
      ([Val.int (((α : ℤ)) * ((α : ℤ)))] ++ ([Val.int (buZN t ℓ h s)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZN t ℓ h s)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (α : ℤ)) (b := (α : ℤ)) trivial)
  have s49 : Pipe main mulP ([Val.int (α : ℤ), Val.int (α : ℤ), Val.int (buZN t ℓ h s)] ++ buCB p α s t) ([Val.int (buZA2c α), Val.int (buZN t ℓ h s)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t49 (le_buSBW_mul hKm (hszAl2) (hszAl2))

  have s50 : Pipe main (rollP 1) ([Val.int (buZA2c α), Val.int (buZN t ℓ h s)] ++ buCB p α s t) ([Val.int (buZN t ℓ h s), Val.int (buZA2c α)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZA2c α), Val.int (buZN t ℓ h s)] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszA2c) (vsz_mem_le_cons (vsz_int_le_buSZ hszN) (vsz_mem_le_nil))) hCB))
    have hV : ([Val.int (buZA2c α), Val.int (buZN t ℓ h s)] : List Val).getD 1 .nil = Val.int (buZN t ℓ h s) := rfl
    have hL : ([Val.int (buZA2c α), Val.int (buZN t ℓ h s)] : List Val).eraseIdx 1 = [Val.int (buZA2c α)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZA2c α), Val.int (buZN t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZA2c α), Val.int (buZN t ℓ h s)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t51 : Pipe main mulP ([Val.int (buZN t ℓ h s), Val.int (buZA2c α)] ++ (buCB p α s t))
      ([Val.int (((buZN t ℓ h s)) * ((buZA2c α)))] ++ (buCB p α s t)) _ :=
    Pipe.appendTail (buCB p α s t) (Pipe.binOp (hmul main) (a := (buZN t ℓ h s)) (b := (buZA2c α)) trivial)
  have s51 : Pipe main mulP ([Val.int (buZN t ℓ h s), Val.int (buZA2c α)] ++ buCB p α s t) ([Val.int (buZA2N t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t51 (le_buSBW_mul hKm (hszN) (hszA2c))

  have s52 : Pipe main (pickP 7) ([Val.int (buZA2N t ℓ h s α)] ++ buCB p α s t) ([Val.int (auPi p), Val.int (buZA2N t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZA2N t ℓ h s α)] ++ buCB p α s t) (k := 7) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (auPi p))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszA2N) (vsz_mem_le_nil)) hCB))

  have t53 : Pipe main mulP ([Val.int (auPi p), Val.int (buZA2N t ℓ h s α)] ++ (buCB p α s t))
      ([Val.int (((auPi p)) * ((buZA2N t ℓ h s α)))] ++ (buCB p α s t)) _ :=
    Pipe.appendTail (buCB p α s t) (Pipe.binOp (hmul main) (a := (auPi p)) (b := (buZA2N t ℓ h s α)) trivial)
  have s53 : Pipe main mulP ([Val.int (auPi p), Val.int (buZA2N t ℓ h s α)] ++ buCB p α s t) ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t53 (le_buSBW_mul hKm (hszPi) (hszA2N))

  have s54 : Pipe main (pickP 3) ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.pickAt main hpick (A := [Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (k := 3) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)
      (v := Val.int (s : ℤ))
      (by rw [buCB]; rfl))
      (le_buSBW_roll hKpick (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszP) (vsz_mem_le_nil)) hCB))

  have t55 : Pipe main dupP ([Val.int (s : ℤ)] ++ ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t))
      ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (Pipe.dup main hdup (Val.int (s : ℤ)))
  have s55 : Pipe main dupP ([Val.int (s : ℤ), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t55 (le_buSBW_one hKd (mS))

  have t56 : Pipe main mulP ([Val.int (s : ℤ), Val.int (s : ℤ)] ++ ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t))
      ([Val.int (((s : ℤ)) * ((s : ℤ)))] ++ ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t)) _ :=
    Pipe.appendTail ([Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (Pipe.binOp (hmul main) (a := (s : ℤ)) (b := (s : ℤ)) trivial)
  have s56 : Pipe main mulP ([Val.int (s : ℤ), Val.int (s : ℤ), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) ([Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t56 (le_buSBW_mul hKm (hszS0) (hszS0))

  have s57 : Pipe main (rollP 1) ([Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) ([Val.int (buZP p t ℓ h s α), Val.int (buZS2 s)] ++ buCB p α s t) (buSBW p KS) := by
    refine Pipe.le (Pipe.rw (Pipe.roll main hroll (A := [Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)] ++ buCB p α s t) (k := 1) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega)) ?_)
      (le_buSBW_roll hKroll (by omega) (by rw [List.length_append, buCB]; simp only [List.length_cons, List.length_nil]; omega) (vsz_mem_le_append (vsz_mem_le_cons (vsz_int_le_buSZ hszS2) (vsz_mem_le_cons (vsz_int_le_buSZ hszP) (vsz_mem_le_nil))) hCB))
    have hV : ([Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)] : List Val).getD 1 .nil = Val.int (buZP p t ℓ h s α) := rfl
    have hL : ([Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)] : List Val).eraseIdx 1 = [Val.int (buZS2 s)] := rfl
    rw [Work.Fx.getD_append_of_lt (l := [Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega),
      Work.Fx.eraseIdx_append_of_lt (l := [Val.int (buZS2 s), Val.int (buZP p t ℓ h s α)]) (k := 1) (by simp only [List.length_cons, List.length_nil]; omega), hV, hL]
    rfl

  have t58 : Pipe main tdivP ([Val.int (buZP p t ℓ h s α), Val.int (buZS2 s)] ++ (buCB p α s t))
      ([Val.int (Int.tdiv ((buZP p t ℓ h s α)) ((buZS2 s)))] ++ (buCB p α s t)) _ :=
    Pipe.appendTail (buCB p α s t) (Pipe.binOp (htdiv main) (a := (buZP p t ℓ h s α)) (b := (buZS2 s)) (buZS2_ne_zero (by omega)))
  have s58 : Pipe main tdivP ([Val.int (buZP p t ℓ h s α), Val.int (buZS2 s)] ++ buCB p α s t) ([Val.int (buZZ p α s t ℓ h)] ++ buCB p α s t) (buSBW p KS) :=
    Pipe.le t58 (le_buSBW_mul hKt (hszP) (hszS2))

  have g58 := s58
  have g57 : Pipe main _ _ _ (2 * buSBW p KS) := Pipe.le (Pipe.comp s57 g58) (by exact Nat.le_of_eq (by ring))
  have g56 : Pipe main _ _ _ (3 * buSBW p KS) := Pipe.le (Pipe.comp s56 g57) (by exact Nat.le_of_eq (by ring))
  have g55 : Pipe main _ _ _ (4 * buSBW p KS) := Pipe.le (Pipe.comp s55 g56) (by exact Nat.le_of_eq (by ring))
  have g54 : Pipe main _ _ _ (5 * buSBW p KS) := Pipe.le (Pipe.comp s54 g55) (by exact Nat.le_of_eq (by ring))
  have g53 : Pipe main _ _ _ (6 * buSBW p KS) := Pipe.le (Pipe.comp s53 g54) (by exact Nat.le_of_eq (by ring))
  have g52 : Pipe main _ _ _ (7 * buSBW p KS) := Pipe.le (Pipe.comp s52 g53) (by exact Nat.le_of_eq (by ring))
  have g51 : Pipe main _ _ _ (8 * buSBW p KS) := Pipe.le (Pipe.comp s51 g52) (by exact Nat.le_of_eq (by ring))
  have g50 : Pipe main _ _ _ (9 * buSBW p KS) := Pipe.le (Pipe.comp s50 g51) (by exact Nat.le_of_eq (by ring))
  have g49 : Pipe main _ _ _ (10 * buSBW p KS) := Pipe.le (Pipe.comp s49 g50) (by exact Nat.le_of_eq (by ring))
  have g48 : Pipe main _ _ _ (11 * buSBW p KS) := Pipe.le (Pipe.comp s48 g49) (by exact Nat.le_of_eq (by ring))
  have g47 : Pipe main _ _ _ (12 * buSBW p KS) := Pipe.le (Pipe.comp s47 g48) (by exact Nat.le_of_eq (by ring))
  have g46 : Pipe main _ _ _ (13 * buSBW p KS) := Pipe.le (Pipe.comp s46 g47) (by exact Nat.le_of_eq (by ring))
  have g45 : Pipe main _ _ _ (14 * buSBW p KS) := Pipe.le (Pipe.comp s45 g46) (by exact Nat.le_of_eq (by ring))
  have g44 : Pipe main _ _ _ (15 * buSBW p KS) := Pipe.le (Pipe.comp s44 g45) (by exact Nat.le_of_eq (by ring))
  have g43 : Pipe main _ _ _ (16 * buSBW p KS) := Pipe.le (Pipe.comp s43 g44) (by exact Nat.le_of_eq (by ring))
  have g42 : Pipe main _ _ _ (17 * buSBW p KS) := Pipe.le (Pipe.comp s42 g43) (by exact Nat.le_of_eq (by ring))
  have g41 : Pipe main _ _ _ (18 * buSBW p KS) := Pipe.le (Pipe.comp s41 g42) (by exact Nat.le_of_eq (by ring))
  have g40 : Pipe main _ _ _ (19 * buSBW p KS) := Pipe.le (Pipe.comp s40 g41) (by exact Nat.le_of_eq (by ring))
  have g39 : Pipe main _ _ _ (20 * buSBW p KS) := Pipe.le (Pipe.comp s39 g40) (by exact Nat.le_of_eq (by ring))
  have g38 : Pipe main _ _ _ (21 * buSBW p KS) := Pipe.le (Pipe.comp s38 g39) (by exact Nat.le_of_eq (by ring))
  have g37 : Pipe main _ _ _ (22 * buSBW p KS) := Pipe.le (Pipe.comp s37 g38) (by exact Nat.le_of_eq (by ring))
  have g36 : Pipe main _ _ _ (23 * buSBW p KS) := Pipe.le (Pipe.comp s36 g37) (by exact Nat.le_of_eq (by ring))
  have g35 : Pipe main _ _ _ (24 * buSBW p KS) := Pipe.le (Pipe.comp s35 g36) (by exact Nat.le_of_eq (by ring))
  have g34 : Pipe main _ _ _ (25 * buSBW p KS) := Pipe.le (Pipe.comp s34 g35) (by exact Nat.le_of_eq (by ring))
  have g33 : Pipe main _ _ _ (26 * buSBW p KS) := Pipe.le (Pipe.comp s33 g34) (by exact Nat.le_of_eq (by ring))
  have g32 : Pipe main _ _ _ (27 * buSBW p KS) := Pipe.le (Pipe.comp s32 g33) (by exact Nat.le_of_eq (by ring))
  have g31 : Pipe main _ _ _ (28 * buSBW p KS) := Pipe.le (Pipe.comp s31 g32) (by exact Nat.le_of_eq (by ring))
  have g30 : Pipe main _ _ _ (29 * buSBW p KS) := Pipe.le (Pipe.comp s30 g31) (by exact Nat.le_of_eq (by ring))
  have g29 : Pipe main _ _ _ (30 * buSBW p KS) := Pipe.le (Pipe.comp s29 g30) (by exact Nat.le_of_eq (by ring))
  have g28 : Pipe main _ _ _ (31 * buSBW p KS) := Pipe.le (Pipe.comp s28 g29) (by exact Nat.le_of_eq (by ring))
  have g27 : Pipe main _ _ _ (32 * buSBW p KS) := Pipe.le (Pipe.comp s27 g28) (by exact Nat.le_of_eq (by ring))
  have g26 : Pipe main _ _ _ (33 * buSBW p KS) := Pipe.le (Pipe.comp s26 g27) (by exact Nat.le_of_eq (by ring))
  have g25 : Pipe main _ _ _ (34 * buSBW p KS) := Pipe.le (Pipe.comp s25 g26) (by exact Nat.le_of_eq (by ring))
  have g24 : Pipe main _ _ _ (35 * buSBW p KS) := Pipe.le (Pipe.comp s24 g25) (by exact Nat.le_of_eq (by ring))
  have g23 : Pipe main _ _ _ (36 * buSBW p KS) := Pipe.le (Pipe.comp s23 g24) (by exact Nat.le_of_eq (by ring))
  have g22 : Pipe main _ _ _ (37 * buSBW p KS) := Pipe.le (Pipe.comp s22 g23) (by exact Nat.le_of_eq (by ring))
  have g21 : Pipe main _ _ _ (38 * buSBW p KS) := Pipe.le (Pipe.comp s21 g22) (by exact Nat.le_of_eq (by ring))
  have g20 : Pipe main _ _ _ (39 * buSBW p KS) := Pipe.le (Pipe.comp s20 g21) (by exact Nat.le_of_eq (by ring))
  have g19 : Pipe main _ _ _ (40 * buSBW p KS) := Pipe.le (Pipe.comp s19 g20) (by exact Nat.le_of_eq (by ring))
  have g18 : Pipe main _ _ _ (41 * buSBW p KS) := Pipe.le (Pipe.comp s18 g19) (by exact Nat.le_of_eq (by ring))
  have g17 : Pipe main _ _ _ (42 * buSBW p KS) := Pipe.le (Pipe.comp s17 g18) (by exact Nat.le_of_eq (by ring))
  have g16 : Pipe main _ _ _ (43 * buSBW p KS) := Pipe.le (Pipe.comp s16 g17) (by exact Nat.le_of_eq (by ring))
  have g15 : Pipe main _ _ _ (44 * buSBW p KS) := Pipe.le (Pipe.comp s15 g16) (by exact Nat.le_of_eq (by ring))
  have g14 : Pipe main _ _ _ (45 * buSBW p KS) := Pipe.le (Pipe.comp s14 g15) (by exact Nat.le_of_eq (by ring))
  have g13 : Pipe main _ _ _ (46 * buSBW p KS) := Pipe.le (Pipe.comp s13 g14) (by exact Nat.le_of_eq (by ring))
  have g12 : Pipe main _ _ _ (47 * buSBW p KS) := Pipe.le (Pipe.comp s12 g13) (by exact Nat.le_of_eq (by ring))
  have g11 : Pipe main _ _ _ (48 * buSBW p KS) := Pipe.le (Pipe.comp s11 g12) (by exact Nat.le_of_eq (by ring))
  have g10 : Pipe main _ _ _ (49 * buSBW p KS) := Pipe.le (Pipe.comp s10 g11) (by exact Nat.le_of_eq (by ring))
  have g9 : Pipe main _ _ _ (50 * buSBW p KS) := Pipe.le (Pipe.comp s9 g10) (by exact Nat.le_of_eq (by ring))
  have g8 : Pipe main _ _ _ (51 * buSBW p KS) := Pipe.le (Pipe.comp s8 g9) (by exact Nat.le_of_eq (by ring))
  have g7 : Pipe main _ _ _ (52 * buSBW p KS) := Pipe.le (Pipe.comp s7 g8) (by exact Nat.le_of_eq (by ring))
  have g6 : Pipe main _ _ _ (53 * buSBW p KS) := Pipe.le (Pipe.comp s6 g7) (by exact Nat.le_of_eq (by ring))
  have g5 : Pipe main _ _ _ (54 * buSBW p KS) := Pipe.le (Pipe.comp s5 g6) (by exact Nat.le_of_eq (by ring))
  have g4 : Pipe main _ _ _ (55 * buSBW p KS) := Pipe.le (Pipe.comp s4 g5) (by exact Nat.le_of_eq (by ring))
  have g3 : Pipe main _ _ _ (56 * buSBW p KS) := Pipe.le (Pipe.comp s3 g4) (by exact Nat.le_of_eq (by ring))
  have g2 : Pipe main _ _ _ (57 * buSBW p KS) := Pipe.le (Pipe.comp s2 g3) (by exact Nat.le_of_eq (by ring))
  have g1 : Pipe main _ _ _ (58 * buSBW p KS) := Pipe.le (Pipe.comp s1 g2) (by exact Nat.le_of_eq (by ring))
  refine Pipe.le (Pipe.rw g1 ?_) ?_
  · rw [buZZ_eq_buZ p α s t ℓ h hs0e]
  · calc 58 * buSBW p KS ≤ 58 * ((KS * 1000000 ^ 2) * (p + 1) ^ 4) :=
        Nat.mul_le_mul_left _ (buSBW_le_pow p KS)
      _ = (58 * KS * 1000000 ^ 2) * (p + 1) ^ 4 := by ring
      _ ≤ (8 * (58 * KS * 1000000 ^ 2 + 4) + 8) * (p + 1) ^ (8 * (58 * KS * 1000000 ^ 2 + 4) + 8) :=
        le_powK (p := p) (c := 58 * KS * 1000000 ^ 2) (d := 4) hp2e hc1e

end Work.Resample
