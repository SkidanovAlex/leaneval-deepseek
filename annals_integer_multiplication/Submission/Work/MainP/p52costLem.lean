import Mathlib
import Submission.Work.MainP.p52helpers

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MainP

open HvdH

/-! ## Helper lemmas for the final cost arithmetic of paper Prop 5.2 -/

/-- Size bound for a list of naturals: if every entry has bit-size `≤ p`, then the encoded list of
values has size at most `length * (p + 3)` (before the `+2` of `vsz_intList_le`). -/
theorem sum_map_size_le (l : List ℕ) {p : ℕ} (h : ∀ t ∈ l, t.size ≤ p) :
    (l.map fun t => t.size + 3).sum ≤ l.length * (p + 3) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a.size + 3 ≤ p + 3 := by have := h a (by simp); omega
    have ht : ∀ b ∈ t, b.size ≤ p := fun b hb => h b (by simp [hb])
    have iht := ih ht
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith [ha, iht]

/-- `resCost` is monotone in the cost constant `K` (with `Cm` monotone). -/
theorem resCostMono {Cm : ℕ → ℕ} (hC : Monotone Cm) {K K' : ℕ} (h : K ≤ K')
    (p α : ℕ) (ts : List ℕ) : HvdH.resCost K Cm p α ts ≤ HvdH.resCost K' Cm p α ts := by
  simp only [HvdH.resCost]
  have h1 : Cm (K * p) ≤ Cm (K' * p) := hC (Nat.mul_le_mul_right p h)
  have h2 : K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) ≤
      K' * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K' * p) + p) := by
    gcongr
  have h3 : K * ts.prod * p ^ 2 ≤ K' * ts.prod * p ^ 2 := by gcongr
  have h4 : K * ts.sum * (p + 1) ^ K ≤ K' * ts.sum * (p + 1) ^ K' := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul h le_rfl
    · exact Nat.pow_le_pow_right (by omega) h
  exact add_le_add (add_le_add h2 h3) h4

/-- The uniform encoding-size bound `SB0` is at most `200·T·p` (`T = ts.prod`). -/
theorem sb0_le {p α : ℕ} {ss ts : List ℕ}
    (hPow : HvdH.PowTwoParams p ts) (hRes : HvdH.ResParams p α ss ts)
    (hSsT : ss.prod ≤ ts.prod) (hT : 3 * HvdH.D * p ^ 2 < ts.prod) :
    Work.MainP.SB0 p α ss ts ≤ 200 * ts.prod * p := by
  have hD : HvdH.D = 1729 := rfl
  have hp : 100 ≤ p := hPow.2.2.2.2
  have hp1 : 1 ≤ p := by omega
  have hclause := hRes.2.2.2.2.2
  have hsp : ∀ s ∈ ss, s.size ≤ p := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    have hiD : i < HvdH.D := by rw [← hRes.1]; exact hi
    have hiT : i < ts.length := by rw [hRes.2.1]; exact hiD
    have h1 := (hclause i hiD).2.2.1
    have h2 := (hclause i hiD).2.1
    rw [List.getD_eq_getElem ss 0 hi] at h2
    rw [List.getD_eq_getElem ts 0 hiT] at h1 h2
    exact Nat.size_le.mpr (lt_trans h2 h1)
  have htp : ∀ t ∈ ts, t.size ≤ p := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hiD : i < HvdH.D := by rw [← hRes.2.1]; exact hi
    have h1 := (hclause i hiD).2.2.1
    rw [List.getD_eq_getElem ts 0 hi] at h1
    exact Nat.size_le.mpr h1
  have hsum_ss : (ss.map fun t => t.size + 3).sum ≤ ss.length * (p + 3) :=
    sum_map_size_le ss hsp
  have hsum_ts : (ts.map fun t => t.size + 3).sum ≤ ts.length * (p + 3) :=
    sum_map_size_le ts htp
  have hss : vsz (intList ss) ≤ 1729 * (p + 4) + 2 := by
    have h := Work.ConvR.vsz_intList_le ss
    rw [hRes.1] at h
    rw [hRes.1] at hsum_ss
    nlinarith [h, hsum_ss]
  have hts : vsz (intList ts) ≤ 1729 * (p + 4) + 2 := by
    have h := Work.ConvR.vsz_intList_le ts
    rw [hRes.2.1] at h
    rw [hRes.2.1] at hsum_ts
    nlinarith [h, hsum_ts]
  have hαp : α ^ 2 < p := hRes.2.2.2.2.1
  have hα2 : 2 ≤ α := hRes.2.2.2.1
  have hcvec : Work.ConvR.cvecSz p ss.prod ≤ ts.prod * (2 * p + 9) + 1 := by
    simp only [Work.ConvR.cvecSz, Work.ConvR.cfxSz]
    nlinarith [hSsT]
  have hiszp : isz (p : ℤ) ≤ p + 2 := by
    have h : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [isz, Int.natAbs_natCast]
    omega
  have hiszα : isz (α : ℤ) ≤ p + 2 := by
    have hα1 : 1 ≤ α := by omega
    have hαα : α ≤ α ^ 2 := by
      have h := Nat.mul_le_mul_left α hα1
      simpa [pow_two] using h
    have hlt : α < 2 ^ p := lt_trans (lt_of_le_of_lt hαα hαp) Nat.lt_two_pow_self
    have h : α.size ≤ p := Nat.size_le.mpr hlt
    simp only [isz, Int.natAbs_natCast]
    omega
  have hiszγ : isz (2 ^ (2 * HvdH.D * α ^ 2) : ℤ) ≤ 3458 * p + 3 := by
    have he : 2 * HvdH.D * α ^ 2 ≤ 3458 * p := by
      rw [hD]
      nlinarith [hαp]
    have hb : (2 : ℤ).natAbs = 2 := by norm_num
    have hle : (2 ^ (2 * HvdH.D * α ^ 2) : ℤ).natAbs ≤ 2 ^ (3458 * p) := by
      rw [Int.natAbs_pow, hb]
      exact Nat.pow_le_pow_right (by norm_num) he
    exact Work.ConvR.isz_le_of_natAbs_le hle
  have hbound : Work.ConvR.cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) +
      isz (p : ℤ) + isz (α : ℤ) + isz (2 ^ (2 * HvdH.D * α ^ 2) : ℤ) + 1 ≤
      ts.prod * (2 * p + 9) + 6918 * p + 13845 := by
    nlinarith [hcvec, hss, hts, hiszp, hiszα, hiszγ]
  have hT' : 5187 * p ^ 2 ≤ ts.prod := by
    have h3 := hT
    rw [hD] at h3
    nlinarith [h3]
  have hp_sq : p ≤ p * p := by
    have h := Nat.mul_le_mul_left p hp1
    simpa using h
  have hT'' : 5187 * (p * p) ≤ ts.prod := by
    have h := hT'
    simpa [pow_two] using h
  simp only [Work.MainP.SB0]
  calc 8 * (Work.ConvR.cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) +
        isz (p : ℤ) + isz (α : ℤ) + isz (2 ^ (2 * HvdH.D * α ^ 2) : ℤ) + 1)
      ≤ 8 * (ts.prod * (2 * p + 9) + 6918 * p + 13845) := Nat.mul_le_mul_left 8 hbound
    _ ≤ 200 * ts.prod * p := by
        have h1 : 8 * (ts.prod * (2 * p + 9)) ≤ 88 * (ts.prod * p) := by
          have h88 : 8 * (2 * p + 9) ≤ 88 * p := by omega
          calc 8 * (ts.prod * (2 * p + 9)) = ts.prod * (8 * (2 * p + 9)) := by ring
            _ ≤ ts.prod * (88 * p) := Nat.mul_le_mul_left ts.prod h88
            _ = 88 * (ts.prod * p) := by ring
        have h2 : 8 * (6918 * p + 13845) ≤ 112 * (ts.prod * p) := by
          have hpc : p ≤ p * p * p := by
            have h := Nat.mul_le_mul_right p hp_sq
            exact le_trans hp_sq h
          have hstep : 112 * ((5187 * p ^ 2) * p) ≤ 112 * (ts.prod * p) :=
            Nat.mul_le_mul_left 112 (Nat.mul_le_mul_right p hT')
          have h3 : 8 * (6918 * p + 13845) ≤ 112 * ((5187 * p ^ 2) * p) := by
            nlinarith [hp1, hpc]
          exact le_trans h3 hstep
        nlinarith [h1, h2]

/-- Pure arithmetic core of the final cost comparison: the uniform allowance together with the
`sgn`-branch overhead and the scaling/conjugation words is absorbed by `Kf·T·p²`. -/
theorem arithCore {KB Kf Ktr Ksv Kcj p T S SB Pm : ℕ}
    (hp : 1 ≤ p) (hT : 1 ≤ T) (hS : S ≤ T)
    (hSB : SB ≤ 200 * T * p) (hPm : Pm ≤ 200 * T * p)
    (hKtr : Ktr ≤ KB) (hKsv : Ksv ≤ KB) (hKcj : Kcj ≤ KB)
    (hKf : Kf = 1000000000000000000 * (KB + 1) * (KB + 1) + 1000000000000000000) :
    44 * ALLOW KB SB Pm + 5 * KB + Ktr * T * p ^ 2 +
      (Ksv * (S + 1) * (p + 1) ^ 2 + Ksv) + 2 * (Kcj * (S + 1) * (p + 1) + Kcj)
      ≤ Kf * T * p ^ 2 := by
  have hTp1 : 1 ≤ T * p := by
    have h := Nat.mul_le_mul hT hp
    simpa using h
  have hp2pow : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp
  have hTp2 : 1 ≤ T * p ^ 2 := by
    have h := Nat.mul_le_mul hT hp2pow
    simpa using h
  have hS1 : S + 1 ≤ 2 * T := by omega
  have hpp : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by
    have h1 : p + 1 ≤ 2 * p := by omega
    have h2 : (p + 1) * (p + 1) ≤ (2 * p) * (2 * p) := Nat.mul_le_mul h1 h1
    nlinarith [h2]
  have hSB1 : SB + 1 + Pm ≤ 401 * (T * p) := by
    have h : SB + Pm ≤ 400 * (T * p) := by nlinarith [hSB, hPm]
    nlinarith [h, hTp1]
  -- the uniform allowance
  have hA : 44 * ALLOW KB SB Pm ≤ 17644000000 * ((KB + 1) * (T * p ^ 2)) := by
    simp only [ALLOW]
    have hp_le : p ≤ p * p := by
      have h := Nat.mul_le_mul_left p hp
      simpa using h
    have h1 : 1000000 * (KB + 1) * (SB + 1 + Pm) ≤ 1000000 * (KB + 1) * (401 * (T * p)) :=
      Nat.mul_le_mul_left (1000000 * (KB + 1)) hSB1
    have h2 : 1000000 * (KB + 1) * (401 * (T * p)) ≤
        1000000 * (KB + 1) * (401 * (T * p ^ 2)) := by
      have h := Nat.mul_le_mul_left T hp_le
      have h' : 401 * (T * p) ≤ 401 * (T * p ^ 2) := Nat.mul_le_mul_left 401 (by simpa [pow_two] using h)
      exact Nat.mul_le_mul_left (1000000 * (KB + 1)) h'
    have h3 : 44 * (1000000 * (KB + 1) * (401 * (T * p ^ 2))) =
        17644000000 * ((KB + 1) * (T * p ^ 2)) := by ring
    calc 44 * (1000000 * (KB + 1) * (SB + 1 + Pm))
        ≤ 44 * (1000000 * (KB + 1) * (401 * (T * p))) := Nat.mul_le_mul_left 44 h1
      _ ≤ 44 * (1000000 * (KB + 1) * (401 * (T * p ^ 2))) := Nat.mul_le_mul_left 44 h2
      _ = 17644000000 * ((KB + 1) * (T * p ^ 2)) := h3
  -- the `sgn`-branch overhead
  have h5 : 5 * KB ≤ 5 * ((KB + 1) * (T * p ^ 2)) := by
    have hle : KB ≤ (KB + 1) * (T * p ^ 2) := by
      have h1 : KB ≤ KB * (T * p ^ 2) := by
        have h := Nat.mul_le_mul_left KB hTp2
        rwa [Nat.mul_one KB] at h
      exact le_trans h1 (Nat.mul_le_mul_right (T * p ^ 2) (Nat.le_succ KB))
    exact Nat.mul_le_mul_left 5 hle
  -- the transform's `Ktr·T·p²` term
  have hKtrT : Ktr * T * p ^ 2 ≤ (KB + 1) * (T * p ^ 2) := by
    have h1 : Ktr ≤ KB + 1 := le_trans hKtr (Nat.le_succ KB)
    calc Ktr * T * p ^ 2 = Ktr * (T * p ^ 2) := by ring
      _ ≤ (KB + 1) * (T * p ^ 2) := Nat.mul_le_mul_right (T * p ^ 2) h1
  -- the scaling word
  have hSV : Ksv * (S + 1) * (p + 1) ^ 2 + Ksv ≤ 9 * ((KB + 1) * (T * p ^ 2)) := by
    have h1 : Ksv * (S + 1) * (p + 1) ^ 2 ≤ 8 * (KB * (T * p ^ 2)) := by
      have hmm := Nat.mul_le_mul (Nat.mul_le_mul hKsv hS1) hpp
      nlinarith [hmm]
    have h2 : Ksv ≤ KB * (T * p ^ 2) := by
      have ha : Ksv ≤ Ksv * (T * p ^ 2) := by
        have h := Nat.mul_le_mul_left Ksv hTp2
        rwa [Nat.mul_one Ksv] at h
      exact le_trans ha (Nat.mul_le_mul_right (T * p ^ 2) hKsv)
    nlinarith [h1, h2]
  -- the two conjugation words
  have hCJ : 2 * (Kcj * (S + 1) * (p + 1) + Kcj) ≤ 10 * ((KB + 1) * (T * p ^ 2)) := by
    have hp1' : p + 1 ≤ 2 * p := by omega
    have h1 : Kcj * (S + 1) * (p + 1) ≤ 4 * (KB * (T * p)) := by
      have hmm := Nat.mul_le_mul (Nat.mul_le_mul hKcj hS1) hp1'
      nlinarith [hmm]
    have h2 : Kcj ≤ KB * (T * p ^ 2) := by
      have ha : Kcj ≤ Kcj * (T * p ^ 2) := by
        have h := Nat.mul_le_mul_left Kcj hTp2
        rwa [Nat.mul_one Kcj] at h
      exact le_trans ha (Nat.mul_le_mul_right (T * p ^ 2) hKcj)
    have h3 : KB * (T * p) ≤ KB * (T * p ^ 2) := by
      have hp_le : p ≤ p * p := by
        have h := Nat.mul_le_mul_left p hp
        simpa using h
      have h := Nat.mul_le_mul_left T hp_le
      exact Nat.mul_le_mul_left KB (by simpa [pow_two] using h)
    nlinarith [h1, h2, h3]
  -- absorb by `Kf · T · p²`
  have hU : 17644000025 * ((KB + 1) * (T * p ^ 2)) ≤ Kf * (T * p ^ 2) := by
    have hKB1 : 1 ≤ KB + 1 := by omega
    have hsq : KB + 1 ≤ (KB + 1) * (KB + 1) := by
      calc KB + 1 = (KB + 1) * 1 := (Nat.mul_one (KB + 1)).symm
        _ ≤ (KB + 1) * (KB + 1) := Nat.mul_le_mul_left (KB + 1) hKB1
    have hbig : 17644000025 * (KB + 1) ≤ 1000000000000000000 * (KB + 1) * (KB + 1) := by
      nlinarith [hKB1, hsq]
    have hKfge : 1000000000000000000 * (KB + 1) * (KB + 1) ≤ Kf := by nlinarith [hKf]
    calc 17644000025 * ((KB + 1) * (T * p ^ 2))
        = (17644000025 * (KB + 1)) * (T * p ^ 2) := by ring
      _ ≤ (1000000000000000000 * (KB + 1) * (KB + 1)) * (T * p ^ 2) :=
          Nat.mul_le_mul_right (T * p ^ 2) hbig
      _ ≤ Kf * (T * p ^ 2) := Nat.mul_le_mul_right (T * p ^ 2) hKfge
  nlinarith [hA, h5, hKtrT, hSV, hCJ, hU]

/-- Paper Prop 5.2, final cost arithmetic: the sum of the costs of all elementary steps of the
assembled word (at most 44 uniform allowances, the `sgn`-branch overhead `5·KB`, the two
resampling words, the power-of-two transform's cost as it appears in `fsCost`, the scaling word
and the two conjugation words) is at most `fsCost Kf Cm p α ts` for the constant `Kf` chosen by
the caller. -/
theorem p52costLem {Kf KB Kres Ktr Ksv Kcj p α : ℕ} {ss ts : List ℕ} {Cm : ℕ → ℕ}
    (hmon : Monotone Cm) (hPow : HvdH.PowTwoParams p ts) (hRes : HvdH.ResParams p α ss ts)
    (h2Da : 2 * HvdH.D * α ^ 2 ≤ p) (h3Dp : 3 * HvdH.D * p ^ 2 < ts.prod) (hSsT : ss.prod ≤ ts.prod)
    (hKres : Kres ≤ KB) (hKtr : Ktr ≤ KB) (hKsv : Ksv ≤ KB) (hKcj : Kcj ≤ KB)
    (hKf : Kf = 1000000000000000000 * (KB + 1) * (KB + 1) + 1000000000000000000) :
    44 * Work.MainP.ALLOW KB (Work.MainP.SB0 p α ss ts) (Work.MainP.Pm0 p) + 5 * KB +
      2 * HvdH.resCost Kres Cm p α ts +
      (4 * (ts.prod / HvdH.lmax ts) * Cm (3 * HvdH.lmax ts * p) + Ktr * ts.prod * p ^ 2 +
        Ktr * ts.sum * (p + 1) ^ Ktr) +
      (Ksv * (ss.prod + 1) * (p + 1) ^ 2 + Ksv) +
      2 * (Kcj * (ss.prod + 1) * (p + 1) + Kcj)
    ≤ HvdH.fsCost Kf Cm p α ts := by
  have _h2Da := h2Da
  have hp1 : 1 ≤ p := by have := hPow.2.2.2.2; omega
  have hT1 : 1 ≤ ts.prod := by have := h3Dp; omega
  have hSB : Work.MainP.SB0 p α ss ts ≤ 200 * ts.prod * p := sb0_le hPow hRes hSsT h3Dp
  have hPm : Work.MainP.Pm0 p ≤ 200 * ts.prod * p := by
    simp only [Work.MainP.Pm0]
    have hD : HvdH.D = 1729 := rfl
    have hT' : 5187 * (p * p) ≤ ts.prod := by
      have h3 := h3Dp
      rw [hD] at h3
      nlinarith [h3]
    have h1 : (p + 16) * (p + 16) ≤ 289 * (p * p) := by nlinarith [hp1]
    have h2a : 5187 * (p * p) ≤ (5187 * (p * p)) * p := by
      have h := Nat.mul_le_mul_left (5187 * (p * p)) hp1
      rwa [Nat.mul_one] at h
    have h2b : 289 * (p * p) ≤ 200 * (5187 * (p * p)) := by nlinarith
    have h2 : 289 * (p * p) ≤ 200 * (5187 * (p * p)) * p := by nlinarith [h2a, h2b]
    have h3 : 200 * (5187 * (p * p)) * p ≤ 200 * ts.prod * p :=
      Nat.mul_le_mul_right p (Nat.mul_le_mul_left 200 hT')
    exact le_trans h1 (le_trans h2 h3)
  have hcore := arithCore (KB := KB) (Kf := Kf) (Ktr := Ktr) (Ksv := Ksv) (Kcj := Kcj)
    (p := p) (T := ts.prod) (S := ss.prod) (SB := Work.MainP.SB0 p α ss ts)
    (Pm := Work.MainP.Pm0 p) hp1 hT1 hSsT hSB hPm hKtr hKsv hKcj hKf
  have hKBKf : KB ≤ Kf := by
    rw [hKf]
    have h1 : KB ≤ (KB + 1) * (KB + 1) := by nlinarith
    nlinarith [h1]
  have hKresKf : Kres ≤ Kf := le_trans hKres hKBKf
  have hKtrKf : Ktr ≤ Kf := le_trans hKtr hKBKf
  have hmono : 2 * HvdH.resCost Kres Cm p α ts ≤ 2 * HvdH.resCost Kf Cm p α ts :=
    Nat.mul_le_mul_left 2 (resCostMono hmon hKresKf p α ts)
  have hexp : Ktr * ts.sum * (p + 1) ^ Ktr ≤ Kf * ts.sum * (p + 1) ^ Kf := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul hKtrKf le_rfl
    · exact Nat.pow_le_pow_right (by omega) hKtrKf
  simp only [HvdH.fsCost]
  nlinarith [hcore, hmono, hexp]

end Work.MainP
