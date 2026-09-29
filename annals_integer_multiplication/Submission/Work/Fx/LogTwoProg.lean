import Mathlib
import Submission.Work.Fx.LogTwoDefs
import Submission.Work.Fx.LogTwoAux
import Submission.Work.Fx.FxAdapt
import Submission.Work.Fx.scaleSteps

/-!
# The `log 2` loop body

The 22-step fixed-point program computing one round of the loop, with the constant-cost helpers
used to bound it by a polynomial in the precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

open HvdH

/-! ## Cost helpers -/

theorem le_sq_add_one (p₀ : ℕ) : p₀ + 1 ≤ (p₀ + 1) ^ 2 := by
  have h : (p₀ + 1) * 1 ≤ (p₀ + 1) * (p₀ + 1) := Nat.mul_le_mul_left _ (by omega)
  simpa [pow_two] using h

/-- `K * k * n ≤ C * (p₀+1)^2` from `K*(k*c) ≤ C` and `n ≤ c*(p₀+1)`. -/
theorem cost_bound {K k n c p₀ C : ℕ} (hK : K * (k * c) ≤ C) (hn : n ≤ c * (p₀ + 1)) :
    K * k * n ≤ C * (p₀ + 1) ^ 2 := by
  have h1 : K * k * n ≤ K * k * (c * (p₀ + 1)) := Nat.mul_le_mul_left _ hn
  have h2 : K * k * (c * (p₀ + 1)) = K * (k * c) * (p₀ + 1) := by ring
  have h3 : K * (k * c) * (p₀ + 1) ≤ C * (p₀ + 1) := Nat.mul_le_mul_right _ hK
  have h4 : C * (p₀ + 1) ≤ C * (p₀ + 1) ^ 2 := Nat.mul_le_mul_left _ (le_sq_add_one p₀)
  calc K * k * n ≤ K * k * (c * (p₀ + 1)) := h1
    _ = K * (k * c) * (p₀ + 1) := h2
    _ ≤ C * (p₀ + 1) := h3
    _ ≤ C * (p₀ + 1) ^ 2 := h4

/-- `K * n ≤ C * (p₀+1)^2` from `K*c ≤ C` and `n ≤ c*(p₀+1)`. -/
theorem cost_bound1 {K n c p₀ C : ℕ} (hK : K * c ≤ C) (hn : n ≤ c * (p₀ + 1)) :
    K * n ≤ C * (p₀ + 1) ^ 2 := by
  calc K * n ≤ K * (c * (p₀ + 1)) := Nat.mul_le_mul_left _ hn
    _ = (K * c) * (p₀ + 1) := by ring
    _ ≤ C * (p₀ + 1) := Nat.mul_le_mul_right _ hK
    _ ≤ C * (p₀ + 1) ^ 2 := Nat.mul_le_mul_left _ (le_sq_add_one p₀)

/-- Product form: `K * a * b ≤ C * (p₀+1)^2`. -/
theorem cost_bound2 {K a b ca cb p₀ C : ℕ} (hK : K * (ca * cb) ≤ C)
    (ha : a ≤ ca * (p₀ + 1)) (hb : b ≤ cb * (p₀ + 1)) : K * a * b ≤ C * (p₀ + 1) ^ 2 := by
  have hab : a * b ≤ (ca * cb) * (p₀ + 1) ^ 2 := by
    calc a * b ≤ (ca * (p₀ + 1)) * (cb * (p₀ + 1)) := Nat.mul_le_mul ha hb
      _ = (ca * cb) * ((p₀ + 1) * (p₀ + 1)) := by ring
      _ = (ca * cb) * (p₀ + 1) ^ 2 := by rw [pow_two]
  calc K * a * b = K * (a * b) := by ring
    _ ≤ K * ((ca * cb) * (p₀ + 1) ^ 2) := Nat.mul_le_mul_left _ hab
    _ = (K * (ca * cb)) * (p₀ + 1) ^ 2 := by ring
    _ ≤ C * (p₀ + 1) ^ 2 := Nat.mul_le_mul_right _ hK

/-! ## Constant-cost adapters -/

/-- A binary integer operation with an arbitrary precondition, on a fixed window prefix. -/
theorem Spec.binStepP (hk : KernelLib) {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) {E : List Val} {Bc : ℕ}
    (hcost : C a b ≤ Bc) :
    Spec main prog (2 + E.length) (fun t => t = [.int a, .int b] ++ E)
      (fun _ o => o = [.int (f a b)] ++ E) (fun _ => Bc) := by
  refine Spec.step2 hk (A := [.int a, .int b]) (n := 2) (by simp) (Spec.binOp hk h)
    ⟨a, b, rfl, hab⟩ (by simpa [binCost_cons_int] using hcost) ?_
  intro o ho
  rcases ho with ⟨a', b', hab', ho'⟩
  obtain ⟨h1, h2, -⟩ := int_cons_inj3 hab'
  rw [ho', ← h1, ← h2]

/-- `swap` at a fixed window prefix, constant cost. -/
theorem Spec.swapStepP (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) {E : List Val} {Bc : ℕ} (hcost : K * (vsz a + vsz b + 1) ≤ Bc) :
    Spec main prog (2 + E.length) (fun t => t = [a, b] ++ E) (fun _ o => o = [b, a] ++ E)
      (fun _ => Bc) := by
  refine Spec.step2 hk (A := [a, b]) (n := 2) (by simp) (Spec.swapK hk h) trivial
    (by simpa [List.getD_cons_zero, List.getD_cons_succ] using hcost) ?_
  intro o ho
  rcases ho with ⟨a', b', hab', ho'⟩
  obtain ⟨h1, h2, -⟩ := cons_inj3 hab'
  rw [ho', ← h1, ← h2]

/-! ## The body -/

/-- One round of the `log 2` loop: `[D,S,c,M,p] ↦ [flag, D/2, S+(D/2)/(c+1), c+1, M, p]`. -/
theorem logBodyAux (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (Kb : ℕ), ∀ (main : HvdH.Cmd) (p₀ : ℕ) (D S c M p : ℤ), 100 ≤ p₀ →
      p = (p₀ : ℤ) → 0 ≤ c → isz D ≤ logSZ p₀ → isz S ≤ logSZ p₀ → isz c ≤ logSZ p₀ →
      isz M ≤ logSZ p₀ →
      Spec main prog 5 (fun t => t = [.int D, .int S, .int c, .int M, .int p])
        (fun _ o => o = [.int (if c < M then 1 else 0), .int (D.tdiv 2),
          .int (S + (D.tdiv 2).tdiv (c + 1)), .int (c + 1), .int M, .int p])
        (fun _ => Kb * (p₀ + 1) ^ 2) := by
  obtain ⟨cPick, KPick, hPick⟩ := hk.pick
  obtain ⟨cRoll, KRoll, hRoll⟩ := hk.roll
  obtain ⟨cDup, KDup, hDup⟩ := hk.dup
  obtain ⟨cDrop, KDrop, hDrop⟩ := hk.drop
  obtain ⟨cSwap, KSwap, hSwap⟩ := hk.swap
  obtain ⟨cPush, KPush, hPush⟩ := hk.pushVal
  obtain ⟨cLt, KLt, hLt⟩ := hi.lt
  obtain ⟨cTdiv, KTdiv, hTdiv⟩ := hi.tdiv
  obtain ⟨cAdd, KAdd, hAdd⟩ := hi.add
  let prog : Cmd := .seq (cPick 3) (.seq (cPick 3) (.seq cLt (.seq (cRoll 1) (.seq cDup
    (.seq (cPush (.int 2)) (.seq cSwap (.seq cTdiv (.seq cSwap (.seq cDrop (.seq (cRoll 3)
    (.seq (cPush (.int 1)) (.seq cSwap (.seq cAdd (.seq (cPick 0) (.seq (cPick 2)
    (.seq cTdiv (.seq (cRoll 4) (.seq cAdd (.seq (cRoll 3) (.seq (cRoll 3) cSwap))))))))))))))))))))
  let Ks : ℕ := 400 * (KPick + KRoll + KDup + KDrop + KSwap + KPush + KLt + KTdiv + KAdd + 1)
  refine ⟨prog, 22 * Ks, ?_⟩
  intro main p₀ D S c M p hp0 hp hc0 hD hS hc hM
  have hD1 : isz D ≤ 2 * p₀ + 25 := by have := hD; simp only [logSZ] at this; omega
  have hS1 : isz S ≤ 2 * p₀ + 25 := by have := hS; simp only [logSZ] at this; omega
  have hc1 : isz c ≤ 2 * p₀ + 25 := by have := hc; simp only [logSZ] at this; omega
  have hM1 : isz M ≤ 2 * p₀ + 25 := by have := hM; simp only [logSZ] at this; omega
  have hp1 : isz p ≤ 2 * p₀ + 25 := by
    rw [hp]; have := p_isz_le p₀; simp only [logSZ] at this; omega
  have h1isz : isz (1 : ℤ) = 3 := by simp [isz, Nat.size_one]
  have h2isz : isz (2 : ℤ) = 4 := by
    have h : (2 : ℤ).natAbs = 2 := rfl
    simp [isz, h, Nat.size_two]
  let fl : ℤ := if c < M then 1 else 0
  let D' : ℤ := D.tdiv 2
  let cc : ℤ := c + 1
  let aa : ℤ := D'.tdiv cc
  let S' : ℤ := S + aa
  have hfl1 : isz fl ≤ 2 * p₀ + 26 := by
    have h : fl = 0 ∨ fl = 1 := by
      by_cases hclt : c < M
      · right; simp only [fl, if_pos hclt]
      · left; simp only [fl, if_neg hclt]
    rcases h with h | h <;> rw [h] <;> simp only [isz, Int.natAbs_one, Int.natAbs_zero,
      Nat.size_one, Nat.size_zero] <;> omega
  have hD'1 : isz D' ≤ 2 * p₀ + 25 := by
    simp only [D']; exact le_trans (isz_tdiv_le D 2) hD1
  have hcc1 : isz cc ≤ 2 * p₀ + 26 := by
    have h := isz_add_le c 1
    have h1 : isz (1 : ℤ) = 3 := h1isz
    simp only [cc]
    omega
  have haa1 : isz aa ≤ 2 * p₀ + 25 := by
    simp only [aa]; exact le_trans (isz_tdiv_le D' cc) hD'1
  have hS'1 : isz S' ≤ 2 * p₀ + 26 := by
    have h := isz_add_le S aa
    simp only [S']
    omega
  -- windows
  let T0 : List Val := [.int D, .int S, .int c, .int M, .int p]
  let T1 : List Val := [.int M, .int D, .int S, .int c, .int M, .int p]
  let T2 : List Val := [.int c, .int M, .int D, .int S, .int c, .int M, .int p]
  let T3 : List Val := [.int fl, .int D, .int S, .int c, .int M, .int p]
  let T4 : List Val := [.int D, .int fl, .int S, .int c, .int M, .int p]
  let T5 : List Val := [.int D, .int D, .int fl, .int S, .int c, .int M, .int p]
  let T6 : List Val := [.int 2, .int D, .int D, .int fl, .int S, .int c, .int M, .int p]
  let T7 : List Val := [.int D, .int 2, .int D, .int fl, .int S, .int c, .int M, .int p]
  let T8 : List Val := [.int D', .int D, .int fl, .int S, .int c, .int M, .int p]
  let T9 : List Val := [.int D, .int D', .int fl, .int S, .int c, .int M, .int p]
  let T10 : List Val := [.int D', .int fl, .int S, .int c, .int M, .int p]
  let T11 : List Val := [.int c, .int D', .int fl, .int S, .int M, .int p]
  let T12 : List Val := [.int 1, .int c, .int D', .int fl, .int S, .int M, .int p]
  let T13 : List Val := [.int c, .int 1, .int D', .int fl, .int S, .int M, .int p]
  let T14 : List Val := [.int cc, .int D', .int fl, .int S, .int M, .int p]
  let T15 : List Val := [.int cc, .int cc, .int D', .int fl, .int S, .int M, .int p]
  let T16 : List Val := [.int D', .int cc, .int cc, .int D', .int fl, .int S, .int M, .int p]
  let T17 : List Val := [.int aa, .int cc, .int D', .int fl, .int S, .int M, .int p]
  let T18 : List Val := [.int S, .int aa, .int cc, .int D', .int fl, .int M, .int p]
  let T19 : List Val := [.int S', .int cc, .int D', .int fl, .int M, .int p]
  let T20 : List Val := [.int fl, .int S', .int cc, .int D', .int M, .int p]
  let T21 : List Val := [.int D', .int fl, .int S', .int cc, .int M, .int p]
  let T22 : List Val := [.int fl, .int D', .int S', .int cc, .int M, .int p]
  -- step 1: pick 3 on T0
  have hsz1 : szl [.int D, .int S, .int c, .int M] + 1 ≤ 20 * (p₀ + 1) := by
    simp only [szl_cons, szl_nil, vsz_int]; omega
  have e1 : Spec main (cPick 3) 5 (fun t => t = T0) (fun _ o => o = T1)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pickStep hk (k := 3) (hPick main 3)
      (A := [.int D, .int S, .int c, .int M]) (by simp) (E := [.int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KPick) (k := 4) (c := 20) (n := szl [.int D, .int S, .int c, .int M] + 1)
        (by simp only [Ks]; omega) hsz1)
    simpa [T0, T1] using h
  -- step 2: pick 3 on T1
  have e2 : Spec main (cPick 3) 6 (fun t => t = T1) (fun _ o => o = T2)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int M, .int D, .int S, .int c] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.pickStep hk (k := 3) (hPick main 3)
      (A := [.int M, .int D, .int S, .int c]) (by simp) (E := [.int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KPick) (k := 4) (c := 20) (n := szl [.int M, .int D, .int S, .int c] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T1, T2, List.cons_append, List.nil_append] using h
  -- step 3: lt
  have e3 : Spec main cLt 7 (fun t => t = T2) (fun _ o => o = T3)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hLt main) (a := c) (b := M) (hab := trivial)
      (E := [.int D, .int S, .int c, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KLt) (c := 8) (n := isz c + isz M) (by simp only [Ks]; omega)
        (by omega))
    simpa [T2, T3, fl] using h
  -- step 4: roll 1
  have e4 : Spec main (cRoll 1) 6 (fun t => t = T3) (fun _ o => o = T4)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int fl, .int D] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 1) (hRoll main 1)
      (A := [.int fl, .int D]) (by simp) (E := [.int S, .int c, .int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 2) (c := 20) (n := szl [.int fl, .int D] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T3, T4, List.cons_append, List.nil_append] using h
  -- step 5: dup
  have e5 : Spec main cDup 6 (fun t => t = T4) (fun _ o => o = T5)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dupStep hk (hDup main) (a := .int D) (E := [.int fl, .int S, .int c, .int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDup) (c := 4) (n := vsz (.int D) + 1) (by simp only [Ks]; omega)
        (by simp only [vsz_int]; omega))
    simpa [T4, T5, List.cons_append, List.nil_append] using h
  -- step 6: push 2
  have e6 : Spec main (cPush (.int 2)) 7 (fun t => t = T5) (fun _ o => o = T6)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 2)) (E := T5) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 5) (n := vsz (.int 2) + 1) (by simp only [Ks]; omega)
        (by simp only [vsz_int, h2isz]; omega))
    simpa [T5, T6, List.cons_append, List.nil_append] using h
  -- step 7: swap
  have e7 : Spec main cSwap 8 (fun t => t = T6) (fun _ o => o = T7)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int 2) (.int D)
      (E := [.int D, .int fl, .int S, .int c, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int 2) + vsz (.int D) + 1)
        (by simp only [Ks]; omega) (by simp only [vsz_int, h2isz]; omega))
    simpa [T6, T7, List.cons_append, List.nil_append] using h
  -- step 8: tdiv
  have e8 : Spec main cTdiv 8 (fun t => t = T7) (fun _ o => o = T8)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hTdiv main) (a := D) (b := 2) (hab := by norm_num)
      (E := [.int D, .int fl, .int S, .int c, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound2 (K := KTdiv) (a := isz D) (b := isz (2 : ℤ)) (ca := 4) (cb := 4)
        (by simp only [Ks]; omega) (by omega) (by simp only [h2isz]; omega))
    simpa [T7, T8, D', List.cons_append, List.nil_append] using h
  -- step 9: swap
  have e9 : Spec main cSwap 7 (fun t => t = T8) (fun _ o => o = T9)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int D') (.int D)
      (E := [.int fl, .int S, .int c, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int D') + vsz (.int D) + 1)
        (by simp only [Ks]; omega) (by simp only [vsz_int]; omega))
    simpa [T8, T9, List.cons_append, List.nil_append] using h
  -- step 10: drop
  have e10 : Spec main cDrop 7 (fun t => t = T9) (fun _ o => o = T10)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.dropStep hk (hDrop main) (a := .int D)
      (E := [.int D', .int fl, .int S, .int c, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KDrop) (c := 4) (n := vsz (.int D) + 1) (by simp only [Ks]; omega)
        (by simp only [vsz_int]; omega))
    simpa [T9, T10] using h
  -- step 11: roll 3
  have e11 : Spec main (cRoll 3) 6 (fun t => t = T10) (fun _ o => o = T11)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int D', .int fl, .int S, .int c] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 3) (hRoll main 3)
      (A := [.int D', .int fl, .int S, .int c]) (by simp) (E := [.int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 4) (c := 20) (n := szl [.int D', .int fl, .int S, .int c] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T10, T11, List.cons_append, List.nil_append] using h
  -- step 12: push 1
  have e12 : Spec main (cPush (.int 1)) 6 (fun t => t = T11) (fun _ o => o = T12)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.pushStep hk (hPush main (.int 1)) (E := T11) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KPush) (c := 5) (n := vsz (.int 1) + 1) (by simp only [Ks]; omega)
        (by simp only [vsz_int, h1isz]; omega))
    simpa [T11, T12, List.cons_append, List.nil_append] using h
  -- step 13: swap
  have e13 : Spec main cSwap 7 (fun t => t = T12) (fun _ o => o = T13)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int 1) (.int c)
      (E := [.int D', .int fl, .int S, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int 1) + vsz (.int c) + 1)
        (by simp only [Ks]; omega) (by simp only [vsz_int, h1isz]; omega))
    simpa [T12, T13, List.cons_append, List.nil_append] using h
  -- step 14: add
  have e14 : Spec main cAdd 7 (fun t => t = T13) (fun _ o => o = T14)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := c) (b := 1) (hab := trivial)
      (E := [.int D', .int fl, .int S, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz c + isz (1 : ℤ)) (by simp only [Ks]; omega)
        (by simp only [h1isz]; omega))
    simpa [T13, T14, cc, List.cons_append, List.nil_append] using h
  -- step 15: pick 0
  have e15 : Spec main (cPick 0) 6 (fun t => t = T14) (fun _ o => o = T15)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int cc] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.pickStep hk (k := 0) (hPick main 0)
      (A := [.int cc]) (by simp) (E := [.int D', .int fl, .int S, .int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KPick) (k := 1) (c := 20) (n := szl [.int cc] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T14, T15, List.cons_append, List.nil_append] using h
  -- step 16: pick 2
  have e16 : Spec main (cPick 2) 7 (fun t => t = T15) (fun _ o => o = T16)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int cc, .int cc, .int D'] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.pickStep hk (k := 2) (hPick main 2)
      (A := [.int cc, .int cc, .int D']) (by simp) (E := [.int fl, .int S, .int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KPick) (k := 3) (c := 20) (n := szl [.int cc, .int cc, .int D'] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T15, T16, List.cons_append, List.nil_append] using h
  -- step 17: tdiv
  have e17 : Spec main cTdiv 8 (fun t => t = T16) (fun _ o => o = T17)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hTdiv main) (a := D') (b := cc) (hab := by omega)
      (E := [.int cc, .int D', .int fl, .int S, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound2 (K := KTdiv) (a := isz D') (b := isz cc) (ca := 4) (cb := 4)
        (by simp only [Ks]; omega) (by omega) (by omega))
    simpa [T16, T17, aa, List.cons_append, List.nil_append] using h
  -- step 18: roll 4
  have e18 : Spec main (cRoll 4) 7 (fun t => t = T17) (fun _ o => o = T18)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int aa, .int cc, .int D', .int fl, .int S] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 4) (hRoll main 4)
      (A := [.int aa, .int cc, .int D', .int fl, .int S]) (by simp) (E := [.int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 5) (c := 20)
        (n := szl [.int aa, .int cc, .int D', .int fl, .int S] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T17, T18, List.cons_append, List.nil_append] using h
  -- step 19: add
  have e19 : Spec main cAdd 7 (fun t => t = T18) (fun _ o => o = T19)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.binStepP hk (hAdd main) (a := S) (b := aa) (hab := trivial)
      (E := [.int cc, .int D', .int fl, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KAdd) (c := 8) (n := isz S + isz aa) (by simp only [Ks]; omega)
        (by omega))
    simpa [T18, T19, S', List.cons_append, List.nil_append] using h
  -- step 20: roll 3
  have e20 : Spec main (cRoll 3) 6 (fun t => t = T19) (fun _ o => o = T20)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int S', .int cc, .int D', .int fl] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 3) (hRoll main 3)
      (A := [.int S', .int cc, .int D', .int fl]) (by simp) (E := [.int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 4) (c := 20) (n := szl [.int S', .int cc, .int D', .int fl] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T19, T20, List.cons_append, List.nil_append] using h
  -- step 21: roll 3
  have e21 : Spec main (cRoll 3) 6 (fun t => t = T20) (fun _ o => o = T21)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have hsz : szl [.int fl, .int S', .int cc, .int D'] + 1 ≤ 20 * (p₀ + 1) := by
      simp only [szl_cons, szl_nil, vsz_int]; omega
    have h := Spec.rollStep hk (k := 3) (hRoll main 3)
      (A := [.int fl, .int S', .int cc, .int D']) (by simp) (E := [.int M, .int p])
      (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound (K := KRoll) (k := 4) (c := 20) (n := szl [.int fl, .int S', .int cc, .int D'] + 1)
        (by simp only [Ks]; omega) hsz)
    simpa [T20, T21, List.cons_append, List.nil_append] using h
  -- step 22: swap
  have e22 : Spec main cSwap 6 (fun t => t = T21) (fun _ o => o = T22)
      (fun _ => Ks * (p₀ + 1) ^ 2) := by
    have h := Spec.swapStepP hk (hSwap main) (.int D') (.int fl)
      (E := [.int S', .int cc, .int M, .int p]) (Bc := Ks * (p₀ + 1) ^ 2)
      (cost_bound1 (K := KSwap) (c := 8) (n := vsz (.int D') + vsz (.int fl) + 1)
        (by simp only [Ks]; omega) (by simp only [vsz_int]; omega))
    simpa [T21, T22, List.cons_append, List.nil_append] using h
  -- composition
  have c21 := Spec.seq_det_quad hk e21 e22 (by simp [T21])
  have c20 := Spec.seq_det_quad hk e20 c21 (by simp [T20])
  have c19 := Spec.seq_det_quad hk e19 c20 (by simp [T19])
  have c18 := Spec.seq_det_quad hk e18 c19 (by simp [T18])
  have c17 := Spec.seq_det_quad hk e17 c18 (by simp [T17])
  have c16 := Spec.seq_det_quad hk e16 c17 (by simp [T16])
  have c15 := Spec.seq_det_quad hk e15 c16 (by simp [T15])
  have c14 := Spec.seq_det_quad hk e14 c15 (by simp [T14])
  have c13 := Spec.seq_det_quad hk e13 c14 (by simp [T13])
  have c12 := Spec.seq_det_quad hk e12 c13 (by simp [T12])
  have c11 := Spec.seq_det_quad hk e11 c12 (by simp [T11])
  have c10 := Spec.seq_det_quad hk e10 c11 (by simp [T10])
  have c9 := Spec.seq_det_quad hk e9 c10 (by simp [T9])
  have c8 := Spec.seq_det_quad hk e8 c9 (by simp [T8])
  have c7 := Spec.seq_det_quad hk e7 c8 (by simp [T7])
  have c6 := Spec.seq_det_quad hk e6 c7 (by simp [T6])
  have c5 := Spec.seq_det_quad hk e5 c6 (by simp [T5])
  have c4 := Spec.seq_det_quad hk e4 c5 (by simp [T4])
  have c3 := Spec.seq_det_quad hk e3 c4 (by simp [T3])
  have c2 := Spec.seq_det_quad hk e2 c3 (by simp [T2])
  have h := Spec.seq_det_quad hk e1 c2 (by simp [T1])
  refine Spec.mono hk (by simpa only [prog] using h) ?_ ?_ ?_
  · intro t ht hP
    rw [hP]
  · intro t o ht hP hQ
    rw [hQ]
  · intro t ht hP
    exact le_of_eq (by ring)

end Work.Fx
