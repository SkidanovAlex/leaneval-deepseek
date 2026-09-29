import Mathlib
import Submission.Work.KronP.defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KronP

open HvdH

/-! ## 1. Constant-cost words with exact stack windows -/

/-- `WordR` with equality pre/post and constant cost. -/
abbrev SEq (main p : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c)

/-- Sequential composition of two `SEq`s. -/
theorem SEq.compose (hK : KernelLib) {main p q : Cmd} {A B B' Cc : List Val} {c1 c2 : ℕ}
    (h1 : SEq main p A B c1) (h2 : SEq main q B' Cc c2) (h : B = B') :
    SEq main (.seq p q) A Cc (c1 + c2) := by
  subst h
  have hseq : WordR main (.seq p q) (fun vs => vs = A)
      (fun _ out => ∃ mid, mid = B ∧ out = Cc) (fun _ => c1 + c2) :=
    hK.seq main p q (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1)
      (fun vs => vs = B) (fun _ out => out = Cc) (fun _ => c2) (fun _ => c2) h1 h2
      (by intro vs mid h1' h2'; exact ⟨h2', le_rfl⟩)
  refine hK.conseq main (.seq p q) _ _ _ _ _ _ hseq ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out hpre hpost
    obtain ⟨mid, hmid, hout⟩ := hpost
    exact hout
  · intro vs _; exact le_rfl

/-- Sequential composition with a prescribed cost bound. -/
theorem SEq.composeE (hK : KernelLib) {main p q : Cmd} {A B B' Cc : List Val}
    {c1 c2 Φ : ℕ} (h1 : SEq main p A B c1) (h2 : SEq main q B' Cc c2) (h : B = B')
    (hΦ : c1 + c2 ≤ Φ) : SEq main (.seq p q) A Cc Φ :=
  hK.conseq main (.seq p q) _ _ _ _ _ _ (SEq.compose hK h1 h2 h) (fun _ h => h)
    (fun _ _ _ hout => hout) (fun _ _ => hΦ)

/-! ### the primitive steps -/

theorem pick1S (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {Kpi T E M : ℕ}
    (hpick : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpi * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hKpi : Kpi ≤ T) (hM : M = T * (4096 * E))
    (w1 w2 : Val) (X : List Val) (hC : Kpi * (1 + 1) * (vsz w1 + vsz w2 + 1) ≤ M) :
    SEq main (pickP 1) (w1 :: w2 :: X) (w2 :: w1 :: w2 :: X) M := by
  have he : (((w1 :: w2 :: X).take (1 + 1)).map vsz).sum + 1 = vsz w1 + vsz w2 + 1 := by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    try ring
  have hcost : Kpi * (1 + 1) * ((((w1 :: w2 :: X).take (1 + 1)).map vsz).sum + 1) ≤ M := by
    rw [he]; exact hC
  refine hK.conseq main (pickP 1) _ _ _ _ _ _ (hpick main 1) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp only [List.length_cons]; omega
  · intro vs out hvs hpost
    rw [hvs] at hpost
    rw [hpost]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  · intro vs hvs; rw [hvs]; exact hcost

theorem pick2S (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {Kpi T E M : ℕ}
    (hpick : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpi * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hKpi : Kpi ≤ T) (hM : M = T * (4096 * E))
    (w1 w2 w3 : Val) (X : List Val)
    (hC : Kpi * (2 + 1) * (vsz w1 + vsz w2 + vsz w3 + 1) ≤ M) :
    SEq main (pickP 2) (w1 :: w2 :: w3 :: X) (w3 :: w1 :: w2 :: w3 :: X) M := by
  have he : (((w1 :: w2 :: w3 :: X).take (2 + 1)).map vsz).sum + 1
      = vsz w1 + vsz w2 + vsz w3 + 1 := by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    try ring
  have hcost : Kpi * (2 + 1) * ((((w1 :: w2 :: w3 :: X).take (2 + 1)).map vsz).sum + 1) ≤ M := by
    rw [he]; exact hC
  refine hK.conseq main (pickP 2) _ _ _ _ _ _ (hpick main 2) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp only [List.length_cons]; omega
  · intro vs out hvs hpost
    rw [hvs] at hpost
    rw [hpost]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  · intro vs hvs; rw [hvs]; exact hcost

theorem pick3S (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {Kpi T E M : ℕ}
    (hpick : ∀ (m : Cmd) (k : ℕ), WordR m (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpi * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hKpi : Kpi ≤ T) (hM : M = T * (4096 * E))
    (w1 w2 w3 w4 : Val) (X : List Val)
    (hC : Kpi * (3 + 1) * (vsz w1 + vsz w2 + vsz w3 + vsz w4 + 1) ≤ M) :
    SEq main (pickP 3) (w1 :: w2 :: w3 :: w4 :: X) (w4 :: w1 :: w2 :: w3 :: w4 :: X) M := by
  have he : (((w1 :: w2 :: w3 :: w4 :: X).take (3 + 1)).map vsz).sum + 1
      = vsz w1 + vsz w2 + vsz w3 + vsz w4 + 1 := by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    try ring
  have hcost : Kpi * (3 + 1) * ((((w1 :: w2 :: w3 :: w4 :: X).take (3 + 1)).map vsz).sum + 1)
      ≤ M := by
    rw [he]; exact hC
  refine hK.conseq main (pickP 3) _ _ _ _ _ _ (hpick main 3) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp only [List.length_cons]; omega
  · intro vs out hvs hpost
    rw [hvs] at hpost
    rw [hpost]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  · intro vs hvs; rw [hvs]; exact hcost

theorem pushS (hK : KernelLib) {main : Cmd} {pushP : Val → Cmd} {Kpu : ℕ}
    (hpush : ∀ (m : Cmd) (v : Val), WordR m (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpu * (vsz v + 1)))
    (v : Val) (X : List Val) (M : ℕ) (hC : Kpu * (vsz v + 1) ≤ M) :
    SEq main (pushP v) X (v :: X) M := by
  refine hK.conseq main (pushP v) _ _ _ _ _ _ (hpush main v) ?_ ?_ ?_
  · intro vs _; trivial
  · intro vs out hvs hpost; rw [hvs] at hpost; exact hpost
  · intro vs _; exact hC

theorem swapS (hK : KernelLib) {main : Cmd} {swapP : Cmd} {Ksw : ℕ}
    (hswap : ∀ m : Cmd, WordR m swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (X : List Val) (M : ℕ) (hC : Ksw * (vsz a + vsz b + 1) ≤ M) :
    SEq main swapP (a :: b :: X) (b :: a :: X) M := by
  refine hK.conseq main swapP _ _ _ _ _ _ (hswap main) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp
  · intro vs out hvs hpost
    rw [hvs] at hpost
    obtain ⟨a', b', X', heq, hout⟩ := hpost
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact hout
  · intro vs hvs; rw [hvs]; simpa using hC

theorem binS (hK : KernelLib) {main P : Cmd} {Pr : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {Cst : ℤ → ℤ → ℕ} (h : BinOp main P Pr f Cst) (a b r : ℤ) (X : List Val) (hr : r = f a b)
    (hPr : Pr a b) (M : ℕ) (hC : Cst a b ≤ M) :
    SEq main P (.int a :: .int b :: X) (.int r :: X) M := by
  have h0 : SEq main P (.int a :: .int b :: X) (.int (f a b) :: X) M := by
    refine hK.conseq main P _ _ _ _ _ _ h ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; exact ⟨a, b, X, rfl, hPr⟩
    · intro vs out hvs hpost
      rw [hvs] at hpost
      obtain ⟨a', b', X', heq, hout⟩ := hpost
      simp only [List.cons.injEq, Val.int.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hout
    · intro vs hvs; rw [hvs]; exact hC
  rw [hr]; exact h0

theorem unS (hK : KernelLib) {main P : Cmd} {Pr : ℤ → Prop} {f : ℤ → ℤ} {Cst : ℤ → ℕ}
    (h : UnOp main P Pr f Cst) (a r : ℤ) (X : List Val) (hr : r = f a) (hPr : Pr a)
    (M : ℕ) (hC : Cst a ≤ M) : SEq main P (.int a :: X) (.int r :: X) M := by
  have h0 : SEq main P (.int a :: X) (.int (f a) :: X) M := by
    refine hK.conseq main P _ _ _ _ _ _ h ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; exact ⟨a, X, rfl, hPr⟩
    · intro vs out hvs hpost
      rw [hvs] at hpost
      obtain ⟨a', X', heq, hout⟩ := hpost
      simp only [List.cons.injEq, Val.int.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hout
    · intro vs hvs; rw [hvs]; exact hC
  rw [hr]; exact h0

/-! ## 2. elementary size facts -/

theorem isz_of_lt {n b : ℕ} (h : n < 2 ^ b) : isz (n : ℤ) ≤ b + 3 := by
  have h1 : (n : ℤ).natAbs.size ≤ b := by
    rw [Int.natAbs_natCast, Nat.size_le]; exact h
  simp only [isz]; omega

theorem isz_natCast_le_self (n : ℕ) : isz (n : ℤ) ≤ n + 3 :=
  isz_of_lt (Nat.lt_two_pow_self (n := n))

theorem isz_le_of_natAbs {z : ℤ} {n : ℕ} (h : z.natAbs = n) : isz z ≤ n + 3 := by
  have h1 : n.size ≤ n + 1 := by
    rw [Nat.size_le]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self (n := n))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [isz, h]; omega

theorem le_E_one (p r : ℕ) : 1 ≤ (r + 1) * (p + 1) ^ 2 := by
  rw [pow_two]
  have h2 : 1 ≤ (p + 1) * (p + 1) := by nlinarith
  exact le_trans h2 (Nat.le_mul_of_pos_left _ (by omega))

theorem le_E_p (p r : ℕ) (hp : 1 ≤ p) : p ≤ (r + 1) * (p + 1) ^ 2 := by
  rw [pow_two]
  have h1 : p ≤ (p + 1) * (p + 1) := by nlinarith
  exact le_trans h1 (Nat.le_mul_of_pos_left _ (by omega))

theorem le_E_r (p r : ℕ) (hr : 2 ≤ r) : r ≤ (r + 1) * (p + 1) ^ 2 := by
  rw [pow_two]
  have h1 : (0:ℕ) < (p + 1) * (p + 1) := by positivity
  have h2 : r + 1 ≤ (r + 1) * ((p + 1) * (p + 1)) := Nat.le_mul_of_pos_right (r + 1) h1
  omega

theorem le_E_pr (p r : ℕ) (hp : 1 ≤ p) : p * r ≤ (r + 1) * (p + 1) ^ 2 := by
  rw [pow_two]
  have h1 : p ≤ (p + 1) * (p + 1) := by nlinarith
  have h2 : r ≤ r + 1 := by omega
  calc p * r ≤ ((p + 1) * (p + 1)) * (r + 1) := Nat.mul_le_mul h1 h2
    _ = (r + 1) * ((p + 1) * (p + 1)) := by ring

theorem le_E_ppr (p r : ℕ) (hp : 1 ≤ p) : p * p * r ≤ (r + 1) * (p + 1) ^ 2 := by
  rw [pow_two]
  have h1 : p * p ≤ (p + 1) * (p + 1) := by nlinarith
  have h2 : r ≤ r + 1 := by omega
  calc p * p * r ≤ ((p + 1) * (p + 1)) * (r + 1) := Nat.mul_le_mul h1 h2
    _ = (r + 1) * ((p + 1) * (p + 1)) := by ring



theorem isz_of_natAbs_pow {z : ℤ} {x : ℕ} (h : z.natAbs = 2 ^ x) : isz z = x + 3 := by
  have h1 : isz z = (2 ^ x).size + 2 := by rw [isz, h]
  have h2 : (2 ^ x).size = x + 1 := Nat.size_pow
  omega

theorem isz_of_natAbs_sub_pow {z : ℤ} {x : ℕ} (h : z.natAbs = 2 ^ x - 1) : isz z ≤ x + 3 := by
  have h1 : isz z = z.natAbs.size + 2 := rfl
  have h3 : (2 ^ x - 1).size ≤ x + 1 := by
    rw [Nat.size_le]
    have hx : 0 < (2 : ℕ) ^ x := Nat.two_pow_pos x
    have h4 : 2 ^ x ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [h1, h]
  omega

theorem le_add_clog {p r : ℕ} (hcl : Nat.clog 2 r ≤ r) : p + Nat.clog 2 r + 3 ≤ p + r + 3 := by
  omega

/-! ## 2b. small-context cost arithmetic (kept out of the main context) -/

theorem ub_mul4 {k S E : ℕ} (hk : k + 1 ≤ 4) (hS : S ≤ 1024 * E) : (k + 1) * S ≤ 4096 * E := by
  calc (k + 1) * S ≤ 4 * (1024 * E) := Nat.mul_le_mul hk hS
    _ = 4096 * E := by ring
theorem ub_powE {A B p r E : ℕ} (hA : A ≤ p + Nat.clog 2 r) (hB : B ≤ p + r + 3)
    (hcl : Nat.clog 2 r ≤ r) (hEp : p ≤ E) (hEr : r ≤ E) (hE1 : 1 ≤ E) :
    A + B ≤ 4096 * E := by linarith
theorem ub_pow6 {A B p r E : ℕ} (hA : A ≤ 2 * r * (3 * p)) (hB : B ≤ 6 * (p * r) + 3)
    (hEpr : p * r ≤ E) (hE1 : 1 ≤ E) : A + B ≤ 4096 * E := by nlinarith
theorem ub_pow3 {A B p E : ℕ} (hA : A ≤ 3 * p) (hB : B ≤ 3 * p + 3) (hEp : p ≤ E)
    (hE1 : 1 ≤ E) : A + B ≤ 4096 * E := by linarith
theorem ub_6pr3p {a b r p E : ℕ} (ha : a ≤ 6 * (p * r) + 3) (hb : b ≤ 3 * p + 3)
    (hEpr : p * r ≤ E) (hEppr : p * p * r ≤ E) (hEp : p ≤ E) (hEr : r ≤ E) (hE1 : 1 ≤ E) :
    a * b ≤ 4096 * E := by nlinarith
theorem ub_3p6pr {a b r p E : ℕ} (ha : a ≤ 3 * p + 3) (hb : b ≤ 6 * (p * r) + 3)
    (hEpr : p * r ≤ E) (hEppr : p * p * r ≤ E) (hEp : p ≤ E) (hEr : r ≤ E) (hE1 : 1 ≤ E) :
    a * b ≤ 4096 * E := by nlinarith
theorem ub_2r3p {a b r p E : ℕ} (ha : a ≤ 2 * r + 3) (hb : b ≤ 3 * p + 3)
    (hEpr : p * r ≤ E) (hEr : r ≤ E) (hEp : p ≤ E) (hE1 : 1 ≤ E) : a * b ≤ 4096 * E := by
  nlinarith
theorem ub_5p {a b p E : ℕ} (ha : a ≤ 5) (hb : b ≤ p + 3) (hEp : p ≤ E) (hE1 : 1 ≤ E) :
    a * b ≤ 4096 * E := by nlinarith
theorem ub_final {T X : ℕ} : 39 * (T * (4096 * X)) ≤ 1048576 * T * X := by nlinarith

/-! ## 3. the closed form of the digit offset -/

theorem digitOffsetTdiv (p N : ℕ) (hp : 1 ≤ p) :
    digitOffset p N =
      (2 : ℤ) ^ (3 * p - 1) * Int.tdiv ((2 : ℤ) ^ (3 * p * N) - 1) ((2 : ℤ) ^ (3 * p) - 1) := by
  obtain ⟨B, hB⟩ : ∃ x : ℤ, x = (2 : ℤ) ^ (3 * p) := ⟨_, rfl⟩
  obtain ⟨Sz, hSz⟩ : ∃ x : ℤ, x = ((List.range N).map (fun m => B ^ m)).sum := ⟨_, rfl⟩
  have hBpow : ∀ m : ℕ, (2 : ℤ) ^ (3 * p * m) = B ^ m := by
    intro m
    rw [hB, ← pow_mul]
  have hmap : (List.range N).map (fun m => (2 : ℤ) ^ (3 * p * m))
      = (List.range N).map (fun m => B ^ m) := by
    apply List.map_congr_left
    intro m _
    exact hBpow m
  have hmain : ∀ k : ℕ, (B - 1) * ((List.range k).map (fun m => B ^ m)).sum = B ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hr : ((List.range (k + 1)).map (fun m => B ^ m)).sum
          = ((List.range k).map (fun m => B ^ m)).sum + B ^ k := by
        rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
      rw [hr, mul_add, ih, pow_succ]
      ring
  have hgeom : (B - 1) * Sz = B ^ N - 1 := by
    rw [hSz]
    exact hmain N
  have hBne : B - 1 ≠ 0 := by
    rw [hB]
    have h2 : (2 : ℕ) ^ 3 ≤ 2 ^ (3 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (8 : ℤ) ≤ ((2 ^ (3 * p) : ℕ) : ℤ) := by exact_mod_cast h2
    have h4 : ((2 ^ (3 * p) : ℕ) : ℤ) = (2 : ℤ) ^ (3 * p) := by push_cast; ring
    rw [h4] at h3
    intro h
    linarith
  have hdiv : Int.tdiv (B ^ N - 1) (B - 1) = Sz :=
    Int.tdiv_eq_of_eq_mul_right hBne hgeom.symm
  have hdig : digitOffset p N = (2 : ℤ) ^ (3 * p - 1) * Sz := by
    rw [hSz]
    unfold digitOffset
    rw [List.sum_map_mul_left, hmap]
  rw [hdig, ← hdiv, hB, ← pow_mul]

/-- The word built by `setup`: `3p`, `2r`, `C`, `2^(p+κ)` above `int p, int r`. -/
def setupProg (pickP : ℕ → Cmd) (pushP : Val → Cmd)
    (swapP addP subP pow2P clog2P tdivP mulSP : Cmd) : Cmd :=
  (((((((((((((((((((((((((((((((((((((((pickP 1)).seq (clog2P)).seq ((pickP 1))).seq (addP)).seq (pow2P)).seq ((pickP 1))).seq (pushP (Val.int (3:ℤ)))).seq (mulSP)).seq ((pickP 3))).seq (pushP (Val.int (2:ℤ)))).seq (mulSP)).seq (mulSP)).seq (pow2P)).seq (pushP (Val.int (1:ℤ)))).seq (swapP)).seq (subP)).seq ((pickP 2))).seq (pushP (Val.int (3:ℤ)))).seq (mulSP)).seq (pow2P)).seq (pushP (Val.int (1:ℤ)))).seq (swapP)).seq (subP)).seq (swapP)).seq (tdivP)).seq ((pickP 2))).seq (pushP (Val.int (3:ℤ)))).seq (mulSP)).seq (pushP (Val.int (1:ℤ)))).seq (swapP)).seq (subP)).seq (pow2P)).seq (mulSP)).seq ((pickP 3))).seq (pushP (Val.int (2:ℤ)))).seq (mulSP)).seq ((pickP 3))).seq (pushP (Val.int (3:ℤ)))).seq (mulSP)

/-! ## 4. the setup word -/


/-
Piece of the Kronecker word for paper Lemma 2.5 (`Work.ConvR.KroneckerSpec`).

Given `int p, int r, P, Q` on the value stack (`P, Q` arbitrary values), compute and push the four
constants used by the rest of the pipeline:
`b = 3p`, `nn = 2r`, `C = digitOffset p (2r) = Σ_{m<2r} 2^{3p-1}·2^{3p·m}`, `D = 2^{p + Nat.clog 2 r}`
(in this order, directly above `int p, int r`; `P, Q` stay untouched below).

All tools are fields of `HvdH.KernelLib` / `HvdH.IntLib` (specs in `Submission/HvdH/Interfaces.lean`):
`dup`, `pushVal`, `mulS` for `3p` and `2r`; `pow2`, `tdiv` for `T = 2^{3p-1}`;
`HvdH.LayoutLib.replicate (2r) T` followed by `HvdH.IntLib.evalPoly` with base `3p` for `C`
(`evalPoly` needs `h < 2^(3·3p)` and `1 ≤ b`, both fine since `1 ≤ p`); `clog2`, `add`, `pow2` for `D`.
Every step costs `O(rp)` or `O(p)`; `pick`/`roll` only ever touch the small values `p, r` and the
constants, never `P, Q`, so the stated bound holds.
-/
theorem setup (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (P Q : HvdH.Val) (rest : List HvdH.Val),
      1 ≤ p → 2 ≤ r → HvdH.IsPow2 r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: P :: Q :: rest)
        (fun _ out => out = HvdH.Val.int (3 * p : ℤ) :: HvdH.Val.int (2 * r : ℤ) ::
            HvdH.Val.int (Work.KronP.digitOffset p (2 * r)) ::
            HvdH.Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: P :: Q :: rest)
        (fun _ => K * (r + 1) * (p + 1) ^ 2) := by
  obtain ⟨pickP, Kpi, hpick⟩ := hK.pick
  obtain ⟨pushP, Kpu, hpush⟩ := hK.pushVal
  obtain ⟨swapP, Ksw, hswap⟩ := hK.swap
  obtain ⟨mulSP, Kmu, hmulS⟩ := hI.mulS
  obtain ⟨addP, Kad, hadd⟩ := hI.add
  obtain ⟨subP, Ksb, hsub⟩ := hI.sub
  obtain ⟨pow2P, Kpw, hpow2⟩ := hI.pow2
  obtain ⟨clog2P, Kcl, hclog2⟩ := hI.clog2
  obtain ⟨tdivP, Ktd, htdiv⟩ := hI.tdiv
  obtain ⟨T, hT⟩ : ∃ x : ℕ, x = Kpi + Kpu + Ksw + Kmu + Kad + Ksb + Kpw + Kcl + Ktd + 1 := ⟨_, rfl⟩
  refine ⟨setupProg pickP pushP swapP addP subP pow2P clog2P tdivP mulSP, 1048576 * T, ?_⟩
  intro main p r P Q rest hp hr hpow
  set S : List Val := P :: Q :: rest with hS
  obtain ⟨E, hE⟩ : ∃ x : ℕ, x = (r + 1) * (p + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ x : ℕ, x = T * (4096 * E) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact le_E_one p r
  have hEp : p ≤ E := by rw [hE]; exact le_E_p p r hp
  have hEr : r ≤ E := by rw [hE]; exact le_E_r p r hr
  have hEpr : p * r ≤ E := by rw [hE]; exact le_E_pr p r hp
  have hEppr : p * p * r ≤ E := by rw [hE]; exact le_E_ppr p r hp
  have hTKpi : Kpi ≤ T := by rw [hT]; omega
  have hTKpu : Kpu ≤ T := by rw [hT]; omega
  have hTKsw : Ksw ≤ T := by rw [hT]; omega
  have hTKmu : Kmu ≤ T := by rw [hT]; omega
  have hTKad : Kad ≤ T := by rw [hT]; omega
  have hTKsb : Ksb ≤ T := by rw [hT]; omega
  have hTKpw : Kpw ≤ T := by rw [hT]; omega
  have hTKcl : Kcl ≤ T := by rw [hT]; omega
  have hTKtd : Ktd ≤ T := by rw [hT]; omega
  have gcl : Nat.clog 2 r ≤ r := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact le_of_lt (Nat.lt_two_pow_self (n := r))
  obtain ⟨q3, hq3⟩ : ∃ x : ℤ, x = 3 * (p : ℤ) := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ x : ℤ, x = 2 * (r : ℤ) := ⟨_, rfl⟩
  obtain ⟨qcr, hqcr⟩ : ∃ x : ℤ, x = ((Nat.clog 2 r : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨qE, hqE⟩ : ∃ x : ℤ, x = (p : ℤ) + qcr := ⟨_, rfl⟩
  obtain ⟨qD, hqD⟩ : ∃ x : ℤ, x = 2 ^ qE.toNat := ⟨_, rfl⟩
  obtain ⟨q6, hq6⟩ : ∃ x : ℤ, x = q2 * q3 := ⟨_, rfl⟩
  obtain ⟨qBN, hqBN⟩ : ∃ x : ℤ, x = 2 ^ q6.toNat := ⟨_, rfl⟩
  obtain ⟨qBNm, hqBNm⟩ : ∃ x : ℤ, x = qBN - 1 := ⟨_, rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ x : ℤ, x = 2 ^ q3.toNat := ⟨_, rfl⟩
  obtain ⟨qBm, hqBm⟩ : ∃ x : ℤ, x = qB - 1 := ⟨_, rfl⟩
  obtain ⟨qS, hqS⟩ : ∃ x : ℤ, x = Int.tdiv qBNm qBm := ⟨_, rfl⟩
  obtain ⟨qT, hqT⟩ : ∃ x : ℤ, x = q3 - 1 := ⟨_, rfl⟩
  obtain ⟨qTm, hqTm⟩ : ∃ x : ℤ, x = 2 ^ qT.toNat := ⟨_, rfl⟩
  obtain ⟨qC, hqC⟩ : ∃ x : ℤ, x = qTm * qS := ⟨_, rfl⟩
  -- cast normal forms
  have cE : qE = (((p + Nat.clog 2 r : ℕ)) : ℤ) := by
    rw [hqE, hqcr]; exact (Nat.cast_add p (Nat.clog 2 r)).symm
  have c2 : q2 = (((2 * r : ℕ)) : ℤ) := by rw [hq2]; exact (Nat.cast_mul 2 r).symm
  have c3 : q3 = (((3 * p : ℕ)) : ℤ) := by rw [hq3]; exact (Nat.cast_mul 3 p).symm
  have c6 : q6 = (((2 * r * (3 * p) : ℕ)) : ℤ) := by
    rw [hq6, hq2, hq3]
    have h1 : (2 : ℤ) * (r : ℤ) = (((2 * r : ℕ)) : ℤ) := (Nat.cast_mul 2 r).symm
    have h2 : (3 : ℤ) * (p : ℤ) = (((3 * p : ℕ)) : ℤ) := (Nat.cast_mul 3 p).symm
    rw [h1, h2]
    exact (Nat.cast_mul (2 * r) (3 * p)).symm
  have gE : qE.toNat = p + Nat.clog 2 r := by rw [cE, Int.toNat_natCast]
  have g2 : q2.toNat = 2 * r := by rw [c2, Int.toNat_natCast]
  have g3 : q3.toNat = 3 * p := by rw [c3, Int.toNat_natCast]
  have g6 : q6.toNat = 2 * r * (3 * p) := by rw [c6, Int.toNat_natCast]
  have gT : qT.toNat = 3 * p - 1 := by
    have h : qT = (((3 * p : ℕ)) : ℤ) - 1 := by rw [hqT, c3]
    rw [h]; exact Int.toNat_sub (3 * p) 1
  have cc3 : (3 : ℤ) * (p : ℤ) = (((3 * p : ℕ)) : ℤ) := (Nat.cast_mul 3 p).symm
  have cc6 : ((2 : ℤ) * (r : ℤ)) * ((3 : ℤ) * (p : ℤ)) = (((2 * r * (3 * p) : ℕ)) : ℤ) := by
    have h1 : (2 : ℤ) * (r : ℤ) = (((2 * r : ℕ)) : ℤ) := (Nat.cast_mul 2 r).symm
    have h2 : (3 : ℤ) * (p : ℤ) = (((3 * p : ℕ)) : ℤ) := (Nat.cast_mul 3 p).symm
    rw [h1, h2]
    exact (Nat.cast_mul (2 * r) (3 * p)).symm
  have ggT : ((3 : ℤ) * (p : ℤ) - 1).toNat = 3 * p - 1 := by
    rw [cc3]; exact Int.toNat_sub (3 * p) 1
  have gg6 : (((2 : ℤ) * (r : ℤ)) * ((3 : ℤ) * (p : ℤ))).toNat = 2 * r * (3 * p) := by
    rw [cc6]; exact Int.toNat_natCast _
  have gg3 : ((3 : ℤ) * (p : ℤ)).toNat = 3 * p := by
    rw [cc3]; exact Int.toNat_natCast _
  -- natAbs normal forms
  have abs_p : (p : ℤ).natAbs = p := Int.natAbs_natCast p
  have abs_r : (r : ℤ).natAbs = r := Int.natAbs_natCast r
  have abs_cr : qcr.natAbs = Nat.clog 2 r := by rw [hqcr, Int.natAbs_natCast]
  have abs_E : qE.natAbs = p + Nat.clog 2 r := by
    have h : ((qE.natAbs : ℕ) : ℤ) = (((p + Nat.clog 2 r : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hqE, hqcr]; positivity), cE]
    exact_mod_cast h
  have abs_D : qD.natAbs = 2 ^ qE.toNat := by
    have h : ((qD.natAbs : ℕ) : ℤ) = (((2 ^ qE.toNat : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hqD]; positivity), hqD]
      exact (Nat.cast_pow 2 qE.toNat).symm
    exact_mod_cast h
  have abs_3 : q3.natAbs = 3 * p := by
    have h : ((q3.natAbs : ℕ) : ℤ) = (((3 * p : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hq3]; positivity), c3]
    exact_mod_cast h
  have abs_2 : q2.natAbs = 2 * r := by
    have h : ((q2.natAbs : ℕ) : ℤ) = (((2 * r : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hq2]; positivity), c2]
    exact_mod_cast h
  have abs_6 : q6.natAbs = 2 * r * (3 * p) := by
    have h : ((q6.natAbs : ℕ) : ℤ) = (((2 * r * (3 * p) : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hq6, hq2, hq3]; positivity), c6]
    exact_mod_cast h
  have abs_BN : qBN.natAbs = 2 ^ q6.toNat := by
    have h : ((qBN.natAbs : ℕ) : ℤ) = (((2 ^ q6.toNat : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hqBN]; positivity), hqBN]
      exact (Nat.cast_pow 2 q6.toNat).symm
    exact_mod_cast h
  have abs_B : qB.natAbs = 2 ^ q3.toNat := by
    have h : ((qB.natAbs : ℕ) : ℤ) = (((2 ^ q3.toNat : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hqB]; positivity), hqB]
      exact (Nat.cast_pow 2 q3.toNat).symm
    exact_mod_cast h
  have abs_Tm : qTm.natAbs = 2 ^ qT.toNat := by
    have h : ((qTm.natAbs : ℕ) : ℤ) = (((2 ^ qT.toNat : ℕ)) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by rw [hqTm]; positivity), hqTm]
      exact (Nat.cast_pow 2 qT.toNat).symm
    exact_mod_cast h
  have hBN1 : (1 : ℤ) ≤ qBN := by
    rw [hqBN]
    have h2 : (1 : ℕ) ≤ 2 ^ q6.toNat := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h2
  have hB1 : (1 : ℤ) ≤ qB := by
    rw [hqB]
    have h2 : (1 : ℕ) ≤ 2 ^ q3.toNat := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h2
  have abs_BNm : qBNm.natAbs = 2 ^ q6.toNat - 1 := by
    have h1 : qBNm = ((2 : ℤ) ^ q6.toNat) - 1 := by rw [hqBNm, hqBN]
    have h2 : (1 : ℤ) ≤ (2 : ℤ) ^ q6.toNat := by rw [← hqBN]; exact hBN1
    rw [h1, Int.natAbs_sub_of_nonneg_of_le (by norm_num : (0 : ℤ) ≤ 1) h2, Int.natAbs_one,
      ← hqBN, abs_BN]
  have abs_Bm : qBm.natAbs = 2 ^ q3.toNat - 1 := by
    have h1 : qBm = ((2 : ℤ) ^ q3.toNat) - 1 := by rw [hqBm, hqB]
    have h2 : (1 : ℤ) ≤ (2 : ℤ) ^ q3.toNat := by rw [← hqB]; exact hB1
    rw [h1, Int.natAbs_sub_of_nonneg_of_le (by norm_num : (0 : ℤ) ≤ 1) h2, Int.natAbs_one,
      ← hqB, abs_B]
  have hBNm0 : 0 ≤ qBNm := by rw [hqBNm]; linarith
  have hBm0 : 0 ≤ qBm := by rw [hqBm]; linarith
  -- fine bounds
  have f_p : isz (p : ℤ) ≤ p + 3 := isz_le_of_natAbs abs_p
  have f_r : isz (r : ℤ) ≤ r + 3 := isz_le_of_natAbs abs_r
  have f_1 : isz (1 : ℤ) ≤ 4 := isz_of_lt (by norm_num : (1 : ℕ) < 2 ^ 1)
  have f_2 : isz (2 : ℤ) ≤ 5 := isz_of_lt (by norm_num : (2 : ℕ) < 2 ^ 2)
  have f_3 : isz (3 : ℤ) ≤ 5 := isz_of_lt (by norm_num : (3 : ℕ) < 2 ^ 2)
  have f_qcr : isz qcr ≤ r + 3 := le_trans (isz_le_of_natAbs abs_cr) (Nat.add_le_add_right gcl 3)
  have f_qE : isz qE ≤ p + r + 3 := le_trans (isz_le_of_natAbs abs_E) (le_add_clog gcl)
  have hsz_D : isz qD = qE.toNat + 3 := isz_of_natAbs_pow abs_D
  have f_qD : isz qD ≤ p + r + 3 := by rw [hsz_D, gE]; exact le_add_clog gcl
  have f_q3 : isz q3 ≤ 3 * p + 3 := isz_le_of_natAbs abs_3
  have f_q2 : isz q2 ≤ 2 * r + 3 := isz_le_of_natAbs abs_2
  have f_q6 : isz q6 ≤ 6 * (p * r) + 3 := by
    refine le_trans (isz_le_of_natAbs abs_6) ?_
    exact le_of_eq (by ring)
  have hsz_BN : isz qBN = q6.toNat + 3 := isz_of_natAbs_pow abs_BN
  have f_qBN : isz qBN ≤ 6 * (p * r) + 3 := by
    rw [hsz_BN, g6]; exact le_of_eq (by ring)
  have hsz_BNm : isz qBNm ≤ q6.toNat + 3 := isz_of_natAbs_sub_pow abs_BNm
  have f_qBNm : isz qBNm ≤ 6 * (p * r) + 3 := by
    refine le_trans hsz_BNm ?_
    rw [g6]; exact le_of_eq (by ring)
  have hsz_B : isz qB = q3.toNat + 3 := isz_of_natAbs_pow abs_B
  have f_qB : isz qB ≤ 3 * p + 3 := by rw [hsz_B, g3]
  have hsz_Bm : isz qBm ≤ q3.toNat + 3 := isz_of_natAbs_sub_pow abs_Bm
  have f_qBm : isz qBm ≤ 3 * p + 3 := by
    refine le_trans hsz_Bm ?_
    rw [g3]
  have hSabs : qS.natAbs ≤ qBNm.natAbs := by
    have h0S : 0 ≤ qS := by rw [hqS]; exact Int.tdiv_nonneg hBNm0 hBm0
    have h2 : ((qS.natAbs : ℕ) : ℤ) ≤ ((qBNm.natAbs : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg h0S, Int.natAbs_of_nonneg hBNm0]
      rw [hqS]; exact Int.tdiv_le_self qBm hBNm0
    exact_mod_cast h2
  have hBNm_le : qBNm.natAbs ≤ 2 ^ (6 * (p * r)) := by
    rw [abs_BNm]
    calc 2 ^ q6.toNat - 1 ≤ 2 ^ q6.toNat := Nat.sub_le _ _
      _ = 2 ^ (2 * r * (3 * p)) := by rw [g6]
      _ = 2 ^ (6 * (p * r)) := by
          rw [show 2 * r * (3 * p) = 6 * (p * r) by ring]
  have f_qS : isz qS ≤ 6 * (p * r) + 3 := by
    have h3 : isz qS = qS.natAbs.size + 2 := rfl
    have h4 : qS.natAbs.size ≤ qBNm.natAbs.size := Nat.size_le_size hSabs
    have h5 : qBNm.natAbs.size ≤ (2 ^ (6 * (p * r))).size := Nat.size_le_size hBNm_le
    calc isz qS = qS.natAbs.size + 2 := h3
      _ ≤ qBNm.natAbs.size + 2 := Nat.add_le_add_right h4 2
      _ ≤ (2 ^ (6 * (p * r))).size + 2 := Nat.add_le_add_right h5 2
      _ = 6 * (p * r) + 3 := by rw [Nat.size_pow]
  have f_qT : isz qT ≤ 3 * p + 3 := by
    have h : qT = (((3 * p - 1 : ℕ)) : ℤ) := by
      rw [hqT, c3]
      exact (Nat.cast_sub (by omega : (1 : ℕ) ≤ 3 * p)).symm
    calc isz qT = isz ((((3 * p - 1 : ℕ)) : ℤ)) := by rw [h]
      _ ≤ 3 * p - 1 + 3 := isz_natCast_le_self _
      _ ≤ 3 * p + 3 := by omega
  have hsz_Tm : isz qTm = qT.toNat + 3 := isz_of_natAbs_pow abs_Tm
  have f_qTm : isz qTm ≤ 3 * p + 3 := by
    rw [hsz_Tm, gT]
    exact Nat.add_le_add_right (Nat.sub_le (3 * p) 1) 3
  have aT : qTm.natAbs ≤ 2 ^ (3 * p) := by
    rw [abs_Tm]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [gT]; exact Nat.sub_le _ _
  have f_qC : isz qC ≤ 6 * (p * r) + 3 * p + 3 := by
    have h : qC.natAbs ≤ 2 ^ (6 * (p * r) + 3 * p) := by
      rw [hqC, Int.natAbs_mul]
      calc qTm.natAbs * qS.natAbs ≤ 2 ^ (3 * p) * 2 ^ (6 * (p * r)) :=
            Nat.mul_le_mul aT (le_trans hSabs hBNm_le)
        _ = 2 ^ (3 * p + 6 * (p * r)) := by rw [← pow_add]
        _ = 2 ^ (6 * (p * r) + 3 * p) := by
            rw [show 3 * p + 6 * (p * r) = 6 * (p * r) + 3 * p by ring]
    have h2 : qC.natAbs.size ≤ 6 * (p * r) + 3 * p + 1 := by
      rw [Nat.size_le]
      calc qC.natAbs ≤ 2 ^ (6 * (p * r) + 3 * p) := h
        _ < 2 ^ (6 * (p * r) + 3 * p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h3 : isz qC = qC.natAbs.size + 2 := rfl
    omega
  -- coarse bounds
  have hi_p : isz (p : ℤ) ≤ 32 * E := by linarith [f_p, hEp, hE1]
  have hi_r : isz (r : ℤ) ≤ 32 * E := by linarith [f_r, hEr, hE1]
  have hi_i1 : isz (1 : ℤ) ≤ 32 * E := by linarith [f_1, hE1]
  have hi_i2 : isz (2 : ℤ) ≤ 32 * E := by linarith [f_2, hE1]
  have hi_i3 : isz (3 : ℤ) ≤ 32 * E := by linarith [f_3, hE1]
  have hi_cr : isz qcr ≤ 32 * E := by linarith [f_qcr, hEr, hE1]
  have hi_qE : isz qE ≤ 32 * E := by linarith [f_qE, hEp, hEr, hE1]
  have hi_qD : isz qD ≤ 32 * E := by linarith [f_qD, hEp, hEr, hE1]
  have hi_q3 : isz q3 ≤ 32 * E := by linarith [f_q3, hEp, hE1]
  have hi_q2 : isz q2 ≤ 32 * E := by linarith [f_q2, hEr, hE1]
  have hi_q6 : isz q6 ≤ 32 * E := by linarith [f_q6, hEpr, hE1]
  have hi_qBN : isz qBN ≤ 32 * E := by linarith [f_qBN, hEpr, hE1]
  have hi_qBNm : isz qBNm ≤ 32 * E := by linarith [f_qBNm, hEpr, hE1]
  have hi_qB : isz qB ≤ 32 * E := by linarith [f_qB, hEp, hE1]
  have hi_qBm : isz qBm ≤ 32 * E := by linarith [f_qBm, hEp, hE1]
  have hi_qS : isz qS ≤ 32 * E := by linarith [f_qS, hEpr, hE1]
  have hi_qT : isz qT ≤ 32 * E := by linarith [f_qT, hEp, hE1]
  have hi_qTm : isz qTm ≤ 32 * E := by linarith [f_qTm, hEp, hE1]
  have hi_qC : isz qC ≤ 32 * E := by linarith [f_qC, hEpr, hEp, hE1]
  have hv_ip : vsz (Val.int (p : ℤ)) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_p
  have hv_ir : vsz (Val.int (r : ℤ)) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_r
  have hv_i1 : vsz (Val.int (1 : ℤ)) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_i1
  have hv_i2 : vsz (Val.int (2 : ℤ)) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_i2
  have hv_i3 : vsz (Val.int (3 : ℤ)) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_i3
  have hv_cr : vsz (Val.int qcr) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_cr
  have hv_qE : vsz (Val.int qE) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qE
  have hv_qD : vsz (Val.int qD) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qD
  have hv_q3 : vsz (Val.int q3) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_q3
  have hv_q2 : vsz (Val.int q2) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_q2
  have hv_q6 : vsz (Val.int q6) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_q6
  have hv_qBN : vsz (Val.int qBN) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qBN
  have hv_qBNm : vsz (Val.int qBNm) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qBNm
  have hv_qB : vsz (Val.int qB) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qB
  have hv_qBm : vsz (Val.int qBm) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qBm
  have hv_qS : vsz (Val.int qS) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qS
  have hv_qT : vsz (Val.int qT) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qT
  have hv_qTm : vsz (Val.int qTm) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qTm
  have hv_qC : vsz (Val.int qC) ≤ 32 * E := by rw [Work.ConvR.vsz_int]; exact hi_qC
  have hqcr_br : qcr = ((Nat.clog 2 ((r : ℤ).toNat) : ℕ) : ℤ) := by
    rw [hqcr, Int.toNat_natCast]
  have hneBm : qBm ≠ 0 := by
    intro h
    have h1 : qBm = (((2 ^ q3.toNat - 1 : ℕ)) : ℤ) := by
      rw [hqBm, hqB]
      have h' : (2 : ℤ) ^ q3.toNat = (((2 ^ q3.toNat : ℕ)) : ℤ) :=
        (Nat.cast_pow 2 q3.toNat).symm
      rw [h']
      exact (Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))).symm
    rw [h1] at h
    have h2 : 2 ^ q3.toNat - 1 = 0 := by exact_mod_cast h
    have h3 : 2 ≤ 2 ^ q3.toNat := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ q3.toNat := Nat.pow_le_pow_right (by norm_num) (by rw [g3]; omega)
    omega
  have hposr : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hposE : (0 : ℤ) ≤ qE := by rw [hqE, hqcr]; positivity
  have hpos6 : (0 : ℤ) ≤ q6 := by rw [hq6, hq2, hq3]; positivity
  have hpos3 : (0 : ℤ) ≤ q3 := by rw [hq3]; positivity
  have hposT : (0 : ℤ) ≤ qT := by
    rw [hqT, hq3]
    have h2 : (1 : ℤ) ≤ 3 * (p : ℤ) := by
      have h3 : (1 : ℕ) ≤ 3 * p := by omega
      exact_mod_cast h3
    linarith

  have hb1 : (1 + 1) * (vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 1) (by norm_num) (by linarith [hv_ip, hv_ir, hE1])
  have hc1 : Kpi * (1 + 1) * (vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb1
  have s1 : SEq main (pickP 1) (Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (r:ℤ) :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick1S hK hpick hTKpi hM (Val.int (p:ℤ)) (Val.int (r:ℤ)) (S) hc1

  have hb2 : isz ((r:ℤ)) ≤ 4096 * E := by linarith [hi_r, hE1]
  have hc2 : Kcl * isz ((r:ℤ)) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKcl hb2
  have s2 : SEq main clog2P (Val.int ((r:ℤ)) :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qcr :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    unS hK (hclog2 main) ((r:ℤ)) qcr (Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqcr_br hposr M hc2

  have hb3 : (1 + 1) * (vsz (Val.int qcr) + vsz (Val.int (p:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 1) (by norm_num) (by linarith [hv_cr, hv_ip, hE1])
  have hc3 : Kpi * (1 + 1) * (vsz (Val.int qcr) + vsz (Val.int (p:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb3
  have s3 : SEq main (pickP 1) (Val.int qcr :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (p:ℤ) :: Val.int qcr :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick1S hK hpick hTKpi hM (Val.int qcr) (Val.int (p:ℤ)) (Val.int (r:ℤ) :: S) hc3

  have hb4 : isz ((p:ℤ)) + isz (qcr) ≤ 4096 * E := by
    calc isz ((p:ℤ)) + isz (qcr) ≤ (p + 3) + (r + 3) := Nat.add_le_add f_p f_qcr
      _ ≤ 4096 * E := by linarith [hEpr, hEppr, hEp, hEr, hE1]
  have hc4 : Kad * (isz ((p:ℤ)) + isz (qcr)) ≤ M := by
    rw [hM]
    exact Nat.mul_le_mul hTKad hb4
  have s4 : SEq main addP (Val.int ((p:ℤ)) :: Val.int (qcr) :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qE :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hadd main) ((p:ℤ)) (qcr) qE (Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqE trivial M hc4

  have hb5 : (qE).toNat + isz (qE) ≤ 4096 * E := ub_powE (A := qE.toNat) (B := isz qE) (by rw [gE]) f_qE gcl hEp hEr hE1
  have hc5 : Kpw * ((qE).toNat + isz (qE)) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpw hb5
  have s5 : SEq main pow2P (Val.int (qE) :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    unS hK (hpow2 main) (qE) qD (Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqD hposE M hc5

  have hb6 : (1 + 1) * (vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 1) (by norm_num) (by linarith [hv_qD, hv_ip, hE1])
  have hc6 : Kpi * (1 + 1) * (vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb6
  have s6 : SEq main (pickP 1) (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (p:ℤ) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick1S hK hpick hTKpi hM (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ) :: S) hc6

  have hb7 : vsz (Val.int (3:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i3, hE1]
  have hc7 : Kpu * (vsz (Val.int (3:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb7
  have s7 : SEq main (pushP (Val.int (3:ℤ))) (Val.int (p:ℤ) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (3:ℤ) :: Val.int (p:ℤ) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (3:ℤ)) (Val.int (p:ℤ) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc7

  have hb8 : isz ((3:ℤ)) * isz ((p:ℤ)) ≤ 4096 * E := by
    calc isz (3:ℤ) * isz (p:ℤ) ≤ 5 * (p + 3) := Nat.mul_le_mul f_3 f_p
      _ ≤ 4096 * E := by linarith [hEp, hE1]
  have hc8 : Kmu * isz ((3:ℤ)) * isz ((p:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb8
  have s8 : SEq main mulSP (Val.int ((3:ℤ)) :: Val.int ((p:ℤ)) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((3:ℤ)) ((p:ℤ)) q3 (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq3 trivial M hc8

  have hb9 : (3 + 1) * (vsz (Val.int q3) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 3) (by norm_num) (by linarith [hv_q3, hv_qD, hv_ip, hv_ir, hE1])
  have hc9 : Kpi * (3 + 1) * (vsz (Val.int q3) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb9
  have s9 : SEq main (pickP 3) (Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (r:ℤ) :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick3S hK hpick hTKpi hM (Val.int q3) (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ)) (S) hc9

  have hb10 : vsz (Val.int (2:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i2, hE1]
  have hc10 : Kpu * (vsz (Val.int (2:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb10
  have s10 : SEq main (pushP (Val.int (2:ℤ))) (Val.int (r:ℤ) :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (2:ℤ) :: Val.int (r:ℤ) :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (2:ℤ)) (Val.int (r:ℤ) :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc10

  have hb11 : isz ((2:ℤ)) * isz ((r:ℤ)) ≤ 4096 * E := by
    calc isz (2:ℤ) * isz (r:ℤ) ≤ 5 * (r + 3) := Nat.mul_le_mul f_2 f_r
      _ ≤ 4096 * E := by linarith [hEr, hE1]
  have hc11 : Kmu * isz ((2:ℤ)) * isz ((r:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb11
  have s11 : SEq main mulSP (Val.int ((2:ℤ)) :: Val.int ((r:ℤ)) :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q2 :: Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((2:ℤ)) ((r:ℤ)) q2 (Val.int q3 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq2 trivial M hc11

  have hb12 : isz (q2) * isz (q3) ≤ 4096 * E := by
    exact ub_2r3p f_q2 f_q3 hEpr hEr hEp hE1
  have hc12 : Kmu * isz (q2) * isz (q3) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb12
  have s12 : SEq main mulSP (Val.int (q2) :: Val.int (q3) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q6 :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) (q2) (q3) q6 (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq6 trivial M hc12

  have hb13 : (q6).toNat + isz (q6) ≤ 4096 * E := ub_pow6 (A := q6.toNat) (B := isz q6) (by rw [g6]) f_q6 hEpr hE1
  have hc13 : Kpw * ((q6).toNat + isz (q6)) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpw hb13
  have s13 : SEq main pow2P (Val.int (q6) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qBN :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    unS hK (hpow2 main) (q6) qBN (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqBN hpos6 M hc13

  have hb14 : vsz (Val.int (1:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i1, hE1]
  have hc14 : Kpu * (vsz (Val.int (1:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb14
  have s14 : SEq main (pushP (Val.int (1:ℤ))) (Val.int qBN :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (1:ℤ) :: Val.int qBN :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (1:ℤ)) (Val.int qBN :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc14

  have hb15 : vsz (Val.int (1:ℤ)) + vsz (Val.int qBN) + 1 ≤ 4096 * E := by
    linarith [hv_i1, hv_qBN, hE1]
  have hc15 : Ksw * (vsz (Val.int (1:ℤ)) + vsz (Val.int qBN) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKsw hb15
  have s15 : SEq main swapP (Val.int (1:ℤ) :: Val.int qBN :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qBN :: Val.int (1:ℤ) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    swapS hK hswap (Val.int (1:ℤ)) (Val.int qBN) (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc15

  have hb16 : isz (qBN) + isz ((1:ℤ)) ≤ 4096 * E := by
    calc isz (qBN) + isz ((1:ℤ)) ≤ (6 * (p * r) + 3) + (4) := Nat.add_le_add f_qBN f_1
      _ ≤ 4096 * E := by linarith [hEpr, hEppr, hEp, hEr, hE1]
  have hc16 : Ksb * (isz (qBN) + isz ((1:ℤ))) ≤ M := by
    rw [hM]
    exact Nat.mul_le_mul hTKsb hb16
  have s16 : SEq main subP (Val.int (qBN) :: Val.int ((1:ℤ)) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hsub main) (qBN) ((1:ℤ)) qBNm (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqBNm trivial M hc16

  have hb17 : (2 + 1) * (vsz (Val.int qBNm) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 2) (by norm_num) (by linarith [hv_qBNm, hv_qD, hv_ip, hE1])
  have hc17 : Kpi * (2 + 1) * (vsz (Val.int qBNm) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb17
  have s17 : SEq main (pickP 2) (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (p:ℤ) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick2S hK hpick hTKpi hM (Val.int qBNm) (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ) :: S) hc17

  have hb18 : vsz (Val.int (3:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i3, hE1]
  have hc18 : Kpu * (vsz (Val.int (3:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb18
  have s18 : SEq main (pushP (Val.int (3:ℤ))) (Val.int (p:ℤ) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (3:ℤ) :: Val.int (p:ℤ) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (3:ℤ)) (Val.int (p:ℤ) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc18

  have hb19 : isz ((3:ℤ)) * isz ((p:ℤ)) ≤ 4096 * E := by
    calc isz (3:ℤ) * isz (p:ℤ) ≤ 5 * (p + 3) := Nat.mul_le_mul f_3 f_p
      _ ≤ 4096 * E := by linarith [hEp, hE1]
  have hc19 : Kmu * isz ((3:ℤ)) * isz ((p:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb19
  have s19 : SEq main mulSP (Val.int ((3:ℤ)) :: Val.int ((p:ℤ)) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q3 :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((3:ℤ)) ((p:ℤ)) q3 (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq3 trivial M hc19

  have hb20 : (q3).toNat + isz (q3) ≤ 4096 * E := ub_pow3 (A := q3.toNat) (B := isz q3) (by rw [g3]) f_q3 hEp hE1
  have hc20 : Kpw * ((q3).toNat + isz (q3)) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpw hb20
  have s20 : SEq main pow2P (Val.int (q3) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qB :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    unS hK (hpow2 main) (q3) qB (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqB hpos3 M hc20

  have hb21 : vsz (Val.int (1:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i1, hE1]
  have hc21 : Kpu * (vsz (Val.int (1:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb21
  have s21 : SEq main (pushP (Val.int (1:ℤ))) (Val.int qB :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (1:ℤ) :: Val.int qB :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (1:ℤ)) (Val.int qB :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc21

  have hb22 : vsz (Val.int (1:ℤ)) + vsz (Val.int qB) + 1 ≤ 4096 * E := by
    linarith [hv_i1, hv_qB, hE1]
  have hc22 : Ksw * (vsz (Val.int (1:ℤ)) + vsz (Val.int qB) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKsw hb22
  have s22 : SEq main swapP (Val.int (1:ℤ) :: Val.int qB :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qB :: Val.int (1:ℤ) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    swapS hK hswap (Val.int (1:ℤ)) (Val.int qB) (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc22

  have hb23 : isz (qB) + isz ((1:ℤ)) ≤ 4096 * E := by
    calc isz (qB) + isz ((1:ℤ)) ≤ (3 * p + 3) + (4) := Nat.add_le_add f_qB f_1
      _ ≤ 4096 * E := by linarith [hEpr, hEppr, hEp, hEr, hE1]
  have hc23 : Ksb * (isz (qB) + isz ((1:ℤ))) ≤ M := by
    rw [hM]
    exact Nat.mul_le_mul hTKsb hb23
  have s23 : SEq main subP (Val.int (qB) :: Val.int ((1:ℤ)) :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qBm :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hsub main) (qB) ((1:ℤ)) qBm (Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqBm trivial M hc23

  have hb24 : vsz (Val.int qBm) + vsz (Val.int qBNm) + 1 ≤ 4096 * E := by
    linarith [hv_qBm, hv_qBNm, hE1]
  have hc24 : Ksw * (vsz (Val.int qBm) + vsz (Val.int qBNm) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKsw hb24
  have s24 : SEq main swapP (Val.int qBm :: Val.int qBNm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qBNm :: Val.int qBm :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    swapS hK hswap (Val.int qBm) (Val.int qBNm) (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc24

  have hb25 : isz (qBNm) * isz (qBm) ≤ 4096 * E := by
    exact ub_6pr3p f_qBNm f_qBm hEpr hEppr hEp hEr hE1
  have hc25 : Ktd * isz (qBNm) * isz (qBm) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKtd hb25
  have s25 : SEq main tdivP (Val.int (qBNm) :: Val.int (qBm) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (htdiv main) (qBNm) (qBm) qS (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqS hneBm M hc25

  have hb26 : (2 + 1) * (vsz (Val.int qS) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 2) (by norm_num) (by linarith [hv_qS, hv_qD, hv_ip, hE1])
  have hc26 : Kpi * (2 + 1) * (vsz (Val.int qS) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb26
  have s26 : SEq main (pickP 2) (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (p:ℤ) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick2S hK hpick hTKpi hM (Val.int qS) (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ) :: S) hc26

  have hb27 : vsz (Val.int (3:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i3, hE1]
  have hc27 : Kpu * (vsz (Val.int (3:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb27
  have s27 : SEq main (pushP (Val.int (3:ℤ))) (Val.int (p:ℤ) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (3:ℤ) :: Val.int (p:ℤ) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (3:ℤ)) (Val.int (p:ℤ) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc27

  have hb28 : isz ((3:ℤ)) * isz ((p:ℤ)) ≤ 4096 * E := by
    calc isz (3:ℤ) * isz (p:ℤ) ≤ 5 * (p + 3) := Nat.mul_le_mul f_3 f_p
      _ ≤ 4096 * E := by linarith [hEp, hE1]
  have hc28 : Kmu * isz ((3:ℤ)) * isz ((p:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb28
  have s28 : SEq main mulSP (Val.int ((3:ℤ)) :: Val.int ((p:ℤ)) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q3 :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((3:ℤ)) ((p:ℤ)) q3 (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq3 trivial M hc28

  have hb29 : vsz (Val.int (1:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i1, hE1]
  have hc29 : Kpu * (vsz (Val.int (1:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb29
  have s29 : SEq main (pushP (Val.int (1:ℤ))) (Val.int q3 :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (1:ℤ) :: Val.int q3 :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (1:ℤ)) (Val.int q3 :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc29

  have hb30 : vsz (Val.int (1:ℤ)) + vsz (Val.int q3) + 1 ≤ 4096 * E := by
    linarith [hv_i1, hv_q3, hE1]
  have hc30 : Ksw * (vsz (Val.int (1:ℤ)) + vsz (Val.int q3) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKsw hb30
  have s30 : SEq main swapP (Val.int (1:ℤ) :: Val.int q3 :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q3 :: Val.int (1:ℤ) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    swapS hK hswap (Val.int (1:ℤ)) (Val.int q3) (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc30

  have hb31 : isz (q3) + isz ((1:ℤ)) ≤ 4096 * E := by
    calc isz (q3) + isz ((1:ℤ)) ≤ (3 * p + 3) + (4) := Nat.add_le_add f_q3 f_1
      _ ≤ 4096 * E := by linarith [hEpr, hEppr, hEp, hEr, hE1]
  have hc31 : Ksb * (isz (q3) + isz ((1:ℤ))) ≤ M := by
    rw [hM]
    exact Nat.mul_le_mul hTKsb hb31
  have s31 : SEq main subP (Val.int (q3) :: Val.int ((1:ℤ)) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qT :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hsub main) (q3) ((1:ℤ)) qT (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqT trivial M hc31

  have hb32 : (qT).toNat + isz (qT) ≤ 4096 * E := ub_pow3 (A := qT.toNat) (B := isz qT) (by rw [gT]; exact Nat.sub_le _ _) f_qT hEp hE1
  have hc32 : Kpw * ((qT).toNat + isz (qT)) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpw hb32
  have s32 : SEq main pow2P (Val.int (qT) :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qTm :: Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    unS hK (hpow2 main) (qT) qTm (Val.int qS :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqTm hposT M hc32

  have hb33 : isz (qTm) * isz (qS) ≤ 4096 * E := by
    exact ub_3p6pr f_qTm f_qS hEpr hEppr hEp hEr hE1
  have hc33 : Kmu * isz (qTm) * isz (qS) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb33
  have s33 : SEq main mulSP (Val.int (qTm) :: Val.int (qS) :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) (qTm) (qS) qC (Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hqC trivial M hc33

  have hb34 : (3 + 1) * (vsz (Val.int qC) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 3) (by norm_num) (by linarith [hv_qC, hv_qD, hv_ip, hv_ir, hE1])
  have hc34 : Kpi * (3 + 1) * (vsz (Val.int qC) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + vsz (Val.int (r:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb34
  have s34 : SEq main (pickP 3) (Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (r:ℤ) :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick3S hK hpick hTKpi hM (Val.int qC) (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ)) (S) hc34

  have hb35 : vsz (Val.int (2:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i2, hE1]
  have hc35 : Kpu * (vsz (Val.int (2:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb35
  have s35 : SEq main (pushP (Val.int (2:ℤ))) (Val.int (r:ℤ) :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (2:ℤ) :: Val.int (r:ℤ) :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (2:ℤ)) (Val.int (r:ℤ) :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc35

  have hb36 : isz ((2:ℤ)) * isz ((r:ℤ)) ≤ 4096 * E := by
    calc isz (2:ℤ) * isz (r:ℤ) ≤ 5 * (r + 3) := Nat.mul_le_mul f_2 f_r
      _ ≤ 4096 * E := by linarith [hEr, hE1]
  have hc36 : Kmu * isz ((2:ℤ)) * isz ((r:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb36
  have s36 : SEq main mulSP (Val.int ((2:ℤ)) :: Val.int ((r:ℤ)) :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((2:ℤ)) ((r:ℤ)) q2 (Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq2 trivial M hc36

  have hb37 : (3 + 1) * (vsz (Val.int q2) + vsz (Val.int qC) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ 4096 * E :=
    ub_mul4 (k := 3) (by norm_num) (by linarith [hv_q2, hv_qC, hv_qD, hv_ip, hE1])
  have hc37 : Kpi * (3 + 1) * (vsz (Val.int q2) + vsz (Val.int qC) + vsz (Val.int qD) + vsz (Val.int (p:ℤ)) + 1) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKpi hb37
  have s37 : SEq main (pickP 3) (Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (p:ℤ) :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pick3S hK hpick hTKpi hM (Val.int q2) (Val.int qC) (Val.int qD) (Val.int (p:ℤ)) (Val.int (r:ℤ) :: S) hc37

  have hb38 : vsz (Val.int (3:ℤ)) + 1 ≤ 4096 * E := by linarith [hv_i3, hE1]
  have hc38 : Kpu * (vsz (Val.int (3:ℤ)) + 1) ≤ M := by
    rw [hM]; exact Nat.mul_le_mul hTKpu hb38
  have s38 : SEq main (pushP (Val.int (3:ℤ))) (Val.int (p:ℤ) :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int (3:ℤ) :: Val.int (p:ℤ) :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    pushS hK hpush (Val.int (3:ℤ)) (Val.int (p:ℤ) :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M hc38

  have hb39 : isz ((3:ℤ)) * isz ((p:ℤ)) ≤ 4096 * E := by
    calc isz (3:ℤ) * isz (p:ℤ) ≤ 5 * (p + 3) := Nat.mul_le_mul f_3 f_p
      _ ≤ 4096 * E := by linarith [hEp, hE1]
  have hc39 : Kmu * isz ((3:ℤ)) * isz ((p:ℤ)) ≤ M := by
    rw [hM, mul_assoc]
    exact Nat.mul_le_mul hTKmu hb39
  have s39 : SEq main mulSP (Val.int ((3:ℤ)) :: Val.int ((p:ℤ)) :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) (Val.int q3 :: Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) M :=
    binS hK (hmulS main) ((3:ℤ)) ((p:ℤ)) q3 (Val.int q2 :: Val.int qC :: Val.int qD :: Val.int (p:ℤ) :: Val.int (r:ℤ) :: S) hq3 trivial M hc39


  have t1 := s1
  have t2 := SEq.composeE (Φ := 2 * M) hK t1 s2 rfl (le_of_eq (by ring))
  have t3 := SEq.composeE (Φ := 3 * M) hK t2 s3 rfl (le_of_eq (by ring))
  have t4 := SEq.composeE (Φ := 4 * M) hK t3 s4 rfl (le_of_eq (by ring))
  have t5 := SEq.composeE (Φ := 5 * M) hK t4 s5 rfl (le_of_eq (by ring))
  have t6 := SEq.composeE (Φ := 6 * M) hK t5 s6 rfl (le_of_eq (by ring))
  have t7 := SEq.composeE (Φ := 7 * M) hK t6 s7 rfl (le_of_eq (by ring))
  have t8 := SEq.composeE (Φ := 8 * M) hK t7 s8 rfl (le_of_eq (by ring))
  have t9 := SEq.composeE (Φ := 9 * M) hK t8 s9 rfl (le_of_eq (by ring))
  have t10 := SEq.composeE (Φ := 10 * M) hK t9 s10 rfl (le_of_eq (by ring))
  have t11 := SEq.composeE (Φ := 11 * M) hK t10 s11 rfl (le_of_eq (by ring))
  have t12 := SEq.composeE (Φ := 12 * M) hK t11 s12 rfl (le_of_eq (by ring))
  have t13 := SEq.composeE (Φ := 13 * M) hK t12 s13 rfl (le_of_eq (by ring))
  have t14 := SEq.composeE (Φ := 14 * M) hK t13 s14 rfl (le_of_eq (by ring))
  have t15 := SEq.composeE (Φ := 15 * M) hK t14 s15 rfl (le_of_eq (by ring))
  have t16 := SEq.composeE (Φ := 16 * M) hK t15 s16 rfl (le_of_eq (by ring))
  have t17 := SEq.composeE (Φ := 17 * M) hK t16 s17 rfl (le_of_eq (by ring))
  have t18 := SEq.composeE (Φ := 18 * M) hK t17 s18 rfl (le_of_eq (by ring))
  have t19 := SEq.composeE (Φ := 19 * M) hK t18 s19 rfl (le_of_eq (by ring))
  have t20 := SEq.composeE (Φ := 20 * M) hK t19 s20 rfl (le_of_eq (by ring))
  have t21 := SEq.composeE (Φ := 21 * M) hK t20 s21 rfl (le_of_eq (by ring))
  have t22 := SEq.composeE (Φ := 22 * M) hK t21 s22 rfl (le_of_eq (by ring))
  have t23 := SEq.composeE (Φ := 23 * M) hK t22 s23 rfl (le_of_eq (by ring))
  have t24 := SEq.composeE (Φ := 24 * M) hK t23 s24 rfl (le_of_eq (by ring))
  have t25 := SEq.composeE (Φ := 25 * M) hK t24 s25 rfl (le_of_eq (by ring))
  have t26 := SEq.composeE (Φ := 26 * M) hK t25 s26 rfl (le_of_eq (by ring))
  have t27 := SEq.composeE (Φ := 27 * M) hK t26 s27 rfl (le_of_eq (by ring))
  have t28 := SEq.composeE (Φ := 28 * M) hK t27 s28 rfl (le_of_eq (by ring))
  have t29 := SEq.composeE (Φ := 29 * M) hK t28 s29 rfl (le_of_eq (by ring))
  have t30 := SEq.composeE (Φ := 30 * M) hK t29 s30 rfl (le_of_eq (by ring))
  have t31 := SEq.composeE (Φ := 31 * M) hK t30 s31 rfl (le_of_eq (by ring))
  have t32 := SEq.composeE (Φ := 32 * M) hK t31 s32 rfl (le_of_eq (by ring))
  have t33 := SEq.composeE (Φ := 33 * M) hK t32 s33 rfl (le_of_eq (by ring))
  have t34 := SEq.composeE (Φ := 34 * M) hK t33 s34 rfl (le_of_eq (by ring))
  have t35 := SEq.composeE (Φ := 35 * M) hK t34 s35 rfl (le_of_eq (by ring))
  have t36 := SEq.composeE (Φ := 36 * M) hK t35 s36 rfl (le_of_eq (by ring))
  have t37 := SEq.composeE (Φ := 37 * M) hK t36 s37 rfl (le_of_eq (by ring))
  have t38 := SEq.composeE (Φ := 38 * M) hK t37 s38 rfl (le_of_eq (by ring))
  have t39 := SEq.composeE (Φ := 39 * M) hK t38 s39 rfl (le_of_eq (by ring))

  -- final conversion
  have e3 : Val.int q3 = Val.int (3 * p : ℤ) := by rw [hq3]
  have e2 : Val.int q2 = Val.int (2 * r : ℤ) := by rw [hq2]
  have eD : Val.int qD = Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) := by rw [hqD, gE]
  have hCval : qC = digitOffset p (2 * r) := by
    rw [hqC, hqTm, hqS, hqBNm, hqBm, hqBN, hqB, hqT, hq6, hq3, hq2, ggT, gg6, gg3,
      show 2 * r * (3 * p) = 3 * p * (2 * r) by ring]
    exact (digitOffsetTdiv p (2 * r) hp).symm
  have eC : Val.int qC = Val.int (digitOffset p (2 * r)) := by rw [hCval]
  have hA : Val.int q3 :: Val.int q2 :: Val.int qC :: Val.int qD ::
      Val.int (p : ℤ) :: Val.int (r : ℤ) :: S
      = Val.int (3 * p : ℤ) :: Val.int (2 * r : ℤ) :: Val.int (digitOffset p (2 * r)) ::
        Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
        Val.int (p : ℤ) :: Val.int (r : ℤ) :: S := by
    rw [e3, e2, eC, eD]
  have hfinal : 39 * M ≤ (1048576 * T) * (r + 1) * (p + 1) ^ 2 := by
    rw [hM, hE, mul_assoc]
    exact ub_final
  refine hK.conseq main _ _ _ _ _ _ _ t39 ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hpost
    rw [hpost]
    exact hA
  · intro vs hvs; exact hfinal

end Work.KronP
