import Mathlib
import Submission.Work.Fx.ExpDefs
import Submission.Work.Fx.FxAdapt

/-!
# The Horner stage of the fixed-point exponential (`Work.Fx.expStepB`)

One Horner stage of the fixed-point complex exponential maps the state window

`(Nre, Nim, dd, Zs, Zt, Pow, d0)`

to

`(Pow + ⌊⌊Nre/Pow⌋/dd⌋, ⌊⌊Nim/Pow⌋/dd⌋, dd - 1, Zs, Zt, Pow, d0)`:

both numerators `Nre`, `Nim` are divided by `Pow` and then by `dd`, the divisor `dd` is
decremented, and the parameters `Zs, Zt, Pow, d0` are carried along untouched.

The 30-step StackLang program is a chain of `KernelLib` / `IntLib` words (`pick`, `dup`, `roll`,
`swap`, `IntLib.tdiv`, `IntLib.sub`, `IntLib.add`, a constant push and a `drop`); each step is
bounded by `quadCost c = c * (szl · + 1)^2` for a *constant* `c` built from the library constants,
and every intermediate window has size at most three times the previous one, so the total cost is
still `O((szl · + 1)^2)`, hence `≤ K * (szl · + 1)^K` for a fixed `K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx

open HvdH

/-! ## Quadratic cost bounds with constant coefficients -/

/-- The normalised quadratic cost bound `t ↦ c * (szl t + 1)^2`. -/
def quadCost (c : ℕ) : List Val → ℕ := fun t => c * (szl t + 1) ^ 2

theorem linCost_le_quadCost (c : ℕ) (t : List Val) : linCost c t ≤ quadCost c t := by
  have h : (szl t + 1) ^ 1 ≤ (szl t + 1) ^ 2 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ szl t + 1) (by norm_num)
  have h2 : szl t + 1 ≤ (szl t + 1) ^ 2 := by simpa using h
  simp only [linCost, quadCost]
  exact Nat.mul_le_mul_left c h2

theorem linCost_le_quadCost_of_le {c x : ℕ} {t : List Val} (h : x ≤ szl t) :
    linCost (c * (x + 1)) t ≤ quadCost c t := by
  simp only [linCost, quadCost]
  have h1 : x + 1 ≤ szl t + 1 := by omega
  calc c * (x + 1) * (szl t + 1) ≤ c * (szl t + 1) * (szl t + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = c * (szl t + 1) ^ 2 := by ring

theorem isz_two_le (z : ℤ) : 2 ≤ isz z := by simp only [isz]; omega

theorem isz_le_szl_of_mem {x : ℤ} {l : List Val} (h : Val.int x ∈ l) : isz x ≤ szl l := by
  have h1 := le_szl h
  rwa [vsz_int] at h1

theorem linCost_dupQ {c : ℕ} {A : Val} {E : List Val} :
    linCost (c * (vsz A + 1)) ([A] ++ E) ≤ quadCost c ([A] ++ E) :=
  linCost_le_quadCost_of_le (c := c) (x := vsz A) (le_szl (by simp))

theorem mul_le_sq_of {x y X K : ℕ} (hx : x ≤ X) (hy : y ≤ X) : K * x * y ≤ K * (X + 1) ^ 2 := by
  have h : x * y ≤ (X + 1) ^ 2 := by nlinarith
  calc K * x * y = K * (x * y) := by ring
    _ ≤ K * (X + 1) ^ 2 := Nat.mul_le_mul_left _ h

theorem add_le_sq_of {x y X K : ℕ} (hx : x ≤ X) (hy : y ≤ X) : K * (x + y) ≤ K * (X + 1) ^ 2 := by
  have h : x + y ≤ (X + 1) ^ 2 := by nlinarith
  exact Nat.mul_le_mul_left _ h

theorem quadCost_le (c : ℕ) (t : List Val) :
    quadCost c t ≤ max c 2 * (szl t + 1) ^ (max c 2) := by
  have h2 : 2 ≤ max c 2 := le_max_right _ _
  have hc : c ≤ max c 2 := le_max_left _ _
  have hpow : (szl t + 1) ^ 2 ≤ (szl t + 1) ^ (max c 2) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ szl t + 1) h2
  simp only [quadCost]
  calc c * (szl t + 1) ^ 2 ≤ max c 2 * (szl t + 1) ^ 2 := Nat.mul_le_mul_right _ hc
    _ ≤ max c 2 * (szl t + 1) ^ (max c 2) := Nat.mul_le_mul_left _ hpow

/-- Turn a linear-cost exact-window step into a quadratic-cost one. -/
theorem Spec.toQuad (hk : KernelLib) {main p : Cmd} {n : ℕ} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {c : ℕ} (h : Spec main p n P Q (linCost c)) :
    Spec main p n P Q (quadCost c) :=
  Spec.mono hk h (fun t _ h => h) (fun t o _ _ h => h) (fun t _ _ => linCost_le_quadCost c t)

/-- Quadratic-cost chaining of two exact-window deterministic steps. -/
theorem Spec.seqQuad (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val} {c1 c2 M : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) (quadCost c1))
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (quadCost c2))
    (hB : B.length = m) (hsz : szl B + 1 ≤ M * (szl A + 1)) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (quadCost (c1 + c2 * M ^ 2)) := by
  have hcost : ∀ (t o : List Val), t.length = n → t = A → o = B →
      quadCost c2 o ≤ (c2 * M ^ 2) * (szl t + 1) ^ 2 := by
    intro t o _ hAt hBo
    rw [hAt, hBo]
    have h2' : (szl B + 1) ^ 2 ≤ (M * (szl A + 1)) ^ 2 := Nat.pow_le_pow_left hsz 2
    calc quadCost c2 B = c2 * (szl B + 1) ^ 2 := rfl
      _ ≤ c2 * (M * (szl A + 1)) ^ 2 := Nat.mul_le_mul_left _ h2'
      _ = (c2 * M ^ 2) * (szl A + 1) ^ 2 := by ring
  have h := Spec.seq hk (main := main) (p := p) (q := q) (n := n) (m := m)
    (P := fun t => t = A) (Q := fun _ o => o = B) (C := quadCost c1)
    (P' := fun t => t = B) (Q' := fun _ o => o = D) (C' := quadCost c2)
    (B := fun t => (c2 * M ^ 2) * (szl t + 1) ^ 2) h1 h2
    (by intro t o _ hAt hBo; rw [hBo]; exact hB)
    (by intro t o _ hAt hBo; rw [hBo])
    hcost
  refine Spec.mono hk h (fun t _ h => h) ?_ ?_
  · intro t o _ _ hQ
    rcases hQ with ⟨m', hm', hD⟩
    exact hD
  · intro t _ _
    show quadCost c1 t + (c2 * M ^ 2) * (szl t + 1) ^ 2 ≤ quadCost (c1 + c2 * M ^ 2) t
    simp only [quadCost]
    have : (c1 + c2 * M ^ 2) * (szl t + 1) ^ 2
        = c1 * (szl t + 1) ^ 2 + (c2 * M ^ 2) * (szl t + 1) ^ 2 := by ring
    rw [this]

/-- A `BinOp` on the top two values of a window, with a quadratic cost bound. -/
theorem Spec.binOpQuad (hk : KernelLib) {main cOp : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main cOp P f C) {A0 B0 : ℤ} (hP : P A0 B0) {E : List Val} {KK : ℕ}
    (hC : C A0 B0 ≤ KK * (szl ([.int A0, .int B0] ++ E) + 1) ^ 2) :
    Spec main cOp (2 + E.length) (fun t => t = [.int A0, .int B0] ++ E)
      (fun _ o => o = [.int (f A0 B0)] ++ E) (quadCost KK) := by
  have h1 : Spec main cOp 2 (fun t => t = [.int A0, .int B0])
      (fun _ o => o = [.int (f A0 B0)]) (binCost C) := by
    refine Spec.mono hk (Spec.binOp hk h) ?_ ?_ ?_
    · intro t ht hq
      rw [hq]
      exact ⟨A0, B0, rfl, hP⟩
    · intro t o ht hq hQ
      rcases hQ with ⟨a, b, hab, ho⟩
      have e1 : ([.int a, .int b] : List Val) = [.int A0, .int B0] := Eq.trans (Eq.symm hab) hq
      have e2 := List.cons.inj e1
      have e3 := List.cons.inj e2.2
      rw [ho, Val.int.inj e2.1, Val.int.inj e3.1]
    · intro t ht hq
      rw [hq]
  have h2 : Spec main cOp (2 + E.length) (fun t => t = [.int A0, .int B0] ++ E)
      (fun _ o => o = [.int (f A0 B0)] ++ E) (fun _ => binCost C [.int A0, .int B0]) :=
    Spec.extend_exact hk h1 (E := E) (k := E.length) rfl
  refine Spec.mono hk h2 (fun t _ ht => ht) (fun t o _ _ hq => hq) ?_
  intro t _ ht
  rw [ht]
  show C A0 B0 ≤ KK * (szl ([.int A0, .int B0] ++ E) + 1) ^ 2
  exact hC

/-! ## Size helpers -/

theorem isz_one : isz (1 : ℤ) = 3 := by decide

theorem isz_add_lin (x y : ℤ) : isz (x + y) ≤ isz x + isz y := by
  have h := isz_add_le x y
  have hx : 2 ≤ isz x := by simp only [isz]; omega
  have hy : 2 ≤ isz y := by simp only [isz]; omega
  omega

theorem isz_sub_lin (x y : ℤ) : isz (x - y) ≤ isz x + isz y := by
  have h := isz_sub_le x y
  have hx : 2 ≤ isz x := by simp only [isz]; omega
  have hy : 2 ≤ isz y := by simp only [isz]; omega
  omega

/-! ## Exact-window adapters -/

/-- `pick` on an exact window of length `k + 1`. -/
theorem Spec.pickEx (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {W : List Val} (hW : W.length = k + 1) {v : Val} (hv : W.getD k .nil = v) :
    Spec main prog (k + 1) (fun t => t = W) (fun _ o => o = v :: W) (linCost (K * (k + 1))) := by
  refine Spec.mono hk (Spec.pickK hk h) (fun t _ _ => trivial) ?_ ?_
  · intro t o _ ht hQ
    rw [ht] at hQ
    rw [hQ, hv]
  · intro t _ ht
    rw [ht]
    rfl

/-- `dup` on an exact window of length one. -/
theorem Spec.dupEx (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (A : Val) :
    Spec main prog 1 (fun t => t = [A]) (fun _ o => o = [A, A]) (linCost (K * (vsz A + 1))) := by
  refine Spec.mono hk (Spec.dupK hk h) (fun t _ _ => trivial) ?_ ?_
  · intro t o _ ht hQ
    rw [ht] at hQ
    rcases hQ with ⟨v, hv, hout⟩
    have h1 : A = v := (List.cons.inj hv).1
    rw [hout, ← h1]
  · intro t _ ht
    rw [ht]
    show K * (vsz (([A] : List Val).getD 0 .nil) + 1) ≤ linCost (K * (vsz A + 1)) [A]
    rw [List.getD_cons_zero]
    simp only [linCost, szl_cons, szl_nil, List.sum_cons, List.sum_nil]
    calc K * (vsz A + 1) = K * (vsz A + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ K * (vsz A + 1) * (vsz A + 0 + 1) := Nat.mul_le_mul_left _ (by omega)

/-- `drop` on an exact window of length one. -/
theorem Spec.dropEx (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) (A : Val) :
    Spec main prog 1 (fun t => t = [A]) (fun _ o => o = []) (linCost (K * (vsz A + 1))) := by
  refine Spec.mono hk (Spec.dropK hk h) (fun t _ _ => trivial) (fun t o _ _ h => h) ?_
  intro t _ ht
  rw [ht]
  show K * (vsz (([A] : List Val).getD 0 .nil) + 1) ≤ linCost (K * (vsz A + 1)) [A]
  rw [List.getD_cons_zero]
  simp only [linCost, szl_cons, szl_nil, List.sum_cons, List.sum_nil]
  calc K * (vsz A + 1) = K * (vsz A + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ K * (vsz A + 1) * (vsz A + 0 + 1) := Nat.mul_le_mul_left _ (by omega)

/-! ## The 30-step chain -/

theorem expStepBChain (hk : KernelLib) (hi : IntLib) :
    ∃ (prog : Cmd) (M : ℕ), ∀ (main : Cmd) (a b c s tt p e : ℤ), p ≠ 0 → c ≠ 0 →
      Spec main prog 7
        (fun t => t = [.int a, .int b, .int c, .int s, .int tt, .int p, .int e])
        (fun _ o => o = [.int (Int.tdiv (Int.tdiv a p) c + p), .int (Int.tdiv (Int.tdiv b p) c),
          .int (c - 1), .int s, .int tt, .int p, .int e])
        (fun t => M * (szl t + 1) ^ M) := by
  obtain ⟨cPk, KPk, hPk⟩ := hk.pick
  obtain ⟨cD, KD, hD⟩ := hk.dup
  obtain ⟨cDr, KDr, hDr⟩ := hk.drop
  obtain ⟨cR, KR, hR⟩ := hk.roll
  obtain ⟨cS, KS, hS⟩ := hk.swap
  obtain ⟨cPv, KPv, hPv⟩ := hk.pushVal
  obtain ⟨cT, KT, hT⟩ := hi.tdiv
  obtain ⟨cSb, KSb, hSb⟩ := hi.sub
  obtain ⟨cAd, KAd, hAd⟩ := hi.add
  -- per-step coefficient bounds (library constants only)
  let C1 : ℕ := KPk * (5 + 1)
  let C2 : ℕ := KD
  let C3 : ℕ := KD
  let C4 : ℕ := KPk * (5 + 1)
  let C5 : ℕ := KD
  let C6 : ℕ := KD
  let C7 : ℕ := KR * (6 + 1)
  let C8 : ℕ := KR * (4 + 1)
  let C9 : ℕ := 3 * KS
  let C10 : ℕ := KT
  let C11 : ℕ := KT
  let C12 : ℕ := KR * (5 + 1)
  let C13 : ℕ := KR * (4 + 1)
  let C14 : ℕ := 3 * KS
  let C15 : ℕ := KT
  let C16 : ℕ := KR * (2 + 1)
  let C17 : ℕ := 3 * KS
  let C18 : ℕ := KT
  let C19 : ℕ := KR * (2 + 1)
  let C20 : ℕ := KPv * (vsz (.int 1) + 1)
  let C21 : ℕ := 3 * KS
  let C22 : ℕ := KSb
  let C23 : ℕ := KR * (2 + 1)
  let C24 : ℕ := KR * (3 + 1)
  let C25 : ℕ := 3 * KS
  let C26 : ℕ := KAd
  let C27 : ℕ := KR * (2 + 1)
  let C28 : ℕ := 3 * KS
  let C29 : ℕ := KR * (3 + 1)
  let C30 : ℕ := KDr
  -- accumulated coefficients (a window may grow by a factor 3 per step)
  let K30 : ℕ := C30
  let K29 : ℕ := C29 + K30 * (3 ^ 2)
  let K28 : ℕ := C28 + K29 * (3 ^ 2)
  let K27 : ℕ := C27 + K28 * (3 ^ 2)
  let K26 : ℕ := C26 + K27 * (3 ^ 2)
  let K25 : ℕ := C25 + K26 * (3 ^ 2)
  let K24 : ℕ := C24 + K25 * (3 ^ 2)
  let K23 : ℕ := C23 + K24 * (3 ^ 2)
  let K22 : ℕ := C22 + K23 * (3 ^ 2)
  let K21 : ℕ := C21 + K22 * (3 ^ 2)
  let K20 : ℕ := C20 + K21 * (3 ^ 2)
  let K19 : ℕ := C19 + K20 * (3 ^ 2)
  let K18 : ℕ := C18 + K19 * (3 ^ 2)
  let K17 : ℕ := C17 + K18 * (3 ^ 2)
  let K16 : ℕ := C16 + K17 * (3 ^ 2)
  let K15 : ℕ := C15 + K16 * (3 ^ 2)
  let K14 : ℕ := C14 + K15 * (3 ^ 2)
  let K13 : ℕ := C13 + K14 * (3 ^ 2)
  let K12 : ℕ := C12 + K13 * (3 ^ 2)
  let K11 : ℕ := C11 + K12 * (3 ^ 2)
  let K10 : ℕ := C10 + K11 * (3 ^ 2)
  let K9 : ℕ := C9 + K10 * (3 ^ 2)
  let K8 : ℕ := C8 + K9 * (3 ^ 2)
  let K7 : ℕ := C7 + K8 * (3 ^ 2)
  let K6 : ℕ := C6 + K7 * (3 ^ 2)
  let K5 : ℕ := C5 + K6 * (3 ^ 2)
  let K4 : ℕ := C4 + K5 * (3 ^ 2)
  let K3 : ℕ := C3 + K4 * (3 ^ 2)
  let K2 : ℕ := C2 + K3 * (3 ^ 2)
  let K1 : ℕ := C1 + K2 * (3 ^ 2)

  let prog : Cmd := (.seq (cPk 5) (.seq (cD) (.seq (cD) (.seq (cPk 5) (.seq (cD) (.seq (cD) (.seq (cR 6) (.seq (cR 4) (.seq (cS) (.seq (cT) (.seq (cT) (.seq (cR 5) (.seq (cR 4) (.seq (cS) (.seq (cT) (.seq (cR 2) (.seq (cS) (.seq (cT) (.seq (cR 2) (.seq (cPv (.int 1)) (.seq (cS) (.seq (cSb) (.seq (cR 2) (.seq (cR 3) (.seq (cS) (.seq (cAd) (.seq (cR 2) (.seq (cS) (.seq (cR 3) cDr)))))))))))))))))))))))))))))
  refine ⟨prog, max K1 2, ?_⟩
  intro main a b c s tt p e hp hc
  -- windows
  let W0 : List Val := [.int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W1 : List Val := [.int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W2 : List Val := [.int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W3 : List Val := [.int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W4 : List Val := [.int c, .int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W5 : List Val := [.int c, .int c, .int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W6 : List Val := [.int c, .int c, .int c, .int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W7 : List Val := [.int a, .int c, .int c, .int c, .int p, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W8 : List Val := [.int p, .int a, .int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W9 : List Val := [.int a, .int p, .int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W10 : List Val := [.int (Int.tdiv a p), .int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W11 : List Val := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]
  let W12 : List Val := [.int b, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W13 : List Val := [.int p, .int b, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W14 : List Val := [.int b, .int p, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W15 : List Val := [.int (Int.tdiv b p), .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W16 : List Val := [.int c, .int (Int.tdiv b p), .int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W17 : List Val := [.int (Int.tdiv b p), .int c, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W18 : List Val := [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]
  let W19 : List Val := [.int c, .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]
  let W20 : List Val := [.int 1, .int c, .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]
  let W21 : List Val := [.int c, .int 1, .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]
  let W22 : List Val := [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]
  let W23 : List Val := [.int (Int.tdiv (Int.tdiv a p) c), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int p, .int c, .int s, .int tt, .int p, .int e]
  let W24 : List Val := [.int p, .int (Int.tdiv (Int.tdiv a p) c), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]
  let W25 : List Val := [.int (Int.tdiv (Int.tdiv a p) c), .int p, .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]
  let W26 : List Val := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]
  let W27 : List Val := [.int (Int.tdiv (Int.tdiv b p) c), .int ((Int.tdiv (Int.tdiv a p) c) + p), .int (c - 1), .int c, .int s, .int tt, .int p, .int e]
  let W28 : List Val := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1), .int c, .int s, .int tt, .int p, .int e]
  let W29 : List Val := [.int c, .int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1), .int s, .int tt, .int p, .int e]
  let W30 : List Val := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1), .int s, .int tt, .int p, .int e]
  -- size facts about the computed values
  have h1z : isz (1 : ℤ) = 3 := isz_one
  have ha2 : 2 ≤ isz a := isz_two_le a
  have hb2 : 2 ≤ isz b := isz_two_le b
  have hc2 : 2 ≤ isz c := isz_two_le c
  have hs2 : 2 ≤ isz s := isz_two_le s
  have ht2 : 2 ≤ isz tt := isz_two_le tt
  have hp2 : 2 ≤ isz p := isz_two_le p
  have he2 : 2 ≤ isz e := isz_two_le e
  have hu : isz (Int.tdiv a p) ≤ isz a := isz_tdiv_le a p
  have huc : isz (Int.tdiv (Int.tdiv a p) c) ≤ isz (Int.tdiv a p) := isz_tdiv_le (Int.tdiv a p) c
  have hv : isz (Int.tdiv b p) ≤ isz b := isz_tdiv_le b p
  have hvc : isz (Int.tdiv (Int.tdiv b p) c) ≤ isz (Int.tdiv b p) := isz_tdiv_le (Int.tdiv b p) c
  have hd1 : isz (c - 1) ≤ isz c + isz (1 : ℤ) := isz_sub_lin c 1
  have hz : isz (Int.tdiv (Int.tdiv a p) c + p) ≤ isz (Int.tdiv (Int.tdiv a p) c) + isz p :=
    isz_add_lin (Int.tdiv (Int.tdiv a p) c) p
  have hsz1 : szl W1 + 1 ≤ 3 * (szl W0 + 1) := by
    simp only [W0, W1, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e1 : Spec main (cPk 5) 7 (fun t => t = W0) (fun _ o => o = W1) (quadCost C1) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.pickEx hk (k := 5) (hPk main 5) (W := [.int a, .int b, .int c, .int s, .int tt, .int p]) (by simp) (v := .int p) (by simp))
        (E := [.int e]) (k := 1) (by simp)))
  have hsz2 : szl W2 + 1 ≤ 3 * (szl W1 + 1) := by
    simp only [W1, W2, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e2 : Spec main (cD) 8 (fun t => t = W1) (fun _ o => o = W2) (quadCost C2) := by
    refine
      (Spec.mono hk (Spec.extendLin hk (Spec.dupEx hk (hD main) (.int p))
        (E := [.int a, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 7) (by simp))
        (fun t _ h => h) (fun t o _ _ h => h)) ?_
    intro t _ hq
    rw [hq]
    exact linCost_dupQ
  have hsz3 : szl W3 + 1 ≤ 3 * (szl W2 + 1) := by
    simp only [W2, W3, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e3 : Spec main (cD) 9 (fun t => t = W2) (fun _ o => o = W3) (quadCost C3) := by
    refine
      (Spec.mono hk (Spec.extendLin hk (Spec.dupEx hk (hD main) (.int p))
        (E := [.int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 8) (by simp))
        (fun t _ h => h) (fun t o _ _ h => h)) ?_
    intro t _ hq
    rw [hq]
    exact linCost_dupQ
  have hsz4 : szl W4 + 1 ≤ 3 * (szl W3 + 1) := by
    simp only [W3, W4, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e4 : Spec main (cPk 5) 10 (fun t => t = W3) (fun _ o => o = W4) (quadCost C4) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.pickEx hk (k := 5) (hPk main 5) (W := [.int p, .int p, .int p, .int a, .int b, .int c]) (by simp) (v := .int c) (by simp))
        (E := [.int s, .int tt, .int p, .int e]) (k := 4) (by simp)))
  have hsz5 : szl W5 + 1 ≤ 3 * (szl W4 + 1) := by
    simp only [W4, W5, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e5 : Spec main (cD) 11 (fun t => t = W4) (fun _ o => o = W5) (quadCost C5) := by
    refine
      (Spec.mono hk (Spec.extendLin hk (Spec.dupEx hk (hD main) (.int c))
        (E := [.int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 10) (by simp))
        (fun t _ h => h) (fun t o _ _ h => h)) ?_
    intro t _ hq
    rw [hq]
    exact linCost_dupQ
  have hsz6 : szl W6 + 1 ≤ 3 * (szl W5 + 1) := by
    simp only [W5, W6, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e6 : Spec main (cD) 12 (fun t => t = W5) (fun _ o => o = W6) (quadCost C6) := by
    refine
      (Spec.mono hk (Spec.extendLin hk (Spec.dupEx hk (hD main) (.int c))
        (E := [.int c, .int p, .int p, .int p, .int a, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 11) (by simp))
        (fun t _ h => h) (fun t o _ _ h => h)) ?_
    intro t _ hq
    rw [hq]
    exact linCost_dupQ
  have hsz7 : szl W7 + 1 ≤ 3 * (szl W6 + 1) := by
    simp only [W6, W7, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e7 : Spec main (cR 6) 13 (fun t => t = W6) (fun _ o => o = W7) (quadCost C7) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 6) (hR main 6) (W := [.int c, .int c, .int c, .int p, .int p, .int p, .int a]) (B := [.int a, .int c, .int c, .int c, .int p, .int p, .int p]) (by simp) (by rfl))
        (E := [.int b, .int c, .int s, .int tt, .int p, .int e]) (k := 6) (by simp)))
  have hsz8 : szl W8 + 1 ≤ 3 * (szl W7 + 1) := by
    simp only [W7, W8, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e8 : Spec main (cR 4) 13 (fun t => t = W7) (fun _ o => o = W8) (quadCost C8) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 4) (hR main 4) (W := [.int a, .int c, .int c, .int c, .int p]) (B := [.int p, .int a, .int c, .int c, .int c]) (by simp) (by rfl))
        (E := [.int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 8) (by simp)))
  have hsz9 : szl W9 + 1 ≤ 3 * (szl W8 + 1) := by
    simp only [W8, W9, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e9 : Spec main (cS) 13 (fun t => t = W8) (fun _ o => o = W9) (quadCost C9) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int p) (.int a))
        (E := [.int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) (k := 11) (by simp)))
  have hsz10 : szl W10 + 1 ≤ 3 * (szl W9 + 1) := by
    simp only [W9, W10, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e10 : Spec main (cT) 13 (fun t => t = W9) (fun _ o => o = W10) (quadCost C10) := by
    refine
      (Spec.binOpQuad hk (hT main) (A0 := a) (B0 := p) (hP := hp)
        (E := [.int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) (KK := KT)) ?_
    have h1 : isz a ≤ szl ([.int a, .int p] ++ [.int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz p ≤ szl ([.int a, .int p] ++ [.int c, .int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact mul_le_sq_of (K := KT) h1 h2
  have hsz11 : szl W11 + 1 ≤ 3 * (szl W10 + 1) := by
    simp only [W10, W11, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e11 : Spec main (cT) 12 (fun t => t = W10) (fun _ o => o = W11) (quadCost C11) := by
    refine
      (Spec.binOpQuad hk (hT main) (A0 := (Int.tdiv a p)) (B0 := c) (hP := hc)
        (E := [.int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) (KK := KT)) ?_
    have h1 : isz (Int.tdiv a p) ≤ szl ([.int (Int.tdiv a p), .int c] ++ [.int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz c ≤ szl ([.int (Int.tdiv a p), .int c] ++ [.int c, .int c, .int p, .int p, .int b, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact mul_le_sq_of (K := KT) h1 h2
  have hsz12 : szl W12 + 1 ≤ 3 * (szl W11 + 1) := by
    simp only [W11, W12, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e12 : Spec main (cR 5) 11 (fun t => t = W11) (fun _ o => o = W12) (quadCost C12) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 5) (hR main 5) (W := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int p, .int b]) (B := [.int b, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int p]) (by simp) (by rfl))
        (E := [.int c, .int s, .int tt, .int p, .int e]) (k := 5) (by simp)))
  have hsz13 : szl W13 + 1 ≤ 3 * (szl W12 + 1) := by
    simp only [W12, W13, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e13 : Spec main (cR 4) 11 (fun t => t = W12) (fun _ o => o = W13) (quadCost C13) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 4) (hR main 4) (W := [.int b, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p]) (B := [.int p, .int b, .int (Int.tdiv (Int.tdiv a p) c), .int c, .int c]) (by simp) (by rfl))
        (E := [.int p, .int c, .int s, .int tt, .int p, .int e]) (k := 6) (by simp)))
  have hsz14 : szl W14 + 1 ≤ 3 * (szl W13 + 1) := by
    simp only [W13, W14, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e14 : Spec main (cS) 11 (fun t => t = W13) (fun _ o => o = W14) (quadCost C14) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int p) (.int b))
        (E := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) (k := 9) (by simp)))
  have hsz15 : szl W15 + 1 ≤ 3 * (szl W14 + 1) := by
    simp only [W14, W15, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e15 : Spec main (cT) 11 (fun t => t = W14) (fun _ o => o = W15) (quadCost C15) := by
    refine
      (Spec.binOpQuad hk (hT main) (A0 := b) (B0 := p) (hP := hp)
        (E := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) (KK := KT)) ?_
    have h1 : isz b ≤ szl ([.int b, .int p] ++ [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz p ≤ szl ([.int b, .int p] ++ [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact mul_le_sq_of (K := KT) h1 h2
  have hsz16 : szl W16 + 1 ≤ 3 * (szl W15 + 1) := by
    simp only [W15, W16, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e16 : Spec main (cR 2) 10 (fun t => t = W15) (fun _ o => o = W16) (quadCost C16) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 2) (hR main 2) (W := [.int (Int.tdiv b p), .int (Int.tdiv (Int.tdiv a p) c), .int c]) (B := [.int c, .int (Int.tdiv b p), .int (Int.tdiv (Int.tdiv a p) c)]) (by simp) (by rfl))
        (E := [.int c, .int p, .int c, .int s, .int tt, .int p, .int e]) (k := 7) (by simp)))
  have hsz17 : szl W17 + 1 ≤ 3 * (szl W16 + 1) := by
    simp only [W16, W17, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e17 : Spec main (cS) 10 (fun t => t = W16) (fun _ o => o = W17) (quadCost C17) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int c) (.int (Int.tdiv b p)))
        (E := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) (k := 8) (by simp)))
  have hsz18 : szl W18 + 1 ≤ 3 * (szl W17 + 1) := by
    simp only [W17, W18, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e18 : Spec main (cT) 10 (fun t => t = W17) (fun _ o => o = W18) (quadCost C18) := by
    refine
      (Spec.binOpQuad hk (hT main) (A0 := (Int.tdiv b p)) (B0 := c) (hP := hc)
        (E := [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) (KK := KT)) ?_
    have h1 : isz (Int.tdiv b p) ≤ szl ([.int (Int.tdiv b p), .int c] ++ [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz c ≤ szl ([.int (Int.tdiv b p), .int c] ++ [.int (Int.tdiv (Int.tdiv a p) c), .int c, .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact mul_le_sq_of (K := KT) h1 h2
  have hsz19 : szl W19 + 1 ≤ 3 * (szl W18 + 1) := by
    simp only [W18, W19, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e19 : Spec main (cR 2) 9 (fun t => t = W18) (fun _ o => o = W19) (quadCost C19) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 2) (hR main 2) (W := [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int c]) (B := [.int c, .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c)]) (by simp) (by rfl))
        (E := [.int p, .int c, .int s, .int tt, .int p, .int e]) (k := 6) (by simp)))
  have hsz20 : szl W20 + 1 ≤ 3 * (szl W19 + 1) := by
    simp only [W19, W20, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e20 : Spec main (cPv (.int 1)) 9 (fun t => t = W19) (fun _ o => o = W20) (quadCost C20) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.pushValEx' hk (hPv main (.int 1)))
        (E := [.int c, .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]) (k := 9) (by simp)))
  have hsz21 : szl W21 + 1 ≤ 3 * (szl W20 + 1) := by
    simp only [W20, W21, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e21 : Spec main (cS) 10 (fun t => t = W20) (fun _ o => o = W21) (quadCost C21) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int 1) (.int c))
        (E := [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]) (k := 8) (by simp)))
  have hsz22 : szl W22 + 1 ≤ 3 * (szl W21 + 1) := by
    simp only [W21, W22, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e22 : Spec main (cSb) 10 (fun t => t = W21) (fun _ o => o = W22) (quadCost C22) := by
    refine
      (Spec.binOpQuad hk (hSb main) (A0 := c) (B0 := 1) (hP := trivial)
        (E := [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]) (KK := KSb)) ?_
    have h1 : isz c ≤ szl ([.int c, .int 1] ++ [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz 1 ≤ szl ([.int c, .int 1] ++ [.int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c), .int p, .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact add_le_sq_of (K := KSb) h1 h2
  have hsz23 : szl W23 + 1 ≤ 3 * (szl W22 + 1) := by
    simp only [W22, W23, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e23 : Spec main (cR 2) 9 (fun t => t = W22) (fun _ o => o = W23) (quadCost C23) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 2) (hR main 2) (W := [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int (Int.tdiv (Int.tdiv a p) c)]) (B := [.int (Int.tdiv (Int.tdiv a p) c), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c)]) (by simp) (by rfl))
        (E := [.int p, .int c, .int s, .int tt, .int p, .int e]) (k := 6) (by simp)))
  have hsz24 : szl W24 + 1 ≤ 3 * (szl W23 + 1) := by
    simp only [W23, W24, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e24 : Spec main (cR 3) 9 (fun t => t = W23) (fun _ o => o = W24) (quadCost C24) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 3) (hR main 3) (W := [.int (Int.tdiv (Int.tdiv a p) c), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int p]) (B := [.int p, .int (Int.tdiv (Int.tdiv a p) c), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c)]) (by simp) (by rfl))
        (E := [.int c, .int s, .int tt, .int p, .int e]) (k := 5) (by simp)))
  have hsz25 : szl W25 + 1 ≤ 3 * (szl W24 + 1) := by
    simp only [W24, W25, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e25 : Spec main (cS) 9 (fun t => t = W24) (fun _ o => o = W25) (quadCost C25) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int p) (.int (Int.tdiv (Int.tdiv a p) c)))
        (E := [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]) (k := 7) (by simp)))
  have hsz26 : szl W26 + 1 ≤ 3 * (szl W25 + 1) := by
    simp only [W25, W26, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e26 : Spec main (cAd) 9 (fun t => t = W25) (fun _ o => o = W26) (quadCost C26) := by
    refine
      (Spec.binOpQuad hk (hAd main) (A0 := (Int.tdiv (Int.tdiv a p) c)) (B0 := p) (hP := trivial)
        (E := [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]) (KK := KAd)) ?_
    have h1 : isz (Int.tdiv (Int.tdiv a p) c) ≤ szl ([.int (Int.tdiv (Int.tdiv a p) c), .int p] ++ [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    have h2 : isz p ≤ szl ([.int (Int.tdiv (Int.tdiv a p) c), .int p] ++ [.int (c - 1), .int (Int.tdiv (Int.tdiv b p) c), .int c, .int s, .int tt, .int p, .int e]) := isz_le_szl_of_mem (by simp)
    exact add_le_sq_of (K := KAd) h1 h2
  have hsz27 : szl W27 + 1 ≤ 3 * (szl W26 + 1) := by
    simp only [W26, W27, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e27 : Spec main (cR 2) 8 (fun t => t = W26) (fun _ o => o = W27) (quadCost C27) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 2) (hR main 2) (W := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (c - 1), .int (Int.tdiv (Int.tdiv b p) c)]) (B := [.int (Int.tdiv (Int.tdiv b p) c), .int ((Int.tdiv (Int.tdiv a p) c) + p), .int (c - 1)]) (by simp) (by rfl))
        (E := [.int c, .int s, .int tt, .int p, .int e]) (k := 5) (by simp)))
  have hsz28 : szl W28 + 1 ≤ 3 * (szl W27 + 1) := by
    simp only [W27, W28, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e28 : Spec main (cS) 8 (fun t => t = W27) (fun _ o => o = W28) (quadCost C28) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk (Spec.swapEx hk (hS main) (.int (Int.tdiv (Int.tdiv b p) c)) (.int ((Int.tdiv (Int.tdiv a p) c) + p)))
        (E := [.int (c - 1), .int c, .int s, .int tt, .int p, .int e]) (k := 6) (by simp)))
  have hsz29 : szl W29 + 1 ≤ 3 * (szl W28 + 1) := by
    simp only [W28, W29, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e29 : Spec main (cR 3) 8 (fun t => t = W28) (fun _ o => o = W29) (quadCost C29) := by
    exact
      (Spec.toQuad hk (Spec.extendLin hk
        (Spec.rollEx hk (k := 3) (hR main 3) (W := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1), .int c]) (B := [.int c, .int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1)]) (by simp) (by rfl))
        (E := [.int s, .int tt, .int p, .int e]) (k := 4) (by simp)))
  have hsz30 : szl W30 + 1 ≤ 3 * (szl W29 + 1) := by
    simp only [W29, W30, szl_cons, szl_nil, List.sum_cons, List.sum_nil, vsz_int, h1z]
    omega
  have e30 : Spec main (cDr) 8 (fun t => t = W29) (fun _ o => o = W30) (quadCost C30) := by
    refine
      (Spec.mono hk (Spec.extendLin hk (Spec.dropEx hk (hDr main) (.int c))
        (E := [.int ((Int.tdiv (Int.tdiv a p) c) + p), .int (Int.tdiv (Int.tdiv b p) c), .int (c - 1), .int s, .int tt, .int p, .int e]) (k := 7) (by simp))
        (fun t _ h => h) (fun t o _ _ h => h)) ?_
    intro t _ hq
    rw [hq]
    exact linCost_dupQ
  -- composition, from the end
  have cc29 := Spec.seqQuad hk e29 e30 (by simp [W29]) hsz29
  have cc28 := Spec.seqQuad hk e28 cc29 (by simp [W28]) hsz28
  have cc27 := Spec.seqQuad hk e27 cc28 (by simp [W27]) hsz27
  have cc26 := Spec.seqQuad hk e26 cc27 (by simp [W26]) hsz26
  have cc25 := Spec.seqQuad hk e25 cc26 (by simp [W25]) hsz25
  have cc24 := Spec.seqQuad hk e24 cc25 (by simp [W24]) hsz24
  have cc23 := Spec.seqQuad hk e23 cc24 (by simp [W23]) hsz23
  have cc22 := Spec.seqQuad hk e22 cc23 (by simp [W22]) hsz22
  have cc21 := Spec.seqQuad hk e21 cc22 (by simp [W21]) hsz21
  have cc20 := Spec.seqQuad hk e20 cc21 (by simp [W20]) hsz20
  have cc19 := Spec.seqQuad hk e19 cc20 (by simp [W19]) hsz19
  have cc18 := Spec.seqQuad hk e18 cc19 (by simp [W18]) hsz18
  have cc17 := Spec.seqQuad hk e17 cc18 (by simp [W17]) hsz17
  have cc16 := Spec.seqQuad hk e16 cc17 (by simp [W16]) hsz16
  have cc15 := Spec.seqQuad hk e15 cc16 (by simp [W15]) hsz15
  have cc14 := Spec.seqQuad hk e14 cc15 (by simp [W14]) hsz14
  have cc13 := Spec.seqQuad hk e13 cc14 (by simp [W13]) hsz13
  have cc12 := Spec.seqQuad hk e12 cc13 (by simp [W12]) hsz12
  have cc11 := Spec.seqQuad hk e11 cc12 (by simp [W11]) hsz11
  have cc10 := Spec.seqQuad hk e10 cc11 (by simp [W10]) hsz10
  have cc9 := Spec.seqQuad hk e9 cc10 (by simp [W9]) hsz9
  have cc8 := Spec.seqQuad hk e8 cc9 (by simp [W8]) hsz8
  have cc7 := Spec.seqQuad hk e7 cc8 (by simp [W7]) hsz7
  have cc6 := Spec.seqQuad hk e6 cc7 (by simp [W6]) hsz6
  have cc5 := Spec.seqQuad hk e5 cc6 (by simp [W5]) hsz5
  have cc4 := Spec.seqQuad hk e4 cc5 (by simp [W4]) hsz4
  have cc3 := Spec.seqQuad hk e3 cc4 (by simp [W3]) hsz3
  have cc2 := Spec.seqQuad hk e2 cc3 (by simp [W2]) hsz2
  have cc1 := Spec.seqQuad hk e1 cc2 (by simp [W1]) hsz1
  have cfin : Spec main prog 7 (fun t => t = W0) (fun _ o => o = W30) (fun t => max K1 2 * (szl t + 1) ^ (max K1 2)) := by
    exact Spec.mono hk cc1 (fun t _ h => h) (fun t o _ _ h => h) (fun t _ _ => quadCost_le K1 t)
  simpa only [W0, W30] using cfin

/-! ## The requested statement -/

/-- One Horner stage of the fixed-point complex exponential. -/
theorem expStepB (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Nre Nim dd Zs Zt Pow d0 : ℤ),
      Pow ≠ 0 → 1 ≤ dd →
      Spec main prog 7
        (fun t => t = [HvdH.Val.int Nre, HvdH.Val.int Nim, HvdH.Val.int dd, HvdH.Val.int Zs,
          HvdH.Val.int Zt, HvdH.Val.int Pow, HvdH.Val.int d0])
        (fun t o => o = [HvdH.Val.int (Pow + Int.tdiv (Int.tdiv Nre Pow) dd),
          HvdH.Val.int (Int.tdiv (Int.tdiv Nim Pow) dd), HvdH.Val.int (dd - 1),
          HvdH.Val.int Zs, HvdH.Val.int Zt, HvdH.Val.int Pow, HvdH.Val.int d0])
        (fun t => K * (szl t + 1) ^ K) := by
  obtain ⟨prog, M, hM⟩ := expStepBChain hk hi
  refine ⟨prog, M, ?_⟩
  intro main Nre Nim dd Zs Zt Pow d0 hPow hdd
  have hc0 : dd ≠ 0 := by omega
  have h := hM main Nre Nim dd Zs Zt Pow d0 hPow hc0
  refine Spec.mono hk h (fun t _ hp => hp) ?_ (fun _ _ _ => le_rfl)
  intro t o _ hp hQ
  rw [hQ]
  simp only [add_comm (Int.tdiv (Int.tdiv Nre Pow) dd) Pow]

end Work.Fx
