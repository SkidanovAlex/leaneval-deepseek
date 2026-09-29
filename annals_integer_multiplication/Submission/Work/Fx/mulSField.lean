import Mathlib
import Submission.Work.Fx.FxLin
import Submission.Work.Fx.mulSFieldMath

set_option maxHeartbeats 4000000

namespace Work.Fx

open HvdH

/-! ## Integer size estimates from `inDisc` -/

theorem natAbs_fst_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.1.natAbs ≤ 2 ^ p := by
  simp only [inDisc] at h
  have h2 : z.1 ^ 2 ≤ (4 : ℤ) ^ p := by nlinarith [sq_nonneg z.2]
  have h3 : ((z.1.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ) : ℤ)) ^ 2 := by
    have e : ((z.1.natAbs : ℤ)) ^ 2 = z.1 ^ 2 := by
      rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg z.1)]
    have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
      have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
      rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    rw [e, e2]
    exact h2
  exact (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)

theorem natAbs_snd_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.2.natAbs ≤ 2 ^ p := by
  have h' : inDisc p (z.2, z.1) := by
    simp only [inDisc] at h ⊢; linarith
  exact natAbs_fst_le_of_inDisc h'

theorem isz_le_of_natAbs_le_x2 {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

/-! ## Exact-window `WordR` adapters -/

theorem wrd_exact_x1 {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {c : ℕ}
    (h : WordR main p P Q C) (hA : P A) (hB : ∀ out, Q A out → out = B) (hc : C A ≤ c) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨out, s', n, hPost, hev, hn, hstk, hfr⟩ := h A hA s R hs
  exact ⟨out, s', n, hB out hPost, hev, le_trans hn hc, hstk, hfr⟩

theorem wrd_seq2 {main p q : Cmd} {A mid B : List Val} {c1 c2 : ℕ}
    (hp : WordR main p (fun vs => vs = A) (fun _ out => out = mid) (fun _ => c1))
    (hq : WordR main q (fun vs => vs = mid) (fun _ out => out = B) (fun _ => c2)) :
    WordR main (p.seq q) (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1 + c2) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨m, s1, n1, hm, hev1, hn1, hstk1, hfr1⟩ := hp A rfl s R hs
  obtain ⟨out, s2, n2, hB, hev2, hn2, hstk2, hfr2⟩ := hq m hm s1 R hstk1
  have hn1' : n1 ≤ c1 := hn1
  have hn2' : n2 ≤ c2 := hn2
  exact ⟨out, s2, n1 + n2, hB, Eval.seq hev1 hev2, by dsimp only; omega, hstk2,
    fun k hk => by rw [hfr2 k hk, hfr1 k hk]⟩

theorem wrd_conseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (hk : KernelLib)
    (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' :=
  hk.conseq main p P P' Q Q' C C' h hP hQ hC

theorem wrd_binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} {rest : List Val} (hP : P a b) {c : ℕ}
    (hc : C a b ≤ c) :
    WordR main prog (fun vs => vs = .int a :: .int b :: rest)
      (fun _ out => out = .int (f a b) :: rest) (fun _ => c) := by
  refine wrd_exact_x1 h ⟨a, b, rest, rfl, hP⟩ ?_ ?_
  · intro out hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    obtain ⟨ha, hr⟩ := List.cons.inj h2
    rw [hout, ← Val.int.inj h1, ← Val.int.inj ha, ← hr]
  · simpa only [binCost] using hc

theorem wrd_unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} {rest : List Val} (hP : P a) {c : ℕ} (hc : C a ≤ c) :
    WordR main prog (fun vs => vs = .int a :: rest) (fun _ out => out = .int (f a) :: rest)
      (fun _ => c) := by
  refine wrd_exact_x1 h ⟨a, rest, rfl, hP⟩ ?_ ?_
  · intro out hQ
    rcases hQ with ⟨a', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    rw [hout, ← Val.int.inj h1, ← h2]
  · simpa only [unCost] using hc

theorem wrd_swap {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (rest : List Val) {c : ℕ} (hc : K * (vsz a + vsz b + 1) ≤ c) :
    WordR main prog (fun vs => vs = a :: b :: rest) (fun _ out => out = b :: a :: rest)
      (fun _ => c) := by
  refine wrd_exact_x1 h ?_ ?_ ?_
  · simp
  · intro out hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    obtain ⟨h3, h4⟩ := List.cons.inj h2
    rw [hout, ← h1, ← h3, ← h4]
  · simpa [List.getD] using hc

theorem wrd_pick {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (v : Val) (hget : A.getD k .nil = v) (hk : k < A.length) {c : ℕ}
    (hc : K * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => c) := by
  refine wrd_exact_x1 (h k) hk ?_ hc
  intro out hout
  rw [hout, hget]

theorem wrd_roll {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (v : Val) (hget : A.getD k .nil = v) (hk : k < A.length) {c : ℕ}
    (hc : K * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = A) (fun _ out => out = v :: A.eraseIdx k) (fun _ => c) := by
  refine wrd_exact_x1 (h k) hk ?_ hc
  intro out hout
  rw [hout, hget]

theorem wrd_drop {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (rest : List Val) {c : ℕ} (hc : K * (vsz a + 1) ≤ c) :
    WordR main prog (fun vs => vs = a :: rest) (fun _ out => out = rest) (fun _ => c) := by
  refine wrd_exact_x1 h ?_ ?_ ?_
  · simp
  · intro out hQ
    rcases hQ with ⟨v, rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    rw [hout, ← h2]
  · simpa [List.headD] using hc

theorem wrd_uncons {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) (rest : List Val) {c : ℕ} (hc : K ≤ c) :
    WordR main prog (fun vs => vs = .cons a b :: rest) (fun _ out => out = a :: b :: rest)
      (fun _ => c) := by
  refine wrd_exact_x1 h ⟨a, b, rest, rfl⟩ ?_ hc
  intro out hQ
  rcases hQ with ⟨a', b', rest', hvs, hout⟩
  obtain ⟨h1, h2⟩ := List.cons.inj hvs
  obtain ⟨ha, hb⟩ := Val.cons.inj h1
  rw [hout, ← ha, ← hb, ← h2]

theorem wrd_cons {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    (a b : Val) (rest : List Val) {c : ℕ} (hc : K ≤ c) :
    WordR main prog (fun vs => vs = a :: b :: rest) (fun _ out => out = .cons a b :: rest)
      (fun _ => c) := by
  refine wrd_exact_x1 h (by simp) ?_ hc
  intro out hQ
  rcases hQ with ⟨a', b', rest', hvs, hout⟩
  obtain ⟨h1, h2⟩ := List.cons.inj hvs
  obtain ⟨h3, h4⟩ := List.cons.inj h2
  rw [hout, ← h1, ← h3, ← h4]

/-! ## Cost estimates (all costs are `≤ 1000*KK*(p+1)^2`) -/

theorem le_sq1 (K p : ℕ) : K * (p + 1) ≤ K * (p + 1) ^ 2 := by
  apply Nat.mul_le_mul_left
  rw [pow_two]
  calc (p + 1) = (p + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)

theorem add39 (c : ℕ) :
    c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c + (c)))))))))))))))))))))))))))))))))))))) = 39 * c := by ring

theorem pickroll_cost {K KK p k s : ℕ} (hK : K ≤ KK) (hk : k + 1 ≤ 7) (hs : s ≤ 133 * (p + 1)) :
    K * (k + 1) * (s + 1) ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hs1 : s + 1 ≤ 134 * (p + 1) := by omega
  have h1 : K * (k + 1) * (s + 1) ≤ K * 7 * (134 * (p + 1)) := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left K hk
    · exact hs1
  have h2 : K * 7 * (134 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 938 * K ≤ 1000 * KK := by omega
    calc K * 7 * (134 * (p + 1)) = (938 * K) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (1000 * KK) * (p + 1) ^ 2 := le_sq1 _ _
  exact le_trans h1 h2

theorem sw_cost {K KK p : ℕ} {a b : Val} (hK : K ≤ KK) (ha : vsz a ≤ 19 * (p + 1))
    (hb : vsz b ≤ 19 * (p + 1)) : K * (vsz a + vsz b + 1) ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hs : vsz a + vsz b + 1 ≤ 39 * (p + 1) := by omega
  have h1 : K * (vsz a + vsz b + 1) ≤ K * (39 * (p + 1)) := Nat.mul_le_mul_left K hs
  have h2 : K * (39 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 39 * K ≤ 1000 * KK := by omega
    calc K * (39 * (p + 1)) = (39 * K) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (1000 * KK) * (p + 1) ^ 2 := le_sq1 _ _
  exact le_trans h1 h2

theorem drop_cost {K KK p : ℕ} {a : Val} (hK : K ≤ KK) (ha : vsz a ≤ 19 * (p + 1)) :
    K * (vsz a + 1) ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hs : vsz a + 1 ≤ 20 * (p + 1) := by omega
  have h1 : K * (vsz a + 1) ≤ K * (20 * (p + 1)) := Nat.mul_le_mul_left K hs
  have h2 : K * (20 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 20 * K ≤ 1000 * KK := by omega
    calc K * (20 * (p + 1)) = (20 * K) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (1000 * KK) * (p + 1) ^ 2 := le_sq1 _ _
  exact le_trans h1 h2

theorem mul_cost {K KK p : ℕ} {a b : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1))
    (hb : isz b ≤ 9 * (p + 1)) : K * isz a * isz b ≤ 1000 * KK * (p + 1) ^ 2 := by
  have h1 : K * isz a * isz b ≤ K * (9 * (p + 1)) * (9 * (p + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left K ha) hb
  have h2 : K * (9 * (p + 1)) * (9 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 81 * K ≤ 1000 * KK := by omega
    calc K * (9 * (p + 1)) * (9 * (p + 1)) = (81 * K) * (p + 1) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) * (p + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK')
      _ = 1000 * KK * (p + 1) ^ 2 := by ring
  exact le_trans h1 h2

theorem addsub_cost {K KK p : ℕ} {a b : ℤ} (hK : K ≤ KK) (ha : isz a ≤ 9 * (p + 1))
    (hb : isz b ≤ 9 * (p + 1)) : K * (isz a + isz b) ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hs : isz a + isz b ≤ 18 * (p + 1) := by omega
  have h1 : K * (isz a + isz b) ≤ K * (18 * (p + 1)) := Nat.mul_le_mul_left K hs
  have h2 : K * (18 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 18 * K ≤ 1000 * KK := by omega
    calc K * (18 * (p + 1)) = (18 * K) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (1000 * KK) * (p + 1) ^ 2 := le_sq1 _ _
  exact le_trans h1 h2

theorem pow2_cost {K KK p : ℕ} (hK : K ≤ KK) :
    K * (p + isz (p : ℤ)) ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hp : isz ((p : ℤ)) ≤ p + 2 := by
    have hna : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
    have hsz : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    simp only [isz, hna]; omega
  have hs : p + isz (p : ℤ) ≤ 3 * (p + 1) := by omega
  have h1 : K * (p + isz (p : ℤ)) ≤ K * (3 * (p + 1)) := Nat.mul_le_mul_left K hs
  have h2 : K * (3 * (p + 1)) ≤ 1000 * KK * (p + 1) ^ 2 := by
    have hK' : 3 * K ≤ 1000 * KK := by omega
    calc K * (3 * (p + 1)) = (3 * K) * (p + 1) := by ring
      _ ≤ (1000 * KK) * (p + 1) := Nat.mul_le_mul_right _ hK'
      _ ≤ (1000 * KK) * (p + 1) ^ 2 := le_sq1 _ _
  exact le_trans h1 h2

theorem uncon_cost {K KK p : ℕ} (hK : K ≤ KK) : K ≤ 1000 * KK * (p + 1) ^ 2 := by
  have hp1 : 1 ≤ (p + 1) ^ 2 := by
    rw [pow_two]
    have h1 : 1 ≤ p + 1 := by omega
    calc 1 ≤ p + 1 := h1
      _ = (p + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ h1
  calc K ≤ KK := hK
    _ = KK * 1 := (Nat.mul_one KK).symm
    _ ≤ KK * ((p + 1) ^ 2) := Nat.mul_le_mul_left KK hp1
    _ ≤ 1000 * KK * (p + 1) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by omega)

/-! ## The program -/

def mulSProg (mulP addP subP tdivP powP : Cmd) (pickP rollP : ℕ → Cmd)
    (swP dropP unconsP consP : Cmd) : Cmd :=
  .seq swP (.seq unconsP (.seq (rollP 3) (.seq unconsP (.seq (pickP 2) (.seq (pickP 1) (.seq mulP (.seq (pickP 4) (.seq (pickP 3) (.seq mulP (.seq swP (.seq subP (.seq (pickP 5) (.seq powP (.seq swP (.seq tdivP (.seq (pickP 3) (.seq (pickP 3) (.seq mulP (.seq (pickP 2) (.seq (pickP 6) (.seq mulP (.seq addP (.seq (pickP 6) (.seq powP (.seq swP (.seq tdivP (.seq swP (.seq consP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) (.seq dropP (.seq (rollP 1) (dropP))))))))))))))))))))))))))))))))))))))


/-- Schoolbook fixed-point complex multiplication (paper Lemma 2.4). Input `int p :: cfxVal u :: cfxVal v`,
output `cfxVal w` with `inDisc p w` and `2^p ‖fxC p w - fxC p u * fxC p v‖ < 2`, cost `K (p+1)^2`.
Route: `w = (Int.tdiv (x*x' - y*y') (2^p), Int.tdiv (x*y' + y*x') (2^p))` where `u = (x,y)`, `v = (x',y')`,
computed with `hi.mulS`, `hi.add`, `hi.sub`, `hi.tdiv`; the sizes are bounded because `inDisc p u` and
`inDisc p v` give `|x|,|y|,|x'|,|y'| ≤ 2^p`. The helper framework `FxCommon`/`FxLin` composes `WordR`
words (`Spec`, `Spec.seq_det_lin`, `Spec.extend_exact`, `Spec.binOp`, `Spec.unconsVK`, `Spec.consVK`, ...).
For `inDisc p w` use `(x x' - y y')^2 + (x y' + y x')^2 = (x^2+y^2)(x'^2+y'^2) ≤ 4^{2p}` together with
`|Int.tdiv a (2^p)| ≤ |a|/2^p`; for the error bound the truncation errors are `≤ 1/2` per coordinate. -/
theorem mulSField (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), HvdH.WordR main prog
      (fun vs => ∃ (u v : ℤ × ℤ) (rest : List HvdH.Val),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest ∧
        HvdH.inDisc p u ∧ HvdH.inDisc p v)
      (fun vs out => ∃ (u v : ℤ × ℤ) (rest : List HvdH.Val) (w : ℤ × ℤ),
        vs = HvdH.Val.int (p : ℤ) :: HvdH.cfxVal u :: HvdH.cfxVal v :: rest ∧
        out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧
        (2 : ℝ) ^ p * ‖HvdH.fxC p w - HvdH.fxC p u * HvdH.fxC p v‖ < 2)
      (fun _ => K * (p + 1) ^ 2) := by
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨tdivP, Ktdiv, htdiv⟩ := hi.tdiv
  obtain ⟨powP, Kpow, hpow⟩ := hi.pow2
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨dropP, Kd, hdrop⟩ := hk.drop
  obtain ⟨unconsP, Kun, huncons⟩ := hk.unconsV
  obtain ⟨consP, Kcon, hcons⟩ := hk.consV
  set KK : ℕ := Kp + Kr + Ksw + Kd + Kun + Kcon + Kmul + Ksub + Kadd + Ktdiv + Kpow + 1 with hKK
  refine ⟨mulSProg mulP addP subP tdivP powP pickP rollP swP dropP unconsP consP, 39000 * KK, ?_⟩
  intro main p
  have hKsw : Ksw ≤ KK := by omega
  have hKr : Kr ≤ KK := by omega
  have hKp : Kp ≤ KK := by omega
  have hKd : Kd ≤ KK := by omega
  have hKun : Kun ≤ KK := by omega
  have hKcon : Kcon ≤ KK := by omega
  have hKmul : Kmul ≤ KK := by omega
  have hKsub : Ksub ≤ KK := by omega
  have hKadd : Kadd ≤ KK := by omega
  have hKtdiv : Ktdiv ≤ KK := by omega
  have hKpow : Kpow ≤ KK := by omega
  have key : ∀ (x y x' y' : ℤ) (rest : List Val), inDisc p (x, y) → inDisc p (x', y') →
      WordR main (mulSProg mulP addP subP tdivP powP pickP rollP swP dropP unconsP consP)
        (fun vs => vs = .int (p : ℤ) :: cfxVal (x, y) :: cfxVal (x', y') :: rest)
        (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: rest ∧ inDisc p w ∧
          (2 : ℝ) ^ p * ‖fxC p w - fxC p (x, y) * fxC p (x', y')‖ < 2)
        (fun _ => 39000 * KK * (p + 1) ^ 2) := by
    intro x y x' y' rest hd1 hd2
    set Cstep : ℕ := 1000 * KK * (p + 1) ^ 2 with hCstep
    have hx4 : isz x ≤ 4 * (p + 1) := by
      have h : isz x ≤ p + 3 := isz_le_of_natAbs_le_x2 (natAbs_fst_le_of_inDisc hd1); omega
    have hy4 : isz y ≤ 4 * (p + 1) := by
      have h : isz y ≤ p + 3 := isz_le_of_natAbs_le_x2 (natAbs_snd_le_of_inDisc hd1); omega
    have hx'4 : isz x' ≤ 4 * (p + 1) := by
      have h : isz x' ≤ p + 3 := isz_le_of_natAbs_le_x2 (natAbs_fst_le_of_inDisc hd2); omega
    have hy'4 : isz y' ≤ 4 * (p + 1) := by
      have h : isz y' ≤ p + 3 := isz_le_of_natAbs_le_x2 (natAbs_snd_le_of_inDisc hd2); omega
    have hx9 : isz x ≤ 9 * (p + 1) := by omega
    have hy9 : isz y ≤ 9 * (p + 1) := by omega
    have hx'9 : isz x' ≤ 9 * (p + 1) := by omega
    have hy'9 : isz y' ≤ 9 * (p + 1) := by omega
    have hpi9 : isz ((p : ℤ)) ≤ 9 * (p + 1) := by
      have hna : ((p : ℤ)).natAbs = p := Int.natAbs_natCast p
      have : isz ((p : ℤ)) = p.size + 2 := by simp only [isz, hna]
      have hs : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
      omega
    have hxx8 : isz (x' * x) ≤ 8 * (p + 1) := by have h := isz_mul_le x' x; omega
    have hyy8 : isz (y' * y) ≤ 8 * (p + 1) := by have h := isz_mul_le y' y; omega
    have hxy8 : isz (y' * x) ≤ 8 * (p + 1) := by have h := isz_mul_le y' x; omega
    have hyx8 : isz (y * x') ≤ 8 * (p + 1) := by have h := isz_mul_le y x'; omega
    have hxx9 : isz (x' * x) ≤ 9 * (p + 1) := by omega
    have hyy9 : isz (y' * y) ≤ 9 * (p + 1) := by omega
    have hxy9 : isz (y' * x) ≤ 9 * (p + 1) := by omega
    have hyx9 : isz (y * x') ≤ 9 * (p + 1) := by omega
    have hXX9 : isz (x' * x - y' * y) ≤ 9 * (p + 1) := by
      have h := isz_sub_le (x' * x) (y' * y)
      rcases le_total (isz (x' * x)) (isz (y' * y)) with hc | hc
      · rw [max_eq_right hc] at h; omega
      · rw [max_eq_left hc] at h; omega
    have hII9 : isz (y * x' + y' * x) ≤ 9 * (p + 1) := by
      have h := isz_add_le (y * x') (y' * x)
      rcases le_total (isz (y * x')) (isz (y' * x)) with hc | hc
      · rw [max_eq_right hc] at h; omega
      · rw [max_eq_left hc] at h; omega
    have h2p9 : isz ((2 : ℤ) ^ p) ≤ 9 * (p + 1) := by
      have h : isz ((2 : ℤ) ^ p) ≤ p + 3 := by
        apply isz_le_of_natAbs_le_x2
        rw [Int.natAbs_pow]; norm_num
      omega
    let W1 : ℤ := Int.tdiv (x' * x - y' * y) ((2 : ℤ) ^ p)
    let W2 : ℤ := Int.tdiv (y * x' + y' * x) ((2 : ℤ) ^ p)
    let Cv : Val := .cons (.int W1) (.int W2)
    have hW19 : isz W1 ≤ 9 * (p + 1) := by
      have h := isz_tdiv_le (x' * x - y' * y) ((2 : ℤ) ^ p)
      exact le_trans h hXX9
    have hW29 : isz W2 ≤ 9 * (p + 1) := by
      have h := isz_tdiv_le (y * x' + y' * x) ((2 : ℤ) ^ p)
      exact le_trans h hII9
    have hcu19 : vsz (cfxVal (x, y)) ≤ 19 * (p + 1) := by
      rw [vsz_cfxVal]; dsimp only; omega
    have hcv19 : vsz (cfxVal (x', y')) ≤ 19 * (p + 1) := by
      rw [vsz_cfxVal]; dsimp only; omega
    have hCv19 : vsz Cv ≤ 19 * (p + 1) := by
      show vsz (.cons (.int W1) (.int W2)) ≤ 19 * (p + 1)
      rw [vsz_cons, vsz_int, vsz_int]; omega
    have hPv19 : vsz (.int (p : ℤ)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hX19 : vsz (.int x) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hY19 : vsz (.int y) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hX'19 : vsz (.int x') ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hY'19 : vsz (.int y') ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hxx19 : vsz (.int (x' * x)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hyy19 : vsz (.int (y' * y)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have h2p19 : vsz (.int ((2 : ℤ) ^ p)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hXX19 : vsz (.int (x' * x - y' * y)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hW119 : vsz (.int W1) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hW219 : vsz (.int W2) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    have hII19 : vsz (.int (y * x' + y' * x)) ≤ 19 * (p + 1) := by rw [vsz_int]; omega
    let A0 : List Val := .int (p : ℤ) :: cfxVal (x, y) :: cfxVal (x', y') :: rest
    let A1 : List Val := cfxVal (x, y) :: .int (p : ℤ) :: cfxVal (x', y') :: rest
    let A2 : List Val := .int x :: .int y :: .int (p : ℤ) :: cfxVal (x', y') :: rest
    let A3 : List Val := cfxVal (x', y') :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A4 : List Val := .int x' :: .int y' :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A5 : List Val := .int x :: A4
    let A6 : List Val := .int x' :: A5
    let A7 : List Val := .int (x' * x) :: A4
    let A8 : List Val := .int y :: A7
    let A9 : List Val := .int y' :: A8
    let A10 : List Val := .int (y' * y) :: A7
    let A11 : List Val := .int (x' * x) :: .int (y' * y) :: A4
    let A12 : List Val := .int (x' * x - y' * y) :: A4
    let A13 : List Val := .int (p : ℤ) :: A12
    let A14 : List Val := .int ((2 : ℤ) ^ p) :: A12
    let A15 : List Val := .int (x' * x - y' * y) :: .int ((2 : ℤ) ^ p) :: A4
    let A16 : List Val := .int W1 :: A4
    let A17 : List Val := .int x :: A16
    let A18 : List Val := .int y' :: A17
    let A19 : List Val := .int (y' * x) :: A16
    let A20 : List Val := .int x' :: A19
    let A21 : List Val := .int y :: A20
    let A22 : List Val := .int (y * x') :: A19
    let A23 : List Val := .int (y * x' + y' * x) :: A16
    let A24 : List Val := .int (p : ℤ) :: A23
    let A25 : List Val := .int ((2 : ℤ) ^ p) :: A23
    let A26 : List Val := .int (y * x' + y' * x) :: .int ((2 : ℤ) ^ p) :: A16
    let A27 : List Val := .int W2 :: A16
    let A28 : List Val := .int W1 :: .int W2 :: A4
    let A29 : List Val := Cv :: A4
    let A30 : List Val := .int x' :: Cv :: .int y' :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A31 : List Val := Cv :: .int y' :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A32 : List Val := .int y' :: Cv :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A33 : List Val := Cv :: .int x :: .int y :: .int (p : ℤ) :: rest
    let A34 : List Val := .int x :: Cv :: .int y :: .int (p : ℤ) :: rest
    let A35 : List Val := Cv :: .int y :: .int (p : ℤ) :: rest
    let A36 : List Val := .int y :: Cv :: .int (p : ℤ) :: rest
    let A37 : List Val := Cv :: .int (p : ℤ) :: rest
    let A38 : List Val := .int (p : ℤ) :: Cv :: rest
    let A39 : List Val := Cv :: rest
    have hs3 : ((A2.take 4).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A2, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cfxVal]
      omega
    have hs5 : ((A4.take 3).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs6 : ((A5.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A5, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs8 : ((A7.take 5).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A7, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs9 : ((A8.take 4).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A8, A7, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs13 : ((A12.take 6).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A12, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs17 : ((A16.take 4).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A16, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs18 : ((A17.take 4).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A17, A16, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs20 : ((A19.take 3).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A19, A16, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs21 : ((A20.take 7).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A20, A19, A16, A4, List.take_succ_cons, List.take_zero, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs24 : ((A23.take 7).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A23, A16, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int]
      omega
    have hs30 : ((A29.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A29, Cv, A4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cons]
      omega
    have hs32 : ((A31.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A31, Cv, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cons]
      omega
    have hs34 : ((A33.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A33, Cv, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cons]
      omega
    have hs36 : ((A35.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A35, Cv, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cons]
      omega
    have hs38 : ((A37.take 2).map vsz).sum ≤ 133 * (p + 1) := by
      simp only [A37, Cv, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, vsz_cons]
      omega
    have h1 : WordR main swP (fun vs => vs = A0) (fun _ out => out = A1) (fun _ => Cstep) :=
      wrd_swap (hsw main) (.int (p : ℤ)) (cfxVal (x, y)) (cfxVal (x', y') :: rest)
        (sw_cost hKsw hPv19 hcu19)
    have h2 : WordR main unconsP (fun vs => vs = A1) (fun _ out => out = A2) (fun _ => Cstep) :=
      wrd_uncons (huncons main) (.int x) (.int y) (.int (p : ℤ) :: cfxVal (x', y') :: rest)
        (uncon_cost hKun)
    have h3 : WordR main (rollP 3) (fun vs => vs = A2) (fun _ out => out = A3) (fun _ => Cstep) :=
      wrd_roll (hroll main) 3 A2 (cfxVal (x', y')) (by rfl)
        (by simp only [A2, List.length_cons]; omega) (pickroll_cost hKr (by norm_num) hs3)
    have h4 : WordR main unconsP (fun vs => vs = A3) (fun _ out => out = A4) (fun _ => Cstep) :=
      wrd_uncons (huncons main) (.int x') (.int y') (.int x :: .int y :: .int (p : ℤ) :: rest)
        (uncon_cost hKun)
    have h5 : WordR main (pickP 2) (fun vs => vs = A4) (fun _ out => out = A5) (fun _ => Cstep) :=
      wrd_pick (hpick main) 2 A4 (.int x) (by rfl)
        (by simp only [A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs5)
    have h6 : WordR main (pickP 1) (fun vs => vs = A5) (fun _ out => out = A6) (fun _ => Cstep) :=
      wrd_pick (hpick main) 1 A5 (.int x') (by rfl)
        (by simp only [A5, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs6)
    have h7 : WordR main mulP (fun vs => vs = A6) (fun _ out => out = A7) (fun _ => Cstep) :=
      wrd_binOp (hmul main) (a := x') (b := x) trivial (mul_cost hKmul hx'9 hx9)
    have h8 : WordR main (pickP 4) (fun vs => vs = A7) (fun _ out => out = A8) (fun _ => Cstep) :=
      wrd_pick (hpick main) 4 A7 (.int y) (by rfl)
        (by simp only [A7, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs8)
    have h9 : WordR main (pickP 3) (fun vs => vs = A8) (fun _ out => out = A9) (fun _ => Cstep) :=
      wrd_pick (hpick main) 3 A8 (.int y') (by rfl)
        (by simp only [A8, A7, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs9)
    have h10 : WordR main mulP (fun vs => vs = A9) (fun _ out => out = A10) (fun _ => Cstep) :=
      wrd_binOp (hmul main) (a := y') (b := y) trivial (mul_cost hKmul hy'9 hy9)
    have h11 : WordR main swP (fun vs => vs = A10) (fun _ out => out = A11) (fun _ => Cstep) :=
      wrd_swap (hsw main) (.int (y' * y)) (.int (x' * x)) A4 (sw_cost hKsw hyy19 hxx19)
    have h12 : WordR main subP (fun vs => vs = A11) (fun _ out => out = A12) (fun _ => Cstep) :=
      wrd_binOp (hsub main) (a := x' * x) (b := y' * y) trivial (addsub_cost hKsub hxx9 hyy9)
    have h13 : WordR main (pickP 5) (fun vs => vs = A12) (fun _ out => out = A13) (fun _ => Cstep) :=
      wrd_pick (hpick main) 5 A12 (.int (p : ℤ)) (by rfl)
        (by simp only [A12, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs13)
    have h14 : WordR main powP (fun vs => vs = A13) (fun _ out => out = A14) (fun _ => Cstep) :=
      wrd_unOp (hpow main) (a := (p : ℤ)) (by exact_mod_cast Nat.zero_le p) (pow2_cost hKpow)
    have h15 : WordR main swP (fun vs => vs = A14) (fun _ out => out = A15) (fun _ => Cstep) :=
      wrd_swap (hsw main) (.int ((2 : ℤ) ^ p)) (.int (x' * x - y' * y)) A4
        (sw_cost hKsw h2p19 hXX19)
    have h16 : WordR main tdivP (fun vs => vs = A15) (fun _ out => out = A16) (fun _ => Cstep) :=
      wrd_binOp (htdiv main) (a := x' * x - y' * y) (b := (2 : ℤ) ^ p)
        (pow_ne_zero p (by norm_num)) (mul_cost hKtdiv hXX9 h2p9)
    have h17 : WordR main (pickP 3) (fun vs => vs = A16) (fun _ out => out = A17) (fun _ => Cstep) :=
      wrd_pick (hpick main) 3 A16 (.int x) (by rfl)
        (by simp only [A16, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs17)
    have h18 : WordR main (pickP 3) (fun vs => vs = A17) (fun _ out => out = A18) (fun _ => Cstep) :=
      wrd_pick (hpick main) 3 A17 (.int y') (by rfl)
        (by simp only [A17, A16, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs18)
    have h19 : WordR main mulP (fun vs => vs = A18) (fun _ out => out = A19) (fun _ => Cstep) :=
      wrd_binOp (hmul main) (a := y') (b := x) trivial (mul_cost hKmul hy'9 hx9)
    have h20 : WordR main (pickP 2) (fun vs => vs = A19) (fun _ out => out = A20) (fun _ => Cstep) :=
      wrd_pick (hpick main) 2 A19 (.int x') (by rfl)
        (by simp only [A19, A16, A4, List.length_cons]; omega) (pickroll_cost hKp (by norm_num) hs20)
    have h21 : WordR main (pickP 6) (fun vs => vs = A20) (fun _ out => out = A21) (fun _ => Cstep) :=
      wrd_pick (hpick main) 6 A20 (.int y) (by rfl)
        (by simp only [A20, A19, A16, A4, List.length_cons]; omega)
        (pickroll_cost hKp (by norm_num) hs21)
    have h22 : WordR main mulP (fun vs => vs = A21) (fun _ out => out = A22) (fun _ => Cstep) :=
      wrd_binOp (hmul main) (a := y) (b := x') trivial (mul_cost hKmul hy9 hx'9)
    have h23 : WordR main addP (fun vs => vs = A22) (fun _ out => out = A23) (fun _ => Cstep) :=
      wrd_binOp (hadd main) (a := y * x') (b := y' * x) trivial (addsub_cost hKadd hyx9 hxy9)
    have h24 : WordR main (pickP 6) (fun vs => vs = A23) (fun _ out => out = A24) (fun _ => Cstep) :=
      wrd_pick (hpick main) 6 A23 (.int (p : ℤ)) (by rfl)
        (by simp only [A23, A16, A4, List.length_cons]; omega)
        (pickroll_cost hKp (by norm_num) hs24)
    have h25 : WordR main powP (fun vs => vs = A24) (fun _ out => out = A25) (fun _ => Cstep) :=
      wrd_unOp (hpow main) (a := (p : ℤ)) (by exact_mod_cast Nat.zero_le p) (pow2_cost hKpow)
    have h26 : WordR main swP (fun vs => vs = A25) (fun _ out => out = A26) (fun _ => Cstep) :=
      wrd_swap (hsw main) (.int ((2 : ℤ) ^ p)) (.int (y * x' + y' * x)) A16
        (sw_cost hKsw h2p19 hII19)
    have h27 : WordR main tdivP (fun vs => vs = A26) (fun _ out => out = A27) (fun _ => Cstep) :=
      wrd_binOp (htdiv main) (a := y * x' + y' * x) (b := (2 : ℤ) ^ p)
        (pow_ne_zero p (by norm_num)) (mul_cost hKtdiv hII9 h2p9)
    have h28 : WordR main swP (fun vs => vs = A27) (fun _ out => out = A28) (fun _ => Cstep) :=
      wrd_swap (hsw main) (.int W2) (.int W1) A4 (sw_cost hKsw hW219 hW119)
    have h29 : WordR main consP (fun vs => vs = A28) (fun _ out => out = A29) (fun _ => Cstep) :=
      wrd_cons (hcons main) (.int W1) (.int W2) A4 (uncon_cost hKcon)
    have h30 : WordR main (rollP 1) (fun vs => vs = A29) (fun _ out => out = A30) (fun _ => Cstep) :=
      wrd_roll (hroll main) 1 A29 (.int x') (by rfl)
        (by simp only [A29, Cv, A4, List.length_cons]; omega)
        (pickroll_cost hKr (by norm_num) hs30)
    have h31 : WordR main dropP (fun vs => vs = A30) (fun _ out => out = A31) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (.int x') A31 (drop_cost hKd hX'19)
    have h32 : WordR main (rollP 1) (fun vs => vs = A31) (fun _ out => out = A32) (fun _ => Cstep) :=
      wrd_roll (hroll main) 1 A31 (.int y') (by rfl)
        (by simp only [A31, Cv, List.length_cons]; omega)
        (pickroll_cost hKr (by norm_num) hs32)
    have h33 : WordR main dropP (fun vs => vs = A32) (fun _ out => out = A33) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (.int y') A33 (drop_cost hKd hY'19)
    have h34 : WordR main (rollP 1) (fun vs => vs = A33) (fun _ out => out = A34) (fun _ => Cstep) :=
      wrd_roll (hroll main) 1 A33 (.int x) (by rfl)
        (by simp only [A33, Cv, List.length_cons]; omega)
        (pickroll_cost hKr (by norm_num) hs34)
    have h35 : WordR main dropP (fun vs => vs = A34) (fun _ out => out = A35) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (.int x) A35 (drop_cost hKd hX19)
    have h36 : WordR main (rollP 1) (fun vs => vs = A35) (fun _ out => out = A36) (fun _ => Cstep) :=
      wrd_roll (hroll main) 1 A35 (.int y) (by rfl)
        (by simp only [A35, Cv, List.length_cons]; omega)
        (pickroll_cost hKr (by norm_num) hs36)
    have h37 : WordR main dropP (fun vs => vs = A36) (fun _ out => out = A37) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (.int y) A37 (drop_cost hKd hY19)
    have h38 : WordR main (rollP 1) (fun vs => vs = A37) (fun _ out => out = A38) (fun _ => Cstep) :=
      wrd_roll (hroll main) 1 A37 (.int (p : ℤ)) (by rfl)
        (by simp only [A37, Cv, List.length_cons]; omega)
        (pickroll_cost hKr (by norm_num) hs38)
    have h39 : WordR main dropP (fun vs => vs = A38) (fun _ out => out = A39) (fun _ => Cstep) :=
      wrd_drop (hdrop main) (.int (p : ℤ)) A39 (drop_cost hKd hPv19)
    have H38 := wrd_seq2 h38 h39
    have H37 := wrd_seq2 h37 H38
    have H36 := wrd_seq2 h36 H37
    have H35 := wrd_seq2 h35 H36
    have H34 := wrd_seq2 h34 H35
    have H33 := wrd_seq2 h33 H34
    have H32 := wrd_seq2 h32 H33
    have H31 := wrd_seq2 h31 H32
    have H30 := wrd_seq2 h30 H31
    have H29 := wrd_seq2 h29 H30
    have H28 := wrd_seq2 h28 H29
    have H27 := wrd_seq2 h27 H28
    have H26 := wrd_seq2 h26 H27
    have H25 := wrd_seq2 h25 H26
    have H24 := wrd_seq2 h24 H25
    have H23 := wrd_seq2 h23 H24
    have H22 := wrd_seq2 h22 H23
    have H21 := wrd_seq2 h21 H22
    have H20 := wrd_seq2 h20 H21
    have H19 := wrd_seq2 h19 H20
    have H18 := wrd_seq2 h18 H19
    have H17 := wrd_seq2 h17 H18
    have H16 := wrd_seq2 h16 H17
    have H15 := wrd_seq2 h15 H16
    have H14 := wrd_seq2 h14 H15
    have H13 := wrd_seq2 h13 H14
    have H12 := wrd_seq2 h12 H13
    have H11 := wrd_seq2 h11 H12
    have H10 := wrd_seq2 h10 H11
    have H9 := wrd_seq2 h9 H10
    have H8 := wrd_seq2 h8 H9
    have H7 := wrd_seq2 h7 H8
    have H6 := wrd_seq2 h6 H7
    have H5 := wrd_seq2 h5 H6
    have H4 := wrd_seq2 h4 H5
    have H3 := wrd_seq2 h3 H4
    have H2 := wrd_seq2 h2 H3
    have H1 := wrd_seq2 h1 H2
    have h39c : 39 * Cstep ≤ 39000 * KK * (p + 1) ^ 2 := by
      rw [hCstep]; exact Nat.le_of_eq (by ring)
    refine wrd_conseq hk H1 (fun vs h => h) ?_ ?_
    · intro vs out hvs hout
      refine ⟨(W1, W2), ?_, (mulSFieldMath x y x' y' hd1 hd2).1,
        (mulSFieldMath x y x' y' hd1 hd2).2⟩
      exact hout.trans rfl
    · intro vs hvs
      simp only [add39]
      exact h39c
  intro vs hpre s R hs
  rcases hpre with ⟨u, v, rest, hvs, hu, hv⟩
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hfr⟩ :=
    key u.1 u.2 v.1 v.2 rest hu hv vs (by rw [hvs]) s R hs
  rcases hpost with ⟨w, hout, hw, herr⟩
  exact ⟨out, s', n, ⟨u, v, rest, w, hvs, hout, hw, herr⟩, hev, hn, hstk, hfr⟩

end Work.Fx
