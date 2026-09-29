import Mathlib
import Submission.Work.Transform.chirpAux
import Submission.Work.Transform.Defs

/-!
# Setup word for the Bluestein chirp table (`Work.Transform.chirpSetupWord`)

From `int p :: intList ts :: R` this word produces the *seed* of the Kronecker (Bluestein) fold of
`Work.Transform.chirpWordBnd`: the reversed list `ts` on top of the single-entry vector
`cvecVal [(2^p, 0)]` (the fixed-point number `1`) and then `int p` and the untouched rest.

Implementation (all words are taken from the libraries `KernelLib`, `IntLib`, `LayoutLib`):

1. `IntLib.pow2` turns `int p` into `int (2^p)`;
2. `KernelLib.pushVal` pushes `int 0`, `KernelLib.swap` and `KernelLib.consV` build
   `cfxVal (2^p, 0) = cons (int (2^p)) (int 0)`;
3. `KernelLib.pushVal` pushes `nil` and `KernelLib.consV` builds the one-element list
   `cvecVal [(2^p,0)] = cons (cfxVal (2^p,0)) nil`;
4. `KernelLib.swap` brings `intList ts` back on top, `LayoutLib.reverse` reverses it
   (`ofList ((ts.map Val.int).reverse) = ofList (ts.reverse.map Val.int)`).

Cost: every step is either constant or a constant times `vsz` of one of the two given values, and
`vsz (intList ts) ≤ 5 * ts.sum + 2` (with `2 ≤ t` for `t ∈ ts`), `vsz (cvecVal …) ≤ p + 8`; the
claimed bound `K * (ts.sum * (p+1)^K) + K` absorbs this for `K = 100 * (K₁+…) + 10`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH

/-! ## Composition and adapters for the library words -/

/-- Compose two `WordR` words whose pre/post describe the value stack *exactly*. -/
theorem cs_seq {main p q : Cmd} {L L' L'' : List Val} {c₁ c₂ : ℕ}
    (h₁ : WordR main p (fun vs => vs = L) (fun _ out => out = L') (fun _ => c₁))
    (h₂ : WordR main q (fun vs => vs = L') (fun _ out => out = L'') (fun _ => c₂)) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = L'') (fun _ => c₁ + c₂) := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hp, he, hn, hstk, hoth⟩ := h₁ vs hvs s R hR
  obtain ⟨out₂, s₂, n₂, hp₂, he₂, hn₂, hstk₂, hoth₂⟩ := h₂ L' rfl s' R (by rw [hstk, hp])
  refine ⟨out₂, s₂, n + n₂, hp₂, Eval.seq he he₂, ?_, ?_, ?_⟩
  · have h1 : n ≤ c₁ := hn
    have h2 : n₂ ≤ c₂ := hn₂
    show n + n₂ ≤ c₁ + c₂
    omega
  · rw [hstk₂, hp₂]
  · intro k hk; rw [hoth₂ k hk, hoth k hk]

/-- An `UnOp` word applied to the integer on top of an exact value stack. -/
theorem cs_unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} {rest : List Val} {c : ℕ} (hP : P a) (hc : C a ≤ c) :
    WordR main prog (fun vs => vs = .int a :: rest) (fun _ out => out = .int (f a) :: rest)
      (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ :=
    h (.int a :: rest) ⟨a, rest, rfl, hP⟩ s R hR
  obtain ⟨a', rest', hvs', hout⟩ := hpost
  simp only [List.cons.injEq] at hvs'
  obtain ⟨hint, hrest⟩ := hvs'
  have hcost' : n ≤ C a := by
    have := hcost
    simpa only [unCost] using this
  refine ⟨out, s', n, ?_, he, le_trans hcost' hc, hstk, hoth⟩
  rw [hout, hrest, Val.int.inj hint]

/-- `KernelLib.pushVal` with an exact precondition. -/
theorem cs_pushVal {main : Cmd} {prog : Val → Cmd} {K : ℕ}
    (h : ∀ v : Val, WordR main (prog v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => K * (vsz v + 1)))
    (v : Val) {rest : List Val} {c : ℕ} (hc : K * (vsz v + 1) ≤ c) :
    WordR main (prog v) (fun vs => vs = rest) (fun _ out => out = v :: rest) (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h v rest trivial s R hR
  refine ⟨out, s', n, ?_, he, le_trans hcost hc, hstk, hoth⟩
  rw [hpost]

/-- `KernelLib.consV` with an exact precondition. -/
theorem cs_consV {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    {a b : Val} {rest : List Val} {c : ℕ} (hc : K ≤ c) :
    WordR main prog (fun vs => vs = a :: b :: rest) (fun _ out => out = .cons a b :: rest)
      (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h (a :: b :: rest) (by simp) s R hR
  obtain ⟨a', b', rest', hvs', hout⟩ := hpost
  simp only [List.cons.injEq] at hvs'
  obtain ⟨ha, hb, hrest⟩ := hvs'
  refine ⟨out, s', n, ?_, he, le_trans hcost hc, hstk, hoth⟩
  rw [hout, ha, hb, hrest]

/-- `KernelLib.swap` with an exact precondition and the cost evaluated on the two values. -/
theorem cs_swap {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    {a b : Val} {rest : List Val} {c : ℕ} (hc : K * (vsz a + vsz b + 1) ≤ c) :
    WordR main prog (fun vs => vs = a :: b :: rest) (fun _ out => out = b :: a :: rest)
      (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h (a :: b :: rest) (by simp) s R hR
  obtain ⟨a', b', rest', hvs', hout⟩ := hpost
  simp only [List.cons.injEq] at hvs'
  obtain ⟨ha, hb, hrest⟩ := hvs'
  have hcost' : n ≤ K * (vsz a + vsz b + 1) := by
    have := hcost
    simpa using this
  refine ⟨out, s', n, ?_, he, le_trans hcost' hc, hstk, hoth⟩
  rw [hout, ha, hb, hrest]

/-- `LayoutLib.reverse` with an exact precondition. -/
theorem cs_reverse {main prog : Cmd} {K : ℕ}
    (h : ∀ (xs : List Val), WordR main prog (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => K * (vsz (ofList xs) + 1)))
    {xs : List Val} {rest : List Val} {c : ℕ} (hc : K * (vsz (ofList xs) + 1) ≤ c) :
    WordR main prog (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = ofList xs.reverse :: rest) (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h xs (ofList xs :: rest) ⟨rest, rfl⟩ s R hR
  obtain ⟨rest', hvs', hout⟩ := hpost
  have hrest : rest' = rest := (List.cons.inj hvs').2.symm
  refine ⟨out, s', n, ?_, he, le_trans hcost hc, hstk, hoth⟩
  rw [hout, hrest]

/-! ## Encoding-size estimates -/

lemma cs_isz_int_natCast_le (p : ℕ) : isz ((p : ℤ)) ≤ p + 2 := by
  have h : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [isz, Int.natAbs_natCast]
  omega

lemma cs_isz_two_pow_le (p : ℕ) : isz ((2 : ℤ) ^ p) ≤ p + 3 := by
  have h1 : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by
    have h : ((2 : ℤ) ^ p) = ((2 ^ p : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.natAbs_natCast]
  rw [isz, h1, Nat.size_pow]

lemma cs_vsz_nil_eq : vsz (Val.nil) = 1 := rfl

/-- The seed vector `cvecVal [(2^p, 0)]` written out (it is the fixed-point number `1`). -/
lemma cs_cvecVal_seed (p : ℕ) :
    cvecVal [((2 : ℤ) ^ p, 0)]
      = Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil := rfl

lemma cs_vsz_int_zero : vsz (Val.int 0) = 2 := by
  rw [chirpAux_vsz_int, isz, Int.natAbs_zero, Nat.size_zero]

lemma cs_vsz_intList_le {ts : List ℕ} (h : ∀ t ∈ ts, 2 ≤ t) : vsz (intList ts) ≤ 5 * ts.sum + 2 := by
  have h1 := chirpAux_vsz_intList_le ts
  have h2 : ts.length ≤ ts.sum :=
    List.length_le_sum_of_one_le ts (fun t ht => by have := h t ht; omega)
  omega

lemma cs_vsz_cf_le (p : ℕ) :
    vsz (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) ≤ p + 6 := by
  rw [chirpAux_vsz_cons, chirpAux_vsz_int, chirpAux_vsz_int]
  have h1 := cs_isz_two_pow_le p
  have h2 : isz (0 : ℤ) = 2 := cs_vsz_int_zero
  omega

lemma cs_vsz_seed_le (p : ℕ) :
    vsz (Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil) ≤ p + 8 := by
  rw [chirpAux_vsz_cons, chirpAux_vsz_cons, chirpAux_vsz_int, chirpAux_vsz_int]
  have h2 := cs_isz_two_pow_le p
  have h3 : isz (0 : ℤ) = 2 := cs_vsz_int_zero
  have h4 : vsz (Val.nil) = 1 := cs_vsz_nil_eq
  omega

/-! ## The cost arithmetic -/

/-- The claimed budget `K * (ts.sum * (p+1)^K) + K` (with `K = 100 * D + 10`) dominates
`C * D * (p + ts.sum + 11)` for any `C ≤ 50`, provided `p ≥ 100` and `ts.sum ≥ 2`. -/
lemma cs_setupArith {p S D C : ℕ} (hp : 100 ≤ p) (hS : 2 ≤ S) (hD : 1 ≤ D) (hC : C ≤ 50) :
    C * D * (p + S + 11) ≤ (100 * D + 10) * (S * (p + 1) ^ (100 * D + 10)) + (100 * D + 10) := by
  have h1 : (p + 1) ^ 2 ≤ (p + 1) ^ (100 * D + 10) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : p + S + 11 ≤ 2 * S * (p + 1) ^ 2 := by
    have key : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
    rw [key]; nlinarith
  have h3 : C * D * (p + S + 11) ≤ C * D * (2 * S * (p + 1) ^ 2) :=
    Nat.mul_le_mul_left _ h2
  have h4 : C * D * (2 * S * (p + 1) ^ 2) = (2 * C) * D * (S * (p + 1) ^ 2) := by ring
  have h5 : 2 * C ≤ 100 := by omega
  have h6 : (2 * C) * D * (S * (p + 1) ^ 2) ≤ 100 * D * (S * (p + 1) ^ 2) := by
    calc (2 * C) * D * (S * (p + 1) ^ 2) = (2 * C) * (D * (S * (p + 1) ^ 2)) := by ring
      _ ≤ 100 * (D * (S * (p + 1) ^ 2)) := Nat.mul_le_mul_right _ h5
      _ = 100 * D * (S * (p + 1) ^ 2) := by ring
  have h7 : 100 * D * (S * (p + 1) ^ 2) ≤ 100 * D * (S * (p + 1) ^ (100 * D + 10)) :=
    Nat.mul_le_mul_left (100 * D) (Nat.mul_le_mul_left S h1)
  have h8 : 100 * D * (S * (p + 1) ^ (100 * D + 10)) + 100 * D
      ≤ (100 * D + 10) * (S * (p + 1) ^ (100 * D + 10)) + (100 * D + 10) := by
    have h9 : 100 * D ≤ 100 * D + 10 := by omega
    have h10 : 100 * D * (S * (p + 1) ^ (100 * D + 10))
        ≤ (100 * D + 10) * (S * (p + 1) ^ (100 * D + 10)) := Nat.mul_le_mul_right _ h9
    omega
  omega

/-! ## The reversed list, in the form of the statement

`ts.reverse.map Val.int` elaborates (through the coercion `List ℕ → List ℤ`) as
`List.map Val.int (ts.reverse >>= fun a => pure (a : ℤ))`, while `LayoutLib.reverse` returns
`ofList ((ts.map Val.int).reverse) = ofList (List.reverse (List.map Val.int (ts >>= …)))`.  The two
following lemmas identify the two forms. -/

lemma cs_coeL_eq_map (l : List ℕ) :
    (l >>= (fun a : ℕ => (pure (a : ℤ) : List ℤ))) = List.map (fun a : ℕ => (a : ℤ)) l := by
  show List.flatMap (fun a : ℕ => ([(a : ℤ)] : List ℤ)) l = List.map (fun a : ℕ => (a : ℤ)) l
  exact (List.map_eq_flatMap).symm

lemma cs_reverseMap (ts : List ℕ) :
    List.reverse (List.map Val.int (ts >>= (fun a : ℕ => (pure (a : ℤ) : List ℤ))))
      = List.map Val.int ((List.reverse ts) >>= (fun a : ℕ => (pure (a : ℤ) : List ℤ))) := by
  rw [cs_coeL_eq_map ts, cs_coeL_eq_map (List.reverse ts), List.map_map, List.map_map,
    ← List.map_reverse]

/-! ## The setup word -/

/-- `KernelLib.pick k` with an exact precondition. -/
theorem cs_pick {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {k : ℕ} {L : List Val} (hk : k < L.length) {c : ℕ}
    (hc : K * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L)
      (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h k L hk s R hR
  refine ⟨out, s', n, ?_, he, le_trans hcost hc, hstk, hoth⟩
  rw [hpost]

/-- `KernelLib.roll k` with an exact precondition. -/
theorem cs_roll {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {k : ℕ} {L : List Val} (hk : k < L.length) {c : ℕ}
    (hc : K * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L.eraseIdx k)
      (fun _ => c) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨out, s', n, hpost, he, hcost, hstk, hoth⟩ := h k L hk s R hR
  refine ⟨out, s', n, ?_, he, le_trans hcost hc, hstk, hoth⟩
  rw [hpost]

/-- `vsz` of the integer value `int p`. -/
lemma cs_vsz_int_natCast_le (p : ℕ) : vsz (Val.int (p : ℤ)) ≤ p + 2 := by
  rw [chirpAux_vsz_int]; exact cs_isz_int_natCast_le p

theorem chirpSetupWord : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p : ℕ) (ts : List ℕ) (R : List HvdH.Val),
      100 ≤ p → ts ≠ [] → (∀ t ∈ ts, 2 ≤ t) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.intList ts :: R)
        (fun vs out => vs = HvdH.Val.int p :: HvdH.intList ts :: R ∧
          out = HvdH.ofList (ts.reverse.map HvdH.Val.int) :: HvdH.cvecVal [(2 ^ p, 0)] ::
            HvdH.Val.int p :: R)
        (fun _ => K * (ts.sum * (p + 1) ^ K) + K) := by
  intro hK hI hL hF
  obtain ⟨powProg, Kpow, hpow⟩ := hI.pow2
  obtain ⟨revProg, Krev, hrev⟩ := hL.reverse
  obtain ⟨swapProg, Kswap, hswap⟩ := hK.swap
  obtain ⟨consProg, Kcons, hcons⟩ := hK.consV
  obtain ⟨pushProg, Kpush, hpush⟩ := hK.pushVal
  obtain ⟨pickProg, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollProg, Kroll, hroll⟩ := hK.roll
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq
      (pickProg 0) powProg) (pushProg (Val.int 0))) swapProg) consProg) (pushProg Val.nil))
      swapProg) consProg) (rollProg 2)) revProg,
    100 * (Kpick + Kpow + Kpush + Kswap + Kcons + Kroll + Krev + 1) + 10, ?_⟩
  intro main p ts R hp hne hge
  have hS2 : 2 ≤ ts.sum := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons t ts' =>
        have h1 : 2 ≤ t := hge t (by simp)
        simp only [List.sum_cons]
        omega
  -- (A) duplicate `int p` (the copy is consumed below, the original stays in place)
  have stepA : WordR main (pickProg 0)
      (fun vs => vs = Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.int (p : ℤ) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kpick * (p + ts.sum + 11)) := by
    have hsum : (((Val.int (p : ℤ) :: intList ts :: R).take (0 + 1)).map vsz).sum
        = vsz (Val.int (p : ℤ)) := rfl
    have h1 : vsz (Val.int (p : ℤ)) ≤ p + 2 := cs_vsz_int_natCast_le p
    have hc : Kpick * (0 + 1) * ((((Val.int (p : ℤ) :: intList ts :: R).take (0 + 1)).map vsz).sum + 1)
        ≤ Kpick * (p + ts.sum + 11) := by
      rw [hsum]
      have h2 : vsz (Val.int (p : ℤ)) + 1 ≤ p + ts.sum + 11 := by omega
      calc Kpick * (0 + 1) * (vsz (Val.int (p : ℤ)) + 1)
          = Kpick * (vsz (Val.int (p : ℤ)) + 1) := by ring
        _ ≤ Kpick * (p + ts.sum + 11) := Nat.mul_le_mul_left _ h2
    exact cs_pick (hpick main) (k := 0) (L := Val.int (p : ℤ) :: intList ts :: R) (by simp) hc
  -- (B) `int p ↦ int (2^p)` (on the copy)
  have stepB : WordR main powProg
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.int ((2 : ℤ) ^ p) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => (2 * Kpow) * (p + ts.sum + 11)) := by
    have hc : Kpow * (((p : ℤ)).toNat + isz ((p : ℤ))) ≤ (2 * Kpow) * (p + ts.sum + 11) := by
      have h1 : ((p : ℤ)).toNat = p := Int.toNat_natCast p
      have h2 : isz ((p : ℤ)) ≤ p + 2 := cs_isz_int_natCast_le p
      rw [h1]
      calc Kpow * (p + isz ((p : ℤ))) ≤ Kpow * (2 * (p + ts.sum + 11)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (2 * Kpow) * (p + ts.sum + 11) := by ring
    have h := cs_unOp (main := main) (prog := powProg) (hpow main)
      (a := (p : ℤ)) (rest := Val.int (p : ℤ) :: intList ts :: R)
      (c := (2 * Kpow) * (p + ts.sum + 11)) (Int.natCast_nonneg p) hc
    simpa only [Int.toNat_natCast] using h
  -- (C) push `int 0`
  have stepC : WordR main (pushProg (Val.int 0))
      (fun vs => vs = Val.int ((2 : ℤ) ^ p) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.int 0 :: Val.int ((2 : ℤ) ^ p) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kpush * (p + ts.sum + 11)) := by
    have hc : Kpush * (vsz (Val.int 0) + 1) ≤ Kpush * (p + ts.sum + 11) := by
      have h1 : vsz (Val.int 0) = 2 := cs_vsz_int_zero
      rw [h1]
      exact Nat.mul_le_mul_left _ (by omega)
    exact cs_pushVal (hpush main) (Val.int 0)
      (rest := Val.int ((2 : ℤ) ^ p) :: Val.int (p : ℤ) :: intList ts :: R)
      (c := Kpush * (p + ts.sum + 11)) hc
  -- (D) swap
  have stepD : WordR main swapProg
      (fun vs => vs = Val.int 0 :: Val.int ((2 : ℤ) ^ p) :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.int ((2 : ℤ) ^ p) :: Val.int 0 :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kswap * (p + ts.sum + 11)) := by
    have hc : Kswap * (vsz (Val.int 0) + vsz (Val.int ((2 : ℤ) ^ p)) + 1)
        ≤ Kswap * (p + ts.sum + 11) := by
      have h1 : vsz (Val.int 0) = 2 := cs_vsz_int_zero
      have h2 : vsz (Val.int ((2 : ℤ) ^ p)) ≤ p + 3 := by
        rw [chirpAux_vsz_int]; exact cs_isz_two_pow_le p
      rw [h1]
      exact Nat.mul_le_mul_left _ (by omega)
    exact cs_swap (hswap main) (a := Val.int 0) (b := Val.int ((2 : ℤ) ^ p))
      (rest := Val.int (p : ℤ) :: intList ts :: R) (c := Kswap * (p + ts.sum + 11)) hc
  -- (E) build `cfxVal (2^p, 0)`
  have stepE : WordR main consProg
      (fun vs => vs = Val.int ((2 : ℤ) ^ p) :: Val.int 0 :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kcons * (p + ts.sum + 11)) := by
    have hc : Kcons ≤ Kcons * (p + ts.sum + 11) := Nat.le_mul_of_pos_right Kcons (by omega)
    exact cs_consV (hcons main) (a := Val.int ((2 : ℤ) ^ p)) (b := Val.int 0)
      (rest := Val.int (p : ℤ) :: intList ts :: R) (c := Kcons * (p + ts.sum + 11)) hc
  -- (F) push `nil`
  have stepF : WordR main (pushProg Val.nil)
      (fun vs => vs = Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.nil :: Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kpush * (p + ts.sum + 11)) := by
    have hc : Kpush * (vsz (Val.nil) + 1) ≤ Kpush * (p + ts.sum + 11) := by
      have h1 : vsz (Val.nil) = 1 := cs_vsz_nil_eq
      rw [h1]
      exact Nat.mul_le_mul_left _ (by omega)
    exact cs_pushVal (hpush main) (Val.nil)
      (rest := Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0) :: Val.int (p : ℤ) :: intList ts :: R)
      (c := Kpush * (p + ts.sum + 11)) hc
  -- (G) swap
  have stepG : WordR main swapProg
      (fun vs => vs = Val.nil :: Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0) :: Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kswap * (p + ts.sum + 11)) := by
    have hc : Kswap * (vsz (Val.nil) + vsz (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) + 1)
        ≤ Kswap * (p + ts.sum + 11) := by
      have h1 : vsz (Val.nil) = 1 := cs_vsz_nil_eq
      have h2 : vsz (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) ≤ p + 6 := cs_vsz_cf_le p
      rw [h1]
      exact Nat.mul_le_mul_left _ (by omega)
    exact cs_swap (hswap main) (a := Val.nil) (b := Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0))
      (rest := Val.int (p : ℤ) :: intList ts :: R) (c := Kswap * (p + ts.sum + 11)) hc
  -- (H) build the seed vector `cvecVal [(2^p, 0)]`
  have stepH : WordR main consProg
      (fun vs => vs = Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0) :: Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ => Kcons * (p + ts.sum + 11)) := by
    have hc : Kcons ≤ Kcons * (p + ts.sum + 11) := Nat.le_mul_of_pos_right Kcons (by omega)
    exact cs_consV (hcons main) (a := Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0))
      (b := Val.nil) (rest := Val.int (p : ℤ) :: intList ts :: R)
      (c := Kcons * (p + ts.sum + 11)) hc
  -- (I) bring the integer list to the top, keeping `int p` above the seed
  have stepI : WordR main (rollProg 2)
      (fun vs => vs = Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R)
      (fun _ out => out = intList ts
        :: Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil :: Val.int (p : ℤ) :: R)
      (fun _ => (30 * Kroll) * (p + ts.sum + 11)) := by
    have hsum : (((Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
          :: Val.int (p : ℤ) :: intList ts :: R).take (2 + 1)).map vsz).sum
        = vsz (Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil)
          + (vsz (Val.int (p : ℤ)) + vsz (intList ts)) := rfl
    have h1 : vsz (Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil) ≤ p + 8 :=
      cs_vsz_seed_le p
    have h2 : vsz (Val.int (p : ℤ)) ≤ p + 2 := cs_vsz_int_natCast_le p
    have h3 : vsz (intList ts) ≤ 5 * ts.sum + 2 := cs_vsz_intList_le hge
    have hc : Kroll * (2 + 1) * ((((Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R).take (2 + 1)).map vsz).sum + 1)
        ≤ (30 * Kroll) * (p + ts.sum + 11) := by
      rw [hsum]
      have h4 : vsz (Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil)
          + (vsz (Val.int (p : ℤ)) + vsz (intList ts)) + 1 ≤ 10 * (p + ts.sum + 11) := by omega
      calc Kroll * (2 + 1) * (vsz (Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil)
            + (vsz (Val.int (p : ℤ)) + vsz (intList ts)) + 1)
          ≤ Kroll * (2 + 1) * (10 * (p + ts.sum + 11)) := Nat.mul_le_mul_left _ h4
        _ = (30 * Kroll) * (p + ts.sum + 11) := by ring
    exact cs_roll (hroll main) (k := 2)
      (L := Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
        :: Val.int (p : ℤ) :: intList ts :: R) (by simp) hc
  -- (J) reverse the list
  have stepJ : WordR main revProg
      (fun vs => vs = intList ts
        :: Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil :: Val.int (p : ℤ) :: R)
      (fun _ out => out = ofList ((ts.map Val.int).reverse)
        :: Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil :: Val.int (p : ℤ) :: R)
      (fun _ => (9 * Krev) * (p + ts.sum + 11)) := by
    have h1 : vsz (ofList (ts.map Val.int)) = vsz (intList ts) := rfl
    have h2 : vsz (intList ts) ≤ 5 * ts.sum + 2 := cs_vsz_intList_le hge
    have hc : Krev * (vsz (ofList (ts.map Val.int)) + 1) ≤ (9 * Krev) * (p + ts.sum + 11) := by
      rw [h1]
      calc Krev * (vsz (intList ts) + 1) ≤ Krev * (9 * (p + ts.sum + 11)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (9 * Krev) * (p + ts.sum + 11) := by ring
    exact cs_reverse (hrev main) (xs := ts.map Val.int)
      (rest := Val.cons (Val.cons (Val.int ((2 : ℤ) ^ p)) (Val.int 0)) Val.nil
        :: Val.int (p : ℤ) :: R)
      (c := (9 * Krev) * (p + ts.sum + 11)) hc
  have hAB := cs_seq stepA stepB
  have hABC := cs_seq hAB stepC
  have hABCD := cs_seq hABC stepD
  have hABCDE := cs_seq hABCD stepE
  have hABCDEF := cs_seq hABCDE stepF
  have hABCDEFG := cs_seq hABCDEF stepG
  have hABCDEFGH := cs_seq hABCDEFG stepH
  have hABCDEFGHI := cs_seq hABCDEFGH stepI
  have hall := cs_seq hABCDEFGHI stepJ
  refine hK.conseq main _ _ _ _ _ _ _ hall ?_ ?_ ?_
  · intro vs hv; exact hv
  · intro vs out hv ho
    refine ⟨hv, ?_⟩
    rw [ho, cs_reverseMap ts, cs_cvecVal_seed p]
  · intro vs hv
    have hcoef : Kpick + 2 * Kpow + 2 * Kpush + 2 * Kswap + 2 * Kcons + 30 * Kroll + 9 * Krev
        ≤ 30 * (Kpick + Kpow + Kpush + Kswap + Kcons + Kroll + Krev + 1) := by omega
    have hM := Nat.mul_le_mul_right (p + ts.sum + 11) hcoef
    have harith := cs_setupArith (p := p) (S := ts.sum)
      (D := Kpick + Kpow + Kpush + Kswap + Kcons + Kroll + Krev + 1)
      (C := 30) hp hS2 (by omega) (by omega)
    have hsum : Kpick * (p + ts.sum + 11) + (2 * Kpow) * (p + ts.sum + 11)
        + Kpush * (p + ts.sum + 11) + Kswap * (p + ts.sum + 11)
        + Kcons * (p + ts.sum + 11) + Kpush * (p + ts.sum + 11)
        + Kswap * (p + ts.sum + 11) + Kcons * (p + ts.sum + 11)
        + (30 * Kroll) * (p + ts.sum + 11) + (9 * Krev) * (p + ts.sum + 11)
        = (Kpick + 2 * Kpow + 2 * Kpush + 2 * Kswap + 2 * Kcons + 30 * Kroll + 9 * Krev)
          * (p + ts.sum + 11) := by ring
    rw [hsum]
    exact le_trans hM harith

end Work.Transform
