import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.KronP.defs

/-!
# KronP: auxiliaries for `splitPack`

Value and list abbreviations for the assembly of `Work.KronP.splitPack`, the combinators used to
chain `WordR` steps with a constant cost, and the single-step words extracted from the library
fields (`dup`, `drop`, `swap`, `pick`, `roll`, `pushVal`, `consV`) with the exact `Pre`/`Post`
equations used by the assembly and with the cost already collapsed to `CMU * B`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## Value abbreviations -/

def cA (p : ℕ) : Val := .int (3 * p : ℤ)

def cB (r : ℕ) : Val := .int (2 * r : ℤ)

def cC (p r : ℕ) : Val := .int (digitOffset p (2 * r))

def cD (p r : ℕ) : Val := .int ((2 : ℤ) ^ (p + Nat.clog 2 r))

def cP (p : ℕ) : Val := .int (p : ℤ)

def cR (r : ℕ) : Val := .int (r : ℤ)

def cU (u : List (ℤ × ℤ)) : Val := cvecVal u

def cV (v : List (ℤ × ℤ)) : Val := cvecVal v

def cU0 (u : List (ℤ × ℤ)) : Val := zsVal (u.map Prod.fst)

def cU1 (u : List (ℤ × ℤ)) : Val := zsVal (u.map Prod.snd)

def cV0 (v : List (ℤ × ℤ)) : Val := zsVal (v.map Prod.fst)

def cV1 (v : List (ℤ × ℤ)) : Val := zsVal (v.map Prod.snd)

def cX0 (u : List (ℤ × ℤ)) (p : ℕ) : Val := .int (kronX0 u p)

def cX1 (u : List (ℤ × ℤ)) (p : ℕ) : Val := .int (kronX1 u p)

def cY0 (v : List (ℤ × ℤ)) (p : ℕ) : Val := .int (kronY0 v p)

def cY1 (v : List (ℤ × ℤ)) (p : ℕ) : Val := .int (kronY1 v p)

def cL2U (u : List (ℤ × ℤ)) (p : ℕ) : Val := zsVal [kronX0 u p, kronX1 u p]

def cL2V (v : List (ℤ × ℤ)) (p : ℕ) : Val := zsVal [kronY0 v p, kronY1 v p]

def cL4U (u : List (ℤ × ℤ)) (p : ℕ) : Val :=
  zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p]

def cL4V (v : List (ℤ × ℤ)) (p : ℕ) : Val :=
  zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p]

/-- The cost currency of `splitPack`. -/
def cBnd (p r : ℕ) (u v : List (ℤ × ℤ)) : ℕ :=
  (r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)

/-! ## Constant-cost words and composition -/

/-- A `WordR` whose cost does not depend on the value stack. -/
abbrev WC (main prog : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : ℕ) : Prop :=
  WordR main prog P Q (fun _ => C)

theorem cons_eq_cons_iff {α : Type*} {a a' : α} {l l' : List α} (h : a :: l = a' :: l') :
    a = a' ∧ l = l' := by
  injection h with h1 h2
  exact ⟨h1, h2⟩

/-- Sequentially compose two constant-cost words with determined states. -/
theorem WC.chainEq (hK : KernelLib) {main p q : Cmd} {S1 S2 S3 : List Val} {C1 C2 : ℕ}
    (h1 : WC main p (fun vs => vs = S1) (fun _ out => out = S2) C1)
    (h2 : WC main q (fun vs => vs = S2) (fun _ out => out = S3) C2) :
    WC main (.seq p q) (fun vs => vs = S1) (fun _ out => out = S3) (C1 + C2) := by
  have hseq : WordR main (.seq p q) (fun vs => vs = S1)
      (fun _ out => ∃ mid, mid = S2 ∧ out = S3) (fun _ => C1 + C2) :=
    hK.seq main p q (fun vs => vs = S1) (fun _ out => out = S2) (fun _ => C1)
      (fun vs => vs = S2) (fun _ out => out = S3) (fun _ => C2) (fun _ => C2) h1 h2
      (fun vs mid _ h2' => ⟨h2', le_rfl⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = S1) (fun vs => vs = S1)
    (fun _ out => ∃ mid, mid = S2 ∧ out = S3) (fun _ out => out = S3)
    (fun _ => C1 + C2) (fun _ => C1 + C2) hseq ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out _ h2'
    obtain ⟨mid, hm, hout⟩ := h2'
    exact hout
  · intro vs _; exact le_rfl

/-- Turn a raw library word into a constant-cost word with the exact `Pre`/`Post` equations. -/
theorem WC.ofState (hK : KernelLib) {main prog : Cmd} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C : List Val → ℕ} {S1 S2 : List Val} {CMU B : ℕ}
    (h : WordR main prog P Q C) (hP : P S1) (hQ : ∀ out, Q S1 out → out = S2)
    (hC : C S1 ≤ CMU * B) :
    WC main prog (fun vs => vs = S1) (fun _ out => out = S2) (CMU * B) := by
  refine hK.conseq main prog P (fun vs => vs = S1) Q (fun _ out => out = S2) C
    (fun _ => CMU * B) h ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hP
  · intro vs out hvs hout; rw [hvs] at hout; exact hQ out hout
  · intro vs hvs; rw [hvs]; exact hC

/-! ## Cost arithmetic -/

theorem cost_le {K CMU B X : ℕ} (hK : 100000000 * K ≤ CMU) (hB : 1 ≤ B) (hX : X ≤ 100000 * B) :
    K * X ≤ CMU * B := by
  calc K * X ≤ K * (100000 * B) := Nat.mul_le_mul_left K hX
    _ = (100000 * K) * B := by ring
    _ ≤ (100000000 * K) * B := Nat.mul_le_mul_right B (Nat.mul_le_mul_right K (by norm_num))
    _ ≤ CMU * B := Nat.mul_le_mul_right B hK

theorem le_add_one {x C B : ℕ} (h : x ≤ C * B) (hB : 1 ≤ B) : x + 1 ≤ (C + 1) * B := by
  calc x + 1 ≤ C * B + B := Nat.add_le_add h hB
    _ = (C + 1) * B := by ring

theorem sum_map_le {l : List Val} {C : ℕ} (h : ∀ v ∈ l, vsz v ≤ C) :
    (l.map vsz).sum ≤ l.length * C := by
  calc (l.map vsz).sum ≤ (l.map (fun _ => C)).sum := List.sum_le_sum (fun v hv => h v hv)
    _ = l.length * C := Work.ConvR.sum_map_const l C

/-- Cost of a `take`-sum, uniform in the length. -/
theorem take_cost_le {S : List Val} {k B : ℕ} (hk : k ≤ 8) (hlen : k + 1 ≤ S.length) (hB : 1 ≤ B)
    (hC : ∀ v ∈ S.take (k + 1), vsz v ≤ 1000 * B) :
    (k + 1) * (((S.take (k + 1)).map vsz).sum + 1) ≤ 100000 * B := by
  have hsum0 : ((S.take (k + 1)).map vsz).sum ≤ (S.take (k + 1)).length * (1000 * B) :=
    sum_map_le (fun v hv => hC v hv)
  rw [List.length_take, Nat.min_eq_left hlen] at hsum0
  have hsum' : ((S.take (k + 1)).map vsz).sum ≤ 9000 * B := by
    calc ((S.take (k + 1)).map vsz).sum ≤ (k + 1) * (1000 * B) := hsum0
      _ ≤ 9 * (1000 * B) := Nat.mul_le_mul_right (1000 * B) (by omega)
      _ = 9000 * B := by ring
  calc (k + 1) * (((S.take (k + 1)).map vsz).sum + 1)
      ≤ 9 * (9000 * B + 1) := Nat.mul_le_mul (by omega) (Nat.add_le_add_right hsum' 1)
    _ ≤ 100000 * B := by nlinarith [hB]

/-! ## Single-step words -/

theorem stepDup {main : Cmd} {prog : Cmd} {Kd CMU B : ℕ}
    (h : ∀ main : Cmd, WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (hK : KernelLib) (v : Val) (tl : List Val) (hKd : 100000000 * Kd ≤ CMU)
    (hsz : vsz v ≤ 1000 * B) (hB : 1 ≤ B) :
    WC main prog (fun vs => vs = v :: tl) (fun _ out => out = v :: v :: tl) (CMU * B) := by
  refine WC.ofState hK (h main) (List.cons_ne_nil v tl) ?_ ?_
  · intro out hout
    obtain ⟨v', rest, hv, ho⟩ := hout
    obtain ⟨h1, h2⟩ := cons_eq_cons_iff hv
    subst h1; subst h2
    exact ho
  · have hsz' : vsz ((v :: tl).headD .nil) ≤ 1000 * B := by simpa using hsz
    exact cost_le hKd hB
      (le_trans (le_add_one hsz' hB) (Nat.mul_le_mul_right B (by norm_num)))

theorem stepDrop {main : Cmd} {prog : Cmd} {Kd CMU B : ℕ}
    (h : ∀ main : Cmd, WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (hK : KernelLib) (v : Val) (tl : List Val) (hKd : 100000000 * Kd ≤ CMU)
    (hsz : vsz v ≤ 1000 * B) (hB : 1 ≤ B) :
    WC main prog (fun vs => vs = v :: tl) (fun _ out => out = tl) (CMU * B) := by
  refine WC.ofState hK (h main) (List.cons_ne_nil v tl) ?_ ?_
  · intro out hout
    obtain ⟨v', rest, hv, ho⟩ := hout
    obtain ⟨h1, h2⟩ := cons_eq_cons_iff hv
    subst h1; subst h2
    exact ho
  · have hsz' : vsz ((v :: tl).headD .nil) ≤ 1000 * B := by simpa using hsz
    exact cost_le hKd hB
      (le_trans (le_add_one hsz' hB) (Nat.mul_le_mul_right B (by norm_num)))

theorem stepSwap {main : Cmd} {prog : Cmd} {Ks CMU B : ℕ}
    (h : ∀ main : Cmd, WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hK : KernelLib) (a b : Val) (tl : List Val) (hKs : 100000000 * Ks ≤ CMU)
    (ha : vsz a ≤ 1000 * B) (hb : vsz b ≤ 1000 * B) (hB : 1 ≤ B) :
    WC main prog (fun vs => vs = a :: b :: tl) (fun _ out => out = b :: a :: tl) (CMU * B) := by
  refine WC.ofState hK (h main) ?_ ?_ ?_
  · simp only [List.length_cons]; omega
  · intro out hout
    obtain ⟨a', b', rest, hv, ho⟩ := hout
    obtain ⟨h1, h2⟩ := cons_eq_cons_iff hv
    obtain ⟨h3, h4⟩ := cons_eq_cons_iff h2
    subst h1; subst h3; subst h4
    exact ho
  · have h1 : vsz ((a :: b :: tl).getD 0 .nil) ≤ 1000 * B := by simpa using ha
    have h2 : vsz ((a :: b :: tl).getD 1 .nil) ≤ 1000 * B := by simpa using hb
    have hX : vsz ((a :: b :: tl).getD 0 .nil) + vsz ((a :: b :: tl).getD 1 .nil) + 1
        ≤ 100000 * B := by
      have h3 : vsz ((a :: b :: tl).getD 0 .nil) + vsz ((a :: b :: tl).getD 1 .nil)
          ≤ 2000 * B := by omega
      exact le_trans (le_add_one h3 hB) (Nat.mul_le_mul_right B (by norm_num))
    exact cost_le hKs hB hX

theorem stepRoll {main : Cmd} {prog : ℕ → Cmd} {Kr CMU B : ℕ}
    (h : ∀ (main : Cmd) (k : ℕ), WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hK : KernelLib) (k : ℕ) (S S' : List Val) (hlen : k < S.length)
    (heq : S.getD k .nil :: S.eraseIdx k = S')
    (hKr : 100000000 * Kr ≤ CMU)
    (hX : (k + 1) * (((S.take (k + 1)).map vsz).sum + 1) ≤ 100000 * B)
    (hB : 1 ≤ B) :
    WC main (prog k) (fun vs => vs = S) (fun _ out => out = S') (CMU * B) := by
  refine WC.ofState hK (h main k) hlen ?_ ?_
  · intro out hout; rw [hout]; exact heq
  · rw [mul_assoc]; exact cost_le hKr hB hX

theorem stepPick {main : Cmd} {prog : ℕ → Cmd} {Kp CMU B : ℕ}
    (h : ∀ (main : Cmd) (k : ℕ), WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hK : KernelLib) (k : ℕ) (S S' : List Val) (hlen : k < S.length)
    (heq : S.getD k .nil :: S = S')
    (hKp : 100000000 * Kp ≤ CMU)
    (hX : (k + 1) * (((S.take (k + 1)).map vsz).sum + 1) ≤ 100000 * B)
    (hB : 1 ≤ B) :
    WC main (prog k) (fun vs => vs = S) (fun _ out => out = S') (CMU * B) := by
  refine WC.ofState hK (h main k) hlen ?_ ?_
  · intro out hout; rw [hout]; exact heq
  · rw [mul_assoc]; exact cost_le hKp hB hX

theorem stepPushVal {main : Cmd} {prog : Val → Cmd} {Kv CMU B : ℕ}
    (h : ∀ (main : Cmd) (v : Val), WordR main (prog v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kv * (vsz v + 1)))
    (hK : KernelLib) (v : Val) (S S' : List Val) (heq : v :: S = S')
    (hKv : 100000000 * Kv ≤ CMU) (hsz : vsz v ≤ 1000 * B) (hB : 1 ≤ B) :
    WC main (prog v) (fun vs => vs = S) (fun _ out => out = S') (CMU * B) := by
  refine WC.ofState hK (h main v) trivial ?_ ?_
  · intro out hout; rw [hout]; exact heq
  · exact cost_le hKv hB
      (le_trans (le_add_one hsz hB) (Nat.mul_le_mul_right B (by norm_num)))

theorem stepConsV {main : Cmd} {prog : Cmd} {Kc CMU B : ℕ}
    (h : ∀ main : Cmd, WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kc))
    (hK : KernelLib) (a b : Val) (tl : List Val) (hKc : 100000000 * Kc ≤ CMU)
    (hB : 1 ≤ B) :
    WC main prog (fun vs => vs = a :: b :: tl) (fun _ out => out = .cons a b :: tl) (CMU * B) := by
  refine WC.ofState hK (h main) ?_ ?_ ?_
  · simp only [List.length_cons]; omega
  · intro out hout
    obtain ⟨a', b', rest, hv, ho⟩ := hout
    obtain ⟨h1, h2⟩ := cons_eq_cons_iff hv
    obtain ⟨h3, h4⟩ := cons_eq_cons_iff h2
    subst h1; subst h3; subst h4
    exact ho
  · have h2 : Kc ≤ 100000000 * Kc := by
      calc Kc = 1 * Kc := (Nat.one_mul Kc).symm
        _ ≤ 100000000 * Kc := Nat.mul_le_mul_right Kc (by norm_num)
    have h3 : CMU ≤ CMU * B := by
      calc CMU = CMU * 1 := (Nat.mul_one CMU).symm
        _ ≤ CMU * B := Nat.mul_le_mul_left CMU hB
    exact le_trans (le_trans h2 hKc) h3



/-! ## Specifications of the delegated pieces and size arithmetic for the assembly -/

/-- The statement of the delegated `packListWord`. -/
def PackSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (xs : List ℤ) (b : ℕ) (tl : List Val),
      1 ≤ b → (∀ x ∈ xs, x.natAbs < 2 ^ (3 * b)) →
      WordR main prog
        (fun vs => vs = zsVal xs :: Val.int (b : ℤ) :: tl)
        (fun _ out => out = Val.int (pack xs b) :: tl)
        (fun _ => K * (vsz (zsVal xs) + xs.length * (b + 1) + isz (b : ℤ) + 2))

/-- The statement of the delegated `mapFstWord`. -/
def MapFstSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (xs : List (ℤ × ℤ)) (L : ℕ) (tl : List Val),
      (∀ z ∈ xs, vsz (cfxVal z) ≤ L) →
      WordR main prog
        (fun vs => vs = cvecVal xs :: tl)
        (fun _ out => out = zsVal (xs.map Prod.fst) :: tl)
        (fun _ => K * (xs.length * (L + 1) + L + 1))

/-- The statement of the delegated `mapSndWord`. -/
def MapSndSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (xs : List (ℤ × ℤ)) (L : ℕ) (tl : List Val),
      (∀ z ∈ xs, vsz (cfxVal z) ≤ L) →
      WordR main prog
        (fun vs => vs = cvecVal xs :: tl)
        (fun _ out => out = zsVal (xs.map Prod.snd) :: tl)
        (fun _ => K * (xs.length * (L + 1) + L + 1))

/-- The statement of the delegated `twoListWord`. -/
def TwoListSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (a b : Val) (tl : List Val),
      WordR main prog
        (fun vs => vs = a :: b :: tl)
        (fun _ out => out = ofList [a, b] :: tl)
        (fun _ => K * (vsz a + vsz b + 3))

/-- The statement of the delegated `quadWord`. -/
def QuadSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (ys : List Val) (tl : List Val),
      WordR main prog
        (fun vs => vs = ofList ys :: tl)
        (fun _ out => out = ofList (ys ++ ys) :: tl)
        (fun _ => K * (vsz (ofList ys) + 1))

/-- The statement of the delegated `quadRevWord`. -/
def QuadRevSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (ys : List Val) (tl : List Val),
      WordR main prog
        (fun vs => vs = ofList ys :: tl)
        (fun _ out => out = ofList (ys ++ ys.reverse) :: tl)
        (fun _ => K * (vsz (ofList ys) + 1))

/-- The statement of the delegated `kronSizes`. -/
def SizesSpec : Prop :=
  ∀ (p r : ℕ) (u v : List (ℤ × ℤ)) (B : ℕ)
    (hB : B = (r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))
    (hp : 1 ≤ p) (hr : 2 ≤ r) (hu : InDiscVec p r u) (hv : InDiscVec p r v),
    1 ≤ B ∧
    isz (3 * p : ℤ) ≤ 1000 * B ∧ isz (2 * r : ℤ) ≤ 1000 * B ∧
    isz (digitOffset p (2 * r)) ≤ 1000 * B ∧
    isz ((2 : ℤ) ^ (p + Nat.clog 2 r)) ≤ 1000 * B ∧
    isz (p : ℤ) ≤ 1000 * B ∧ isz (r : ℤ) ≤ 1000 * B ∧
    vsz (zsVal (u.map Prod.fst)) ≤ 1000 * B ∧
    vsz (zsVal (u.map Prod.snd)) ≤ 1000 * B ∧
    vsz (zsVal (v.map Prod.fst)) ≤ 1000 * B ∧
    vsz (zsVal (v.map Prod.snd)) ≤ 1000 * B ∧
    isz (kronX0 u p) ≤ 1000 * B ∧ isz (kronX1 u p) ≤ 1000 * B ∧
    isz (kronY0 v p) ≤ 1000 * B ∧ isz (kronY1 v p) ≤ 1000 * B ∧
    vsz (zsVal [kronX0 u p, kronX1 u p]) ≤ 1000 * B ∧
    vsz (zsVal [kronY0 v p, kronY1 v p]) ≤ 1000 * B ∧
    vsz (zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p]) ≤ 1000 * B ∧
    vsz (zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p]) ≤ 1000 * B

/-- The value `.int (3*p)` is the abbreviation `cA p` also with the `ℕ`-cast of `3*p`. -/
theorem int_cast_A (p : ℕ) : Val.int ((3 * p : ℕ) : ℤ) = cA p := by
  simp only [cA]
  have h : ((3 * p : ℕ) : ℤ) = 3 * (p : ℤ) := by push_cast; ring
  rw [h]

theorem cfxSz_le (p : ℕ) : Work.ConvR.cfxSz p + 1 ≤ 12 * (p + 1) := by
  simp only [Work.ConvR.cfxSz]
  omega

/-- Cost bound for the `mapFst`/`mapSnd` steps. -/
theorem coordCost_le {r p B n : ℕ} (hn : n = r) (hB : (r + 1) * (p + 1) ≤ B) :
    n * (Work.ConvR.cfxSz p + 1) + Work.ConvR.cfxSz p + 1 ≤ 100000 * B := by
  rw [hn]
  have h1 : Work.ConvR.cfxSz p + 1 ≤ 12 * (p + 1) := cfxSz_le p
  have h2 : r * (12 * (p + 1)) + 12 * (p + 1) = 12 * ((r + 1) * (p + 1)) := by ring
  calc r * (Work.ConvR.cfxSz p + 1) + Work.ConvR.cfxSz p + 1
      ≤ r * (12 * (p + 1)) + 12 * (p + 1) := by
        have h2 := Nat.mul_le_mul_left r h1
        omega
    _ = 12 * ((r + 1) * (p + 1)) := h2
    _ ≤ 12 * B := Nat.mul_le_mul_left 12 hB
    _ ≤ 100000 * B := Nat.mul_le_mul_right B (by norm_num)

/-- Cost bound for the `packListWord` steps. -/
theorem packCost_le {p r B V A : ℕ} (hV : V ≤ 1000 * B) (hA : A ≤ 1000 * B) (hB1 : 1 ≤ B)
    (hB : (r + 1) * (p + 1) ≤ B) : V + r * (3 * p + 1) + A + 2 ≤ 100000 * B := by
  have h3 : 3 * p + 1 ≤ 4 * (p + 1) := by omega
  have h4 : r * (3 * p + 1) ≤ 4 * B := by
    calc r * (3 * p + 1) ≤ r * (4 * (p + 1)) := Nat.mul_le_mul_left r h3
      _ = 4 * (r * (p + 1)) := by ring
      _ ≤ 4 * ((r + 1) * (p + 1)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (p + 1) (Nat.le_succ r))
      _ ≤ 4 * B := Nat.mul_le_mul_left 4 hB
  have h5 : 2 ≤ 2 * B := Nat.mul_le_mul_left 2 hB1
  nlinarith [hV, hA, h4, h5]

/-- Cost bound for the `twoListWord` steps. -/
theorem twoCost_le {B a b : ℕ} (hB1 : 1 ≤ B) (ha : a ≤ 1000 * B) (hb : b ≤ 1000 * B) :
    a + b + 3 ≤ 100000 * B := by
  have h3 : 3 ≤ 3 * B := Nat.mul_le_mul_left 3 hB1
  nlinarith [ha, hb, h3]

/-- Cost bound for the `quadWord`/`quadRevWord` steps. -/
theorem quadCost_le {B V : ℕ} (hB1 : 1 ≤ B) (hV : V ≤ 1000 * B) : V + 1 ≤ 100000 * B := by
  have h1 : 1 ≤ B := hB1
  nlinarith [hV, h1]

theorem neg_pow_lt (p : ℕ) (hp : 1 ≤ p) : p < 3 * (3 * p) := by
  have h2 : 3 * (3 * p) = 9 * p := by ring
  rw [h2]
  calc p = 1 * p := (Nat.one_mul p).symm
    _ < 9 * p := Nat.mul_lt_mul_of_pos_right (by norm_num) (by omega)

theorem pow_lt_9p {p x : ℕ} (h : x ≤ 2 ^ p) (hp : 1 ≤ p) : x < 2 ^ (3 * (3 * p)) :=
  lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (neg_pow_lt p hp))

/-- `(37 * CMU) * B = 37 * (CMU * B)`. -/
theorem mul_rotate (n CMU B : ℕ) : (n * CMU) * B = n * (CMU * B) := by ring

/-- Cost monotonicity for constant-cost words. -/
theorem WC.monoCost (hK : KernelLib) {main : Cmd} {prog : Cmd} {P : List Val → Prop}
    {Q : List Val → List Val → Prop} {C C' : ℕ} (h : WC main prog P Q C) (hle : C ≤ C') :
    WC main prog P Q C' :=
  hK.conseq main prog P P Q Q (fun _ => C) (fun _ => C') h (fun _ h => h) (fun _ _ _ h => h)
    (fun _ _ => hle)

/-- Add one more constant-cost step to an accumulated chain. -/
theorem WC.add (hK : KernelLib) {main p q : Cmd} {S0 S1 S2 : List Val} {CMU B k : ℕ}
    (h1 : WC main p (fun vs => vs = S0) (fun _ out => out = S1) (k * (CMU * B)))
    (h2 : WC main q (fun vs => vs = S1) (fun _ out => out = S2) (CMU * B)) :
    WC main (.seq p q) (fun vs => vs = S0) (fun _ out => out = S2) ((k + 1) * (CMU * B)) := by
  have h := WC.chainEq hK h1 h2
  have hcost : k * (CMU * B) + CMU * B = (k + 1) * (CMU * B) := by ring
  exact WC.monoCost hK h (le_of_eq hcost)

end Work.KronP
