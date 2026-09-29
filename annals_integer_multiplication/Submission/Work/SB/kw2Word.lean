import Mathlib
import Submission.Work.Layout.Shared

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Work.SB

open HvdH
open Work.Layout

local infixl:68 " ;;; " => HvdH.Cmd.seq

namespace Kw2

/-! ## Sizes of encoded values

(The four `encode*_length` lemmas and `vsz_int`/`vsz_cons` are copies of
`Submission.Work.ConvR.basic`, to keep this file's import surface small.) -/

theorem encodePosNum_length (q : PosNum) : (Computability.encodePosNum q).length = q.natSize := by
  induction q with
  | one => rfl
  | bit0 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

theorem encodeNum_length (x : Num) : (Computability.encodeNum x).length = x.natSize := by
  cases x with
  | zero => rfl
  | pos q => exact encodePosNum_length q

theorem castNum_ofNat'_nat (n : ℕ) : ((Num.ofNat' n : Num) : ℕ) = n := by simp

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  change (Computability.encodeNum (Num.ofNat' n)).length = n.size
  rw [encodeNum_length, Num.natSize_to_nat, castNum_ofNat'_nat]

theorem vsz_int (z : ℤ) : vsz (.int z) = isz z := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_nil,
    List.length_map, encodeNat_length, isz]

theorem vsz_cons (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

/-! ## Constant-cost words -/

/-- `WordR` with a constant cost. -/
def WordC (main p : Cmd) (P : List Val → Prop) (Q : List Val → List Val → Prop) (C : ℕ) : Prop :=
  WordR main p P Q (fun _ => C)

theorem WordC.ofWordR {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : ℕ} (h : WordR main p P Q (fun _ => C)) : WordC main p P Q C := h

theorem WordC.seq (hK : KernelLib) {main p q : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : ℕ}
    (h1 : WordC main p P Q C) (h2 : WordC main q P' Q' C')
    (h : ∀ vs mid, P vs → Q vs mid → P' mid) :
    WordC main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out) (C + C') :=
  hK.seq main p q P Q (fun _ => C) P' Q' (fun _ => C') (fun _ => C') h1 h2
    (fun _ _ _ hq => ⟨h _ _ ‹_› hq, le_rfl⟩)

theorem WordC.conseq (hK : KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : ℕ}
    (h1 : WordC main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : C ≤ C') :
    WordC main p P' Q' C' :=
  hK.conseq main p P P' Q Q' (fun _ => C) (fun _ => C') h1 hP hQ (fun _ _ => hC)

/-- Composition of constant-cost words with explicit input/output lists, the cost of the two
parts being added. -/
theorem WordC.seqEq (hK : KernelLib) {main p q : Cmd} {L M N : List Val} {C C' C'' : ℕ}
    (h1 : WordC main p (fun vs => vs = L) (fun _ out => out = M) C)
    (h2 : WordC main q (fun vs => vs = M) (fun _ out => out = N) C')
    (h : C + C' ≤ C'') :
    WordC main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) C'' := by
  refine WordC.conseq hK (WordC.seq hK h1 h2 ?_) (fun _ hh => hh) ?_ h
  · intro vs mid _ hq; exact hq
  · rintro vs out _ ⟨mid, -, hout⟩; exact hout

/-! ## Step combinators -/

/-- `unconsV` at a fixed `cons` value. -/
theorem WordC.unconsStep (hK : KernelLib) {main : Cmd} {uncons : Cmd} {Ku : ℕ}
    (huncons : ∀ main : Cmd, WordR main uncons
      (fun vs => ∃ a b rest, vs = Val.cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = Val.cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => Ku))
    (x y : Val) (tl : List Val) {C : ℕ} (hC : Ku ≤ C) :
    WordC main uncons (fun vs => vs = Val.cons x y :: tl) (fun _ out => out = x :: y :: tl) C := by
  refine WordC.conseq hK (WordC.ofWordR (huncons main)) (fun vs hv => ⟨x, y, tl, hv⟩) ?_ hC
  rintro vs out hv ⟨a, b, rest, hvs, hout⟩
  rw [hv] at hvs
  simp only [List.cons.injEq, Val.cons.injEq, and_assoc] at hvs
  obtain ⟨rfl, rfl, rfl⟩ := hvs
  exact hout

/-- `dup` at a fixed list. -/
theorem WordC.dupStep (hK : KernelLib) {main : Cmd} {dupP : Cmd} {Kd : ℕ}
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    {L L' : List Val} {C : ℕ} (hne : L ≠ [])
    (hL' : L.headD .nil :: L = L') (hC : Kd * (vsz (L.headD .nil) + 1) ≤ C) :
    WordC main dupP (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main dupP (fun vs => vs ≠ []) (fun vs => vs = L)
    (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest) (fun _ out => out = L')
    (fun vs => Kd * (vsz (vs.headD .nil) + 1)) (fun _ => C) (hdup main) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hne
  · intro vs out hvs hQ
    rw [hvs] at hQ
    obtain ⟨v, rest, hv, hout⟩ := hQ
    rw [hout]
    have hv' : v = L.headD .nil := by rw [hv]; rfl
    rw [← hv, hv']
    exact hL'
  · intro vs hvs; rw [hvs]; exact hC

/-- `pick k` at a fixed list. -/
theorem WordC.pickStep (hK : KernelLib) {main : Cmd} {pickP : ℕ → Cmd} {PK : ℕ}
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => PK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k C : ℕ} (hk : k < L.length) (hL' : L.getD k .nil :: L = L')
    (hC : PK * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordC main (pickP k) (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main (pickP k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs) (fun _ out => out = L')
    (fun vs => PK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => C)
    (hpick main k) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hQ; rw [hvs] at hQ; rw [hQ, hL']
  · intro vs hvs; rw [hvs]; exact hC

/-- `roll k` at a fixed list. -/
theorem WordC.rollStep (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {KR : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {L L' : List Val} {k C : ℕ} (hk : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L')
    (hC : KR * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordC main (rollP k) (fun vs => vs = L) (fun _ out => out = L') C := by
  refine hK.conseq main (rollP k) (fun vs => k < vs.length) (fun vs => vs = L)
    (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k) (fun _ out => out = L')
    (fun vs => KR * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)) (fun _ => C)
    (hroll main k) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hk
  · intro vs out hvs hQ; rw [hvs] at hQ; rw [hQ, hL']
  · intro vs hvs; rw [hvs]; exact hC

/-- `swap` at a fixed pair. -/
theorem WordC.swapStep (hK : KernelLib) {main : Cmd} {swapP : Cmd} {Ks : ℕ}
    (hswap : ∀ main : Cmd, WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (tl : List Val) {C : ℕ} (hC : Ks * (vsz a + vsz b + 1) ≤ C) :
    WordC main swapP (fun vs => vs = a :: b :: tl) (fun _ out => out = b :: a :: tl) C := by
  refine hK.conseq main swapP (fun vs => 2 ≤ vs.length) (fun vs => vs = a :: b :: tl)
    (fun vs out => ∃ x y rest, vs = x :: y :: rest ∧ out = y :: x :: rest)
    (fun _ out => out = b :: a :: tl)
    (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)) (fun _ => C)
    (hswap main) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp
  · intro vs out hvs hQ
    rw [hvs] at hQ
    obtain ⟨x, y, rest, hv, hout⟩ := hQ
    rw [hout]
    simp only [List.cons.injEq, and_assoc] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    rfl
  · intro vs hvs
    rw [hvs]
    have h1 : (a :: b :: tl).getD 0 .nil = a := by simp
    have h2 : (a :: b :: tl).getD 1 .nil = b := by simp
    rw [h1, h2]
    exact hC

/-- `consV` at a fixed pair. -/
theorem WordC.consVStep (hK : KernelLib) {main : Cmd} {consVP : Cmd} {KC : ℕ}
    (hconsV : ∀ main : Cmd, WordR main consVP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => KC))
    (a b : Val) (tl : List Val) {C : ℕ} (hC : KC ≤ C) :
    WordC main consVP (fun vs => vs = a :: b :: tl) (fun _ out => out = .cons a b :: tl) C := by
  refine hK.conseq main consVP (fun vs => 2 ≤ vs.length) (fun vs => vs = a :: b :: tl)
    (fun vs out => ∃ x y rest, vs = x :: y :: rest ∧ out = .cons x y :: rest)
    (fun _ out => out = .cons a b :: tl) (fun _ => KC) (fun _ => C) (hconsV main) ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; simp
  · intro vs out hvs hQ
    rw [hvs] at hQ
    obtain ⟨x, y, rest, hv, hout⟩ := hQ
    rw [hout]
    simp only [List.cons.injEq, Val.cons.injEq, and_assoc] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    rfl
  · intro vs hvs; exact hC

/-- `pushVal` of a fixed constant. -/
theorem WordC.pushStep (hK : KernelLib) {main : Cmd} {pushP : Val → Cmd} {KP : ℕ}
    (hpush : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => KP * (vsz v + 1)))
    (z : Val) (tl : List Val) {C : ℕ} (hC : KP * (vsz z + 1) ≤ C) :
    WordC main (pushP z) (fun vs => vs = tl) (fun _ out => out = z :: tl) C := by
  refine hK.conseq main (pushP z) (fun _ => True) (fun vs => vs = tl)
    (fun vs out => out = z :: vs) (fun _ out => out = z :: tl)
    (fun _ => KP * (vsz z + 1)) (fun _ => C) (hpush main z) ?_ ?_ ?_
  · intro vs _; trivial
  · intro vs out hvs hQ; rw [hvs] at hQ; rw [hQ]
  · intro vs _; exact hC

/-- A binary operation at a fixed pair of integers. -/
theorem WordC.binStep (hK : KernelLib) {main p : Cmd} {P : ℤ → ℤ → Prop} {fn : ℤ → ℤ → ℤ}
    {KB : ℤ → ℤ → ℕ} {a b : ℤ} {r : List Val} {C : ℕ}
    (h : BinOp main p P fn KB) (hP : P a b) (hC : KB a b ≤ C) :
    WordC main p (fun vs => vs = .int a :: .int b :: r) (fun _ out => out = .int (fn a b) :: r)
      C := by
  refine hK.conseq main p (fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ P a b)
    (fun vs => vs = .int a :: .int b :: r)
    (fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (fn a b) :: rest)
    (fun _ out => out = .int (fn a b) :: r) (binCost KB) (fun _ => C) h ?_ ?_ ?_
  · intro vs hv; exact ⟨a, b, r, hv, hP⟩
  · intro vs out hv hQ
    obtain ⟨a', b', r', hvs, hout⟩ := hQ
    rw [hv] at hvs
    simp only [List.cons.injEq, Val.int.injEq, and_assoc] at hvs
    obtain ⟨rfl, rfl, rfl⟩ := hvs
    exact hout
  · intro vs hv
    rw [hv]
    simp only [binCost]
    exact hC

/-! ## Arithmetic helpers -/

theorem isz_natCast (n : ℕ) : isz (n : ℤ) = n.size + 2 := by
  simp only [isz, Int.natAbs_natCast]

theorem isz_natCast_le {a N : ℕ} (h : a ≤ N) : isz (a : ℤ) ≤ N.size + 2 := by
  rw [isz_natCast]
  exact Nat.add_le_add_right (Nat.size_le_size h) 2

theorem fdiv_natCast {a : ℤ} {n : ℕ} (ha : 0 ≤ a) (hn : 0 < n) :
    Int.fdiv a (n : ℤ) = ((a.toNat / n : ℕ) : ℤ) := by
  rw [Int.fdiv_eq_ediv_of_nonneg a (by exact_mod_cast hn.le)]
  have h : ((a.toNat / n : ℕ) : ℤ) = a / (n : ℤ) := by
    rw [Int.natCast_ediv, Int.toNat_of_nonneg ha]
  exact h.symm

theorem fmod_natCast {a : ℤ} {n : ℕ} (ha : 0 ≤ a) (hn : 0 < n) :
    Int.fmod a (n : ℤ) = ((a.toNat % n : ℕ) : ℤ) := by
  rw [Int.fmod_eq_emod_of_nonneg a (by exact_mod_cast hn.le)]
  have h : ((a.toNat % n : ℕ) : ℤ) = a % (n : ℤ) := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg ha]
  exact h.symm

/-- The key index identity. -/
theorem tgtIdx_sub_one (n B F : ℕ) (hn : 0 < n) :
    (F / n / B * (n - 1) + F % n) * B + F / n = tgtIdx n B (F / n) (F % n) := by
  simp only [tgtIdx]
  set q := F / n / B with hqdef
  set j := F % n with hjdef
  set b := (F / n) % B with hbdef
  have hs : F / n = q * B + b := by
    rw [hbdef, hqdef, Nat.mul_comm]
    exact (Nat.div_add_mod (F / n) B).symm
  have hq : q * (n - 1) + q = q * n := by
    rw [← Nat.mul_succ]; congr 1; omega
  rw [hs]
  show (q * (n - 1) + j) * B + (q * B + b) = (q * n + j) * B + b
  rw [← Nat.add_assoc, ← Nat.add_mul, Nat.add_right_comm, hq]

/-- `(f/n/B)*(n-1) + f%n` is at most the corresponding flat output index. -/
theorem x_le_tgtIdx (n B F : ℕ) (_hn : 0 < n) (hB : 0 < B) :
    F / n / B * (n - 1) + F % n ≤ tgtIdx n B (F / n) (F % n) := by
  have h2 : F / n / B * n + F % n ≤ (F / n / B * n + F % n) * B := by
    calc F / n / B * n + F % n = (F / n / B * n + F % n) * 1 := (Nat.mul_one _).symm
      _ ≤ (F / n / B * n + F % n) * B := Nat.mul_le_mul_left _ hB
  simp only [tgtIdx]
  calc F / n / B * (n - 1) + F % n ≤ F / n / B * n + F % n := by
        have h : F / n / B * (n - 1) ≤ F / n / B * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
        omega
    _ ≤ (F / n / B * n + F % n) * B := h2
    _ ≤ (F / n / B * n + F % n) * B + (F / n) % B := Nat.le_add_right _ _

/-- `(f/n/B)*(n-1) + f%n` times `B` is at most the flat output index. -/
theorem y_le_tgtIdx (n B F : ℕ) (_hn : 0 < n) :
    (F / n / B * (n - 1) + F % n) * B ≤ tgtIdx n B (F / n) (F % n) := by
  simp only [tgtIdx]
  calc (F / n / B * (n - 1) + F % n) * B ≤ (F / n / B * n + F % n) * B :=
        Nat.mul_le_mul_right _ (by
          have h : F / n / B * (n - 1) ≤ F / n / B * n := Nat.mul_le_mul_left _ (Nat.sub_le n 1)
          omega)
    _ ≤ (F / n / B * n + F % n) * B + (F / n) % B := Nat.le_add_right _ _

/-! ## Cost bounds for the uniform budget `KT * BUD` -/

theorem costK_le {K KT BUD : ℕ} (hK : K ≤ KT) (hBUD1 : 1 ≤ BUD) : K ≤ KT * BUD := by
  calc K ≤ KT := hK
    _ = KT * 1 := (Nat.mul_one KT).symm
    _ ≤ KT * BUD := Nat.mul_le_mul_left KT hBUD1

theorem costLin_le {K a KT BUD : ℕ} (ha : a ≤ BUD) (hBUD1 : 1 ≤ BUD) (hK : 2 * K ≤ KT) :
    K * (a + 1) ≤ KT * BUD := by
  have h1 : K * (a + 1) ≤ K * (2 * BUD) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (2 * BUD) = 2 * K * BUD := by ring
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_right BUD hK)

theorem costPick_le {K k S KT BUD : ℕ} (hS : S ≤ 6 * BUD) (hk : k + 1 ≤ 5) (hK : 30 * K ≤ KT) :
    K * (k + 1) * S ≤ KT * BUD := by
  have h1 : K * (k + 1) * S ≤ K * 5 * (6 * BUD) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left K hk) hS
  have h2 : K * 5 * (6 * BUD) = 30 * K * BUD := by ring
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_right BUD hK)

theorem costSum_le {K a b KT BUD : ℕ} (ha : a ≤ BUD) (hb : b ≤ BUD) (hK : 2 * K ≤ KT) :
    K * (a + b) ≤ KT * BUD := by
  have h1 : K * (a + b) ≤ K * (2 * BUD) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (2 * BUD) = 2 * K * BUD := by ring
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_right BUD hK)

theorem costAdd1_le {K a b KT BUD : ℕ} (ha : a ≤ BUD) (hb : b ≤ BUD) (hBUD1 : 1 ≤ BUD)
    (hK : 3 * K ≤ KT) : K * (a + b + 1) ≤ KT * BUD := by
  have h1 : K * (a + b + 1) ≤ K * (3 * BUD) := Nat.mul_le_mul_left K (by omega)
  have h2 : K * (3 * BUD) = 3 * K * BUD := by ring
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_right BUD hK)

theorem costMulSplit_le {K a b KT M2 Sz : ℕ} (ha : a ≤ Sz) (hb : b ≤ M2) (hK : K ≤ KT) :
    K * a * b ≤ KT * (M2 * Sz) := by
  calc K * a * b ≤ KT * Sz * M2 := Nat.mul_le_mul (Nat.mul_le_mul hK ha) hb
    _ = KT * (M2 * Sz) := by ring

end Kw2

open Kw2

theorem kw2Word (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (n B N Lin : ℕ) (f : ℤ) (v : Val) (tail : List Val),
      0 < n → 0 < B → 0 ≤ f → f.toNat < N → tgtIdx n B (f.toNat / n) (f.toNat % n) < N →
      isz (n : ℤ) ≤ Lin → isz (B : ℤ) ≤ Lin →
      vsz (.cons (.int f) v) ≤ Lin →
      vsz (Val.cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v) ≤ Lin + N.size + 2 ∧
      WordR main p
        (fun vs => vs = .cons (.int f) v :: .int (n : ℤ) :: .int (B : ℤ) :: tail)
        (fun _ out => out = .cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v ::
          .int (n : ℤ) :: .int (B : ℤ) :: tail)
        (fun _ => K * (Lin + N.size + 2) * (N.size + 2)) := by
  obtain ⟨uP, Ku, hu⟩ := hK.unconsV
  obtain ⟨dP, Kd, hd⟩ := hK.dup
  obtain ⟨pP, PK, hp⟩ := hK.pick
  obtain ⟨rP, KR, hr⟩ := hK.roll
  obtain ⟨swP, KS, hsw⟩ := hK.swap
  obtain ⟨cP, KC, hc⟩ := hK.consV
  obtain ⟨vP, KV, hv⟩ := hK.pushVal
  obtain ⟨fdP, Kfd, hfd⟩ := hI.fdiv
  obtain ⟨fmP, Kfm, hfm⟩ := hI.fmod
  obtain ⟨mlP, Kml, hml⟩ := hI.mulS
  obtain ⟨adP, Kad, had⟩ := hI.add
  obtain ⟨sbP, Ksb, hsb⟩ := hI.sub
  let KT : ℕ := 100 * (Ku + Kd + PK + KR + KS + KC + KV + Kfd + Kfm + Kml + Kad + Ksb + 1)
  let PROG : Cmd := (uP ;;; dP ;;; pP 3 ;;; rP 1 ;;; fdP ;;; pP 4 ;;; pP 4 ;;; rP 3 ;;; fmP ;;;
      pP 4 ;;; vP (.int 1) ;;; swP ;;; sbP ;;; pP 3 ;;; pP 3 ;;; rP 1 ;;; fdP ;;; mlP ;;; adP ;;;
      mlP ;;; adP ;;; cP)
  refine ⟨PROG, 22 * KT, ?_⟩
  intro main n B N Lin f v tail hn hB hf0 hfN hRN hnl hBl hval
  let BUD : ℕ := (Lin + N.size + 2) * (N.size + 2)
  let BU2 : ℕ := KT * BUD
  refine ⟨?_, ?_⟩
  · have hZ : (tgtIdx n B (f.toNat / n) (f.toNat % n)).size ≤ N.size :=
      Nat.size_le_size (le_of_lt hRN)
    rw [vsz_cons, vsz_int] at hval
    rw [vsz_cons, vsz_int]
    rw [isz_natCast]
    omega
  · -- the word
    have hsZ : Int.fdiv f (n : ℤ) = ((f.toNat / n : ℕ) : ℤ) := fdiv_natCast hf0 hn
    have hjZ : Int.fmod f (n : ℤ) = ((f.toNat % n : ℕ) : ℤ) := fmod_natCast hf0 hn
    have hqZ : Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) = (((f.toNat / n) / B : ℕ) : ℤ) := by
      rw [hsZ, fdiv_natCast (by positivity) hB, Int.toNat_natCast]
    have hn1Z : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    -- size facts (all bounds are by `N.size + 2` or by `Lin + N.size + 2`)
    have hSz1 : 1 ≤ N.size + 2 := by omega
    have hM1 : 1 ≤ Lin + N.size + 2 := by omega
    have hLin2 : 2 ≤ Lin := by
      have h : 2 ≤ isz (n : ℤ) := by rw [isz_natCast]; omega
      omega
    have hff : isz f ≤ N.size + 2 := by
      rw [← Int.toNat_of_nonneg hf0]; exact isz_natCast_le hfN.le
    have hfs : isz (Int.fdiv f (n : ℤ)) ≤ N.size + 2 := by
      rw [hsZ]; exact isz_natCast_le (le_trans (Nat.div_le_self _ _) hfN.le)
    have hfj : isz (Int.fmod f (n : ℤ)) ≤ N.size + 2 := by
      rw [hjZ]; exact isz_natCast_le (le_trans (Nat.mod_le _ _) hfN.le)
    have hfq : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ)) ≤ N.size + 2 := by
      rw [hqZ]
      exact isz_natCast_le (le_trans (Nat.div_le_self _ _) (le_trans (Nat.div_le_self _ _) hfN.le))
    have hfn : isz (n : ℤ) ≤ Lin + N.size + 2 := by omega
    have hfB : isz (B : ℤ) ≤ Lin + N.size + 2 := by omega
    have hfv : vsz v ≤ Lin + N.size + 2 := by
      rw [vsz_cons, vsz_int] at hval; omega
    have hfn1 : isz ((n : ℤ) - 1) ≤ Lin + N.size + 2 := by
      have h1 : isz ((n - 1 : ℕ) : ℤ) ≤ n.size + 2 := isz_natCast_le (Nat.sub_le n 1)
      have h2 : isz (n : ℤ) = n.size + 2 := isz_natCast n
      rw [hn1Z]; omega
    have hf1 : isz (1 : ℤ) ≤ Lin + N.size + 2 := by
      have h2 : isz (1 : ℤ) ≤ (1 : ℕ).size + 2 := by
        rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl]
        exact isz_natCast_le (le_refl 1)
      have h3 : (1 : ℕ).size ≤ 1 := Nat.size_le.mpr (by norm_num)
      omega
    have hx_le : ((f.toNat / n) / B) * (n - 1) + f.toNat % n ≤ N :=
      le_trans (x_le_tgtIdx n B f.toNat hn hB) hRN.le
    have hx_eq : Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ)
        = ((((f.toNat / n) / B) * (n - 1) + f.toNat % n : ℕ) : ℤ) := by
      rw [hqZ, hn1Z, hjZ, ← Nat.cast_mul, ← Nat.cast_add]
    have hx : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ))
        ≤ N.size + 2 := by
      rw [hx_eq]; exact isz_natCast_le hx_le
    have hxq_eq : Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
        = ((((f.toNat / n) / B) * (n - 1) : ℕ) : ℤ) := by
      rw [hqZ, hn1Z, ← Nat.cast_mul]
    have hxq : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)) ≤ N.size + 2 := by
      rw [hxq_eq]
      exact isz_natCast_le (le_trans (Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.sub_le _ _))
        (le_trans (Nat.div_mul_le_self _ _) hfN.le))
    have hy_le : (((f.toNat / n) / B) * (n - 1) + f.toNat % n) * B ≤ N :=
      le_trans (y_le_tgtIdx n B f.toNat hn) hRN.le
    have hy_eq : (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ)) *
          (B : ℤ)
        = (((((f.toNat / n) / B) * (n - 1) + f.toNat % n) * B : ℕ) : ℤ) := by
      rw [hx_eq, ← Nat.cast_mul]
    have hy : isz ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
          + Int.fmod f (n : ℤ)) * (B : ℤ)) ≤ N.size + 2 := by
      rw [hy_eq]; exact isz_natCast_le hy_le
    have hrZ : (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ)) *
          (B : ℤ) + Int.fdiv f (n : ℤ)
        = ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ) := by
      rw [hqZ, hn1Z, hjZ, hsZ, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add,
        tgtIdx_sub_one n B f.toNat hn]
    -- budget helpers
    have hBUD1 : 1 ≤ BUD := by dsimp only [BUD]; nlinarith [hM1, hSz1]
    have hSzBUD : N.size + 2 ≤ BUD := by
      dsimp only [BUD]
      calc N.size + 2 = 1 * (N.size + 2) := (Nat.one_mul _).symm
        _ ≤ (Lin + N.size + 2) * (N.size + 2) := Nat.mul_le_mul_right _ hM1
    have hM2BUD : Lin + N.size + 2 ≤ BUD := by
      dsimp only [BUD]
      calc Lin + N.size + 2 = (Lin + N.size + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (Lin + N.size + 2) * (N.size + 2) := Nat.mul_le_mul_left _ hSz1
    have hffBUD : isz f ≤ BUD := le_trans hff hSzBUD
    have hfsBUD : isz (Int.fdiv f (n : ℤ)) ≤ BUD := le_trans hfs hSzBUD
    have hfjBUD : isz (Int.fmod f (n : ℤ)) ≤ BUD := le_trans hfj hSzBUD
    have hfqBUD : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ)) ≤ BUD := le_trans hfq hSzBUD
    have hfnBUD : isz (n : ℤ) ≤ BUD := le_trans hfn hM2BUD
    have hfBBUD : isz (B : ℤ) ≤ BUD := le_trans hfB hM2BUD
    have hfvBUD : vsz v ≤ BUD := le_trans hfv hM2BUD
    have hfn1BUD : isz ((n : ℤ) - 1) ≤ BUD := le_trans hfn1 hM2BUD
    have hf1BUD : isz (1 : ℤ) ≤ BUD := le_trans hf1 hM2BUD
    have hfxBUD : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
        + Int.fmod f (n : ℤ)) ≤ BUD := le_trans hx hSzBUD
    have hxqBUD : isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)) ≤ BUD :=
      le_trans hxq hSzBUD
    have hfyBUD : isz ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
        + Int.fmod f (n : ℤ)) * (B : ℤ)) ≤ BUD := le_trans hy hSzBUD
    have hKu : Ku ≤ KT := by dsimp only [KT]; omega
    have hKd : 2 * Kd ≤ KT := by dsimp only [KT]; omega
    have hPK : 30 * PK ≤ KT := by dsimp only [KT]; omega
    have hKR : 30 * KR ≤ KT := by dsimp only [KT]; omega
    have hKS : 3 * KS ≤ KT := by dsimp only [KT]; omega
    have hKC : KC ≤ KT := by dsimp only [KT]; omega
    have hKV : 2 * KV ≤ KT := by dsimp only [KT]; omega
    have hKfd : Kfd ≤ KT := by dsimp only [KT]; omega
    have hKfm : Kfm ≤ KT := by dsimp only [KT]; omega
    have hKml : Kml ≤ KT := by dsimp only [KT]; omega
    have hKad : 2 * Kad ≤ KT := by dsimp only [KT]; omega
    have hKsb : 2 * Ksb ≤ KT := by dsimp only [KT]; omega
    -- states
    let S0 : List Val := .cons (.int f) v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S1 : List Val := .int f :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S2 : List Val := .int f :: .int f :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S3 : List Val := .int (n : ℤ) :: .int f :: .int f :: v :: .int (n : ℤ) ::
      .int (B : ℤ) :: tail
    let S4 : List Val := .int f :: .int (n : ℤ) :: .int f :: v :: .int (n : ℤ) ::
      .int (B : ℤ) :: tail
    let S5 : List Val := .int (Int.fdiv f (n : ℤ)) :: .int f :: v :: .int (n : ℤ) ::
      .int (B : ℤ) :: tail
    let S6 : List Val := .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: .int f :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S7 : List Val := .int (n : ℤ) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: .int f ::
      v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S8 : List Val := .int f :: .int (n : ℤ) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) ::
      v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S9 : List Val := .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) ::
      v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S10 : List Val := .int (n : ℤ) :: .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) ::
      .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S11 : List Val := .int (1 : ℤ) :: .int (n : ℤ) :: .int (Int.fmod f (n : ℤ)) ::
      .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S12 : List Val := .int (n : ℤ) :: .int (1 : ℤ) :: .int (Int.fmod f (n : ℤ)) ::
      .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S13 : List Val := .int ((n : ℤ) - 1) :: .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) ::
      .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S14 : List Val := .int (Int.fdiv f (n : ℤ)) :: .int ((n : ℤ) - 1) ::
      .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S15 : List Val := .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: .int ((n : ℤ) - 1) ::
      .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S16 : List Val := .int (Int.fdiv f (n : ℤ)) :: .int (B : ℤ) :: .int ((n : ℤ) - 1) ::
      .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S17 : List Val := .int (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ)) :: .int ((n : ℤ) - 1) ::
      .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S18 : List Val := .int (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)) ::
      .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S19 : List Val := .int (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
      + Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S20 : List Val := .int ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
      + Int.fmod f (n : ℤ)) * (B : ℤ)) :: .int (Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S21 : List Val := .int ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
      + Int.fmod f (n : ℤ)) * (B : ℤ) + Int.fdiv f (n : ℤ)) :: v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    let S22 : List Val := .cons (.int ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)
      + Int.fmod f (n : ℤ)) * (B : ℤ) + Int.fdiv f (n : ℤ))) v ::
      .int (n : ℤ) :: .int (B : ℤ) :: tail
    have h1 : WordC main uP (fun vs => vs = S0) (fun _ out => out = S1) BU2 :=
      WordC.unconsStep hK hu (.int f) v (.int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2)
        (by dsimp only [BU2]; exact costK_le (K := Ku) (KT := KT) (BUD := BUD) hKu hBUD1)
    have h2 : WordC main dP (fun vs => vs = S1) (fun _ out => out = S2) BU2 := by
      refine WordC.dupStep hK hd (L := S1) (L' := S2) (C := BU2) ?_ ?_ ?_
      · dsimp only [S1]; simp
      · dsimp only [S1, S2]; first | rfl | simp
      · dsimp only [S1]
        simp only [List.headD_cons, vsz_int]
        dsimp only [BU2]
        exact costLin_le (K := Kd) (a := isz f) (KT := KT) (BUD := BUD) hffBUD hBUD1 hKd
    have h3 : WordC main (pP 3) (fun vs => vs = S2) (fun _ out => out = S3) BU2 := by
      refine WordC.pickStep hK hp (k := 3) (L := S2) (L' := S3) (C := BU2) ?_ ?_ ?_
      · dsimp only [S2]; simp only [List.length_cons]; omega
      · dsimp only [S2, S3]; first | rfl | simp
      · generalize hSdef : (((S2.take (3 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S2]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 3) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h4 : WordC main (rP 1) (fun vs => vs = S3) (fun _ out => out = S4) BU2 := by
      refine WordC.rollStep hK hr (k := 1) (L := S3) (L' := S4) (C := BU2) ?_ ?_ ?_
      · dsimp only [S3]; simp only [List.length_cons]; omega
      · dsimp only [S3, S4]; first | rfl | simp
      · generalize hSdef : (((S3.take (1 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S3]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := KR) (k := 1) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hKR

    have h5 : WordC main fdP (fun vs => vs = S4) (fun _ out => out = S5) BU2 := by
      refine WordC.binStep hK (hfd main) (a := f) (b := (n : ℤ))
        (r := .int f :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · omega
      · dsimp only [BU2, BUD]
        exact costMulSplit_le (K := Kfd) (a := isz f) (b := isz (n : ℤ)) (KT := KT)
          (M2 := Lin + N.size + 2) (Sz := N.size + 2) hff hfn hKfd
    have h6 : WordC main (pP 4) (fun vs => vs = S5) (fun _ out => out = S6) BU2 := by
      refine WordC.pickStep hK hp (k := 4) (L := S5) (L' := S6) (C := BU2) ?_ ?_ ?_
      · dsimp only [S5]; simp only [List.length_cons]; omega
      · dsimp only [S5, S6]; first | rfl | simp
      · generalize hSdef : (((S5.take (4 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S5]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 4) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h7 : WordC main (pP 4) (fun vs => vs = S6) (fun _ out => out = S7) BU2 := by
      refine WordC.pickStep hK hp (k := 4) (L := S6) (L' := S7) (C := BU2) ?_ ?_ ?_
      · dsimp only [S6]; simp only [List.length_cons]; omega
      · dsimp only [S6, S7]; first | rfl | simp
      · generalize hSdef : (((S6.take (4 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S6]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 4) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h8 : WordC main (rP 3) (fun vs => vs = S7) (fun _ out => out = S8) BU2 := by
      refine WordC.rollStep hK hr (k := 3) (L := S7) (L' := S8) (C := BU2) ?_ ?_ ?_
      · dsimp only [S7]; simp only [List.length_cons]; omega
      · dsimp only [S7, S8]; first | rfl | simp
      · generalize hSdef : (((S7.take (3 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S7]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := KR) (k := 3) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hKR

    have h9 : WordC main fmP (fun vs => vs = S8) (fun _ out => out = S9) BU2 := by
      refine WordC.binStep hK (hfm main) (a := f) (b := (n : ℤ))
        (r := .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) ::
          .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · omega
      · dsimp only [BU2, BUD]
        exact costMulSplit_le (K := Kfm) (a := isz f) (b := isz (n : ℤ)) (KT := KT)
          (M2 := Lin + N.size + 2) (Sz := N.size + 2) hff hfn hKfm
    have h10 : WordC main (pP 4) (fun vs => vs = S9) (fun _ out => out = S10) BU2 := by
      refine WordC.pickStep hK hp (k := 4) (L := S9) (L' := S10) (C := BU2) ?_ ?_ ?_
      · dsimp only [S9]; simp only [List.length_cons]; omega
      · dsimp only [S9, S10]; first | rfl | simp
      · generalize hSdef : (((S9.take (4 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S9]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 4) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h11 : WordC main (vP (.int 1)) (fun vs => vs = S10) (fun _ out => out = S11) BU2 := by
      refine WordC.pushStep hK hv (z := .int (1 : ℤ)) (tl := S10) (C := BU2) ?_
      dsimp only [BU2]
      simp only [vsz_int]
      exact costLin_le (K := KV) (a := isz (1 : ℤ)) (KT := KT) (BUD := BUD) hf1BUD hBUD1 hKV
    have h12 : WordC main swP (fun vs => vs = S11) (fun _ out => out = S12) BU2 := by
      refine WordC.swapStep hK hsw (.int (1 : ℤ)) (.int (n : ℤ))
        (.int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
          .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_
      dsimp only [BU2]
      simp only [vsz_int]
      exact costAdd1_le (K := KS) (a := isz (1 : ℤ)) (b := isz (n : ℤ)) (KT := KT) (BUD := BUD)
        hf1BUD hfnBUD hBUD1 hKS
    have h13 : WordC main sbP (fun vs => vs = S12) (fun _ out => out = S13) BU2 := by
      refine WordC.binStep hK (hsb main) (a := (n : ℤ)) (b := (1 : ℤ))
        (r := .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
          .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · trivial
      · dsimp only [BU2]
        exact costSum_le (K := Ksb) (a := isz (n : ℤ)) (b := isz (1 : ℤ)) (KT := KT) (BUD := BUD)
          hfnBUD hf1BUD hKsb
    have h14 : WordC main (pP 3) (fun vs => vs = S13) (fun _ out => out = S14) BU2 := by
      refine WordC.pickStep hK hp (k := 3) (L := S13) (L' := S14) (C := BU2) ?_ ?_ ?_
      · dsimp only [S13]; simp only [List.length_cons]; omega
      · dsimp only [S13, S14]; first | rfl | simp
      · generalize hSdef : (((S13.take (3 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S13]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 3) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h15 : WordC main (pP 3) (fun vs => vs = S14) (fun _ out => out = S15) BU2 := by
      refine WordC.pickStep hK hp (k := 3) (L := S14) (L' := S15) (C := BU2) ?_ ?_ ?_
      · dsimp only [S14]; simp only [List.length_cons]; omega
      · dsimp only [S14, S15]; first | rfl | simp
      · generalize hSdef : (((S14.take (3 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S14]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := PK) (k := 3) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hPK

    have h16 : WordC main (rP 1) (fun vs => vs = S15) (fun _ out => out = S16) BU2 := by
      refine WordC.rollStep hK hr (k := 1) (L := S15) (L' := S16) (C := BU2) ?_ ?_ ?_
      · dsimp only [S15]; simp only [List.length_cons]; omega
      · dsimp only [S15, S16]; first | rfl | simp
      · generalize hSdef : (((S15.take (1 + 1)).map vsz).sum + 1) = S
        have hSle : S ≤ 6 * BUD := by
          rw [← hSdef]
          dsimp only [S15]
          simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
          omega
        dsimp only [BU2]
        exact costPick_le (K := KR) (k := 1) (S := S) (KT := KT) (BUD := BUD) hSle (by omega) hKR

    have h17 : WordC main fdP (fun vs => vs = S16) (fun _ out => out = S17) BU2 := by
      refine WordC.binStep hK (hfd main) (a := Int.fdiv f (n : ℤ)) (b := (B : ℤ))
        (r := .int ((n : ℤ) - 1) :: .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) ::
          .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · omega
      · dsimp only [BU2, BUD]
        exact costMulSplit_le (K := Kfd) (a := isz (Int.fdiv f (n : ℤ))) (b := isz (B : ℤ))
          (KT := KT) (M2 := Lin + N.size + 2) (Sz := N.size + 2) hfs hfB hKfd
    have h18 : WordC main mlP (fun vs => vs = S17) (fun _ out => out = S18) BU2 := by
      refine WordC.binStep hK (hml main) (a := Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ))
        (b := (n : ℤ) - 1)
        (r := .int (Int.fmod f (n : ℤ)) :: .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v ::
          .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · trivial
      · dsimp only [BU2, BUD]
        exact costMulSplit_le (K := Kml) (a := isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ)))
          (b := isz ((n : ℤ) - 1)) (KT := KT) (M2 := Lin + N.size + 2) (Sz := N.size + 2)
          hfq hfn1 hKml
    have h19 : WordC main adP (fun vs => vs = S18) (fun _ out => out = S19) BU2 := by
      refine WordC.binStep hK (had main)
        (a := Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1))
        (b := Int.fmod f (n : ℤ))
        (r := .int (B : ℤ) :: .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) ::
          .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · trivial
      · dsimp only [BU2]
        exact costSum_le (K := Kad)
          (a := isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1)))
          (b := isz (Int.fmod f (n : ℤ))) (KT := KT) (BUD := BUD) hxqBUD hfjBUD hKad
    have h20 : WordC main mlP (fun vs => vs = S19) (fun _ out => out = S20) BU2 := by
      refine WordC.binStep hK (hml main)
        (a := Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ))
        (b := (B : ℤ))
        (r := .int (Int.fdiv f (n : ℤ)) :: v :: .int (n : ℤ) :: .int (B : ℤ) :: tail)
        (C := BU2) ?_ ?_
      · trivial
      · dsimp only [BU2, BUD]
        exact costMulSplit_le (K := Kml)
          (a := isz (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ)))
          (b := isz (B : ℤ)) (KT := KT) (M2 := Lin + N.size + 2) (Sz := N.size + 2) hx hfB hKml
    have h21 : WordC main adP (fun vs => vs = S20) (fun _ out => out = S21) BU2 := by
      refine WordC.binStep hK (had main)
        (a := (Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ))
          * (B : ℤ))
        (b := Int.fdiv f (n : ℤ))
        (r := v :: .int (n : ℤ) :: .int (B : ℤ) :: tail) (C := BU2) ?_ ?_
      · trivial
      · dsimp only [BU2]
        exact costSum_le (K := Kad)
          (a := isz ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ))
            * (B : ℤ)))
          (b := isz (Int.fdiv f (n : ℤ))) (KT := KT) (BUD := BUD) hfyBUD hfsBUD hKad
    have h22 : WordC main cP (fun vs => vs = S21) (fun _ out => out = S22) BU2 := by
      refine WordC.consVStep hK hc
        (.int ((Int.fdiv (Int.fdiv f (n : ℤ)) (B : ℤ) * ((n : ℤ) - 1) + Int.fmod f (n : ℤ))
          * (B : ℤ) + Int.fdiv f (n : ℤ))) v (.int (n : ℤ) :: .int (B : ℤ) :: tail)
        (C := BU2) ?_
      dsimp only [BU2]
      exact costK_le (K := KC) (KT := KT) (BUD := BUD) hKC hBUD1

    -- compose
    have A2 := WordC.seqEq hK h1 h2 (C'' := 2 * BU2) (by omega)
    have A3 := WordC.seqEq hK A2 h3 (C'' := 3 * BU2) (by omega)
    have A4 := WordC.seqEq hK A3 h4 (C'' := 4 * BU2) (by omega)
    have A5 := WordC.seqEq hK A4 h5 (C'' := 5 * BU2) (by omega)
    have A6 := WordC.seqEq hK A5 h6 (C'' := 6 * BU2) (by omega)
    have A7 := WordC.seqEq hK A6 h7 (C'' := 7 * BU2) (by omega)
    have A8 := WordC.seqEq hK A7 h8 (C'' := 8 * BU2) (by omega)
    have A9 := WordC.seqEq hK A8 h9 (C'' := 9 * BU2) (by omega)
    have A10 := WordC.seqEq hK A9 h10 (C'' := 10 * BU2) (by omega)
    have A11 := WordC.seqEq hK A10 h11 (C'' := 11 * BU2) (by omega)
    have A12 := WordC.seqEq hK A11 h12 (C'' := 12 * BU2) (by omega)
    have A13 := WordC.seqEq hK A12 h13 (C'' := 13 * BU2) (by omega)
    have A14 := WordC.seqEq hK A13 h14 (C'' := 14 * BU2) (by omega)
    have A15 := WordC.seqEq hK A14 h15 (C'' := 15 * BU2) (by omega)
    have A16 := WordC.seqEq hK A15 h16 (C'' := 16 * BU2) (by omega)
    have A17 := WordC.seqEq hK A16 h17 (C'' := 17 * BU2) (by omega)
    have A18 := WordC.seqEq hK A17 h18 (C'' := 18 * BU2) (by omega)
    have A19 := WordC.seqEq hK A18 h19 (C'' := 19 * BU2) (by omega)
    have A20 := WordC.seqEq hK A19 h20 (C'' := 20 * BU2) (by omega)
    have A21 := WordC.seqEq hK A20 h21 (C'' := 21 * BU2) (by omega)
    have A22 := WordC.seqEq hK A21 h22 (C'' := 22 * BU2) (by omega)
    refine hK.conseq main PROG (fun vs => vs = S0)
      (fun vs => vs = .cons (.int f) v :: .int (n : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ out => out = S22)
      (fun _ out => out = .cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v ::
        .int (n : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ => 22 * BU2)
      (fun _ => 22 * KT * (Lin + N.size + 2) * (N.size + 2)) A22 ?_ ?_ ?_
    · intro vs h
      exact h
    · rintro vs out _ hout
      rw [hout]
      dsimp only [S22]
      rw [hrZ]
    · intro vs _
      exact le_of_eq (by dsimp only [BU2, BUD]; ring)

end Work.SB
