import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auCWDefs

/-!
# `Work.Resample.auCWRecVal`: the carry-record value of one round

The word built here reads a pair `[.int zr, .int zi]` of carries (`0` or `1`), tests each of them for
equality with `1` (`IntLib.eq`), and assembles the record value

`awRec zr zi = ofList (([.int 1] if zr = 1 else []) ++ ([.int 2] if zi = 1 else []))`

of `Work.Resample.auCWDefs`.  The cost is `O (isz zr + isz zi + 1)`: two equality tests, two pushes of
constants, one `KernelLib.ifZero` per component (each followed by a push of a constant and a `consV`)
and one `swap`.

The proof walks through the four cases `(zr = 1, zi = 1)` explicitly; `Pipe` (from `auKit`) is the
Hoare-triple-with-cost interface for words acting on a fixed window of a value stack.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## The value produced by the record word -/

/-- The carry flag of the real component: `1` if `zr = 1`, else `0`. -/
def recCz (zr : ℤ) : ℤ := if (1 : ℤ) = zr then 1 else 0

/-- The carry flag of the imaginary component: `1` if `zi = 1`, else `0`. -/
def recCi (zi : ℤ) : ℤ := if (1 : ℤ) = zi then 1 else 0

/-- The record part contributed by the imaginary component: `[.int 2]` iff its carry is `1`. -/
def recWv (ci : ℤ) : Val := if ci = 0 then Val.nil else Val.cons (Val.int 2) Val.nil

/-- The complete record value computed by the word. -/
def recVv (ci cz : ℤ) : Val := if cz = 0 then recWv ci else Val.cons (Val.int 1) (recWv ci)

theorem recCz_zero_or_one (zr : ℤ) : recCz zr = 0 ∨ recCz zr = 1 := by
  unfold recCz; split <;> simp

theorem recCi_zero_or_one (zi : ℤ) : recCi zi = 0 ∨ recCi zi = 1 := by
  unfold recCi; split <;> simp

theorem isz_one : isz (1 : ℤ) = 3 := by decide
theorem isz_zero : isz (0 : ℤ) = 2 := by decide
theorem isz_two : isz (2 : ℤ) = 4 := by decide
theorem vsz_val_nil : vsz (Val.nil) = 1 := rfl
theorem vsz_val_int_1 : vsz (Val.int 1) = 3 := by rw [Work.Fx.vsz_int, isz_one]
theorem vsz_val_int_2 : vsz (Val.int 2) = 4 := by rw [Work.Fx.vsz_int, isz_two]

theorem isz_recCz_le (zr : ℤ) : isz (recCz zr) ≤ 3 := by
  rcases recCz_zero_or_one zr with h | h <;> rw [h] <;> decide

theorem isz_recCi_le (zi : ℤ) : isz (recCi zi) ≤ 3 := by
  rcases recCi_zero_or_one zi with h | h <;> rw [h] <;> decide

theorem vsz_int_recCz_le (zr : ℤ) : vsz (Val.int (recCz zr)) ≤ 3 := by
  rw [Work.Fx.vsz_int]; exact isz_recCz_le zr

theorem vsz_recWv_le (ci : ℤ) : vsz (recWv ci) ≤ 6 := by
  by_cases h : ci = 0
  · rw [recWv, ite_eq_left h, vsz_val_nil]; norm_num
  · rw [recWv, ite_eq_right h, Work.Fx.vsz_cons, vsz_val_int_2, vsz_val_nil]

/-- The record value is exactly `awRec zr zi`. -/
theorem recVv_eq_awRec (zr zi : ℤ) : recVv (recCi zi) (recCz zr) = awRec zr zi := by
  have hcn : ∀ x : ℤ, ¬(1 = x) → ¬(x = 1) := fun x h h' => h h'.symm
  by_cases h1 : (1:ℤ) = zi
  · subst h1; by_cases h2 : (1:ℤ) = zr
    · subst h2; simp [recVv, recWv, recCi, recCz, awRec, ofList]
    · simp [recVv, recWv, recCi, recCz, awRec, ofList, h2, hcn zr h2]
  · by_cases h2 : (1:ℤ) = zr
    · subst h2; simp [recVv, recWv, recCi, recCz, awRec, ofList, h1, hcn zi h1]
    · simp [recVv, recWv, recCi, recCz, awRec, ofList, h1, h2, hcn zi h1, hcn zr h2]

/-! ## `Pipe` adaptors for the library primitives -/

/-- `KernelLib.pushVal` on an arbitrary window. -/
theorem pipePushVal {main : Cmd} {pv : Val → Cmd} {Kpv : ℕ}
    (hpv : ∀ (m : Cmd) (v : Val), WordR m (pv v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpv * (vsz v + 1)))
    (v : Val) (L : List Val) : Pipe main (pv v) L (v :: L) (Kpv * (vsz v + 1)) := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hpv main v vs trivial s R hR
  exact ⟨out, s', n, by simp only [hout, hvs, List.cons_append], hev, hn, hstk, hoth⟩

/-- `KernelLib.consV` on an arbitrary window (the two top elements are rebuilt as a `cons`). -/
theorem pipeConsV {main cvP : Cmd} {Kcv : ℕ}
    (hcv : WordR main cvP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (a b : Val) (T : List Val) : Pipe main cvP (a :: b :: T) (.cons a b :: T) Kcv := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    hcv vs (by rw [hvs]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hvs)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

/-- `KernelLib.skip` on a fixed window. -/
theorem pipeSkip {main : Cmd} (L : List Val) : Pipe main .skip L L 1 := by
  intro rest vs hvs s R hR
  exact ⟨vs, s, 1, hvs, Eval.skip s, le_refl 1, hR, fun _ _ => rfl⟩

/-- `KernelLib.ifZero` as a `Pipe`: the tested value sits on top of the window `T`, the branches are
run on the window `T` (everything below is the opaque frame) and return the fixed windows `U₁`, `U₂`. -/
theorem pipeIzApp {main : Cmd} {izC : Cmd → Cmd → Cmd} {Kiz : ℕ}
    (hiz : ∀ (main : Cmd) (q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (izC q₁ q₂) (fun vs => vs = .int z :: rest)
        (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => Kiz * (isz z + 1) + max c₁ c₂))
    {q₁ q₂ : Cmd} {z : ℤ} {T U₁ U₂ : List Val} {c₁ c₂ c : ℕ}
    (h₁ : z = 0 → Pipe main q₁ T U₁ c₁) (h₂ : z ≠ 0 → Pipe main q₂ T U₂ c₂)
    (hc : Kiz * (isz z + 1) + max c₁ c₂ ≤ c) :
    Pipe main (izC q₁ q₂) (.int z :: T) (if z = 0 then U₁ else U₂) c := by
  intro rest vs hvs s R hR
  have hvs' : vs = .int z :: (T ++ rest) := by rw [hvs]; rfl
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
    hiz main q₁ q₂ z (T ++ rest) (fun out => out = U₁ ++ rest) (fun out => out = U₂ ++ rest)
      c₁ c₂ (fun hz => h₁ hz rest) (fun hz => h₂ hz rest) vs hvs' s R hR
  refine ⟨out, s', n, ?_, hev, le_trans hn hc, hstk, hoth⟩
  by_cases hz : z = 0
  · rw [ite_eq_left hz]; exact hpost.1 hz
  · rw [ite_eq_right hz]; exact hpost.2 hz

/-! ## The program -/

/-- The prefix `[zr, zi] ↦ [cz, ci]` (two equality tests). -/
def recPreProg (pv : Val → Cmd) (eqP swP : Cmd) : Cmd :=
  Cmd.seq (Cmd.seq (pv (Val.int 1)) eqP) (Cmd.seq swP (Cmd.seq (pv (Val.int 1)) eqP))

/-- The tail `[ci, cz] ↦ [recVv ci cz]`. -/
def recTailProg (pv : Val → Cmd) (swP cvP : Cmd) (izC : Cmd → Cmd → Cmd) : Cmd :=
  Cmd.seq (izC (pv Val.nil) (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)))
          (Cmd.seq swP (izC Cmd.skip (Cmd.seq (pv (Val.int 1)) cvP)))

/-- The complete record word. -/
def recProg (pv : Val → Cmd) (eqP swP cvP : Cmd) (izC : Cmd → Cmd → Cmd) : Cmd :=
  Cmd.seq (recPreProg pv eqP swP) (recTailProg pv swP cvP izC)

/-- Cost of the tail as a function of the two carry flags. -/
def recCost (Kpv Ksw Kcv Kiz : ℕ) (ci cz : ℤ) : ℕ :=
  (Kiz * (isz ci + 1) + max (Kpv * (vsz Val.nil + 1))
      (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv)))
  + (Ksw * (vsz (recWv ci) + vsz (Val.int cz) + 1)
     + (Kiz * (isz cz + 1) + max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)))

/-- The prefix turns `[.int zr, .int zi]` into `[.int (recCi zi), .int (recCz zr)]`. -/
theorem pipePre {main : Cmd} {pv : Val → Cmd} {eqP swP : Cmd} {Kpv Keq Ksw : ℕ}
    (hpv : ∀ (m : Cmd) (v : Val), WordR m (pv v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpv * (vsz v + 1)))
    (heq : ∀ (m : Cmd), BinOp m eqP (fun _ _ => True) (fun a b => if a = b then 1 else 0)
      (fun a b => Keq * (isz a + isz b)))
    (hsw : ∀ (m : Cmd), WordR m swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (zr zi : ℤ) :
    Pipe main (recPreProg pv eqP swP)
      [Val.int zr, Val.int zi] [Val.int (recCi zi), Val.int (recCz zr)]
      (Kpv * (vsz (Val.int 1) + 1) + Keq * (isz 1 + isz zr)
        + (Ksw * (vsz (Val.int (recCz zr)) + vsz (Val.int zi) + 1)
           + (Kpv * (vsz (Val.int 1) + 1) + Keq * (isz 1 + isz zi)))) := by
  have h1a := pipePushVal (main := main) hpv (Val.int 1) [Val.int zr, Val.int zi]
  have h1b := Pipe.appendTail [Val.int zi]
    (Pipe.binOp (heq main) (a := (1:ℤ)) (b := zr) trivial : Pipe main eqP [Val.int 1, Val.int zr]
      [Val.int (recCz zr)] (Keq * (isz 1 + isz zr)))
  have h2a := Pipe.swap main hsw (Val.int (recCz zr)) (Val.int zi)
  have h2b := pipePushVal (main := main) hpv (Val.int 1) [Val.int zi, Val.int (recCz zr)]
  have h2c := Pipe.appendTail [Val.int (recCz zr)]
    (Pipe.binOp (heq main) (a := (1:ℤ)) (b := zi) trivial : Pipe main eqP [Val.int 1, Val.int zi]
      [Val.int (recCi zi)] (Keq * (isz 1 + isz zi)))
  exact Pipe.comp (Pipe.comp h1a h1b) (Pipe.comp h2a (Pipe.comp h2b h2c))

/-- The tail turns `[.int ci, .int cz]` into `[recVv ci cz]` for carries `ci, cz ∈ {0,1}`. -/
theorem pipeTail {main : Cmd} {pv : Val → Cmd} {swP cvP : Cmd} {izC : Cmd → Cmd → Cmd}
    {Kpv Ksw Kcv Kiz : ℕ}
    (hpv : ∀ (m : Cmd) (v : Val), WordR m (pv v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kpv * (vsz v + 1)))
    (hsw : ∀ (m : Cmd), WordR m swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcv : WordR main cvP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (hiz : ∀ (main : Cmd) (q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (izC q₁ q₂) (fun vs => vs = .int z :: rest)
        (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out)) (fun _ => Kiz * (isz z + 1) + max c₁ c₂))
    (ci cz : ℤ) (hci : ci = 0 ∨ ci = 1) (hcz : cz = 0 ∨ cz = 1) :
    Pipe main (recTailProg pv swP cvP izC) [Val.int ci, Val.int cz] [recVv ci cz]
      (recCost Kpv Ksw Kcv Kiz ci cz) := by
  have hz1 : ¬((1:ℤ) = 0) := by decide
  have hb1 : ∀ T : List Val, Pipe main (pv Val.nil) T (Val.nil :: T) (Kpv * (vsz Val.nil + 1)) :=
    fun T => pipePushVal (main := main) hpv Val.nil T
  have hb2 : ∀ T : List Val, Pipe main (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)) T
      (Val.cons (Val.int 2) Val.nil :: T)
      (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv)) :=
    fun T => Pipe.comp (pipePushVal (main := main) hpv Val.nil T)
      (Pipe.comp (pipePushVal (main := main) hpv (Val.int 2) (Val.nil :: T))
        (pipeConsV hcv (Val.int 2) Val.nil T))
  have hb3 : ∀ W : Val, Pipe main Cmd.skip [W] [W] 1 := fun W => pipeSkip [W]
  have hb4 : ∀ W : Val, Pipe main (Cmd.seq (pv (Val.int 1)) cvP) [W] [Val.cons (Val.int 1) W]
      (Kpv * (vsz (Val.int 1) + 1) + Kcv) :=
    fun W => Pipe.comp (pipePushVal (main := main) hpv (Val.int 1) [W])
      (pipeConsV hcv (Val.int 1) W [])
  have key : ∀ (c₁ c₂ : ℤ), (c₁ = 0 ∨ c₁ = 1) → (c₂ = 0 ∨ c₂ = 1) →
      Pipe main (recTailProg pv swP cvP izC) [Val.int c₁, Val.int c₂] [recVv c₁ c₂]
        (recCost Kpv Ksw Kcv Kiz c₁ c₂) := by
    intro c₁ c₂ h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · subst h₁; subst h₂
      have hS3 : Pipe main (izC (pv Val.nil) (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)))
          [Val.int 0, Val.int 0] [Val.nil, Val.int 0]
          (Kiz * (isz (0:ℤ) + 1) + max (Kpv * (vsz Val.nil + 1))
            (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))) := by
        simpa using (pipeIzApp hiz (q₁ := pv Val.nil) (q₂ := Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP))
          (T := [Val.int 0]) (U₁ := [Val.nil, Val.int 0]) (U₂ := [Val.cons (Val.int 2) Val.nil, Val.int 0])
          (c₁ := Kpv * (vsz Val.nil + 1)) (c₂ := Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))
          (fun _ => hb1 [Val.int 0]) (fun h => absurd rfl h) (le_refl _))
      have hswp : Pipe main swP [Val.nil, Val.int 0] [Val.int 0, Val.nil]
          (Ksw * (vsz Val.nil + vsz (Val.int 0) + 1)) := Pipe.swap main hsw Val.nil (Val.int 0)
      have hS4 : Pipe main (izC Cmd.skip (Cmd.seq (pv (Val.int 1)) cvP)) [Val.int 0, Val.nil] [Val.nil]
          (Kiz * (isz (0:ℤ) + 1) + max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)) := by
        simpa using (pipeIzApp hiz (q₁ := Cmd.skip) (q₂ := Cmd.seq (pv (Val.int 1)) cvP)
          (T := [Val.nil]) (U₁ := [Val.nil]) (U₂ := [Val.cons (Val.int 1) Val.nil])
          (c₁ := 1) (c₂ := Kpv * (vsz (Val.int 1) + 1) + Kcv)
          (fun _ => hb3 Val.nil) (fun h => absurd rfl h) (le_refl _))
      simpa [recTailProg, recCost, recVv, recWv] using (Pipe.comp hS3 (Pipe.comp hswp hS4))
    · subst h₁; subst h₂
      have hS3 : Pipe main (izC (pv Val.nil) (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)))
          [Val.int 0, Val.int 1] [Val.nil, Val.int 1]
          (Kiz * (isz (0:ℤ) + 1) + max (Kpv * (vsz Val.nil + 1))
            (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))) := by
        simpa using (pipeIzApp hiz (q₁ := pv Val.nil) (q₂ := Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP))
          (T := [Val.int 1]) (U₁ := [Val.nil, Val.int 1]) (U₂ := [Val.cons (Val.int 2) Val.nil, Val.int 1])
          (c₁ := Kpv * (vsz Val.nil + 1)) (c₂ := Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))
          (fun _ => hb1 [Val.int 1]) (fun h => absurd rfl h) (le_refl _))
      have hswp : Pipe main swP [Val.nil, Val.int 1] [Val.int 1, Val.nil]
          (Ksw * (vsz Val.nil + vsz (Val.int 1) + 1)) := Pipe.swap main hsw Val.nil (Val.int 1)
      have hS4 : Pipe main (izC Cmd.skip (Cmd.seq (pv (Val.int 1)) cvP))
          [Val.int 1, Val.nil] [Val.cons (Val.int 1) Val.nil]
          (Kiz * (isz (1:ℤ) + 1) + max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)) := by
        have h := pipeIzApp (z := (1:ℤ)) hiz (q₁ := Cmd.skip) (q₂ := Cmd.seq (pv (Val.int 1)) cvP)
          (T := [Val.nil]) (U₁ := [Val.nil]) (U₂ := [Val.cons (Val.int 1) Val.nil])
          (c₁ := 1) (c₂ := Kpv * (vsz (Val.int 1) + 1) + Kcv)
          (fun h => absurd h (by decide)) (fun _ => hb4 Val.nil) (le_refl _)
        rw [ite_eq_right hz1] at h
        exact h
      simpa [recTailProg, recCost, recVv, recWv] using (Pipe.comp hS3 (Pipe.comp hswp hS4))
    · subst h₁; subst h₂
      have hS3 : Pipe main (izC (pv Val.nil) (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)))
          [Val.int 1, Val.int 0] [Val.cons (Val.int 2) Val.nil, Val.int 0]
          (Kiz * (isz (1:ℤ) + 1) + max (Kpv * (vsz Val.nil + 1))
            (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))) := by
        have h := pipeIzApp (z := (1:ℤ)) hiz (q₁ := pv Val.nil)
          (q₂ := Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP))
          (T := [Val.int 0]) (U₁ := [Val.nil, Val.int 0]) (U₂ := [Val.cons (Val.int 2) Val.nil, Val.int 0])
          (c₁ := Kpv * (vsz Val.nil + 1)) (c₂ := Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))
          (fun h => absurd h (by decide)) (fun _ => hb2 [Val.int 0]) (le_refl _)
        rw [ite_eq_right hz1] at h
        exact h
      have hswp : Pipe main swP [Val.cons (Val.int 2) Val.nil, Val.int 0]
          [Val.int 0, Val.cons (Val.int 2) Val.nil]
          (Ksw * (vsz (Val.cons (Val.int 2) Val.nil) + vsz (Val.int 0) + 1)) :=
        Pipe.swap main hsw (Val.cons (Val.int 2) Val.nil) (Val.int 0)
      have hS4 : Pipe main (izC Cmd.skip (Cmd.seq (pv (Val.int 1)) cvP))
          [Val.int 0, Val.cons (Val.int 2) Val.nil] [Val.cons (Val.int 2) Val.nil]
          (Kiz * (isz (0:ℤ) + 1) + max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)) := by
        simpa using (pipeIzApp hiz (q₁ := Cmd.skip) (q₂ := Cmd.seq (pv (Val.int 1)) cvP)
          (T := [Val.cons (Val.int 2) Val.nil]) (U₁ := [Val.cons (Val.int 2) Val.nil])
          (U₂ := [Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil)])
          (c₁ := 1) (c₂ := Kpv * (vsz (Val.int 1) + 1) + Kcv)
          (fun _ => hb3 (Val.cons (Val.int 2) Val.nil)) (fun h => absurd rfl h) (le_refl _))
      simpa [recTailProg, recCost, recVv, recWv] using (Pipe.comp hS3 (Pipe.comp hswp hS4))
    · subst h₁; subst h₂
      have hS3 : Pipe main (izC (pv Val.nil) (Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP)))
          [Val.int 1, Val.int 1] [Val.cons (Val.int 2) Val.nil, Val.int 1]
          (Kiz * (isz (1:ℤ) + 1) + max (Kpv * (vsz Val.nil + 1))
            (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))) := by
        have h := pipeIzApp (z := (1:ℤ)) hiz (q₁ := pv Val.nil)
          (q₂ := Cmd.seq (pv Val.nil) (Cmd.seq (pv (Val.int 2)) cvP))
          (T := [Val.int 1]) (U₁ := [Val.nil, Val.int 1]) (U₂ := [Val.cons (Val.int 2) Val.nil, Val.int 1])
          (c₁ := Kpv * (vsz Val.nil + 1)) (c₂ := Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))
          (fun h => absurd h (by decide)) (fun _ => hb2 [Val.int 1]) (le_refl _)
        rw [ite_eq_right hz1] at h
        exact h
      have hswp : Pipe main swP [Val.cons (Val.int 2) Val.nil, Val.int 1]
          [Val.int 1, Val.cons (Val.int 2) Val.nil]
          (Ksw * (vsz (Val.cons (Val.int 2) Val.nil) + vsz (Val.int 1) + 1)) :=
        Pipe.swap main hsw (Val.cons (Val.int 2) Val.nil) (Val.int 1)
      have hS4 : Pipe main (izC Cmd.skip (Cmd.seq (pv (Val.int 1)) cvP))
          [Val.int 1, Val.cons (Val.int 2) Val.nil] [Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil)]
          (Kiz * (isz (1:ℤ) + 1) + max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)) := by
        have h := pipeIzApp (z := (1:ℤ)) hiz (q₁ := Cmd.skip) (q₂ := Cmd.seq (pv (Val.int 1)) cvP)
          (T := [Val.cons (Val.int 2) Val.nil]) (U₁ := [Val.cons (Val.int 2) Val.nil])
          (U₂ := [Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil)])
          (c₁ := 1) (c₂ := Kpv * (vsz (Val.int 1) + 1) + Kcv)
          (fun h => absurd h (by decide)) (fun _ => hb4 (Val.cons (Val.int 2) Val.nil)) (le_refl _)
        rw [ite_eq_right hz1] at h
        exact h
      simpa [recTailProg, recCost, recVv, recWv] using (Pipe.comp hS3 (Pipe.comp hswp hS4))
  exact key ci cz hci hcz

/-! ## The record word -/

theorem auCWRecVal (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (zr zi : ℤ),
      Work.Resample.Pipe main prog [HvdH.Val.int zr, HvdH.Val.int zi] [Work.Resample.awRec zr zi]
        (K * (HvdH.isz zr + HvdH.isz zi + 1)) := by
  obtain ⟨pv, Kpv, hpv⟩ := hk.pushVal
  obtain ⟨eqP, Keq, heq⟩ := hi.eq
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨cvP, Kcv, hcv⟩ := hk.consV
  obtain ⟨izC, Kiz, hiz⟩ := hk.ifZero
  refine ⟨recProg pv eqP swP cvP izC, 54 * (Kpv + Keq + Ksw + Kcv + Kiz + 1), ?_⟩
  intro main zr zi
  have hPre := pipePre (main := main) hpv heq hsw zr zi
  have hTail := pipeTail (main := main) (cvP := cvP) hpv hsw (hcv main) hiz (recCi zi) (recCz zr)
    (recCi_zero_or_one zi) (recCz_zero_or_one zr)
  have hAll : Pipe main (recProg pv eqP swP cvP izC) [Val.int zr, Val.int zi]
      [recVv (recCi zi) (recCz zr)]
      ((Kpv * (vsz (Val.int 1) + 1) + Keq * (isz 1 + isz zr)
        + (Ksw * (vsz (Val.int (recCz zr)) + vsz (Val.int zi) + 1)
           + (Kpv * (vsz (Val.int 1) + 1) + Keq * (isz 1 + isz zi))))
       + recCost Kpv Ksw Kcv Kiz (recCi zi) (recCz zr)) :=
    Pipe.comp hPre hTail
  rw [recVv_eq_awRec zr zi] at hAll
  refine Pipe.le hAll ?_
  dsimp only [recCost]
  have hmax1 : max (Kpv * (vsz Val.nil + 1))
        (Kpv * (vsz Val.nil + 1) + (Kpv * (vsz (Val.int 2) + 1) + Kcv))
      ≤ Kpv * (vsz Val.nil + 1) + (Kpv * (vsz Val.nil + 1)
        + (Kpv * (vsz (Val.int 2) + 1) + Kcv)) := by omega
  have hmax2 : max 1 (Kpv * (vsz (Val.int 1) + 1) + Kcv)
      ≤ 1 + (Kpv * (vsz (Val.int 1) + 1) + Kcv) := by omega
  have hv1 : vsz (Val.int 1) = 3 := vsz_val_int_1
  have hi1 : isz (1 : ℤ) = 3 := isz_one
  have hvn : vsz Val.nil = 1 := vsz_val_nil
  have hv2 : vsz (Val.int 2) = 4 := vsz_val_int_2
  have hcz : isz (recCz zr) ≤ 3 := isz_recCz_le zr
  have hci : isz (recCi zi) ≤ 3 := isz_recCi_le zi
  have hcvz : vsz (Val.int (recCz zr)) ≤ 3 := vsz_int_recCz_le zr
  have hcw : vsz (recWv (recCi zi)) ≤ 6 := vsz_recWv_le _
  have hz : isz zr ≤ isz zr + isz zi + 1 := by omega
  have hi : isz zi ≤ isz zr + isz zi + 1 := by omega
  have hzi : vsz (Val.int zi) ≤ isz zr + isz zi + 1 := by
    rw [Work.Fx.vsz_int]; omega
  have hM : 1 ≤ isz zr + isz zi + 1 := by omega
  nlinarith [hmax1, hmax2, hv1, hi1, hvn, hv2, hcz, hci, hcvz, hcw, hz, hi, hzi, hM,
    Nat.zero_le Kpv, Nat.zero_le Keq, Nat.zero_le Ksw, Nat.zero_le Kcv, Nat.zero_le Kiz]

end Work.Resample
